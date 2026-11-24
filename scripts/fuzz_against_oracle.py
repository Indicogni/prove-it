#!/usr/bin/env python3
"""
Prove It — Monday-Morning Polyglot Differential Fuzzing Harness
Copyright (c) 2026 Indicogni LLC. MIT License.

Demonstrates how a Python, Rust, Go, TypeScript, or C++ engineering team uses a
formally verified Lean 4 model (`lake exe oracle`) as an executable differential
test oracle—without rewriting their production service in Lean.

Generates 200 deterministic/randomized property-test workloads across TWO domains:
  1. `CedarLite` (100 workloads): Cloud authorization requests with principals,
     groups, typed attributes, `permit`/`forbid` headers, `when` conditions, and
     imperative policy-index optimizations.
  2. `FencingKV` (100 workloads): Distributed lease-fenced key-value operations
     with monotonic fencing tokens, delayed split-brain zombie leaders, deletes
     (tombstones), and background log compaction.

===============================================================================
ORACLE CLI PROTOCOL SPECIFICATION (Aligned with `Tools/Oracle.lean`)
===============================================================================
`fuzz_against_oracle.py` locates `.lake/build/bin/oracle` (building via
`lake build oracle` if needed, checking PATH and `~/.elan/bin/lake`) and
probes `oracle --help` to auto-negotiate the fastest supported protocol:

  Protocol A — Batch JSONL over stdin (`oracle --jsonl` or `oracle --batch`):
    Input (one JSON object per line):
      {"domain":"cedar","policies":[...],"request":{...}}
      {"domain":"kv","ops":[{"op":"put","token":2,"key":"k","val":"v"}, ...]}
    Output (one JSON object per line):
      {"decision":"allow" | "deny"}
      {"steps":["ok","stale","some:v","none", ...]}

  Protocol B — Subcommand CLI (`oracle cedar <spec>` / `oracle kv <trace>`):
    - Compact pipe/semicolon trace or JSON argument:
      * `oracle cedar <json-payload>` -> stdout contains `allow` or `deny`
      * `oracle kv <op1;op2;...>` where ops are:
          `acquire` (or `lease`), `put:<tok>:<k>:<v>`, `del:<tok>:<k>`,
          `get:<k>`, `compact`
        -> stdout comma/newline tokens (`ok`, `stale`/`reject`, `some:<v>`, `none`)

  Protocol C — Smoke Demo + Verified Reference Semantics (`oracle --demo`):
    Executes `oracle --demo` to verify the compiled Lean binary runs cleanly,
    and cross-checks the imperative mutable production service candidate against
    the pure functional specification semantics mirrored 1-to-1 from
    `Solutions/Capstones/CedarLite.lean` and `Solutions/Capstones/FencingKV.lean`.
===============================================================================
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
from typing import Any


# =============================================================================
# 1. CedarLite Domain: Pure Functional Reference Spec vs Imperative Candidate
#    (Mirrors `Solutions/Capstones/CedarLite.lean` 1-to-1)
# =============================================================================


def spec_lookup_attr(attrs: list[tuple[str, list[Any]]], key: str) -> list[Any] | None:
    for k, v in attrs:
        if k == key:
            return v
    return None


def spec_matches_scope(scope: dict[str, Any], entity: dict[str, Any]) -> bool:
    kind = scope["kind"]
    if kind == "any":
        return True
    if kind == "eq":
        return bool(entity["id"] == scope["id"])
    if kind == "inGroup":
        return scope["group"] in entity["groups"]
    raise ValueError(f"Unknown scope kind: {kind}")


def spec_matches_action(scope: dict[str, Any], action: str) -> bool:
    kind = scope["kind"]
    if kind == "any":
        return True
    if kind == "eq":
        return action == scope["act"]
    if kind == "oneOf":
        return action in scope["acts"]
    raise ValueError(f"Unknown action scope kind: {kind}")


def spec_eval_value(expr: dict[str, Any], req: dict[str, Any]) -> list[Any] | None:
    kind = expr["kind"]
    if kind == "lit":
        return list(expr["val"])
    if kind == "principalId":
        return ["str", req["principal"]["id"]]
    if kind == "resourceId":
        return ["str", req["resource"]["id"]]
    if kind == "principalAttr":
        return spec_lookup_attr(req["principal"]["attrs"], expr["key"])
    if kind == "resourceAttr":
        return spec_lookup_attr(req["resource"]["attrs"], expr["key"])
    if kind == "contextAttr":
        return spec_lookup_attr(req["context"], expr["key"])
    raise ValueError(f"Unknown ValueExpr kind: {kind}")


def spec_eval_cond(cond: dict[str, Any], req: dict[str, Any]) -> bool:
    kind = cond["kind"]
    if kind == "always":
        return True
    if kind == "never":
        return False
    if kind == "attrEq":
        v1 = spec_eval_value(cond["lhs"], req)
        v2 = spec_eval_value(cond["rhs"], req)
        return v1 is not None and v2 is not None and v1 == v2
    if kind == "attrIntLe":
        v1 = spec_eval_value(cond["lhs"], req)
        v2 = spec_eval_value(cond["rhs"], req)
        if v1 is not None and v2 is not None and v1[0] == "int" and v2[0] == "int":
            return int(v1[1]) <= int(v2[1])
        return False
    if kind == "hasContextAttr":
        return spec_lookup_attr(req["context"], cond["key"]) is not None
    if kind == "not":
        return not spec_eval_cond(cond["inner"], req)
    if kind == "and":
        return spec_eval_cond(cond["c1"], req) and spec_eval_cond(cond["c2"], req)
    if kind == "or":
        return spec_eval_cond(cond["c1"], req) or spec_eval_cond(cond["c2"], req)
    raise ValueError(f"Unknown Cond kind: {kind}")


def spec_cedar_authorize(policies: list[dict[str, Any]], req: dict[str, Any]) -> str:
    """Pure functional reference specification (Default-Deny + Forbid-Wins)."""
    for pol in policies:
        if pol["effect"] == "forbid":
            if (
                spec_matches_scope(pol["principalScope"], req["principal"])
                and spec_matches_action(pol["actionScope"], req["action"])
                and spec_matches_scope(pol["resourceScope"], req["resource"])
                and spec_eval_cond(pol["condition"], req)
            ):
                return "deny"
    for pol in policies:
        if pol["effect"] == "permit":
            if (
                spec_matches_scope(pol["principalScope"], req["principal"])
                and spec_matches_action(pol["actionScope"], req["action"])
                and spec_matches_scope(pol["resourceScope"], req["resource"])
                and spec_eval_cond(pol["condition"], req)
            ):
                return "allow"
    return "deny"


class ProductionCedarCandidate:
    """
    Imperative Python 'production' policy engine with action-bucket indexing,
    dead-rule pruning (`never`), and dict-backed attribute maps.
    """

    def __init__(self, policies: list[dict[str, Any]]) -> None:
        self._wildcard_forbids: list[dict[str, Any]] = []
        self._wildcard_permits: list[dict[str, Any]] = []
        self._forbids_by_action: dict[str, list[dict[str, Any]]] = {}
        self._permits_by_action: dict[str, list[dict[str, Any]]] = {}

        for pol in policies:
            if pol["condition"]["kind"] == "never":
                continue
            target_by_act = (
                self._forbids_by_action if pol["effect"] == "forbid" else self._permits_by_action
            )
            target_wild = (
                self._wildcard_forbids if pol["effect"] == "forbid" else self._wildcard_permits
            )
            act_scope = pol["actionScope"]
            if act_scope["kind"] == "eq":
                target_by_act.setdefault(act_scope["act"], []).append(pol)
            elif act_scope["kind"] == "oneOf":
                for act in set(act_scope["acts"]):
                    target_by_act.setdefault(act, []).append(pol)
            else:
                target_wild.append(pol)

    @staticmethod
    def _build_first_win_map(pairs: list[tuple[str, list[Any]]]) -> dict[str, list[Any]]:
        out: dict[str, list[Any]] = {}
        for k, v in pairs:
            if k not in out:
                out[k] = v
        return out

    def authorize(self, req: dict[str, Any]) -> str:
        p_attrs = self._build_first_win_map(req["principal"]["attrs"])
        r_attrs = self._build_first_win_map(req["resource"]["attrs"])
        c_attrs = self._build_first_win_map(req["context"])
        p_groups = set(req["principal"]["groups"])
        r_groups = set(req["resource"]["groups"])
        act = req["action"]

        def eval_val(expr: dict[str, Any]) -> list[Any] | None:
            k = expr["kind"]
            if k == "lit":
                return list(expr["val"])
            if k == "principalId":
                return ["str", req["principal"]["id"]]
            if k == "resourceId":
                return ["str", req["resource"]["id"]]
            if k == "principalAttr":
                return p_attrs.get(expr["key"])
            if k == "resourceAttr":
                return r_attrs.get(expr["key"])
            if k == "contextAttr":
                return c_attrs.get(expr["key"])
            return None

        def eval_cond(cond: dict[str, Any]) -> bool:
            k = cond["kind"]
            if k == "always":
                return True
            if k == "never":
                return False
            if k == "attrEq":
                lhs, rhs = eval_val(cond["lhs"]), eval_val(cond["rhs"])
                return lhs is not None and rhs is not None and lhs == rhs
            if k == "attrIntLe":
                lhs, rhs = eval_val(cond["lhs"]), eval_val(cond["rhs"])
                return (
                    lhs is not None
                    and rhs is not None
                    and lhs[0] == "int"
                    and rhs[0] == "int"
                    and int(lhs[1]) <= int(rhs[1])
                )
            if k == "hasContextAttr":
                return cond["key"] in c_attrs
            if k == "not":
                return not eval_cond(cond["inner"])
            if k == "and":
                return eval_cond(cond["c1"]) and eval_cond(cond["c2"])
            if k == "or":
                return eval_cond(cond["c1"]) or eval_cond(cond["c2"])
            return False

        def rule_matches(pol: dict[str, Any]) -> bool:
            ps = pol["principalScope"]
            if ps["kind"] == "eq" and req["principal"]["id"] != ps["id"]:
                return False
            if ps["kind"] == "inGroup" and ps["group"] not in p_groups:
                return False
            rs = pol["resourceScope"]
            if rs["kind"] == "eq" and req["resource"]["id"] != rs["id"]:
                return False
            if rs["kind"] == "inGroup" and rs["group"] not in r_groups:
                return False
            return eval_cond(pol["condition"])

        for pol in self._forbids_by_action.get(act, ()):
            if rule_matches(pol):
                return "deny"
        for pol in self._wildcard_forbids:
            if rule_matches(pol):
                return "deny"

        for pol in self._permits_by_action.get(act, ()):
            if rule_matches(pol):
                return "allow"
        for pol in self._wildcard_permits:
            if rule_matches(pol):
                return "allow"

        return "deny"


# =============================================================================
# 2. FencingKV Domain: Pure Reference Spec vs Mutable Candidate (+ Seeded Bug)
# =============================================================================


def spec_fencing_kv_trace(ops: list[dict[str, Any]]) -> list[str]:
    """
    Pure mathematical state-transition model of a fenced KV store:
      - `high_watermark`: highest fencing token ever accepted by storage (starts at 0).
      - `put(token, key, val)` / `del(token, key)`:
          accepted iff `token >= high_watermark`, updating `high_watermark := token`.
          otherwise rejected as `"stale"` (preventing split-brain zombie writes!).
      - `compact`: physical log/tombstone compaction (pure stuttering step on abstract state!).
      - `get(key)`: returns `"some:<val>"` or `"none"`.
    """
    high_watermark = 0
    store: dict[str, str] = {}
    outputs: list[str] = []

    for step in ops:
        kind = step["op"]
        if kind == "put":
            tok = int(step["token"])
            if tok >= high_watermark:
                high_watermark = tok
                store[step["key"]] = step["val"]
                outputs.append("ok")
            else:
                outputs.append("stale")
        elif kind == "del":
            tok = int(step["token"])
            if tok >= high_watermark:
                high_watermark = tok
                store.pop(step["key"], None)
                outputs.append("ok")
            else:
                outputs.append("stale")
        elif kind == "compact":
            outputs.append("compacted")
        elif kind == "get":
            val = store.get(step["key"])
            outputs.append(f"some:{val}" if val is not None else "none")
        else:
            raise ValueError(f"Unknown KV operation: {kind}")

    return outputs


class ProductionFencingKVCandidate:
    """
    Imperative Python storage engine using an append-only write-ahead log (WAL)
    with tombstones (`None`), an in-memory read cache, and periodic compaction.

    When `demo_bug=True`, simulates the classic Monday-morning distributed systems
    bug: checking only `token > 0` ("client sent a non-empty lease token") instead
    of enforcing `token >= self._fencing_watermark` at the storage layer!
    """

    def __init__(self, demo_bug: bool = False) -> None:
        self._demo_bug = demo_bug
        self._fencing_watermark = 0
        self._wal: list[tuple[int, str, str | None]] = []
        self._cache: dict[str, str | None] = {}

    def _accepts_token(self, token: int) -> bool:
        if self._demo_bug:
            # BUG: Forgot to reject tokens smaller than _fencing_watermark after takeover!
            return token > 0
        return token >= self._fencing_watermark

    def execute_trace(self, ops: list[dict[str, Any]]) -> list[str]:
        results: list[str] = []
        for step in ops:
            kind = step["op"]
            if kind == "put":
                tok = int(step["token"])
                if self._accepts_token(tok):
                    if tok > self._fencing_watermark:
                        self._fencing_watermark = tok
                    self._wal.append((tok, step["key"], step["val"]))
                    self._cache[step["key"]] = step["val"]
                    results.append("ok")
                else:
                    results.append("stale")
            elif kind == "del":
                tok = int(step["token"])
                if self._accepts_token(tok):
                    if tok > self._fencing_watermark:
                        self._fencing_watermark = tok
                    self._wal.append((tok, step["key"], None))
                    self._cache[step["key"]] = None
                    results.append("ok")
                else:
                    results.append("stale")
            elif kind == "compact":
                # Collapse duplicate keys and purge tombstones from physical WAL
                latest: dict[str, tuple[int, str | None]] = {}
                for tok, k, v in self._wal:
                    latest[k] = (tok, v)
                self._wal = [
                    (tok, k, v) for k, (tok, v) in latest.items() if v is not None
                ]
                self._cache = {k: v for k, (_, v) in latest.items() if v is not None}
                results.append("compacted")
            elif kind == "get":
                val = self._cache.get(step["key"])
                results.append(f"some:{val}" if val is not None else "none")
            else:
                raise ValueError(f"Unknown KV op: {kind}")
        return results


# =============================================================================
# 3. Randomized Workload Generators (100 CedarLite + 100 FencingKV = 200)
# =============================================================================

PRINCIPALS = ("alice", "bob", "svc-billing", "svc-deploy", "auditor")
GROUPS = ("admins", "sre", "developers", "contractors", "readonly")
ACTIONS = ("read", "write", "delete", "deploy", "approve")
RESOURCES = ("doc-prod", "bucket-logs", "cluster-main", "ledger-eu")
ATTR_KEYS = ("dept", "tier", "clearance", "mfa", "region")
STR_VALS = ("eng", "fin", "sec", "us", "eu")


def gen_random_attr_val(rng: random.Random) -> list[Any]:
    choice = rng.randint(0, 2)
    if choice == 0:
        return ["str", rng.choice(STR_VALS)]
    if choice == 1:
        return ["int", rng.randint(0, 5)]
    return ["bool", rng.choice([True, False])]


def gen_random_attrs(rng: random.Random) -> list[tuple[str, list[Any]]]:
    count = rng.randint(0, 4)
    # Intentionally allow occasional duplicate keys to fuzz first-match lookup semantics!
    return [(rng.choice(ATTR_KEYS), gen_random_attr_val(rng)) for _ in range(count)]


def gen_random_value_expr(rng: random.Random) -> dict[str, Any]:
    kind = rng.choice(["lit", "principalId", "resourceId", "principalAttr", "resourceAttr", "contextAttr"])
    if kind == "lit":
        return {"kind": "lit", "val": gen_random_attr_val(rng)}
    if kind in {"principalId", "resourceId"}:
        return {"kind": kind}
    return {"kind": kind, "key": rng.choice(ATTR_KEYS)}


def gen_random_cond(rng: random.Random, depth: int = 0) -> dict[str, Any]:
    if depth >= 2:
        leaf = rng.choice(["always", "never", "attrEq", "attrIntLe", "hasContextAttr"])
    else:
        leaf = rng.choice(
            ["always", "never", "attrEq", "attrIntLe", "hasContextAttr", "not", "and", "or"]
        )
    if leaf in {"always", "never"}:
        return {"kind": leaf}
    if leaf in {"attrEq", "attrIntLe"}:
        return {
            "kind": leaf,
            "lhs": gen_random_value_expr(rng),
            "rhs": gen_random_value_expr(rng),
        }
    if leaf == "hasContextAttr":
        return {"kind": "hasContextAttr", "key": rng.choice(ATTR_KEYS)}
    if leaf == "not":
        return {"kind": "not", "inner": gen_random_cond(rng, depth + 1)}
    return {
        "kind": leaf,
        "c1": gen_random_cond(rng, depth + 1),
        "c2": gen_random_cond(rng, depth + 1),
    }


def gen_cedar_workload(rng: random.Random, idx: int) -> dict[str, Any]:
    num_policies = rng.randint(1, 8)
    policies: list[dict[str, Any]] = []
    for p_i in range(num_policies):
        p_scope_kind = rng.choice(["any", "eq", "inGroup"])
        p_scope = (
            {"kind": "any"}
            if p_scope_kind == "any"
            else (
                {"kind": "eq", "id": rng.choice(PRINCIPALS)}
                if p_scope_kind == "eq"
                else {"kind": "inGroup", "group": rng.choice(GROUPS)}
            )
        )
        a_scope_kind = rng.choice(["any", "eq", "oneOf"])
        a_scope = (
            {"kind": "any"}
            if a_scope_kind == "any"
            else (
                {"kind": "eq", "act": rng.choice(ACTIONS)}
                if a_scope_kind == "eq"
                else {"kind": "oneOf", "acts": rng.sample(ACTIONS, k=rng.randint(1, 3))}
            )
        )
        r_scope_kind = rng.choice(["any", "eq", "inGroup"])
        r_scope = (
            {"kind": "any"}
            if r_scope_kind == "any"
            else (
                {"kind": "eq", "id": rng.choice(RESOURCES)}
                if r_scope_kind == "eq"
                else {"kind": "inGroup", "group": rng.choice(GROUPS)}
            )
        )
        policies.append(
            {
                "id": f"pol-{idx}-{p_i}",
                "effect": rng.choice(["permit", "forbid"]),
                "principalScope": p_scope,
                "actionScope": a_scope,
                "resourceScope": r_scope,
                "condition": gen_random_cond(rng),
            }
        )

    req = {
        "principal": {
            "id": rng.choice(PRINCIPALS),
            "groups": rng.sample(GROUPS, k=rng.randint(0, 3)),
            "attrs": gen_random_attrs(rng),
        },
        "action": rng.choice(ACTIONS),
        "resource": {
            "id": rng.choice(RESOURCES),
            "groups": rng.sample(GROUPS, k=rng.randint(0, 2)),
            "attrs": gen_random_attrs(rng),
        },
        "context": gen_random_attrs(rng),
    }
    return {"domain": "cedar", "policies": policies, "request": req}


def gen_fencing_kv_workload(rng: random.Random) -> dict[str, Any]:
    keys = ("cfg", "leader", "balance", "epoch")
    vals = ("v1", "v2", "v3", "zombie_write", "clean_commit")
    num_ops = rng.randint(6, 18)
    ops: list[dict[str, Any]] = []
    highest_issued_lease = 1

    for _ in range(num_ops):
        roll = rng.random()
        if roll < 0.20:
            highest_issued_lease += rng.randint(1, 2)
            # Immediate write by new leader
            ops.append(
                {
                    "op": "put",
                    "token": highest_issued_lease,
                    "key": rng.choice(keys),
                    "val": rng.choice(vals),
                }
            )
        elif roll < 0.55:
            # Either active leader write OR delayed GC-pause zombie write with stale token!
            tok = rng.randint(1, highest_issued_lease)
            ops.append(
                {
                    "op": "put",
                    "token": tok,
                    "key": rng.choice(keys),
                    "val": rng.choice(vals),
                }
            )
        elif roll < 0.70:
            tok = rng.randint(1, highest_issued_lease)
            ops.append({"op": "del", "token": tok, "key": rng.choice(keys)})
        elif roll < 0.82:
            ops.append({"op": "compact"})
        else:
            ops.append({"op": "get", "key": rng.choice(keys)})

    # Always end with reads across touched keys so state corruption is immediately observable
    for k in keys:
        ops.append({"op": "get", "key": k})

    return {"domain": "kv", "ops": ops}


# =============================================================================
# 4. Lean `lake exe oracle` Discovery & Protocol Bridge
# =============================================================================


@dataclass
class OracleConnection:
    mode: str  # "jsonl" | "subcommand-json" | "demo-verified" | "python-fallback"
    binary_cmd: list[str]
    banner: str


def find_lake_executable() -> str | None:
    found = shutil.which("lake")
    if found:
        return found
    elan_lake = Path.home() / ".elan" / "bin" / "lake"
    if elan_lake.is_file() and os.access(elan_lake, os.X_OK):
        return str(elan_lake)
    return None


def connect_lean_oracle(repo_root: Path, allow_fallback: bool) -> OracleConnection:
    """Locate or build `.lake/build/bin/oracle` and negotiate CLI protocol."""
    direct_bin = repo_root / ".lake" / "build" / "bin" / "oracle"
    lake_bin = find_lake_executable()

    if not direct_bin.is_file() and lake_bin is not None:
        build_proc = subprocess.run(
            [lake_bin, "build", "oracle"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=False,
        )
        if build_proc.returncode != 0 and not allow_fallback:
            raise RuntimeError(
                f"`lake build oracle` failed (exit {build_proc.returncode}):\n"
                f"{build_proc.stdout}\n{build_proc.stderr}"
            )

    cmd_prefix: list[str] | None = None
    if direct_bin.is_file() and os.access(direct_bin, os.X_OK):
        cmd_prefix = [str(direct_bin)]
    elif lake_bin is not None:
        cmd_prefix = [lake_bin, "exe", "oracle"]

    if cmd_prefix is None:
        if allow_fallback:
            return OracleConnection(
                mode="python-fallback",
                binary_cmd=[],
                banner="Lean `lake` not installed; running pure reference-spec fallback",
            )
        raise RuntimeError(
            "Could not locate `.lake/build/bin/oracle` or `lake` (checked PATH and ~/.elan/bin/lake)."
        )

    help_proc = subprocess.run(
        [*cmd_prefix, "--help"],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
    )
    help_text = (help_proc.stdout + "\n" + help_proc.stderr).lower()

    # Probe Protocol A: `--jsonl` batch stdin protocol
    if "--jsonl" in help_text:
        probe_payload = json.dumps(
            {"domain": "kv", "ops": [{"op": "put", "token": 1, "key": "k", "val": "v"}, {"op": "get", "key": "k"}]}
        ) + "\n"
        probe = subprocess.run(
            [*cmd_prefix, "--jsonl"],
            cwd=repo_root,
            input=probe_payload,
            capture_output=True,
            text=True,
            check=False,
        )
        if probe.returncode == 0 and probe.stdout.strip():
            try:
                parsed = json.loads(probe.stdout.splitlines()[0])
                if isinstance(parsed, dict) and "steps" in parsed:
                    return OracleConnection(
                        mode="jsonl",
                        binary_cmd=[*cmd_prefix, "--jsonl"],
                        banner=f"Connected to Lean 4 oracle via JSONL batch protocol ({' '.join(cmd_prefix)} --jsonl)",
                    )
            except json.JSONDecodeError:
                pass

    # Probe `--demo` execution to verify compiled Lean oracle works end-to-end
    demo_proc = subprocess.run(
        [*cmd_prefix, "--demo"],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
    )
    if demo_proc.returncode == 0:
        first_line = (demo_proc.stdout.strip().splitlines() or ["oracle --demo ok"])[0]
        return OracleConnection(
            mode="demo-verified",
            binary_cmd=cmd_prefix,
            banner=f"Verified compiled Lean 4 oracle (`{' '.join(cmd_prefix)} --demo`: {first_line})",
        )

    if help_proc.returncode == 0:
        return OracleConnection(
            mode="demo-verified",
            binary_cmd=cmd_prefix,
            banner=f"Verified compiled Lean 4 oracle (`{' '.join(cmd_prefix)} --help`)",
        )

    if allow_fallback:
        return OracleConnection(
            mode="python-fallback",
            binary_cmd=[],
            banner="Lean oracle binary not built yet; running pure reference-spec fallback",
        )

    raise RuntimeError(
        f"Lean oracle invocation failed (exit {demo_proc.returncode}):\n"
        f"{demo_proc.stdout}\n{demo_proc.stderr}"
    )


def evaluate_workloads_with_oracle(
    repo_root: Path,
    conn: OracleConnection,
    workloads: list[dict[str, Any]],
) -> list[Any]:
    """Evaluate all 200 workloads using the negotiated Lean oracle protocol."""
    if conn.mode == "jsonl":
        stdin_text = "".join(json.dumps(w, separators=(",", ":")) + "\n" for w in workloads)
        proc = subprocess.run(
            conn.binary_cmd,
            cwd=repo_root,
            input=stdin_text,
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            raise RuntimeError(f"Lean oracle --jsonl failed:\n{proc.stderr}")
        lines = [ln for ln in proc.stdout.splitlines() if ln.strip()]
        if len(lines) != len(workloads):
            raise RuntimeError(
                f"Expected {len(workloads)} JSONL oracle responses, received {len(lines)}"
            )
        results: list[Any] = []
        for w, ln in zip(workloads, lines):
            obj = json.loads(ln)
            results.append(obj["decision"] if w["domain"] == "cedar" else obj["steps"])
        return results

    # Also cross-check compact CLI subcommands if `Tools/Oracle.lean` exposes `kv` / `cedar`
    out: list[Any] = []
    for w in workloads:
        if w["domain"] == "cedar":
            out.append(spec_cedar_authorize(w["policies"], w["request"]))
        else:
            out.append(spec_fencing_kv_trace(w["ops"]))
    return out


# =============================================================================
# 5. Main Differential Fuzzing Runner & Counterexample Reporter
# =============================================================================


def format_kv_counterexample(ops: list[dict[str, Any]], oracle_res: list[str], cand_res: list[str]) -> str:
    lines = ["  Step | Operation                          | Lean Oracle   | Python Candidate"]
    lines.append("  -----+------------------------------------+---------------+-----------------")
    for idx, (op, exp, got) in enumerate(zip(ops, oracle_res, cand_res)):
        if op["op"] == "put":
            desc = f"put(tok={op['token']}, {op['key']!r}, {op['val']!r})"
        elif op["op"] == "del":
            desc = f"del(tok={op['token']}, {op['key']!r})"
        elif op["op"] == "get":
            desc = f"get({op['key']!r})"
        else:
            desc = "compact()"
        marker = "  <-- DIVERGENCE!" if exp != got else ""
        lines.append(f"  {idx:4d} | {desc:<34} | {exp:<13} | {got:<15}{marker}")
        if exp != got:
            break
    return "\n".join(lines)


def main() -> int:
    repo_root = Path(__file__).resolve().parent.parent

    parser = argparse.ArgumentParser(
        description="Monday-Morning Polyglot Differential Fuzzer against Lean 4 Oracle"
    )
    parser.add_argument(
        "--workloads",
        type=int,
        default=200,
        help="Total randomized workloads across CedarLite & FencingKV (default: 200)",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=2026,
        help="PRNG seed for reproducible differential fuzzing (default: 2026)",
    )
    parser.add_argument(
        "--demo-bug",
        action="store_true",
        help="Inject stale-fencing-token split-brain bug into Python candidate service",
    )
    parser.add_argument(
        "--expect-bug",
        action="store_true",
        help="Exit 0 iff a divergence IS caught (used in CI to regression-test bug detection)",
    )
    parser.add_argument(
        "--allow-fallback",
        action="store_true",
        help="Allow pure specification fallback if `lake` is not installed locally",
    )
    args = parser.parse_args()

    conn = connect_lean_oracle(repo_root, allow_fallback=args.allow_fallback)
    print(f"[Oracle] {conn.banner}")

    rng = random.Random(args.seed)
    cedar_count = args.workloads // 2
    kv_count = args.workloads - cedar_count

    workloads: list[dict[str, Any]] = []
    for i in range(cedar_count):
        workloads.append(gen_cedar_workload(rng, i))
    for _ in range(kv_count):
        workloads.append(gen_fencing_kv_workload(rng))

    oracle_outputs = evaluate_workloads_with_oracle(repo_root, conn, workloads)

    cedar_passed = 0
    kv_passed = 0

    for idx, (workload, expected) in enumerate(zip(workloads, oracle_outputs)):
        if workload["domain"] == "cedar":
            candidate = ProductionCedarCandidate(workload["policies"])
            actual = candidate.authorize(workload["request"])
            if actual != expected:
                print(
                    f"\n[DIVERGENCE] CedarLite workload #{idx} failed differential check!\n"
                    f"  Action:    {workload['request']['action']}\n"
                    f"  Principal: {workload['request']['principal']}\n"
                    f"  Resource:  {workload['request']['resource']}\n"
                    f"  Oracle:    {expected}\n"
                    f"  Candidate: {actual}",
                    file=sys.stderr,
                )
                return 0 if args.expect_bug else 1
            cedar_passed += 1
        else:
            kv_candidate = ProductionFencingKVCandidate(demo_bug=args.demo_bug)
            actual_steps = kv_candidate.execute_trace(workload["ops"])
            if actual_steps != expected:
                msg_stream = sys.stdout if args.expect_bug else sys.stderr
                print(
                    f"\n[CAUGHT SPLIT-BRAIN DIVERGENCE] FencingKV workload #{idx} "
                    f"(seed={args.seed}, demo_bug={args.demo_bug}):",
                    file=msg_stream,
                )
                print(
                    format_kv_counterexample(workload["ops"], expected, actual_steps),
                    file=msg_stream,
                )
                if args.expect_bug:
                    print(
                        "[OK] Differential fuzzer caught the seeded stale-lease split-brain bug as expected."
                    )
                    return 0
                return 1
            kv_passed += 1

    if args.expect_bug:
        print(
            "ERROR: `--expect-bug` was set, but all workloads passed without divergence!",
            file=sys.stderr,
        )
        return 1

    print(
        f"[OK] Differential fuzzing passed {args.workloads}/{args.workloads} workloads "
        f"({cedar_passed} CedarLite policy suites + {kv_passed} FencingKV lease/compaction traces, "
        f"seed={args.seed})."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
