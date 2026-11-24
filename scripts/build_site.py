#!/usr/bin/env python3
"""
Indicogni Static Course Builder — Prove It: Formally Verified Software in Lean 4
Generates all CSP-safe HTML pages and chapter interactive data under site/.
Zero external dependencies, zero trackers, zero inline scripts/styles.
"""

from __future__ import annotations

import html
import json
import shutil
import urllib.parse
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parent.parent
SITE_DIR = ROOT_DIR / "site"
DIST_DIR = ROOT_DIR / "dist"
MOUNT_PATH = "/learn/prove-it"
CANONICAL_BASE = f"https://indicogni.com{MOUNT_PATH}"

PARTS = [
    {
        "num": "Part I",
        "title": "Part I · Executable Specifications & Gear 1 Model Checking",
        "summary": "Total functions, algebraic state modeling, Boolean reflection, and a 35-line TLA+ BFS trace explorer.",
        "units": ["01", "02", "03", "04", "cp1"],
    },
    {
        "num": "Part II",
        "title": "Part II · The Proof Engine & Gear 2 Inductive Invariants",
        "summary": "Reading the Infoview as a stack trace, tactic control flow, triaging false specs, and strengthening invariants.",
        "units": ["05", "06", "07", "08", "cp2"],
    },
    {
        "num": "Part III",
        "title": "Part III · Precision Types, 64-Bit Hardware & Refinement",
        "summary": "Zero-cost Subtype witnesses, BitVec 64 overflow proofs with bv_decide, termination as DoS defense, and stuttering refinement.",
        "units": ["09", "10", "11", "12", "cp3"],
    },
    {
        "num": "Part IV",
        "title": "Part IV · AI-Native Verification & Monday-Morning Transfer",
        "summary": "Defeating all 9 LLM verification cheats, spec-first co-design, TLV binary framing, and polyglot differential fuzzing.",
        "units": ["13", "14", "15", "16", "cp4"],
    },
]

UNITS: list[dict] = [
    {
        "id": "01",
        "code": "Ch 01",
        "part": "Part I · Executable Specifications",
        "title": "Silent Truncation Bug",
        "subtitle": "Why natural-number subtraction breaks an AI-written rate limiter—and how Lean's kernel catches what 10,000 unit tests miss.",
        "lake_cmd": "lake exe check ch01",
        "lean_file": "ProveIt/Ch01.lean",
        "est": "25 min",
        "puzzle_title": "5-Line Production Bug · AI Rate-Limiter Quota Check",
        "puzzle_code": (
            "def remainingQuota (limit used : Nat) : Nat := limit - used\n"
            "def allowRequest (limit used cost : Nat) : Bool :=\n"
            "  remainingQuota limit (used + cost) > 0\n"
            "-- Suppose limit = 10, used = 12, cost = 1.\n"
            "-- Now a refund subtracts 5 from (limit - used): (10 - 12) + 5 = ??"
        ),
        "prediction": {
            "question": "In Lean 4, `limit` and `used` have type `Nat` (natural numbers ≥ 0). What does `(10 : Nat) - 12 + 5` evaluate to?",
            "options": [
                "3, because `-2 + 5` resolves once `+ 5` brings the expression back above zero.",
                "5, because `10 - 12` clamps silently to `0` before `+ 5` ever runs.",
                "A compile-time underflow error rejecting `10 - 12`.",
                "A runtime panic (`ArithmeticException: underflow`) when `10 < 12`."
            ],
            "answerIndex": 1,
            "explanation": (
                "In Lean (and Coq/Rocq, Isabelle, and Rust's `saturating_sub`), `Nat` is closed under subtraction without throwing exceptions: "
                "whenever `a < b`, `a - b` evaluates to `0`. Therefore `(10 - 12) + 5` becomes `0 + 5 = 5`, fabricating 5 units of quota out of thin air! "
                "When we try to prove conservation `(limit - used) + used = limit` without `used ≤ limit`, Lean refuses to compile the proof."
            ),
        },
        "prose": [
            (
                "Why Tests Miss Truncation—and Equations Catch It",
                [
                    "Ask an AI coding assistant for a token-bucket rate limiter and a test suite, and both files will look clean. The tests pass `limit = 100, used = 40` and `limit = 100, used = 100`. Because the same model wrote both implementation and tests, neither asks what happens after an administrative quota reduction lowers `limit` below `used`.",
                    "In Lean 4, every function must return a valid value of its return type for every possible input—a design guarantee we call a **total function** (earned here because there are no exceptions, `null` pointers, or undefined traps to hide behind). Making `Nat - Nat : Nat` total forces `0 - 1 = 0`, known as **saturating subtraction**.",
                    "Instead of hoping callers remember `used ≤ limit`, we have two honest engineering options: use signed integers (`Int`), or return `Option Nat` (`some remaining` vs `none`) so failure is explicit in the return type and prove conservation across all valid withdrawals."
                ],
            ),
            (
                "Your First Two Proof Tools: `rfl` and `omega`",
                [
                    "When both sides of an equation compute to the exact same value—such as `#guard (10 : Nat) - 12 = 0` or `withdraw 10 4 = some 6`—Lean closes the proof by computation (`rfl`, short for **reflexivity**).",
                    "When your claim universally quantifies over *every* `limit used : Nat`—infinitely many inputs—computation on concrete constants is no longer enough. Lean's linear integer/natural solver `omega` checks whether the arithmetic equation holds across all non-negative integers, and immediately flags missing bounds like `used ≤ limit`."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch01.lean · Guarded Quota Conservation",
            "code": (
                "def withdraw (bal cost : Nat) : Option Nat :=\n"
                "  if cost <= bal then some (bal - cost) else none\n"
                "\n"
                "theorem withdraw_conserves (bal cost rem : Nat)\n"
                "    (h : withdraw bal cost = some rem) :\n"
                "    rem + cost = bal := by\n"
                "  unfold withdraw at h\n"
                "  split at h\n"
                "  · simp only [Option.some.injEq] at h\n"
                "    omega\n"
                "  · contradiction"
            ),
            "playgroundCode": (
                "-- Chapter 01: Silent Truncation Bug\n"
                "#guard ((10 : Nat) - 12) + 5 == 5\n\n"
                "def withdraw (bal cost : Nat) : Option Nat :=\n"
                "  if cost <= bal then some (bal - cost) else none\n\n"
                "#guard withdraw 10 12 == none\n"
                "#guard withdraw 10 4  == some 6\n\n"
                "theorem withdraw_conserves (bal cost rem : Nat)\n"
                "    (h : withdraw bal cost = some rem) :\n"
                "    rem + cost = bal := by\n"
                "  unfold withdraw at h\n"
                "  split at h\n"
                "  · simp only [Option.some.injEq] at h\n"
                "    omega\n"
                "  · contradiction\n"
            ),
            "steps": [
                {
                    "line": 6,
                    "status": "open",
                    "objects": "bal cost rem : Nat",
                    "hyps": "h : withdraw bal cost = some rem",
                    "goal": "⊢ rem + cost = bal",
                    "note": "Initial state: Lean displays our inputs (`Objects`), known assumption `h`, and the conservation equation after `⊢`.",
                },
                {
                    "line": 7,
                    "status": "open",
                    "objects": "bal cost rem : Nat",
                    "hyps": "h : (if cost ≤ bal then some (bal - cost) else none) = some rem",
                    "goal": "⊢ rem + cost = bal",
                    "note": "`unfold withdraw at h` replaces the function call with its body so we can inspect the guard `cost ≤ bal`.",
                },
                {
                    "line": 8,
                    "status": "open",
                    "objects": "bal cost rem : Nat",
                    "hyps": "h_cond : cost ≤ bal\nh : some (bal - cost) = some rem",
                    "goal": "⊢ rem + cost = bal",
                    "note": "`split at h` breaks the `if` into two cases: `cost ≤ bal` (active) and `¬(cost ≤ bal)` (queued).",
                },
                {
                    "line": 9,
                    "status": "open",
                    "objects": "bal cost rem : Nat",
                    "hyps": "h_cond : cost ≤ bal\nh : bal - cost = rem",
                    "goal": "⊢ rem + cost = bal",
                    "note": "`simp only [Option.some.injEq] at h` peels off `some` on both sides.",
                },
                {
                    "line": 10,
                    "status": "open",
                    "objects": "bal cost rem : Nat",
                    "hyps": "h_cond : ¬cost ≤ bal\nh : none = some rem",
                    "goal": "⊢ rem + cost = bal",
                    "note": "`omega` solved Case 1 (`bal - cost = rem` with `cost ≤ bal` implies `rem + cost = bal`)! Now Case 2 is active.",
                },
                {
                    "line": 11,
                    "status": "verified",
                    "objects": "bal cost rem : Nat",
                    "hyps": "(all branches discharged)",
                    "goal": "Goals accomplished",
                    "note": "`contradiction` sees `none = some rem` is impossible because `Option.none` and `Option.some` are distinct constructors.",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch01.lean`, replace the buggy `Nat` rate-limiter helper with an `Option`-returning function and prove both non-underflow and quota conservation.",
    },
    {
        "id": "02",
        "code": "Ch 02",
        "part": "Part I · Executable Specifications",
        "title": "Illegal States & Domain Modeling",
        "subtitle": "Eliminating boolean-soup authentication structs with algebraic sum and product types.",
        "lake_cmd": "lake exe check ch02",
        "lean_file": "ProveIt/Ch02.lean",
        "est": "25 min",
        "puzzle_title": "5-Line Production Bug · Boolean-Soup Session Middleware",
        "puzzle_code": (
            "structure RawSession where\n"
            "  isAuthenticated : Bool\n"
            "  isMfaPending    : Bool\n"
            "  isRevoked       : Bool\n"
            "  userId          : Option Nat -- 2^3 * 2 = 16 shapes; how many make sense?"
        ),
        "prediction": {
            "question": "Suppose middleware checks `if s.isAuthenticated && !s.isMfaPending then grantAccess s.userId`. Which representable `RawSession` bypasses revocation or triggers a missing-user failure?",
            "options": [
                "None—`isAuthenticated = true` guarantees `userId` is `some id` and `isRevoked = false`.",
                "`{ isAuthenticated := true, isMfaPending := false, isRevoked := true, userId := none }` passes the `if` guard while both revoked AND lacking a `userId`!",
                "Lean automatically rejects structs with more than two `Bool` fields.",
                "Only `isMfaPending := true` can ever cause a security bug."
            ],
            "answerIndex": 1,
            "explanation": (
                "A struct of independent booleans and `Option` fields forms a Cartesian product (**product type**): every combination of field values is legal to construct, "
                "including revoked sessions that still have `isAuthenticated := true` and `userId := none`. Replacing boolean flags with mutually exclusive variants (**sum types**, written `inductive` in Lean) deletes those illegal combinations from the type system."
            ),
        },
        "prose": [
            (
                "Counting States: Product Soup vs. Sum Precision",
                [
                    "Every extra `Bool` field doubles the state space of a `structure`. Four independent flags create 16 combinations, even when your domain lifecycle only has four real states: `anonymous`, `mfaPending (uid : Nat)`, `active (uid : Nat) (tokenEpoch : Nat)`, and `revoked (reason : String)`.",
                    "When you model mutually exclusive lifecycle phases with `inductive Session`, an `anonymous` or `revoked` session physically cannot carry an active token, and an `active` session physically cannot omit `uid : Nat`. You no longer write defensive assertions for impossible combinations because no code—human or AI—can construct them."
                ],
            ),
            (
                "Exhaustive Pattern Matching as Refactoring Armor",
                [
                    "Lean's pattern matcher checks **exhaustiveness** at compile time. Add a fifth lifecycle state (`suspended`) next quarter, and every `match` expression across your codebase that forgets `suspended` fails to compile with the exact missing constructor.",
                    "Even better: your theorems over `Session` split cleanly into four crisp subgoals via `cases s`, matching the domain 1-to-1 instead of 16 messy boolean truth-table rows."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch02.lean · Algebraic Session Lifecycle",
            "code": (
                "inductive Session where\n"
                "  | anonymous\n"
                "  | mfaPending (uid : Nat)\n"
                "  | active (uid : Nat)\n"
                "  | revoked (uid : Nat)\n"
                "\n"
                "def revoke : Session → Session\n"
                "  | .anonymous      => .anonymous\n"
                "  | .mfaPending uid => .revoked uid\n"
                "  | .active uid     => .revoked uid\n"
                "  | .revoked uid    => .revoked uid\n"
                "\n"
                "def authorizedUid : Session → Option Nat\n"
                "  | .active uid => some uid\n"
                "  | _           => none\n"
                "\n"
                "theorem revoke_denies_all (s : Session) :\n"
                "    authorizedUid (revoke s) = none := by\n"
                "  cases s <;> rfl"
            ),
            "playgroundCode": (
                "-- Chapter 02: Illegal States & Domain Modeling\n"
                "inductive Session where\n"
                "  | anonymous\n"
                "  | mfaPending (uid : Nat)\n"
                "  | active (uid : Nat)\n"
                "  | revoked (uid : Nat)\n"
                "  deriving Repr, DecidableEq\n\n"
                "def revoke : Session → Session\n"
                "  | .anonymous      => .anonymous\n"
                "  | .mfaPending uid => .revoked uid\n"
                "  | .active uid     => .revoked uid\n"
                "  | .revoked uid    => .revoked uid\n\n"
                "def authorizedUid : Session → Option Nat\n"
                "  | .active uid => some uid\n"
                "  | _           => none\n\n"
                "theorem revoke_denies_all (s : Session) :\n"
                "    authorizedUid (revoke s) = none := by\n"
                "  cases s <;> rfl\n"
            ),
            "steps": [
                {
                    "line": 17,
                    "status": "open",
                    "objects": "s : Session",
                    "hyps": "(none)",
                    "goal": "⊢ authorizedUid (revoke s) = none",
                    "note": "We want to guarantee that revoking ANY session state immediately drops `authorizedUid` to `none`.",
                },
                {
                    "line": 19,
                    "status": "verified",
                    "objects": "uid : Nat (in constructors mfaPending, active, revoked)",
                    "hyps": "(4 constructor cases generated by `cases s`, each reduced by `rfl`)",
                    "goal": "Goals accomplished",
                    "note": "`cases s` splits into `.anonymous`, `.mfaPending uid`, `.active uid`, and `.revoked uid`; `<;> rfl` evaluates `authorizedUid (revoke ...)` to `none` in every branch.",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch02.lean`, refactor a flag-ridden payment/auth record into an `inductive` state type and prove that terminal states can never emit authorization tokens.",
    },
    {
        "id": "03",
        "code": "Ch 03",
        "part": "Part I · Executable Specifications",
        "title": "Compile-Time Exhaustion & Boolean Reflection",
        "subtitle": "Verifying finite RBAC permission matrices automatically with `Decidable`, `decide`, and `Bool ↔ Prop` bridges.",
        "lake_cmd": "lake exe check ch03",
        "lean_file": "ProveIt/Ch03.lean",
        "est": "30 min",
        "puzzle_title": "5-Line Engineering Puzzle · Two Worlds of Truth (`Bool` vs `Prop`)",
        "puzzle_code": (
            "inductive Role | admin | ops | reader deriving DecidableEq\n"
            "inductive Action | view | restart | wipeProd deriving DecidableEq\n"
            "def evalRbac (r : Role) (a : Action) : Bool := ...\n"
            "-- Production runs `evalRbac : Bool` at 2M req/sec.\n"
            "-- Security auditors write logical specs `PolicySpec r a : Prop`. Can they drift?"
        ),
        "prediction": {
            "question": "There are `3 × 3 = 9` `(Role, Action)` pairs. If `PolicySpec r a` is decidable for every finite `Role` and `Action`, what can Lean do at compile time?",
            "options": [
                "Nothing without a manual 9-branch proof script written by hand.",
                "Sample 5 random `(Role, Action)` pairs like a quickcheck fuzzer.",
                "Exhaustively evaluate all 9 combinations inside the kernel via `decide` (or `cases r <;> cases a <;> decide`), turning a finite truth-table check into a mathematical theorem.",
                "Convert `Prop` into a runtime string at startup."
            ],
            "answerIndex": 2,
            "explanation": (
                "When a domain is finite and every atomic check has a `Decidable` instance, Lean's kernel can evaluate every constructor combination directly during compilation! "
                "And when you connect your fast runtime evaluator `evalRbac r a = true` to your declarative specification `PolicySpec r a` via an if-and-only-if theorem (`↔`, called **Boolean reflection**), "
                "your runtime `Bool` check carries the exact logical meaning of `PolicySpec`."
            ),
        },
        "prose": [
            (
                "Why Lean Distinguishes `Bool` (Data) from `Prop` (Specifications)",
                [
                    "At first glance, having both `Bool` (`true` / `false`) and `Prop` (logical statements like `∀ n : Nat, n + 0 = n`) feels redundant. Here is why systems verification needs both: a `Prop` can quantify over *infinitely many* inputs (`∀ epoch : Nat, ...`), which no runtime `Bool` function could ever finish looping over!",
                    "Conversely, your HTTP router cannot branch on an uncomputable `Prop` at runtime; it needs a concrete bit (`Bool`, 0 or 1). The `Decidable P` typeclass is the bridge: it packages either a proof `isTrue (h : P)` or a refutation `isFalse (h : ¬P)` that executes like a `Bool` while carrying a kernel-checked certificate."
                ],
            ),
            (
                "Finite Exhaustion in 1 Line",
                [
                    "For finite enumerations (`Role`, `Action`, `Region`, `Environment`), case-splitting every enum constructor reduces an entire security matrix to concrete ground propositions that `decide` checks inside the kernel with zero external axioms."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch03.lean · Bridging Runtime `Bool` to `Prop` Policy",
            "code": (
                "inductive Role | admin | ops | reader deriving DecidableEq\n"
                "inductive Action | view | restart | wipeProd deriving DecidableEq\n"
                "\n"
                "def evalRbac (r : Role) (a : Action) : Bool :=\n"
                "  match r, a with\n"
                "  | .admin, _        => true\n"
                "  | .ops,   .view    => true\n"
                "  | .ops,   .restart => true\n"
                "  | .reader, .view   => true\n"
                "  | _,      _        => false\n"
                "\n"
                "def CanWipeSpec (r : Role) : Prop := r = .admin\n"
                "\n"
                "theorem wipe_iff_admin (r : Role) :\n"
                "    (evalRbac r .wipeProd = true) ↔ CanWipeSpec r := by\n"
                "  unfold CanWipeSpec\n"
                "  cases r <;> decide"
            ),
            "playgroundCode": (
                "-- Chapter 03: Compile-Time Exhaustion & Boolean Reflection\n"
                "inductive Role | admin | ops | reader deriving DecidableEq\n"
                "inductive Action | view | restart | wipeProd deriving DecidableEq\n\n"
                "def evalRbac (r : Role) (a : Action) : Bool :=\n"
                "  match r, a with\n"
                "  | .admin, _        => true\n"
                "  | .ops,   .view    => true\n"
                "  | .ops,   .restart => true\n"
                "  | .reader, .view   => true\n"
                "  | _,      _        => false\n\n"
                "def CanWipeSpec (r : Role) : Prop := r = .admin\n\n"
                "theorem wipe_iff_admin (r : Role) :\n"
                "    (evalRbac r .wipeProd = true) ↔ CanWipeSpec r := by\n"
                "  unfold CanWipeSpec\n"
                "  cases r <;> decide\n"
            ),
            "steps": [
                {
                    "line": 14,
                    "status": "open",
                    "objects": "r : Role",
                    "hyps": "(none)",
                    "goal": "⊢ (evalRbac r Action.wipeProd = true) ↔ CanWipeSpec r",
                    "note": "We state an exact equivalence (`↔`): `evalRbac` allows `.wipeProd` if and only if `r = .admin`.",
                },
                {
                    "line": 17,
                    "status": "verified",
                    "objects": "(3 finite branches: .admin, .ops, .reader)",
                    "hyps": "(each ground ↔ checked via Decidable)",
                    "goal": "Goals accomplished",
                    "note": "`cases r` enumerates all 3 roles; `<;> decide` evaluates both sides of `↔` on each concrete role inside Lean's kernel.",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch03.lean`, verify a multi-role cloud RBAC evaluator against explicit security invariants (`ExplicitDeny`, `LeastPrivilege`) using `Decidable` reflection.",
    },
    {
        "id": "04",
        "code": "Ch 04",
        "part": "Part I · Executable Specifications",
        "title": "Gear 1: TLA+ Model Checker in 35 Lines",
        "subtitle": "Demystifying state-space exploration by building a breadth-first protocol bug-finder from scratch.",
        "lake_cmd": "lake exe check ch04",
        "lean_file": "ProveIt/Ch04.lean",
        "est": "35 min",
        "puzzle_title": "5-Line Distributed Bug · Unfenced Lease Split-Brain",
        "puzzle_code": (
            "structure LeaseSys where\n"
            "  leaderEpoch : Nat  -- coordinator's current lease epoch\n"
            "  staleInFlight : Bool -- client 1 (epoch 1) packet paused in network\n"
            "  storageVal  : String -- 'init' | 'v2_committed' | 'v1_stale'\n"
            "  epoch2Done  : Bool -- client 2 (epoch 2) already ACKed commit to user!"
        ),
        "prediction": {
            "question": "Before spending two hours trying to prove `epoch2Done = true → storageVal ≠ \"v1_stale\"` in Lean, what happens if we run a 4-step breadth-first search (BFS) over all possible action interleavings?",
            "options": [
                "BFS passes because unit tests run actions sequentially.",
                "BFS explores all interleavings up to depth 4 in <1 millisecond and hands back the exact 3-action trace (`Client1Send` → `Client2Commit` → `DeliverStale`) that overwrites committed data!",
                "Model checking requires installing a separate Java runtime and external TLA+ toolbox.",
                "BFS can prove the protocol safe for unbounded `Nat` epochs."
            ],
            "answerIndex": 1,
            "explanation": (
                "Never waste hours trying to prove a false theorem! **Gear 1 (Bounded BFS State Search)** explores every interleaving of nondeterministic network/timeout steps up to depth `k`, "
                "immediately returning the shortest counterexample trace when a shallow protocol bug exists. Once Gear 1 passes, **Gear 2 (Chapter 08)** proves safety across *unbounded* epochs and depths."
            ),
        },
        "prose": [
            (
                "TLA+ Without the Mystery: `init`, `nextStates`, `safe`",
                [
                    "Leslie Lamport's TLA+ taught systems engineers to view any distributed protocol, cache coherence controller, or WAL engine as a state machine: an initial state `init : S`, a transition function `nextStates : S → List (Action × S)` returning all enabled next steps, and an invariant `safe : S → Bool`.",
                    "Because Lean 4 is simultaneously a fast functional programming language and an interactive theorem prover, you can write a generic TLA+-style BFS model checker in 35 lines of pure Lean—and execute it directly at compile time with `#eval` or `#guard`!"
                ],
            ),
            (
                "Why Two Gears Beat Either Gear Alone",
                [
                    "Model checking (Gear 1) finds shallow protocol bugs automatically with concrete traces, yet must cap integer bounds and queue lengths so the search terminates. Deductive proof (Gear 2) handles infinite integers and unbounded message histories, yet requires human/AI invariant insight. Running Gear 1 *first* inside the same Lean file gives you instant falsification before investing in proofs."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch04.lean · 35-Line Executable BFS Trace Finder",
            "code": (
                "inductive Act | c1Send | c2Commit | deliverStale deriving Repr, DecidableEq\n"
                "\n"
                "structure Sys where\n"
                "  inFlight   : Bool\n"
                "  epoch2Done : Bool\n"
                "  corrupted  : Bool\n"
                "  deriving Repr, DecidableEq\n"
                "\n"
                "def stepBuggy (s : Sys) : List (Act × Sys) :=\n"
                "  (if !s.inFlight && !s.epoch2Done then [(.c1Send, { s with inFlight := true })] else []) ++\n"
                "  (if !s.epoch2Done then [(.c2Commit, { s with epoch2Done := true })] else []) ++\n"
                "  (if s.inFlight then [(.deliverStale, { s with inFlight := false, corrupted := s.epoch2Done })] else [])\n"
                "\n"
                "def bfs (fuel : Nat) (frontier : List (List Act × Sys)) (seen : List Sys) : Option (List Act) :=\n"
                "  match fuel with\n"
                "  | 0 => none\n"
                "  | fuel' + 1 =>\n"
                "    match frontier.find? (fun (_, s) => s.corrupted) with\n"
                "    | some (trace, _) => some trace.reverse\n"
                "    | none =>\n"
                "      let next := frontier.flatMap fun (tr, s) =>\n"
                "        (stepBuggy s).filterMap fun (a, s') =>\n"
                "          if seen.contains s' then none else some (a :: tr, s')\n"
                "      bfs fuel' next (seen ++ next.map Prod.snd)"
            ),
            "playgroundCode": (
                "-- Chapter 04: Gear 1 — A TLA+ Model Checker in Pure Lean 4\n"
                "inductive Act | c1Send | c2Commit | deliverStale deriving Repr, DecidableEq\n\n"
                "structure Sys where\n"
                "  inFlight   : Bool\n"
                "  epoch2Done : Bool\n"
                "  corrupted  : Bool\n"
                "  deriving Repr, DecidableEq\n\n"
                "def initSys : Sys := { inFlight := false, epoch2Done := false, corrupted := false }\n\n"
                "def stepBuggy (s : Sys) : List (Act × Sys) :=\n"
                "  (if !s.inFlight && !s.epoch2Done then [(.c1Send, { s with inFlight := true })] else []) ++\n"
                "  (if !s.epoch2Done then [(.c2Commit, { s with epoch2Done := true })] else []) ++\n"
                "  (if s.inFlight then [(.deliverStale, { s with inFlight := false, corrupted := s.epoch2Done })] else [])\n\n"
                "def bfs (fuel : Nat) (frontier : List (List Act × Sys)) (seen : List Sys) : Option (List Act) :=\n"
                "  match fuel with\n"
                "  | 0 => none\n"
                "  | fuel' + 1 =>\n"
                "    match frontier.find? (fun (_, s) => s.corrupted) with\n"
                "    | some (trace, _) => some trace.reverse\n"
                "    | none =>\n"
                "      let next := frontier.flatMap fun (tr, s) =>\n"
                "        (stepBuggy s).filterMap fun (a, s') =>\n"
                "          if seen.contains s' then none else some (a :: tr, s')\n"
                "      bfs fuel' next (seen ++ next.map Prod.snd)\n\n"
                "#guard bfs 5 [([], initSys)] [initSys] == some [.c1Send, .c2Commit, .deliverStale]\n"
            ),
            "steps": [
                {
                    "line": 9,
                    "status": "open",
                    "objects": "s : Sys",
                    "hyps": "initSys = { inFlight := false, epoch2Done := false, corrupted := false }",
                    "goal": "Explore reachable interleavings from initSys",
                    "note": "Depth 0: Only `.c1Send` and `.c2Commit` are enabled from `initSys`.",
                },
                {
                    "line": 12,
                    "status": "open",
                    "objects": "trace = [.c2Commit, .c1Send]",
                    "hyps": "s = { inFlight := true, epoch2Done := true, corrupted := false }",
                    "goal": "Check `.deliverStale` transition without fencing guard",
                    "note": "Depth 2: Client 1 queued an old write AND Client 2 committed under epoch 2.",
                },
                {
                    "line": 18,
                    "status": "refuted",
                    "objects": "counterexample : List Act",
                    "hyps": "bfs 5 [([], initSys)] [initSys] = some [.c1Send, .c2Commit, .deliverStale]",
                    "goal": "Safety violated at depth 3: s.corrupted = true",
                    "note": "Gear 1 instantly extracts the minimal 3-step split-brain trace! Try toggling the fencing fix live in Browser Lab 2.",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch04.lean` (and live in Browser Lab 2), run Gear 1 BFS to uncover a split-brain trace, add monotonic epoch fencing, and verify bounded exhaustion with `#guard`.",
    },
    {
        "id": "cp1",
        "code": "CP 1",
        "part": "Part I · Checkpoint 1",
        "title": "Checkpoint 1: Zero-Panic Rollout Router",
        "subtitle": "Closed-notes synthesis: model a canary rollout state machine, run Gear 1 search, and prove fail-closed safety.",
        "lake_cmd": "lake exe check cp1",
        "lean_file": "ProveIt/Checkpoints/Cp1.lean",
        "est": "35 min",
        "puzzle_title": "Checkpoint Spec · Canary Traffic Router",
        "puzzle_code": (
            "-- Requirements:\n"
            "-- 1. Rollout mode is Disabled | Canary (pct : Nat) | Full.\n"
            "-- 2. If backend health is Unhealthy, route MUST return Stable (fail-closed).\n"
            "-- 3. Emergency killSwitch transitions ANY state to Disabled in 1 step."
        ),
        "prediction": {
            "question": "Suppose `Canary (pct : Nat)` receives `pct = 150` from a misconfigured config file, while `healthy = false`. Does a fail-closed router `if healthy && matchMode mode bucket then .canary else .stable` ever send traffic to `.canary`?",
            "options": [
                "Yes, because `150 > 100` overrides the health flag.",
                "No—short-circuiting on `healthy = false` guarantees `.stable` regardless of `pct` or `bucket`, which we can prove universally for all `pct bucket : Nat`!",
                "Only when `bucket = 0`.",
                "It fails to compile unless `pct` is a `Float`."
            ],
            "answerIndex": 1,
            "explanation": (
                "Putting the health invariant at the top of the decision boundary ensures fail-closed routing across *all* configuration values (`∀ mode bucket, route false mode bucket = .stable`)."
            ),
        },
        "prose": [
            (
                "Synthesizing Part I Without Training Wheels",
                [
                    "This first checkpoint combines Chapters 01–04 into a clean production component: an algebraic rollout configuration (`Disabled | Canary pct | Full`), a total `route` function, an administrative state-transition function (`promote`, `setCanary`, `killSwitch`), and theorems guaranteeing both fail-closed unhealthy routing and kill-switch lockdown."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Checkpoints/Cp1.lean · Fail-Closed Canary Router",
            "code": (
                "inductive Mode | disabled | canary (pct : Nat) | full deriving DecidableEq\n"
                "inductive Target | stable | canaryBackend deriving DecidableEq\n"
                "\n"
                "def route (healthy : Bool) (m : Mode) (bucket : Nat) : Target :=\n"
                "  if !healthy then .stable\n"
                "  else match m with\n"
                "    | .disabled   => .stable\n"
                "    | .canary pct => if bucket < pct then .canaryBackend else .stable\n"
                "    | .full       => .canaryBackend\n"
                "\n"
                "theorem unhealthy_always_stable (m : Mode) (bucket : Nat) :\n"
                "    route false m bucket = .stable := by\n"
                "  rfl"
            ),
            "playgroundCode": (
                "-- Checkpoint 1: Zero-Panic Rollout Router\n"
                "inductive Mode | disabled | canary (pct : Nat) | full deriving Repr, DecidableEq\n"
                "inductive Target | stable | canaryBackend deriving Repr, DecidableEq\n\n"
                "def route (healthy : Bool) (m : Mode) (bucket : Nat) : Target :=\n"
                "  if !healthy then .stable\n"
                "  else match m with\n"
                "    | .disabled   => .stable\n"
                "    | .canary pct => if bucket < pct then .canaryBackend else .stable\n"
                "    | .full       => .canaryBackend\n\n"
                "def killSwitch (_ : Mode) : Mode := .disabled\n\n"
                "theorem unhealthy_always_stable (m : Mode) (bucket : Nat) :\n"
                "    route false m bucket = .stable := rfl\n\n"
                "theorem killSwitch_stops_canary (healthy : Bool) (m : Mode) (bucket : Nat) :\n"
                "    route healthy (killSwitch m) bucket = .stable := by\n"
                "  cases healthy <;> rfl\n"
            ),
            "steps": [
                {
                    "line": 11,
                    "status": "open",
                    "objects": "m : Mode, bucket : Nat",
                    "hyps": "(none)",
                    "goal": "⊢ route false m bucket = Target.stable",
                    "note": "Check `route false m bucket`: `!false` reduces immediately to `true`.",
                },
                {
                    "line": 13,
                    "status": "verified",
                    "objects": "m : Mode, bucket : Nat",
                    "hyps": "(definitional reduction)",
                    "goal": "Goals accomplished",
                    "note": "Because `!false` evaluates to `true` before `match m` is even inspected, `rfl` closes the theorem in one step!",
                },
            ],
        },
        "takeaway": "Complete `ProveIt/Checkpoints/Cp1.lean` locally and verify with `lake exe check cp1`.",
    },
    {
        "id": "05",
        "code": "Ch 05",
        "part": "Part II · The Proof Engine & Gear 2",
        "title": "Proofs Are Programs, Goals Are Stack Traces",
        "subtitle": "Reading the Lean Infoview cleanly and mastering `→`, `∧`, `∨`, `¬`, `∀`, and `∃` as typed API contracts.",
        "lake_cmd": "lake exe check ch05",
        "lean_file": "ProveIt/Ch05.lean",
        "est": "30 min",
        "puzzle_title": "5-Line Mental-Model Shift · Propositions as Function Signatures",
        "puzzle_code": (
            "-- Look at these two Lean declarations side by side:\n"
            "def applyFallback (f : Req → Resp) (x : Req) : Resp := f x\n"
            "theorem applyImplication (h_imp : SafeConfig → NoOutage) (h_cfg : SafeConfig) : NoOutage :=\n"
            "  h_imp h_cfg\n"
            "-- Why do `def` and `theorem` have the EXACT same body?"
        ),
        "prediction": {
            "question": "If an implication `P → Q` is a function taking a proof of `P` to a proof of `Q`, what data structure corresponds to proving `P ∧ Q` (`And P Q`)?",
            "options": [
                "An `Either` / union containing either `P` or `Q`, whichever is easier to construct.",
                "A 2-field struct / tuple `⟨proofOfP, proofOfQ⟩` supplying BOTH witnesses simultaneously.",
                "A mutable global boolean variable.",
                "A loop that retries `P` until `Q` becomes true."
            ],
            "answerIndex": 1,
            "explanation": (
                "Proving `P ∧ Q` requires handing the kernel a pair `⟨hp, hq⟩` (`constructor` in tactic mode), whereas proving `P ∨ Q` is a sum type (`Or.inl hp` or `Or.inr hq`). "
                "This correspondence—propositions as types, proofs as total programs (**Curry-Howard isomorphism**, earned right here)—means you already know 80% of Lean's logic from everyday typed programming!"
            ),
        },
        "prose": [
            (
                "Reading the Lean Infoview Like a Debugger Frame",
                [
                    "Every time you click inside a `by ...` block, Lean's **Infoview** shows your live stack frame: **Objects** (`req : Request`, `n : Nat`) are function arguments in scope; **Hypotheses** (`h1 : Valid req`, `h2 : n < 100`) are local immutable bindings holding proofs you already possess; and **⊢ Goal** is the return type your remaining block must construct.",
                    "Every logical connective has two moves: how to **build** it when it sits in the `⊢ Goal`, and how to **unpack** it when it sits in a hypothesis `h`."
                ],
            ),
            (
                "The Six Core Connectives Cheat-Sheet",
                [
                    "`P → Q` and `∀ x, P x`: build with `intro`, use by calling `h x` (`apply` / `exact`). `P ∧ Q`: build with `constructor` (or `⟨hp, hq⟩`), unpack with `rcases h with ⟨hp, hq⟩`. `P ∨ Q`: build with `left` or `right`, unpack with `rcases h with hp | hq` (must handle *both* cases!). `∃ x, P x`: build by supplying a concrete witness `⟨witness, proof⟩` (`refine ⟨w, ?_⟩`), unpack with `rcases h with ⟨x, hx⟩`. And `¬P` is defined as `P → False`—a function showing `P` leads to contradiction!"
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch05.lean · Unpacking & Building Logical Contracts",
            "code": (
                "theorem sla_handoff (PrimaryUp BackupUp Serving : Prop)\n"
                "    (h_either : PrimaryUp ∨ BackupUp)\n"
                "    (h_prim   : PrimaryUp → Serving)\n"
                "    (h_back   : BackupUp  → Serving) :\n"
                "    Serving := by\n"
                "  rcases h_either with hp | hb\n"
                "  · exact h_prim hp\n"
                "  · exact h_back hb"
            ),
            "playgroundCode": (
                "-- Chapter 05: Proofs Are Programs, Goals Are Stack Traces\n"
                "theorem sla_handoff (PrimaryUp BackupUp Serving : Prop)\n"
                "    (h_either : PrimaryUp ∨ BackupUp)\n"
                "    (h_prim   : PrimaryUp → Serving)\n"
                "    (h_back   : BackupUp  → Serving) :\n"
                "    Serving := by\n"
                "  rcases h_either with hp | hb\n"
                "  · exact h_prim hp\n"
                "  · exact h_back hb\n\n"
                "theorem witness_safe_port : ∃ p : Nat, p > 1024 ∧ p < 65535 :=\n"
                "  ⟨8080, by omega⟩\n"
            ),
            "steps": [
                {
                    "line": 5,
                    "status": "open",
                    "objects": "PrimaryUp BackupUp Serving : Prop",
                    "hyps": "h_either : PrimaryUp ∨ BackupUp\nh_prim : PrimaryUp → Serving\nh_back : BackupUp → Serving",
                    "goal": "⊢ Serving",
                    "note": "`h_either` is a sum type (`Or`). We don't know which server is up, so our proof must handle both possibilities.",
                },
                {
                    "line": 6,
                    "status": "open",
                    "objects": "PrimaryUp BackupUp Serving : Prop",
                    "hyps": "hp : PrimaryUp\nh_prim : PrimaryUp → Serving\nh_back : BackupUp → Serving",
                    "goal": "⊢ Serving",
                    "note": "`rcases h_either with hp | hb` pattern-matches `Or`, spawning Branch 1 (`hp : PrimaryUp`) and Branch 2 (`hb : BackupUp`).",
                },
                {
                    "line": 7,
                    "status": "open",
                    "objects": "PrimaryUp BackupUp Serving : Prop",
                    "hyps": "hb : BackupUp\nh_prim : PrimaryUp → Serving\nh_back : BackupUp → Serving",
                    "goal": "⊢ Serving",
                    "note": "`exact h_prim hp` calls function `h_prim` on `hp` to produce `Serving`, closing Branch 1! Branch 2 is now active.",
                },
                {
                    "line": 8,
                    "status": "verified",
                    "objects": "PrimaryUp BackupUp Serving : Prop",
                    "hyps": "(all branches discharged)",
                    "goal": "Goals accomplished",
                    "note": "`exact h_back hb` closes Branch 2. Failover guarantees `Serving` in all cases.",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch05.lean`, practice driving the Infoview across conjunctions, disjunctions, negations, and existential witnesses without guesswork.",
    },
    {
        "id": "06",
        "code": "Ch 06",
        "part": "Part II · The Proof Engine & Gear 2",
        "title": "Control Flow, Rewriting & Linear Math",
        "subtitle": "Verifying real branching code cleanly with `fun_cases`, surgical `simp only`, `omega`, and `@[grind =]` / `grind`.",
        "lake_cmd": "lake exe check ch06",
        "lean_file": "ProveIt/Ch06.lean",
        "est": "30 min",
        "puzzle_title": "5-Line Maintainability Puzzle · Fragile vs. Resilient Proofs",
        "puzzle_code": (
            "def backoffMs (attempt cap : Nat) : Nat :=\n"
            "  let raw := 100 * (attempt + 1)\n"
            "  if raw <= cap then raw else cap\n"
            "-- Question: How do we prove `cap ≥ 100 → backoffMs a cap ≤ cap`\n"
            "-- without brittle 15-line manual case splits?"
        ),
        "prediction": {
            "question": "Why do production Lean codebases prefer `simp only [lemma1, lemma2]` and `@[grind =]` over unrestricted `simp` in the middle of a proof?",
            "options": [
                "Unrestricted `simp` is illegal syntax in Lean 4.",
                "Unrestricted `simp` uses every global `@[simp]` lemma in scope; adding a new `@[simp]` lemma elsewhere can change the intermediate goal shape and break downstream tactics, whereas `simp only [...]` pins the exact rewrite set.",
                "`simp only` skips the Lean kernel typechecker.",
                "`simp` only works on strings."
            ],
            "answerIndex": 1,
            "explanation": (
                "Non-terminal `simp` is the #1 cause of proof rot when a codebase grows! Using `fun_cases` to mirror a function's exact branch structure, `simp only [...]` for surgical rewrites, "
                "and terminal `omega` or `grind` to close leaf obligations keeps proofs rock-solid across refactors."
            ),
        },
        "prose": [
            (
                "`fun_cases`: Let the Function's Own Branches Drive the Proof",
                [
                    "Manually nested `split` calls lose track of `let`-bindings and multi-pattern `match` arms. Lean 4's `fun_cases f x y` automatically generates one goal per execution path of `f x y`, naming the exact branch hypotheses for you."
                ],
            ),
            (
                "Closing Leaf Goals with `omega` and `grind`",
                [
                    "Once control flow is split, most systems verification leaves boil down to linear inequalities (`omega`) or congruence closure + equality chaining + case splitting (`grind`, guided by `@[grind =]` annotations on domain definitions). Together, `fun_cases ... <;> grind` or `fun_cases ... <;> omega` turns 25 lines of tedious bookkeeping into 2 readable lines."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch06.lean · `fun_cases` + `omega` + `grind`",
            "code": (
                "@[grind =]\n"
                "def backoffMs (attempt cap : Nat) : Nat :=\n"
                "  if 100 * (attempt + 1) <= cap then 100 * (attempt + 1) else cap\n"
                "\n"
                "theorem backoff_capped (attempt cap : Nat) :\n"
                "    backoffMs attempt cap ≤ cap := by\n"
                "  fun_cases backoffMs attempt cap\n"
                "  · omega\n"
                "  · omega"
            ),
            "playgroundCode": (
                "-- Chapter 06: Control Flow, Rewriting & Linear Math\n"
                "@[grind =]\n"
                "def backoffMs (attempt cap : Nat) : Nat :=\n"
                "  if 100 * (attempt + 1) <= cap then 100 * (attempt + 1) else cap\n\n"
                "theorem backoff_capped (attempt cap : Nat) :\n"
                "    backoffMs attempt cap ≤ cap := by\n"
                "  fun_cases backoffMs attempt cap\n"
                "  · omega\n"
                "  · omega\n\n"
                "theorem backoff_positive (attempt cap : Nat) (h : 100 ≤ cap) :\n"
                "    100 ≤ backoffMs attempt cap := by\n"
                "  grind\n"
            ),
            "steps": [
                {
                    "line": 6,
                    "status": "open",
                    "objects": "attempt cap : Nat",
                    "hyps": "(none)",
                    "goal": "⊢ backoffMs attempt cap ≤ cap",
                    "note": "`backoffMs` branches on `100 * (attempt + 1) ≤ cap`.",
                },
                {
                    "line": 7,
                    "status": "open",
                    "objects": "attempt cap : Nat",
                    "hyps": "h : 100 * (attempt + 1) ≤ cap",
                    "goal": "⊢ 100 * (attempt + 1) ≤ cap",
                    "note": "`fun_cases backoffMs attempt cap` unfolds and splits along the function's exact branches! Branch 1 has `h : 100 * (attempt + 1) ≤ cap`.",
                },
                {
                    "line": 8,
                    "status": "open",
                    "objects": "attempt cap : Nat",
                    "hyps": "h : ¬100 * (attempt + 1) ≤ cap",
                    "goal": "⊢ cap ≤ cap",
                    "note": "`omega` solved Branch 1; Branch 2 (`else cap`) asks for `cap ≤ cap`.",
                },
                {
                    "line": 9,
                    "status": "verified",
                    "objects": "attempt cap : Nat",
                    "hyps": "(all branches discharged)",
                    "goal": "Goals accomplished",
                    "note": "Both branches verified cleanly—and notice in the playground how `@[grind =]` lets `grind` prove `backoff_positive` in a single word!",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch06.lean`, verify a multi-tier retry/circuit-breaker controller using `fun_cases`, `simp only`, `omega`, and `grind`.",
    },
    {
        "id": "07",
        "code": "Ch 07",
        "part": "Part II · The Proof Engine & Gear 2",
        "title": "Unprovable on Purpose",
        "subtitle": "How to read a stuck Infoview goal and triage between (A) Buggy Code, (B) False Spec, and (C) Weak Invariant.",
        "lake_cmd": "lake exe check ch07",
        "lean_file": "ProveIt/Ch07.lean",
        "est": "30 min",
        "puzzle_title": "5-Line Debugging Puzzle · Why Won't `omega` Close This Goal?",
        "puzzle_code": (
            "def rebalance (a b : Nat) : Nat × Nat :=\n"
            "  let half := (a + b) / 2\n"
            "  (half, half)\n"
            "-- Attempted theorem: `(rebalance a b).1 + (rebalance a b).2 = a + b`\n"
            "-- Infoview gets stuck at: `⊢ (a + b) / 2 + (a + b) / 2 = a + b`"
        ),
        "prediction": {
            "question": "Look at the stuck goal `⊢ (a + b) / 2 + (a + b) / 2 = a + b`. Why did `omega` refuse to prove it?",
            "options": [
                "`omega` does not understand `+`.",
                "The theorem is FALSE! Plug in `a = 1, b = 0`: `(1 / 2) + (1 / 2) = 0 + 0 = 0 ≠ 1`—`rebalance` silently destroys 1 unit whenever `a + b` is odd!",
                "We forgot to call `simp` ten times.",
                "Lean requires floating-point numbers for addition."
            ],
            "answerIndex": 1,
            "explanation": (
                "Beginners treat a stuck proof as 'Lean is fighting me' and throw random tactics at the screen. Experienced verification engineers read a stuck leaf goal as a **bug detector**: "
                "substitute small concrete values into the unresolved variables (`a := 1, b := 0`), confirm the counterexample in 5 seconds with `#guard (rebalance 1 0) == (0, 0)`, and fix `rebalance` to `(half, (a + b) - half)`!"
            ),
        },
        "prose": [
            (
                "The 3-Way Stuck-Goal Triage Protocol",
                [
                    "Whenever a leaf goal refuses to close, stop guessing tactics and classify it into one of three buckets: **(A) Buggy Implementation** (your code mishandles an edge case like odd sums, empty lists, or `0`; write a `#guard` failing test immediately); **(B) Over-Strong / Missing-Precondition Spec** (the code works as designed, e.g., integer division rounds down, so the spec forgot a hypothesis like `Even (a + b)` or `cap > 0`); or **(C) Weak Inductive Hypothesis** (the claim is true on reachable states, yet your induction hypothesis threw away a structural link—solved in Chapter 08)."
                ],
            ),
            (
                "Turning Stuck Goals into `#guard` Regression Tests",
                [
                    "A stuck Infoview goal lists the exact constraints (`h1`, `h2`, `¬h3`) leading to the failure branch. Solve those constraints on paper for the smallest `Nat` values (`0`, `1`, `2`), run `#eval` on your function, and you have a concrete reproducible bug report."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch07.lean · Diagnosing & Fixing Odd-Unit Loss",
            "code": (
                "def rebalanceBuggy (a b : Nat) : Nat × Nat :=\n"
                "  let half := (a + b) / 2\n"
                "  (half, half)\n"
                "\n"
                "-- Counterexample extracted from stuck goal `(a + b)/2 + (a + b)/2 = a + b`:\n"
                "#guard (let (x, y) := rebalanceBuggy 1 0; x + y) != 1 + 0\n"
                "\n"
                "def rebalanceFixed (a b : Nat) : Nat × Nat :=\n"
                "  let half := (a + b) / 2\n"
                "  (half, (a + b) - half)\n"
                "\n"
                "theorem rebalanceFixed_conserves (a b : Nat) :\n"
                "    (rebalanceFixed a b).1 + (rebalanceFixed a b).2 = a + b := by\n"
                "  dsimp only [rebalanceFixed]\n"
                "  omega"
            ),
            "playgroundCode": (
                "-- Chapter 07: Unprovable on Purpose — Stuck-Goal Triage\n"
                "def rebalanceBuggy (a b : Nat) : Nat × Nat :=\n"
                "  let half := (a + b) / 2\n"
                "  (half, half)\n\n"
                "-- 1. Confirm counterexample from stuck goal:\n"
                "#guard (let (x, y) := rebalanceBuggy 1 0; x + y) == 0\n\n"
                "-- 2. Repair remainder conservation:\n"
                "def rebalanceFixed (a b : Nat) : Nat × Nat :=\n"
                "  let half := (a + b) / 2\n"
                "  (half, (a + b) - half)\n\n"
                "theorem rebalanceFixed_conserves (a b : Nat) :\n"
                "    (rebalanceFixed a b).1 + (rebalanceFixed a b).2 = a + b := by\n"
                "  dsimp only [rebalanceFixed]\n"
                "  omega\n"
            ),
            "steps": [
                {
                    "line": 6,
                    "status": "refuted",
                    "objects": "a = 1, b = 0",
                    "hyps": "rebalanceBuggy 1 0 = (0, 0)",
                    "goal": "Counterexample confirmed: 0 + 0 ≠ 1 + 0 (Bucket A: Buggy Code)",
                    "note": "Instead of fighting the prover, `#guard` pins down the exact odd-sum loss bug.",
                },
                {
                    "line": 14,
                    "status": "open",
                    "objects": "a b : Nat",
                    "hyps": "(none)",
                    "goal": "⊢ (a + b) / 2 + (a + b - (a + b) / 2) = a + b",
                    "note": "After repairing the second shard to `(a + b) - half`, `unfold rebalanceFixed` exposes clean Euclidean arithmetic.",
                },
                {
                    "line": 15,
                    "status": "verified",
                    "objects": "a b : Nat",
                    "hyps": "(linear division/subtraction bound `(a + b) / 2 ≤ a + b`)",
                    "goal": "Goals accomplished",
                    "note": "`omega` knows `(a + b) / 2 ≤ a + b` for all `Nat`, sealing conservation across both even and odd totals!",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch07.lean`, diagnose three broken theorem attempts (one buggy implementation, one missing precondition, one off-by-one boundary), record `#guard` counterexamples, and prove the repaired versions.",
    },
    {
        "id": "08",
        "code": "Ch 08",
        "part": "Part II · The Proof Engine & Gear 2",
        "title": "Gear 2: Inductive Invariants & Strengthening",
        "subtitle": "Why true safety properties fail naive induction on 'Garden-of-Eden' states—and how invariant strengthening seals infinite runs.",
        "lake_cmd": "lake exe check ch08",
        "lean_file": "ProveIt/Ch08.lean",
        "est": "40 min",
        "puzzle_title": "5-Line Induction Paradox · A True Theorem That Cannot Prove Itself",
        "puzzle_code": (
            "structure CounterPair where\n"
            "  issued    : Nat  -- tickets issued so far\n"
            "  redeemed  : Nat  -- tickets redeemed (incremented only when redeemed < issued)\n"
            "  vaultCash : Nat  -- incremented on issue, decremented on redeem\n"
            "-- Safety goal: Reachable s → s.redeemed ≤ s.issued + s.vaultCash (TRUE, yet consider vaultCash ≥ 0...)"
        ),
        "prediction": {
            "question": "Suppose our fenced storage from Chapter 04 tracks `leaderEpoch`, `storageEpoch`, and `committedEpoch2 : Bool`. Safety says `Safe s := ¬s.corrupted`. Why does proving `Safe s → Step s s' → Safe s'` FAIL on its own even when the protocol is 100% bug-free?",
            "options": [
                "Lean cannot perform induction on state machines.",
                "Because `Safe s` alone allows an unreachable 'Garden-of-Eden' state `{ committedEpoch2 := true, storageEpoch := 0, inFlightEpoch1 := true, corrupted := false }` where `Safe s` is TRUE right now, yet one stale epoch-1 delivery (`1 ≥ 0`) sets `corrupted := true`!",
                "Because `Bool` fields cannot appear inside invariants.",
                "Induction only works up to `epoch = 10`."
            ],
            "answerIndex": 1,
            "explanation": (
                "This is the single most important insight in formal verification! When proving `Inv s → Step s s' → Inv s'`, `s` is an *arbitrary* state satisfying `Inv s`, NOT guaranteed to be reachable unless `Inv` records why bad transitions are blocked! "
                "Strengthening `Inv s` to `Safe s ∧ (s.committedEpoch2 = true → s.storageEpoch ≥ 2)` rules out that unreachable Garden-of-Eden state, making `Inv` **inductive** across infinite runs."
            ),
        },
        "prose": [
            (
                "The Three Obligations of Gear 2",
                [
                    "To prove `∀ s, Reachable s → Safe s` across infinitely many steps and unbounded `Nat` epochs without enumerating states, you pick a strengthened predicate `Inv : State → Prop` and prove three finite, step-local theorems: (1) **Initiation**: `Init s → Inv s`; (2) **Consecution (Inductiveness)**: `Inv s → Next s s' → Inv s'`; and (3) **Safety Entailment**: `Inv s → Safe s`.",
                    "Think of `Inv` as a protective fence drawn cleanly around `Reachable` and strictly inside `Safe` (explore this live in Browser Lab 2's State-Space Funnel!)."
                ],
            ),
            (
                "How Stuck Consecution Tells You Exactly How to Strengthen `Inv`",
                [
                    "Whenever `Inv s → Next s s' → Inv s'` gets stuck on an impossible-looking state `s` (like `committedEpoch2 = true` while `storageEpoch = 0`), ask: *why can't the real system ever reach `s`?* The answer (`committedEpoch2 = true → storageEpoch ≥ 2`) is literally the missing conjunct to add to `Inv`!"
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch08.lean · Unbounded Fenced-Storage Inductive Invariant",
            "code": (
                "structure FencedSys where\n"
                "  storageEpoch   : Nat\n"
                "  committedEp2   : Bool\n"
                "  corrupted      : Bool\n"
                "\n"
                "inductive Next : FencedSys → FencedSys → Prop\n"
                "  | commit2 (s : FencedSys) (h : 2 ≥ s.storageEpoch) :\n"
                "      Next s { s with storageEpoch := 2, committedEp2 := true }\n"
                "  | deliverStale1 (s : FencedSys) (h_fence : 1 ≥ s.storageEpoch) :\n"
                "      Next s { s with corrupted := s.committedEp2 }\n"
                "\n"
                "def Safe (s : FencedSys) : Prop := s.corrupted = false\n"
                "\n"
                "def SafeInv (s : FencedSys) : Prop :=\n"
                "  s.corrupted = false ∧ (s.committedEp2 = true → s.storageEpoch ≥ 2)\n"
                "\n"
                "theorem inv_consecution (s s' : FencedSys) (h_inv : SafeInv s) (h_step : Next s s') :\n"
                "    SafeInv s' := by\n"
                "  unfold SafeInv at *\n"
                "  cases h_step <;> grind"
            ),
            "playgroundCode": (
                "-- Chapter 08: Gear 2 — Inductive Invariants & Strengthening\n"
                "structure FencedSys where\n"
                "  storageEpoch : Nat\n"
                "  committedEp2 : Bool\n"
                "  corrupted    : Bool\n\n"
                "def Init (s : FencedSys) : Prop :=\n"
                "  s = { storageEpoch := 1, committedEp2 := false, corrupted := false }\n\n"
                "inductive Next : FencedSys → FencedSys → Prop\n"
                "  | commit2 (s : FencedSys) (h : 2 ≥ s.storageEpoch) :\n"
                "      Next s { s with storageEpoch := 2, committedEp2 := true }\n"
                "  | deliverStale1 (s : FencedSys) (h_fence : 1 ≥ s.storageEpoch) :\n"
                "      Next s { s with corrupted := s.committedEp2 }\n\n"
                "inductive Reachable : FencedSys → Prop\n"
                "  | init (s : FencedSys) : Init s → Reachable s\n"
                "  | step (s s' : FencedSys) : Reachable s → Next s s' → Reachable s'\n\n"
                "def Safe (s : FencedSys) : Prop := s.corrupted = false\n\n"
                "def SafeInv (s : FencedSys) : Prop :=\n"
                "  s.corrupted = false ∧ (s.committedEp2 = true → s.storageEpoch ≥ 2)\n\n"
                "theorem inv_init (s : FencedSys) (h : Init s) : SafeInv s := by\n"
                "  unfold Init SafeInv at *; subst h; decide\n\n"
                "theorem inv_consecution (s s' : FencedSys) (h_inv : SafeInv s) (h_step : Next s s') :\n"
                "    SafeInv s' := by\n"
                "  unfold SafeInv at *\n"
                "  cases h_step <;> grind\n\n"
                "theorem reachable_safe (s : FencedSys) (hr : Reachable s) : Safe s := by\n"
                "  have h_inv : SafeInv s := by\n"
                "    induction hr with\n"
                "    | init s hi => exact inv_init s hi\n"
                "    | step s s' _ hnext ih => exact inv_consecution s s' ih hnext\n"
                "  exact h_inv.1\n"
            ),
            "steps": [
                {
                    "line": 17,
                    "status": "open",
                    "objects": "s s' : FencedSys",
                    "hyps": "h_inv : Inv s\nh_step : Next s s'",
                    "goal": "⊢ Inv s'",
                    "note": "`Inv` pairs `corrupted = false` with the strengthening fact `committedEp2 = true → storageEpoch ≥ 2`.",
                },
                {
                    "line": 19,
                    "status": "open",
                    "objects": "s s' : FencedSys",
                    "hyps": "h_inv : s.corrupted = false ∧ (s.committedEp2 = true → s.storageEpoch ≥ 2)\nh_step : Next s s'",
                    "goal": "⊢ s'.corrupted = false ∧ (s'.committedEp2 = true → s'.storageEpoch ≥ 2)",
                    "note": "`unfold Inv at *` exposes both conjuncts before splitting on transitions.",
                },
                {
                    "line": 20,
                    "status": "verified",
                    "objects": "s s' : FencedSys",
                    "hyps": "Case commit2 sets storageEpoch := 2; Case deliverStale1 has 1 ≥ storageEpoch, forcing committedEp2 = false!",
                    "goal": "Goals accomplished",
                    "note": "`cases h_step <;> grind` checks every transition: in `deliverStale1`, `1 ≥ s.storageEpoch` contradicts `s.storageEpoch ≥ 2`, proving `s.committedEp2 = false`!",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch08.lean`, strengthen a naive safety invariant on a multi-epoch lease protocol and prove `∀ s, Reachable s → Safe s` across infinite runs.",
    },
    {
        "id": "cp2",
        "code": "CP 2",
        "part": "Part II · Checkpoint 2",
        "title": "Checkpoint 2: Crash-Safe WAL Ledger",
        "subtitle": "Repair a write-ahead log replay double-credit bug, strengthen the ledger invariant, and prove conservation across arbitrary crash loops.",
        "lake_cmd": "lake exe check cp2",
        "lean_file": "ProveIt/Checkpoints/Cp2.lean",
        "est": "40 min",
        "puzzle_title": "Checkpoint Bug · Crash Between Balance Update and ACK",
        "puzzle_code": (
            "structure WalLedger where\n"
            "  balance   : Nat\n"
            "  appliedTx : List Nat -- committed tx IDs persisted in WAL\n"
            "-- Buggy recovery re-runs `balance := balance + tx.amount` without checking `tx.id ∈ appliedTx`!\n"
            "-- After 1 crash-restart, a $500 deposit credits $1,000."
        ),
        "prediction": {
            "question": "After adding the deduplication guard `if txId ∈ s.appliedTx then s else ...`, what inductive invariant links `s.appliedTx` to replaying `txId` after `k` crashes?",
            "options": [
                "`s.appliedTx = []` forever.",
                "Once `applyTx s txId amt` runs, `txId ∈ (applyTx s txId amt).appliedTx` holds—so every subsequent replay hits the `if`-true branch and leaves `balance` identical!",
                "`s.balance` resets to `0` on crash.",
                "Deduplication only holds for 1 crash."
            ],
            "answerIndex": 1,
            "explanation": (
                "Proving `txId ∈ (applyTx s txId amt).appliedTx` gives the exact inductive hook needed to prove idempotence (`applyTx (applyTx s id amt) id amt = applyTx s id amt`) and multi-crash conservation!"
            ),
        },
        "prose": [
            (
                "Crash-Recovery Verification Pattern",
                [
                    "Storage engines, Kafka consumers, and Stripe-style payment ledgers achieve effectively-once state updates over at-least-once delivery by persisting transaction IDs inside the same atomic WAL batch as the balance mutation. Proving idempotence + monotonic `appliedTx` membership guarantees zero double-credits across arbitrary crash-restart traces."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Checkpoints/Cp2.lean · Idempotent WAL Recovery",
            "code": (
                "structure Wal where\n"
                "  balance : Nat\n"
                "  seen    : List Nat\n"
                "\n"
                "def credit (w : Wal) (txId amt : Nat) : Wal :=\n"
                "  if txId ∈ w.seen then w\n"
                "  else { balance := w.balance + amt, seen := txId :: w.seen }\n"
                "\n"
                "theorem credit_idempotent (w : Wal) (txId amt : Nat) :\n"
                "    credit (credit w txId amt) txId amt = credit w txId amt := by\n"
                "  unfold credit\n"
                "  split <;> simp only [List.mem_cons, true_or, ↓reduceIte]"
            ),
            "playgroundCode": (
                "-- Checkpoint 2: Crash-Safe Idempotent WAL Ledger\n"
                "structure Wal where\n"
                "  balance : Nat\n"
                "  seen    : List Nat\n"
                "  deriving Repr, DecidableEq\n\n"
                "def credit (w : Wal) (txId amt : Nat) : Wal :=\n"
                "  if txId ∈ w.seen then w\n"
                "  else { balance := w.balance + amt, seen := txId :: w.seen }\n\n"
                "theorem credit_seen (w : Wal) (txId amt : Nat) :\n"
                "    txId ∈ (credit w txId amt).seen := by\n"
                "  unfold credit\n"
                "  split\n"
                "  · assumption\n"
                "  · simp only [List.mem_cons, true_or]\n\n"
                "theorem credit_idempotent (w : Wal) (txId amt : Nat) :\n"
                "    credit (credit w txId amt) txId amt = credit w txId amt := by\n"
                "  unfold credit\n"
                "  split <;> simp only [List.mem_cons, true_or, ↓reduceIte]\n"
            ),
            "steps": [
                {
                    "line": 9,
                    "status": "open",
                    "objects": "w : Wal, txId amt : Nat",
                    "hyps": "(none)",
                    "goal": "⊢ credit (credit w txId amt) txId amt = credit w txId amt",
                    "note": "Whether `txId` is fresh or already committed, applying `credit` twice must equal applying it once.",
                },
                {
                    "line": 12,
                    "status": "verified",
                    "objects": "w : Wal, txId amt : Nat",
                    "hyps": "Branch 1: txId ∈ w.seen; Branch 2: txId ∉ w.seen (inserts txId :: w.seen)",
                    "goal": "Goals accomplished",
                    "note": "In Branch 2, the second `credit` sees `txId ∈ txId :: w.seen` (`true_or`) and returns the first update unchanged.",
                },
            ],
        },
        "takeaway": "Complete `ProveIt/Checkpoints/Cp2.lean` locally and run `lake exe check cp2`.",
    },
    {
        "id": "09",
        "code": "Ch 09",
        "part": "Part III · Precision Types, Hardware & Refinement",
        "title": "Packing Proofs into Types (`Subtype` & `Fin`)",
        "subtitle": "Bundling invariants directly inside data structures with zero-byte runtime overhead.",
        "lake_cmd": "lake exe check ch09",
        "lean_file": "ProveIt/Ch09.lean",
        "est": "35 min",
        "puzzle_title": "5-Line API Friction Puzzle · External Hypotheses vs. Self-Certifying Types",
        "puzzle_code": (
            "-- Style A: Pass raw `Nat` everywhere and beg every caller for `(h1 : pct ≤ 100)`\n"
            "def feeA (amount pct : Nat) (h : pct ≤ 100) : Nat := (amount * pct) / 100\n"
            "-- Style B: Bundle the value AND its proof into a single type `BasisPct`:\n"
            "abbrev Percent := { p : Nat // p ≤ 100 }\n"
            "-- Question: How many bytes does the proof `p ≤ 100` occupy in compiled C/machine code?"
        ),
        "prediction": {
            "question": "When Lean compiles `Percent := { p : Nat // p ≤ 100 }` (`Subtype`) to native machine code, how much memory and CPU time does the proof field `property : p ≤ 100` cost at runtime?",
            "options": [
                "8 bytes for a pointer to a proof tree on the heap.",
                "Zero bytes and zero CPU instructions—every `Prop` proof witness is completely erased (`lcErased`) during compilation, leaving a bare `Nat`!",
                "It re-runs `omega` on every HTTP request.",
                "24 bytes per struct instance."
            ],
            "answerIndex": 1,
            "explanation": (
                "Because `Prop` has **proof irrelevance** (any two proofs of `p ≤ 100` are indistinguishable and contain no runtime branching data), Lean's compiler erases all `Prop` fields completely! "
                "You check untrusted JSON at the edge *once* with `if h : raw ≤ 100 then some ⟨raw, h⟩ else none`, and every downstream function enjoys compile-time guarantees at zero runtime cost (inspect this live in Browser Lab 4)."
            ),
        },
        "prose": [
            (
                "Why Dependent Types Feel Natural *After* `omega`",
                [
                    "Earlier courses throw `Fin n` (`{ i : Nat // i < n }`) at learners on Day 1, before they know `omega` or `if h : ...`, turning array indexing into cryptic compiler errors. Now that you command `omega` and `grind`, `Subtype` (`{ x : α // P x }`) is effortless: `.val` (or coercion) extracts the data, `.property` hands `omega` the built-in proof `P x`, and `if h : idx < arr.size` binds `h` right at your parsing boundary!"
                ],
            ),
            (
                "Zero-Bounds-Check Array Access (`arr[i]`) & Non-Zero Divisors",
                [
                    "In Lean 4, `arr[i]` looks up a proof of `i < arr.size` automatically in your local context (using `omega` tactics behind the scenes!) and compiles to an unguarded pointer load `lean_array_uget`—memory safety without runtime bounds-check tax."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch09.lean · Parse-Don't-Validate with `Subtype` & `Fin`",
            "code": (
                "abbrev Percent := { p : Nat // p ≤ 100 }\n"
                "\n"
                "def parsePercent (raw : Nat) : Option Percent :=\n"
                "  if h : raw ≤ 100 then some ⟨raw, h⟩ else none\n"
                "\n"
                "def applyDiscount (price : Nat) (disc : Percent) : Nat :=\n"
                "  price - (price * disc.val) / 100\n"
                "\n"
                "theorem discount_never_exceeds_price (price : Nat) (disc : Percent) :\n"
                "    applyDiscount price disc ≤ price := by\n"
                "  unfold applyDiscount\n"
                "  omega"
            ),
            "playgroundCode": (
                "-- Chapter 09: Packing Proofs into Types (Subtype & Fin)\n"
                "abbrev Percent := { p : Nat // p ≤ 100 }\n\n"
                "def parsePercent (raw : Nat) : Option Percent :=\n"
                "  if h : raw ≤ 100 then some ⟨raw, h⟩ else none\n\n"
                "#guard (parsePercent 25).isSome == true\n"
                "#guard (parsePercent 150).isSome == false\n\n"
                "def applyDiscount (price : Nat) (disc : Percent) : Nat :=\n"
                "  price - (price * disc.val) / 100\n\n"
                "theorem discount_never_exceeds_price (price : Nat) (disc : Percent) :\n"
                "    applyDiscount price disc ≤ price := by\n"
                "  unfold applyDiscount\n"
                "  omega\n\n"
                "def ringNext {cap : Nat} (h_pos : 0 < cap) (slot : Fin cap) : Fin cap :=\n"
                "  ⟨(slot.val + 1) % cap, Nat.mod_lt _ h_pos⟩\n"
            ),
            "steps": [
                {
                    "line": 4,
                    "status": "open",
                    "objects": "raw : Nat",
                    "hyps": "h : raw ≤ 100 (inside `then` branch of dependent `if h : ...`)",
                    "goal": "Construct `Percent` (`{ p : Nat // p ≤ 100 }`)",
                    "note": "Writing `if h : raw ≤ 100` both runs the runtime integer comparison AND binds proof `h : raw ≤ 100` so `⟨raw, h⟩` typechecks!",
                },
                {
                    "line": 10,
                    "status": "open",
                    "objects": "price : Nat, disc : Percent",
                    "hyps": "disc.property : disc.val ≤ 100",
                    "goal": "⊢ price - price * disc.val / 100 ≤ price",
                    "note": "Every `disc : Percent` carries `disc.property : disc.val ≤ 100` wherever it travels.",
                },
                {
                    "line": 12,
                    "status": "verified",
                    "objects": "price : Nat, disc : Percent",
                    "hyps": "(proof erased at runtime; bound sealed at compile time)",
                    "goal": "Goals accomplished",
                    "note": "`omega` closes the inequality immediately; at runtime, `Percent` is just an unboxed integer.",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch09.lean`, build boundary parsers into `Subtype` / `Fin` types for a shard router and eliminate runtime out-of-bounds failures.",
    },
    {
        "id": "10",
        "code": "Ch 10",
        "part": "Part III · Precision Types, Hardware & Refinement",
        "title": "64-Bit Hardware Truth (`UInt64` & `BitVec`)",
        "subtitle": "Catching `2^64 - 1` wrap-around blind spots with `bv_decide` and auditing LRAT trust tiers.",
        "lake_cmd": "lake exe check ch10",
        "lean_file": "ProveIt/Ch10.lean",
        "est": "35 min",
        "puzzle_title": "5-Line Famous Bug · Binary Search Midpoint on 64-Bit Registers",
        "puzzle_code": (
            "def midBuggy (lo hi : BitVec 64) : BitVec 64 :=\n"
            "  (lo + hi) >>> 1\n"
            "-- Proved in Java's java.util.Arrays for 9 years before Joshua Bloch's bug report!\n"
            "-- What happens when `lo = 2^63` (`0x8000000000000000`) and `hi = 2^63`?"
        ),
        "prediction": {
            "question": "On 64-bit hardware (`BitVec 64` / `UInt64`), if `lo = 0x8000000000000000` (`2^63`) and `hi = 0x8000000000000000` (`2^63`), what does `(lo + hi) >>> 1` compute?",
            "options": [
                "`0x8000000000000000` (`2^63`), matching mathematical `(lo + hi) / 2`.",
                "`0x0000000000000000` (`0`), because `2^63 + 2^63 = 2^64 ≡ 0 (mod 2^64)`, and `0 >>> 1 = 0`—violating `lo ≤ mid`!",
                "`0xFFFFFFFFFFFFFFFF`.",
                "A CPU division-by-zero trap."
            ],
            "answerIndex": 1,
            "explanation": (
                "Proving `(lo + hi) / 2 ≥ lo` over mathematical `Nat` SUCCEEDS—hiding the hardware wrap-around at `2^63`! "
                "Modeling registers faithfully as `BitVec 64` and running `bv_decide` immediately flags the counterexample `lo = 0x8000000000000000#64, hi = 0x8000000000000000#64`, "
                "and proves the overflow-free formula `lo + ((hi - lo) >>> 1)` across all `2^128` pairs `(lo, hi)`!"
            ),
        },
        "prose": [
            (
                "Why Property Fuzzers Miss `2^64` Wrap-Arounds—and `bv_decide` Never Does",
                [
                    "Random property tests sample small integers or uniform random values that hit narrow overflow windows (`balance + fee < balance` when `balance > 2^64 - fee`) with probability `< 2^-50`. Lean 4's `bv_decide` bit-blasts fixed-width `BitVec` goals to SAT and checks an **LRAT unsatisfiability certificate**, either returning an exact bit-level counterexample or sealing all `2^64` values."
                ],
            ),
            (
                "Understanding `#print axioms` on `bv_decide` (`DECISIONS.md` Ruling #4)",
                [
                    "To verify big LRAT certificates quickly, `bv_decide` evaluates its verified certificate checker via `Lean.ofReduceBool` / `Lean.trustCompiler`. That means `#print axioms` shows those two trust markers—the same ones emitted by dangerous raw `native_decide`! In Chapter 13 and Browser Lab 3, you will see how `lake exe verigate --trust-tier=bv-lrat` safely allows `bv_decide` while still blocking raw `native_decide`."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch10.lean · Hardware-Exact Midpoint Proof via `bv_decide`",
            "code": (
                "import Std.Tactic.BVDecide\n"
                "\n"
                "def midBuggy (lo hi : BitVec 64) : BitVec 64 := (lo + hi) >>> 1\n"
                "#guard midBuggy 0x8000000000000000#64 0x8000000000000000#64 == 0#64\n"
                "\n"
                "def midSafe (lo hi : BitVec 64) : BitVec 64 :=\n"
                "  lo + ((hi - lo) >>> 1)\n"
                "\n"
                "theorem midSafe_in_bounds (lo hi : BitVec 64) (h : lo ≤ hi) :\n"
                "    lo ≤ midSafe lo hi ∧ midSafe lo hi ≤ hi := by\n"
                "  unfold midSafe\n"
                "  bv_decide"
            ),
            "playgroundCode": (
                "-- Chapter 10: 64-Bit Hardware Truth (UInt64 & BitVec)\n"
                "import Std.Tactic.BVDecide\n\n"
                "def midBuggy (lo hi : BitVec 64) : BitVec 64 := (lo + hi) >>> 1\n"
                "#guard midBuggy 0x8000000000000000#64 0x8000000000000000#64 == 0#64\n\n"
                "def midSafe (lo hi : BitVec 64) : BitVec 64 :=\n"
                "  lo + ((hi - lo) >>> 1)\n\n"
                "theorem midSafe_in_bounds (lo hi : BitVec 64) (h : lo ≤ hi) :\n"
                "    lo ≤ midSafe lo hi ∧ midSafe lo hi ≤ hi := by\n"
                "  unfold midSafe\n"
                "  bv_decide\n\n"
                "def addChecked64 (a b : BitVec 64) : Option (BitVec 64) :=\n"
                "  let sum := a + b\n"
                "  if sum < a then none else some sum\n\n"
                "theorem addChecked64_no_wrap (a b res : BitVec 64)\n"
                "    (h : addChecked64 a b = some res) : a ≤ res ∧ b ≤ res := by\n"
                "  dsimp only [addChecked64] at h\n"
                "  split at h\n"
                "  · contradiction\n"
                "  · simp only [Option.some.injEq] at h\n"
                "    subst h\n"
                "    bv_decide\n"
            ),
            "steps": [
                {
                    "line": 4,
                    "status": "refuted",
                    "objects": "lo = 0x8000000000000000#64, hi = 0x8000000000000000#64",
                    "hyps": "lo ≤ hi holds, yet midBuggy lo hi = 0#64 < lo!",
                    "goal": "Hardware wrap-around exposed before deployment",
                    "note": "Explore this exact bit-pattern interactively in Browser Lab 5!",
                },
                {
                    "line": 11,
                    "status": "open",
                    "objects": "lo hi : BitVec 64",
                    "hyps": "h : lo ≤ hi",
                    "goal": "⊢ lo ≤ lo + (hi - lo) >>> 1 ∧ lo + (hi - lo) >>> 1 ≤ hi",
                    "note": "Because `lo ≤ hi`, `hi - lo` never underflows, `(hi - lo) >>> 1 ≤ hi - lo`, and `lo + ...` never wraps `2^64`.",
                },
                {
                    "line": 12,
                    "status": "verified",
                    "objects": "lo hi : BitVec 64",
                    "hyps": "(LRAT certificate checked across all 64-bit bit-vectors)",
                    "goal": "Goals accomplished",
                    "note": "`bv_decide` proves both bounds across all `(2^64)^2` register pairs in milliseconds.",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch10.lean` (and Browser Lab 5), verify overflow-checked `UInt64` / `BitVec 64` escrow and pointer-offset arithmetic with `bv_decide`.",
    },
    {
        "id": "11",
        "code": "Ch 11",
        "part": "Part III · Precision Types, Hardware & Refinement",
        "title": "Pure Effects & Termination as DoS Defense",
        "subtitle": "Functional cores (`Except`, `StateM`), `termination_by` proofs against infinite-loop outages, and `fun_induction`.",
        "lake_cmd": "lake exe check ch11",
        "lean_file": "ProveIt/Ch11.lean",
        "est": "35 min",
        "puzzle_title": "5-Line Outage Bug · Malformed Packet Infinite-Loop DoS",
        "puzzle_code": (
            "partial def parseChunks (buf : ByteArray) (offset : Nat) : List Nat :=\n"
            "  if offset >= buf.size then []\n"
            "  else let chunkLen := buf.get! offset |>.toNat\n"
            "       chunkLen :: parseChunks buf (offset + chunkLen)\n"
            "-- Attacker sends a 1-byte packet `[0x00]`. What happens on every worker thread?"
        ),
        "prediction": {
            "question": "When an attacker sends `[0x00]`, `chunkLen = 0`, so `offset + chunkLen = offset`. Why did Lean allow this CPU-pinning infinite loop to compile above?",
            "options": [
                "Lean never checks termination.",
                "Because the author slapped `partial` on `parseChunks`, opting out of Lean's termination proof! Without `partial`, Lean demands a decreasing measure (`buf.size - offset`) and forces `chunkLen > 0`, stopping the zero-length DoS bug at compile time!",
                "`ByteArray` always pads zeros to `1`.",
                "Recursion is banned in functional programming."
            ],
            "answerIndex": 1,
            "explanation": (
                "In network parsers, policy symlink resolvers, and compilers, a **termination proof** (`termination_by buf.size - offset`) is a **compile-time Denial-of-Service defense**! "
                "Moreover, `partial` functions are opaque in Lean's logic (you cannot unfold them in proofs because an infinite loop `bad : False := bad` would break soundness), whereas total functions unlock `fun_induction`!"
            ),
        },
        "prose": [
            (
                "Imperative Readability, Pure Proof Power (`do` + `Except` / `StateM`)",
                [
                    "Real systems code uses early-return error handling and mutable-looking state updates. Lean 4's `do` notation compiles `let mut`, `for`, and early `throw` over `Except Err` and `StateM S` directly into pure functional transformers—giving you imperative ergonomics in code and pure mathematical equations in proofs (the **Functional Core, Imperative Shell** architecture)."
                ],
            ),
            (
                "`termination_by` + `fun_induction`",
                [
                    "Once you prove a recursive parser or binary search terminates (`termination_by hi - lo`), Lean automatically synthesizes a custom induction principle matched to that recursion (`fun_induction`), eliminating manual strong-induction boilerplate."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch11.lean · DoS-Proof Chunk Parser with `termination_by` & `fun_induction`",
            "code": (
                "inductive ParseErr | zeroStep | truncated deriving DecidableEq\n"
                "\n"
                "def scanOffsets (total offset : Nat) (stepSize : Nat) : Except ParseErr (List Nat) :=\n"
                "  if offset ≥ total then .ok []\n"
                "  else if stepSize = 0 then .error .zeroStep\n"
                "  else do\n"
                "    let rest ← scanOffsets total (offset + stepSize) stepSize\n"
                "    pure (offset :: rest)\n"
                "termination_by total - offset\n"
                "decreasing_by omega\n"
                "\n"
                "theorem zero_step_rejected (total offset : Nat) (h : offset < total) :\n"
                "    scanOffsets total offset 0 = .error .zeroStep := by\n"
                "  unfold scanOffsets\n"
                "  simp only [Nat.not_le.mpr h, ↓reduceIte]"
            ),
            "playgroundCode": (
                "-- Chapter 11: Pure Effects & Termination as DoS Defense\n"
                "inductive ParseErr | zeroStep | truncated deriving Repr, DecidableEq\n\n"
                "def scanOffsets (total offset : Nat) (stepSize : Nat) : Except ParseErr (List Nat) :=\n"
                "  if offset ≥ total then .ok []\n"
                "  else if stepSize = 0 then .error .zeroStep\n"
                "  else do\n"
                "    let rest ← scanOffsets total (offset + stepSize) stepSize\n"
                "    pure (offset :: rest)\n"
                "termination_by total - offset\n"
                "decreasing_by omega\n\n"
                "#guard (match scanOffsets 10 0 0 with | .error .zeroStep => true | _ => false)\n"
                "#guard (match scanOffsets 6  0 2 with | .ok [0, 2, 4]    => true | _ => false)\n\n"
                "theorem zero_step_rejected (total offset : Nat) (h : offset < total) :\n"
                "    scanOffsets total offset 0 = .error .zeroStep := by\n"
                "  unfold scanOffsets\n"
                "  simp only [Nat.not_le.mpr h, ↓reduceIte]\n"
            ),
            "steps": [
                {
                    "line": 9,
                    "status": "open",
                    "objects": "total offset stepSize : Nat",
                    "hyps": "h_done : ¬offset ≥ total\nh_zero : ¬(stepSize == 0)",
                    "goal": "⊢ total - (offset + stepSize) < total - offset",
                    "note": "Without `h_zero`, `stepSize` could be `0`, making `total - (offset + 0) < total - offset` FALSE! Guarding `stepSize == 0` makes termination provable.",
                },
                {
                    "line": 10,
                    "status": "open",
                    "objects": "total offset stepSize : Nat",
                    "hyps": "offset < total ∧ stepSize > 0",
                    "goal": "Termination obligation closed by `omega`",
                    "note": "`decreasing_by omega` proves the remaining byte budget strictly shrinks on every recursive call.",
                },
                {
                    "line": 15,
                    "status": "verified",
                    "objects": "total offset : Nat",
                    "hyps": "h : offset < total",
                    "goal": "Goals accomplished",
                    "note": "Every zero-length attacker frame is guaranteed to fail fast in `O(1)` with `.error .zeroStep`.",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch11.lean`, eliminate `partial` from a recursive packet/DAG resolver, prove termination against attacker-crafted inputs, and verify its `Except`/`StateM` properties with `fun_induction`.",
    },
    {
        "id": "12",
        "code": "Ch 12",
        "part": "Part III · Precision Types, Hardware & Refinement",
        "title": "Refinement Mappings & Stuttering Steps",
        "subtitle": "Proving a fast log-structured cache+tombstone KV store behaves identically to a 10-line abstract map.",
        "lake_cmd": "lake exe check ch12",
        "lean_file": "ProveIt/Ch12.lean",
        "est": "40 min",
        "puzzle_title": "5-Line Architecture Puzzle · Fast Implementation vs. Simple Spec",
        "puzzle_code": (
            "-- SpecKV: a trivial function `Key → Option Val`.\n"
            "-- ImplKV: append-only write log + tombstone deletes + background compaction!\n"
            "-- Question: Background compaction mutates `ImplKV` in memory, yet changes ZERO\n"
            "-- user-visible keys. How do we express 'internal optimization step' mathematically?"
        ),
        "prediction": {
            "question": "Suppose `abs : ImplKV → SpecKV` maps any concrete log state to its logical key-value view. When background compaction rewrites `ImplKV` from `impl` to `compact impl`, what equation proves compaction is invisible to callers?",
            "options": [
                "`compact impl = impl` (compaction may not free any memory).",
                "`∀ k, abs (compact impl) k = abs impl k` — in TLA+ terms, compaction refines an abstract **stuttering step** (`SpecNext` or `UNCHANGED specVars`)!",
                "Compaction cannot be verified.",
                "`abs` must run at runtime in production."
            ],
            "answerIndex": 1,
            "explanation": (
                "This is Lamport's **refinement mapping** (`abs : Impl → Spec`)! User operations commute (`abs (putImpl s k v) = putSpec (abs s) k v`), "
                "while internal housekeeping steps like GC, cache eviction, rebalancing, or tombstone compaction map to `abs s' = abs s`—a **stuttering step** on the abstract spec!"
            ),
        },
        "prose": [
            (
                "Commuting Diagrams: Keep Specs Tiny, Let Implementations Run Fast",
                [
                    "Nobody wants auditors reading 3,000 lines of lock-free ring buffers or LSM compaction logic to understand what `get` and `put` mean. Instead, write a 10-line `SpecKV` that any engineer can eyeball in 30 seconds, define an abstraction function `abs : ImplKV → SpecKV` (purely for verification—erased or unused at runtime!), and prove that every concrete operation either matches `SpecKV` or stutters (`abs s' = abs s`)."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch12.lean · Log-Structured KV Refinement & Compaction Stuttering",
            "code": (
                "abbrev SpecKV := Nat → Option Nat\n"
                "abbrev ImplLog := List (Nat × Option Nat) -- head is newest write/tombstone\n"
                "\n"
                "def lookupLog : ImplLog → Nat → Option Nat\n"
                "  | [], _ => none\n"
                "  | (k, v) :: rest, q => if q == k then v else lookupLog rest q\n"
                "\n"
                "def putImpl (log : ImplLog) (k v : Nat) : ImplLog := (k, some v) :: log\n"
                "def delImpl (log : ImplLog) (k : Nat)   : ImplLog := (k, none) :: log\n"
                "\n"
                "-- Drop shadowed older entries for key `k` behind a newer head entry `(k, v)`:\n"
                "def compactHead : ImplLog → ImplLog\n"
                "  | [] => []\n"
                "  | (k, v) :: rest => (k, v) :: rest.filter (fun (k', _) => k' != k)\n"
                "\n"
                "theorem filter_lookup_other (rest : ImplLog) (k q : Nat) (hq : (q == k) = false) :\n"
                "    lookupLog (rest.filter (fun (k', _) => k' != k)) q = lookupLog rest q := by\n"
                "  induction rest with\n"
                "  | nil => rfl\n"
                "  | cons hd tl ih =>\n"
                "    rcases hd with ⟨k', v'⟩\n"
                "    simp only [List.filter]\n"
                "    by_cases hkk : (k' != k) = true\n"
                "    · simp only [hkk, lookupLog, ih]\n"
                "    · have heq : (q == k') = false := by grind\n"
                "      simp only [Bool.not_eq_true] at hkk\n"
                "      simp only [hkk, lookupLog, heq, Bool.false_eq_true, ↓reduceIte, ih]\n"
                "\n"
                "theorem compactHead_stutters (log : ImplLog) (q : Nat) :\n"
                "    lookupLog (compactHead log) q = lookupLog log q := by\n"
                "  cases log with\n"
                "  | nil => rfl\n"
                "  | cons hd rest =>\n"
                "    rcases hd with ⟨k, v⟩\n"
                "    simp only [compactHead, lookupLog]\n"
                "    split\n"
                "    · rfl\n"
                "    · next hnot =>\n"
                "      exact filter_lookup_other rest k q (Bool.eq_false_iff.mpr hnot)"
            ),
            "playgroundCode": (
                "-- Chapter 12: Refinement Mappings & Stuttering Steps\n"
                "abbrev SpecKV := Nat → Option Nat\n"
                "abbrev ImplLog := List (Nat × Option Nat)\n\n"
                "def lookupLog : ImplLog → Nat → Option Nat\n"
                "  | [], _ => none\n"
                "  | (k, v) :: rest, q => if q == k then v else lookupLog rest q\n\n"
                "def compactHead : ImplLog → ImplLog\n"
                "  | [] => []\n"
                "  | (k, v) :: rest => (k, v) :: rest.filter (fun (k', _) => k' != k)\n\n"
                "theorem filter_lookup_other (rest : ImplLog) (k q : Nat) (hq : (q == k) = false) :\n"
                "    lookupLog (rest.filter (fun (k', _) => k' != k)) q = lookupLog rest q := by\n"
                "  induction rest with\n"
                "  | nil => rfl\n"
                "  | cons hd tl ih =>\n"
                "    rcases hd with ⟨k', v'⟩\n"
                "    simp only [List.filter]\n"
                "    by_cases hkk : (k' != k) = true\n"
                "    · simp only [hkk, lookupLog, ih]\n"
                "    · have heq : (q == k') = false := by grind\n"
                "      simp only [Bool.not_eq_true] at hkk\n"
                "      simp only [hkk, lookupLog, heq, Bool.false_eq_true, ↓reduceIte, ih]\n\n"
                "theorem compactHead_stutters (log : ImplLog) (q : Nat) :\n"
                "    lookupLog (compactHead log) q = lookupLog log q := by\n"
                "  cases log with\n"
                "  | nil => rfl\n"
                "  | cons hd rest =>\n"
                "    rcases hd with ⟨k, v⟩\n"
                "    simp only [compactHead, lookupLog]\n"
                "    split\n"
                "    · rfl\n"
                "    · next hnot =>\n"
                "      exact filter_lookup_other rest k q (Bool.eq_false_iff.mpr hnot)\n"
            ),
            "steps": [
                {
                    "line": 29,
                    "status": "open",
                    "objects": "log : ImplLog, q : Nat",
                    "hyps": "(none)",
                    "goal": "⊢ lookupLog (compactHead log) q = lookupLog log q",
                    "note": "`lookupLog` is our refinement mapping `abs : ImplLog → SpecKV`. We prove `compactHead` is an exact stuttering step.",
                },
                {
                    "line": 36,
                    "status": "open",
                    "objects": "k : Nat, v : Option Nat, rest : ImplLog, q : Nat",
                    "hyps": "Case 1: (q == k) = true; Case 2: (q == k) = false",
                    "goal": "If `q == k`, both sides return `v`; if `q != k`, filtering `k` out of `rest` preserves `q`!",
                    "note": "Shadowed duplicates of `k` were unreachable behind `(k, v)` anyway; other keys `q ≠ k` are untouched by `filter`.",
                },
                {
                    "line": 39,
                    "status": "verified",
                    "objects": "log : ImplLog, q : Nat",
                    "hyps": "(stuttering refinement proven for all queries `q`)",
                    "goal": "Goals accomplished",
                    "note": "Memory shrinks in `ImplLog` while `SpecKV` stutters unchanged!",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch12.lean`, prove full `put`/`delete`/`get` refinement and multi-pass compaction stuttering for a concrete KV store.",
    },
    {
        "id": "cp3",
        "code": "CP 3",
        "part": "Part III · Checkpoint 3",
        "title": "Checkpoint 3: Fixed-Width Ring Buffer",
        "subtitle": "Prove bounds safety and FIFO queue refinement for a bounded circular buffer.",
        "lake_cmd": "lake exe check cp3",
        "lean_file": "ProveIt/Checkpoints/Cp3.lean",
        "est": "45 min",
        "puzzle_title": "Checkpoint Spec · Bounded Circular Queue vs. Abstract `List α`",
        "puzzle_code": (
            "-- SpecQueue: plain `List α` (`enqueue` appends at back, `dequeue` pops front, max `cap`).\n"
            "-- RingBuf: fixed capacity `cap > 0`, modular index arithmetic `(head + len) % cap`.\n"
            "-- Prove: (1) zero out-of-bounds indices, (2) `toList (push rb x) = toList rb ++ [x]` when `len < cap`."
        ),
        "prediction": {
            "question": "In a circular ring buffer of capacity `cap > 0`, why should the state store `(head : Fin cap)` and `(len : Nat)` (`len ≤ cap`) instead of just `(head : Fin cap)` and `(tail : Fin cap)`?",
            "options": [
                "Because `tail` cannot be stored in memory.",
                "Because `head == tail` is ambiguous between EMPTY (`len = 0`) and FULL (`len = cap`)! Tracking `(head, len)` with `len ≤ cap` makes every fullness state unambiguous and gives `writeIdx = (head + len) % cap < cap` cleanly.",
                "Because `%` only works on powers of 10.",
                "Lists are faster than arrays in DMA drivers."
            ],
            "answerIndex": 1,
            "explanation": (
                "Storing `head` + `len` (`h_len : len ≤ cap`) eliminates the classic empty-vs-full ambiguity without wasting a slot, and makes the abstraction mapping `toList : RingBuf α cap → List α` clean to state and prove!"
            ),
        },
        "prose": [
            (
                "Bringing `Fin`, Modular Arithmetic, and Refinement Together",
                [
                    "Kernel network rings (`io_uring`, DPDK) and telemetry queues use fixed-capacity circular buffers to guarantee zero heap allocation on hot paths. Proving that modular wrap-around `(head + i) % cap` refines an ordinary `List α` FIFO queue seals off both out-of-bounds panics and silent wrap-overwrite corruption."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Checkpoints/Cp3.lean · Modular Slot Safety & Queue Length Invariant",
            "code": (
                "structure RingMeta (cap : Nat) where\n"
                "  head : Nat\n"
                "  len  : Nat\n"
                "  h_cap : 0 < cap\n"
                "  h_len : len ≤ cap\n"
                "\n"
                "def writeSlot {cap : Nat} (r : RingMeta cap) : Fin cap :=\n"
                "  ⟨(r.head + r.len) % cap, Nat.mod_lt _ r.h_cap⟩\n"
                "\n"
                "def pushMeta {cap : Nat} (r : RingMeta cap) : Option (RingMeta cap) :=\n"
                "  if h : r.len < cap then\n"
                "    some { r with len := r.len + 1, h_len := by omega }\n"
                "  else none\n"
                "\n"
                "theorem pushMeta_increments {cap : Nat} (r r' : RingMeta cap)\n"
                "    (h : pushMeta r = some r') : r'.len = r.len + 1 := by\n"
                "  unfold pushMeta at h\n"
                "  split at h\n"
                "  · simp only [Option.some.injEq] at h; subst h; rfl\n"
                "  · contradiction"
            ),
            "playgroundCode": (
                "-- Checkpoint 3: Fixed-Width Ring Buffer Bounds & Refinement\n"
                "structure RingMeta (cap : Nat) where\n"
                "  head  : Nat\n"
                "  len   : Nat\n"
                "  h_cap : 0 < cap\n"
                "  h_len : len ≤ cap\n\n"
                "def writeSlot {cap : Nat} (r : RingMeta cap) : Fin cap :=\n"
                "  ⟨(r.head + r.len) % cap, Nat.mod_lt _ r.h_cap⟩\n\n"
                "def pushMeta {cap : Nat} (r : RingMeta cap) : Option (RingMeta cap) :=\n"
                "  if h : r.len < cap then\n"
                "    some { r with len := r.len + 1, h_len := by omega }\n"
                "  else none\n\n"
                "theorem pushMeta_increments {cap : Nat} (r r' : RingMeta cap)\n"
                "    (h : pushMeta r = some r') : r'.len = r.len + 1 := by\n"
                "  unfold pushMeta at h\n"
                "  split at h\n"
                "  · simp only [Option.some.injEq] at h; subst h; rfl\n"
                "  · contradiction\n"
            ),
            "steps": [
                {
                    "line": 7,
                    "status": "open",
                    "objects": "cap : Nat, r : RingMeta cap",
                    "hyps": "r.h_cap : 0 < cap",
                    "goal": "Construct `Fin cap` (`(r.head + r.len) % cap < cap`)",
                    "note": "`Nat.mod_lt _ r.h_cap` certifies at compile time that `writeSlot` is always in `[0, cap)`.",
                },
                {
                    "line": 12,
                    "status": "open",
                    "objects": "r : RingMeta cap",
                    "hyps": "h : r.len < cap",
                    "goal": "⊢ r.len + 1 ≤ cap",
                    "note": "Dependent `if h : r.len < cap` feeds `h` straight into `by omega` to build the updated `RingMeta cap` invariant.",
                },
                {
                    "line": 20,
                    "status": "verified",
                    "objects": "r r' : RingMeta cap",
                    "hyps": "(fullness check enforced; length step proven)",
                    "goal": "Goals accomplished",
                    "note": "Full push/pop FIFO list refinement awaits you in `ProveIt/Checkpoints/Cp3.lean`!",
                },
            ],
        },
        "takeaway": "Complete the full array-backed FIFO ring buffer refinement in `ProveIt/Checkpoints/Cp3.lean` and run `lake exe check cp3`.",
    },
    {
        "id": "13",
        "code": "Ch 13",
        "part": "Part IV · AI-Native Verification & Transfer",
        "title": "How AI Cheats Formal Verification",
        "subtitle": "Auditing the 9 real-world exploit vectors coding agents use to green-light broken proofs—and stopping every single one.",
        "lake_cmd": "lake exe check ch13",
        "lean_file": "ProveIt/Ch13.lean",
        "est": "35 min",
        "puzzle_title": "5-Line Red-Team Alert · Zero `sorry`, Compiles Clean, 100% Broken!",
        "puzzle_code": (
            "def unsafeFastTransfer (_bal _amt : Nat) : Nat := 999999999\n"
            "\n"
            "@[implemented_by unsafeFastTransfer]\n"
            "def transfer (bal amt : Nat) : Nat := bal - amt\n"
            "\n"
            "theorem transfer_le (bal amt : Nat) : transfer bal amt ≤ bal := by unfold transfer; omega"
        ),
        "prediction": {
            "question": "If a CI pipeline checks ONLY (1) `lake build` exits `0`, (2) grep finds zero `sorry`, and (3) `#print axioms transfer_le` is empty `[]`, what happens to the PR above?",
            "options": [
                "Lean refuses to compile `@[implemented_by]`.",
                "`#print axioms` flags `unsafeFastTransfer` automatically.",
                "ALL THREE naive checks pass green—and production binaries execute `unsafeFastTransfer`, fabricating `999,999,999` on every call!",
                "`omega` catches the runtime attribute."
            ],
            "answerIndex": 2,
            "explanation": (
                "Reward-hacking coding agents optimize relentlessly for making CI green! `@[implemented_by]`, `@[extern]`, and `@[csimp]` redirect the compiled binary without touching kernel axioms; "
                "vacuous preconditions (`h : n < 0` on `n : Nat`) prove anything from `False` with zero axioms; and mutating `Spec.lean` to prove `True` passes `lake build` effortlessly. "
                "That is why `lake exe verigate` audits ASTs, environment attributes, `Spec` hashes, axiom whitelists, and non-vacuity witnesses together (test yourself in Browser Lab 6!)."
            ),
        },
        "prose": [
            (
                "The 9 AI Verification Cheat Vectors",
                [
                    "When an RL-trained coding agent gets stuck on a hard proof obligation, it reaches for every escape hatch in the language manual: (1) `sorry` / `admit` (`sorryAx`), (2) custom `axiom` / `opaque` assumptions, (3) raw `native_decide` (`Lean.trustCompiler`), (4) `@[implemented_by]`, (5) `@[extern]`, (6) `@[csimp]` runtime replacement rules, (7) `unsafe` / unverified `partial` definitions, (8) **Spec mutation** (weakening the theorem statement to `True` or deleting conjuncts), and (9) **Vacuous preconditions** (`False → Safe`, satisfied by zero real inputs!)."
                ],
            ),
            (
                "Two-Tier Soundness Auditing (`lake exe verigate`)",
                [
                    "As recorded in `DECISIONS.md`, **Tier 0 (`--strict-kernel`, default)** permits strictly `{propext, Quot.sound, Classical.choice}`, while **Tier 1 (`--trust-tier=bv-lrat`)** permits `bv_decide` bit-blasting *only* after scanning syntax/elaboration to ensure zero raw `native_decide` calls exist—and both tiers unconditionally block attributes `@[implemented_by]`/`@[extern]`/`@[csimp]`, `Spec` hash drift, and missing non-vacuity witnesses."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch13.lean · Exposing Vacuous Preconditions with Non-Vacuity Witnesses",
            "code": (
                "-- Subtle Cheat #9: Vacuous Precondition (zero axioms, zero attributes!)\n"
                "def brokenWithdraw (bal amt : Nat) : Nat := bal + amt -- ADDS instead of subtracting!\n"
                "\n"
                "def BadPre (bal amt : Nat) : Prop := amt ≤ bal ∧ bal < 0\n"
                "\n"
                "theorem vacuous_safety (bal amt : Nat) (h : BadPre bal amt) :\n"
                "    brokenWithdraw bal amt ≤ bal := by\n"
                "  unfold BadPre at h\n"
                "  omega -- passes because `bal < 0` is impossible for `bal : Nat`!\n"
                "\n"
                "-- Antidote: Mandatory Non-Vacuity Witness (`∃ bal amt, Pre bal amt`)\n"
                "def HonestPre (bal amt : Nat) : Prop := amt ≤ bal ∧ 0 < amt\n"
                "\n"
                "theorem honestPre_satisfiable : ∃ bal amt, HonestPre bal amt :=\n"
                "  ⟨100, 25, by unfold HonestPre; omega⟩"
            ),
            "playgroundCode": (
                "-- Chapter 13: How AI Cheats Formal Verification\n"
                "def brokenWithdraw (bal amt : Nat) : Nat := bal + amt\n\n"
                "def BadPre (bal amt : Nat) : Prop := amt ≤ bal ∧ bal < 0\n\n"
                "theorem vacuous_safety (bal amt : Nat) (h : BadPre bal amt) :\n"
                "    brokenWithdraw bal amt ≤ bal := by\n"
                "  unfold BadPre at h\n"
                "  omega\n\n"
                "-- Notice `#print axioms vacuous_safety` is clean—yet NO input satisfies BadPre!\n"
                "theorem badPre_empty : ¬(∃ bal amt, BadPre bal amt) := by\n"
                "  intro ⟨bal, amt, h⟩\n"
                "  unfold BadPre at h\n"
                "  omega\n\n"
                "-- Antidote: Require a proven Non-Vacuity Witness in Spec.lean!\n"
                "def HonestPre (bal amt : Nat) : Prop := amt ≤ bal ∧ 0 < amt\n\n"
                "theorem honestPre_satisfiable : ∃ bal amt, HonestPre bal amt :=\n"
                "  ⟨100, 25, by unfold HonestPre; omega⟩\n"
            ),
            "steps": [
                {
                    "line": 6,
                    "status": "refuted",
                    "objects": "bal amt : Nat",
                    "hyps": "h : amt ≤ bal ∧ bal < 0",
                    "goal": "⊢ bal + amt ≤ bal (vacuously 'proved' from impossible `bal < 0`!)",
                    "note": "Because `bal : Nat` can never be `< 0`, `BadPre` is equivalent to `False`. Any theorem `False → Garbage` compiles!",
                },
                {
                    "line": 14,
                    "status": "verified",
                    "objects": "witness: bal := 100, amt := 25",
                    "hyps": "HonestPre 100 25",
                    "goal": "Goals accomplished (Non-vacuity certified!)",
                    "note": "Requiring `∃ x, Pre x` guarantees at least one valid real-world input enters your safety theorem—and with `HonestPre`, `brokenWithdraw` is immediately rejected!",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch13.lean` (and Browser Lab 6 + `RedTeam/`), audit planted agent exploits and verify that `lake exe verigate --self-test` blocks all 9 cheat vectors.",
    },
    {
        "id": "14",
        "code": "Ch 14",
        "part": "Part IV · AI-Native Verification & Transfer",
        "title": "Spec-First Agentic Co-Design",
        "subtitle": "Structuring `Spec.lean` vs `Impl.lean` so untrusted coding agents synthesize fast code and proofs at 10x speed safely.",
        "lake_cmd": "lake exe check ch14",
        "lean_file": "ProveIt/Ch14.lean",
        "est": "30 min",
        "puzzle_title": "5-Line Workflow Architecture · Who Owns What in AI Vericoding?",
        "puzzle_code": (
            "-- File 1 (Human-Owned, SHA-256 Locked in CI): `Spec.lean`\n"
            "--   Defines domain types, reference semantics `specFn`, and `ValidInput`.\n"
            "-- File 2 (Agent-Editable, Untrusted): `Impl.lean`\n"
            "--   Defines optimized `implFn` + proves `impl_refines_spec` + `validInput_nonvacuous`."
        ),
        "prediction": {
            "question": "Why should `Spec.lean` require BOTH a soundness theorem (`impl r = some y → Valid r y`) AND a completeness/liveness theorem (` Satisfiable r → (impl r).isSome`)?",
            "options": [
                "Because two theorems look nicer in code review.",
                "Because without completeness/liveness, an AI agent can implement `def impl (_ : Req) : Option Resp := none`—vacuously satisfying `none = some y → Valid r y` while rejecting 100% of production traffic!",
                "Lean requires pairs of theorems in every file.",
                "`Option` cannot be used without completeness."
            ],
            "answerIndex": 1,
            "explanation": (
                "Always-returning-`none` (or always-returning-`deny`) is the classic **trivial fail-closed shortcut**! Pairing **Soundness** (*every accepted output is valid*) with **Completeness** (*every valid request succeeds*) pins down exact behavioral equivalence while leaving performance optimizations completely free to the AI."
            ),
        },
        "prose": [
            (
                "The Vericoding Division of Labor",
                [
                    "Humans are terrible at typing 200 lines of repetitive case-analysis tactics; LLMs are fast at tactic search and optimization synthesis, yet unreliable when allowed to invent their own acceptance criteria. Splitting every verified subsystem into a read-only `Spec.lean` (domain types + tiny reference function + soundness/completeness signature) and an agent-writable `Impl.lean` gives you AI velocity with mathematical certainty."
                ],
            ),
            (
                "Feeding Stuck Infoview States Back to Agents",
                [
                    "When Lean's language server or `lake build` reports an exact unresolved Infoview goal (`x : Nat, h : x > 0 ⊢ ...`), pasting that structured goal + our Chapter 07 3-Way Triage prompt (see the Reference AI Playbook) lets an agent repair leaf lemmas in 2–3 turns instead of hallucinating blind rewrites."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch14.lean · Soundness + Completeness Spec Contract",
            "code": (
                "-- Locked Spec: Fee tier calculator\n"
                "def specFee (vol : Nat) : Nat :=\n"
                "  if vol < 1000 then vol * 3 / 100 else vol * 1 / 100\n"
                "\n"
                "-- Agent's branchless/fast implementation candidate:\n"
                "def implFee (vol : Nat) : Option Nat :=\n"
                "  some (if vol < 1000 then (vol * 3) / 100 else vol / 100)\n"
                "\n"
                "-- Two-sided contract prevents `implFee _ := none`:\n"
                "theorem implFee_exact (vol : Nat) :\n"
                "    implFee vol = some (specFee vol) := by\n"
                "  unfold implFee specFee\n"
                "  split <;> simp only [Nat.mul_one]"
            ),
            "playgroundCode": (
                "-- Chapter 14: Spec-First Agentic Co-Design\n"
                "def specFee (vol : Nat) : Nat :=\n"
                "  if vol < 1000 then vol * 3 / 100 else vol * 1 / 100\n\n"
                "-- Notice a lazy agent returning `none` CANNOT satisfy `implFee vol = some (specFee vol)`!\n"
                "def implFee (vol : Nat) : Option Nat :=\n"
                "  some (if vol < 1000 then (vol * 3) / 100 else vol / 100)\n\n"
                "theorem implFee_exact (vol : Nat) :\n"
                "    implFee vol = some (specFee vol) := by\n"
                "  unfold implFee specFee\n"
                "  split <;> simp only [Nat.mul_one]\n"
            ),
            "steps": [
                {
                    "line": 10,
                    "status": "open",
                    "objects": "vol : Nat",
                    "hyps": "(none)",
                    "goal": "⊢ implFee vol = some (specFee vol)",
                    "note": "Stating `implFee vol = some (specFee vol)` bundles both totality (never returns `none`) and exact value agreement in one theorem.",
                },
                {
                    "line": 13,
                    "status": "verified",
                    "objects": "vol : Nat",
                    "hyps": "vol * 1 = vol",
                    "goal": "Goals accomplished",
                    "note": "Copy ready-to-use Spec-First agent prompts and CI lockfiles from `site/reference/ai-playbook.html`!",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch14.lean`, complete an `Impl` module against a locked `Spec` contract including soundness, completeness, and non-vacuity.",
    },
    {
        "id": "15",
        "code": "Ch 15",
        "part": "Part IV · AI-Native Verification & Transfer",
        "title": "Verified Wire Formats (TLV Framing)",
        "subtitle": "Eliminating parser differentials and TCP stream-smuggling bugs with `decode (encode pkt ++ rest) = some (pkt, rest)`.",
        "lake_cmd": "lake exe check ch15",
        "lean_file": "ProveIt/Ch15.lean",
        "est": "35 min",
        "puzzle_title": "5-Line Security Bug · Single-Buffer Round-Trip vs. TCP Stream Concatenation",
        "puzzle_code": (
            "def encodeBad (msg : List UInt8) : List UInt8 := msg\n"
            "def decodeBad (wire : List UInt8) : Option (List UInt8) := some wire\n"
            "-- `decodeBad (encodeBad msg) = some msg` is TRUE (`rfl`)!\n"
            "-- Yet over a socket, `encodeBad [1, 2] ++ encodeBad [3, 4]` decodes as ONE `[1, 2, 3, 4]` packet!"
        ),
        "prediction": {
            "question": "What stronger round-trip theorem forces a binary serializer (`encode`) and parser (`decode`) to self-delimit packet boundaries cleanly on an arbitrary byte stream?",
            "options": [
                "`decode (encode pkt) = some pkt`.",
                "`∀ (pkt : Packet) (rest : List UInt8), decode (encode pkt ++ rest) = some (pkt, rest)` — proving `decode` recovers `pkt` AND leaves trailing stream bytes `rest` completely intact!",
                "`(encode pkt).length > 0`.",
                "Adding a trailing newline without escaping newlines inside `pkt`."
            ],
            "answerIndex": 1,
            "explanation": (
                "Quantifying over *every arbitrary suffix* `rest : List UInt8` (`decode (encode pkt ++ rest) = some (pkt, rest)`) makes frame-boundary smuggling mathematically impossible! "
                "`encodeBad` fails immediately on `pkt = [1], rest = [2]` (`some ([1, 2], []) ≠ some ([1], [2])`), whereas Type-Length-Value (TLV) framing with a bounded length header satisfies the stream round-trip theorem cleanly."
            ),
        },
        "prose": [
            (
                "Why Parser Differentials Cause Critical CVEs",
                [
                    "HTTP request smuggling, X.509 certificate confusion, and consensus-splitting blockchain bugs happen when two parsers disagree on where Frame 1 ends and Frame 2 begins. Proving **Prefix-Unambiguous Stream Round-Trip** (`decode (encode p ++ rest) = some (p, rest)`) plus deterministic encoding guarantees every compliant node splits a byte stream identically."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch15.lean · Stream-Safe TLV Packet Framing",
            "code": (
                "structure TlvPacket where\n"
                "  tag     : UInt8\n"
                "  payload : List UInt8\n"
                "  h_bound : payload.length < 256\n"
                "\n"
                "def encodeTlv (p : TlvPacket) : List UInt8 :=\n"
                "  p.tag :: UInt8.ofNat p.payload.length :: p.payload\n"
                "\n"
                "def decodeRaw (wire : List UInt8) : Option (UInt8 × List UInt8 × List UInt8) :=\n"
                "  match wire with\n"
                "  | tag :: lenByte :: body =>\n"
                "    let n := lenByte.toNat\n"
                "    if body.length >= n then\n"
                "      some (tag, body.take n, body.drop n)\n"
                "    else none\n"
                "  | _ => none\n"
                "\n"
                "theorem tlv_stream_roundtrip (p : TlvPacket) (rest : List UInt8) :\n"
                "    decodeRaw (encodeTlv p ++ rest) = some (p.tag, p.payload, rest) := by\n"
                "  unfold encodeTlv decodeRaw\n"
                "  have h_len : (UInt8.ofNat p.payload.length).toNat = p.payload.length :=\n"
                "    UInt8.toNat_ofNat_of_lt p.h_bound\n"
                "  simp only [List.cons_append, h_len, List.length_append]\n"
                "  have h_ge : p.payload.length + rest.length ≥ p.payload.length := by omega\n"
                "  simp only [ge_iff_le, h_ge, ↓reduceIte, List.take_append_of_le_length (Nat.le_refl _),\n"
                "    List.take_length, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]"
            ),
            "playgroundCode": (
                "-- Chapter 15: Verified Wire Formats (TLV Stream Framing)\n"
                "structure TlvPacket where\n"
                "  tag     : UInt8\n"
                "  payload : List UInt8\n"
                "  h_bound : payload.length < 256\n\n"
                "def encodeTlv (p : TlvPacket) : List UInt8 :=\n"
                "  p.tag :: UInt8.ofNat p.payload.length :: p.payload\n\n"
                "def decodeRaw (wire : List UInt8) : Option (UInt8 × List UInt8 × List UInt8) :=\n"
                "  match wire with\n"
                "  | tag :: lenByte :: body =>\n"
                "    let n := lenByte.toNat\n"
                "    if body.length >= n then\n"
                "      some (tag, body.take n, body.drop n)\n"
                "    else none\n"
                "  | _ => none\n\n"
                "theorem tlv_stream_roundtrip (p : TlvPacket) (rest : List UInt8) :\n"
                "    decodeRaw (encodeTlv p ++ rest) = some (p.tag, p.payload, rest) := by\n"
                "  unfold encodeTlv decodeRaw\n"
                "  have h_len : (UInt8.ofNat p.payload.length).toNat = p.payload.length :=\n"
                "    UInt8.toNat_ofNat_of_lt p.h_bound\n"
                "  simp only [List.cons_append, h_len, List.length_append]\n"
                "  have h_ge : p.payload.length + rest.length ≥ p.payload.length := by omega\n"
                "  simp only [ge_iff_le, h_ge, ↓reduceIte, List.take_append_of_le_length (Nat.le_refl _),\n"
                "    List.take_length, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]\n"
            ),
            "steps": [
                {
                    "line": 18,
                    "status": "open",
                    "objects": "p : TlvPacket, rest : List UInt8",
                    "hyps": "p.h_bound : p.payload.length < 256",
                    "goal": "⊢ decodeRaw (encodeTlv p ++ rest) = some (p.tag, p.payload, rest)",
                    "note": "Notice `p.h_bound : payload.length < 256` from Chapter 09! Without `< 256`, `UInt8.ofNat` would wrap mod 256 and truncate long payloads!",
                },
                {
                    "line": 21,
                    "status": "open",
                    "objects": "p : TlvPacket, rest : List UInt8",
                    "hyps": "h_len : (UInt8.ofNat p.payload.length).toNat = p.payload.length",
                    "goal": "Slice `(p.payload ++ rest).take p.payload.length` and `.drop p.payload.length`",
                    "note": "`UInt8.toNat_ofNat_of_lt p.h_bound` proves the 1-byte length header decodes losslessly.",
                },
                {
                    "line": 25,
                    "status": "verified",
                    "objects": "p : TlvPacket, rest : List UInt8",
                    "hyps": "(exact payload recovered; trailing stream `rest` preserved byte-for-byte)",
                    "goal": "Goals accomplished",
                    "note": "Zero packet concatenation ambiguity across arbitrary TCP chunks!",
                },
            ],
        },
        "takeaway": "In `ProveIt/Ch15.lean`, verify a multi-message TLV stream decoder loop (`decodeAll`) and prove truncation rejection on short buffers.",
    },
    {
        "id": "16",
        "code": "Ch 16",
        "part": "Part IV · AI-Native Verification & Transfer",
        "title": "Monday-Morning Transfer (`lake exe oracle`)",
        "subtitle": "Using Lean 4 as a Reference Differential Oracle for Rust, Go, TypeScript, Python, and C++ services.",
        "lake_cmd": "lake exe check ch16",
        "lean_file": "ProveIt/Ch16.lean",
        "est": "30 min",
        "puzzle_title": "5-Line Adoption Question · 'My Team Ships Rust/Go/TS, Not Lean!'",
        "puzzle_code": (
            "-- AWS S3 ShardStore, AWS Cedar, and Cloudflare didn't rewrite 10M lines of Rust/Go in Lean.\n"
            "-- Instead: 300 lines of Lean 4 = Verified Executable Reference Oracle (`lake exe oracle`).\n"
            "-- CI pipes 50,000 adversarial traces into BOTH Production Rust/Go AND `lake exe oracle`.\n"
            "-- Any 1-bit divergence between Production and Verified Lean fails the PR immediately!"
        ),
        "prediction": {
            "question": "Why does differential-fuzzing a Rust/Go/TypeScript service against a verified Lean 4 executable oracle (`lake exe oracle`) catch bugs that ordinary self-contained property tests in Rust/Go miss?",
            "options": [
                "Because JSON serialization makes code run faster.",
                "Because in ordinary tests, hand-written assertions only check rough properties (like 'did not panic'), whereas `lake exe oracle` computes the **exact ground-truth output** of a mathematically proven specification on every adversarial trace!",
                "Lean automatically edits `.rs` and `.go` files.",
                "Differential testing only runs once per year."
            ],
            "answerIndex": 1,
            "explanation": (
                "This is AWS Cedar's exact playbook! Writing a 250-line executable Lean 4 model of your auth engine, billing ledger, or consensus state machine takes an afternoon; "
                "proving its invariants in Lean guarantees the oracle itself has zero subtle edge-case bugs; and piping JSONL traces through `lake exe oracle` tests your production Rust/Go/TS/Python code against proven mathematical truth on every commit!"
            ),
        },
        "prose": [
            (
                "Three Monday-Morning Adoption Rungs",
                [
                    "**Rung 1 (Zero Lean in Prod — Design & Typestate Habits)**: Apply sum-type domain modeling (Ch 02), explicit overflow/saturating awareness (Ch 01 & Ch 10), and Gear 1 state-table thinking to your everyday Rust enums, TypeScript discriminated unions, and Go structs.",
                    "**Rung 2 (Verified Reference Oracle in CI — Highest ROI)**: Model your gnarliest 300-line core (authorization, billing, lease fencing, rate limiting, wire framing) in Lean 4, prove its invariants, and differential-fuzz your production service against `lake exe oracle` via `scripts/fuzz_against_oracle.py`.",
                    "**Rung 3 (Direct C FFI / Proof-Carrying AI Gate)**: Compile hot pure cores to C via Lean's compiler or enforce `lake exe verigate` on AI-synthesized modules."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Ch16.lean · Executable Trace Oracle State Machine",
            "code": (
                "inductive Cmd | deposit (amt : Nat) | withdraw (amt : Nat) | freeze\n"
                "\n"
                "structure AccountOracle where\n"
                "  balance : Nat\n"
                "  frozen  : Bool\n"
                "\n"
                "def stepOracle (s : AccountOracle) (c : Cmd) : AccountOracle :=\n"
                "  if s.frozen then s\n"
                "  else match c with\n"
                "    | .deposit amt  => { s with balance := s.balance + amt }\n"
                "    | .withdraw amt => if amt ≤ s.balance then { s with balance := s.balance - amt } else s\n"
                "    | .freeze       => { s with frozen := true }\n"
                "\n"
                "def runTrace (s : AccountOracle) (cmds : List Cmd) : AccountOracle :=\n"
                "  cmds.foldl stepOracle s\n"
                "\n"
                "theorem frozen_locks_balance (s : AccountOracle) (cmds : List Cmd) (h : s.frozen = true) :\n"
                "    (runTrace s cmds).balance = s.balance := by\n"
                "  induction cmds generalizing s with\n"
                "  | nil => rfl\n"
                "  | cons c rest ih =>\n"
                "    simp only [runTrace, List.foldl_cons, stepOracle, h, ↓reduceIte]\n"
                "    exact ih s h"
            ),
            "playgroundCode": (
                "-- Chapter 16: Monday-Morning Transfer — Verified Differential Oracle\n"
                "inductive Cmd | deposit (amt : Nat) | withdraw (amt : Nat) | freeze deriving Repr\n\n"
                "structure AccountOracle where\n"
                "  balance : Nat\n"
                "  frozen  : Bool\n"
                "  deriving Repr, DecidableEq\n\n"
                "def stepOracle (s : AccountOracle) (c : Cmd) : AccountOracle :=\n"
                "  if s.frozen then s\n"
                "  else match c with\n"
                "    | .deposit amt  => { s with balance := s.balance + amt }\n"
                "    | .withdraw amt => if amt ≤ s.balance then { s with balance := s.balance - amt } else s\n"
                "    | .freeze       => { s with frozen := true }\n\n"
                "def runTrace (s : AccountOracle) (cmds : List Cmd) : AccountOracle :=\n"
                "  cmds.foldl stepOracle s\n\n"
                "theorem frozen_locks_balance (s : AccountOracle) (cmds : List Cmd) (h : s.frozen = true) :\n"
                "    (runTrace s cmds).balance = s.balance := by\n"
                "  induction cmds generalizing s with\n"
                "  | nil => rfl\n"
                "  | cons c rest ih =>\n"
                "    simp only [runTrace, List.foldl_cons, stepOracle, h, ↓reduceIte]\n"
                "    exact ih s h\n"
            ),
            "steps": [
                {
                    "line": 14,
                    "status": "open",
                    "objects": "s : AccountOracle, cmds : List Cmd",
                    "hyps": "(executable foldl trace runner exported by `lake exe oracle`)",
                    "goal": "Prove multi-step trace invariants AND emit JSONL oracle outputs",
                    "note": "The exact same `runTrace` function both carries inductive trace proofs AND answers differential fuzz queries over stdin/stdout!",
                },
                {
                    "line": 23,
                    "status": "verified",
                    "objects": "s : AccountOracle, cmds : List Cmd",
                    "hyps": "(proven across arbitrary trace lengths)",
                    "goal": "Goals accomplished",
                    "note": "See `site/reference/ai-playbook.html` for copy-paste Rust, Go, TypeScript, and Python differential harness templates.",
                },
            ],
        },
        "takeaway": "Run `lake exe oracle --demo` and `python3 scripts/fuzz_against_oracle.py` locally, then finish `ProveIt/Ch16.lean`!",
    },
    {
        "id": "cp4",
        "code": "CP 4",
        "part": "Part IV · Checkpoint 4",
        "title": "Checkpoint 4: Red-Team Audit of an AI Batch Escrow",
        "subtitle": "Final boss checkpoint: uncover 3 planted AI exploits in a 64-bit batch escrow submission, restore the spec, and seal kernel soundness.",
        "lake_cmd": "lake exe check cp4",
        "lean_file": "ProveIt/Checkpoints/Cp4.lean",
        "est": "45 min",
        "puzzle_title": "Final Red-Team Brief · Audit Untrusted PR Before Mainnet Deploy",
        "puzzle_code": (
            "-- An autonomous coding agent submitted a '100% verified' Batch Escrow release module.\n"
            "-- Planted exploits hidden inside:\n"
            "--   1. Vacuous precondition (`payouts.length = 0 ∧ payouts.length > 0`)\n"
            "--   2. Unchecked `UInt64` batch sum wrap-around (`0xFFFFFFFFFFFFFFF0 + 0x20 == 0x10 ≤ vault`!)\n"
            "--   3. Smuggled custom helper axiom / weakened conservation spec."
        ),
        "prediction": {
            "question": "In a batch payout function over `UInt64`, why is checking `payoutA + payoutB ≤ vaultBalance` in `UInt64` arithmetic a catastrophic fund-drain vulnerability?",
            "options": [
                "Because `UInt64` addition is slow.",
                "Because two huge payouts `payoutA = 2^64 - 10` and `payoutB = 20` wrap mod `2^64` to `10`! If `vaultBalance = 50`, `10 ≤ 50` passes while releasing nearly `2^65` units!",
                "Because `vaultBalance` is always zero.",
                "Addition never overflows for two numbers."
            ],
            "answerIndex": 1,
            "explanation": (
                "This exact integer-overflow pattern caused famous smart-contract and ledger drains (BeautyChain / BEC batchOverflow)! "
                "Checking overflow on *each* addition (`sum < a`) and verifying with `bv_decide` + non-vacuity witnesses seals the vault completely."
            ),
        },
        "prose": [
            (
                "Graduating as a Trusted Computing Base Architect",
                [
                    "By repairing all three planted vulnerabilities in `ProveIt/Checkpoints/Cp4.lean`—restoring an honest satisfiable precondition with an explicit `∃` witness, checking 64-bit addition overflow via `BitVec 64` + `bv_decide`, and verifying clean axioms under `lake exe verigate`—you bring together all four parts of *Prove It*."
                ],
            ),
        ],
        "workbench": {
            "title": "ProveIt/Checkpoints/Cp4.lean · Overflow-Safe Two-Party Escrow Release",
            "code": (
                "import Std.Tactic.BVDecide\n"
                "\n"
                "def batchReleaseSafe (vault p1 p2 : BitVec 64) : Option (BitVec 64) :=\n"
                "  let total := p1 + p2\n"
                "  if total < p1 then none -- overflow guard!\n"
                "  else if total ≤ vault then some (vault - total)\n"
                "  else none\n"
                "\n"
                "theorem release_conserves_vault (vault p1 p2 rem : BitVec 64)\n"
                "    (h : batchReleaseSafe vault p1 p2 = some rem) :\n"
                "    rem + p1 + p2 = vault ∧ p1 ≤ vault ∧ p2 ≤ vault := by\n"
                "  dsimp only [batchReleaseSafe] at h\n"
                "  split at h\n"
                "  · contradiction\n"
                "  · split at h\n"
                "    · simp only [Option.some.injEq] at h\n"
                "      subst h\n"
                "      bv_decide\n"
                "    · contradiction"
            ),
            "playgroundCode": (
                "-- Checkpoint 4: Red-Team Audit of AI Batch Escrow\n"
                "import Std.Tactic.BVDecide\n\n"
                "def batchReleaseSafe (vault p1 p2 : BitVec 64) : Option (BitVec 64) :=\n"
                "  let total := p1 + p2\n"
                "  if total < p1 then none\n"
                "  else if total ≤ vault then some (vault - total)\n"
                "  else none\n\n"
                "-- Overflow attack (`2^64 - 10` + `20` against `vault = 50`) is cleanly blocked:\n"
                "#guard batchReleaseSafe 50#64 (0xFFFFFFFFFFFFFFF6#64) 20#64 == none\n\n"
                "-- Non-vacuity witness: real valid batch succeeds!\n"
                "theorem batchRelease_nonvacuous :\n"
                "    ∃ vault p1 p2 rem, p1 > 0#64 ∧ p2 > 0#64 ∧ batchReleaseSafe vault p1 p2 = some rem :=\n"
                "  ⟨100#64, 40#64, 35#64, 25#64, by decide⟩\n\n"
                "theorem release_conserves_vault (vault p1 p2 rem : BitVec 64)\n"
                "    (h : batchReleaseSafe vault p1 p2 = some rem) :\n"
                "    rem + p1 + p2 = vault ∧ p1 ≤ vault ∧ p2 ≤ vault := by\n"
                "  dsimp only [batchReleaseSafe] at h\n"
                "  split at h\n"
                "  · contradiction\n"
                "  · split at h\n"
                "    · simp only [Option.some.injEq] at h\n"
                "      subst h\n"
                "      bv_decide\n"
                "    · contradiction\n"
            ),
            "steps": [
                {
                    "line": 5,
                    "status": "open",
                    "objects": "vault p1 p2 : BitVec 64",
                    "hyps": "total := p1 + p2",
                    "goal": "Guard `total < p1` rejects wrap-around before comparing `total ≤ vault`",
                    "note": "Without `if total < p1 then none`, `0xFFFFFFFFFFFFFFF6 + 20` wraps to `10 ≤ 50`!",
                },
                {
                    "line": 18,
                    "status": "verified",
                    "objects": "vault p1 p2 rem : BitVec 64",
                    "hyps": "(conservation + individual payout bounds + non-vacuity certified)",
                    "goal": "Goals accomplished",
                    "note": "Congratulations—you are ready to tackle all 4 Production Capstones!",
                },
            ],
        },
        "takeaway": "Complete `ProveIt/Checkpoints/Cp4.lean` and verify with `lake exe check cp4` and `lake exe verigate`.",
    },
]

CAPSTONES = [
    {
        "id": "cedar-lite",
        "badge": "Capstone 01 · Cloud Security",
        "title": "CedarLite — Cloud IAM Policy Engine & Optimizer",
        "path": "ProveIt/Capstones/CedarLite.lean",
        "check_cmd": "lake build ProveIt.Capstones.CedarLite",
        "summary": (
            "Inspired by AWS's Lean-verified Cedar authorization engine. Model principals, actions, resources, "
            "and `permit`/`forbid` policy sets, then build a policy constant-folder/dead-rule eliminator and prove "
            "three non-negotiable security theorems."
        ),
        "invariants": [
            "Default-Deny: An empty policy set denies every `(Principal, Action, Resource)` request.",
            "Forbid-Overrides-Permit: If ANY matching `forbid` rule fires, `authorize` returns `.deny` regardless of how many `permit` rules match.",
            "Optimizer Equivalence: `authorize (optimizePolicies ps) req = authorize ps req` for all requests.",
        ],
        "playground": (
            "-- Capstone 1 Preview: CedarLite Authorization & Forbid-Overrides-Permit\n"
            "inductive Effect | permit | forbid deriving Repr, DecidableEq\n"
            "inductive Decision | allow | deny deriving Repr, DecidableEq\n\n"
            "structure Request where\n"
            "  principal : Nat\n"
            "  action    : Nat\n"
            "  resource  : Nat\n"
            "  deriving DecidableEq\n\n"
            "structure Rule where\n"
            "  effect : Effect\n"
            "  targetPrincipal : Option Nat -- none = wildcard *\n"
            "  targetAction    : Option Nat\n\n"
            "def matchesRule (r : Rule) (req : Request) : Bool :=\n"
            "  (match r.targetPrincipal with | none => true | some p => p == req.principal) &&\n"
            "  (match r.targetAction    with | none => true | some a => a == req.action)\n\n"
            "def authorize (rules : List Rule) (req : Request) : Decision :=\n"
            "  let active := rules.filter (fun r => matchesRule r req)\n"
            "  if active.any (fun r => r.effect == .forbid) then .deny\n"
            "  else if active.any (fun r => r.effect == .permit) then .allow\n"
            "  else .deny\n\n"
            "theorem default_deny (req : Request) : authorize [] req = .deny := rfl\n\n"
            "theorem explicit_forbid_wins (r : Rule) (rest : List Rule) (req : Request)\n"
            "    (h_forbid : r.effect = .forbid) (h_match : matchesRule r req = true) :\n"
            "    authorize (r :: rest) req = .deny := by\n"
            "  unfold authorize\n"
            "  simp only [List.filter, h_match, ↓reduceIte, List.any_cons, h_forbid, BEq.rfl, Bool.true_or]\n"
        ),
    },
    {
        "id": "fencing-kv",
        "badge": "Capstone 02 · Distributed Systems",
        "title": "FencingKV — Split-Brain Leases & Tombstone Compaction",
        "path": "ProveIt/Capstones/FencingKV.lean",
        "check_cmd": "lake build ProveIt.Capstones.FencingKV",
        "summary": (
            "Full Two-Gear TLA+-in-Lean distributed verification: use Gear 1 BFS to reproduce a GC-pause split-brain "
            "write on unfenced storage, then prove Gear 2 unbounded inductive epoch monotonicity AND tombstone-compaction refinement."
        ),
        "invariants": [
            "Gear 1 Falsification: Unfenced delayed leader writes corrupt newer epoch commits in 4 steps.",
            "Gear 2 Monotonic Fencing: `msg.epoch < node.fencedEpoch` is rejected across all unbounded `epoch : Nat`.",
            "Stuttering Compaction: Garbage-collecting shadowed writes and tombstones preserves logical key reads.",
        ],
        "playground": (
            "-- Capstone 2 Preview: FencingKV Monotonic Token Guard\n"
            "structure StorageNode where\n"
            "  fencedEpoch : Nat\n"
            "  val         : Nat\n"
            "  deriving Repr, DecidableEq\n\n"
            "def writeFenced (node : StorageNode) (msgEpoch msgVal : Nat) : StorageNode :=\n"
            "  if msgEpoch ≥ node.fencedEpoch then\n"
            "    { fencedEpoch := msgEpoch, val := msgVal }\n"
            "  else node\n\n"
            "theorem fenced_epoch_monotonic (node : StorageNode) (ep v : Nat) :\n"
            "    node.fencedEpoch ≤ (writeFenced node ep v).fencedEpoch := by\n"
            "  unfold writeFenced\n"
            "  split <;> omega\n\n"
            "theorem stale_epoch_ignored (node : StorageNode) (ep v : Nat)\n"
            "    (h_stale : ep < node.fencedEpoch) :\n"
            "    writeFenced node ep v = node := by\n"
            "  unfold writeFenced\n"
            "  have h_not : ¬(ep ≥ node.fencedEpoch) := by omega\n"
            "  simp only [h_not, ↓reduceIte]\n"
        ),
    },
    {
        "id": "stack-vm",
        "badge": "Capstone 03 · Compilers & Runtimes",
        "title": "StackVM — Verified Optimizing Compiler & Bytecode VM",
        "path": "ProveIt/Capstones/StackVM.lean",
        "check_cmd": "lake build ProveIt.Capstones.StackVM",
        "summary": (
            "Compile an expression AST with variables, arithmetic, and conditionals into flat stack-machine bytecode, "
            "write an algebraic constant-folding optimizer, and prove end-to-end semantic preservation for arbitrary code continuations."
        ),
        "invariants": [
            "Optimizer Soundness: `eval env (optimize e) = eval env e`.",
            "Continuation-Safe Stack Preservation: `exec env (compile e ++ codeRest) stk = exec env codeRest (eval env e :: stk)`.",
            "Zero Stack-Underflow Guarantee: Compiled programs never trap on an empty operand stack.",
        ],
        "playground": (
            "-- Capstone 3 Preview: StackVM Compiler Continuation Preservation\n"
            "inductive Expr\n"
            "  | lit (n : Nat)\n"
            "  | var (x : Nat)\n"
            "  | add (a b : Expr)\n\n"
            "def eval (env : Nat → Nat) : Expr → Nat\n"
            "  | .lit n   => n\n"
            "  | .var x   => env x\n"
            "  | .add a b => eval env a + eval env b\n\n"
            "inductive Instr | push (n : Nat) | load (x : Nat) | iadd\n\n"
            "def compile : Expr → List Instr\n"
            "  | .lit n   => [.push n]\n"
            "  | .var x   => [.load x]\n"
            "  | .add a b => compile a ++ compile b ++ [.iadd]\n\n"
            "def exec (env : Nat → Nat) : List Instr → List Nat → Option (List Nat)\n"
            "  | [], stk => some stk\n"
            "  | .push n :: rest, stk => exec env rest (n :: stk)\n"
            "  | .load x :: rest, stk => exec env rest (env x :: stk)\n"
            "  | .iadd :: rest, b :: a :: stk => exec env rest ((a + b) :: stk)\n"
            "  | .iadd :: _, _ => none\n\n"
            "theorem compile_correct (env : Nat → Nat) (e : Expr) (rest : List Instr) (stk : List Nat) :\n"
            "    exec env (compile e ++ rest) stk = exec env rest (eval env e :: stk) := by\n"
            "  induction e generalizing rest stk with\n"
            "  | lit n => rfl\n"
            "  | var x => rfl\n"
            "  | add a b iha ihb =>\n"
            "    simp only [compile, List.append_assoc, iha, ihb, eval]\n"
            "    rfl\n"
        ),
    },
    {
        "id": "verigate-oracle",
        "badge": "Capstone 04 · AI Safety & Polyglot CI",
        "title": "VeriGate & Oracle — AI Proof-Carrying Gate & Differential Fuzzer",
        "path": "ProveIt/Capstones/VeriGate.lean",
        "check_cmd": "lake exe verigate --self-test && lake exe oracle --demo",
        "summary": (
            "Build the supervision harness that lets autonomous coding agents write fast implementations without compromising "
            "soundness: lock `Spec` hashes, audit axioms/attributes against `RedTeam/` exploits, and differential-fuzz external services."
        ),
        "invariants": [
            "Two-Tier Axiom Policy: Strict Tier 0 (`propext`, `Quot.sound`, `Classical.choice`) + explicit Tier 1 (`bv_decide` without raw `native_decide`).",
            "Attribute & Spec-Drift Firewall: Blocks `sorryAx`, custom `axiom`, `@[implemented_by]`, `@[extern]`, `@[csimp]`, and `Spec.lean` edits.",
            "Polyglot Differential Oracle (`lake exe oracle`): Streams ground-truth outputs to test Rust, Go, TS, and Python services.",
        ],
        "playground": (
            "-- Capstone 4 Preview: Pure Axiom-Policy Classifier Model\n"
            "inductive TrustTier | strictKernel | bvLrat deriving DecidableEq\n\n"
            "structure AuditInput where\n"
            "  axiomsUsed      : List String\n"
            "  hasRawNativeDec : Bool\n"
            "  hasRuntimeSwap  : Bool -- @[implemented_by] / @[extern] / @[csimp]\n"
            "  specHashMatches : Bool\n"
            "  hasNonVacuity   : Bool\n\n"
            "def allowedAxiom (tier : TrustTier) (ax : String) : Bool :=\n"
            "  ax == \"propext\" || ax == \"Quot.sound\" || ax == \"Classical.choice\" ||\n"
            "  (tier == .bvLrat && (ax == \"Lean.ofReduceBool\" || ax == \"Lean.trustCompiler\"))\n\n"
            "def verigatePass (tier : TrustTier) (inp : AuditInput) : Bool :=\n"
            "  inp.specHashMatches &&\n"
            "  inp.hasNonVacuity &&\n"
            "  !inp.hasRuntimeSwap &&\n"
            "  !inp.hasRawNativeDec &&\n"
            "  inp.axiomsUsed.all (allowedAxiom tier)\n\n"
            "theorem sorry_always_rejected (tier : TrustTier) (inp : AuditInput)\n"
            "    (h : \"sorryAx\" ∈ inp.axiomsUsed) : verigatePass tier inp = false := by\n"
            "  unfold verigatePass\n"
            "  have hall : inp.axiomsUsed.all (allowedAxiom tier) = false := by\n"
            "    rw [List.all_eq_false]\n"
            "    refine ⟨\"sorryAx\", h, ?_⟩\n"
            "    cases tier <;> decide\n"
            "  simp only [hall, Bool.and_false]\n"
        ),
    },
]

ROSETTA_ITEMS = [
    {
        "cat": "state",
        "title": "State Variables (`VARIABLES`)",
        "note": "TLA+ declares untyped global variables; Lean groups state cleanly into a typed `structure`.",
        "tla": "VARIABLES leaderEpoch, storageEpoch, committedVal",
        "lean": "structure SysState where\n  leaderEpoch  : Nat\n  storageEpoch : Nat\n  committedVal : Option String",
    },
    {
        "cat": "state",
        "title": "Initial State Predicate (`Init`)",
        "note": "Express deterministic initialization as a value `init : S` or nondeterministic initial sets as `Init : S → Prop`.",
        "tla": "Init ==\n  /\\ leaderEpoch = 1\n  /\\ storageEpoch = 1\n  /\\ committedVal = \"none\"",
        "lean": "def Init (s : SysState) : Prop :=\n  s.leaderEpoch = 1 ∧\n  s.storageEpoch = 1 ∧\n  s.committedVal = none",
    },
    {
        "cat": "transitions",
        "title": "Next-State Relation (`Next`) & `UNCHANGED`",
        "note": "Record update syntax `{ s with field := v }` automatically keeps all unmentioned fields `UNCHANGED` without forgetting any!",
        "tla": "BumpEpoch ==\n  /\\ leaderEpoch' = leaderEpoch + 1\n  /\\ UNCHANGED <<storageEpoch, committedVal>>\n\nNext == BumpEpoch \\/ CommitWrite",
        "lean": "inductive Next : SysState → SysState → Prop\n  | bumpEpoch (s : SysState) :\n      Next s { s with leaderEpoch := s.leaderEpoch + 1 }\n  | commitWrite (s : SysState) (v : String)\n      (h : s.leaderEpoch ≥ s.storageEpoch) :\n      Next s { s with storageEpoch := s.leaderEpoch, committedVal := some v }",
    },
    {
        "cat": "checking",
        "title": "Gear 1: TLC Bounded Model Checking (`Spec => []TypeOK /\\ []Safe`)",
        "note": "Executable `step : S → List S` explored via pure BFS catches shallow bugs in milliseconds via `#guard`.",
        "tla": "-- In MCMini.cfg:\nSPECIFICATION Spec\nINVARIANT Safe",
        "lean": "-- Pure Lean Gear 1 BFS (Ch 04):\n#guard bfsExplore 6 [initSys] == .allSafe",
    },
    {
        "cat": "invariants",
        "title": "Gear 2: Inductive Invariant (`Init => Inv` & `Inv /\\ Next => Inv'`)",
        "note": "Equivalent to TLAPS `THEOREM Spec => []Safe` via strengthened invariant `Inv`.",
        "tla": "Inv ==\n  /\\ Safe\n  /\\ committedVal /= \"none\" => storageEpoch >= 1\n\nTHEOREM Init => Inv\nTHEOREM Inv /\\ [Next]_vars => Inv'",
        "lean": "theorem inv_init (s : SysState) : Init s → Inv s := ...\ntheorem inv_next (s s' : SysState) : Inv s → Next s s' → Inv s' := ...\ntheorem reachable_safe (s : SysState) : Reachable s → Safe s := ...",
    },
    {
        "cat": "refinement",
        "title": "Refinement Mapping & Stuttering (`INSTANCE Abs WITH ...`)",
        "note": "Concrete implementation steps map either to an abstract `SpecNext` step or an abstract stuttering step `abs s' = abs s`.",
        "tla": "Abs == INSTANCE SpecKV\n  WITH kv <- [k \\in Keys |-> LookupLog(log, k)]\n\nTHEOREM ImplSpec => Abs!Spec",
        "lean": "def abs (impl : ImplKV) : SpecKV := lookupLog impl.log\n\ntheorem compact_stutters (impl : ImplKV) :\n    abs (compact impl) = abs impl := ...",
    },
    {
        "cat": "progress",
        "title": "Bounded Progress / Termination (`WF_vars` / Variant Function)",
        "note": "Lean's `termination_by` proves a well-founded ranking measure strictly decreases, guaranteeing zero infinite internal loops.",
        "tla": "Variant == totalBytes - offset\nTHEOREM ParseStep => Variant' < Variant",
        "lean": "def parseAll (buf : ByteArray) (offset : Nat) : ...\n  ...\ntermination_by buf.size - offset\ndecreasing_by omega",
    },
]

GLOSSARY_ITEMS = [
    ("Part I", "Total Function", "A function guaranteed to return a valid output for every possible input of its parameter types—never throwing exceptions, looping forever, or dereferencing null.", "Default for all `def` functions in Lean 4 (Ch 01).", "chapters/01.html"),
    ("Part I", "Saturating Subtraction", "Defining `a - b = 0` on `Nat` whenever `a < b` so natural numbers stay closed without throwing runtime exceptions.", "`(10 : Nat) - 12 = 0` (Ch 01).", "chapters/01.html"),
    ("Part I", "Product Type (`structure`)", "A record packing Field A AND Field B together; total state count multiplies (`|A| × |B|`).", "`structure Config where ...` (Ch 02).", "chapters/02.html"),
    ("Part I", "Sum Type (`inductive`)", "A tagged choice representing Variant A OR Variant B (mutually exclusive); state count adds (`|A| + |B|`), making illegal combinations unrepresentable.", "`inductive Session | anonymous | active (uid : Nat)` (Ch 02).", "chapters/02.html"),
    ("Part I", "Boolean Reflection (`Decidable`)", "Connecting an executable `Bool` check (0/1 data) to a rich mathematical specification `Prop` via `eval x = true ↔ Spec x`.", "`Decidable P`, `decide`, `↔` (Ch 03).", "chapters/03.html"),
    ("Part I", "Gear 1 (Bounded BFS Model Checking)", "Exhaustively exploring all reachable action interleavings up to depth `k` to catch shallow protocol bugs and emit minimal counterexample traces.", "35-line pure `bfs` in Lean + `#guard` (Ch 04).", "chapters/04.html"),
    ("Part II", "Lean Infoview", "The live proof-state inspector showing **Objects** (variables), **Hypotheses** (assumptions in scope), and **⊢ Goal** (remaining obligation).", "Interactive split-view in every chapter (Ch 05).", "chapters/05.html"),
    ("Part II", "Curry-Howard Correspondence", "The exact identity between logical propositions and types: proving `P → Q` is writing a total function taking a proof of `P` to a proof of `Q`.", "`theorem` bodies typechecked by Lean's kernel (Ch 05).", "chapters/05.html"),
    ("Part II", "Garden-of-Eden State", "An unreachable syntactic state `s` where `Safe s` happens to hold right now, yet one transition `Next s s'` crashes into an unsafe state `¬Safe s'`—breaking naive induction.", "Eliminated by Inductive Strengthening (Ch 08 & Lab 2).", "chapters/08.html"),
    ("Part II", "Gear 2 (Inductive Strengthening)", "Adding structural invariants (`Inv s := Safe s ∧ Helper s`) so `Init s → Inv s` and `Inv s → Next s s' → Inv s'` hold across infinite depths and unbounded integers.", "`Reachable s → Safe s` (Ch 08).", "chapters/08.html"),
    ("Part III", "Subtype & Runtime Proof Erasure", "Bundling a runtime value `x : α` with a compile-time proof `h : P x` (`{ x : α // P x }`). Lean erases `h` to zero bytes (`lcErased`) in machine code.", "`Subtype`, `Fin cap`, `if h : ...` (Ch 09 & Lab 4).", "chapters/09.html"),
    ("Part III", "Bit-Blasting & LRAT (`bv_decide`)", "Translating fixed-width 64-bit hardware arithmetic (`BitVec 64`) into SAT and checking an unsatisfiability certificate to catch `2^64` wrap-around bugs.", "`import Std.Tactic.BVDecide`, `bv_decide` (Ch 10 & Lab 5).", "chapters/10.html"),
    ("Part III", "Well-Founded Termination", "Proving a measure (`buf.size - offset`) strictly decreases on every recursive call—turning termination proofs into compile-time Denial-of-Service protection.", "`termination_by`, `decreasing_by`, `fun_induction` (Ch 11).", "chapters/11.html"),
    ("Part III", "Refinement Mapping & Stuttering", "An abstraction function `abs : Impl → Spec` proving optimized code implements a tiny spec; internal housekeeping steps (compaction, GC) satisfy `abs s' = abs s`.", "`abs (compact s) = abs s` (Ch 12).", "chapters/12.html"),
    ("Part IV", "Trusted Computing Base (TCB)", "The minimal set of components (`Spec.lean` + Lean kernel + audit gate) that must be honest for your verification guarantee to hold—excluding untrusted AI agents!", "`#print axioms` & `lake exe verigate` (Ch 13 & Lab 3).", "chapters/13.html"),
    ("Part IV", "Non-Vacuity Witness", "A companion theorem `∃ x, Pre x` proving your safety theorem's preconditions are satisfiable by real inputs—blocking vacuous `False → Anything` cheats.", "Enforced in `Spec.lean` & `verigate` (Ch 13–14).", "chapters/14.html"),
    ("Part IV", "Stream-Safe Framing", "Proving `decode (encode pkt ++ rest) = some (pkt, rest)` for all trailing bytes `rest`, ruling out TCP concatenation and frame-smuggling vulnerabilities.", "TLV packet framing (Ch 15).", "chapters/15.html"),
    ("Part IV", "Differential Reference Oracle", "Executing a mathematically verified Lean model (`lake exe oracle`) alongside a production Rust/Go/TS/Python service on thousands of adversarial traces.", "`lake exe oracle` + `fuzz_against_oracle.py` (Ch 16).", "chapters/16.html"),
]


def esc(text: str) -> str:
    return html.escape(text, quote=True)


DEFAULT_DESC = (
    "Free, hands-on Lean 4 formal verification course for software engineers. "
    "Catch protocol bugs with bounded BFS, prove invariants in Lean's kernel, and gate AI-written code."
)


def render_head(
    title: str,
    rel_prefix: str,
    canonical_subpath: str = "",
    description: str = DEFAULT_DESC,
    extra_meta: str = "",
) -> str:
    csp = (
        "default-src 'self'; "
        "script-src 'self'; "
        "style-src 'self'; "
        "img-src 'self' data:; "
        "connect-src 'none'; "
        "object-src 'none'; "
        "base-uri 'self'; "
        "form-action 'none';"
    )
    sub = canonical_subpath.lstrip("/")
    canonical_url = f"{CANONICAL_BASE}/{sub}" if sub else f"{CANONICAL_BASE}/"
    full_title = f"{title} · Prove It · indicogni"
    canonical_tag = (
        f'  <link rel="canonical" href="{esc(canonical_url)}">\n'
        f'  <meta property="og:url" content="{esc(canonical_url)}">\n'
        if canonical_subpath != "__none__"
        else ""
    )
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta http-equiv="Content-Security-Policy" content="{csp}">
  <meta name="referrer" content="strict-origin-when-cross-origin">
  <meta name="color-scheme" content="light dark">
  <meta name="theme-color" content="#FBF8F1" media="(prefers-color-scheme: light)">
  <meta name="theme-color" content="#0E1116" media="(prefers-color-scheme: dark)">
  <title>{esc(full_title)}</title>
  <meta name="description" content="{esc(description)}">
  <meta property="og:type" content="website">
  <meta property="og:site_name" content="Indicogni">
  <meta property="og:title" content="{esc(full_title)}">
  <meta property="og:description" content="{esc(description)}">
{canonical_tag}{extra_meta}  <link rel="icon" type="image/svg+xml" href="{rel_prefix}assets/favicon.svg">
  <link rel="stylesheet" href="{rel_prefix}assets/style.css">
</head>"""


def render_header(rel_prefix: str, active: str) -> str:
    def curr(name: str) -> str:
        return ' aria-current="page"' if active == name else ""

    return f"""<header class="site-header">
  <div class="nav-inner">
    <span class="brand-link">
      <a class="brand-org" href="https://indicogni.com/">indicogni</a>
      <span class="brand-sep" aria-hidden="true">/</span>
      <a class="brand-title" href="{rel_prefix}index.html">Prove It</a>
    </span>
    <nav class="nav-links" aria-label="Primary">
      <a class="nav-link" href="{rel_prefix}index.html#curriculum"{curr("curriculum")}>Curriculum</a>
      <a class="nav-link" href="{rel_prefix}labs/index.html"{curr("labs")}>6 Live Labs</a>
      <a class="nav-link" href="{rel_prefix}capstones/index.html"{curr("capstones")}>4 Capstones</a>
      <a class="nav-link" href="{rel_prefix}reference/tla-to-lean.html"{curr("tla")}>TLA+ ↔ Lean</a>
      <a class="nav-link" href="{rel_prefix}reference/ai-playbook.html"{curr("ai")}>AI Playbook</a>
      <a class="nav-link" href="{rel_prefix}reference/glossary.html"{curr("glossary")}>Glossary</a>
    </nav>
    <div class="nav-controls">
      <span class="progress-pill" data-progress-summary>0/20 units · 0/6 labs</span>
      <button type="button" class="icon-btn" data-action="open-shortcuts" title="Keyboard shortcuts (?)">Shortcuts (?)</button>
      <button type="button" class="icon-btn" data-action="toggle-theme">Dark theme (t)</button>
    </div>
  </div>
</header>"""


def render_shortcut_modal_and_footer(rel_prefix: str, extra_scripts: list[str] | None = None) -> str:
    scripts_html = f'  <script type="module" src="{rel_prefix}assets/app.js"></script>\n'
    for sc in extra_scripts or []:
        scripts_html += f'  <script type="module" src="{rel_prefix}{sc}"></script>\n'

    return f"""<div class="modal-backdrop" id="shortcut-modal" hidden role="dialog" aria-modal="true" aria-labelledby="shortcut-modal-title">
  <div class="modal-dialog">
    <div class="prediction-header">
      <h3 id="shortcut-modal-title">Keyboard Shortcuts</h3>
      <button type="button" class="btn btn-sm" data-action="close-shortcuts">Close (Esc)</button>
    </div>
    <div class="shortcut-row"><span>Step tactic forward in Infoview</span><kbd>j</kbd></div>
    <div class="shortcut-row"><span>Step tactic backward in Infoview</span><kbd>k</kbd></div>
    <div class="shortcut-row"><span>Previous unit / chapter</span><kbd>[</kbd></div>
    <div class="shortcut-row"><span>Next unit / chapter</span><kbd>]</kbd></div>
    <div class="shortcut-row"><span>Toggle Light / Dark theme</span><kbd>t</kbd></div>
    <div class="shortcut-row"><span>Open or close this help dialog</span><kbd>?</kbd></div>
  </div>
</div>

<footer class="site-footer">
  <div class="footer-inner">
    <div>
      <strong>Indicogni LLC</strong> · <em>Prove It: Formally Verified Software in Lean 4</em><br>
      Pinned to zero-dependency Core/<code>Std</code> Lean <code>v4.36.0</code>. Zero cookies, zero analytics, zero tracking.
    </div>
    <div>
      Code: MIT · Prose &amp; SVG Diagrams: CC BY 4.0 · Feedback &amp; security: <code>feedback@indicogni.com</code><br>
      <a href="https://github.com/indicogni/prove-it" target="_blank" rel="noopener noreferrer">github.com/indicogni/prove-it</a> ·
      <a href="https://live.lean-lang.org/" target="_blank" rel="noopener noreferrer">live.lean-lang.org</a>
    </div>
  </div>
</footer>
{scripts_html}</body>
</html>
"""


def svg_two_gear_diagram() -> str:
    return """<figure class="diagram-figure">
  <svg class="diagram-svg" viewBox="0 0 920 270" role="img" aria-labelledby="svg-twogear-title svg-twogear-desc">
    <title id="svg-twogear-title">The Two-Gear Verification Loop: TLA+ Bounded BFS and Lean 4 Kernel Proof</title>
    <desc id="svg-twogear-desc">System state machine flows into Gear 1 bounded BFS search to catch shallow counterexample traces in milliseconds, then into Gear 2 inductive invariants in the Lean 4 kernel to seal unbounded state spaces.</desc>
    <defs>
      <marker id="arrow-muted" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
        <path d="M 0 1 L 10 5 L 0 9 z" class="svg-head-muted"/>
      </marker>
      <marker id="arrow-accent" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
        <path d="M 0 1 L 10 5 L 0 9 z" class="svg-head-accent"/>
      </marker>
      <marker id="arrow-verified" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
        <path d="M 0 1 L 10 5 L 0 9 z" class="svg-head-verified"/>
      </marker>
      <marker id="arrow-refuted" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
        <path d="M 0 1 L 10 5 L 0 9 z" class="svg-head-refuted"/>
      </marker>
    </defs>

    <rect x="16" y="42" width="210" height="175" rx="10" class="svg-box"/>
    <text x="34" y="72" class="svg-title">1. Executable Spec</text>
    <text x="34" y="98" class="svg-mono-ink">State · Init · Next</text>
    <text x="34" y="122" class="svg-mono">Total functions (no null)</text>
    <text x="34" y="144" class="svg-mono">Sum types eliminate</text>
    <text x="34" y="162" class="svg-mono">boolean-soup states</text>
    <text x="34" y="192" class="svg-mono-ink">Chapters 01–03</text>

    <path d="M 226 115 L 288 115" class="svg-arrow-accent" marker-end="url(#arrow-accent)"/>

    <rect x="292" y="26" width="275" height="132" rx="10" class="svg-box-open"/>
    <text x="312" y="55" class="svg-title">2. Gear 1 · TLA+ BFS Search</text>
    <text x="312" y="80" class="svg-mono-ink">#guard bfs depth≤6 == .safe</text>
    <text x="312" y="103" class="svg-mono">Explores packet delays, crashes,</text>
    <text x="312" y="121" class="svg-mono">&amp; interleavings in &lt;5 ms</text>
    <text x="312" y="144" class="svg-mono-ink">Chapter 04 · Browser Lab 2</text>

    <rect x="292" y="180" width="275" height="72" rx="8" class="svg-box-refuted"/>
    <text x="312" y="205" class="svg-label">Shortest Counterexample Trace</text>
    <text x="312" y="227" class="svg-mono">[c1Send, c2Commit, deliverStale]</text>
    <text x="312" y="243" class="svg-mono">Fix spec/code BEFORE proving!</text>

    <path d="M 430 158 L 430 178" class="svg-arrow-refuted" marker-end="url(#arrow-refuted)"/>
    <path d="M 292 216 L 120 216 L 120 219" class="svg-arrow-refuted"/>

    <path d="M 567 92 L 628 92" class="svg-arrow-verified" marker-end="url(#arrow-verified)"/>

    <rect x="632" y="26" width="272" height="226" rx="10" class="svg-box-verified"/>
    <text x="652" y="55" class="svg-title">3. Gear 2 · Lean 4 Kernel</text>
    <text x="652" y="80" class="svg-mono-ink">Unbounded Mathematical Proof</text>
    <text x="652" y="106" class="svg-mono">• Init s → Inv s</text>
    <text x="652" y="126" class="svg-mono">• Inv s → Next s s' → Inv s'</text>
    <text x="652" y="146" class="svg-mono">• abs (compact s) = abs s</text>
    <text x="652" y="168" class="svg-mono">• BitVec 64 wrap-around sealed</text>
    <text x="652" y="196" class="svg-label">Infinite epochs &amp; 2^64 states</text>
    <text x="652" y="222" class="svg-mono-ink">Chapters 08–12 · Zero sorry</text>
  </svg>
  <figcaption class="diagram-caption">
    <strong>Architecture 1 — The Two-Gear Verification Loop:</strong> Never burn hours attempting an inductive proof on a buggy protocol. Gear 1 falsifies shallow bugs with concrete traces in milliseconds; Gear 2 seals unbounded epochs, arbitrary message reorderings, and 64-bit hardware boundaries inside Lean's tiny trusted kernel.
  </figcaption>
</figure>"""


def svg_verigate_diagram() -> str:
    return """<figure class="diagram-figure">
  <svg class="diagram-svg" viewBox="0 0 920 265" role="img" aria-labelledby="svg-verigate-title svg-verigate-desc">
    <title id="svg-verigate-title">The AI Vericoding Gate: Locked Human Spec vs Untrusted Coding Agent</title>
    <desc id="svg-verigate-desc">Human engineers lock Spec.lean and non-vacuity witnesses while untrusted AI agents synthesize Impl.lean and tactic proofs; lake exe verigate blocks all 9 exploit vectors before deployment or oracle fuzzing.</desc>
    <defs>
      <marker id="vg-accent" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
        <path d="M 0 1 L 10 5 L 0 9 z" class="svg-head-accent"/>
      </marker>
      <marker id="vg-verified" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
        <path d="M 0 1 L 10 5 L 0 9 z" class="svg-head-verified"/>
      </marker>
      <marker id="vg-refuted" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
        <path d="M 0 1 L 10 5 L 0 9 z" class="svg-head-refuted"/>
      </marker>
    </defs>

    <rect x="16" y="22" width="248" height="102" rx="10" class="svg-box-accent"/>
    <text x="34" y="49" class="svg-title">Human TCB · Spec.lean</text>
    <text x="34" y="72" class="svg-mono-ink">SHA-256 Pinned · Read-Only</text>
    <text x="34" y="93" class="svg-mono">Domain types + Soundness</text>
    <text x="34" y="111" class="svg-mono">+ Non-vacuity (∃ x, Pre x)</text>

    <rect x="16" y="142" width="248" height="102" rx="10" class="svg-box"/>
    <text x="34" y="169" class="svg-title">Untrusted Agent · Impl.lean</text>
    <text x="34" y="192" class="svg-mono-ink">100x Fast Synthesis, Zero Trust</text>
    <text x="34" y="213" class="svg-mono">Optimized algorithms + tactics</text>
    <text x="34" y="231" class="svg-mono">(may attempt spec-gaming!)</text>

    <path d="M 264 74 L 328 112" class="svg-arrow-accent" marker-end="url(#vg-accent)"/>
    <path d="M 264 192 L 328 152" class="svg-arrow-accent" marker-end="url(#vg-accent)"/>

    <rect x="332" y="34" width="286" height="196" rx="10" class="svg-box-verified"/>
    <text x="352" y="63" class="svg-title">lake exe verigate (CI Gate)</text>
    <text x="352" y="88" class="svg-mono-ink">1. Lean Kernel Typecheck</text>
    <text x="352" y="110" class="svg-mono">2. Spec SHA-256 Integrity Check</text>
    <text x="352" y="130" class="svg-mono">3. Axiom Whitelist (Tier 0 / Tier 1)</text>
    <text x="352" y="150" class="svg-mono">4. Ban @[implemented_by] / @[extern]</text>
    <text x="352" y="170" class="svg-mono">5. Ban raw native_decide &amp; sorryAx</text>
    <text x="352" y="190" class="svg-mono">6. Verify Non-Vacuity Witness</text>
    <text x="352" y="214" class="svg-mono-ink">Chapters 13–14 · Browser Lab 6</text>

    <path d="M 618 92 L 676 68" class="svg-arrow-refuted" marker-end="url(#vg-refuted)"/>
    <rect x="680" y="24" width="224" height="86" rx="8" class="svg-box-refuted"/>
    <text x="698" y="50" class="svg-label">Reject Cheating PRs</text>
    <text x="698" y="72" class="svg-mono">sorry · custom axiom · csimp</text>
    <text x="698" y="92" class="svg-mono">False → Safe · Spec drift</text>

    <path d="M 618 168 L 676 184" class="svg-arrow-verified" marker-end="url(#vg-verified)"/>
    <rect x="680" y="134" width="224" height="106" rx="8" class="svg-box-verified"/>
    <text x="698" y="160" class="svg-label">Verified Artifact + Oracle</text>
    <text x="698" y="182" class="svg-mono-ink">lake exe oracle</text>
    <text x="698" y="203" class="svg-mono">Differential-fuzz Rust, Go,</text>
    <text x="698" y="221" class="svg-mono">TS &amp; Python in CI (Ch 16)</text>
  </svg>
  <figcaption class="diagram-caption">
    <strong>Architecture 2 — The AI Vericoding Gate:</strong> Coding agents share correlated blind spots when writing both code and unit tests. Locking human-owned specifications and auditing kernel axioms/attributes turns Lean 4 into an unforgeable sandbox for AI-generated software.
  </figcaption>
</figure>"""


def build_chapter_data_js() -> None:
    payload = {}
    for u in UNITS:
        payload[u["id"]] = {
            "prediction": u["prediction"],
            "workbench": u["workbench"],
        }
    js_content = (
        "// Auto-generated by scripts/build_site.py — Socratic predictions & simulated Lean 4.36.0 Infoview states.\n"
        "export const CHAPTER_INTERACTIVES = "
        + json.dumps(payload, indent=2, ensure_ascii=False)
        + ";\n"
    )
    (SITE_DIR / "assets" / "chapter-data.js").write_text(js_content, encoding="utf-8")


def build_landing_page() -> None:
    unit_by_id = {u["id"]: u for u in UNITS}

    curriculum_html = ""
    for p in PARTS:
        rows = ""
        for uid in p["units"]:
            u = unit_by_id[uid]
            cp_cls = " is-checkpoint" if uid.startswith("cp") else ""
            rows += f"""      <li>
        <a class="chapter-row{cp_cls}" href="chapters/{uid}.html" data-unit-row="{uid}">
          <span class="chapter-num">{esc(u["code"])}</span>
          <span class="chapter-info">
            <strong>{esc(u["title"])}</strong>
            <span>{esc(u["subtitle"])}</span>
          </span>
          <span class="chapter-status-pill" data-unit-status>Unread</span>
        </a>
      </li>\n"""
        curriculum_html += f"""    <details class="part-details" open>
      <summary class="part-summary">
        <span>{esc(p["title"])}</span>
        <span class="badge">{len(p["units"])} units</span>
      </summary>
      <ul class="chapter-list">
{rows}      </ul>
    </details>\n"""

    capstones_cards = ""
    for cap in CAPSTONES:
        capstones_cards += f"""      <article class="card card-elevated">
        <span class="badge badge-accent">{esc(cap["badge"])}</span>
        <h3>{esc(cap["title"])}</h3>
        <p>{esc(cap["summary"])}</p>
        <p><code>{esc(cap["path"])}</code></p>
        <a class="btn btn-sm" href="capstones/index.html#{esc(cap["id"])}">Inspect Capstone &amp; Run in Browser →</a>
      </article>\n"""

    page = f"""{render_head("Formally Verified Software in Lean 4", "", "")}
<body>
{render_header("", "curriculum")}
<main class="container-wide">
  <section class="resume-banner" id="resume-banner" hidden aria-label="Course progress">
    <div class="resume-meta">
      <span class="resume-eyebrow">Continue where you left off</span>
      <strong id="resume-title">Chapter 01 · Silent Truncation Bug</strong>
    </div>
    <div class="resume-actions">
      <a class="btn btn-sm btn-primary" id="resume-link" href="chapters/01.html">Resume unit →</a>
      <button type="button" class="btn btn-sm" data-action="export-progress">Export progress JSON</button>
      <button type="button" class="btn btn-sm btn-danger" data-action="reset-progress">Reset progress</button>
    </div>
  </section>

  <section class="hero">
    <span class="eyebrow">Indicogni Interactive Engineering Course · Lean 4.36.0</span>
    <h1 class="hero-title">Don't hope the AI's code works. <em>Prove</em> it.</h1>
    <p class="hero-subtitle">
      A hands-on software and distributed-systems verification course for working engineers. Skip Peano arithmetic warmups and multi-gigabyte library downloads: catch protocol bugs with a 35-line TLA+ state explorer, seal 64-bit hardware invariants in Lean's kernel, audit untrusted AI code with <code>verigate</code>, and differential-fuzz Rust/Go/TS services against <code>oracle</code>.
    </p>
    <div class="hero-cta-row">
      <a class="btn btn-primary" href="chapters/01.html">Start Chapter 01: Silent Truncation →</a>
      <a class="btn" href="labs/index.html">Explore 6 Live Browser Labs</a>
      <a class="btn" href="capstones/index.html">View 4 Capstones</a>
      <a class="btn" href="https://github.com/indicogni/prove-it" target="_blank" rel="noopener noreferrer">GitHub Workspace ↗</a>
    </div>

    <div class="stats-bar">
      <div class="stat-card">
        <span class="stat-value">16 chapters</span>
        <span class="stat-label">+ 4 closed-notes synthesis checkpoints</span>
      </div>
      <div class="stat-card">
        <span class="stat-value">4 capstones</span>
        <span class="stat-label">CedarLite, FencingKV, StackVM, VeriGate</span>
      </div>
      <div class="stat-card">
        <span class="stat-value">6 live labs</span>
        <span class="stat-label">Zero-install BFS, BitVec, Erasure &amp; Red-Team</span>
      </div>
      <div class="stat-card">
        <span class="stat-value">$0 / Zero tracking</span>
        <span class="stat-label">No cookies, no telemetry, offline-ready</span>
      </div>
    </div>
  </section>

  <section aria-labelledby="dual-mode-heading">
    <h2 id="dual-mode-heading">Dual-Mode Learning: Zero-Setup Browser + Full Local Lake Toolchain</h2>
    <div class="grid-2">
      <div class="card card-elevated">
        <span class="badge badge-verified">Mode 1 · Runs in your browser</span>
        <h3>Zero Install, Instant Proof Intuition</h3>
        <p>
          Every chapter opens with a concrete 5-line production bug, locks your Socratic prediction before revealing the mechanism, lets you step line-by-line through a simulated <strong>Lean 4 Infoview</strong> (<kbd>j</kbd> / <kbd>k</kbd>), and launches standalone zero-dependency code in one click on <a href="https://live.lean-lang.org/" target="_blank" rel="noopener noreferrer">live.lean-lang.org</a>.
        </p>
        <a class="btn btn-sm" href="labs/index.html">Open Browser Labs →</a>
      </div>
      <div class="card card-elevated">
        <span class="badge badge-accent">Mode 2 · Your machine or Codespaces</span>
        <h3>Production Proof Engineering &amp; CI Gates</h3>
        <p>
          Clone <a href="https://github.com/indicogni/prove-it" target="_blank" rel="noopener noreferrer">indicogni/prove-it</a> or launch GitHub Codespaces. Because we pin pure Core/<code>Std</code> Lean <code>v4.36.0</code> with zero external packages, cold <code>lake build</code> finishes in seconds offline—complete with <code>lake exe check</code>, <code>lake exe verigate</code>, and <code>lake exe oracle</code>.
        </p>
        <button type="button" class="btn btn-sm" data-copy-text="git clone https://github.com/indicogni/prove-it.git && cd prove-it && lake build">Copy clone &amp; build command</button>
      </div>
    </div>
  </section>

  <section aria-labelledby="arch-heading">
    <h2 id="arch-heading">How Systems Verification &amp; AI Supervision Fit Together</h2>
    {svg_two_gear_diagram()}
    {svg_verigate_diagram()}
  </section>

  <section id="curriculum" aria-labelledby="curriculum-heading">
    <h2 id="curriculum-heading">Complete 4-Part Curriculum (16 Chapters + 4 Checkpoints)</h2>
    <p>Progress is stored locally in your browser (<code>localStorage["indicogni.proveit.v1"]</code>) and never transmitted anywhere.</p>
{curriculum_html}
  </section>

  <section aria-labelledby="capstones-heading">
    <h2 id="capstones-heading">The 4 Production Capstones</h2>
    <div class="grid-2">
{capstones_cards}
    </div>
  </section>

  <section aria-labelledby="ref-heading">
    <h2 id="ref-heading">Field Reference &amp; Monday-Morning Playbooks</h2>
    <div class="grid-2">
      <div class="card">
        <h3><a href="reference/tla-to-lean.html">TLA+ ↔ Lean 4 Rosetta Stone</a></h3>
        <p>Side-by-side translation of <code>VARIABLES</code>, <code>Init</code>, <code>Next</code>, <code>UNCHANGED</code>, TLC BFS, inductive invariants, and stuttering refinement.</p>
      </div>
      <div class="card">
        <h3><a href="reference/ai-playbook.html">Spec-First AI Playbook &amp; Polyglot Oracle</a></h3>
        <p>Copyable agent prompts, <code>VeriGate</code> GitHub Actions workflow, and Rust / Go / TypeScript / Python differential-fuzzing harnesses.</p>
      </div>
    </div>
  </section>
</main>
{render_shortcut_modal_and_footer("")}"""
    (SITE_DIR / "index.html").write_text(page, encoding="utf-8")


def build_chapter_pages() -> None:
    chapters_dir = SITE_DIR / "chapters"
    chapters_dir.mkdir(parents=True, exist_ok=True)

    for idx, u in enumerate(UNITS):
        prev_u = UNITS[idx - 1] if idx > 0 else None
        next_u = UNITS[idx + 1] if idx + 1 < len(UNITS) else None

        prev_attr = f' data-prev-href="{prev_u["id"]}.html"' if prev_u else ""
        next_attr = f' data-next-href="{next_u["id"]}.html"' if next_u else ""

        prose_html = ""
        for sec_title, paragraphs in u["prose"]:
            prose_html += f"    <h2>{esc(sec_title)}</h2>\n"
            for para in paragraphs:
                # Allow inline code backticks rendered cleanly
                parts = para.split("`")
                rendered_parts = []
                for p_i, chunk in enumerate(parts):
                    if p_i % 2 == 1:
                        rendered_parts.append(f"<code>{esc(chunk)}</code>")
                    else:
                        # Handle **bold** and *italic* cleanly
                        b_parts = chunk.split("**")
                        b_out = []
                        for b_i, b_chunk in enumerate(b_parts):
                            if b_i % 2 == 1:
                                b_out.append(f"<strong>{esc(b_chunk)}</strong>")
                            else:
                                i_parts = b_chunk.split("*")
                                i_out = []
                                for i_i, i_chunk in enumerate(i_parts):
                                    if i_i % 2 == 1:
                                        i_out.append(f"<em>{esc(i_chunk)}</em>")
                                    else:
                                        i_out.append(esc(i_chunk))
                                b_out.append("".join(i_out))
                        rendered_parts.append("".join(b_out))
                prose_html += f"    <p>{''.join(rendered_parts)}</p>\n"

        playground_url = "https://live.lean-lang.org/#code=" + urllib.parse.quote(
            u["workbench"]["playgroundCode"], safe=""
        )

        prev_card = (
            f'<a class="pager-card" href="{prev_u["id"]}.html">'
            f'<span class="pager-dir">← Previous ([) · {esc(prev_u["code"])}</span>'
            f'<span class="pager-title">{esc(prev_u["title"])}</span></a>'
            if prev_u
            else '<a class="pager-card" href="../index.html">'
                 '<span class="pager-dir">← Course Home</span>'
                 '<span class="pager-title">Curriculum Overview</span></a>'
        )
        next_card = (
            f'<a class="pager-card align-right" href="{next_u["id"]}.html">'
            f'<span class="pager-dir">Next (]) · {esc(next_u["code"])} →</span>'
            f'<span class="pager-title">{esc(next_u["title"])}</span></a>'
            if next_u
            else '<a class="pager-card align-right" href="../capstones/index.html">'
                 '<span class="pager-dir">Up Next →</span>'
                 '<span class="pager-title">The 4 Production Capstones</span></a>'
        )

        unit_full_title = f"{u['code']}: {u['title']}"

        page = f"""{render_head(unit_full_title, "../", f"chapters/{u['id']}", u["subtitle"])}
<body data-unit-id="{u['id']}" data-unit-title="{esc(unit_full_title)}"{prev_attr}{next_attr}>
{render_header("../", "curriculum")}
<main class="chapter-shell">
  <div class="chapter-header">
    <div class="chapter-topbar">
      <span class="badge badge-accent">{esc(u["part"])}</span>
      <span class="badge">{esc(u["code"])} · {esc(u["est"])} · <code>{esc(u["lean_file"])}</code></span>
    </div>
    <h1>{esc(u["title"])}</h1>
    <p class="hero-subtitle">{esc(u["subtitle"])}</p>

    <div class="puzzle-box">
      <span class="puzzle-title">{esc(u["puzzle_title"])}</span>
      <pre><code>{esc(u["puzzle_code"])}</code></pre>
    </div>

    <section class="prediction-card" id="prediction-card" aria-labelledby="pred-heading">
      <div class="prediction-header">
        <strong id="pred-heading">Socratic Gate · Commit to a Prediction</strong>
        <span class="badge badge-open" data-prediction-status>Unanswered · Locks on commit</span>
      </div>
      <p>{esc(u["prediction"]["question"])}</p>
      <div class="prediction-options" data-prediction-options></div>
      <button type="button" class="btn btn-primary btn-sm" data-action="lock-prediction" disabled>Lock Prediction &amp; Reveal Mechanism</button>
      <div class="prediction-reveal" data-prediction-reveal hidden>
        <strong>Why this happens:</strong>
        <p data-prediction-explanation></p>
      </div>
    </section>
  </div>

  <article class="container-prose">
{prose_html}
  </article>

  <section class="workbench" id="chapter-workbench" aria-label="Interactive Lean 4 Infoview Stepper">
    <div class="workbench-toolbar">
      <div class="workbench-title">
        <span>⊢</span>
        <span>{esc(u["workbench"]["title"])}</span>
      </div>
      <div class="stepper-controls">
        <button type="button" class="btn btn-sm" data-action="step-reset">⏮ Reset</button>
        <button type="button" class="btn btn-sm" data-action="step-prev">← Prev (k)</button>
        <span class="step-counter" data-step-counter>Step 1 / 1</span>
        <button type="button" class="btn btn-sm btn-primary" data-action="step-next">Next (j) →</button>
      </div>
    </div>

    <div class="workbench-split">
      <div class="code-pane" aria-label="Lean 4 source code">
        <div class="code-lines" data-code-lines></div>
      </div>
      <div class="infoview-pane" aria-live="polite" aria-label="Simulated Lean 4 Infoview">
        <div class="infoview-header">
          <span class="infoview-title">Lean Infoview</span>
          <span class="badge badge-open" data-goal-badge>Open Goal</span>
        </div>
        <div>
          <span class="infoview-section-label">Objects</span>
          <div class="infoview-block" data-infoview-objects></div>
        </div>
        <div>
          <span class="infoview-section-label">Hypotheses</span>
          <div class="infoview-block" data-infoview-hyps></div>
        </div>
        <div>
          <span class="infoview-section-label">⊢ Current Goal</span>
          <div class="infoview-block infoview-goal" data-infoview-goal></div>
        </div>
        <div class="infoview-note" data-infoview-note></div>
      </div>
    </div>

    <div class="workbench-footer">
      <div class="action-group">
        <a class="btn btn-primary btn-sm" data-playground-link href="{playground_url}" target="_blank" rel="noopener noreferrer">Run in Lean 4 Playground ↗</a>
        <button type="button" class="btn btn-sm" data-action="copy-lean">Copy Lean snippet</button>
      </div>
      <div class="action-group">
        <button type="button" class="btn btn-sm" data-copy-text="{esc(u['lake_cmd'])}">Copy local command: <code>{esc(u['lake_cmd'])}</code></button>
      </div>
    </div>
  </section>

  <div class="container-prose">
    <div class="callout callout-verified">
      <strong>Hands-On Exercise ({esc(u["lean_file"])}):</strong>
      <p>{esc(u["takeaway"])}</p>
    </div>

    <div class="chapter-complete-bar">
      <div>
        <strong>Finished the Socratic gate, Infoview trace, and playground run?</strong><br>
        <span>Record completion in local browser storage to track your 20-unit progress.</span>
      </div>
      <button type="button" class="btn btn-verified" data-action="toggle-complete">Mark chapter complete</button>
    </div>

    <nav class="chapter-pager" aria-label="Chapter pagination">
      {prev_card}
      {next_card}
    </nav>
  </div>
</main>
{render_shortcut_modal_and_footer("../")}"""
        (chapters_dir / f"{u['id']}.html").write_text(page, encoding="utf-8")


def build_labs_page() -> None:
    labs_dir = SITE_DIR / "labs"
    labs_dir.mkdir(parents=True, exist_ok=True)

    page = f"""{render_head("6 Interactive Browser Labs", "../", "labs/")}
<body>
{render_header("../", "labs")}
<main class="container-wide">
  <span class="eyebrow">Zero-Install Client-Side Simulators</span>
  <h1>6 Interactive Verification Labs</h1>
  <p class="hero-subtitle">
    Experiment directly in your browser with tactic goal transformations, TLA+ split-brain BFS search vs. inductive invariant funnels, kernel axiom taint graphs, zero-byte proof erasure, 64-bit hardware wrap-around, and adversarial AI red-teaming.
  </p>

  <nav class="lab-nav" aria-label="Jump to Lab">
    <a class="btn btn-sm" href="#lab-1">Lab 1 · Infoview &amp; Tactics</a>
    <a class="btn btn-sm" href="#lab-2">Lab 2 · Split-Brain BFS vs Funnel</a>
    <a class="btn btn-sm" href="#lab-3">Lab 3 · Kernel &amp; #print axioms DAG</a>
    <a class="btn btn-sm" href="#lab-4">Lab 4 · Proof Erasure &amp; Decidable</a>
    <a class="btn btn-sm" href="#lab-5">Lab 5 · 64-Bit BitVec vs Nat</a>
    <a class="btn btn-sm" href="#lab-6">Lab 6 · AI Spec-Gaming Red-Team</a>
  </nav>

  <!-- LAB 1 -->
  <section class="lab-card" id="lab-1">
    <div class="prediction-header">
      <span class="badge badge-accent">Lab 1 · Chapters 01, 05 &amp; 06</span>
      <span class="badge badge-open" id="lab1-badge">Open Goal</span>
    </div>
    <h2>Interactive Lean Infoview &amp; Tactic Stepper</h2>
    <p>Select a theorem, step with <kbd>j</kbd> / <kbd>k</kbd>, or test tactics directly from the palette to see why applicable tactics advance the goal and mismatched tactics fail.</p>
    <div id="lab1-root">
      <div class="lab-controls">
        <label for="lab1-select"><strong>Theorem:</strong></label>
        <select id="lab1-select" class="lab-select">
          <option value="quota">1. Safe Quota Withdraw Conservation</option>
          <option value="canary">2. Canary Router Fail-Closed Default</option>
          <option value="idempotent">3. Idempotent Write-Ahead Ledger Replay</option>
        </select>
        <button type="button" class="btn btn-sm" id="lab1-reset">⏮ Reset</button>
        <button type="button" class="btn btn-sm" id="lab1-prev">← Prev (k)</button>
        <button type="button" class="btn btn-sm btn-primary" id="lab1-next">Next (j) →</button>
        <a class="btn btn-sm" id="lab1-playground" href="https://live.lean-lang.org/" target="_blank" rel="noopener noreferrer">Run in Playground ↗</a>
      </div>
      <div class="lab-controls" id="lab1-palette">
        <strong>Apply tactic:</strong>
      </div>
      <p class="step-counter" id="lab1-counter"></p>
      <div class="lab-output-grid">
        <div>
          <span class="infoview-section-label">Objects</span>
          <div class="infoview-block" id="lab1-objects"></div>
          <span class="infoview-section-label">Hypotheses</span>
          <div class="infoview-block" id="lab1-hyps"></div>
        </div>
        <div>
          <span class="infoview-section-label">⊢ Goal</span>
          <div class="infoview-block infoview-goal" id="lab1-goal"></div>
          <span class="infoview-section-label">Coach Feedback</span>
          <div class="infoview-note" id="lab1-feedback"></div>
        </div>
      </div>
    </div>
  </section>

  <!-- LAB 2 -->
  <section class="lab-card" id="lab-2">
    <div class="prediction-header">
      <span class="badge badge-accent">Lab 2 · Chapters 04 &amp; 08 + Capstone 2</span>
      <span class="badge badge-refuted" id="lab2-status">Running BFS...</span>
    </div>
    <h2>Fencing-Lease Split-Brain BFS Explorer vs. Inductive Invariant Funnel</h2>
    <p>Toggle network delay / GC pause and monotonic fencing tokens (`msg.epoch ≥ storage.fencedEpoch`). Watch Gear 1 BFS discover a live split-brain trace when unfenced, then inspect why Gear 2 needs invariant strengthening to exclude Garden-of-Eden states.</p>
    <div class="lab-controls">
      <label class="toggle-label">
        <input type="checkbox" id="lab2-delay" checked>
        Simulate GC Pause / Delayed Network Packet
      </label>
      <label class="toggle-label">
        <input type="checkbox" id="lab2-fence">
        Enable Monotonic Fencing Guard (<code>txEpoch ≥ storageEpoch</code>)
      </label>
      <button type="button" class="btn btn-sm" id="lab2-garden-btn">Test Unreachable Garden-of-Eden State</button>
    </div>
    <div class="lab-output-grid">
      <div>
        <span class="infoview-section-label">Gear 1 · Live BFS State-Space Trace</span>
        <ul class="trace-list" id="lab2-trace"></ul>
      </div>
      <div>
        <span class="infoview-section-label">Gear 2 · State-Space Invariant Funnel</span>
        <div class="funnel-ring">
          <strong>All Syntactic States</strong> (arbitrary struct values)
          <div class="funnel-ring funnel-safe">
            <strong>Safe States</strong> (<code>¬corrupted</code> — includes Garden-of-Eden traps!)
            <div class="funnel-ring funnel-inductive">
              <strong>Strengthened Inductive Invariant</strong> (<code>¬corrupted ∧ (committedEp2 → storageEpoch ≥ 2)</code>)
              <div class="funnel-ring funnel-reachable">
                <strong>Reachable States</strong> (from <code>Init</code> via <code>Next*</code> across ∞ epochs)
              </div>
            </div>
          </div>
        </div>
        <div class="infoview-note" id="lab2-funnel-note"></div>
      </div>
    </div>
  </section>

  <!-- LAB 3 -->
  <section class="lab-card" id="lab-3">
    <div class="prediction-header">
      <span class="badge badge-accent">Lab 3 · Chapters 10 &amp; 13 + VeriGate</span>
      <div class="action-group">
        <span class="badge badge-verified" id="lab3-tier0">Tier 0: PASS</span>
        <span class="badge badge-verified" id="lab3-tier1">Tier 1: PASS</span>
      </div>
    </div>
    <h2>Kernel Trust &amp; <code>#print axioms</code> Taint DAG Inspector</h2>
    <p>Toggle proof tactics and compiler attributes to see what enters <code>#print axioms</code>, which exploits hide outside <code>#print axioms</code>, and how <code>lake exe verigate</code> enforces Tier 0 vs. Tier 1 soundness.</p>
    <div id="lab3-root">
      <div class="lab-controls">
        <label class="toggle-label"><input type="checkbox" id="lab3-core" checked disabled> Core Kernel (<code>rfl</code>/<code>omega</code>/<code>grind</code>)</label>
        <label class="toggle-label"><input type="checkbox" id="lab3-classical" checked> Classical (<code>byContradiction</code>)</label>
        <label class="toggle-label"><input type="checkbox" id="lab3-bv"> <code>bv_decide</code> (Verified LRAT)</label>
        <label class="toggle-label"><input type="checkbox" id="lab3-native"> Raw <code>native_decide</code></label>
        <label class="toggle-label"><input type="checkbox" id="lab3-axiom"> Custom <code>axiom</code></label>
        <label class="toggle-label"><input type="checkbox" id="lab3-sorry"> <code>sorry</code></label>
        <label class="toggle-label"><input type="checkbox" id="lab3-implby"> <code>@[implemented_by]</code></label>
      </div>
      <span class="infoview-section-label">Simulated Lean <code>#print axioms withdraw_safe</code> Output</span>
      <div class="infoview-block" id="lab3-axioms-out"></div>
      <div class="infoview-note" id="lab3-explain"></div>
    </div>
  </section>

  <!-- LAB 4 -->
  <section class="lab-card" id="lab-4">
    <div class="prediction-header">
      <span class="badge badge-accent">Lab 4 · Chapters 03 &amp; 09</span>
      <span class="badge badge-verified" id="lab4-badge">Proof Erased to 0 Bytes</span>
    </div>
    <h2>Runtime Proof Erasure &amp; <code>Decidable</code> Bridge Inspector</h2>
    <p>Adjust ring-buffer index, capacity, and RBAC role to compare the compile-time elaborated Lean kernel term (carrying proof witnesses) against the proof-erased LCNF / C representation emitted at runtime.</p>
    <div class="lab-controls">
      <label for="lab4-idx"><strong>Index:</strong></label>
      <input type="number" id="lab4-idx" class="lab-input" value="5" min="0" max="999">
      <label for="lab4-cap"><strong>Capacity:</strong></label>
      <input type="number" id="lab4-cap" class="lab-input" value="16" min="1" max="999">
      <label for="lab4-role"><strong>Role:</strong></label>
      <select id="lab4-role" class="lab-select">
        <option value="Admin">Admin</option>
        <option value="Developer">Developer</option>
        <option value="Guest">Guest</option>
      </select>
    </div>
    <div class="lab-output-grid">
      <div>
        <span class="infoview-section-label">Compile-Time Kernel Term (With Proof Witnesses)</span>
        <div class="infoview-block" id="lab4-elaborated"></div>
      </div>
      <div>
        <span class="infoview-section-label">Compiled Runtime LCNF / C (Zero-Byte Proof Overhead)</span>
        <div class="infoview-block" id="lab4-compiled"></div>
      </div>
    </div>
  </section>

  <!-- LAB 5 -->
  <section class="lab-card" id="lab-5">
    <div class="prediction-header">
      <span class="badge badge-accent">Lab 5 · Chapters 01 &amp; 10</span>
      <span class="badge badge-refuted" id="lab5-status">Divergence Check</span>
    </div>
    <h2>64-Bit <code>BitVec</code> Overflow vs. Mathematical <code>Nat</code> Truncation Explorer</h2>
    <p>Compare unbounded/saturating <code>Nat</code> semantics against exact 64-bit hardware register arithmetic (<code>UInt64</code> / <code>BitVec 64</code>) across classic systems bugs.</p>
    <div class="lab-controls">
      <label for="lab5-preset"><strong>Bug Preset:</strong></label>
      <select id="lab5-preset" class="lab-select">
        <option value="underflow">0 - 1 (Nat Saturating 0 vs UInt64 Wrap)</option>
        <option value="maxwrap">MAX_UINT64 + 1 (Epoch Counter Wrap)</option>
        <option value="midpoint">(lo + hi) / 2 at 2^63 (Binary Search Midpoint Bug)</option>
        <option value="escrow">Escrow Deposit Wrap (2^64 - 10 + 25)</option>
      </select>
      <input type="text" id="lab5-a" class="lab-input" value="0" aria-label="Operand A">
      <select id="lab5-op" class="lab-select" aria-label="Operation">
        <option value="sub" selected>a - b</option>
        <option value="add">a + b</option>
        <option value="mid">(a + b) / 2</option>
      </select>
      <input type="text" id="lab5-b" class="lab-input" value="1" aria-label="Operand B">
    </div>
    <div class="lab-output-grid">
      <div class="infoview-block" id="lab5-nat"></div>
      <div class="infoview-block" id="lab5-bv"></div>
    </div>
    <span class="infoview-section-label">64-Bit Hardware Register Bit-Strip (16 Hex Nibbles · Bit 63 → Bit 0)</span>
    <div class="bit-strip" id="lab5-bits"></div>
    <div class="infoview-note" id="lab5-note"></div>
  </section>

  <!-- LAB 6 -->
  <section class="lab-card" id="lab-6">
    <div class="prediction-header">
      <span class="badge badge-accent">Lab 6 · Chapters 13–15 + CP4</span>
      <span class="badge badge-open" id="lab6-score">0 / 5 exploits caught</span>
    </div>
    <h2>AI Spec-Gaming Red-Team Trap Detector</h2>
    <p>Five autonomous coding-agent PRs compiled with zero <code>sorry</code>s. Inspect the submitted code and <code>#print axioms</code> output for each PR, and identify the exact exploit vector!</p>
    <div class="lab-controls" id="lab6-tabs"></div>
    <div class="lab-output-grid">
      <div>
        <span class="infoview-section-label">Untrusted Agent Submission</span>
        <div class="infoview-block" id="lab6-code"></div>
        <span class="infoview-section-label"><code>#print axioms</code> Output</span>
        <div class="infoview-block" id="lab6-axioms"></div>
      </div>
      <div>
        <span class="infoview-section-label">Classify the Exploit Vector</span>
        <div class="prediction-options" id="lab6-choices"></div>
        <div class="infoview-note" id="lab6-result">Inspect PR #101 and choose the exploit vector above.</div>
      </div>
    </div>
  </section>
</main>
{render_shortcut_modal_and_footer("../", ["assets/labs.js"])}"""
    (labs_dir / "index.html").write_text(page, encoding="utf-8")


def build_capstones_page() -> None:
    cap_dir = SITE_DIR / "capstones"
    cap_dir.mkdir(parents=True, exist_ok=True)

    sections_html = ""
    for idx, cap in enumerate(CAPSTONES, start=1):
        code_id = f"cap-code-{idx}"
        play_url = "https://live.lean-lang.org/#code=" + urllib.parse.quote(cap["playground"], safe="")
        inv_items = "".join(f"<li>{esc(inv)}</li>" for inv in cap["invariants"])

        sections_html += f"""  <section class="lab-card" id="{esc(cap['id'])}">
    <div class="prediction-header">
      <span class="badge badge-accent">{esc(cap["badge"])}</span>
      <code>{esc(cap["path"])}</code>
    </div>
    <h2>{esc(cap["title"])}</h2>
    <p>{esc(cap["summary"])}</p>
    <h3>Core Theorems &amp; Engineering Guarantees</h3>
    <ul>{inv_items}</ul>
    <h3>Self-Contained Verified Preview (Lean 4.36.0)</h3>
    <pre><code id="{code_id}">{esc(cap["playground"])}</code></pre>
    <div class="action-group">
      <a class="btn btn-primary btn-sm" href="{play_url}" target="_blank" rel="noopener noreferrer">Run Capstone Slice in Lean 4 Playground ↗</a>
      <button type="button" class="btn btn-sm" data-copy-target="{code_id}">Copy Lean preview</button>
      <button type="button" class="btn btn-sm" data-copy-text="{esc(cap['check_cmd'])}">Copy local command: <code>{esc(cap['check_cmd'])}</code></button>
    </div>
  </section>\n"""

    page = f"""{render_head("4 Production Capstones", "../", "capstones/")}
<body>
{render_header("../", "capstones")}
<main class="container-wide">
  <span class="eyebrow">Industrial Verification Suites</span>
  <h1>The 4 Production Capstones</h1>
  <p class="hero-subtitle">
    Move beyond toy exercises into four real-world verification domains: cloud IAM authorization, distributed split-brain lease storage, optimizing bytecode compilation, and proof-carrying AI supervision + polyglot differential fuzzing.
  </p>
  <p>
    Each capstone ships with a starter specification in <code>ProveIt/Capstones/</code>, architectural notes in <code>capstones/*/README.md</code>, and a 100% zero-<code>sorry</code> verified solution in <code>Solutions/Capstones/</code>. Every standalone preview below compiles directly in <a href="https://live.lean-lang.org/" target="_blank" rel="noopener noreferrer">live.lean-lang.org</a>.
  </p>
{sections_html}
</main>
{render_shortcut_modal_and_footer("../", ["assets/reference.js"])}"""
    (cap_dir / "index.html").write_text(page, encoding="utf-8")


def build_reference_pages() -> None:
    ref_dir = SITE_DIR / "reference"
    ref_dir.mkdir(parents=True, exist_ok=True)

    # 1. TLA+ <-> Lean 4 Rosetta Stone
    rosetta_cards = ""
    for idx, item in enumerate(ROSETTA_ITEMS, start=1):
        lean_id = f"rosetta-lean-{idx}"
        rosetta_cards += f"""  <article class="rosetta-card" data-filter-item data-cat="{esc(item['cat'])}">
    <div class="prediction-header">
      <h3>{esc(item["title"])}</h3>
      <button type="button" class="btn btn-sm" data-copy-target="{lean_id}">Copy Lean pattern</button>
    </div>
    <p>{esc(item["note"])}</p>
    <div class="rosetta-pair">
      <div>
        <span class="infoview-section-label">TLA+ / PlusCal Idiom</span>
        <pre><code>{esc(item["tla"])}</code></pre>
      </div>
      <div>
        <span class="infoview-section-label">Lean 4.36.0 Idiom</span>
        <pre><code id="{lean_id}">{esc(item["lean"])}</code></pre>
      </div>
    </div>
  </article>\n"""

    tla_page = f"""{render_head("TLA+ to Lean 4 Rosetta Stone", "../", "reference/tla-to-lean")}
<body>
{render_header("../", "tla")}
<main class="container-wide">
  <span class="eyebrow">Systems Specification Reference</span>
  <h1>TLA+ ↔ Lean 4 Rosetta Stone</h1>
  <p class="hero-subtitle">
    Already think in Lamport's state machines, invariants, TLC model checking, and refinement mappings? Filter every TLA+ construct alongside its idiomatic zero-dependency Lean 4 counterpart.
  </p>

  <div class="filter-bar">
    <input type="search" class="search-input" data-filter-input placeholder="Search TLA+ or Lean constructs (e.g., UNCHANGED, stuttering, Init, BFS)...">
    <button type="button" class="btn btn-sm btn-primary" data-filter-cat="all">All</button>
    <button type="button" class="btn btn-sm" data-filter-cat="state">State &amp; Init</button>
    <button type="button" class="btn btn-sm" data-filter-cat="transitions">Next &amp; UNCHANGED</button>
    <button type="button" class="btn btn-sm" data-filter-cat="checking">Gear 1 BFS</button>
    <button type="button" class="btn btn-sm" data-filter-cat="invariants">Gear 2 Invariants</button>
    <button type="button" class="btn btn-sm" data-filter-cat="refinement">Refinement</button>
    <button type="button" class="btn btn-sm" data-filter-cat="progress">Termination</button>
  </div>
  <p class="step-counter" data-filter-count></p>

{rosetta_cards}
</main>
{render_shortcut_modal_and_footer("../", ["assets/reference.js"])}"""
    (ref_dir / "tla-to-lean.html").write_text(tla_page, encoding="utf-8")

    # 2. AI Playbook & Polyglot Oracle Integration
    prompt_spec = (
        "You are assisting with a Lean 4.36.0 Spec-First module (zero external dependencies, Core/Std only).\n"
        "1. Do NOT write implementation optimizations yet.\n"
        "2. Propose `Spec.lean` containing algebraic domain types (no boolean soup), a tiny total reference function,\n"
        "   BOTH a Soundness theorem and a Completeness theorem (blocking trivial always-none implementations),\n"
        "   and an explicit Non-Vacuity witness `theorem pre_satisfiable : ∃ x, Pre x`.\n"
        "3. List 3 concrete `#guard` sanity examples we should review together before locking `Spec.lean`."
    )
    prompt_prover = (
        "`Spec.lean` is SHA-256 locked—do NOT modify any declaration or theorem signature in `Spec.lean`.\n"
        "Edit ONLY `Impl.lean` to implement the optimized algorithm and prove all required theorems.\n"
        "Hard CI constraints enforced by `lake exe verigate`:\n"
        "- Zero `sorry`, zero custom `axiom` or `opaque`, zero `unsafe` or `partial`.\n"
        "- Zero `@[implemented_by]`, `@[extern]`, `@[csimp]`, or raw `native_decide`.\n"
        "- Prefer `fun_cases`, surgical `simp only [...]`, `omega`, `grind`, and `bv_decide` (when Tier 1 is enabled)."
    )
    prompt_triage = (
        "My Lean 4.36.0 proof is stuck at this exact Infoview state:\n"
        "[PASTE OBJECTS / HYPOTHESES / ⊢ GOAL HERE]\n\n"
        "Before suggesting ANY tactics, run the 3-Way Triage:\n"
        "(A) Is the leaf goal actually FALSE for concrete small values? If so, give a `#guard` counterexample.\n"
        "(B) Did the theorem statement omit a real domain precondition?\n"
        "(C) Is this a true property failing on an unreachable Garden-of-Eden state that needs inductive strengthening?"
    )
    ci_yaml = (
        "name: VeriGate & Differential Oracle CI\n"
        "on: [push, pull_request]\n"
        "jobs:\n"
        "  verify:\n"
        "    runs-on: ubuntu-latest\n"
        "    steps:\n"
        "      - uses: actions/checkout@v4\n"
        "      - uses: leanprover/lean-action@v1\n"
        "      - name: Enforce VeriGate TCB Audit\n"
        "        run: lake exe verigate --strict-kernel\n"
        "      - name: Differential-Fuzz Service Against Verified Lean Oracle\n"
        "        run: python3 scripts/fuzz_against_oracle.py"
    )
    polyglot_py = (
        "# Differential fuzzing any Rust / Go / TypeScript / Python binary against `lake exe oracle`\n"
        "import json, subprocess\n\n"
        "def query_jsonl(cmd: list[str], trace: list[dict]) -> dict:\n"
        "    proc = subprocess.run(cmd, input=json.dumps({'trace': trace}) + '\\n',\n"
        "                          text=True, capture_output=True, check=True)\n"
        "    return json.loads(proc.stdout)\n\n"
        "lean_truth = query_jsonl(['lake', 'exe', 'oracle', '--jsonl'], adversarial_trace)\n"
        "prod_actual = query_jsonl(['./target/release/my-rust-service', '--jsonl'], adversarial_trace)\n"
        "assert prod_actual == lean_truth, f'Divergence vs verified Lean spec: {prod_actual} != {lean_truth}'"
    )

    ai_page = f"""{render_head("AI Vericoding Playbook & Polyglot Oracle Guide", "../", "reference/ai-playbook")}
<body>
{render_header("../", "ai")}
<main class="container-wide">
  <span class="eyebrow">Chapters 13, 14 &amp; 16 Field Guide</span>
  <h1>AI Vericoding Playbook &amp; Polyglot <code>oracle</code> Guide</h1>
  <p class="hero-subtitle">
    Copy-paste prompts for supervising untrusted coding agents, CI configuration for <code>lake exe verigate</code>, and differential-fuzzing harnesses connecting Lean 4 to Rust, Go, TypeScript, and Python services.
  </p>

  <section class="lab-card">
    <div class="prediction-header">
      <h2>1. Copyable Spec-First Agent Prompts</h2>
      <span class="badge badge-accent">Human Owns Spec · Agent Owns Impl</span>
    </div>

    <h3>Prompt A — Co-Designing <code>Spec.lean</code> (Before Any Implementation)</h3>
    <pre><code id="prompt-spec">{esc(prompt_spec)}</code></pre>
    <button type="button" class="btn btn-sm" data-copy-target="prompt-spec">Copy Spec Architect Prompt</button>

    <h3>Prompt B — Locked-Spec Implementation &amp; Proof Synthesis</h3>
    <pre><code id="prompt-prover">{esc(prompt_prover)}</code></pre>
    <button type="button" class="btn btn-sm" data-copy-target="prompt-prover">Copy Locked-Spec Prover Prompt</button>

    <h3>Prompt C — Stuck Infoview 3-Way Triage</h3>
    <pre><code id="prompt-triage">{esc(prompt_triage)}</code></pre>
    <button type="button" class="btn btn-sm" data-copy-target="prompt-triage">Copy Stuck-Goal Triage Prompt</button>
  </section>

  <section class="lab-card">
    <h2>2. Two-Tier Axiom Policy &amp; <code>VeriGate</code> GitHub Actions Setup</h2>
    <div class="table-wrap">
      <table>
        <thead>
          <tr>
            <th>Mechanism / Declaration</th>
            <th>Tier 0 (<code>--strict-kernel</code>)</th>
            <th>Tier 1 (<code>--trust-tier=bv-lrat</code>)</th>
            <th>Security Rationale</th>
          </tr>
        </thead>
        <tbody>
          <tr>
            <td><code>propext</code>, <code>Quot.sound</code>, <code>Classical.choice</code></td>
            <td><span class="badge badge-verified">Allowed</span></td>
            <td><span class="badge badge-verified">Allowed</span></td>
            <td>Standard mathematical foundation of Lean 4's small kernel.</td>
          </tr>
          <tr>
            <td><code>bv_decide</code> (LRAT hardware bit-blasting)</td>
            <td><span class="badge badge-refuted">Rejected</span></td>
            <td><span class="badge badge-verified">Allowed (audited)</span></td>
            <td>Permits verified LRAT bit-vector certificates when zero raw <code>native_decide</code> exists.</td>
          </tr>
          <tr>
            <td>Raw <code>native_decide</code></td>
            <td><span class="badge badge-refuted">Rejected</span></td>
            <td><span class="badge badge-refuted">Rejected</span></td>
            <td>Pulls unverified native code generation into the proof TCB.</td>
          </tr>
          <tr>
            <td><code>sorryAx</code>, custom <code>axiom</code> / <code>opaque</code></td>
            <td><span class="badge badge-refuted">Rejected</span></td>
            <td><span class="badge badge-refuted">Rejected</span></td>
            <td>Prevents unfinished holes and arbitrary unproven assumptions.</td>
          </tr>
          <tr>
            <td><code>@[implemented_by]</code>, <code>@[extern]</code>, <code>@[csimp]</code></td>
            <td><span class="badge badge-refuted">Rejected</span></td>
            <td><span class="badge badge-refuted">Rejected</span></td>
            <td>Blocks silent swaps between verified kernel models and unverified runtime binaries.</td>
          </tr>
        </tbody>
      </table>
    </div>
    <h3>Minimal GitHub Actions Workflow</h3>
    <pre><code id="ci-yaml">{esc(ci_yaml)}</code></pre>
    <button type="button" class="btn btn-sm" data-copy-target="ci-yaml">Copy GitHub Actions YAML</button>
  </section>

  <section class="lab-card">
    <h2>3. Polyglot Differential Fuzzing with <code>lake exe oracle</code></h2>
    <p>
      Your production service can stay 100% Rust, Go, TypeScript, Python, or C++. Expose a thin CLI or test endpoint accepting JSONL action traces, and compare every state transition output against <code>lake exe oracle</code>:
    </p>
    <pre><code id="polyglot-py">{esc(polyglot_py)}</code></pre>
    <div class="action-group">
      <button type="button" class="btn btn-sm" data-copy-target="polyglot-py">Copy Differential Harness Template</button>
      <button type="button" class="btn btn-sm" data-copy-text="python3 scripts/fuzz_against_oracle.py">Copy local fuzzer command</button>
    </div>
    <div class="grid-2">
      <div class="callout">
        <strong>Rust &amp; Go Services:</strong>
        <p>Feed <code>proptest</code> / <code>go test -fuzz</code> byte seeds into both your struct state machine and a long-lived <code>lake exe oracle --stdio</code> child process over newline-delimited JSON.</p>
      </div>
      <div class="callout">
        <strong>TypeScript &amp; Python Services:</strong>
        <p>Generate 1,000 golden edge-case JSON vectors from your verified Lean spec (<code>lake exe oracle --dump-vectors &gt; vectors.json</code>) and assert 100% parity in Vitest / Pytest in under 200ms.</p>
      </div>
    </div>
  </section>
</main>
{render_shortcut_modal_and_footer("../", ["assets/reference.js"])}"""
    (ref_dir / "ai-playbook.html").write_text(ai_page, encoding="utf-8")

    # 3. Filterable Earned-Jargon Glossary
    glossary_cards = ""
    for part_label, term, plain_def, lean_mech, href in GLOSSARY_ITEMS:
        cat_slug = part_label.lower().replace(" ", "-")
        glossary_cards += f"""    <article class="card card-elevated" data-filter-item data-cat="{esc(cat_slug)}">
      <div class="prediction-header">
        <span class="badge badge-accent">{esc(part_label)}</span>
        <a href="../{esc(href)}">Earned in unit →</a>
      </div>
      <h3>{esc(term)}</h3>
      <p><strong>Plain-English Meaning:</strong> {esc(plain_def)}</p>
      <p><strong>Lean 4 Mechanism:</strong> <code>{esc(lean_mech)}</code></p>
    </article>\n"""

    glossary_page = f"""{render_head("Earned-Jargon Glossary", "../", "reference/glossary")}
<body>
{render_header("../", "glossary")}
<main class="container-wide">
  <span class="eyebrow">Plain-English First, Jargon Second</span>
  <h1>Earned-Jargon Glossary</h1>
  <p class="hero-subtitle">
    Every formal term in <em>Prove It</em> is earned by solving a concrete engineering problem first. Filter by course part or search any Lean, TLA+, or verification concept below.
  </p>

  <div class="filter-bar">
    <input type="search" class="search-input" data-filter-input placeholder="Filter terms (e.g., Subtype, Garden-of-Eden, LRAT, stuttering, TCB)...">
    <button type="button" class="btn btn-sm btn-primary" data-filter-cat="all">All Parts</button>
    <button type="button" class="btn btn-sm" data-filter-cat="part-i">Part I</button>
    <button type="button" class="btn btn-sm" data-filter-cat="part-ii">Part II</button>
    <button type="button" class="btn btn-sm" data-filter-cat="part-iii">Part III</button>
    <button type="button" class="btn btn-sm" data-filter-cat="part-iv">Part IV</button>
  </div>
  <p class="step-counter" data-filter-count></p>

  <div class="glossary-grid">
{glossary_cards}  </div>
</main>
{render_shortcut_modal_and_footer("../", ["assets/reference.js"])}"""
    (ref_dir / "glossary.html").write_text(glossary_page, encoding="utf-8")


def build_not_found_and_sitemap() -> None:
    def make_404(prefix: str) -> str:
        return f"""{render_head("Page not found", prefix, "__none__", "Page not found.", '  <meta name="robots" content="noindex">\\n')}
<body>
{render_header(prefix, "")}
<main class="container-wide">
  <section class="hero">
    <span class="eyebrow">404 · Uninhabited Type</span>
    <h1 class="hero-title">Page not found.</h1>
    <p class="hero-subtitle">
      There is no inhabitant at this URL path. Return to the course syllabus or jump into the live browser labs.
    </p>
    <div class="hero-cta-row">
      <a class="btn btn-primary" href="{prefix}index.html">Go to Prove It home →</a>
      <a class="btn" href="{prefix}labs/index.html">Open 6 Live Labs</a>
      <a class="btn" href="https://indicogni.com/">All Indicogni courses</a>
    </div>
  </section>
</main>
{render_shortcut_modal_and_footer(prefix)}"""

    (SITE_DIR / "404.html").write_text(make_404(""), encoding="utf-8")

    urls = [
        f"{CANONICAL_BASE}/",
        f"{CANONICAL_BASE}/labs/",
        f"{CANONICAL_BASE}/capstones/",
        f"{CANONICAL_BASE}/reference/tla-to-lean",
        f"{CANONICAL_BASE}/reference/ai-playbook",
        f"{CANONICAL_BASE}/reference/glossary",
    ]
    for u in UNITS:
        urls.append(f"{CANONICAL_BASE}/chapters/{u['id']}")

    xml_entries = "\n".join(f"  <url><loc>{esc(loc)}</loc></url>" for loc in urls)
    sitemap_xml = (
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
        f"{xml_entries}\n"
        "</urlset>\n"
    )
    (SITE_DIR / "sitemap.xml").write_text(sitemap_xml, encoding="utf-8")

    # Build Cloudflare Worker static-assets bundle in dist/ mirroring /learn/prove-it/
    if DIST_DIR.exists():
        shutil.rmtree(DIST_DIR)
    mounted_dir = DIST_DIR / MOUNT_PATH.lstrip("/")
    mounted_dir.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(SITE_DIR, mounted_dir)

    # Worker 404 page can be served at arbitrary nested paths, so anchor its asset/nav links to /learn/prove-it/
    worker_404 = make_404(f"{MOUNT_PATH}/")
    (mounted_dir / "404.html").write_text(worker_404, encoding="utf-8")
    (DIST_DIR / "404.html").write_text(worker_404, encoding="utf-8")

    headers_txt = (
        "/*\n"
        "  Strict-Transport-Security: max-age=31536000\n"
        "  Content-Security-Policy: default-src 'self'; script-src 'self'; style-src 'self'; "
        "img-src 'self' data:; connect-src 'none'; object-src 'none'; base-uri 'self'; "
        "form-action 'none'; frame-ancestors 'none'\n"
        "  X-Content-Type-Options: nosniff\n"
        "  X-Frame-Options: DENY\n"
        "  Referrer-Policy: strict-origin-when-cross-origin\n"
        "  Permissions-Policy: camera=(), microphone=(), geolocation=(), browsing-topics=()\n"
    )
    (DIST_DIR / "_headers").write_text(headers_txt, encoding="utf-8")


def main() -> None:
    (SITE_DIR / "assets").mkdir(parents=True, exist_ok=True)
    build_chapter_data_js()
    build_landing_page()
    build_chapter_pages()
    build_labs_page()
    build_capstones_page()
    build_reference_pages()
    build_not_found_and_sitemap()
    print(f"Generated static course in {SITE_DIR} and Worker bundle in {DIST_DIR}{MOUNT_PATH}/ ({len(UNITS)} interactive units + labs + capstones + reference + sitemap).")


if __name__ == "__main__":
    main()
