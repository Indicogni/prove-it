# Capstone 2: `FencingKV` — Distributed Lease Fencing & Crash-Safe Tombstone KV

## 1. Engineering Problem

Distributed storage systems face two subtle failure modes that survive unit tests:

1. **Stale-Leader Split-Brain (Kleppmann's Lease Trap)**: Process `L1` acquires a lease, hits a 30-second GC pause while its write packet is in flight, and loses its lease to `L2`. `L2` commits a newer configuration. Then `L1` wakes up—or the network delivers `L1`'s delayed packet—silently overwriting `L2`'s committed state if storage fails to enforce **monotonic fencing tokens**.
2. **LSM Zombie Value Resurrection**: Log-structured storage engines delete keys by appending `.tombstone` records and later run background compaction. If compaction strips a tombstone without simultaneously suppressing older shadowed records for the same key, deleted data comes back from the dead!

In `FencingKV`, you apply the **Two-Gear Verification Workflow**:
- **Gear 1 (Bounded Bug-Finding)**: Run an executable BFS state-space explorer in Lean to automatically catch the 4-step split-brain trace on unfenced storage.
- **Gear 2 (Unbounded Mechanized Proof)**: Prove an inductive invariant across unbounded epochs and arbitrary packet duplication/reordering, plus a stuttering refinement mapping against a 15-line abstract `SpecKV`.

---

## 2. Architecture Overview

| Component | Role |
| :--- | :--- |
| `SpecKV` | 15-line pure functional specification (`String → Option String`) |
| `TombstoneKV` | Append-only log (`List (String × Entry)`) with tombstone deletes and single-pass `compact` |
| `findSplitBrainCounterexample` | Gear 1 fuel-bounded BFS catching stale overwrite on unfenced storage |
| `Step` & `FencingInv` | Gear 2A unbounded network/storage transition relation & strengthened invariant |
| `absKV` & `compact_stutters` | Gear 2B refinement mapping & stuttering equivalence proof |

---

## 3. Socratic Verification Roadmap

### Milestone 1 — Gear 1: Catching Split-Brain (`gear1_split_brain_caught`)
*Question*: Why start with bounded BFS before attempting an unbounded inductive invariant?
- Inspect `stepBuggy`: storage applies `pkt` without checking `s.storageFence ≤ pkt.token`.
- Discharge `gear1_split_brain_caught` with `decide` and inspect the 4-step trace discovered by `findSplitBrainCounterexample`.

### Milestone 2 — Gear 2A: Unbounded Fencing Safety (`step_preserves_fencingInv`, `reachable_no_split_brain`)
*Question*: Why isn't `s.committedEpoch = s.highWaterEpoch` inductive on its own?
- If `s.storageFence` were `10` while `s.highWaterEpoch` were `20`, accepting a packet with token `15` (`10 ≤ 15`) would regress `committedEpoch` from `20` to `15`!
- Notice how `FencingInv` ties **both** `committedEpoch` and `highWaterEpoch` directly to `storageFence`, and bounds every in-flight packet's token by `latestIssued`.
- Case-split on `hStep` (`issue`, `duplicate`, `reorder`, `deliver`, `compact`) and use `omega` on the arithmetic obligations.

### Milestone 3 — Gear 2B: Tombstone Refinement (`absKV_put`, `absKV_del`, `compact_stutters`)
*Question*: Why must `compactAux` record `k` in `seen` **even when dropping `(k, .tombstone)`**?
- Use `funext k'` for `absKV_put` and `absKV_del`.
- For `compact_stutters`, prove two generalized helpers over `(seen : List String)` by induction on `db generalizing seen`:
  1. `get_compactAux_of_mem`: if `k ∈ seen`, `TombstoneKV.get (compactAux seen db) k = none`.
  2. `get_compactAux_of_not_mem`: if `k ∉ seen`, `TombstoneKV.get (compactAux seen db) k = TombstoneKV.get db k`.
- Notice how `get_compactAux_of_not_mem` invokes `get_compactAux_of_mem` at the exact moment a `.tombstone` is purged!

### Milestone 4 — Non-Vacuity (`non_vacuous_fenced_lifecycle`)
Prove via `decide` that writing `"v1"` at token `1`, deleting `"k"` at token `2`, and running `compact` leaves `[]` with `NoSplitBrainOverwrite = true`.

---

## 4. Verification Commands

```bash
lake exe check fencing-kv
lake exe verigate ProveIt/Capstones/FencingKV.lean
lake exe oracle kv "put 1 cfg v1; put 2 cfg v2; put 1 cfg stale; get cfg"
```
