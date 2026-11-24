# `FencingKV` — Proof Engineering & Design Decisions

## 1. Why Pair Gear 1 (Bounded BFS) with Gear 2 (Inductive Invariants)?

When verifying distributed protocols, jumping straight into unbounded proofs on a subtly broken transition system wastes hours trying to prove a false theorem. By implementing an executable state explorer (`bfsSearch`) inside the same Lean file:
1. We validate our state model and safety predicate (`NoSplitBrainOverwrite`) by watching it **catch** the unfenced split-brain bug in 4 steps (`gear1_split_brain_caught`).
2. Because `isValidSplitBrainWitness findSplitBrainCounterexample = true` is proved by `decide`, Lean's kernel executes the BFS search and verifies the counterexample trace with zero external model-checker dependencies.

## 2. Modeling Asynchronous Network Chaos Relationally

Rather than modeling a complex priority queue or discrete-event simulator for network delays, `Step` models an unstructured network bag `inFlight : List Packet` with explicit chaos transitions:
- `Step.duplicate` duplicates any existing packet arbitrarily many times.
- `Step.reorder` replaces `inFlight` with *any* list whose elements come from `s.inFlight` (`∀ p ∈ newBag, p ∈ s.inFlight`), subsuming arbitrary permutation, packet loss, and out-of-order delivery in a single two-line constructor!

This relational abstraction makes the `duplicate` and `reorder` cases of `step_preserves_fencingInv` five lines each while covering strictly *more* adversarial network schedules than any fixed queue implementation.

## 3. Generalizing Accumulator Induction in `compactAux`

`TombstoneKV.compact db` calls `compactAux [] db`, where `seen : List String` accumulates keys encountered in newer log positions. Attempting direct induction on `compactAux [] db` fails immediately because the recursive call changes the accumulator from `[]` to `k :: []`!

Generalizing `seen` (`induction db generalizing seen`) and splitting the specification of `compactAux` into two crisp regimes:
- **Masked regime (`k ∈ seen`)**: `get_compactAux_of_mem` guarantees older entries for `k` are completely erased (`none`).
- **Live regime (`k ∉ seen`)**: `get_compactAux_of_not_mem` guarantees `compactAux` preserves `TombstoneKV.get db k`.

Notice how cleanly the zombie-resurrection hazard appears in the proof: when `(k, .tombstone)` is encountered in the live regime (`k ∉ seen`), `compactAux` drops the tombstone physically from the output list *and* pushes `k` into `seen`, transitioning the tail `rest` into the masked regime (`get_compactAux_of_mem`) so any older `(k, .val old)` in `rest` cannot resurface!

## 4. Function Extensionality (`funext`) and Stuttering Refinement

Representing `SpecKV` as a pure mathematical function `String → Option String` means our abstract specification is 15 lines of self-evident code. Using `funext k`, concrete list transformations (`put`, `del`, `compact`) reduce directly to point-lookup equalities, demonstrating TLA+-style **stuttering refinement** (`absKV (compact db) = absKV db`) inside Lean's type theory.
