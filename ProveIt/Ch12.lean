/-
  Chapter 12: Refinement Mappings & Stuttering Steps
  ==================================================

  How do engineers verify a 1,000-line storage engine with write-ahead logs,
  read caches, and background log compaction without drowning in ad-hoc lemmas?

  The answer—pioneered by Hoare, Lamport (TLA+), IronFleet, and AWS—is a
  **refinement mapping** (`abs : Impl → Spec`):
  1. Write a tiny, obviously-correct 15-line abstract state machine `SpecKV`.
  2. Build the fast concrete implementation `ImplKV` (newest-first WAL + hot cache).
  3. Prove that every concrete operation commutes with `abs` (simulation) while
     preserving internal representation invariants (`CacheConsistent`).
  4. Prove that internal maintenance—like **background log compaction**—is a
     **stuttering step**: it rewrites concrete memory while leaving `abs s`
     completely unchanged (`abs (compact s) = abs s`)!
-/
set_option autoImplicit false

namespace ProveIt.Ch12

/-! ## 1. The 15-Line Reference Specification (`SpecKV`) -/

/-- Abstract key-value store: a pure mathematical mapping from keys to optional values. -/
structure SpecKV where
  lookup : String → Option String

theorem SpecKV.ext {s₁ s₂ : SpecKV} (h : ∀ k, s₁.lookup k = s₂.lookup k) : s₁ = s₂ := by
  cases s₁; cases s₂; simp only [mk.injEq]; exact funext h

@[simp] def SpecKV.empty : SpecKV := ⟨fun _ => none⟩
@[simp] def SpecKV.get (s : SpecKV) (k : String) : Option String := s.lookup k
@[simp] def SpecKV.put (s : SpecKV) (k : String) (v : String) : SpecKV :=
  ⟨fun q => if q == k then some v else s.lookup q⟩
@[simp] def SpecKV.delete (s : SpecKV) (k : String) : SpecKV :=
  ⟨fun q => if q == k then none else s.lookup q⟩

/-! ## 2. The Concrete Engine (`ImplKV`: Append-Log + Tombstones + Cache) -/

/--
  Design for Verifiability (RocksDB / LSM-tree style):
  Representing a write-ahead log entry with `value : Option String` (`some v` for put,
  `none` for a deletion tombstone) models real storage engines AND halves proof cases!
-/
structure LogEntry where
  key   : String
  value : Option String
  deriving Repr, DecidableEq

/-- Concrete KV engine: newest-first write log + bounded/hot read cache. -/
structure ImplKV where
  log   : List LogEntry
  cache : List LogEntry
  deriving Repr, DecidableEq

/-- Replay a newest-first log to find the latest entry (if any) for `k`. -/
@[simp]
def replayLog : List LogEntry → String → Option String
  | [], _ => none
  | e :: rest, k => if k == e.key then e.value else replayLog rest k

/-- Search the hot cache; `none` means cache miss, `some e.value` means cache hit! -/
@[simp]
def lookupCache : List LogEntry → String → Option (Option String)
  | [], _ => none
  | e :: rest, k => if k == e.key then some e.value else lookupCache rest k

/-- The Refinement Mapping (`abs`): maps concrete state to abstract `SpecKV`. -/
@[simp]
def abs (s : ImplKV) : SpecKV :=
  ⟨replayLog s.log⟩

/-- Representation Invariant: every cached key agrees with the authoritative log. -/
def CacheConsistent (s : ImplKV) : Prop :=
  ∀ k res, lookupCache s.cache k = some res → replayLog s.log k = res

@[simp] def ImplKV.empty : ImplKV := { log := [], cache := [] }

/-- Fast-path read: consult `cache` first; only scan `log` on a cache miss! -/
def ImplKV.get (s : ImplKV) (k : String) : Option String :=
  match lookupCache s.cache k with
  | some cached => cached
  | none => replayLog s.log k

@[simp]
def ImplKV.put (s : ImplKV) (k : String) (v : String) : ImplKV :=
  let entry : LogEntry := { key := k, value := some v }
  { log := entry :: s.log, cache := entry :: s.cache }

@[simp]
def ImplKV.delete (s : ImplKV) (k : String) : ImplKV :=
  let tomb : LogEntry := { key := k, value := none }
  { log := tomb :: s.log, cache := tomb :: s.cache }

/-! ## 3. Worked Refinement Proofs: Empty & Fast-Path `get` -/

theorem abs_empty : abs ImplKV.empty = SpecKV.empty :=
  SpecKV.ext (fun _ => rfl)

theorem empty_consistent : CacheConsistent ImplKV.empty := by
  intro k res hHit
  nomatch hHit

/--
  Worked Example: Whenever `CacheConsistent s` holds, the cached fast-path
  `ImplKV.get` returns the exact same answer as the 15-line `SpecKV.get`!
-/
theorem get_refines (s : ImplKV) (hInv : CacheConsistent s) (k : String) :
    s.get k = (abs s).get k := by
  unfold ImplKV.get
  simp only [abs, SpecKV.get]
  split
  · rename_i cached hHit
    exact (hInv k cached hHit).symm
  · rfl

/-! ## 4. Background Compaction & Exercises -/

/--
  Deduplicate shadowed entries in a newest-first log:
  keep only the first (newest) entry for each key, dropping older shadowed writes.
-/
@[simp]
def compactLog (seen : List String) : List LogEntry → List LogEntry
  | [] => []
  | e :: rest =>
    if seen.contains e.key then
      compactLog seen rest
    else
      e :: compactLog (e.key :: seen) rest

/-- Background compaction deduplicates `log` and flushes `cache` cleanly. -/
@[simp]
def ImplKV.compact (s : ImplKV) : ImplKV :=
  { log := compactLog [] s.log, cache := [] }

#guard (
  let s0 := ImplKV.empty
  let s1 := ((s0.put "a" "1").put "b" "2").put "a" "3"
  let sc := s1.compact
  sc.log.length == 2 && sc.get "a" == some "3" && sc.get "b" == some "2"
)

/--
  EXERCISE 1: Prove the commuting diagram for `ImplKV.put`:
  `abs (s.put k v) = (abs s).put k v`.
-/
theorem put_refines (s : ImplKV) (k v : String) :
    abs (s.put k v) = (abs s).put k v := by
  sorry

/--
  EXERCISE 2: Prove the commuting diagram for `ImplKV.delete`:
  `abs (s.delete k) = (abs s).delete k`.
-/
theorem delete_refines (s : ImplKV) (k : String) :
    abs (s.delete k) = (abs s).delete k := by
  sorry

/--
  EXERCISE 3: Prove that `ImplKV.put` preserves the `CacheConsistent` invariant.
-/
theorem put_preserves_invariant (s : ImplKV) (hInv : CacheConsistent s) (k v : String) :
    CacheConsistent (s.put k v) := by
  sorry

/--
  EXERCISE 4: Prove that `compactLog` never increases log length (`≤`).
-/
theorem compactLog_length_le (seen : List String) (ops : List LogEntry) :
    (compactLog seen ops).length ≤ ops.length := by
  sorry

/--
  EXERCISE 5 (Key Lemma for Stuttering): Prove that for any key `k` NOT yet in `seen`
  (`seen.contains k = false`), replaying `compactLog seen ops` returns the exact
  same result for `k` as replaying `ops`!
-/
theorem replayLog_compactLog (seen : List String) (ops : List LogEntry) (k : String)
    (hFresh : seen.contains k = false) :
    replayLog (compactLog seen ops) k = replayLog ops k := by
  sorry

/--
  EXERCISE 6 (The Stuttering Theorem + Invariant Preservation):
  Prove that `ImplKV.compact` is an abstract **stuttering step** (`abs s.compact = abs s`)
  AND leaves the engine in a `CacheConsistent` state!
-/
theorem compact_stutters_and_consistent (s : ImplKV) :
    abs s.compact = abs s ∧ CacheConsistent s.compact := by
  sorry

end ProveIt.Ch12
