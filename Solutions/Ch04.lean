set_option autoImplicit false

/-!
# Chapter 4: Gear 1 — A TLA+ Model Checker in 35 Lines (Reference Solutions)

Before proving unbounded theorems over distributed protocols (Gear 2, Chapter 8),
practicing verification engineers reach for **Gear 1**: executable state-machine
modeling and bounded breadth-first state-space exploration.

Below is a complete, polymorphic bounded BFS model checker in 30 lines of Lean 4,
applied to the classic distributed lock split-brain bug.
-/

namespace Ch04

/-!
## Part 1: A Polymorphic Bounded Model Checker in 30 Lines
-/

structure Violation (State Action : Type) where
  badState : State
  trace    : List Action
  deriving Repr, DecidableEq

def expandState {State Action : Type}
    (step : State → Action → Option State) (actions : List Action)
    (s : State) (revTrace : List Action) : List (State × List Action) :=
  actions.filterMap fun act =>
    match step s act with
    | some s' => some (s', act :: revTrace)
    | none    => none

def bfsLoop {State Action : Type} [DecidableEq State]
    (step : State → Action → Option State)
    (actions : List Action) (safe : State → Bool) :
    Nat → List State → List (State × List Action) → Option (Violation State Action)
  | 0, _, _ => none
  | _, _, [] => none
  | fuel + 1, visited, (s, revTrace) :: rest =>
    if !safe s then
      some { badState := s, trace := revTrace.reverse }
    else if s ∈ visited then
      bfsLoop step actions safe fuel visited rest
    else
      let nexts := expandState step actions s revTrace
      bfsLoop step actions safe fuel (s :: visited) (rest ++ nexts)

def bfsViolation {State Action : Type} [DecidableEq State]
    (init : State) (step : State → Action → Option State)
    (actions : List Action) (safe : State → Bool) (fuel : Nat) :
    Option (Violation State Action) :=
  bfsLoop step actions safe fuel [] [(init, [])]

/-!
## Part 2: Modeling an Unfenced Distributed Lock Service

Two worker nodes (`nodeA`, `nodeB`) acquire time-bounded leases from a lock
server before writing to shared storage:
- During a stop-the-world GC pause, the lock server can expire the current lease
  (`expireLease`) while the paused worker still caches its old grant locally.
- If a second worker acquires a fresh lease and writes to storage, and the first
  worker then wakes up and writes without a **fencing token** check at storage,
  the stale worker silently clobbers newer data (`staleOverwrite = true`).
-/

inductive Node where
  | nodeA
  | nodeB
  deriving Repr, DecidableEq

inductive LockAction where
  | acquire (n : Node)
  | expireLease
  | write (n : Node)
  deriving Repr, DecidableEq

def allLockActions : List LockAction :=
  [.acquire .nodeA, .acquire .nodeB, .expireLease, .write .nodeA, .write .nodeB]

structure LockState where
  nextEpoch      : Nat
  serverOwner    : Option Node
  aCachedEpoch   : Option Nat
  bCachedEpoch   : Option Nat
  storageEpoch   : Nat
  staleOverwrite : Bool
  deriving Repr, DecidableEq

def initLockState : LockState :=
  { nextEpoch      := 1
    serverOwner    := none
    aCachedEpoch   := none
    bCachedEpoch   := none
    storageEpoch   := 0
    staleOverwrite := false }

def cachedEpochOf (s : LockState) (n : Node) : Option Nat :=
  match n with
  | .nodeA => s.aCachedEpoch
  | .nodeB => s.bCachedEpoch

/--
Unfenced transition relation (bounded to `nextEpoch ≤ 3` for finite-state checking):
Notice `write` checks that the worker *locally* holds some cached lease,
but storage never compares `tok` against `s.storageEpoch`!
-/
def unfencedStep (s : LockState) (act : LockAction) : Option LockState :=
  match act with
  | .acquire n =>
    if s.serverOwner == none && s.nextEpoch ≤ 2 then
      match n with
      | .nodeA =>
        some { s with serverOwner := some .nodeA
                      aCachedEpoch := some s.nextEpoch
                      nextEpoch := s.nextEpoch + 1 }
      | .nodeB =>
        some { s with serverOwner := some .nodeB
                      bCachedEpoch := some s.nextEpoch
                      nextEpoch := s.nextEpoch + 1 }
    else
      none
  | .expireLease =>
    if s.serverOwner != none then
      some { s with serverOwner := none }
    else
      none
  | .write n =>
    match cachedEpochOf s n with
    | none => none
    | some tok =>
      if tok < s.storageEpoch then
        some { s with staleOverwrite := true }
      else
        some { s with storageEpoch := tok }

def lockSafe (s : LockState) : Bool :=
  !s.staleOverwrite

-- Compile-time model checking! `bfsViolation` automatically discovers a 5-step
-- split-brain trace where `.nodeA` acquires epoch 1, pauses while its lease
-- expires, `.nodeB` acquires epoch 2 and writes, and `.nodeA` wakes up to clobber
-- storage!
#guard (bfsViolation initLockState unfencedStep allLockActions lockSafe 200).map (·.trace) ==
  some [.acquire .nodeA, .expireLease, .acquire .nodeB, .write .nodeB, .write .nodeA]

/-!
## Helper: Replaying a Trace
-/

def runTrace {State Action : Type}
    (step : State → Action → Option State) :
    State → List Action → Option State
  | s, []          => some s
  | s, act :: rest =>
    match step s act with
    | some s' => runTrace step s' rest
    | none    => none

/-!
## Exercises (Solved)
-/

/--
Exercise 4.1: Prove that replaying the 5-step counterexample trace discovered by
`bfsViolation` from `initLockState` reaches a state `sFinal` that violates `lockSafe`.
-/
def splitBrainTrace : List LockAction :=
  [.acquire .nodeA, .expireLease, .acquire .nodeB, .write .nodeB, .write .nodeA]

theorem splitBrainTrace_violates_safety :
    ∃ sFinal : LockState,
      runTrace unfencedStep initLockState splitBrainTrace = some sFinal ∧
      lockSafe sFinal = false := by
  refine ⟨_, rfl, ?_⟩
  rfl

/--
Exercise 4.2: Implement `fencedWrite` and `fencedStep` so shared storage enforces
monotonic fencing tokens:
- A write carrying cached token `tok` is accepted (`some ...`) ONLY when
  `s.storageEpoch ≤ tok`, updating `storageEpoch := tok`.
- Any stale write (`tok < s.storageEpoch`) is rejected (`none`) by storage!
-/
def fencedWrite (s : LockState) (n : Node) : Option LockState :=
  match cachedEpochOf s n with
  | none => none
  | some tok =>
    if s.storageEpoch ≤ tok then
      some { s with storageEpoch := tok }
    else
      none

def fencedStep (s : LockState) (act : LockAction) : Option LockState :=
  match act with
  | .acquire n   => unfencedStep s (.acquire n)
  | .expireLease => unfencedStep s .expireLease
  | .write n     => fencedWrite s n

-- Bounded BFS explores the entire fenced state space and finds `none` violations!
#guard bfsViolation initLockState fencedStep allLockActions lockSafe 500 == none

/--
Exercise 4.3a: Prove that `fencedWrite` never decreases `storageEpoch` for *any*
unbounded `LockState` (beyond `nextEpoch ≤ 2`).
-/
theorem fencedWrite_epoch_monotone (s s' : LockState) (n : Node)
    (h : fencedWrite s n = some s') :
    s.storageEpoch ≤ s'.storageEpoch := by
  unfold fencedWrite at h
  split at h
  · nomatch h
  · split at h
    · injection h with hEq
      rw [← hEq]
      omega
    · nomatch h

/--
Exercise 4.3b: Prove that `fencedWrite` preserves `lockSafe` across a single step.
-/
theorem fencedWrite_preserves_safe (s s' : LockState) (n : Node)
    (hSafe : lockSafe s = true)
    (hStep : fencedWrite s n = some s') :
    lockSafe s' = true := by
  unfold fencedWrite at hStep
  split at hStep
  · nomatch hStep
  · split at hStep
    · injection hStep with hEq
      rw [← hEq]
      exact hSafe
    · nomatch hStep

/-- info: 'Ch04.fencedWrite_epoch_monotone' does not depend on any axioms -/
#guard_msgs in
#print axioms fencedWrite_epoch_monotone

end Ch04
