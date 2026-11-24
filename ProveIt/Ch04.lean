set_option autoImplicit false

/-!
# Chapter 4: Gear 1 — A TLA+ Model Checker in 35 Lines

Two worker processes (`nodeA`, `nodeB`) coordinate writes to shared object
storage using time-bounded leases from a lock service:
1. `nodeA` acquires lease #1, then hits a 15-second stop-the-world GC pause.
2. The lock server expires `nodeA`'s lease and grants lease #2 to `nodeB`.
3. `nodeB` writes fresh data to storage.
4. `nodeA` wakes up from GC pause—still believing its cached lease is valid—and
   sends its delayed write to storage.

Before proving unbounded theorems over distributed systems (Gear 2, Chapter 8),
formal methods engineers start in **Gear 1**: write an executable state machine
(`init`, `step`, `safe`) and run a bounded breadth-first state-space explorer to
hunt for multi-step counterexample traces automatically.
-/

namespace Ch04

/-!
## Part 1: A Polymorphic Bounded BFS Model Checker in 30 Lines
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
## Part 2: The Unfenced Lock State Machine
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

-- PREDICT: How many steps long is the shortest split-brain trace from `initLockState`
-- to `staleOverwrite = true`? Trace the actions mentally before checking below!
#guard (bfsViolation initLockState unfencedStep allLockActions lockSafe 200).map (·.trace) ==
  some [.acquire .nodeA, .expireLease, .acquire .nodeB, .write .nodeB, .write .nodeA]

def runTrace {State Action : Type}
    (step : State → Action → Option State) :
    State → List Action → Option State
  | s, []          => some s
  | s, act :: rest =>
    match step s act with
    | some s' => runTrace step s' rest
    | none    => none

/-!
## Exercises
-/

def splitBrainTrace : List LockAction :=
  [.acquire .nodeA, .expireLease, .acquire .nodeB, .write .nodeB, .write .nodeA]

/--
Exercise 4.1: Prove that replaying `splitBrainTrace` on `unfencedStep` from
`initLockState` deterministically reaches a final state `sFinal` violating `lockSafe`.
-/
theorem splitBrainTrace_violates_safety :
    ∃ sFinal : LockState,
      runTrace unfencedStep initLockState splitBrainTrace = some sFinal ∧
      lockSafe sFinal = false := by
  sorry

/--
Exercise 4.2: Implement `fencedWrite` so shared storage checks monotonic fencing
tokens on every write:
- Look up the writer's cached token via `cachedEpochOf s n`.
- If `none`, return `none`.
- If `some tok` and `s.storageEpoch ≤ tok`, accept the write and update
  `storageEpoch := tok`.
- If `tok < s.storageEpoch`, reject the stale write (`none`)!
-/
def fencedWrite (s : LockState) (n : Node) : Option LockState :=
  sorry

def fencedStep (s : LockState) (act : LockAction) : Option LockState :=
  match act with
  | .acquire n   => unfencedStep s (.acquire n)
  | .expireLease => unfencedStep s .expireLease
  | .write n     => fencedWrite s n

-- Once `fencedWrite` is implemented, prove with `rfl` that bounded BFS explores
-- the entire fenced state space and finds `none` safety violations!
example : bfsViolation initLockState fencedStep allLockActions lockSafe 500 = none := by
  sorry

/--
Exercise 4.3a: Bounded BFS checked epochs up to `2`. Now prove a property over
*unbounded* `Nat` epochs: `fencedWrite` never decreases `storageEpoch`.
-/
theorem fencedWrite_epoch_monotone (s s' : LockState) (n : Node)
    (h : fencedWrite s n = some s') :
    s.storageEpoch ≤ s'.storageEpoch := by
  sorry

/--
Exercise 4.3b: Prove that `fencedWrite` preserves `lockSafe` across any single step.
-/
theorem fencedWrite_preserves_safe (s s' : LockState) (n : Node)
    (hSafe : lockSafe s = true)
    (hStep : fencedWrite s n = some s') :
    lockSafe s' = true := by
  sorry

end Ch04
