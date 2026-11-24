set_option autoImplicit false

/-!
# Chapter 8: Gear 2 — Inductive Invariants & Strengthening (Reference Solutions)

In Chapter 4 (Gear 1), bounded breadth-first search verified a finite slice of a
protocol's state space. What about protocols that run for millions of epochs,
drop packets, and hand off leadership indefinitely?

Welcome to **Gear 2**: TLA+-style state machines (`Init`, `Next`, `Reachable`)
and **inductive invariants** that verify safety across *every* execution trace of
arbitrary, unbounded length.
-/

namespace Ch08

/-!
## 1. TLA+ in Lean 4: `ClusterState`, `Init`, `Next`, and `Reachable`

A coordinator elects at most one active leader at a time over an asynchronous
network where grant messages travel on the wire (`inFlightGrants`) and may also
be lost (`dropGrant`):
-/

structure ClusterState where
  coordinatorHasAuthority : Bool
  inFlightGrants          : Nat
  activeLeaders           : Nat
  deriving Repr, DecidableEq

def Init (s : ClusterState) : Prop :=
  s = { coordinatorHasAuthority := true
        inFlightGrants          := 0
        activeLeaders           := 0 }

inductive Next : ClusterState → ClusterState → Prop where
  | dispatchGrant (s : ClusterState)
      (hAuth : s.coordinatorHasAuthority = true) :
      Next s { s with coordinatorHasAuthority := false
                      inFlightGrants := s.inFlightGrants + 1 }
  | deliverGrant (s : ClusterState)
      (hFlight : 0 < s.inFlightGrants) :
      Next s { s with inFlightGrants := s.inFlightGrants - 1
                      activeLeaders  := s.activeLeaders + 1 }
  | relinquish (s : ClusterState)
      (hLeader : 0 < s.activeLeaders) :
      Next s { s with coordinatorHasAuthority := true
                      activeLeaders := s.activeLeaders - 1 }
  | dropGrant (s : ClusterState)
      (hFlight : 0 < s.inFlightGrants) :
      Next s { s with inFlightGrants := s.inFlightGrants - 1 }

/--
`Reachable s` holds if `s` can be reached from `Init` in `0, 1, 2, ...` (unboundedly
many) `Next` transitions.
-/
inductive Reachable : ClusterState → Prop where
  | init {s : ClusterState} (hInit : Init s) : Reachable s
  | step {s s' : ClusterState} (hReach : Reachable s) (hNext : Next s s') : Reachable s'

/--
Target safety property: never more than one active leader in the cluster.
-/
abbrev SafeMutualExclusion (s : ClusterState) : Prop :=
  s.activeLeaders ≤ 1

/-!
## 2. Why Naive Induction Fails: "Garden-of-Eden" Wire States

Suppose you try to prove `Reachable s → SafeMutualExclusion s` directly by
induction on `Reachable`:
- Base case (`Init`): `0 ≤ 1` holds.
- Inductive step: assume `SafeMutualExclusion s` (`s.activeLeaders ≤ 1`) and
  `Next s s'`, and try to prove `s'.activeLeaders ≤ 1`.

On `Next.deliverGrant`, your Infoview stalls at:
  `ih      : s.activeLeaders ≤ 1`
  `hFlight : 0 < s.inFlightGrants`
  `⊢ s.activeLeaders + 1 ≤ 1`

Look at `edenWireState` below: one leader is ALREADY active (`activeLeaders = 1`),
AND a duplicate grant is simultaneously sitting on the network wire
(`inFlightGrants = 1`). `edenWireState` satisfies `SafeMutualExclusion`, yet one
`deliverGrant` step transitions it into a split-brain state (`activeLeaders = 2`)!

Such a state is called a **Garden-of-Eden state**: it satisfies the weak safety
predicate, steps into a bad state, and is *unreachable* from `Init`.
-/

def edenWireState : ClusterState :=
  { coordinatorHasAuthority := false
    inFlightGrants          := 1
    activeLeaders           := 1 }

#guard edenWireState.activeLeaders ≤ 1

/-!
## 3. Invariant Strengthening: Accounting for the Authority Token

To exclude Garden-of-Eden wire states, our invariant must bound `inFlightGrants + activeLeaders ≤ 1`—and
to make `dispatchGrant` inductive as well, it must account for all three places
the single authority token can live:
1. At the coordinator (`if s.coordinatorHasAuthority then 1 else 0`),
2. In flight on the network (`s.inFlightGrants`), or
3. Held by an elected leader (`s.activeLeaders`).
-/

@[grind =]
def authorityCount (s : ClusterState) : Nat :=
  (if s.coordinatorHasAuthority then 1 else 0) + s.inFlightGrants + s.activeLeaders

abbrev TokenInvariant (s : ClusterState) : Prop :=
  authorityCount s ≤ 1

abbrev WireAndLeaderBound (s : ClusterState) : Prop :=
  s.inFlightGrants + s.activeLeaders ≤ 1

-- `edenWireState` violates both `WireAndLeaderBound` and `TokenInvariant`!
#guard !(edenWireState.inFlightGrants + edenWireState.activeLeaders ≤ 1)
#guard !(authorityCount edenWireState ≤ 1)

theorem tokenInvariant_init {s : ClusterState} (hInit : Init s) :
    TokenInvariant s := by
  rw [hInit]
  decide

/-!
## Exercises (Solved)
-/

/--
Exercise 8.1: Prove that `edenWireState` satisfies `SafeMutualExclusion`, yet
takes a valid `Next.deliverGrant` step to a state `sBad` violating `SafeMutualExclusion`.
(This proves `SafeMutualExclusion` is NOT inductive on its own.)
-/
theorem eden_breaks_naive_induction :
    SafeMutualExclusion edenWireState ∧
    ∃ sBad : ClusterState, Next edenWireState sBad ∧ ¬ SafeMutualExclusion sBad := by
  constructor
  · decide
  · refine ⟨_, Next.deliverGrant edenWireState (by decide), ?_⟩
    decide

/--
Exercise 8.2a: Prove that `TokenInvariant` implies both `WireAndLeaderBound`
(`inFlightGrants + activeLeaders ≤ 1`) and `SafeMutualExclusion` (`activeLeaders ≤ 1`).
-/
theorem tokenInvariant_implies_safety (s : ClusterState)
    (hInv : TokenInvariant s) :
    WireAndLeaderBound s ∧ SafeMutualExclusion s := by
  dsimp [TokenInvariant, authorityCount, WireAndLeaderBound, SafeMutualExclusion] at *
  split at hInv <;> omega

/--
Exercise 8.2b (Inductive Step):
Prove that *every* transition of `Next` (`dispatchGrant`, `deliverGrant`,
`relinquish`, `dropGrant`) preserves `TokenInvariant`.
-/
theorem tokenInvariant_next {s s' : ClusterState}
    (hInv : TokenInvariant s) (hNext : Next s s') :
    TokenInvariant s' := by
  cases hNext with
  | dispatchGrant hAuth =>
    dsimp [TokenInvariant, authorityCount] at *
    rw [hAuth] at hInv
    dsimp at hInv
    omega
  | deliverGrant hFlight =>
    dsimp [TokenInvariant, authorityCount] at *
    cases hAuth : s.coordinatorHasAuthority <;> simp only [hAuth] at * <;> omega
  | relinquish hLeader =>
    dsimp [TokenInvariant, authorityCount] at *
    cases hAuth : s.coordinatorHasAuthority <;> simp only [hAuth] at * <;> omega
  | dropGrant hFlight =>
    dsimp [TokenInvariant, authorityCount] at *
    cases hAuth : s.coordinatorHasAuthority <;> simp only [hAuth] at * <;> omega

/--
Exercise 8.3a: Prove by induction on `hReach` that every reachable state in an
execution of arbitrary length satisfies `TokenInvariant`.
-/
theorem reachable_tokenInvariant {s : ClusterState}
    (hReach : Reachable s) :
    TokenInvariant s := by
  induction hReach with
  | init hInit => exact tokenInvariant_init hInit
  | step _ hNext ih => exact tokenInvariant_next ih hNext

/--
Exercise 8.3b (Unbounded Cluster Mutual Exclusion):
Conclude that *every* reachable state—across unboundedly many grants, handoffs,
and dropped packets—has at most one active leader (`activeLeaders ≤ 1`).
-/
theorem reachable_mutual_exclusion {s : ClusterState}
    (hReach : Reachable s) :
    SafeMutualExclusion s :=
  (tokenInvariant_implies_safety s (reachable_tokenInvariant hReach)).right

/-- info: 'Ch08.reachable_mutual_exclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reachable_mutual_exclusion

end Ch08
