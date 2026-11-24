set_option autoImplicit false

/-!
# Chapter 8: Gear 2 — Inductive Invariants & Strengthening

In Chapter 4 (Gear 1), bounded breadth-first search checked a finite slice of a
protocol's state space. What happens when a distributed cluster hands off
leadership millions of times over asynchronous networks that can also drop
messages?

Welcome to **Gear 2**: TLA+-style transition systems (`Init`, `Next`, `Reachable`)
and **inductive invariants** that verify safety across *every* execution trace of
unbounded length.
-/

namespace Ch08

/-!
## 1. TLA+ in Lean 4: `ClusterState`, `Init`, `Next`, and `Reachable`
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

inductive Reachable : ClusterState → Prop where
  | init {s : ClusterState} (hInit : Init s) : Reachable s
  | step {s s' : ClusterState} (hReach : Reachable s) (hNext : Next s s') : Reachable s'

abbrev SafeMutualExclusion (s : ClusterState) : Prop :=
  s.activeLeaders ≤ 1

/-!
## 2. Why Naive Induction Stalls: "Garden-of-Eden" Wire States

Suppose you attempt induction directly on `Reachable` using `SafeMutualExclusion`:
on `Next.deliverGrant`, your Infoview stalls with:
  `ih      : s.activeLeaders ≤ 1`
  `hFlight : 0 < s.inFlightGrants`
  `⊢ s.activeLeaders + 1 ≤ 1`

Inspect `edenWireState` below: one node is already acting as leader
(`activeLeaders = 1`) while a second grant sits on the network wire
(`inFlightGrants = 1`). Such an unreachable state that satisfies the weak safety
property yet steps into a violation is called a **Garden-of-Eden state**.
-/

def edenWireState : ClusterState :=
  { coordinatorHasAuthority := false
    inFlightGrants          := 1
    activeLeaders           := 1 }

-- PREDICT: Does `edenWireState` satisfy `SafeMutualExclusion`? What is
-- `activeLeaders` after one `deliverGrant` step from `edenWireState`?
#guard edenWireState.activeLeaders ≤ 1

/-!
## 3. Strengthening the Invariant: Conservation of Authority

To rule out Garden-of-Eden wire states (`inFlightGrants + activeLeaders ≤ 1`)
and keep `dispatchGrant` inductive as well, we count the single authority token
across all three locations where it can reside:
-/

@[grind =]
def authorityCount (s : ClusterState) : Nat :=
  (if s.coordinatorHasAuthority then 1 else 0) + s.inFlightGrants + s.activeLeaders

abbrev TokenInvariant (s : ClusterState) : Prop :=
  authorityCount s ≤ 1

abbrev WireAndLeaderBound (s : ClusterState) : Prop :=
  s.inFlightGrants + s.activeLeaders ≤ 1

#guard !(edenWireState.inFlightGrants + edenWireState.activeLeaders ≤ 1)
#guard !(authorityCount edenWireState ≤ 1)

theorem tokenInvariant_init {s : ClusterState} (hInit : Init s) :
    TokenInvariant s := by
  rw [hInit]
  decide

/-!
## Exercises
-/

/--
Exercise 8.1: Prove that `edenWireState` satisfies `SafeMutualExclusion`, yet
takes a valid `Next.deliverGrant` step to a state `sBad` violating `SafeMutualExclusion`.
-/
theorem eden_breaks_naive_induction :
    SafeMutualExclusion edenWireState ∧
    ∃ sBad : ClusterState, Next edenWireState sBad ∧ ¬ SafeMutualExclusion sBad := by
  sorry

/--
Exercise 8.2a: Prove that `TokenInvariant` implies both `WireAndLeaderBound`
(`inFlightGrants + activeLeaders ≤ 1`) and `SafeMutualExclusion` (`activeLeaders ≤ 1`).
-/
theorem tokenInvariant_implies_safety (s : ClusterState)
    (hInv : TokenInvariant s) :
    WireAndLeaderBound s ∧ SafeMutualExclusion s := by
  sorry

/--
Exercise 8.2b (Inductive Step):
Prove that *every* transition of `Next` preserves `TokenInvariant`.
-/
theorem tokenInvariant_next {s s' : ClusterState}
    (hInv : TokenInvariant s) (hNext : Next s s') :
    TokenInvariant s' := by
  sorry

/--
Exercise 8.3a: Prove by induction on `hReach` (`induction hReach with ...`)
that every reachable state satisfies `TokenInvariant`.
-/
theorem reachable_tokenInvariant {s : ClusterState}
    (hReach : Reachable s) :
    TokenInvariant s := by
  sorry

/--
Exercise 8.3b (Unbounded Cluster Mutual Exclusion):
Conclude that every reachable state across executions of arbitrary length has at
most one active leader (`activeLeaders ≤ 1`).
-/
theorem reachable_mutual_exclusion {s : ClusterState}
    (hReach : Reachable s) :
    SafeMutualExclusion s := by
  sorry

end Ch08
