set_option autoImplicit false

/-!
# Chapter 7: Unprovable on Purpose — Stuck-Infoview Triage

In textbook exercises, every theorem statement handed to you is true. In real
engineering verification, **most of your diagnostic skill lives in reading a
stuck Infoview goal**.

When tactics stall on an unsolved subgoal, ask which of three failure modes you
have uncovered:
1. **Buggy Implementation**: The code computes the wrong value on a valid input.
2. **False Specification**: The code behaves as intended, but the theorem statement
   omitted a required precondition.
3. **Too-Weak Invariant**: Both the code and the safety goal hold on reachable
   states, yet the goal is not preserved from arbitrary states satisfying only
   the weak hypothesis.
-/

namespace Ch07

/-!
## Case 1: Triage a Stuck Billing Refund Goal

A billing service refunds credits into a tenant wallet, intending to cap the
post-refund balance at `maxBalance`:
-/

@[grind =]
def creditRefundBuggy (balance refund maxBalance : Nat) : Nat :=
  if refund ≤ maxBalance then
    balance + refund
  else
    maxBalance

/-
PREDICT: Suppose `balance ≤ maxBalance`, and you try to prove
  `creditRefundBuggy balance refund maxBalance ≤ maxBalance`.
`fun_cases` leaves the Infoview goal:
  `hBal  : balance ≤ maxBalance`
  `hCond : refund ≤ maxBalance`
  `⊢ balance + refund ≤ maxBalance`
Is this a missing tactic, a false spec, or a buggy implementation? Pick concrete
numbers `(balance, refund, maxBalance)` that violate `balance + refund ≤ maxBalance`!
-/

/--
Exercise 7.1a: Exhibit a concrete `(balance, refund, maxBalance)` witness proving
`creditRefundBuggy` can exceed `maxBalance` even when `balance ≤ maxBalance`.
-/
theorem creditRefundBuggy_overflows_cap :
    ∃ balance refund maxBalance : Nat,
      balance ≤ maxBalance ∧
      maxBalance < creditRefundBuggy balance refund maxBalance := by
  sorry

/--
Exercise 7.1b: Implement `creditRefundFixed` so `balance + refund` is properly
capped at `maxBalance`, and prove its specification below.
-/
def creditRefundFixed (balance refund maxBalance : Nat) : Nat :=
  sorry

example : creditRefundFixed 80 50 100 = 100 := by sorry
example : creditRefundFixed 40 30 100 = 70 := by sorry

theorem creditRefundFixed_spec (balance refund maxBalance : Nat)
    (hBal : balance ≤ maxBalance) :
    balance ≤ creditRefundFixed balance refund maxBalance ∧
    creditRefundFixed balance refund maxBalance ≤ maxBalance ∧
    creditRefundFixed balance refund maxBalance ≤ balance + refund := by
  sorry

/-!
## Case 2: Triage a Stuck Ring-Buffer Cursor Goal

A circular ring buffer advances its write index modulo `capacity`:
-/

def ringNextSlot (cursor capacity : Nat) : Nat :=
  (cursor + 1) % capacity

/-
PREDICT: An engineer writes the precondition-free theorem:
  `∀ cursor capacity : Nat, ringNextSlot cursor capacity < capacity`
What does Lean evaluate `(0 + 1) % 0` to? Why does the theorem fail at `capacity = 0`?
-/
#guard ringNextSlot 0 0 == 1

/--
Exercise 7.2a: Refute the precondition-free specification!
-/
theorem ringNextSlot_unconditional_false :
    ¬ (∀ cursor capacity : Nat, ringNextSlot cursor capacity < capacity) := by
  sorry

/--
Exercise 7.2b: Prove the repaired specification with the non-empty ring-buffer
precondition `0 < capacity` (Hint: `Nat.mod_lt` has type `∀ a {b}, 0 < b → a % b < b`).
-/
theorem ringNextSlot_lt_capacity (cursor capacity : Nat)
    (hPos : 0 < capacity) :
    ringNextSlot cursor capacity < capacity := by
  sorry

/-!
## Case 3: Triage a Stuck Request-Tracker Step Goal

An RPC dispatcher tracks `submitted`, `completed`, and `inFlight` requests:
-/

structure TrackerState where
  submitted : Nat
  completed : Nat
  inFlight  : Nat
  deriving Repr, DecidableEq

def trackerInit : TrackerState :=
  { submitted := 0, completed := 0, inFlight := 0 }

@[grind =]
def onSubmit (s : TrackerState) : TrackerState :=
  { s with submitted := s.submitted + 1
           inFlight  := s.inFlight + 1 }

@[grind =]
def onComplete (s : TrackerState) : TrackerState :=
  if 0 < s.inFlight then
    { s with completed := s.completed + 1
             inFlight  := s.inFlight - 1 }
  else
    s

abbrev WeakSafety (s : TrackerState) : Prop :=
  s.completed ≤ s.submitted

/-
PREDICT: Starting from `trackerInit`, `WeakSafety` (`completed ≤ submitted`) holds
after any sequence of `onSubmit` and `onComplete` calls. Yet proving
  `∀ s, WeakSafety s → WeakSafety (onComplete s)`
directly stalls at:
  `hWeak : s.completed ≤ s.submitted`
  `hPos  : 0 < s.inFlight`
  `⊢ s.completed + 1 ≤ s.submitted`
Construct an unreachable `TrackerState` that satisfies `WeakSafety` and `0 < inFlight`,
but transitions under `onComplete` to `completed > submitted`!
-/

/--
Exercise 7.3a: Prove that `WeakSafety` alone is NOT preserved by `onComplete`
over arbitrary `TrackerState` records.
-/
theorem weakSafety_not_inductive :
    ¬ (∀ s : TrackerState, WeakSafety s → WeakSafety (onComplete s)) := by
  sorry

/--
Exercise 7.3b: Define a strengthened invariant `StrongInv` relating `completed`,
`inFlight`, and `submitted`, then prove all four obligations below.
-/
def StrongInv (s : TrackerState) : Prop :=
  sorry

theorem strongInv_init : StrongInv trackerInit := by
  sorry

theorem strongInv_onSubmit (s : TrackerState) (h : StrongInv s) :
    StrongInv (onSubmit s) := by
  sorry

theorem strongInv_onComplete (s : TrackerState) (h : StrongInv s) :
    StrongInv (onComplete s) := by
  sorry

theorem strongInv_implies_weak (s : TrackerState) (h : StrongInv s) :
    WeakSafety s := by
  sorry

end Ch07
