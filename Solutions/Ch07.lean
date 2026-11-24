set_option autoImplicit false

/-!
# Chapter 7: Unprovable on Purpose — Stuck-Infoview Triage (Reference Solutions)

In textbook exercises, every theorem handed to you is already true. In real-world
software verification, **most of your engineering judgment happens when a proof
gets stuck**.

When Lean's Infoview leaves an unprovable subgoal, ask which of three root causes
you are looking at:
1. **Buggy Implementation**: The code computes the wrong answer on valid inputs.
2. **False Specification**: The code behaves as intended, but the theorem omitted
   a required precondition.
3. **Too-Weak Invariant**: Both the code and the safety property hold on all
   reachable states, yet the property is not preserved from arbitrary states
   that satisfy only the weak hypothesis.
-/

namespace Ch07

/-!
## Case 1: Buggy Implementation (`creditRefundBuggy`)

A billing service refunds credits to a tenant wallet, intending to cap the
post-refund balance at `maxBalance`:
-/

@[grind =]
def creditRefundBuggy (balance refund maxBalance : Nat) : Nat :=
  if refund ≤ maxBalance then
    balance + refund
  else
    maxBalance

/-
If you attempt to prove:
  `balance ≤ maxBalance → creditRefundBuggy balance refund maxBalance ≤ maxBalance`
with `fun_cases creditRefundBuggy balance refund maxBalance <;> omega`,
Lean's Infoview halts on the first branch with:
  `hBal : balance ≤ maxBalance`
  `hCond : refund ≤ maxBalance`
  `⊢ balance + refund ≤ maxBalance`
Reading that stuck goal directly hands you a concrete counterexample: pick
`balance = 80`, `refund = 50`, `maxBalance = 100`!
-/

-- Counterexample witness verified at compile time:
#guard creditRefundBuggy 80 50 100 == 130
#guard !(creditRefundBuggy 80 50 100 ≤ 100)

/--
Exercise 7.1a: Prove that the naive bound fails on `creditRefundBuggy` by
exhibiting a concrete `(balance, refund, maxBalance)` counterexample.
-/
theorem creditRefundBuggy_overflows_cap :
    ∃ balance refund maxBalance : Nat,
      balance ≤ maxBalance ∧
      maxBalance < creditRefundBuggy balance refund maxBalance := by
  refine ⟨80, 50, 100, ?_, ?_⟩ <;> decide

/--
Exercise 7.1b: Fix the implementation in `creditRefundFixed` so the returned
balance caps `balance + refund` at `maxBalance`, and prove both upper-bound and
no-loss properties when `balance ≤ maxBalance`.
-/
@[grind =]
def creditRefundFixed (balance refund maxBalance : Nat) : Nat :=
  if balance + refund ≤ maxBalance then
    balance + refund
  else
    maxBalance

#guard creditRefundFixed 80 50 100 == 100
#guard creditRefundFixed 40 30 100 == 70

theorem creditRefundFixed_spec (balance refund maxBalance : Nat)
    (hBal : balance ≤ maxBalance) :
    balance ≤ creditRefundFixed balance refund maxBalance ∧
    creditRefundFixed balance refund maxBalance ≤ maxBalance ∧
    creditRefundFixed balance refund maxBalance ≤ balance + refund := by
  fun_cases creditRefundFixed balance refund maxBalance <;> omega

/-!
## Case 2: False Specification (`ringNextSlot`)

A lock-free ring buffer advances its write cursor modulo `capacity`:
-/

def ringNextSlot (cursor capacity : Nat) : Nat :=
  (cursor + 1) % capacity

/-
Suppose an engineer writes the specification:
  `∀ cursor capacity : Nat, ringNextSlot cursor capacity < capacity`
Why is this unprovable? In Lean (to stay total without division-by-zero panics),
`n % 0 = n`. At `capacity = 0`, `ringNextSlot 0 0 = 1`, which is not `< 0`!
The implementation is standard; the *specification* forgot `0 < capacity`.
-/

#guard ringNextSlot 0 0 == 1
#guard !(ringNextSlot 0 0 < 0)

/--
Exercise 7.2a: Refute the precondition-free specification!
-/
theorem ringNextSlot_unconditional_false :
    ¬ (∀ cursor capacity : Nat, ringNextSlot cursor capacity < capacity) := by
  intro hAll
  have hZero : ringNextSlot 0 0 < 0 := hAll 0 0
  nomatch hZero

/--
Exercise 7.2b: Prove the repaired specification with the non-empty ring-buffer
precondition `0 < capacity` (Hint: `Nat.mod_lt` proves `a % b < b` from `0 < b`).
-/
theorem ringNextSlot_lt_capacity (cursor capacity : Nat)
    (hPos : 0 < capacity) :
    ringNextSlot cursor capacity < capacity := by
  unfold ringNextSlot
  exact Nat.mod_lt (cursor + 1) hPos

/-!
## Case 3: Too-Weak Invariant (`TrackerState`)

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
Starting from `trackerInit`, `WeakSafety` (`completed ≤ submitted`) is genuinely
true after any sequence of `onSubmit` and `onComplete` calls!
Yet if you try to prove the inductive step `WeakSafety s → WeakSafety (onComplete s)`
directly, the Infoview gets stuck at:
  `hWeak : s.completed ≤ s.submitted`
  `hPos  : 0 < s.inFlight`
  `⊢ s.completed + 1 ≤ s.submitted`
Look at `bogusState := { submitted := 5, completed := 5, inFlight := 1 }`:
it satisfies `WeakSafety` (`5 ≤ 5`), yet `onComplete bogusState` produces
`completed = 6 > submitted = 5`!
-/

def bogusState : TrackerState :=
  { submitted := 5, completed := 5, inFlight := 1 }

#guard bogusState.completed ≤ bogusState.submitted
#guard !((onComplete bogusState).completed ≤ (onComplete bogusState).submitted)

/--
Exercise 7.3a: Prove that `WeakSafety` alone is NOT preserved by `onComplete`
over arbitrary `TrackerState` records.
-/
theorem weakSafety_not_inductive :
    ¬ (∀ s : TrackerState, WeakSafety s → WeakSafety (onComplete s)) := by
  intro hStep
  have hWeak : WeakSafety bogusState := by decide
  have hNext : WeakSafety (onComplete bogusState) := hStep bogusState hWeak
  revert hNext
  decide

/--
Exercise 7.3b: Strengthen the invariant! Define `StrongInv` to capture exact
request conservation (`completed + inFlight = submitted`), then prove it holds
at `trackerInit`, is preserved by both `onSubmit` and `onComplete`, and implies
`WeakSafety`.
-/
@[grind =]
def StrongInv (s : TrackerState) : Prop :=
  s.completed + s.inFlight = s.submitted

theorem strongInv_init : StrongInv trackerInit := by
  rfl

theorem strongInv_onSubmit (s : TrackerState) (h : StrongInv s) :
    StrongInv (onSubmit s) := by
  dsimp [StrongInv, onSubmit] at *
  omega

theorem strongInv_onComplete (s : TrackerState) (h : StrongInv s) :
    StrongInv (onComplete s) := by
  fun_cases onComplete s <;> dsimp [StrongInv] at * <;> omega

theorem strongInv_implies_weak (s : TrackerState) (h : StrongInv s) :
    WeakSafety s := by
  dsimp [StrongInv, WeakSafety] at *
  omega

/-- info: 'Ch07.creditRefundFixed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms creditRefundFixed_spec

/-- info: 'Ch07.strongInv_onComplete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms strongInv_onComplete

end Ch07
