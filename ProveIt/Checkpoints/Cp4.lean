/-
  Checkpoint 4 (Closed-Notes): Red-Team & Repair an AI-Verified Batch Escrow Module
  =================================================================================

  An autonomous coding agent submitted `BuggyAI` below with a green CI badge:
  "Formally verified batch escrow engine — zero `sorry`!"

  Your mission in this closed-notes Part IV synthesis checkpoint:
  1. **Red-Team Audit (Exercises 1–2)**: Audit `BuggyAI` to uncover three planted
     specification & arithmetic flaws (vacuity, unchecked `Nat` subtraction, and
     a dangerously weak postcondition), proving formal exploit theorems against it.
  2. **Spec-First Repair (Exercises 3–6)**: Implement an atomic `settleOne` / `settleBatch`
     engine inside `VerifiedRepair`, prove exact double-entry conservation + reserve
     safety with zero `sorry`, and prove a multi-item **non-vacuity witness**!
-/
set_option autoImplicit false

namespace ProveIt.Checkpoints.Cp4

/-! ## Phase 1: Audit the Suspect AI Submission (`namespace BuggyAI`) -/

namespace BuggyAI

@[simp]
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

/-- Inspect every conjunct of the AI's precondition carefully! -/
def AiValidBatch (pool : Nat) (payouts : List Nat) (reserveMin : Nat) : Prop :=
  0 < payouts.length ∧
  pool < reserveMin ∧
  sumList payouts + reserveMin ≤ pool

/-- Inspect the guard vs the subtraction in the AI's single-item settlement! -/
def aiSettleOne (pool payout fee : Nat) : Option Nat :=
  if payout ≤ pool then
    some (pool - payout - fee)
  else
    none

/-- Inspect what the AI's "conservation" predicate actually checks! -/
def AiConserved (poolBefore poolAfter : Nat) : Prop :=
  poolAfter ≤ poolBefore

/-- The AI's "green" theorem that sailed past a naive `lean` exit-code check: -/
theorem aiSettle_safe (pool : Nat) (payouts : List Nat) (reserveMin : Nat)
    (hValid : AiValidBatch pool payouts reserveMin) :
    AiConserved pool (pool + 999_999) := by
  unfold AiValidBatch at hValid
  omega

/--
  EXERCISE 1 (Diagnose Flaw 1 — Vacuous Precondition):
  Prove that `AiValidBatch` is unsatisfiable (`False`) for ALL inputs!
-/
theorem flaw1_vacuous (pool : Nat) (payouts : List Nat) (reserveMin : Nat)
    (h : AiValidBatch pool payouts reserveMin) : False := by
  sorry

/--
  EXERCISE 2 (Diagnose Flaws 2 & 3 — Underflow Passing Weak `AiConserved`):
  Exhibit concrete `pool`, `payout`, `fee`, and `newPool` such that
  `aiSettleOne pool payout fee = some newPool`, the AI's `AiConserved pool newPool`
  HOLDS, yet `newPool + payout + fee > pool` (more value disbursed than existed!).
-/
theorem flaw2_and_3_exploit :
    ∃ pool payout fee newPool : Nat,
      aiSettleOne pool payout fee = some newPool ∧
      AiConserved pool newPool ∧
      newPool + payout + fee > pool := by
  sorry

end BuggyAI

/-! ## Phase 2: Spec-First Verified Batch Escrow (`namespace VerifiedRepair`) -/

namespace VerifiedRepair

/-- Authoritative state of the repaired batch escrow pool. -/
structure BatchState where
  pool       : Nat
  reserveMin : Nat
  totalPaid  : Nat
  totalFees  : Nat
  deriving Repr, DecidableEq

/-- Invariant 1: Pool never drops below the required minimum reserve. -/
def ReserveSafe (s : BatchState) : Prop :=
  s.reserveMin ≤ s.pool

/-- Invariant 2: Exact double-entry conservation across pool, payouts, and fees,
    plus immutability of the configured `reserveMin`. -/
def ExactConservation (before after : BatchState) : Prop :=
  after.pool + after.totalPaid + after.totalFees =
    before.pool + before.totalPaid + before.totalFees ∧
  after.reserveMin = before.reserveMin

theorem ExactConservation.refl (s : BatchState) : ExactConservation s s :=
  ⟨rfl, rfl⟩

theorem ExactConservation.trans {s1 s2 s3 : BatchState}
    (h12 : ExactConservation s1 s2) (h23 : ExactConservation s2 s3) :
    ExactConservation s1 s3 := by
  obtain ⟨hBal12, hRes12⟩ := h12
  obtain ⟨hBal23, hRes23⟩ := h23
  refine ⟨by omega, by rw [hRes23, hRes12]⟩

/--
  EXERCISE 3a: Implement `settleOne`.
  Succeeds (`some ...`) iff `s.reserveMin + payout + fee ≤ s.pool`, deducting
  `payout + fee` from `pool`, adding `payout` to `totalPaid`, and adding `fee`
  to `totalFees`. Otherwise returns `none`.
-/
def settleOne (s : BatchState) (payout fee : Nat) : Option BatchState :=
  let _ := (s, payout, fee)
  sorry

/--
  EXERCISE 3b: Implement all-or-nothing `settleBatch` over `items : List (Nat × Nat)`
  (where each pair is `(payout, fee)`). If any item fails, the entire batch returns `none`.
-/
def settleBatch (s : BatchState) (items : List (Nat × Nat)) : Option BatchState :=
  let _ := (s, items)
  sorry

/--
  EXERCISE 4 (Single-Item Soundness):
  Prove that whenever `settleOne` succeeds, `ReserveSafe` holds on `s'` AND
  `ExactConservation s s'` holds!
-/
theorem settleOne_sound (s s' : BatchState) (payout fee : Nat)
    (hStep : settleOne s payout fee = some s') :
    ReserveSafe s' ∧ ExactConservation s s' := by
  sorry

/--
  EXERCISE 5 (Full-Batch Atomic Soundness):
  Prove by induction on `items` that if `ReserveSafe s` holds and
  `settleBatch s items = some sFinal`, then BOTH `ReserveSafe sFinal`
  and `ExactConservation s sFinal` hold!
-/
theorem settleBatch_sound (s sFinal : BatchState) (items : List (Nat × Nat))
    (hInit : ReserveSafe s)
    (hBatch : settleBatch s items = some sFinal) :
    ReserveSafe sFinal ∧ ExactConservation s sFinal := by
  sorry

/--
  EXERCISE 6 (Non-Vacuity & Multi-Item Liveness Witness):
  Prove that `VerifiedRepair` is neither vacuous nor stonewalling:
  exhibit a `ReserveSafe` initial state with `0 < s.reserveMin` and a 2-item batch
  that succeeds (`some sFinal`) with `0 < sFinal.totalPaid` and `0 < sFinal.totalFees`.
  Tip: Use moderate numbers (e.g. `pool := 100`) so `rfl` / `decide` reduces instantly!
-/
theorem settleBatch_nonvacuous :
    ∃ (s sFinal : BatchState) (items : List (Nat × Nat)),
      ReserveSafe s ∧
      0 < s.reserveMin ∧
      items.length = 2 ∧
      settleBatch s items = some sFinal ∧
      0 < sFinal.totalPaid ∧
      0 < sFinal.totalFees := by
  sorry

end VerifiedRepair

end ProveIt.Checkpoints.Cp4
