/-
  Checkpoint 4 (Closed-Notes): Red-Team & Repair an AI-Verified Batch Escrow Module (Solutions)
  =============================================================================================

  An autonomous coding agent submitted `BuggyAI` below with a green CI badge:
  "Formally verified batch escrow engine — 100% kernel-checked!"

  Your mission in this closed-notes Part IV synthesis checkpoint:
  1. **Red-Team Audit (Exercises 1–2)**: Formally prove that the AI's module harbors
     three interacting specification & arithmetic flaws:
     - **Flaw 1 (Vacuous Precondition)**: `AiValidBatch` demands `reserveMin > pool`
       AND `sumList payouts + reserveMin ≤ pool`—making `aiSettle_safe` 100% vacuous!
     - **Flaw 2 (`Nat` Underflow on Unchecked Fee)**: `aiSettleOne` checks `payout ≤ pool`
       but forgets `+ fee`, so `pool - payout - fee` truncates to `0` on `Nat`!
     - **Flaw 3 (Weak Inequality Spec)**: `AiConserved` only checks `poolAfter ≤ poolBefore`,
       allowing both `Nat` underflow (`0 ≤ 100`) and vanishing funds!
  2. **Spec-First Repair (Exercises 3–6)**: Implement an atomic `settleOne` / `settleBatch`
     engine, prove exact conservation + reserve safety with zero admitted proof holes, and prove a
     multi-item **non-vacuity witness** audited by `#print axioms`.
-/
set_option autoImplicit false

namespace Solutions.Checkpoints.Cp4

/-! ## Phase 1: The Suspect AI Submission (`namespace BuggyAI`) -/

namespace BuggyAI

@[simp]
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

/-- FLAW 1: Look closely at `hReserve` vs `hBudget`! -/
def AiValidBatch (pool : Nat) (payouts : List Nat) (reserveMin : Nat) : Prop :=
  0 < payouts.length ∧
  pool < reserveMin ∧
  sumList payouts + reserveMin ≤ pool

/-- FLAW 2: Guards `payout ≤ pool`, but subtracts `fee` without checking `payout + fee ≤ pool`! -/
def aiSettleOne (pool payout fee : Nat) : Option Nat :=
  if payout ≤ pool then
    some (pool - payout - fee)
  else
    none

/-- FLAW 3: Weak inequality postcondition—permits both underflow and burned funds! -/
def AiConserved (poolBefore poolAfter : Nat) : Prop :=
  poolAfter ≤ poolBefore

/-- The AI's "green" theorem that sailed past a naive `lean` exit-code check: -/
theorem aiSettle_safe (pool : Nat) (payouts : List Nat) (reserveMin : Nat)
    (hValid : AiValidBatch pool payouts reserveMin) :
    AiConserved pool (pool + 999_999) := by
  unfold AiValidBatch at hValid
  omega

/--
  EXERCISE 1 (Expose Flaw 1 — Vacuous Precondition):
  Prove that `AiValidBatch` is unsatisfiable (`False`) for ALL inputs!
-/
theorem flaw1_vacuous (pool : Nat) (payouts : List Nat) (reserveMin : Nat)
    (h : AiValidBatch pool payouts reserveMin) : False := by
  unfold AiValidBatch at h
  omega

/--
  EXERCISE 2 (Expose Flaws 2 & 3 — Fee Underflow Passing `AiConserved`):
  Prove there exist `pool`, `payout`, `fee`, and `newPool` such that
  `aiSettleOne pool payout fee = some newPool`, the AI's weak `AiConserved pool newPool`
  HOLDS, yet `newPool + payout + fee > pool` (the engine disbursed more value than existed!).
-/
theorem flaw2_and_3_exploit :
    ∃ pool payout fee newPool : Nat,
      aiSettleOne pool payout fee = some newPool ∧
      AiConserved pool newPool ∧
      newPool + payout + fee > pool := by
  refine ⟨100, 95, 20, 0, rfl, ?_, by omega⟩
  unfold AiConserved
  omega

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
  if s.reserveMin + payout + fee ≤ s.pool then
    some { s with
      pool      := s.pool - (payout + fee)
      totalPaid := s.totalPaid + payout
      totalFees := s.totalFees + fee }
  else
    none

/--
  EXERCISE 3b: Implement all-or-nothing `settleBatch` over `items : List (Nat × Nat)`
  (where each pair is `(payout, fee)`). If any item fails, the entire batch returns `none`.
-/
def settleBatch (s : BatchState) : List (Nat × Nat) → Option BatchState
  | [] => some s
  | (payout, fee) :: rest =>
    match settleOne s payout fee with
    | none => none
    | some s1 => settleBatch s1 rest

/--
  EXERCISE 4 (Single-Item Soundness):
  Prove that whenever `settleOne` succeeds, `ReserveSafe` holds on `s'` AND
  `ExactConservation s s'` holds!
-/
theorem settleOne_sound (s s' : BatchState) (payout fee : Nat)
    (hStep : settleOne s payout fee = some s') :
    ReserveSafe s' ∧ ExactConservation s s' := by
  unfold settleOne at hStep
  split at hStep
  · injection hStep with hEq
    subst hEq
    refine ⟨?_, ?_, rfl⟩
    · unfold ReserveSafe; simp only; omega
    · simp only; omega
  · nomatch hStep

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
  induction items generalizing s with
  | nil =>
    simp only [settleBatch] at hBatch
    injection hBatch with hEq
    subst hEq
    exact ⟨hInit, ExactConservation.refl s⟩
  | cons item rest ih =>
    rcases item with ⟨payout, fee⟩
    simp only [settleBatch] at hBatch
    split at hBatch
    · nomatch hBatch
    · rename_i s1 hOne
      obtain ⟨hSafe1, hCons1⟩ := settleOne_sound s s1 payout fee hOne
      obtain ⟨hSafeF, hConsF⟩ := ih s1 hSafe1 hBatch
      exact ⟨hSafeF, ExactConservation.trans hCons1 hConsF⟩

/--
  EXERCISE 6 (Non-Vacuity & Multi-Item Liveness Witness):
  Prove that `VerifiedRepair` is neither vacuous nor stonewalling:
  exhibit a `ReserveSafe` initial state with `0 < s.reserveMin` and a 2-item batch
  that succeeds (`some sFinal`) with `0 < sFinal.totalPaid` and `0 < sFinal.totalFees`.
-/
theorem settleBatch_nonvacuous :
    ∃ (s sFinal : BatchState) (items : List (Nat × Nat)),
      ReserveSafe s ∧
      0 < s.reserveMin ∧
      items.length = 2 ∧
      settleBatch s items = some sFinal ∧
      0 < sFinal.totalPaid ∧
      0 < sFinal.totalFees := by
  let s0 : BatchState := { pool := 100, reserveMin := 20, totalPaid := 0, totalFees := 0 }
  let batch : List (Nat × Nat) := [(30, 2), (25, 1)]
  refine ⟨s0, _, batch, ?_, by decide, rfl, rfl, by decide, by decide⟩
  unfold ReserveSafe
  decide

end VerifiedRepair

/-- info: 'Solutions.Checkpoints.Cp4.VerifiedRepair.settleBatch_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedRepair.settleBatch_sound

/-- info: 'Solutions.Checkpoints.Cp4.VerifiedRepair.settleBatch_nonvacuous' does not depend on any axioms -/
#guard_msgs in
#print axioms VerifiedRepair.settleBatch_nonvacuous

end Solutions.Checkpoints.Cp4
