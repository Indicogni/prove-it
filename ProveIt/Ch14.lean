/-
  Chapter 14: Spec-First Agentic Co-Design
  ========================================

  How do engineering teams collaborate safely with coding agents on critical
  financial or infrastructure logic?

  1. **Freeze `namespace Spec` (Human-Owned, CI-Protected)**:
     Humans define domain types, safety invariants, finality rules, and
     non-vacuity witnesses. Coding agents have READ-ONLY access to `Spec`.
  2. **Synthesize `namespace Impl` with Skeleton-Driven `have` Decomposition**:
     Instead of letting an agent spew a fragile 80-line tactic script, structure
     proofs around explicit intermediate `have` claims (`have hSplit := ...`).
     Each `have` acts as an isolated, readable sub-lemma that never breaks
     neighboring steps when business logic evolves.
-/
set_option autoImplicit false

namespace ProveIt.Ch14

/-! ## Part 1: Human-Owned Specification (`namespace Spec` — Read-Only in CI) -/

namespace Spec

inductive EscrowPhase where
  | funded
  | disputed
  | released
  | refunded
  deriving Repr, DecidableEq

inductive Action where
  | release         (feeBps : Nat)
  | refund
  | dispute
  | resolveToSeller (feeBps : Nat)
  | resolveToBuyer
  deriving Repr, DecidableEq

structure EscrowState where
  buyerPaid    : Nat
  escrowLocked : Nat
  sellerPayout : Nat
  buyerRefund  : Nat
  protocolFee  : Nat
  phase        : EscrowPhase
  deriving Repr, DecidableEq

/-- Initial funded escrow state when a buyer deposits `deposit` units. -/
def initEscrow (deposit : Nat) : EscrowState :=
  { buyerPaid    := deposit
    escrowLocked := deposit
    sellerPayout := 0
    buyerRefund  := 0
    protocolFee  := 0
    phase        := .funded }

/-- Every unit deposited by the buyer is accounted for across the 4 buckets. -/
def Conserved (s : EscrowState) : Prop :=
  s.escrowLocked + s.sellerPayout + s.buyerRefund + s.protocolFee = s.buyerPaid

/-- Active phases hold the full deposit; terminal phases hold zero locked funds. -/
def ValidPhase (s : EscrowState) : Prop :=
  match s.phase with
  | .funded | .disputed => s.escrowLocked = s.buyerPaid
  | .released | .refunded => s.escrowLocked = 0

/-- Combined system invariant owned by `Spec`. -/
def Invariant (s : EscrowState) : Prop :=
  Conserved s ∧ ValidPhase s

/-- Protocol fee cap: at most `1_000` basis points (10.00%). -/
def ValidFeeBps (feeBps : Nat) : Prop :=
  feeBps ≤ 1_000

def IsTerminal (p : EscrowPhase) : Prop :=
  p = .released ∨ p = .refunded

/-- Human-authored non-vacuity check on `Spec.Invariant` before handing off to `Impl`. -/
theorem initEscrow_invariant (deposit : Nat) : Invariant (initEscrow deposit) := by
  refine ⟨?_, rfl⟩
  unfold Conserved initEscrow
  simp only
  omega

end Spec

/-! ## Part 2: Implementation & Skeleton-Driven Proofs (`namespace Impl`) -/

namespace Impl

open Spec

/-- Split `locked` funds into `(sellerPayout, protocolFee)` given `feeBps` out of `10_000`. -/
def splitPayout (locked feeBps : Nat) : Nat × Nat :=
  let fee := (locked * feeBps) / 10_000
  (locked - fee, fee)

/--
  Worked Example (Skeleton-Driven `have` Decomposition):
  Notice how stating `hMul` and `hFeeLe` explicitly makes the nonlinear bound
  `fee ≤ locked` transparent and keeps `omega` instant on the final goal!
-/
theorem splitPayout_spec (locked feeBps : Nat) (hCap : ValidFeeBps feeBps) :
    (splitPayout locked feeBps).1 + (splitPayout locked feeBps).2 = locked ∧
    (splitPayout locked feeBps).2 ≤ locked := by
  unfold ValidFeeBps at hCap
  dsimp only [splitPayout]
  have hMul : locked * feeBps ≤ locked * 10_000 :=
    Nat.mul_le_mul_left locked (by omega)
  have hFeeLe : (locked * feeBps) / 10_000 ≤ (locked * 10_000) / 10_000 :=
    Nat.div_le_div_right hMul
  omega

/--
  EXERCISE 1: Implement the escrow state-transition function `step`.
  Rules:
  - `.funded`:
    - `.release feeBps`: if `feeBps ≤ 1_000`, `let sp := splitPayout s.escrowLocked feeBps`,
      add `sp.1` to `sellerPayout`, `sp.2` to `protocolFee`, set `escrowLocked := 0`,
      `phase := .released`; else `none`.
    - `.refund`: move `s.escrowLocked` into `s.buyerRefund`, `escrowLocked := 0`, `phase := .refunded`.
    - `.dispute`: keep balances unchanged, set `phase := .disputed`.
    - any other action: `none`.
  - `.disputed`:
    - `.resolveToSeller feeBps`: if `feeBps ≤ 1_000`, disburse `s.escrowLocked` via `splitPayout`
      (`sp.1` / `sp.2`), `escrowLocked := 0`, `phase := .released`; else `none`.
    - `.resolveToBuyer`: move `s.escrowLocked` into `s.buyerRefund`, `escrowLocked := 0`, `phase := .refunded`.
    - any other action: `none`.
  - `.released` or `.refunded`: always return `none` (terminal finality!).
-/
def step (s : EscrowState) (act : Action) : Option EscrowState :=
  let _ := (s, act)
  sorry

/--
  EXERCISE 2 (Terminal Finality): Prove that once an escrow reaches a terminal
  phase (`IsTerminal s.phase`), NO action can ever transition it again!
-/
theorem step_terminal_final (s : EscrowState) (act : Action)
    (hTerm : IsTerminal s.phase) :
    step s act = none := by
  sorry

/--
  EXERCISE 3 (Skeleton-Driven Invariant Preservation):
  Prove that `step` preserves `Spec.Invariant` (`Conserved ∧ ValidPhase`) across
  all reachable transitions.
  Tip: `split at hStep` produces ONLY the match arms of `step` (instead of
  `4 × 5 = 20` cross-product cases)—keeping the proof resilient if new actions are added!
-/
theorem step_preserves_invariant (s s' : EscrowState) (act : Action)
    (hInv : Invariant s) (hStep : step s act = some s') :
    Invariant s' := by
  sorry

/--
  EXERCISE 4 (Multi-Step Non-Vacuity & Liveness Contract):
  Prove that `Impl.step` actually executes BOTH a contested arbitration payout
  (`funded → disputed → released` with positive seller payout AND positive fee)
  AND a buyer refund (`funded → refunded`).
  This blocks any stonewalling implementation from passing CI!
-/
theorem impl_liveness_nonvacuous :
    (∃ s1 s2 : EscrowState,
      step (initEscrow 10_000) .dispute = some s1 ∧
      step s1 (.resolveToSeller 250) = some s2 ∧
      0 < s2.sellerPayout ∧ 0 < s2.protocolFee ∧ s2.phase = .released) ∧
    (∃ sr : EscrowState,
      step (initEscrow 10_000) .refund = some sr ∧
      sr.buyerRefund = 10_000 ∧ sr.phase = .refunded) := by
  sorry

end Impl

end ProveIt.Ch14
