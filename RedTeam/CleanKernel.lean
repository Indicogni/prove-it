/-
  RedTeam Baseline 1 — Clean Tier-0 Verified Kernel
  Passes `verigate --strict-kernel` AND SHA-256 spec-lock check.
-/
set_option autoImplicit false

namespace RedTeam.CleanKernel

-- BEGIN VERIGATE SPEC
structure Vault where
  balance : Nat
  cap : Nat
  deriving Repr, DecidableEq

def ValidVault (v : Vault) : Prop :=
  v.balance ≤ v.cap
-- END VERIGATE SPEC

def depositBounded (v : Vault) (amt : Nat) : Option Vault :=
  if decide (v.balance + amt ≤ v.cap) then
    some { v with balance := v.balance + amt }
  else
    none

theorem depositBounded_sound {v v' : Vault} {amt : Nat}
    (hStep : depositBounded v amt = some v') :
    ValidVault v' := by
  unfold depositBounded at hStep
  by_cases hOk : v.balance + amt ≤ v.cap
  · simp [hOk] at hStep
    subst hStep
    exact hOk
  · simp [hOk] at hStep

theorem non_vacuous :
    ∃ v' : Vault, depositBounded { balance := 10, cap := 50 } 25 = some v' ∧ v'.balance = 35 := by
  refine ⟨{ balance := 35, cap := 50 }, ?_⟩
  decide

end RedTeam.CleanKernel
