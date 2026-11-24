/-
  RedTeam Exploit 3 — `native_decide` Compiler-Trust Bypass Cheat
  Rejected by BOTH Tier 0 (`--strict-kernel`) and Tier 1 (`--trust-tier=bv-lrat`).
-/
set_option autoImplicit false

namespace RedTeam.NativeDecideCheat

-- BEGIN VERIGATE SPEC
structure Vault where
  balance : Nat
  cap : Nat
  deriving Repr, DecidableEq

def ValidVault (v : Vault) : Prop :=
  v.balance ≤ v.cap
-- END VERIGATE SPEC

def sampleVault : Vault := { balance := 20, cap := 50 }

-- CHEAT: invokes `native_decide`, pulling the native code generator into the TCB!
theorem sampleVault_valid : ValidVault sampleVault := by
  unfold ValidVault sampleVault
  native_decide

theorem non_vacuous : sampleVault.balance = 20 := by
  decide

end RedTeam.NativeDecideCheat
