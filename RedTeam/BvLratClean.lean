/-
  RedTeam Baseline 2 — Hardware/BitVec `bv_decide` Module
  Rejected under Tier 0 (`--strict-kernel`), Accepted under Tier 1 (`--trust-tier=bv-lrat`).
-/
import Std.Tactic.BVDecide

set_option autoImplicit false

namespace RedTeam.BvLratClean

-- BEGIN VERIGATE SPEC
def xorRoundtrip (payload mask : BitVec 64) : BitVec 64 :=
  (payload ^^^ mask) ^^^ mask
-- END VERIGATE SPEC

theorem xorRoundtrip_id (payload mask : BitVec 64) :
    xorRoundtrip payload mask = payload := by
  unfold xorRoundtrip
  bv_decide

theorem non_vacuous :
    xorRoundtrip 0xdeadbeef_cafebabe#64 0x01020304_05060708#64 = 0xdeadbeef_cafebabe#64 := by
  decide

end RedTeam.BvLratClean
