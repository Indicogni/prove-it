import Std.Tactic.BVDecide

/-
  Chapter 10: 64-Bit Hardware Truth (`UInt64` & `BitVec`)
  =======================================================

  Proofs over Lean's unbounded `Nat` guarantee mathematical correctness,
  not hardware correctness. On real CPUs—Rust `u64`, Go `uint64`, C `uint64_t`,
  and Lean's `UInt64` / `BitVec 64`—addition wraps modulo `2^64`.

  Worse, conventional fuzzing and property tests typically sample inputs from
  small ranges like `[0 .. 10^9]`, where two values can never sum to `2^64`.
  An AI-generated billing check can pass 100 million random tests and still
  let an attacker buy a `2^64 - 1`-credit asset for 10 credits.

  In Lean 4.36, `Std.Tactic.BVDecide` (`bv_decide`) bit-blasts fixed-width
  `BitVec` and `UInt64` goals to a verified SAT solver—exhaustively checking all
  `2^64` (or `2^192`) combinations in milliseconds and emitting a checked
  LRAT UNSAT certificate.
-/
set_option autoImplicit false

namespace ProveIt.Ch10

/-! ## 1. Catching a Wrap-Around Billing Bug That Passes `[0 .. 10^9]` Tests -/

/--
  BUGGY AI-generated affordability check:
  "A user can afford `price` plus `fee` when `price + fee ≤ balance`."
-/
def buggyCanAfford (balance price fee : BitVec 64) : Bool :=
  price + fee ≤ balance

-- Every test in `[0 .. 10^9]` passes without issue:
#guard buggyCanAfford 1_000_000_000#64 600_000_000_0#64 300_000_000#64 == false
#guard buggyCanAfford 1_000_000_000#64 600_000_000#64 300_000_000#64 == true
#guard buggyCanAfford 500_000_000#64 400_000_000#64 200_000_000#64 == false

/--
  EXPLOIT: Near `2^64 - 1` (`0xFFFF_FFFF_FFFF_FFFF#64`), `price + fee` wraps
  around modulo `2^64` to `9#64`, which is `≤ 100#64`!
-/
theorem buggyCanAfford_exploitable :
    buggyCanAfford 100#64 0xFFFF_FFFF_FFFF_FFFF#64 10#64 = true ∧
    ¬ (100#64 ≥ 0xFFFF_FFFF_FFFF_FFFF#64) := by
  unfold buggyCanAfford
  bv_decide

/--
  SAFE affordability check: rearrange subtraction after guarding `price ≤ balance`.
  Because `price ≤ balance`, `balance - price` cannot underflow!
-/
def safeCanAfford (balance price fee : BitVec 64) : Bool :=
  (price ≤ balance) && (fee ≤ balance - price)

/--
  Worked Example: `bv_decide` proves for ALL `2^192` triples `(balance, price, fee)`
  that `safeCanAfford` prevents unsigned addition overflow and guarantees
  both `price ≤ balance` and `price + fee ≤ balance`.
  Tip: Always `unfold` your custom definitions before calling `bv_decide`!
-/
theorem safeCanAfford_sound (balance price fee : BitVec 64)
    (hOk : safeCanAfford balance price fee = true) :
    ¬ BitVec.uaddOverflow price fee ∧
    price ≤ balance ∧
    fee ≤ balance ∧
    price + fee ≤ balance := by
  unfold safeCanAfford at hOk
  bv_decide

-- Notice `..._native.bv_decide...` in `#print axioms`: `bv_decide` checks its LRAT
-- UNSAT certificate using Lean's native evaluator, and `#print axioms` transparently
-- records that native reduction step in the theorem's trust footprint.
/--
info: 'ProveIt.Ch10.safeCanAfford_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 safeCanAfford_sound._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms safeCanAfford_sound

/-! ## 2. Saturating Token-Bucket Arithmetic -/

/-- Maximum 64-bit unsigned value (`2^64 - 1`). -/
abbrev maxU64 : BitVec 64 := 0xFFFF_FFFF_FFFF_FFFF#64

/--
  EXERCISE 1: Implement saturating 64-bit unsigned addition.
  If `BitVec.uaddOverflow a b` is true, saturate at `maxU64`; otherwise return `a + b`.
-/
def saturatingAdd64 (a b : BitVec 64) : BitVec 64 :=
  let _ := (a, b)
  sorry

-- Uncomment after completing Exercise 1:
-- #guard saturatingAdd64 100#64 250#64 == 350#64
-- #guard saturatingAdd64 maxU64 1#64 == maxU64

/--
  EXERCISE 2: Prove with `bv_decide` that `saturatingAdd64` is monotonic in both
  arguments (it never wraps downward below `a` or `b`).
-/
theorem saturatingAdd64_no_drop (a b : BitVec 64) :
    a ≤ saturatingAdd64 a b ∧ b ≤ saturatingAdd64 a b := by
  sorry

/--
  EXERCISE 3: Implement a wrap-safe token-bucket refill capped at `cap`.
  Refill `tokens` by `delta` using `saturatingAdd64`, then clamp to `cap`.
-/
def safeRefill (tokens delta cap : BitVec 64) : BitVec 64 :=
  let _ := (tokens, delta, cap)
  sorry

-- Uncomment after completing Exercise 3:
-- #guard safeRefill 900#64 50#64 1000#64 == 950#64
-- #guard safeRefill 900#64 0xFFFF_FFFF_FFFF_FC80#64 1000#64 == 1000#64

/--
  EXERCISE 4: Prove that whenever `tokens ≤ cap`, `safeRefill` never drops below
  `tokens` and never exceeds `cap`, even if an attacker supplies `delta = 2^64 - 1`.
-/
theorem safeRefill_bounds (tokens delta cap : BitVec 64) (hInit : tokens ≤ cap) :
    tokens ≤ safeRefill tokens delta cap ∧ safeRefill tokens delta cap ≤ cap := by
  sorry

/-! ## 3. Checked Fee Billing & `UInt64` Hardware Midpoints -/

/--
  EXERCISE 5: Implement `checkedBill`, returning `none` if `subtotal + fee`
  overflows 64 bits and `some (subtotal + fee)` otherwise.
-/
def checkedBill (subtotal fee : BitVec 64) : Option (BitVec 64) :=
  let _ := (subtotal, fee)
  sorry

-- Uncomment after completing Exercise 5:
-- #guard checkedBill 500#64 25#64 == some 525#64
-- #guard checkedBill maxU64 1#64 == none

/--
  EXERCISE 6: Prove that whenever `checkedBill` returns `some total`,
  `total` is at least `subtotal`, at least `fee`, and equals `subtotal + fee`
  without unsigned overflow.
-/
theorem checkedBill_sound (subtotal fee total : BitVec 64)
    (hBill : checkedBill subtotal fee = some total) :
    ¬ BitVec.uaddOverflow subtotal fee ∧
    subtotal ≤ total ∧
    fee ≤ total ∧
    total = subtotal + fee := by
  sorry

/-- Overflow-safe 64-bit midpoint on `UInt64`. -/
def safeMidU64 (lo hi : UInt64) : UInt64 :=
  lo + ((hi - lo) >>> 1)

#guard safeMidU64 0xFFFF_FFFF_FFFF_FFF0 0xFFFF_FFFF_FFFF_FFFE == 0xFFFF_FFFF_FFFF_FFF7

/--
  EXERCISE 7: Prove for all 64-bit hardware integers `lo ≤ hi` that `safeMidU64 lo hi`
  stays inside `[lo, hi]`—eliminating the classic `(lo + hi) >>> 1` overflow bug!
-/
theorem safeMidU64_in_bounds (lo hi : UInt64) (hLe : lo ≤ hi) :
    lo ≤ safeMidU64 lo hi ∧ safeMidU64 lo hi ≤ hi := by
  sorry

end ProveIt.Ch10
