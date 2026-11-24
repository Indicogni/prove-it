/-
  Chapter 13: How AI Cheats Formal Verification (Solutions)
  =========================================================

  Lean's kernel cannot be tricked into accepting an invalid proof of a theorem.
  So when you ask an LLM agent to "implement `X` and prove it correct in Lean 4"
  with a reward loop gated only on `lean` exiting `0`, how does the agent cheat?

  It cheats at the **specification boundary**! Here are the 5 classic exploits:
  1. **Vacuous Preconditions**: Contradictory hypotheses (`x > 10 ∧ x < 5`) make
     `False → Anything` trivially provable—even for `def withdraw := 999999`!
  2. **Always-`none` Rejection**: Satisfying `run s = some s' → Safe s'` by
     making `run` unconditionally return `none`!
  3. **Tautological / Mirror Specs**: Defining `Spec` by copying the buggy `Impl`
     so `impl x = spec x` reduces by `rfl`.
  4. **`Nat` Truncating Underflow**: Using `bal - amt` on `Nat` where `20 - 100 = 0`,
     passing `newBal ≤ bal` while letting an attacker withdraw 100 from 20!
  5. **Axiom Smuggling**: Declaring `axiom trust_me : ...` or leaving admitted proof holes,
     instantly caught by `#print axioms`.

  Defense: Frozen human-owned specs, `#print axioms` gates, and mandatory
  **Non-Vacuity Witnesses** (`∃ input output, Pre input ∧ run input = some output`).
-/
set_option autoImplicit false

namespace Solutions.Ch13

/-! ## Exploit 1: Vacuous Hypotheses (`False` in Disguise) -/

/--
  AI-written precondition that looks plausible at a glance, but silently demands
  `10 < x` and `x < 5` simultaneously!
-/
def BadPre (x : Nat) : Prop := x > 10 ∧ x < 5

/-- Broken implementation that steals funds! -/
def brokenPayout (x : Nat) : Nat := x + 1_000_000

/--
  Worked Example: The kernel happily accepts this "safety theorem" because `BadPre x`
  is impossible—`omega` derives `False` from `h` without even looking at `brokenPayout`!
-/
theorem brokenPayout_looks_safe (x : Nat) (h : BadPre x) :
    brokenPayout x ≤ x := by
  unfold BadPre at h
  omega

/-! ## Exploit 2: Always-`none` Trivial Satisfaction -/

/-- An AI agent asked to prove `aiTransfer s amt = some s' → Conservation s s'`
    can trivially satisfy the implication by rejecting every request! -/
def stonewallTransfer (_bal _amt : Nat) : Option Nat := none

theorem stonewallTransfer_vacuously_conserves (bal amt rem : Nat)
    (hOk : stonewallTransfer bal amt = some rem) :
    rem + amt = bal := by
  nomatch hOk

/-! ## Exploit 3 & 4: Tautological Specs & Axiom Smuggling Audit -/

/-- Tautological spec anti-pattern: never let the implementation define its own oracle! -/
def buggyFee (amt : Nat) : Nat := amt * 105 / 100 -- 105% instead of 5%!
theorem tautological_fee_spec (amt : Nat) : buggyFee amt = buggyFee amt := rfl

-- Audit Gate: `#print axioms` lists every axiom in a theorem's transitive dependency
-- cone. Anything outside `[propext, Classical.choice, Quot.sound]` (or explicitly
-- approved `bv_decide` certificates) fails review immediately!
/-- info: 'Solutions.Ch13.stonewallTransfer_vacuously_conserves' does not depend on any axioms -/
#guard_msgs in
#print axioms stonewallTransfer_vacuously_conserves

/-! ## Exercises: Red-Teaming & Hardening Against AI Verification Cheats -/

/--
  An AI-generated rate-limiter config structure with subtly contradictory invariants:
  `burstLimit` must be at least `2 * sustainedRate`, `sustainedRate ≥ 50`,
  yet `burstLimit ≤ 80`!
-/
structure BadLimiterConfig where
  sustainedRate : Nat
  burstLimit    : Nat
  hMinRate      : 50 ≤ sustainedRate
  hBurst        : 2 * sustainedRate ≤ burstLimit
  hCap          : burstLimit ≤ 80

/--
  EXERCISE 1 (Expose Vacuity): Prove that `BadLimiterConfig` has ZERO inhabitants!
  Any theorem of the form `∀ (cfg : BadLimiterConfig), ...` is 100% vacuous.
-/
theorem badLimiterConfig_vacuous (cfg : BadLimiterConfig) : False := by
  have h1 := cfg.hMinRate
  have h2 := cfg.hBurst
  have h3 := cfg.hCap
  omega

/-- Repaired configuration with consistent bounds (`burstLimit ≤ 500`). -/
structure GoodLimiterConfig where
  sustainedRate : Nat
  burstLimit    : Nat
  hMinRate      : 50 ≤ sustainedRate
  hBurst        : 2 * sustainedRate ≤ burstLimit
  hCap          : burstLimit ≤ 500

/--
  EXERCISE 2 (Non-Vacuity Witness): Prove that `GoodLimiterConfig` is inhabited
  by constructing an explicit witness with strict headroom (`2 * sustainedRate < burstLimit`).
-/
theorem goodLimiterConfig_nonvacuous :
    ∃ cfg : GoodLimiterConfig, 2 * cfg.sustainedRate < cfg.burstLimit := by
  refine ⟨{
    sustainedRate := 100
    burstLimit    := 250
    hMinRate      := by omega
    hBurst        := by omega
    hCap          := by omega
  }, by simp only; omega⟩

/-! ### Catching & Fixing `Nat` Truncating-Subtraction Underflow -/

/--
  AI-written withdrawal on `Nat`: `bal - amt` truncates to `0` when `amt > bal`!
  Notice it even satisfies `naiveWithdraw bal amt ≤ bal`!
-/
def naiveWithdraw (bal amt : Nat) : Nat := bal - amt

theorem naiveWithdraw_deceptive_bound (bal amt : Nat) : naiveWithdraw bal amt ≤ bal := by
  unfold naiveWithdraw
  omega

/--
  EXERCISE 3 (Red-Team `Nat` Underflow): Exhibit concrete `bal` and `amt` showing
  that after `rem := naiveWithdraw bal amt`, `rem + amt > bal` (money created out of thin air!).
-/
theorem naiveWithdraw_creates_money :
    ∃ bal amt : Nat, naiveWithdraw bal amt + amt > bal := by
  refine ⟨20, 100, ?_⟩
  unfold naiveWithdraw
  omega

/--
  EXERCISE 4 (Verified Checked Withdrawal): Implement `checkedWithdraw` so it
  succeeds (`some (bal - amt)`) iff `amt ≤ bal`, and returns `none` otherwise.
-/
def checkedWithdraw (bal amt : Nat) : Option Nat :=
  if amt ≤ bal then
    some (bal - amt)
  else
    none

#guard checkedWithdraw 100 40 == some 60
#guard checkedWithdraw 20 100 == none

/--
  EXERCISE 5 (Exact Conservation + Anti-Stonewalling Non-Vacuity):
  Prove BOTH:
  1. Soundness: whenever `checkedWithdraw bal amt = some rem`, `rem + amt = bal`
     (impossible to satisfy if `Nat` underflow occurred!).
  2. Non-Vacuity / Liveness Witness: there exist `bal`, `amt > 0`, and `rem`
     where `checkedWithdraw bal amt = some rem` (impossible for `stonewallTransfer`!).
-/
theorem checkedWithdraw_conserves (bal amt rem : Nat)
    (hOk : checkedWithdraw bal amt = some rem) :
    rem + amt = bal := by
  unfold checkedWithdraw at hOk
  split at hOk
  · injection hOk with hRem
    omega
  · nomatch hOk

theorem checkedWithdraw_nonvacuous :
    ∃ bal amt rem : Nat, 0 < amt ∧ checkedWithdraw bal amt = some rem := by
  refine ⟨100, 40, 60, by omega, rfl⟩

/-- info: 'Solutions.Ch13.checkedWithdraw_conserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkedWithdraw_conserves

/-- info: 'Solutions.Ch13.checkedWithdraw_nonvacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkedWithdraw_nonvacuous

end Solutions.Ch13
