set_option autoImplicit false

/-!
# Chapter 6: Control Flow, Rewriting & Linear Arithmetic (Reference Solutions)

Real systems code branches heavily: retry controllers clamp backoff intervals,
quota managers move tokens between `available`, `reserved`, and `used` buckets,
and multi-tier rate limiters enforce plan caps alongside cluster ceilings.

Writing nested `unfold` + `split` scripts by hand grows brittle fast. Lean 4.36
provides four tools that keep control-flow proofs short and resilient:
1. `fun_cases` — branches along the exact control-flow paths of a function call.
2. `simp only [...]` — rewrites with an explicit allow-list of `@[simp]` lemmas.
3. `omega` — decides linear `Nat` and `Int` arithmetic.
4. `@[grind =]` + `grind` — combines case splitting, congruence closure, and
   linear arithmetic automatically.
-/

namespace Ch06

/-!
## 1. `fun_cases` + `omega`: Verifying Clamped Retry Backoff
-/

@[grind =]
def clampBackoffMs (rawMs minMs maxMs : Nat) : Nat :=
  if rawMs < minMs then
    minMs
  else if maxMs < rawMs then
    maxMs
  else
    rawMs

#guard clampBackoffMs 10 50 1000 == 50
#guard clampBackoffMs 250 50 1000 == 250
#guard clampBackoffMs 5000 50 1000 == 1000

/--
`fun_cases clampBackoffMs rawMs minMs maxMs` generates the exact three control-flow
branches of `clampBackoffMs`, attaching the branch conditions as hypotheses so
`omega` solves all three goals immediately.
-/
theorem clampBackoffMs_in_bounds (rawMs minMs maxMs : Nat)
    (hValid : minMs ≤ maxMs) :
    minMs ≤ clampBackoffMs rawMs minMs maxMs ∧
    clampBackoffMs rawMs minMs maxMs ≤ maxMs := by
  fun_cases clampBackoffMs rawMs minMs maxMs <;> omega

/--
Because `clampBackoffMs` is marked `@[grind =]`, `grind` also proves the exact
same theorem in one tactic!
-/
theorem clampBackoffMs_in_bounds_grind (rawMs minMs maxMs : Nat)
    (hValid : minMs ≤ maxMs) :
    minMs ≤ clampBackoffMs rawMs minMs maxMs ∧
    clampBackoffMs rawMs minMs maxMs ≤ maxMs := by
  grind

/-!
## 2. Surgical `simp only` & Multi-Bucket Quota Accounting

Prior to executing an LLM call with an estimated max-token budget `est`, a
gateway moves `est` tokens from `available` to `reserved`. Once the response
stream finishes with `actual` tokens consumed, `settleQuota` moves `actual` into
`used` and returns unused reserved tokens back to `available`.
-/

structure QuotaBucket where
  used      : Nat
  reserved  : Nat
  available : Nat
  deriving Repr, DecidableEq

@[simp, grind =]
def QuotaBucket.total (q : QuotaBucket) : Nat :=
  q.used + q.reserved + q.available

@[grind =]
def reserveQuota (q : QuotaBucket) (est : Nat) : Option QuotaBucket :=
  if est ≤ q.available then
    some { q with reserved := q.reserved + est
                  available := q.available - est }
  else
    none

/--
Worked example: `reserveQuota` preserves `QuotaBucket.total` whenever it succeeds.
Notice `simp only [QuotaBucket.total]` unfolds ONLY `QuotaBucket.total` without
touching unrelated definitions.
-/
theorem reserveQuota_preserves_total (q q' : QuotaBucket) (est : Nat)
    (h : reserveQuota q est = some q') :
    q'.total = q.total := by
  revert h
  fun_cases reserveQuota q est
  · intro h
    injection h with hEq
    rw [← hEq]
    simp only [QuotaBucket.total]
    omega
  · intro h
    nomatch h

/-!
## Exercises (Solved)
-/

@[grind =]
def nextBackoffMs (prevMs minMs maxMs : Nat) : Nat :=
  clampBackoffMs (prevMs * 2 + 10) minMs maxMs

/--
Exercise 6.1: Prove that exponential-jitter backoff `nextBackoffMs` always stays
within `[minMs, maxMs]` whenever `minMs ≤ maxMs`.
-/
theorem nextBackoffMs_bounded (prevMs minMs maxMs : Nat)
    (hValid : minMs ≤ maxMs) :
    minMs ≤ nextBackoffMs prevMs minMs maxMs ∧
    nextBackoffMs prevMs minMs maxMs ≤ maxMs := by
  unfold nextBackoffMs
  exact clampBackoffMs_in_bounds (prevMs * 2 + 10) minMs maxMs hValid

/--
Settlement rule when an in-flight call finishes:
- If `actual ≤ q.reserved`, add `actual` to `used`, refund `q.reserved - actual`
  to `available`, and reset `reserved` to `0`.
- If `q.reserved < actual` (stream overran estimate), move the entire `q.reserved`
  into `used`, leave `available` unchanged, and reset `reserved` to `0`.
-/
@[grind =]
def settleQuota (q : QuotaBucket) (actual : Nat) : QuotaBucket :=
  if actual ≤ q.reserved then
    { used      := q.used + actual
      reserved  := 0
      available := q.available + (q.reserved - actual) }
  else
    { used      := q.used + q.reserved
      reserved  := 0
      available := q.available }

#guard settleQuota { used := 100, reserved := 50, available := 850 } 30 ==
  { used := 130, reserved := 0, available := 870 }

/--
Exercise 6.2: Prove using `fun_cases`, `simp only [QuotaBucket.total]`, and `omega`
(or `grind`) that `settleQuota` conserves `QuotaBucket.total` on *both* branches!
-/
theorem settleQuota_preserves_total (q : QuotaBucket) (actual : Nat) :
    (settleQuota q actual).total = q.total := by
  fun_cases settleQuota q actual <;> simp only [QuotaBucket.total] <;> omega

/-!
## 3. Multi-Tier Rate Limiting with `@[grind =]`
-/

inductive PlanTier where
  | free
  | pro
  | dedicated
  deriving Repr, DecidableEq

@[grind =]
def tierLimitRps (tier : PlanTier) : Nat :=
  match tier with
  | .free      => 20
  | .pro       => 500
  | .dedicated => 10000

@[grind =]
def effectiveRps (tier : PlanTier) (requestedRps clusterCeiling : Nat) : Nat :=
  let planCapped :=
    if requestedRps ≤ tierLimitRps tier then requestedRps else tierLimitRps tier
  if planCapped ≤ clusterCeiling then planCapped else clusterCeiling

#guard effectiveRps .free 100 5000 == 20
#guard effectiveRps .pro 300 250 == 250

/--
Exercise 6.3: Use `grind` (or `fun_cases` + `omega`) to prove that across all
`PlanTier` values, `requestedRps`, and `clusterCeiling`, `effectiveRps` never
exceeds `clusterCeiling`, never exceeds `requestedRps`, and never exceeds the
plan's `tierLimitRps`.
-/
theorem effectiveRps_respects_all_caps
    (tier : PlanTier) (requestedRps clusterCeiling : Nat) :
    effectiveRps tier requestedRps clusterCeiling ≤ clusterCeiling ∧
    effectiveRps tier requestedRps clusterCeiling ≤ requestedRps ∧
    effectiveRps tier requestedRps clusterCeiling ≤ tierLimitRps tier := by
  grind

/-- info: 'Ch06.settleQuota_preserves_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms settleQuota_preserves_total

/-- info: 'Ch06.effectiveRps_respects_all_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms effectiveRps_respects_all_caps

end Ch06
