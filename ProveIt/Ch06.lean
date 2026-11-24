set_option autoImplicit false

/-!
# Chapter 6: Control Flow, Rewriting & Linear Arithmetic

Production systems branch constantly: retry loops clamp exponential backoff
timers, quota managers shuffle tokens across `available`, `reserved`, and `used`
buckets, and rate limiters reconcile per-tenant plan caps with global cluster
ceilings.

Writing manual `unfold` + nested `split` scripts quickly turns brittle when an
engineer reorders two `if` branches. Lean 4.36 equips you with four non-brittle
tools for control-flow verification:
1. `fun_cases` — branches along the exact control-flow paths of a function call.
2. `simp only [...]` — rewrites using an explicit allow-list of `@[simp]` lemmas.
3. `omega` — decides linear `Nat` and `Int` inequalities and equations.
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

-- PREDICT: What would `clampBackoffMs 10 500 100` return if a caller inverted
-- `minMs` and `maxMs` (`minMs = 500 > maxMs = 100`)? Why does our theorem below
-- require `hValid : minMs ≤ maxMs`?
#guard clampBackoffMs 10 50 1000 == 50
#guard clampBackoffMs 250 50 1000 == 250
#guard clampBackoffMs 5000 50 1000 == 1000

/--
`fun_cases clampBackoffMs rawMs minMs maxMs` generates three subgoals—one per
return path of `clampBackoffMs`—with the corresponding `if` conditions in scope.
`omega` then discharges all three branches.
-/
theorem clampBackoffMs_in_bounds (rawMs minMs maxMs : Nat)
    (hValid : minMs ≤ maxMs) :
    minMs ≤ clampBackoffMs rawMs minMs maxMs ∧
    clampBackoffMs rawMs minMs maxMs ≤ maxMs := by
  fun_cases clampBackoffMs rawMs minMs maxMs <;> omega

/--
Because `clampBackoffMs` carries `@[grind =]`, `grind` also proves the exact
same theorem in a single step.
-/
theorem clampBackoffMs_in_bounds_grind (rawMs minMs maxMs : Nat)
    (hValid : minMs ≤ maxMs) :
    minMs ≤ clampBackoffMs rawMs minMs maxMs ∧
    clampBackoffMs rawMs minMs maxMs ≤ maxMs := by
  grind

/-!
## 2. Surgical `simp only` & Multi-Bucket Quota Accounting
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
Worked example: `reserveQuota` conserves `QuotaBucket.total` whenever it returns
`some q'`. Notice `revert h` puts `reserveQuota q est` into the goal so
`fun_cases` rewrites it directly in each branch, and `simp only [QuotaBucket.total]`
expands ONLY `.total` without disturbing anything else.
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
## Exercises
-/

@[grind =]
def nextBackoffMs (prevMs minMs maxMs : Nat) : Nat :=
  clampBackoffMs (prevMs * 2 + 10) minMs maxMs

/--
Exercise 6.1: Prove that `nextBackoffMs` stays within `[minMs, maxMs]` whenever
`minMs ≤ maxMs`. (Try reusing `clampBackoffMs_in_bounds`, or use `grind`!)
-/
theorem nextBackoffMs_bounded (prevMs minMs maxMs : Nat)
    (hValid : minMs ≤ maxMs) :
    minMs ≤ nextBackoffMs prevMs minMs maxMs ∧
    nextBackoffMs prevMs minMs maxMs ≤ maxMs := by
  sorry

/--
Settlement rule when an in-flight call finishes:
- If `actual ≤ q.reserved`, move `actual` into `used`, refund `q.reserved - actual`
  back to `available`, and reset `reserved` to `0`.
- If `q.reserved < actual` (stream overran estimate), move all `q.reserved`
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

-- PREDICT: If `reserved = 50` and `actual = 80` (overrun!), does `settleQuota`
-- still preserve `used + reserved + available`? Check before proving Exercise 6.2!
#guard settleQuota { used := 100, reserved := 50, available := 850 } 30 ==
  { used := 130, reserved := 0, available := 870 }
#guard settleQuota { used := 100, reserved := 50, available := 850 } 80 ==
  { used := 150, reserved := 0, available := 850 }

/--
Exercise 6.2: Prove using `fun_cases settleQuota q actual`,
`simp only [QuotaBucket.total]`, and `omega` (or `grind`) that `settleQuota`
conserves `QuotaBucket.total` on both branches.
-/
theorem settleQuota_preserves_total (q : QuotaBucket) (actual : Nat) :
    (settleQuota q actual).total = q.total := by
  sorry

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
Exercise 6.3: Prove that across all `PlanTier` values, `requestedRps`, and
`clusterCeiling`, `effectiveRps` simultaneously respects the cluster ceiling,
the caller's request, and the tier limit.
-/
theorem effectiveRps_respects_all_caps
    (tier : PlanTier) (requestedRps clusterCeiling : Nat) :
    effectiveRps tier requestedRps clusterCeiling ≤ clusterCeiling ∧
    effectiveRps tier requestedRps clusterCeiling ≤ requestedRps ∧
    effectiveRps tier requestedRps clusterCeiling ≤ tierLimitRps tier := by
  sorry

end Ch06
