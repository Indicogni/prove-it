set_option autoImplicit false

/-!
# Chapter 1: The Silent Truncation Bug

An LLM API gateway tracks each tenant's remaining token quota as a `Nat`
(natural number: `0, 1, 2, ...`). During an incident review, an engineer
discovers that tenants with `0` tokens left are still sending `500`-token
completion requests without ever getting rate-limited.

Read the 4-line function from the gateway below before scrolling further:
-/

namespace Ch01

def chargeQuotaBuggy (remaining cost : Nat) : Option Nat :=
  let next := remaining - cost
  if next ≥ 0 then some next else none

-- PREDICT: What does `chargeQuotaBuggy 0 500` return?
-- Does an account with 0 tokens remaining get `none` (rejected) or `some 0`?
#guard chargeQuotaBuggy 0 500 == some 0

/-!
## Why Did `0 - 500` Equal `0`?

In Lean, every function you write is **total** by default: for every input of the
declared type, it must terminate and return a value of the output type without
throwing an exception, panicking, or wrapping around to `2^64 - 1`.

To keep `(a - b : Nat)` inside `Nat` without panicking, `Nat` uses **truncating
(saturating) subtraction**: whenever `b ≥ a`, `a - b` evaluates to `0`.
Because every `Nat` satisfies `next ≥ 0`, the `else none` branch in
`chargeQuotaBuggy` is dead code!
-/

-- PREDICT: What do `(0 : Nat) - 1` and `(10 : Nat) - 25` evaluate to?
#guard (0 : Nat) - 1 == 0
#guard (10 : Nat) - 25 == 0

/--
Your first theorem! A `theorem` states a proposition after `:` and supplies a
proof after `:= by`. The `rfl` ("reflexivity") tactic asks Lean's kernel to
compute both sides of `=` and verify they reduce to the exact same value.
-/
theorem chargeQuotaBuggy_allows_when_empty :
    chargeQuotaBuggy 0 500 = some 0 := by
  rfl

/-!
## Two Principled Fixes

### Fix 1: Check the Precondition Before Subtracting (`Option Nat`)
Compare `cost ≤ remaining` *before* subtracting on `Nat`. Now subtraction only
executes when `cost ≤ remaining`, and insufficient quota returns `none`.
-/

@[grind =]
def chargeQuotaOpt (remaining cost : Nat) : Option Nat :=
  if cost ≤ remaining then
    some (remaining - cost)
  else
    none

-- PREDICT: What does `chargeQuotaOpt` return at the boundary `remaining = cost = 500`?
#guard chargeQuotaOpt 0 500 == none
#guard chargeQuotaOpt 1000 500 == some 500
#guard chargeQuotaOpt 500 500 == some 0

/--
Unit tests check three inputs. A theorem checks *infinitely many* inputs at once.
Here we prove that whenever `chargeQuotaOpt` approves a request (`some next`),
no tokens are created or destroyed: `next + cost = remaining`.

Step through each tactic line in your Lean Infoview to watch the goal evolve:
- `unfold` opens the definition of `chargeQuotaOpt` inside hypothesis `h`.
- `split at h` branches on the `if cost ≤ remaining` condition.
- `injection` extracts `remaining - cost = next` from `some (remaining - cost) = some next`.
- `omega` solves linear arithmetic over `Nat` and `Int`.
- `nomatch h` closes the impossible `none = some next` branch.
-/
theorem chargeQuotaOpt_conserves (remaining cost next : Nat)
    (h : chargeQuotaOpt remaining cost = some next) :
    next + cost = remaining := by
  unfold chargeQuotaOpt at h
  split at h
  · injection h with hNext
    omega
  · nomatch h

/-!
### Fix 2: Signed Accounting (`Int`)
When negative balances represent intentional post-paid overdrafts rather than
impossible states, use `Int` (`..., -2, -1, 0, 1, 2, ...`) instead of `Nat`.
-/

def balanceAfter (remaining cost : Int) : Int :=
  remaining - cost

-- PREDICT: Unlike `Nat`, what does `balanceAfter 0 500` evaluate to on `Int`?
#guard balanceAfter 0 500 == -500
#guard balanceAfter 300 120 == 180

/-!
## Exercises

Replace each `sorry` below with working code or tactics so the file compiles
with zero `sorry` warnings.
-/

/--
Exercise 1.1: Prove that an exhausted quota (`0` remaining) rejects *every*
request with strictly positive token cost (`0 < cost`).
-/
theorem chargeQuotaOpt_zero_rejects (cost : Nat) (hPos : 0 < cost) :
    chargeQuotaOpt 0 cost = none := by
  sorry

/--
Exercise 1.2: Prove that under signed `Int` accounting, whenever `remaining < cost`,
the resulting balance is strictly negative (`< 0`).
-/
theorem balanceAfter_negative_on_overdraft (remaining cost : Int)
    (hOver : remaining < cost) :
    balanceAfter remaining cost < 0 := by
  sorry

/--
Exercise 1.3a: Implement `chargeWithReserve` so a request of `cost` tokens is
approved (`some next`) if and only if deducting `cost` from `remaining` leaves
at least `reserve` tokens remaining in the bucket. Otherwise return `none`.
-/
def chargeWithReserve (remaining cost reserve : Nat) : Option Nat :=
  sorry

-- Once `chargeWithReserve` is implemented, prove these boundary checks with `rfl`:
example : chargeWithReserve 1000 700 200 = some 300 := by sorry
example : chargeWithReserve 1000 850 200 = none := by sorry

/--
Exercise 1.3b: Prove that whenever `chargeWithReserve` returns `some next`,
tokens are conserved (`next + cost = remaining`) AND the safety reserve is
maintained (`reserve ≤ next`).
-/
theorem chargeWithReserve_sound (remaining cost reserve next : Nat)
    (h : chargeWithReserve remaining cost reserve = some next) :
    next + cost = remaining ∧ reserve ≤ next := by
  sorry

end Ch01
