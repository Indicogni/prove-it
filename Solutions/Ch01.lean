set_option autoImplicit false

/-!
# Chapter 1: The Silent Truncation Bug (Reference Solutions)

An LLM API gateway tracks each tenant's remaining token quota as a `Nat`
(non-negative integer: `0, 1, 2, ...`). During an incident review, an engineer
discovers that tenants with `0` tokens left are still sending `500`-token
completion requests without ever getting rate-limited.

Here is the 4-line function from the gateway:
-/

namespace Ch01

def chargeQuotaBuggy (remaining cost : Nat) : Option Nat :=
  let next := remaining - cost
  if next ≥ 0 then some next else none

-- Counterexample witness: an empty quota (0) approves a 500-token request!
#guard chargeQuotaBuggy 0 500 == some 0

-- Why? In Lean (and many verification languages), `Nat` is closed under
-- subtraction so every function stays total (never panics or throws).
-- Subtracting a larger `Nat` from a smaller `Nat` truncates at `0`:
#guard (0 : Nat) - 1 == 0
#guard (10 : Nat) - 25 == 0

/--
A concrete theorem witnessing the bug: `rfl` ("reflexivity") asks Lean's
kernel to evaluate both sides and confirm they normalize to the same value.
-/
theorem chargeQuotaBuggy_allows_when_empty :
    chargeQuotaBuggy 0 500 = some 0 := by
  rfl

/-!
## Two Principled Fixes

### Fix 1: Guard before subtracting (`Option Nat`)
Check `cost ≤ remaining` *before* subtracting on `Nat`. Now underflow is
impossible on the `then` branch, and rejection is explicit via `none`.
-/

@[grind =]
def chargeQuotaOpt (remaining cost : Nat) : Option Nat :=
  if cost ≤ remaining then
    some (remaining - cost)
  else
    none

#guard chargeQuotaOpt 0 500 == none
#guard chargeQuotaOpt 1000 500 == some 500
#guard chargeQuotaOpt 500 500 == some 0

/--
Universal conservation law: across *all* infinite pairs `(remaining, cost)`,
whenever `chargeQuotaOpt` approves a request and returns `some next`,
the new quota plus the request cost equals the original quota.
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
### Fix 2: Signed accounting (`Int`)
When negative balances represent intentional post-paid overdrafts, model
balances as `Int` rather than `Nat`.
-/

def balanceAfter (remaining cost : Int) : Int :=
  remaining - cost

#guard balanceAfter 0 500 == -500
#guard balanceAfter 300 120 == 180

/-!
## Exercises (Solved)
-/

/--
Exercise 1.1: Prove that an exhausted quota (`0` remaining) rejects every
request with positive token cost (`0 < cost`).
-/
theorem chargeQuotaOpt_zero_rejects (cost : Nat) (hPos : 0 < cost) :
    chargeQuotaOpt 0 cost = none := by
  unfold chargeQuotaOpt
  split
  · omega
  · rfl

/--
Exercise 1.2: Prove that under signed `Int` accounting, whenever `remaining < cost`,
the resulting balance is strictly negative (`< 0`).
-/
theorem balanceAfter_negative_on_overdraft (remaining cost : Int)
    (hOver : remaining < cost) :
    balanceAfter remaining cost < 0 := by
  unfold balanceAfter
  omega

/--
Exercise 1.3a: Implement `chargeWithReserve` so a request of `cost` tokens is
approved (`some next`) if and only if deducting `cost` from `remaining` leaves
at least `reserve` tokens in the bucket. Otherwise return `none`.
-/
def chargeWithReserve (remaining cost reserve : Nat) : Option Nat :=
  if cost + reserve ≤ remaining then
    some (remaining - cost)
  else
    none

#guard chargeWithReserve 1000 700 200 == some 300
#guard chargeWithReserve 1000 850 200 == none
#guard chargeWithReserve 0 1 0 == none
#guard chargeWithReserve 200 0 200 == some 200

/--
Exercise 1.3b: Prove that whenever `chargeWithReserve` returns `some next`,
tokens are conserved (`next + cost = remaining`) AND the safety reserve is
respected (`reserve ≤ next`).
-/
theorem chargeWithReserve_sound (remaining cost reserve next : Nat)
    (h : chargeWithReserve remaining cost reserve = some next) :
    next + cost = remaining ∧ reserve ≤ next := by
  unfold chargeWithReserve at h
  split at h
  · injection h with hNext
    omega
  · nomatch h

/-- info: 'Ch01.chargeWithReserve_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chargeWithReserve_sound

end Ch01
