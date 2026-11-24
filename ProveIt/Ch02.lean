set_option autoImplicit false

/-!
# Chapter 2: Illegal States & Domain Modeling

Authentication services frequently accumulate "boolean soup": records where
independent flags (`isAuthenticated`, `mfaVerified`, `isRevoked`) and nullable
fields (`Option`) allow contradictory states to exist at runtime.

Examine `RawSession` and `zombieSession` below:
-/

namespace Ch02

structure RawSession where
  isAuthenticated : Bool
  mfaVerified     : Bool
  isRevoked       : Bool
  principalId     : Option String
  sessionToken    : Option Nat
  deriving Repr, DecidableEq

def rawBearerToken (s : RawSession) : Option Nat :=
  if s.isAuthenticated && s.mfaVerified then
    s.sessionToken
  else
    none

def zombieSession : RawSession :=
  { isAuthenticated := true
    mfaVerified     := true
    isRevoked       := true
    principalId     := none
    sessionToken    := some 9001 }

-- PREDICT: `zombieSession` is revoked AND has `principalId := none`.
-- What does `rawBearerToken zombieSession` return?
#guard rawBearerToken zombieSession == some 9001

/-!
## Sum & Product Types: Making Illegal States Unrepresentable

Count the inhabitants: three `Bool` fields already create `2^3 = 8` combinations,
before even considering whether `principalId` and `sessionToken` are `some` or
`none`.

Instead of keeping independent flags synchronized by discipline:
1. Model mutually exclusive lifecycle phases with an `inductive` **sum type**.
2. Bundle fields that only exist together inside `.active` into an `ActiveGrant`
   **product type** (`structure`).

Resilient-verification tip: wrapping `.active`'s fields inside `ActiveGrant`
keeps pattern matches written `.active grant` stable even if `ActiveGrant` later
gains a `deviceId` or `ipSubnet` field.
-/

inductive RevokeReason where
  | userLogout
  | keyCompromise
  | idleTimeout
  deriving Repr, DecidableEq

structure ActiveGrant where
  principalId  : String
  sessionToken : Nat
  expiresAt    : Nat
  deriving Repr, DecidableEq

inductive SessionState where
  | anonymous
  | pendingMfa (principalId : String) (challengeId : Nat)
  | active (grant : ActiveGrant)
  | revoked (principalId : String) (reason : RevokeReason)
  deriving Repr, DecidableEq

/--
Exhaustive pattern matching: delete any arm of this `match` and Lean refuses to
compile until every constructor of `SessionState` is handled.
-/
def bearerToken (s : SessionState) (now : Nat) : Option Nat :=
  match s with
  | .anonymous        => none
  | .pendingMfa _ _   => none
  | .revoked _ _      => none
  | .active grant     =>
    if now < grant.expiresAt then
      some grant.sessionToken
    else
      none

-- PREDICT: What happens right at the expiration boundary `now = 200` when `expiresAt = 200`?
#guard bearerToken .anonymous 100 == none
#guard bearerToken (.pendingMfa "svc-billing" 42) 100 == none
#guard bearerToken (.active { principalId := "svc-billing", sessionToken := 9001, expiresAt := 200 }) 100 == some 9001
#guard bearerToken (.active { principalId := "svc-billing", sessionToken := 9001, expiresAt := 200 }) 200 == none

/--
Constructors of an `inductive` type are mathematically disjoint: `.anonymous`
can never equal `.active grant`. `nomatch` discharges impossible constructor
equalities immediately.
-/
theorem anonymous_ne_active (grant : ActiveGrant) :
    SessionState.anonymous ≠ SessionState.active grant := by
  intro h
  nomatch h

/--
No session awaiting MFA can ever produce a bearer token, for any principal ID,
challenge ID, or timestamp.
-/
theorem pendingMfa_no_token (pid : String) (cid now : Nat) :
    bearerToken (.pendingMfa pid cid) now = none := by
  rfl

/-!
## Exercises
-/

/--
Exercise 2.1: Implement `revokeSession` according to the audit specification:
- `.anonymous` remains `.anonymous` (no principal exists to record).
- `.pendingMfa pid _` transitions to `.revoked pid reason`.
- `.active grant` transitions to `.revoked grant.principalId reason`.
- `.revoked pid originalReason` preserves `originalReason` unchanged so a later
  idle timeout cannot overwrite an earlier `.keyCompromise` audit record.
-/
def revokeSession (s : SessionState) (reason : RevokeReason) : SessionState :=
  sorry

-- Once `revokeSession` is implemented, verify these three transitions with `rfl`:
example : revokeSession .anonymous .userLogout = .anonymous := by sorry
example : revokeSession (.pendingMfa "svc-api" 7) .idleTimeout = .revoked "svc-api" .idleTimeout := by sorry
example : revokeSession (.revoked "svc-api" .keyCompromise) .idleTimeout = .revoked "svc-api" .keyCompromise := by sorry

/--
Exercise 2.2: Prove that after `revokeSession`, `bearerToken` returns `none`
for *every* initial `SessionState`, `RevokeReason`, and timestamp `now`.
(Hint: `cases s` splits `s` into its four constructors; `<;>` runs the next
tactic on every resulting goal.)
-/
theorem revokeSession_clears_bearer
    (s : SessionState) (reason : RevokeReason) (now : Nat) :
    bearerToken (revokeSession s reason) now = none := by
  sorry

/--
Exercise 2.3: Prove that whenever `bearerToken s now` yields `some tok`,
the session must be `.active grant` for an unexpired `ActiveGrant` whose
`sessionToken` equals `tok`.
-/
theorem bearerToken_some_unexpired (s : SessionState) (now tok : Nat)
    (h : bearerToken s now = some tok) :
    ∃ grant : ActiveGrant,
      s = .active grant ∧ grant.sessionToken = tok ∧ now < grant.expiresAt := by
  sorry

end Ch02
