set_option autoImplicit false

/-!
# Chapter 2: Illegal States & Domain Modeling (Reference Solutions)

Production authentication services frequently accumulate "boolean soup"—records
where orthogonal flags (`isAuthenticated`, `mfaVerified`, `isRevoked`) and
nullable fields (`Option`) allow nonsensical combinations to exist at runtime.
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

/--
A "zombie" session constructible in boolean soup: marked authenticated and
MFA-verified, simultaneously marked revoked, and missing a `principalId`!
-/
def zombieSession : RawSession :=
  { isAuthenticated := true
    mfaVerified     := true
    isRevoked       := true
    principalId     := none
    sessionToken    := some 9001 }

#guard rawBearerToken zombieSession == some 9001

/-!
## Making Illegal States Unrepresentable

Instead of independent booleans and `Option` fields that must be kept in sync
by discipline, model the lifecycle phases as a **sum type** (`inductive`) and
bundle phase-specific data into a **product type** (`structure`).

Engineering note on proof resilience: grouping the `.active` payload into an
`ActiveGrant` structure means pattern matches written `.active grant` do not
break if `ActiveGrant` later gains an `ipCidr` or `deviceId` field.
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
Exhaustive pattern matching: Lean rejects this definition at compile time if any
constructor of `SessionState` is omitted.
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

#guard bearerToken .anonymous 100 == none
#guard bearerToken (.pendingMfa "svc-billing" 42) 100 == none
#guard bearerToken (.active { principalId := "svc-billing", sessionToken := 9001, expiresAt := 200 }) 100 == some 9001
#guard bearerToken (.active { principalId := "svc-billing", sessionToken := 9001, expiresAt := 200 }) 200 == none

/--
Constructors of an `inductive` type are disjoint: `.anonymous` can never equal
`.active grant`. The `nomatch` tactic discharges impossible equalities directly.
-/
theorem anonymous_ne_active (grant : ActiveGrant) :
    SessionState.anonymous ≠ SessionState.active grant := by
  intro h
  nomatch h

/--
A session awaiting MFA never yields a bearer token at any timestamp.
-/
theorem pendingMfa_no_token (pid : String) (cid now : Nat) :
    bearerToken (.pendingMfa pid cid) now = none := by
  rfl

/-!
## Exercises (Solved)
-/

/--
Exercise 2.1: Implement `revokeSession` according to the audit specification:
- `.anonymous` remains `.anonymous` (there is no principal to record).
- `.pendingMfa pid _` transitions to `.revoked pid reason`.
- `.active grant` transitions to `.revoked grant.principalId reason`.
- `.revoked pid originalReason` keeps `originalReason` unchanged so a later
  timeout cannot overwrite an earlier `.keyCompromise` audit record.
-/
def revokeSession (s : SessionState) (reason : RevokeReason) : SessionState :=
  match s with
  | .anonymous                 => .anonymous
  | .pendingMfa pid _          => .revoked pid reason
  | .active grant              => .revoked grant.principalId reason
  | .revoked pid originalReason => .revoked pid originalReason

#guard revokeSession .anonymous .userLogout == .anonymous
#guard revokeSession (.pendingMfa "svc-api" 7) .idleTimeout == .revoked "svc-api" .idleTimeout
#guard revokeSession (.revoked "svc-api" .keyCompromise) .idleTimeout == .revoked "svc-api" .keyCompromise

/--
Exercise 2.2: Prove that after `revokeSession`, `bearerToken` returns `none`
for *every* initial `SessionState`, `RevokeReason`, and timestamp `now`.
-/
theorem revokeSession_clears_bearer
    (s : SessionState) (reason : RevokeReason) (now : Nat) :
    bearerToken (revokeSession s reason) now = none := by
  cases s <;> rfl

/--
Exercise 2.3: Prove that whenever `bearerToken s now` yields `some tok`,
the session must be in the `.active` state with an unexpired `ActiveGrant`
whose `sessionToken` is `tok`.
-/
theorem bearerToken_some_unexpired (s : SessionState) (now tok : Nat)
    (h : bearerToken s now = some tok) :
    ∃ grant : ActiveGrant,
      s = .active grant ∧ grant.sessionToken = tok ∧ now < grant.expiresAt := by
  cases s with
  | anonymous => nomatch h
  | pendingMfa _ _ => nomatch h
  | revoked _ _ => nomatch h
  | active grant =>
    dsimp [bearerToken] at h
    split at h
    · injection h with hTok
      exact ⟨grant, rfl, hTok, ‹now < grant.expiresAt›⟩
    · nomatch h

/-- info: 'Ch02.revokeSession_clears_bearer' does not depend on any axioms -/
#guard_msgs in
#print axioms revokeSession_clears_bearer

/-- info: 'Ch02.bearerToken_some_unexpired' does not depend on any axioms -/
#guard_msgs in
#print axioms bearerToken_some_unexpired

end Ch02
