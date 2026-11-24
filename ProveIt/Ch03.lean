set_option autoImplicit false

/-!
# Chapter 3: Compile-Time Exhaustion & Boolean Reflection

Authorization systems face an architectural tension:
1. Runtime request handlers want a fast `Bool` function (`checkAccess`).
2. Security compliance auditors want an explicit `Prop` rule table (`Allowed`)
   where every granted permission traces back to a named rule.

When those two artifacts live separately, shortcut wildcards in code silently
grant unintended privileges. Inspect `checkAccessBuggy` below:
-/

namespace Ch03

inductive Role where
  | viewer
  | deployer
  | auditor
  | admin
  deriving Repr, DecidableEq

inductive Action where
  | readMetrics
  | deployService
  | readAuditLog
  | deleteCluster
  deriving Repr, DecidableEq

def checkAccessBuggy (role : Role) (action : Action) : Bool :=
  match role, action with
  | _,         .readMetrics   => true
  | .deployer, .deployService => true
  | .auditor,  _              => action != .deleteCluster
  | .admin,    _              => true
  | _,         _              => false

-- PREDICT: The author intended `.auditor` to read metrics and audit logs.
-- What does `checkAccessBuggy .auditor .deployService` evaluate to?
#guard checkAccessBuggy .auditor .deployService == true

/-!
## Declarative Policy Specification (`Prop`) vs. Executable Evaluator (`Bool`)

An `inductive` predicate landing in `Prop` acts as an allow-list of inference
rules: `Allowed role action` holds if and only if one of its four constructors
builds evidence for `(role, action)`.
-/

inductive Allowed : Role → Action → Prop where
  | allReadMetrics (r : Role) : Allowed r .readMetrics
  | deployerDeploy            : Allowed .deployer .deployService
  | auditorReadAudit          : Allowed .auditor .readAuditLog
  | adminAll (a : Action)     : Allowed .admin a

/--
The repaired executable policy evaluator (`Bool`).
-/
def checkAccess (role : Role) (action : Action) : Bool :=
  match role, action with
  | _,         .readMetrics   => true
  | .deployer, .deployService => true
  | .auditor,  .readAuditLog  => true
  | .admin,    _              => true
  | _,         _              => false

-- PREDICT: Does `checkAccess .auditor .deployService` now return `false`?
#guard checkAccess .auditor .deployService == false
#guard checkAccess .auditor .readAuditLog == true
#guard checkAccess .deployer .deployService == true
#guard checkAccess .viewer .readMetrics == true

/-!
## Compile-Time Exhaustion & Boolean Reflection

For finite types (`Role` has 4 values, `Action` has 4 values), Lean's `decide`
tactic can verify decidable propositions across every case at compile time.

To tie our `Bool` fast path permanently to our `Prop` specification, we prove
**Boolean Reflection**: `checkAccess role action = true ↔ Allowed role action`.

Here is the completeness direction (`Allowed → checkAccess = true`), worked out:
-/
theorem allowed_implies_checkAccess (role : Role) (action : Action)
    (h : Allowed role action) :
    checkAccess role action = true := by
  cases h with
  | allReadMetrics => cases role <;> rfl
  | deployerDeploy => rfl
  | auditorReadAudit => rfl
  | adminAll => cases action <;> rfl

/-!
## Exercises
-/

/--
Exercise 3.1 (Least Privilege for `.viewer`):
Prove that if `checkAccess .viewer action = true`, then `action = .readMetrics`.
(Hint: `revert h` puts `h` back into the goal as an implication; then
`cases action <;> decide` checks all four actions at compile time!)
-/
theorem viewer_least_privilege (action : Action)
    (h : checkAccess .viewer action = true) :
    action = .readMetrics := by
  sorry

/--
Exercise 3.2a (Soundness):
Prove that whenever `checkAccess role action = true`, `Allowed role action` holds.
-/
theorem checkAccess_implies_allowed (role : Role) (action : Action)
    (h : checkAccess role action = true) :
    Allowed role action := by
  sorry

/--
Exercise 3.2b (Full Boolean Reflection):
Combine `checkAccess_implies_allowed` and `allowed_implies_checkAccess` to prove
the bidirectional equivalence (`↔`).
-/
theorem checkAccess_iff_allowed (role : Role) (action : Action) :
    checkAccess role action = true ↔ Allowed role action := by
  sorry

/--
Once `checkAccess_iff_allowed` is proven, `decidable_of_iff` gives `Allowed`
a `Decidable` instance so `decide` can evaluate `Allowed` propositions directly!
-/
instance instDecidableAllowed (role : Role) (action : Action) :
    Decidable (Allowed role action) :=
  decidable_of_iff (checkAccess role action = true) (checkAccess_iff_allowed role action)

-- Once Exercises 3.2a & 3.2b are complete, prove this check with `decide`:
example : Allowed .auditor .readAuditLog := by sorry

/--
Exercise 3.3 (Separation of Duty):
Prove that no non-admin role may simultaneously deploy services AND read audit
logs.
-/
theorem separation_of_duty (role : Role)
    (hNonAdmin : role ≠ .admin) :
    ¬ (Allowed role .deployService ∧ Allowed role .readAuditLog) := by
  sorry

end Ch03
