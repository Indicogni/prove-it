set_option autoImplicit false

/-!
# Chapter 3: Compile-Time Exhaustion & Boolean Reflection (Reference Solutions)

Authorization engines face a persistent tension:
1. Runtime request handlers want a fast `Bool` function (`checkAccess`).
2. Security auditors want a declarative `Prop` specification (`Allowed`) where
   every grant traces back to an explicit policy rule.

When those two representations live in separate documents, wildcard shortcuts in
code silently grant unintended privileges.
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

/--
A buggy fast-path evaluator: someone wrote a negative check (`action != .deleteCluster`)
for `.auditor` instead of enumerating allowed actions, accidentally granting
`.auditor` permission to `.deployService`!
-/
def checkAccessBuggy (role : Role) (action : Action) : Bool :=
  match role, action with
  | _,         .readMetrics => true
  | .deployer, .deployService => true
  | .auditor,  _ => action != .deleteCluster
  | .admin,    _ => true
  | _,         _ => false

-- Privilege escalation caught on concrete inputs:
#guard checkAccessBuggy .auditor .deployService == true

/-!
## Declarative Policy Specification (`Prop`)

Each constructor of `Allowed` is an explicit authorization rule—nothing is
permitted unless a constructor derives it.
-/

inductive Allowed : Role → Action → Prop where
  | allReadMetrics (r : Role) : Allowed r .readMetrics
  | deployerDeploy            : Allowed .deployer .deployService
  | auditorReadAudit          : Allowed .auditor .readAuditLog
  | adminAll (a : Action)     : Allowed .admin a

/--
The repaired executable policy checker (`Bool`).
-/
def checkAccess (role : Role) (action : Action) : Bool :=
  match role, action with
  | _,         .readMetrics   => true
  | .deployer, .deployService => true
  | .auditor,  .readAuditLog  => true
  | .admin,    _              => true
  | _,         _              => false

#guard checkAccess .auditor .deployService == false
#guard checkAccess .auditor .readAuditLog == true
#guard checkAccess .deployer .deployService == true
#guard checkAccess .viewer .readMetrics == true

/-!
## Bridging `Prop` and `Bool`: Boolean Reflection

Direction 1 (Completeness): Every action permitted by `Allowed` evaluates to
`true` in `checkAccess`. Notice how `cases h` splits over the four policy rules,
and `cases r` / `cases a` exhausts the finite types at compile time.
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
## Exercises (Solved)
-/

/--
Exercise 3.1 (Least Privilege for `.viewer`):
Prove by finite exhaustion (`revert h; cases action <;> decide`) that if
`checkAccess .viewer action = true`, the action must be `.readMetrics`.
-/
theorem viewer_least_privilege (action : Action)
    (h : checkAccess .viewer action = true) :
    action = .readMetrics := by
  revert h
  cases action <;> decide

/--
Exercise 3.2a (Soundness):
Prove that whenever `checkAccess role action = true`, there is a valid
derivation of `Allowed role action`.
Notice how pattern matching on `(role, action, h)` mirrors `checkAccess` in 4
lines while Lean automatically discharges every `false = true` pair!
-/
theorem checkAccess_implies_allowed (role : Role) (action : Action)
    (h : checkAccess role action = true) :
    Allowed role action :=
  match role, action, h with
  | r,         .readMetrics,   _ => .allReadMetrics r
  | .deployer, .deployService, _ => .deployerDeploy
  | .auditor,  .readAuditLog,  _ => .auditorReadAudit
  | .admin,    a,              _ => .adminAll a

/--
Exercise 3.2b (Full Boolean Reflection):
Combine both directions to prove `checkAccess` and `Allowed` are equivalent
across the entire `4 × 4 = 16` authorization matrix.
-/
theorem checkAccess_iff_allowed (role : Role) (action : Action) :
    checkAccess role action = true ↔ Allowed role action :=
  ⟨checkAccess_implies_allowed role action, allowed_implies_checkAccess role action⟩

/--
Once Boolean Reflection is proven, Lean's `decidable_of_iff` equips the
declarative `Prop` predicate `Allowed` with a compile-time decision procedure!
-/
instance instDecidableAllowed (role : Role) (action : Action) :
    Decidable (Allowed role action) :=
  decidable_of_iff (checkAccess role action = true) (checkAccess_iff_allowed role action)

#guard decide (Allowed .auditor .readAuditLog) == true
#guard decide (Allowed .auditor .deployService) == false

/--
Exercise 3.3 (Separation of Duty):
Prove that no non-admin role may simultaneously deploy services AND read audit
logs. With `instDecidableAllowed` registered above, finite case splitting +
`decide` discharges every role automatically!
-/
theorem separation_of_duty (role : Role)
    (hNonAdmin : role ≠ .admin) :
    ¬ (Allowed role .deployService ∧ Allowed role .readAuditLog) := by
  revert hNonAdmin
  cases role <;> decide

/-- info: 'Ch03.checkAccess_iff_allowed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkAccess_iff_allowed

/-- info: 'Ch03.separation_of_duty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms separation_of_duty

end Ch03
