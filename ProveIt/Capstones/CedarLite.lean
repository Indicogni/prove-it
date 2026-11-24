/-
  Capstone 1 — CedarLite (Learner Starter)
  AWS Cedar-inspired Cloud Authorization Engine & Verified Policy Optimizer

  Read `capstones/cedar-lite/README.md` for the Socratic brief and roadmap,
  and `capstones/cedar-lite/DESIGN.md` for proof-engineering guidance.

  Your mission: replace every `sorry` below with a complete kernel-checked proof!
-/
set_option autoImplicit false

namespace CedarLite

/-- Policy effect: either grants (`permit`) or blocks (`forbid`) access. -/
inductive Effect where
  | permit
  | forbid
  deriving Repr, DecidableEq

/-- Final authorization decision returned by the engine. -/
inductive Decision where
  | allow
  | deny
  deriving Repr, DecidableEq

/-- Attribute values carried on principals, resources, and request context. -/
inductive AttrVal where
  | str (s : String)
  | int (n : Int)
  | bool (b : Bool)
  deriving Repr, DecidableEq

/-- Deterministic key-value attribute lookup. -/
def lookupAttr (attrs : List (String × AttrVal)) (key : String) : Option AttrVal :=
  match attrs with
  | [] => none
  | (k, v) :: rest => if k == key then some v else lookupAttr rest key

/-- An entity (principal or resource) with an ID, group memberships, and attributes. -/
structure Entity where
  id : String
  groups : List String := []
  attrs : List (String × AttrVal) := []
  deriving Repr, DecidableEq

/-- An incoming authorization request. -/
structure Request where
  principal : Entity
  action : String
  resource : Entity
  context : List (String × AttrVal) := []
  deriving Repr, DecidableEq

/-- Entity scope constraint in a policy header. -/
inductive Scope where
  | any
  | eq (id : String)
  | inGroup (group : String)
  deriving Repr, DecidableEq

/-- Action scope constraint in a policy header. -/
inductive ActionScope where
  | any
  | eq (act : String)
  | oneOf (acts : List String)
  deriving Repr, DecidableEq

/-- Value expressions used inside policy `when` conditions. -/
inductive ValueExpr where
  | lit (v : AttrVal)
  | principalId
  | resourceId
  | principalAttr (key : String)
  | resourceAttr (key : String)
  | contextAttr (key : String)
  deriving Repr, DecidableEq

/-- Boolean attribute condition (`when` clause) on a policy. -/
inductive Cond where
  | always
  | never
  | attrEq (lhs rhs : ValueExpr)
  | attrIntLe (lhs rhs : ValueExpr)
  | hasContextAttr (key : String)
  | not (c : Cond)
  | and (c1 c2 : Cond)
  | or (c1 c2 : Cond)
  deriving Repr, DecidableEq

/-- A complete CedarLite policy rule. -/
structure Policy where
  id : String
  effect : Effect
  principalScope : Scope := .any
  actionScope : ActionScope := .any
  resourceScope : Scope := .any
  condition : Cond := .always
  deriving Repr, DecidableEq

/-! ## 1. Reference Evaluator -/

def matchesScope (s : Scope) (e : Entity) : Bool :=
  match s with
  | .any => true
  | .eq target => e.id == target
  | .inGroup grp => e.groups.contains grp

def matchesAction (s : ActionScope) (act : String) : Bool :=
  match s with
  | .any => true
  | .eq target => act == target
  | .oneOf targets => targets.contains act

def evalValue (ve : ValueExpr) (req : Request) : Option AttrVal :=
  match ve with
  | .lit v => some v
  | .principalId => some (.str req.principal.id)
  | .resourceId => some (.str req.resource.id)
  | .principalAttr k => lookupAttr req.principal.attrs k
  | .resourceAttr k => lookupAttr req.resource.attrs k
  | .contextAttr k => lookupAttr req.context k

def evalCond (c : Cond) (req : Request) : Bool :=
  match c with
  | .always => true
  | .never => false
  | .attrEq lhs rhs =>
      match evalValue lhs req, evalValue rhs req with
      | some v1, some v2 => decide (v1 = v2)
      | _, _ => false
  | .attrIntLe lhs rhs =>
      match evalValue lhs req, evalValue rhs req with
      | some (.int n1), some (.int n2) => decide (n1 ≤ n2)
      | _, _ => false
  | .hasContextAttr k => (lookupAttr req.context k).isSome
  | .not inner => !(evalCond inner req)
  | .and c1 c2 => evalCond c1 req && evalCond c2 req
  | .or c1 c2 => evalCond c1 req || evalCond c2 req

def Policy.matches (p : Policy) (req : Request) : Bool :=
  matchesScope p.principalScope req.principal &&
  matchesAction p.actionScope req.action &&
  matchesScope p.resourceScope req.resource &&
  evalCond p.condition req

def matchesWithEffect (eff : Effect) (req : Request) (p : Policy) : Bool :=
  decide (p.effect = eff) && p.matches req

def authorize (policies : List Policy) (req : Request) : Decision :=
  if policies.any (matchesWithEffect .forbid req) then
    .deny
  else if policies.any (matchesWithEffect .permit req) then
    .allow
  else
    .deny

/-! ## 2. Policy Optimizer -/

def mkNot : Cond → Cond
  | .always => .never
  | .never => .always
  | .not c => c
  | c => .not c

def mkAnd : Cond → Cond → Cond
  | .never, _ => .never
  | _, .never => .never
  | .always, r => r
  | l, .always => l
  | l, r => .and l r

def mkOr : Cond → Cond → Cond
  | .always, _ => .always
  | _, .always => .always
  | .never, r => r
  | l, .never => l
  | l, r => .or l r

def optimizeCond : Cond → Cond
  | .always => .always
  | .never => .never
  | .attrEq lhs rhs =>
      match lhs, rhs with
      | .lit v1, .lit v2 => if decide (v1 = v2) then .always else .never
      | _, _ => .attrEq lhs rhs
  | .attrIntLe lhs rhs =>
      match lhs, rhs with
      | .lit (.int n1), .lit (.int n2) => if decide (n1 ≤ n2) then .always else .never
      | _, _ => .attrIntLe lhs rhs
  | .hasContextAttr k => .hasContextAttr k
  | .not inner => mkNot (optimizeCond inner)
  | .and c1 c2 => mkAnd (optimizeCond c1) (optimizeCond c2)
  | .or c1 c2 => mkOr (optimizeCond c1) (optimizeCond c2)

def optimizePolicy (p : Policy) : Policy :=
  { p with condition := optimizeCond p.condition }

def isDeadPolicy (p : Policy) : Bool :=
  decide (p.condition = .never) || decide (p.actionScope = .oneOf [])

def dedupPolicies : List Policy → List Policy
  | [] => []
  | p :: rest =>
      let rest' := dedupPolicies rest
      if decide (p ∈ rest') then rest' else p :: rest'

def optimizePolicies (policies : List Policy) : List Policy :=
  dedupPolicies ((policies.map optimizePolicy).filter (fun p => !isDeadPolicy p))

/-! ## 3. Verification Milestones -/

/-- Milestone 1a: Empty policy pack always denies. -/
theorem default_deny_empty (req : Request) :
    authorize [] req = .deny := by
  rfl

/--
  Milestone 1b (**Default-Deny**):
  Prove that if no `.permit` policy in `policies` matches `req`,
  `authorize policies req = .deny`.
  *Hint*: Prove a helper `any_eq_false_of_forall` by induction on the list.
-/
theorem default_deny_no_permit (policies : List Policy) (req : Request)
    (hNoPermit : ∀ p ∈ policies, p.effect = .permit → p.matches req = false) :
    authorize policies req = .deny := by
  sorry

/--
  Milestone 2 (**Explicit-Forbid Always Wins**):
  Prove that if *any* policy `p ∈ policies` has `p.effect = .forbid` and `p.matches req = true`,
  `authorize policies req = .deny` regardless of how many `.permit` rules match.
  *Hint*: Prove a helper `any_eq_true_of_mem` showing `xs.any f = true` from a witness `x ∈ xs`.
-/
theorem forbidOverridesPermit (policies : List Policy) (req : Request) (p : Policy)
    (hMem : p ∈ policies) (hEff : p.effect = .forbid) (hMatch : p.matches req = true) :
    authorize policies req = .deny := by
  sorry

/--
  Milestone 3a (**Order-Independence under Permutations**):
  Prove that permuting a policy list never alters any authorization decision.
  *Hint*: Show `authorize` depends only on list membership (`∀ p, p ∈ ps₁ ↔ p ∈ ps₂`),
  then apply `hPerm.mem_iff`.
-/
theorem authorize_perm (ps₁ ps₂ : List Policy) (req : Request)
    (hPerm : ps₁.Perm ps₂) :
    authorize ps₁ req = authorize ps₂ req := by
  sorry

/--
  Milestone 3b (**Deduplication Invariance**):
  Prove that `dedupPolicies` preserves authorization decisions.
-/
theorem authorize_dedup (ps : List Policy) (req : Request) :
    authorize (dedupPolicies ps) req = authorize ps req := by
  sorry

/--
  Milestone 4a (**Condition Optimizer Soundness**):
  Prove that `optimizeCond` preserves `evalCond` for every request.
  *Hint*: Prove 3-line helper lemmas `mkNot_sound`, `mkAnd_sound`, `mkOr_sound` first!
-/
theorem optimizeCond_sound (c : Cond) (req : Request) :
    evalCond (optimizeCond c) req = evalCond c req := by
  sorry

/--
  Milestone 4b (**Full Policy-Pack Optimizer Equivalence**):
  Prove that simplifying conditions, pruning dead policies, and deduplicating
  preserves `authorize` across all requests.
-/
theorem optimizePolicies_sound (policies : List Policy) (req : Request) :
    authorize (optimizePolicies policies) req = authorize policies req := by
  sorry

/-! ## 4. Non-Vacuity Witnesses -/

def samplePolicies : List Policy :=
  [ { id := "owner-read-write"
      effect := .permit
      actionScope := .oneOf ["read", "write"]
      condition := .and (.attrEq .principalId (.resourceAttr "owner"))
                        (.hasContextAttr "mfa") }
  , { id := "admin-wildcard"
      effect := .permit
      principalScope := .inGroup "admins" }
  , { id := "high-risk-freeze"
      effect := .forbid
      condition := .not (.attrIntLe (.contextAttr "riskScore") (.lit (.int 50))) }
  ]

/-- Milestone 5: Exhibit a concrete request that `samplePolicies` allows (`decide`). -/
theorem non_vacuous_allow :
    ∃ req : Request, authorize samplePolicies req = .allow := by
  sorry

end CedarLite
