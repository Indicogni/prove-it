/-
  Capstone 1 — CedarLite (Model Solution)
  AWS Cedar-inspired Cloud Authorization Engine & Verified Policy Optimizer
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

/-- Check whether an entity satisfies a header `Scope`. -/
def matchesScope (s : Scope) (e : Entity) : Bool :=
  match s with
  | .any => true
  | .eq target => e.id == target
  | .inGroup grp => e.groups.contains grp

/-- Check whether a request action satisfies an `ActionScope`. -/
def matchesAction (s : ActionScope) (act : String) : Bool :=
  match s with
  | .any => true
  | .eq target => act == target
  | .oneOf targets => targets.contains act

/-- Evaluate a `ValueExpr` against a `Request`. -/
def evalValue (ve : ValueExpr) (req : Request) : Option AttrVal :=
  match ve with
  | .lit v => some v
  | .principalId => some (.str req.principal.id)
  | .resourceId => some (.str req.resource.id)
  | .principalAttr k => lookupAttr req.principal.attrs k
  | .resourceAttr k => lookupAttr req.resource.attrs k
  | .contextAttr k => lookupAttr req.context k

/-- Evaluate a `Cond` against a `Request`. Missing attributes fail closed (`false`). -/
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

/-- Check whether all scopes and conditions of `p` match `req`. -/
def Policy.matches (p : Policy) (req : Request) : Bool :=
  matchesScope p.principalScope req.principal &&
  matchesAction p.actionScope req.action &&
  matchesScope p.resourceScope req.resource &&
  evalCond p.condition req

/-- Predicate testing whether `p` is a matching policy of the given `Effect`. -/
def matchesWithEffect (eff : Effect) (req : Request) (p : Policy) : Bool :=
  decide (p.effect = eff) && p.matches req

/--
  Authorize `req` under `policies`:
  1. If any matching `forbid` policy exists, return `.deny` (Explicit-Forbid Wins).
  2. Otherwise, if any matching `permit` policy exists, return `.allow`.
  3. Otherwise, return `.deny` (Default-Deny).
-/
def authorize (policies : List Policy) (req : Request) : Decision :=
  if policies.any (matchesWithEffect .forbid req) then
    .deny
  else if policies.any (matchesWithEffect .permit req) then
    .allow
  else
    .deny

/-! ## 2. Policy Optimizer -/

/-- Smart constructor for negation: folds constants and double negation. -/
def mkNot : Cond → Cond
  | .always => .never
  | .never => .always
  | .not c => c
  | c => .not c

/-- Smart constructor for conjunction: short-circuits `.never` and absorbs `.always`. -/
def mkAnd : Cond → Cond → Cond
  | .never, _ => .never
  | _, .never => .never
  | .always, r => r
  | l, .always => l
  | l, r => .and l r

/-- Smart constructor for disjunction: short-circuits `.always` and absorbs `.never`. -/
def mkOr : Cond → Cond → Cond
  | .always, _ => .always
  | _, .always => .always
  | .never, r => r
  | l, .never => l
  | l, r => .or l r

/-- Constant-fold and algebraically simplify a `Cond`. -/
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

/-- Simplify the condition inside a single policy. -/
def optimizePolicy (p : Policy) : Policy :=
  { p with condition := optimizeCond p.condition }

/-- Detect syntactically unsatisfiable policies that can never match any request. -/
def isDeadPolicy (p : Policy) : Bool :=
  decide (p.condition = .never) || decide (p.actionScope = .oneOf [])

/-- Deduplicate an exact list of policies using decidable equality (`∈`). -/
def dedupPolicies : List Policy → List Policy
  | [] => []
  | p :: rest =>
      let rest' := dedupPolicies rest
      if decide (p ∈ rest') then rest' else p :: rest'

/-- Full policy-pack optimization pipeline: simplify conditions, drop dead rules, deduplicate. -/
def optimizePolicies (policies : List Policy) : List Policy :=
  dedupPolicies ((policies.map optimizePolicy).filter (fun p => !isDeadPolicy p))

/-! ## 3. Core Security & Equivalence Proofs -/

/-- **Default-Deny (Empty Pack)**: An empty policy list always denies every request. -/
theorem default_deny_empty (req : Request) :
    authorize [] req = .deny := by
  rfl

/-- Helper: `List.any` is false when every element maps to `false`. -/
theorem any_eq_false_of_forall {α : Type} (xs : List α) (f : α → Bool)
    (h : ∀ x ∈ xs, f x = false) :
    xs.any f = false := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff]
    exact ⟨h x (.head rest), ih (fun y hy => h y (.tail x hy))⟩

/-- **Default-Deny (No Matching Permit)**: Without a matching permit, access is always denied. -/
theorem default_deny_no_permit (policies : List Policy) (req : Request)
    (hNoPermit : ∀ p ∈ policies, p.effect = .permit → p.matches req = false) :
    authorize policies req = .deny := by
  unfold authorize
  split
  · rfl
  · have hAnyFalse : policies.any (matchesWithEffect .permit req) = false := by
      apply any_eq_false_of_forall
      intro p hp
      unfold matchesWithEffect
      by_cases hEff : p.effect = .permit
      · simp [hEff, hNoPermit p hp hEff]
      · simp [hEff]
    simp [hAnyFalse]

/-- Helper: `List.any` is true when a witness element satisfies the predicate. -/
theorem any_eq_true_of_mem {α : Type} (xs : List α) (f : α → Bool) (x : α)
    (hMem : x ∈ xs) (hx : f x = true) :
    xs.any f = true := by
  induction xs with
  | nil => cases hMem
  | cons hd tl ih =>
    simp only [List.any_cons, Bool.or_eq_true]
    cases hMem with
    | head => exact Or.inl hx
    | tail _ hSub => exact Or.inr (ih hSub)

/--
  **Explicit-Forbid Always Wins (`forbidOverridesPermit`)**:
  If *any* policy in `policies` has effect `.forbid` and matches `req`,
  `authorize` returns `.deny` regardless of any matching `.permit` policies.
-/
theorem forbidOverridesPermit (policies : List Policy) (req : Request) (p : Policy)
    (hMem : p ∈ policies) (hEff : p.effect = .forbid) (hMatch : p.matches req = true) :
    authorize policies req = .deny := by
  unfold authorize
  have hForbid : policies.any (matchesWithEffect .forbid req) = true := by
    apply any_eq_true_of_mem policies _ p hMem
    simp [matchesWithEffect, hEff, hMatch]
  simp [hForbid]

/-- Adding more policies can never override an existing matching `forbid`. -/
theorem forbid_monotonic (ps₁ ps₂ : List Policy) (req : Request) (p : Policy)
    (hMem : p ∈ ps₁) (hEff : p.effect = .forbid) (hMatch : p.matches req = true) :
    authorize (ps₁ ++ ps₂) req = .deny := by
  exact forbidOverridesPermit (ps₁ ++ ps₂) req p (List.mem_append_left ps₂ hMem) hEff hMatch

/-- Characterization of `List.any` via existential membership. -/
theorem any_eq_true_iff {α : Type} (xs : List α) (f : α → Bool) :
    xs.any f = true ↔ ∃ x ∈ xs, f x = true := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.any_cons, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · intro h
      rcases h with hHd | ⟨x, hMem, hx⟩
      · exact ⟨hd, Or.inl rfl, hHd⟩
      · exact ⟨x, Or.inr hMem, hx⟩
    · rintro ⟨x, rfl | hMem, hx⟩
      · exact Or.inl hx
      · exact Or.inr ⟨x, hMem, hx⟩

/-- Two lists with identical element membership produce identical `List.any` results. -/
theorem any_congr_mem {α : Type} (xs ys : List α) (f : α → Bool)
    (hMem : ∀ x, x ∈ xs ↔ x ∈ ys) :
    xs.any f = ys.any f := by
  apply Bool.eq_iff_iff.mpr
  rw [any_eq_true_iff, any_eq_true_iff]
  constructor
  · rintro ⟨x, hx, hf⟩
    exact ⟨x, (hMem x).mp hx, hf⟩
  · rintro ⟨x, hy, hf⟩
    exact ⟨x, (hMem x).mpr hy, hf⟩

/-- Extensionality of `authorize` with respect to policy membership. -/
theorem authorize_congr_mem (ps₁ ps₂ : List Policy) (req : Request)
    (hMem : ∀ p, p ∈ ps₁ ↔ p ∈ ps₂) :
    authorize ps₁ req = authorize ps₂ req := by
  unfold authorize
  rw [any_congr_mem ps₁ ps₂ (matchesWithEffect .forbid req) hMem]
  rw [any_congr_mem ps₁ ps₂ (matchesWithEffect .permit req) hMem]

/--
  **Order-Independence (Permutation Invariance)**:
  Reordering a policy pack never alters any authorization decision.
-/
theorem authorize_perm (ps₁ ps₂ : List Policy) (req : Request)
    (hPerm : ps₁.Perm ps₂) :
    authorize ps₁ req = authorize ps₂ req := by
  exact authorize_congr_mem ps₁ ps₂ req (fun p => hPerm.mem_iff)

/-- Swapping two policy packs concatenated together preserves all decisions. -/
theorem authorize_append_comm (ps₁ ps₂ : List Policy) (req : Request) :
    authorize (ps₁ ++ ps₂) req = authorize (ps₂ ++ ps₁) req := by
  apply authorize_congr_mem
  intro p
  simp [List.mem_append, Or.comm]

/-- Membership preservation for `dedupPolicies`. -/
theorem mem_dedupPolicies (ps : List Policy) (q : Policy) :
    q ∈ dedupPolicies ps ↔ q ∈ ps := by
  induction ps with
  | nil => simp [dedupPolicies]
  | cons p rest ih =>
    simp only [dedupPolicies]
    by_cases hp : p ∈ dedupPolicies rest
    · simp only [hp, decide_true, ↓reduceIte, ih, List.mem_cons]
      constructor
      · intro hq; exact Or.inr hq
      · rintro (rfl | hq)
        · exact ih.mp hp
        · exact hq
    · simp only [hp, decide_false, Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih]

/-- **Deduplication Invariance**: Removing duplicate policies preserves authorization. -/
theorem authorize_dedup (ps : List Policy) (req : Request) :
    authorize (dedupPolicies ps) req = authorize ps req := by
  exact authorize_congr_mem (dedupPolicies ps) ps req (mem_dedupPolicies ps)

/-- Soundness of smart negation `mkNot`. -/
theorem mkNot_sound (c : Cond) (req : Request) :
    evalCond (mkNot c) req = !(evalCond c req) := by
  cases c <;> simp [mkNot, evalCond]

/-- Soundness of smart conjunction `mkAnd`. -/
theorem mkAnd_sound (c1 c2 : Cond) (req : Request) :
    evalCond (mkAnd c1 c2) req = (evalCond c1 req && evalCond c2 req) := by
  cases c1 <;> cases c2 <;> simp [mkAnd, evalCond]

/-- Soundness of smart disjunction `mkOr`. -/
theorem mkOr_sound (c1 c2 : Cond) (req : Request) :
    evalCond (mkOr c1 c2) req = (evalCond c1 req || evalCond c2 req) := by
  cases c1 <;> cases c2 <;> simp [mkOr, evalCond]

/-- Soundness of condition constant-folding and algebraic simplification. -/
theorem optimizeCond_sound (c : Cond) (req : Request) :
    evalCond (optimizeCond c) req = evalCond c req := by
  induction c with
  | always => rfl
  | never => rfl
  | attrEq lhs rhs =>
    cases lhs <;> cases rhs <;> try rfl
    rename_i v1 v2
    simp only [optimizeCond, evalCond, evalValue]
    by_cases h : v1 = v2 <;> simp [h, evalCond]
  | attrIntLe lhs rhs =>
    cases lhs with
    | lit v1 =>
      cases v1 <;> cases rhs <;> try rfl
      rename_i n1 v2
      cases v2 <;> try rfl
      rename_i n2
      simp only [optimizeCond, evalCond, evalValue]
      by_cases h : n1 ≤ n2 <;> simp [h, evalCond]
    | _ => rfl
  | hasContextAttr k => rfl
  | not inner ih =>
    simp [optimizeCond, mkNot_sound, evalCond, ih]
  | and c1 c2 ih1 ih2 =>
    simp [optimizeCond, mkAnd_sound, evalCond, ih1, ih2]
  | or c1 c2 ih1 ih2 =>
    simp [optimizeCond, mkOr_sound, evalCond, ih1, ih2]

/-- Policy optimization preserves per-policy matching and effect. -/
theorem optimizePolicy_matches (p : Policy) (req : Request) :
    (optimizePolicy p).matches req = p.matches req := by
  simp [optimizePolicy, Policy.matches, optimizeCond_sound]

theorem matchesWithEffect_optimizePolicy (eff : Effect) (req : Request) (p : Policy) :
    matchesWithEffect eff req (optimizePolicy p) = matchesWithEffect eff req p := by
  unfold matchesWithEffect
  rw [optimizePolicy_matches]
  rfl

/-- Dead policies never match any request. -/
theorem isDeadPolicy_matches_false (p : Policy) (req : Request)
    (hDead : isDeadPolicy p = true) :
    p.matches req = false := by
  unfold isDeadPolicy at hDead
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hDead
  rcases hDead with hNever | hEmptyActs
  · simp [Policy.matches, hNever, evalCond]
  · simp [Policy.matches, hEmptyActs, matchesAction]

/-- Filtering out dead policies preserves `List.any (matchesWithEffect eff req)`. -/
theorem any_filter_not_dead (ps : List Policy) (eff : Effect) (req : Request) :
    (ps.filter (fun p => !isDeadPolicy p)).any (matchesWithEffect eff req) =
    ps.any (matchesWithEffect eff req) := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.filter_cons, List.any_cons]
    by_cases hDead : isDeadPolicy p = true
    · have hMatchFalse : p.matches req = false := isDeadPolicy_matches_false p req hDead
      simp [hDead, matchesWithEffect, hMatchFalse, ih]
    · simp only [Bool.not_eq_true] at hDead
      simp [hDead, ih]

/-- Mapping `optimizePolicy` preserves `List.any (matchesWithEffect eff req)`. -/
theorem any_map_optimizePolicy (ps : List Policy) (eff : Effect) (req : Request) :
    (ps.map optimizePolicy).any (matchesWithEffect eff req) =
    ps.any (matchesWithEffect eff req) := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    simp [List.map_cons, List.any_cons, matchesWithEffect_optimizePolicy, ih]

/--
  **Policy Optimizer Equivalence (`optimizePolicies_sound`)**:
  Running condition constant-folding, dead-policy elimination, and deduplication
  produces the exact same authorization decision on every possible request.
-/
theorem optimizePolicies_sound (policies : List Policy) (req : Request) :
    authorize (optimizePolicies policies) req = authorize policies req := by
  unfold optimizePolicies
  rw [authorize_dedup]
  unfold authorize
  rw [any_filter_not_dead, any_filter_not_dead]
  rw [any_map_optimizePolicy, any_map_optimizePolicy]

/-! ## 4. Non-Vacuity Witnesses -/

/-- Sample production policy pack combining RBAC, ABAC ownership, and risk-score guardrails. -/
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

/-- Non-vacuity witness 1: A valid low-risk MFA owner request is genuinely allowed. -/
theorem non_vacuous_allow :
    ∃ req : Request, authorize samplePolicies req = .allow := by
  refine ⟨{
    principal := { id := "alice", groups := ["eng"] }
    action := "write"
    resource := { id := "doc-42", attrs := [("owner", .str "alice")] }
    context := [("mfa", .bool true), ("riskScore", .int 10)]
  }, ?_⟩
  decide

/-- Non-vacuity witness 2: Even an admin is denied when the explicit high-risk forbid fires. -/
theorem non_vacuous_forbid_wins :
    ∃ req : Request,
      samplePolicies.any (matchesWithEffect .permit req) = true ∧
      authorize samplePolicies req = .deny := by
  refine ⟨{
    principal := { id := "root-admin", groups := ["admins"] }
    action := "delete"
    resource := { id := "prod-db" }
    context := [("riskScore", .int 95)]
  }, ?_⟩
  decide

end CedarLite
