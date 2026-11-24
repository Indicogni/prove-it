# Capstone 1: `CedarLite` — Cloud Authorization Engine & Policy Optimizer

## 1. Engineering Problem

Cloud IAM and authorization engines (inspired by AWS Cedar) sit on the critical security path of every API call. Two bugs repeatedly cause production incidents in hand-rolled authorization engines:

1. **Order-Dependent Evaluation Bugs**: Engines that iterate through rules and return on the *first* match silently invert security posture whenever policies are reordered, merged across teams, or loaded from hash maps.
2. **Broken Policy Optimizers**: Control-plane compilers that constant-fold conditions, prune dead rules, or deduplicate policy bundles accidentally turn a fail-closed rule into an open permit.

In `CedarLite`, you will verify an RBAC + ABAC authorization engine and its policy-pack optimizer across **all** possible principals, actions, resources, context maps, and policy permutations.

---

## 2. Architecture Overview

| Component | File Location | Role |
| :--- | :--- | :--- |
| Domain & AST | `ProveIt/Capstones/CedarLite.lean` | `Effect`, `Decision`, `Entity`, `Request`, `Scope`, `ActionScope`, `ValueExpr`, `Cond`, `Policy` |
| Reference Engine | `authorize` | Evaluates matching `forbid` and `permit` sets with fail-closed attribute semantics |
| Policy Optimizer | `optimizePolicies` | Smart-constructor constant folding (`mkNot`, `mkAnd`, `mkOr`), dead-policy pruning, deduplication |
| Model Solution | `Solutions/Capstones/CedarLite.lean` | Complete zero-`sorry` reference proofs |
| Differential Oracle | `lake exe oracle cedar ...` | Executes the verified evaluator over JSON/CLI queries for differential fuzzing |

---

## 3. Socratic Verification Roadmap

Work through the milestones in `ProveIt/Capstones/CedarLite.lean` in order:

### Milestone 1 — Default-Deny (`default_deny_no_permit`)
*Question to ask yourself*: What happens when `policies` contains zero matching `.permit` policies—even if it contains non-matching permits or non-matching forbids?
- Prove a general list helper: `any_eq_false_of_forall : (∀ x ∈ xs, f x = false) → xs.any f = false`.
- Use `split` on the outer `forbid` check in `authorize`; if no forbid matched, show the inner `permit` scan evaluates to `false`.

### Milestone 2 — Explicit-Forbid Always Wins (`forbidOverridesPermit`)
*Question to ask yourself*: Why does evaluating `forbid` via `List.any` *before* `permit` guarantee monotonicity of denials?
- Prove the dual list helper: `any_eq_true_of_mem : x ∈ xs → f x = true → xs.any f = true`.
- Feed your witness `p ∈ policies` into `any_eq_true_of_mem` to collapse `authorize` directly to `.deny`.

### Milestone 3 — Order-Independence & Deduplication (`authorize_perm`, `authorize_dedup`)
*Question to ask yourself*: Why prove permutation invariance and deduplication invariance separately when both follow from **membership extensionality**?
- Prove `any_congr_mem : (∀ x, x ∈ xs ↔ x ∈ ys) → xs.any f = ys.any f`.
- Lift that to `authorize_congr_mem`. Both `List.Perm.mem_iff` and `mem_dedupPolicies` then discharge their theorems in two lines!

### Milestone 4 — Policy Optimizer Equivalence (`optimizeCond_sound`, `optimizePolicies_sound`)
*Question to ask yourself*: If you inline `match optimizeCond c1, optimizeCond c2` inside `optimizeCond`, how many nested `split` branches explode in your proof?
- Notice how `optimizeCond` delegates algebraic rewrites to smart constructors (`mkNot`, `mkAnd`, `mkOr`).
- Prove 3-line soundness lemmas for each smart constructor (`cases c1 <;> cases c2 <;> simp [...]`), then finish `optimizeCond_sound` by structural induction on `c`.
- Combine `authorize_dedup`, dead-policy filtering (`isDeadPolicy_matches_false`), and `optimizePolicy` mapping to prove `optimizePolicies_sound`.

### Milestone 5 — Non-Vacuity Witness (`non_vacuous_allow`)
A specification that denies *every* request trivially satisfies `default_deny` and `forbidOverridesPermit`—and takes production down! Prove `non_vacuous_allow` using `decide` on a concrete MFA-authenticated owner request.

---

## 4. Verification Commands

```bash
# Check your progress on Capstone 1
lake exe check cedar-lite

# Audit your completed file under the strict kernel gate
lake exe verigate ProveIt/Capstones/CedarLite.lean

# Run differential oracle queries against the verified engine
lake exe oracle --demo
```
