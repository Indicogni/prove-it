# `CedarLite` — Proof Engineering & Design Decisions

## 1. Set Semantics Over Lists via Membership Extensionality

In production Rust, Go, or TypeScript implementations, policy bundles are stored in slices, vectors, or hash sets. Modeling `policies : List Policy` in Lean 4 gives executable performance and straightforward JSON deserialization, while proving **membership extensionality**:

```lean
theorem authorize_congr_mem (ps₁ ps₂ : List Policy) (req : Request)
    (hMem : ∀ p, p ∈ ps₁ ↔ p ∈ ps₂) :
    authorize ps₁ req = authorize ps₂ req
```

gives `authorize` true **finite-set semantics** without forcing learners to carry quotient types (`Finset`) through executable code. Once `authorize_congr_mem` is established, permutation invariance (`authorize_perm`), append commutativity (`authorize_append_comm`), and deduplication soundness (`authorize_dedup`) all become 2-line corollaries.

## 2. Fail-Closed Missing-Attribute Semantics

Real ABAC bugs often arise from three-valued or exception-throwing attribute lookups (e.g., `!(context.riskScore <= 50)` evaluating to `true` or crashing when `riskScore` is absent).

In `CedarLite`:
- `evalValue` returns `Option AttrVal`.
- Atomic comparisons (`attrEq`, `attrIntLe`) return `false` whenever either operand is `none` or has a mismatched runtime type (e.g., comparing `.str` with `.int` in `attrIntLe`).
- Crucially, `optimizeCond` **only** folds `.attrEq` and `.attrIntLe` on syntactic literals (`.lit`), never applying unsound rewrites such as `x == x ↦ .always` (which would be **unsound** when `x` is a missing attribute `none`!).

Try testing your mental model: if `optimizeCond` rewrote `.attrEq e e` to `.always`, `evalCond (.attrEq (.contextAttr "missing") (.contextAttr "missing")) req` would flip from `false` to `true`! Keeping rewrites restricted to `.lit` preserves exact fail-closed equivalence.

## 3. Smart Constructors Prevent Case-Explosion

A classic beginner mistake in verified compiler/optimizer passes is pattern-matching directly on recursive calls inside the main recursion:

```lean
-- Anti-pattern: causes 25+ nested `split` goals with fragile hypotheses
| .and c1 c2 =>
    match optimizeCond c1, optimizeCond c2 with ...
```

By factoring algebraic simplifications into standalone smart constructors (`mkNot`, `mkAnd`, `mkOr`):
1. Each smart constructor has a 1-line soundness theorem proved by `cases c1 <;> cases c2 <;> simp`.
2. The inductive step of `optimizeCond_sound` never needs to inspect what shape `optimizeCond c1` produced—it simply rewrites with `mkAnd_sound`, `ih1`, and `ih2`!

## 4. `deriving Repr, DecidableEq` vs `BEq`

In Lean 4.36.0, deriving `DecidableEq` automatically synthesizes a lawful `BEq` instance via `instBEqOfDecidableEq`, where `(a == b) = true ↔ a = b` (`decide_eq_true_eq`) holds definitionally. Combining `deriving DecidableEq, BEq` would overwrite that lawful bridge with an opaque structural `BEq` lacking automatic lawfulness lemmas. We therefore derive `Repr, DecidableEq` across all syntax trees and use `decide (...)` in predicates so `simp` bridges `Bool` and `Prop` effortlessly.
