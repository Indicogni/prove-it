# Architecture & Supervisor Arbitration Decisions

This document records the key pedagogical, technical, and security decisions made by the **Indicogni Specialist Council** (TLA+/Feynman Systems Tutor, Socratic Pedagogy Lead, Precision & Visual Intuition Tutor, Lean 4 Software Verification Architect, Indicogni UI/UX Architect, AI Verification Specialist, and Safety & Security Officer) and arbitrated by the **Two Supervisor Agents**.

## 1. Zero-Dependency Core/`Std` Lean 4.36.0 (No `Mathlib` Wall)
- **Conflict:** Importing `Mathlib` or `Plausible` gives prebuilt algebra and property-testing combinators, at the cost of multi-gigabyte cache downloads, brittle version churn, and broken standalone `live.lean-lang.org` snippets.
- **Ruling:** Strict zero-dependency `lakefile.toml` pinned to `leanprover/lean4:v4.36.0`.
  - Cold `lake build` finishes in seconds and works 100% offline.
  - Every `.lean` lesson opens standalone in 1 click on `live.lean-lang.org`.
  - Building a 35-line TLA+-style bounded BFS state-space explorer from first principles in Chapter 04 demystifies model checking completely before introducing unbounded inductive proofs in Chapter 08.

## 2. Pedagogical Ordering: Systems & State Machines Before Dependent Indexing
- **Conflict:** Traditional courses open with Peano natural numbers (`0 + n = n`) or early dependent vector indexing (`Fin n` / `Vector α n`), triggering cryptic motive-typecheck errors before engineers understand tactics.
- **Ruling:**
  1. Open Chapter 01 Line 1 with a concrete AI-generated rate-limiter bug caused by `Nat` saturating subtraction (`0 - 1 = 0`).
  2. Teach plain `structure`/`inductive` data + executable `Bool`/`Option` functions + `Init`/`Next` state-machine invariants first (Parts I–II).
  3. Introduce `Subtype` (`{ x // P x }`) and `Fin n` in Chapter 09 (Part III) once `omega`, `simp only`, and `grind` are second nature—so dependent types feel like a superpower, not compiler friction.

## 3. Two-Gear Verification (TLA+ Bounded Search + Lean Deductive Proof)
- **Ruling:** Never frame model checking and theorem proving as rivals. Engineers learn a **Two-Gear Loop**:
  - **Gear 1 (Bounded BFS Search):** Exhaustively search small bounds (`depth ≤ 6`) in milliseconds to catch shallow protocol bugs and extract concrete counterexample traces instead of wasting hours proving a false theorem.
  - **Gear 2 (Unbounded Inductive Proof & Stuttering Refinement):** Prove `Init s → Inv s`, `Inv s → Next s e s' → Inv s'`, and `Inv s → Safe s` (plus `abs : Impl → Spec` refinement mappings) to mathematically seal infinite epochs, arbitrary packet duplication/reordering, and 64-bit counter wrap-around.

## 4. Two-Tier Axiom Policy in `lake exe verigate`
- **Conflict:** Both `bv_decide` (verified LRAT bit-blasting for `BitVec 64` hardware arithmetic) and raw `native_decide` emit `Lean.ofReduceBool` / `Lean.trustCompiler` in `#print axioms`.
- **Ruling:**
  - **Tier 0 (`--strict-kernel`, Default):** Permits strictly `{propext, Quot.sound, Classical.choice}`.
  - **Tier 1 (`--trust-tier=bv-lrat`, Explicit Opt-In for `BitVec` / `UInt64`):** Permits `Lean.ofReduceBool` / `Lean.trustCompiler` *only* when source/environment auditing confirms zero raw `native_decide` usage.
  - **Unconditional Rejects:** `sorryAx`, custom `axiom`/`opaque`, raw `native_decide`, `@[implemented_by]`, `@[extern]`, `@[csimp]`, `unsafe`, unverified `partial`, `Spec` hash drift, and missing non-vacuity witnesses (`∃ x, Pre x`).

## 5. Multi-Domain 4-Capstone Suite + Polyglot Differential Oracle
- **Ruling:** Ship four distinct production capstones (`CedarLite` IAM policy engine, `FencingKV` distributed lease & tombstone store, `StackVM` optimizing bytecode compiler, and `VeriGate` AI proof-carrying harness) plus `lake exe oracle` so engineers whose day job is Rust, Go, TypeScript, Python, or C++ can immediately differential-fuzz production code against verified Lean specs.
