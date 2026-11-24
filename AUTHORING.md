# Authoring & Proof-Engineering Guide

Internal house guide for maintaining **Prove It: Formally Verified Software in Lean 4**.

## 1. Indicogni Socratic Voice
- **Open with a failure or puzzle in ≤ 5 lines.** Never open with a definition ("In Lean, an inductive type is..."). Show the bug or surprising output first, ask the learner to commit to a prediction (`PREDICT`), then earn the concept and name the term once in bold.
- **Plain, direct prose.** Never write *"simply"*, *"obviously"*, *"trivially"*, or *"just"*. No emojis.
- **Analogies have seams.** At most one concrete analogy per concept, always stating explicitly where the analogy breaks.

## 2. Lean 4.36.0 Anti-Brittleness Rules
- **Pin:** `leanprover/lean4:v4.36.0` in `lean-toolchain`; zero external Lake packages.
- **Standalone files:** Every `ProveIt/*.lean` and `Solutions/*.lean` begins with `set_option autoImplicit false` and carries zero cross-chapter dependencies so learners can open any file in one click on `live.lean-lang.org`.
- **Never combine `deriving DecidableEq, BEq`:** In Lean 4.36.0, `deriving Repr, DecidableEq` already synthesizes `BEq` and `LawfulBEq`. Adding `BEq` shadows `LawfulBEq` and breaks `==`-to-`=` reflection inside `simp` and `grind`.
- **Structured automation:** Prefer pure total functions, targeted `@[grind =]` / `@[simp]` unfolding lemmas, `fun_cases`, `fun_induction`, `simp only [...]`, `omega`, `grind`, and `bv_decide` (`import Std.Tactic.BVDecide`).
- **Silent builds:** Wrap `#eval` and `#print axioms` inside `#guard` or `/-- info: ... -/ #guard_msgs in`.

## 3. Zero-PII & Security Hygiene
- Every commit MUST use Author and Committer: `Indicogni LLC <noreply@indicogni.com>`.
- Run `python3 scripts/audit_security.py`, `lake build`, `lake exe check --solutions`, `lake exe verigate --self-test`, and `python3 scripts/fuzz_against_oracle.py` before every commit.
