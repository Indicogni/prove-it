# Learner Synthesis Workbook (`NOTES.md`)

Write two to four sentences in your own words after finishing each unit—**before** opening `Solutions/` or the *Check your explanation* rubric in `guides/`.
Spaced retrieval schedule: revisit your notes at **+1 day**, **+7 days**, and **+21 days** without looking at the code.

## Ch 01 · The Silent Truncation Bug

**Prompt:** Why did `Nat` subtraction hide the rate-limiter bug, and when should a specification use `Int` or `Option` instead?

**My synthesis:** _(write your answer here)_

---

## Ch 02 · Illegal States & Domain Modeling

**Prompt:** How do algebraic sum/product types eliminate preconditions that would otherwise require theorem hypotheses?

**My synthesis:** _(write your answer here)_

---

## Ch 03 · Compile-Time Exhaustion & Boolean Reflection

**Prompt:** What does `Decidable P` bridge, and why prove `check x = true ↔ Safe x` instead of putting `Prop` inside runtime structs?

**My synthesis:** _(write your answer here)_

---

## Ch 04 · Gear 1: A TLA+ Model Checker in 35 Lines

**Prompt:** When does bounded BFS beat deductive proof, and where does state-space explosion force Gear 2?

**My synthesis:** _(write your answer here)_

---

## CP 01 · Checkpoint 1: Zero-Panic Canary Router

**Prompt:** Which invariant prevented routing traffic to a drained or zero-weight backend?

**My synthesis:** _(write your answer here)_

---

## Ch 05 · Proofs Are Programs, Goals Are Stack Traces

**Prompt:** How do `intro`, `apply`, `rcases`, and `constructor` correspond to constructing and pattern-matching ordinary data?

**My synthesis:** _(write your answer here)_

---

## Ch 06 · Control Flow, Rewriting & Linear Math

**Prompt:** Why should `simp only [...]` be preferred mid-proof while `grind` and `omega` close leaf goals?

**My synthesis:** _(write your answer here)_

---

## Ch 07 · Unprovable on Purpose

**Prompt:** Given a stuck Infoview goal, how do you tell apart (A) buggy code, (B) a false spec, and (C) a weak inductive hypothesis?

**My synthesis:** _(write your answer here)_

---

## Ch 08 · Gear 2: Inductive Invariants & Strengthening

**Prompt:** What is a 'Garden-of-Eden' state, and why can a true safety property fail naive one-step induction?

**My synthesis:** _(write your answer here)_

---

## CP 02 · Checkpoint 2: Idempotent Write-Ahead Ledger

**Prompt:** Which extra state invariant made crash-replay idempotency provable across arbitrary batch lengths?

**My synthesis:** _(write your answer here)_

---

## Ch 09 · Packing Proofs into Types

**Prompt:** Why do `Prop` fields inside `{ x // P x }` add zero runtime memory overhead after compilation?

**My synthesis:** _(write your answer here)_

---

## Ch 10 · 64-Bit Hardware Truth (`UInt64` & `BitVec`)

**Prompt:** What additional component enters the Trusted Computing Base when switching from `omega` to `bv_decide`?

**My synthesis:** _(write your answer here)_

---

## Ch 11 · Pure Effects & Termination as DoS Defense

**Prompt:** Why did `(lo + hi) / 2` threaten both overflow and non-termination, and what measure proved termination?

**My synthesis:** _(write your answer here)_

---

## Ch 12 · Refinement Mappings & Stuttering Steps

**Prompt:** Why does background compaction need a stuttering clause `abs s' = abs s` in a refinement proof?

**My synthesis:** _(write your answer here)_

---

## CP 03 · Checkpoint 3: Fixed-Capacity Ring Buffer

**Prompt:** How does your `abs : RingBuffer α cap → List α` mapping distinguish full from empty?

**My synthesis:** _(write your answer here)_

---

## Ch 13 · How AI Cheats Formal Verification

**Prompt:** List three ways an untrusted agent can pass `lake build` without proving your intended property, and how `verigate` stops each.

**My synthesis:** _(write your answer here)_

---

## Ch 14 · Spec-First Agentic Co-Design

**Prompt:** Why must every locked `Spec.lean` include a proven `∃ x, ValidInput x` non-vacuity witness?

**My synthesis:** _(write your answer here)_

---

## Ch 15 · Verified Wire Formats (TLV Framing)

**Prompt:** Why prove `decode (encode pkt ++ rest) = some (pkt, rest)` instead of `decode (encode pkt) = some (pkt, [])`?

**My synthesis:** _(write your answer here)_

---

## Ch 16 · Monday-Morning Transfer

**Prompt:** Where in your own team's stack would a 150-line Lean oracle (`lake exe oracle`) catch the highest-cost bugs?

**My synthesis:** _(write your answer here)_

---

## CP 04 · Checkpoint 4: Red-Team Batch Escrow Audit

**Prompt:** Which planted exploit in the escrow module was hardest to spot by human code review alone?

**My synthesis:** _(write your answer here)_

---
