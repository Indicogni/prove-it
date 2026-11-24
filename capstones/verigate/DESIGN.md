# `VeriGateLab` — Proof Engineering & PCC Gate Architecture

## 1. Separation of Trust: $O(N)$ Audit Spec vs. $O(1)$ Production Code

A golden rule of Proof-Carrying Code (PCC) is: **Specifications optimize for human auditability; implementations optimize for machine execution.**

- Inside `BEGIN VERIGATE SPEC`, `sumBalances` and `sumReserved` are 3-line recursive list sums over `s.accounts.toList`. Any domain engineer can audit `ValidKernel` in 30 seconds.
- Outside the locked spec, `stepKernel` never calls `sumBalances` or `sumReserved`! It indexes `s.accounts[tid]` in $O(1)$, updates `s.accounts.set tid acct' h` in $O(1)$ (mutating the underlying buffer in place under Lean 4's FBIP reference-counting runtime when uniquely owned), and adjusts `s.globalInflight` in $O(1)$.
- The mechanized proof bridges the performance gap once at compile time, paying **zero** $O(N)$ audit cost at runtime.

## 2. Additive Conservation Laws Tame `Nat` Truncation

In Lean 4, `Nat` subtraction truncates at zero (`3 - 5 = 0`). Writing a list-update lemma as:
```lean
-- Fragile: requires proving xs[i].balance ≤ sumBalances xs first!
sumBalances (xs.set i a') = sumBalances xs - xs[i].balance + a'.balance
```
creates tedious auxiliary obligations. Writing the exact same law additively:
```lean
sumBalances (xs.set i a') + xs[i].balance = sumBalances xs + a'.balance
```
eliminates subtraction from the lemma statement completely, allowing `omega` to solve `deposit`, `reserve`, `settle`, and `cancel` automatically!

## 3. Why Non-Vacuity (`non_vacuous`) Is Part of the Trust Gate

Consider a malicious or hallucinating AI agent asked to implement `stepKernel` satisfying `stepKernel s op = some s' → ValidKernel s'`. Setting:
```lean
def stepKernel (_ : KernelState) (_ : KernelOp) : Option KernelState := none
```
makes `hStep : none = some s'` contradictory, proving `ValidKernel s'` in one line with **zero** axioms and **zero** spec edits!

`VeriGate` closes this vacuity loophole via two complementary mechanisms:
1. Requiring a `non_vacuous` theorem in the audited module whose type is not an implication from `False` and whose proof passes Tier-0 axiom checks.
2. Cryptographically pinning the `VERIGATE SPEC` block via SHA-256 so the required theorem signatures and `ValidKernel` definition cannot be weakened.
