# Capstone 4: `VeriGateLab` — AI Proof-Carrying Code & Multi-Tenant Token Kernel

## 1. Engineering Problem

When an AI coding agent generates high-performance systems code—such as an $O(1)$ multi-tenant GPU token quota and billing settlement kernel—how can a human team merge it with mathematical certainty without reading thousands of lines of proof tactics?

Unchecked AI proof agents routinely exploit verification loopholes:
- Weakening `ValidKernel` to `True` or adding a vacuous `False → ...` hypothesis.
- Implementing `stepKernel _ _ := none` (which trivially preserves every state invariant because no step ever succeeds!).
- Sneaking in `sorry`, custom `axiom`s, `native_decide` (`Lean.trustCompiler`), or `@[implemented_by]` runtime overrides.

In `VeriGateLab`, you verify a genuine $O(1)$ array-backed multi-tenant token settlement kernel against a **human-locked SHA-256 specification** and pass the `lake exe verigate` Proof-Carrying Code gate.

---

## 2. Architecture Overview

| Layer | Role |
| :--- | :--- |
| `BEGIN VERIGATE SPEC ... END VERIGATE SPEC` | Human-locked specification pinned by SHA-256 |
| `ValidKernel` | $O(N)$ global audit invariant: Zero Inflight Drift + Hard Capacity Ceiling + Exact Credit Conservation |
| `stepKernel` | $O(1)$ refcounted-array indexing (`s.accounts[tid]`), update (`s.accounts.set`), and cached `globalInflight` tracking |
| `non_vacuous` | Mandatory non-vacuity witness required by `verigate` proving multi-tenant settlement succeeds |

---

## 3. Socratic Verification Roadmap

### Milestone 1 — Bridging $O(1)$ Array Mutation to $O(N)$ Ledger Sums (`sumBalances_set`, `sumReserved_set`)
*Question*: Why state the delta lemma using addition (`sumBalances (xs.set i a') + xs[i].balance = sumBalances xs + a'.balance`) instead of `Nat` subtraction?
- Truncating `Nat` subtraction (`a - b = 0` when `a < b`) requires side-conditions everywhere! Stating the conservation law purely with `+` lets `omega` solve every branch without subtraction underflow side-conditions.

### Milestone 2 — Kernel Conservation & Quota Ceiling (`initKernel_valid`, `stepKernel_preserves_valid`)
*Question*: During `settle tid reservedTokens actualUsed`, tokens move simultaneously between `reserved`, `balance` (refund), `platformRevenue`, and `globalInflight`. Why doesn't a single token credit vanish?
- Notice `reservedTokens = actualUsed + (reservedTokens - actualUsed)` whenever `actualUsed ≤ reservedTokens`.
- Combine `sumBalances_set`, `sumReserved_set`, and `Array.getElem_toList` so `omega` verifies all three clauses of `ValidKernel` simultaneously.

### Milestone 3 — Mandatory Non-Vacuity Witness (`non_vacuous`)
Exhibit the exact post-settlement `KernelState` for the 6-step multi-tenant scenario and close the proof with `decide`.

---

## 4. Verification Commands

```bash
# Check progress on Capstone 4
lake exe check verigate

# Run the full VeriGate Tier-0 strict kernel & SHA-256 spec-lock audit
lake exe verigate Solutions/Capstones/VeriGateLab.lean

# Run VeriGate's built-in adversarial Red-Team self-test suite
lake exe verigate --self-test
```
