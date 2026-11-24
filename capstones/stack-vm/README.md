# Capstone 3: `StackVM` — Verified Optimizing Bytecode Compiler & Stack Machine

## 1. Engineering Problem

Every bytecode runtime (JVM, WebAssembly, Python VM, eBPF, SQL expression engines) relies on two delicate invariants:

1. **Optimizer Equivalence**: Constant folding, algebraic identities (`x + 0 ↦ x`, `0 * y ↦ 0`), and dead-branch elimination (`if 2 < 5 then t else f ↦ t`) must never alter expression evaluation under any variable environment.
2. **Stack Discipline & Operand Order**: Lowering recursive expression trees into sequential stack bytecode must never underflow the operand stack, never leak extra values onto caller frames, and never invert operand order (`a - b` vs `b - a`) when popping operands off LIFO storage.

In `StackVM`, you prove **both** Optimizer Soundness and Total Compiler Correctness across arbitrary code continuations and arbitrary caller stacks.

---

## 2. Architecture Overview

| Component | Role |
| :--- | :--- |
| `Expr`, `ArithOp`, `CmpOp` | Statically stratified expression AST (`eval : Env → Expr → Int`) |
| `optimize` | Bottom-up constant folder + algebraic simplifier (`mkArith`, `mkIfCmp`) |
| `Instr`, `execInstr`, `exec` | Structured WebAssembly-style stack bytecode & VM returning `Option Stack` |
| `compile` | Recursive compiler lowering `Expr` to `List Instr` |

---

## 3. Socratic Verification Roadmap

### Milestone 1 — Optimizer Soundness (`mkArith_sound`, `mkIfCmp_sound`, `optimize_sound`)
*Question*: Why prove `mkArith_sound` and `mkIfCmp_sound` before touching `optimize`?
- Unfold `mkArith`, use `split`, and discharge each algebraic identity with `Int.zero_add`, `Int.add_zero`, `Int.sub_zero`, `Int.zero_mul`, `Int.mul_zero`, `Int.one_mul`, `Int.mul_one`.
- Once both smart-constructor lemmas hold, `optimize_sound` collapses to a 6-line structural induction on `e`.

### Milestone 2 — The Continuation Strengthening (`compile_correct_cont`, `compile_correct`)
*Question*: Try proving `exec env (compile e) stk = some (eval env e :: stk)` directly by induction on `e`. Where does `.arith op lhs rhs` get stuck?
- `compile (.arith op lhs rhs)` produces `compile lhs ++ compile rhs ++ [.binOp op]`. Here `compile lhs` is **not** executed in isolation—it is followed by the continuation `rest := compile rhs ++ [.binOp op]`, and `compile rhs` is executed on the *modified* stack `eval env lhs :: stk`!
- Generalizing **both** the code suffix `rest` and the stack `stk` (`induction e generalizing rest stk`) gives `compile_correct_cont`:
  ```lean
  exec env (compile e ++ rest) stk = exec env rest (eval env e :: stk)
  ```
- Look closely at `.ifCmp`: `execInstr` evaluates the chosen branch block (`compile thenBr`) in a structured frame (`[]` suffix), which your induction hypothesis `iht [] stk` turns directly into `some (eval env thenBr :: stk)`!
- Finally, specialize `rest = []` to obtain `compile_correct : exec env (compile e) stk = some (eval env e :: stk)`.

### Milestone 3 — End-to-End Verified Pipeline (`pipeline_correct`)
Chain `compile_correct` with `optimize_sound` in a single `rw` line to verify the complete optimizing compiler!

---

## 4. Verification Commands

```bash
lake exe check stack-vm
lake exe verigate ProveIt/Capstones/StackVM.lean
```
