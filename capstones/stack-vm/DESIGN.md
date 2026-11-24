# `StackVM` — Proof Engineering & Design Decisions

## 1. Syntactic Stratification vs. Extrinsic Type Judgments

In an untyped AST where booleans and integers share one syntax node, `eval` must return `Option Val` (failing on `true + 5`), polluting every compiler theorem with `HasType Γ e τ` hypotheses.

By stratifying comparison operators (`CmpOp`) into structured conditional guards (`ifCmp cmp lhs rhs thenBr elseBr`) while keeping arithmetic expressions (`ArithOp`) over `Int`:
1. Ill-typed expressions are **syntactically unrepresentable**.
2. `eval : Env → Expr → Int` is **100% total**, while `exec : Env → List Instr → Stack → Option Stack` remains partial (`none` on stack underflow).
3. Proving `exec env (compile e) stk = some (eval env e :: stk)` simultaneously proves **absence of VM stack underflow** AND **functional equivalence**!

## 2. Mutual Structural Recursion (`execInstr` / `exec`) for Kernel Reduction

Notice that `Instr.branchCmp` embeds nested `List Instr` blocks (just like WebAssembly's structured `if ... else ... end` bytecode). If `exec` were written as a single function matching `.branchCmp cmp t f :: rest`, Lean 4 would compile it via well-founded `sizeOf` recursion, blocking definitional kernel reduction (`rfl` and `decide`).

By splitting single-instruction execution (`execInstr : Instr → ...`) and block execution (`exec : List Instr → ...`) inside a `mutual` block:
- Lean 4 compiles them via **pure structural recursion** on `Instr` and `List Instr`.
- `lit`, `var`, and `arith` steps in `compile_correct_cont` close by `rfl`!
- Concrete end-to-end execution tests (`non_vacuous_pipeline`) close by `decide` inside the kernel without `native_decide`!
- Sequencing composition (`exec_append`) becomes a 5-line proof over `List` that never even inspects `Instr` constructors!

## 3. Catching the LIFO Operand-Order Bug

When `compile (.arith .sub a b)` runs `compile a` followed by `compile b` on `stk`:
1. `compile a` pushes `va`, giving `va :: stk`.
2. `compile b` pushes `vb`, giving `vb :: va :: stk`.

Notice `vb` sits at the **head** of the stack and `va` sits **second**! If `execInstr` popped `va :: vb :: stk` instead of `vb :: va :: stk`, commutative tests (`add`, `mul`, `eq`) would all pass while `sub` and `lt` silently computed `b - a` and `b < a`. Mechanizing `compile_correct_cont` makes such LIFO inversion bugs impossible to ship.
