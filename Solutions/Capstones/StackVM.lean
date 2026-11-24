/-
  Capstone 3 — StackVM (Model Solution)
  Typed Arithmetic/Conditional AST, Constant-Folding Optimizer & Verified Stack Bytecode VM
-/
set_option autoImplicit false

namespace StackVM

/-! ## 1. Syntax & Reference Semantics -/

/-- Binary integer arithmetic operators. -/
inductive ArithOp where
  | add
  | sub
  | mul
  deriving Repr, DecidableEq

/-- Relational integer comparison operators used in conditional guards. -/
inductive CmpOp where
  | eq
  | lt
  | le
  deriving Repr, DecidableEq

/--
  Statically stratified arithmetic & conditional expression AST.
  Arithmetic operators combine integer expressions, while comparisons appear only in
  typed branch guards (`ifCmp`), making type errors syntactically unrepresentable.
-/
inductive Expr where
  | lit (n : Int)
  | var (name : String)
  | arith (op : ArithOp) (lhs rhs : Expr)
  | ifCmp (cmp : CmpOp) (lhs rhs : Expr) (thenBr elseBr : Expr)
  deriving Repr, DecidableEq

/-- Variable environment mapping identifier names to integer values (defaulting to `0`). -/
abbrev Env := List (String × Int)

def Env.lookup (env : Env) (name : String) : Int :=
  match env with
  | [] => 0
  | (k, v) :: rest => if k == name then v else Env.lookup rest name

/-- Denotation of binary arithmetic operators. -/
def evalArith (op : ArithOp) (a b : Int) : Int :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

/-- Denotation of relational comparison operators. -/
def evalCmp (cmp : CmpOp) (a b : Int) : Bool :=
  match cmp with
  | .eq => decide (a = b)
  | .lt => decide (a < b)
  | .le => decide (a ≤ b)

/-- Total reference evaluator for `Expr`. -/
def eval (env : Env) : Expr → Int
  | .lit n => n
  | .var name => Env.lookup env name
  | .arith op lhs rhs => evalArith op (eval env lhs) (eval env rhs)
  | .ifCmp cmp lhs rhs thenBr elseBr =>
      if evalCmp cmp (eval env lhs) (eval env rhs) then
        eval env thenBr
      else
        eval env elseBr

/-! ## 2. Constant-Folding & Dead-Branch-Eliminating Optimizer -/

/-- Smart constructor folding constant arithmetic and neutral/absorbing identities. -/
def mkArith (op : ArithOp) (lhs rhs : Expr) : Expr :=
  match op, lhs, rhs with
  | op, .lit a, .lit b => .lit (evalArith op a b)
  | .add, .lit 0, r => r
  | .add, l, .lit 0 => l
  | .sub, l, .lit 0 => l
  | .mul, .lit 0, _ => .lit 0
  | .mul, _, .lit 0 => .lit 0
  | .mul, .lit 1, r => r
  | .mul, l, .lit 1 => l
  | op, l, r => .arith op l r

/-- Smart constructor folding constant comparisons and identical branch arms. -/
def mkIfCmp (cmp : CmpOp) (lhs rhs thenBr elseBr : Expr) : Expr :=
  match lhs, rhs with
  | .lit a, .lit b =>
      if evalCmp cmp a b then thenBr else elseBr
  | _, _ =>
      if decide (thenBr = elseBr) then
        thenBr
      else
        .ifCmp cmp lhs rhs thenBr elseBr

/-- Bottom-up constant-folding and dead-branch-elimination pass. -/
def optimize : Expr → Expr
  | .lit n => .lit n
  | .var name => .var name
  | .arith op lhs rhs => mkArith op (optimize lhs) (optimize rhs)
  | .ifCmp cmp lhs rhs thenBr elseBr =>
      mkIfCmp cmp (optimize lhs) (optimize rhs) (optimize thenBr) (optimize elseBr)

/-! ## 3. Stack Bytecode Instruction Set, Compiler & Virtual Machine -/

/-- Operand stack holding intermediate `Int` values (top of stack at list head). -/
abbrev Stack := List Int

/-- Structured stack-machine bytecode instructions. -/
inductive Instr where
  | push (n : Int)
  | load (name : String)
  | binOp (op : ArithOp)
  | branchCmp (cmp : CmpOp) (thenCode elseCode : List Instr)
  deriving Repr

mutual
/--
  Execute a single bytecode instruction on `stk`.
  Returns `none` on stack underflow (fewer than 2 operands for `binOp` or `branchCmp`).
  Note operand order: `lhs` is pushed before `rhs`, so `rhs` sits above `lhs` (`vb :: va :: stk`).
-/
def execInstr (env : Env) : Instr → Stack → Option Stack
  | .push n, stk => some (n :: stk)
  | .load name, stk => some (Env.lookup env name :: stk)
  | .binOp op, vb :: va :: stk => some (evalArith op va vb :: stk)
  | .binOp _, _ => none
  | .branchCmp cmp thenCode elseCode, vb :: va :: stk =>
      if evalCmp cmp va vb then
        exec env thenCode stk
      else
        exec env elseCode stk
  | .branchCmp _ _ _, _ => none

/-- Execute a sequence of bytecode instructions starting from `stk`. -/
def exec (env : Env) : List Instr → Stack → Option Stack
  | [], stk => some stk
  | instr :: rest, stk =>
      match execInstr env instr stk with
      | none => none
      | some stk' => exec env rest stk'
end

/-- Compile an `Expr` into stack-machine bytecode. -/
def compile : Expr → List Instr
  | .lit n => [.push n]
  | .var name => [.load name]
  | .arith op lhs rhs => compile lhs ++ compile rhs ++ [.binOp op]
  | .ifCmp cmp lhs rhs thenBr elseBr =>
      compile lhs ++ compile rhs ++ [.branchCmp cmp (compile thenBr) (compile elseBr)]

/-! ## 4. Optimizer Soundness Proofs -/

/-- Soundness of arithmetic smart constructor `mkArith`. -/
theorem mkArith_sound (env : Env) (op : ArithOp) (lhs rhs : Expr) :
    eval env (mkArith op lhs rhs) = evalArith op (eval env lhs) (eval env rhs) := by
  unfold mkArith
  split
  · rfl
  · simp [eval, evalArith, Int.zero_add]
  · simp [eval, evalArith, Int.add_zero]
  · simp [eval, evalArith, Int.sub_zero]
  · simp [eval, evalArith, Int.zero_mul]
  · simp [eval, evalArith, Int.mul_zero]
  · simp [eval, evalArith, Int.one_mul]
  · simp [eval, evalArith, Int.mul_one]
  · rfl

/-- Soundness of conditional smart constructor `mkIfCmp`. -/
theorem mkIfCmp_sound (env : Env) (cmp : CmpOp) (lhs rhs thenBr elseBr : Expr) :
    eval env (mkIfCmp cmp lhs rhs thenBr elseBr) =
      (if evalCmp cmp (eval env lhs) (eval env rhs) then eval env thenBr else eval env elseBr) := by
  unfold mkIfCmp
  split
  · next a b =>
    by_cases hCmp : evalCmp cmp a b = true <;> simp [hCmp, eval]
  · by_cases hEq : thenBr = elseBr
    · subst hEq
      simp
    · simp [hEq, eval]

/--
  **Optimizer Soundness (`optimize_sound`)**:
  Constant folding, algebraic simplification, and dead-branch elimination
  preserve exact expression semantics under every variable environment.
-/
theorem optimize_sound (env : Env) (e : Expr) :
    eval env (optimize e) = eval env e := by
  induction e with
  | lit _ => rfl
  | var _ => rfl
  | arith op lhs rhs ihl ihr =>
    simp [optimize, mkArith_sound, eval, ihl, ihr]
  | ifCmp cmp lhs rhs thenBr elseBr ihl ihr iht ihe =>
    simp [optimize, mkIfCmp_sound, eval, ihl, ihr, iht, ihe]

/-! ## 5. Total Compiler & Pipeline Correctness Proofs -/

/--
  **Continuation-Generalized Compiler Correctness (`compile_correct_cont`)**:
  Executing `compile e` followed by *any* code suffix `rest` on *any* initial stack `stk`
  never underflows during `compile e` and is equivalent to running `rest` on `eval env e :: stk`.
-/
theorem compile_correct_cont (env : Env) (e : Expr) (rest : List Instr) (stk : Stack) :
    exec env (compile e ++ rest) stk = exec env rest (eval env e :: stk) := by
  induction e generalizing rest stk with
  | lit n =>
    rfl
  | var name =>
    rfl
  | arith op lhs rhs ihl ihr =>
    simp only [compile, List.append_assoc]
    rw [ihl, ihr]
    rfl
  | ifCmp cmp lhs rhs thenBr elseBr ihl ihr iht ihe =>
    simp only [compile, List.append_assoc]
    rw [ihl, ihr]
    simp only [ List.singleton_append, exec, execInstr, eval]
    by_cases hCmp : evalCmp cmp (eval env lhs) (eval env rhs) = true
    · simp only [hCmp, ↓reduceIte]
      have ht := iht [] stk
      simp only [List.append_nil, exec] at ht
      rw [ht]
    · simp only [hCmp, Bool.false_eq_true, ↓reduceIte]
      have hf := ihe [] stk
      simp only [List.append_nil, exec] at hf
      rw [hf]

/--
  **Total Compiler Correctness (`compile_correct`)**:
  Running `compile e` on any initial stack `stk` terminates without error (`some`)
  and pushes `eval env e` cleanly onto `stk`.
-/
theorem compile_correct (env : Env) (e : Expr) (stk : Stack) :
    exec env (compile e) stk = some (eval env e :: stk) := by
  have h := compile_correct_cont env e [] stk
  simpa [exec] using h

/-- Bytecode composition lemma: running `c1 ++ c2` binds `exec env c2` over `exec env c1`. -/
theorem exec_append (env : Env) (c1 c2 : List Instr) (stk : Stack) :
    exec env (c1 ++ c2) stk = (exec env c1 stk).bind (exec env c2) := by
  induction c1 generalizing stk with
  | nil => rfl
  | cons instr rest ih =>
    simp only [List.cons_append, exec]
    cases execInstr env instr stk with
    | none => rfl
    | some stk' => exact ih stk'

/--
  **End-to-End Optimizing Compiler Correctness (`pipeline_correct_cont`)**:
  Compiling the optimized AST `optimize e` with any trailing bytecode `rest`
  behaves identically to pushing the unoptimized `eval env e` onto `stk` and running `rest`.
-/
theorem pipeline_correct_cont (env : Env) (e : Expr) (rest : List Instr) (stk : Stack) :
    exec env (compile (optimize e) ++ rest) stk = exec env rest (eval env e :: stk) := by
  rw [compile_correct_cont, optimize_sound]

theorem pipeline_correct (env : Env) (e : Expr) (stk : Stack) :
    exec env (compile (optimize e)) stk = some (eval env e :: stk) := by
  rw [compile_correct, optimize_sound]

/-! ## 6. Non-Vacuity Witnesses -/

/-- Sample expression exercising non-commutative subtraction, comparisons, and dead branches. -/
def sampleExpr : Expr :=
  .ifCmp .lt (.lit 2) (.lit 5)
    (.arith .sub (.var "x") (.arith .mul (.lit 0) (.var "y")))
    (.lit 999)

/-- Non-vacuity witness: `optimize` collapses `sampleExpr` to `.var "x"` and VM returns `42`. -/
theorem non_vacuous_pipeline :
    optimize sampleExpr = .var "x" ∧
    exec [("x", 42), ("y", 100)] (compile (optimize sampleExpr)) [7] = some [42, 7] := by
  decide

end StackVM
