/-
  Capstone 3 — StackVM (Learner Starter)
  Typed Arithmetic/Conditional AST, Constant-Folding Optimizer & Verified Stack Bytecode VM

  Read `capstones/stack-vm/README.md` for the Socratic brief and roadmap,
  and `capstones/stack-vm/DESIGN.md` for proof-engineering guidance.

  Your mission: replace every `sorry` below with a complete kernel-checked proof!
-/
set_option autoImplicit false

namespace StackVM

/-! ## 1. Syntax & Reference Semantics -/

inductive ArithOp where
  | add
  | sub
  | mul
  deriving Repr, DecidableEq

inductive CmpOp where
  | eq
  | lt
  | le
  deriving Repr, DecidableEq

inductive Expr where
  | lit (n : Int)
  | var (name : String)
  | arith (op : ArithOp) (lhs rhs : Expr)
  | ifCmp (cmp : CmpOp) (lhs rhs : Expr) (thenBr elseBr : Expr)
  deriving Repr, DecidableEq

abbrev Env := List (String × Int)

def Env.lookup (env : Env) (name : String) : Int :=
  match env with
  | [] => 0
  | (k, v) :: rest => if k == name then v else Env.lookup rest name

def evalArith (op : ArithOp) (a b : Int) : Int :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

def evalCmp (cmp : CmpOp) (a b : Int) : Bool :=
  match cmp with
  | .eq => decide (a = b)
  | .lt => decide (a < b)
  | .le => decide (a ≤ b)

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

def mkIfCmp (cmp : CmpOp) (lhs rhs thenBr elseBr : Expr) : Expr :=
  match lhs, rhs with
  | .lit a, .lit b =>
      if evalCmp cmp a b then thenBr else elseBr
  | _, _ =>
      if decide (thenBr = elseBr) then
        thenBr
      else
        .ifCmp cmp lhs rhs thenBr elseBr

def optimize : Expr → Expr
  | .lit n => .lit n
  | .var name => .var name
  | .arith op lhs rhs => mkArith op (optimize lhs) (optimize rhs)
  | .ifCmp cmp lhs rhs thenBr elseBr =>
      mkIfCmp cmp (optimize lhs) (optimize rhs) (optimize thenBr) (optimize elseBr)

/-! ## 3. Stack Bytecode Instruction Set, Compiler & Virtual Machine -/

abbrev Stack := List Int

inductive Instr where
  | push (n : Int)
  | load (name : String)
  | binOp (op : ArithOp)
  | branchCmp (cmp : CmpOp) (thenCode elseCode : List Instr)
  deriving Repr

mutual
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

def exec (env : Env) : List Instr → Stack → Option Stack
  | [], stk => some stk
  | instr :: rest, stk =>
      match execInstr env instr stk with
      | none => none
      | some stk' => exec env rest stk'
end

def compile : Expr → List Instr
  | .lit n => [.push n]
  | .var name => [.load name]
  | .arith op lhs rhs => compile lhs ++ compile rhs ++ [.binOp op]
  | .ifCmp cmp lhs rhs thenBr elseBr =>
      compile lhs ++ compile rhs ++ [.branchCmp cmp (compile thenBr) (compile elseBr)]

/-! ## 4. Verification Milestones -/

/-- Milestone 1a: Prove the arithmetic smart constructor preserves `eval`. -/
theorem mkArith_sound (env : Env) (op : ArithOp) (lhs rhs : Expr) :
    eval env (mkArith op lhs rhs) = evalArith op (eval env lhs) (eval env rhs) := by
  sorry

/-- Milestone 1b: Prove the conditional smart constructor preserves `eval`. -/
theorem mkIfCmp_sound (env : Env) (cmp : CmpOp) (lhs rhs thenBr elseBr : Expr) :
    eval env (mkIfCmp cmp lhs rhs thenBr elseBr) =
      (if evalCmp cmp (eval env lhs) (eval env rhs) then eval env thenBr else eval env elseBr) := by
  sorry

/--
  Milestone 1c (**Optimizer Soundness**):
  Prove `eval env (optimize e) = eval env e` across all environments and expressions.
-/
theorem optimize_sound (env : Env) (e : Expr) :
    eval env (optimize e) = eval env e := by
  sorry

/--
  Milestone 2a (**Continuation-Generalized Compiler Correctness**):
  Prove that running `compile e ++ rest` on any `stk` equals running `rest` on `eval env e :: stk`.
  *Hint*: Use `induction e generalizing rest stk`! Notice why generalizing *both* `rest`
  and `stk` is essential for `compile lhs ++ compile rhs ++ [...]`.
-/
theorem compile_correct_cont (env : Env) (e : Expr) (rest : List Instr) (stk : Stack) :
    exec env (compile e ++ rest) stk = exec env rest (eval env e :: stk) := by
  sorry

/--
  Milestone 2b (**Total Compiler Correctness**):
  Specialize `compile_correct_cont` to `rest = []` to prove `compile e` never underflows
  and leaves `some (eval env e :: stk)`.
-/
theorem compile_correct (env : Env) (e : Expr) (stk : Stack) :
    exec env (compile e) stk = some (eval env e :: stk) := by
  sorry

/--
  Milestone 3 (**End-to-End Optimizing Compiler Pipeline**):
  Compose `compile_correct` and `optimize_sound`.
-/
theorem pipeline_correct (env : Env) (e : Expr) (stk : Stack) :
    exec env (compile (optimize e)) stk = some (eval env e :: stk) := by
  sorry

/-! ## 5. Non-Vacuity Witness -/

def sampleExpr : Expr :=
  .ifCmp .lt (.lit 2) (.lit 5)
    (.arith .sub (.var "x") (.arith .mul (.lit 0) (.var "y")))
    (.lit 999)

/-- Milestone 4: Verify concrete constant folding and bytecode execution via `decide`. -/
theorem non_vacuous_pipeline :
    optimize sampleExpr = .var "x" ∧
    exec [("x", 42), ("y", 100)] (compile (optimize sampleExpr)) [7] = some [42, 7] := by
  sorry

end StackVM
