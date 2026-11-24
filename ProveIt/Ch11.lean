/-
  Chapter 11: Pure Effects & Termination as DoS Defense
  =====================================================

  Production services mutate state, fail with structured errors, search arrays,
  and resolve recursive configurations. In Lean 4:
  1. Stateful and fallible computations (`StateM`, `Except`, `StateT σ (Except ε)`)
     are pure mathematical functions—giving you imperative `do` syntax AND
     transactional rollback on error without mocks or side-effect harnesses.
  2. Termination proofs (`termination_by` / `decreasing_by`) are compile-time
     Denial-of-Service (DoS) defenses: a total function is mathematically
     incapable of hanging on adversarial inputs (such as cyclic config aliases
     or off-by-one binary search bounds).
  3. Even better, total recursive functions unlock `fun_induction`—Lean's
     functional induction tactic that mirrors your function's exact branches!
-/
set_option autoImplicit false

namespace ProveIt.Ch11

/-! ## 1. Transactional Pure Effects with `StateM` and `Except` -/

structure Ledger where
  alice : Nat
  bob   : Nat
  deriving Repr, DecidableEq

inductive TxError where
  | insufficientFunds (available required : Nat)
  deriving Repr, DecidableEq

/--
  Worked Example: Stacking `StateT Ledger` over `Except TxError` gives
  `Ledger → Except TxError (Unit × Ledger)`: imperative `get`/`set`/`throw`
  notation with atomic rollback whenever an error is thrown!
-/
def transferAliceToBob (amount : Nat) : StateT Ledger (Except TxError) Unit := do
  let s ← get
  if s.alice < amount then
    throw (.insufficientFunds s.alice amount)
  set ({ s with alice := s.alice - amount, bob := s.bob + amount } : Ledger)

theorem transferAliceToBob_conserves (amount : Nat) (s s' : Ledger)
    (hOk : (transferAliceToBob amount).run s = .ok ((), s')) :
    s'.alice + s'.bob = s.alice + s.bob := by
  simp only [transferAliceToBob, StateT.run, pure, bind, get, getThe,
    MonadStateOf.get, StateT.get, set, throw, throwThe, MonadExceptOf.throw,
    StateT.bind, Except.bind, Except.pure] at hOk
  split at hOk
  · nomatch hOk
  · injection hOk with hPair
    injection hPair with _ hState
    subst hState
    simp only
    omega

/-- info: Except.ok ((), { alice := 70, bob := 50 }) -/
#guard_msgs in
#eval (transferAliceToBob 30).run { alice := 100, bob := 20 }

/-- info: Except.error (ProveIt.Ch11.TxError.insufficientFunds 100 150) -/
#guard_msgs in
#eval (transferAliceToBob 150).run { alice := 100, bob := 20 }

/-! ## 2. Midpoint Binary Search, Termination, and `fun_induction` -/

/--
  Worked Example: Binary search over half-open `[lo, hi)` using overflow-safe
  midpoint `lo + (hi - lo) / 2`.
  Notice two things:
  - `termination_by hi - lo` + `decreasing_by all_goals omega` proves zero infinite loops.
  - Indexing `arr[mid]` uses Lean's compile-time bounds proof without runtime checks!
-/
def bsearch (arr : Array Nat) (target : Nat) (lo hi : Nat) (hHi : hi ≤ arr.size) :
    Option (Fin arr.size) :=
  if hLo : lo < hi then
    let mid := lo + (hi - lo) / 2
    have hMidSize : mid < arr.size := by omega
    if arr[mid] == target then
      some ⟨mid, hMidSize⟩
    else if arr[mid] < target then
      bsearch arr target (mid + 1) hi hHi
    else
      bsearch arr target lo mid (by omega)
  else
    none
termination_by hi - lo
decreasing_by
  all_goals omega

/--
  `fun_induction` generates one goal per control-flow path of `bsearch`,
  automatically supplying inductive hypotheses for the recursive calls!
-/
theorem bsearch_sound (arr : Array Nat) (target : Nat) (lo hi : Nat)
    (hHi : hi ≤ arr.size) (idx : Fin arr.size)
    (hFound : bsearch arr target lo hi hHi = some idx) :
    arr[idx] = target ∧ lo ≤ idx.val ∧ idx.val < hi := by
  fun_induction bsearch arr target lo hi hHi generalizing idx
  · -- Branch 1: `arr[mid] == target`
    injection hFound with hIdx
    subst hIdx
    rename_i mid _ hEq
    simp only [beq_iff_eq] at hEq
    simp only [mid]
    refine ⟨hEq, ?_, ?_⟩ <;> omega
  · -- Branch 2: `arr[mid] < target` (searched `[mid + 1, hi)`)
    rename_i ih
    obtain ⟨hVal, hGe, hLtHi⟩ := ih idx hFound
    refine ⟨hVal, ?_, hLtHi⟩
    omega
  · -- Branch 3: `arr[mid] > target` (searched `[lo, mid)`)
    rename_i ih
    obtain ⟨hVal, hGe, hLtMid⟩ := ih idx hFound
    refine ⟨hVal, hGe, ?_⟩
    omega
  · -- Branch 4: empty interval `¬ lo < hi`
    nomatch hFound

#guard (bsearch #[10, 20, 35, 50, 80] 35 0 5 (by decide)).map Fin.val == some 2
#guard (bsearch #[10, 20, 35, 50, 80] 42 0 5 (by decide)).isNone

/-- info: 'ProveIt.Ch11.bsearch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bsearch_sound

/-! ## Exercises -/

structure Vault where
  balance       : Nat
  feesCollected : Nat
  deriving Repr, DecidableEq

inductive VaultErr where
  | insufficientBalance (balance needed : Nat)
  deriving Repr, DecidableEq

/--
  EXERCISE 1: Implement `debitWithFee` in `StateT Vault (Except VaultErr) Nat`.
  - If `v.balance < amount + fee`, throw `.insufficientBalance v.balance (amount + fee)`.
  - Otherwise subtract `amount + fee` from `balance`, add `fee` to `feesCollected`,
    and return the new `balance`.
-/
def debitWithFee (amount fee : Nat) : StateT Vault (Except VaultErr) Nat :=
  let _ := (amount, fee)
  sorry

-- Uncomment after completing Exercise 1:
-- #eval (debitWithFee 100 5).run { balance := 200, feesCollected := 10 }
-- #eval (debitWithFee 200 5).run { balance := 200, feesCollected := 10 }

/--
  EXERCISE 2: Prove conservation of funds for `debitWithFee`:
  whenever `debitWithFee` succeeds, `rem = v'.balance` and
  `v'.balance + v'.feesCollected + amount = v.balance + v.feesCollected`.
-/
theorem debitWithFee_conserves (amount fee rem : Nat) (v v' : Vault)
    (hOk : (debitWithFee amount fee).run v = .ok (rem, v')) :
    rem = v'.balance ∧
    v'.balance + v'.feesCollected + amount = v.balance + v.feesCollected := by
  sorry

/-! ### DoS-Safe Config-Graph Alias Resolution -/

inductive ConfigEntry where
  | literal (val : String)
  | alias   (targetKey : String)
  deriving Repr, DecidableEq

inductive ConfigErr where
  | missingKey (key : String)
  | depthExceeded (key : String)
  deriving Repr, DecidableEq

def lookupEntry (env : List (String × ConfigEntry)) (key : String) : Option ConfigEntry :=
  match env.find? (fun p => p.1 == key) with
  | some (_, entry) => some entry
  | none => none

/--
  Bounded config resolver: follows `.alias targetKey` hops at most `fuel` times,
  preventing cyclic alias graphs (`A → B → A`) from hanging worker threads.
-/
def resolveConfig (env : List (String × ConfigEntry)) (fuel : Nat) (key : String) :
    Except ConfigErr String :=
  match fuel with
  | 0 => .error (.depthExceeded key)
  | fuel' + 1 =>
    match lookupEntry env key with
    | none => .error (.missingKey key)
    | some (.literal val) => .ok val
    | some (.alias nextKey) => resolveConfig env fuel' nextKey
termination_by fuel

/-- info: Except.ok "10.0.0.1" -/
#guard_msgs in
#eval resolveConfig [("db", .alias "primary"), ("primary", .literal "10.0.0.1")] 4 "db"

/-- info: Except.error (ProveIt.Ch11.ConfigErr.depthExceeded "b") -/
#guard_msgs in
#eval resolveConfig [("a", .alias "b"), ("b", .alias "a")] 5 "a"

/--
  EXERCISE 3: Prove using `fun_induction resolveConfig` that any successful
  resolution consumed at least 1 unit of fuel (`0 < fuel`).
-/
theorem resolveConfig_pos_fuel (env : List (String × ConfigEntry)) (fuel : Nat)
    (key val : String) (hOk : resolveConfig env fuel key = .ok val) :
    0 < fuel := by
  sorry

/--
  EXERCISE 4: Prove fuel monotonicity using `fun_induction resolveConfig`:
  increasing the recursion budget from `fuel` to `fuel'` (`fuel ≤ fuel'`)
  never changes or breaks an already-successful config resolution!
-/
theorem resolveConfig_mono (env : List (String × ConfigEntry)) (fuel fuel' : Nat)
    (key val : String) (hOk : resolveConfig env fuel key = .ok val) (hLe : fuel ≤ fuel') :
    resolveConfig env fuel' key = .ok val := by
  sorry

/--
  Partition-point lower bound over `[lo, hi)` using overflow-safe midpoint.
-/
def lowerBound (pred : Nat → Bool) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    let mid := lo + (hi - lo) / 2
    if pred mid then
      lowerBound pred lo mid
    else
      lowerBound pred (mid + 1) hi
  else
    lo
termination_by hi - lo
decreasing_by
  all_goals omega

#guard lowerBound (fun x => decide (x ≥ 35)) 0 100 == 35

/--
  EXERCISE 5: Prove via `fun_induction lowerBound` + `omega` that whenever
  `lo ≤ hi`, `lowerBound pred lo hi` always lands inside `[lo, hi]`.
-/
theorem lowerBound_in_range (pred : Nat → Bool) (lo hi : Nat) (hLe : lo ≤ hi) :
    lo ≤ lowerBound pred lo hi ∧ lowerBound pred lo hi ≤ hi := by
  sorry

end ProveIt.Ch11
