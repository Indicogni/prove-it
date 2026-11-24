/-
  Capstone 4 — VeriGateLab (Model Solution)
  AI Proof-Carrying Code Challenge: Multi-Tenant Token Quota & Settlement Kernel
-/
set_option autoImplicit false

namespace VeriGateLab

-- BEGIN VERIGATE SPEC
/-!
  ## Human-Locked Specification (`Spec`)
  WARNING: In a VeriGate CI pipeline, bytes between `BEGIN VERIGATE SPEC` and
  `END VERIGATE SPEC` are pinned by SHA-256 (`lake exe verigate --spec-hash ...`).
  An untrusted prover or AI agent MUST NOT modify any declaration in this block.
-/

/-- Per-tenant credit balance and currently locked inflight token reservation. -/
structure Account where
  balance : Nat := 0
  reserved : Nat := 0
  deriving Repr, DecidableEq

/--
  Multi-tenant quota & settlement state.
  `accounts` provides O(1) indexed tenant slots; `globalInflight` caches total
  reserved tokens in O(1) without scanning all tenants on every API call.
-/
structure KernelState where
  clusterCapacity : Nat
  totalDeposited : Nat := 0
  platformRevenue : Nat := 0
  globalInflight : Nat := 0
  accounts : Array Account
  deriving Repr, DecidableEq

/-- Operations supported by the multi-tenant token settlement kernel. -/
inductive KernelOp where
  | deposit (tenantId : Nat) (amount : Nat)
  | reserve (tenantId : Nat) (maxTokens : Nat)
  | settle (tenantId : Nat) (reservedTokens : Nat) (actualUsed : Nat)
  | cancel (tenantId : Nat) (reservedTokens : Nat)
  deriving Repr, DecidableEq

/-- Reference O(N) audit sum of available tenant balances. -/
def sumBalances : List Account → Nat
  | [] => 0
  | a :: rest => a.balance + sumBalances rest

/-- Reference O(N) audit sum of locked tenant reservations. -/
def sumReserved : List Account → Nat
  | [] => 0
  | a :: rest => a.reserved + sumReserved rest

/--
  **Human-Locked Global Safety Invariant (`ValidKernel`)**:
  1. `globalInflight` matches the exact sum of all tenant `reserved` fields (Zero Drift).
  2. `globalInflight` never exceeds `clusterCapacity` (Hard Quota Ceiling).
  3. Available balances + locked reservations + settled revenue = `totalDeposited`
     (Exact Conservation of Token Credits).
-/
def ValidKernel (s : KernelState) : Prop :=
  s.globalInflight = sumReserved s.accounts.toList ∧
  s.globalInflight ≤ s.clusterCapacity ∧
  sumBalances s.accounts.toList + sumReserved s.accounts.toList + s.platformRevenue = s.totalDeposited

-- END VERIGATE SPEC

/-! ## 2. Verified O(1) State Transition Implementation -/

/-- Initialize a cluster with `numTenants` zeroed accounts and `capacity` token limit. -/
def initKernel (numTenants : Nat) (capacity : Nat) : KernelState :=
  { clusterCapacity := capacity
    totalDeposited := 0
    platformRevenue := 0
    globalInflight := 0
    accounts := Array.replicate numTenants {} }

/--
  O(1) state transition kernel.
  Uses direct array indexing (`s.accounts[tid]`), in-place refcounted array update
  (`s.accounts.set tid ...`), and O(1) arithmetic updates to `globalInflight`.
-/
def stepKernel (s : KernelState) (op : KernelOp) : Option KernelState :=
  match op with
  | .deposit tid amount =>
      if h : tid < s.accounts.size then
        let acct := s.accounts[tid]
        let acct' : Account := { acct with balance := acct.balance + amount }
        some { s with
          totalDeposited := s.totalDeposited + amount
          accounts := s.accounts.set tid acct' h }
      else
        none
  | .reserve tid maxTokens =>
      if h : tid < s.accounts.size then
        let acct := s.accounts[tid]
        if decide (maxTokens ≤ acct.balance ∧ s.globalInflight + maxTokens ≤ s.clusterCapacity) then
          let acct' : Account :=
            { balance := acct.balance - maxTokens
              reserved := acct.reserved + maxTokens }
          some { s with
            globalInflight := s.globalInflight + maxTokens
            accounts := s.accounts.set tid acct' h }
        else
          none
      else
        none
  | .settle tid reservedTokens actualUsed =>
      if h : tid < s.accounts.size then
        let acct := s.accounts[tid]
        if decide (actualUsed ≤ reservedTokens ∧ reservedTokens ≤ acct.reserved ∧ reservedTokens ≤ s.globalInflight) then
          let refund := reservedTokens - actualUsed
          let acct' : Account :=
            { balance := acct.balance + refund
              reserved := acct.reserved - reservedTokens }
          some { s with
            platformRevenue := s.platformRevenue + actualUsed
            globalInflight := s.globalInflight - reservedTokens
            accounts := s.accounts.set tid acct' h }
        else
          none
      else
        none
  | .cancel tid reservedTokens =>
      if h : tid < s.accounts.size then
        let acct := s.accounts[tid]
        if decide (reservedTokens ≤ acct.reserved ∧ reservedTokens ≤ s.globalInflight) then
          let acct' : Account :=
            { balance := acct.balance + reservedTokens
              reserved := acct.reserved - reservedTokens }
          some { s with
            globalInflight := s.globalInflight - reservedTokens
            accounts := s.accounts.set tid acct' h }
        else
          none
      else
        none

/-- Execute a batch of operations sequentially, aborting on any rejected step. -/
def runKernel (s : KernelState) : List KernelOp → Option KernelState
  | [] => some s
  | op :: rest =>
      match stepKernel s op with
      | none => none
      | some s' => runKernel s' rest

/-! ## 3. Ledger Sum & Array Update Lemmas -/

theorem sumBalances_replicate (n : Nat) :
    sumBalances (List.replicate n {}) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, sumBalances, ih]

theorem sumReserved_replicate (n : Nat) :
    sumReserved (List.replicate n {}) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, sumReserved, ih]

/-- Updating index `i` in a list shifts `sumBalances` by the exact per-account delta. -/
theorem sumBalances_set (xs : List Account) (i : Nat) (a' : Account) (h : i < xs.length) :
    sumBalances (xs.set i a') + xs[i].balance = sumBalances xs + a'.balance := by
  induction xs generalizing i with
  | nil => cases h
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp [List.set, sumBalances]
      omega
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ h
      have hSub := ih k hk
      simp only [List.set, sumBalances, List.getElem_cons_succ]
      omega

/-- Updating index `i` in a list shifts `sumReserved` by the exact per-account delta. -/
theorem sumReserved_set (xs : List Account) (i : Nat) (a' : Account) (h : i < xs.length) :
    sumReserved (xs.set i a') + xs[i].reserved = sumReserved xs + a'.reserved := by
  induction xs generalizing i with
  | nil => cases h
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp [List.set, sumReserved]
      omega
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ h
      have hSub := ih k hk
      simp only [List.set, sumReserved, List.getElem_cons_succ]
      omega

/-! ## 4. Main Soundness & Conservation Proofs -/

/-- Base case: `initKernel` satisfies all three safety & conservation clauses. -/
theorem initKernel_valid (numTenants capacity : Nat) :
    ValidKernel (initKernel numTenants capacity) := by
  unfold initKernel ValidKernel
  simp [Array.toList_replicate, sumBalances_replicate, sumReserved_replicate]

/--
  **Single-Step Soundness (`stepKernel_preserves_valid`)**:
  Every accepted O(1) transition preserves zero inflight drift, cluster capacity bounds,
  and exact token credit conservation.
-/
theorem stepKernel_preserves_valid {s s' : KernelState} {op : KernelOp}
    (hValid : ValidKernel s) (hStep : stepKernel s op = some s') :
    ValidKernel s' := by
  rcases hValid with ⟨hDrift, hCap, hCons⟩
  cases op with
  | deposit tid amount =>
    simp only [stepKernel] at hStep
    by_cases hIdx : tid < s.accounts.size
    · simp only [hIdx, ↓reduceDIte, Option.some.injEq] at hStep
      subst hStep
      have hLen : tid < s.accounts.toList.length := by simpa using hIdx
      let acct' : Account := { s.accounts[tid] with balance := s.accounts[tid].balance + amount }
      have hB := sumBalances_set s.accounts.toList tid acct' hLen
      have hR := sumReserved_set s.accounts.toList tid acct' hLen
      simp only [Array.getElem_toList hLen, acct'] at hB hR
      dsimp [ValidKernel]
      refine ⟨by omega, hCap, by omega⟩
    · simp [hIdx] at hStep
  | reserve tid maxTokens =>
    simp only [stepKernel] at hStep
    by_cases hIdx : tid < s.accounts.size
    · simp only [hIdx, ↓reduceDIte] at hStep
      by_cases hGuards : maxTokens ≤ s.accounts[tid].balance ∧ s.globalInflight + maxTokens ≤ s.clusterCapacity
      · simp [hGuards] at hStep
        rcases hGuards with ⟨hBalOk, hCapOk⟩
        subst hStep
        have hLen : tid < s.accounts.toList.length := by simpa using hIdx
        let acct' : Account :=
          { balance := s.accounts[tid].balance - maxTokens
            reserved := s.accounts[tid].reserved + maxTokens }
        have hB := sumBalances_set s.accounts.toList tid acct' hLen
        have hR := sumReserved_set s.accounts.toList tid acct' hLen
        simp only [Array.getElem_toList hLen, acct'] at hB hR
        dsimp [ValidKernel]
        refine ⟨by omega, hCapOk, by omega⟩
      · simp [hGuards] at hStep
    · simp [hIdx] at hStep
  | settle tid reservedTokens actualUsed =>
    simp only [stepKernel] at hStep
    by_cases hIdx : tid < s.accounts.size
    · simp only [hIdx, ↓reduceDIte] at hStep
      by_cases hGuards : actualUsed ≤ reservedTokens ∧ reservedTokens ≤ s.accounts[tid].reserved ∧ reservedTokens ≤ s.globalInflight
      · simp [hGuards] at hStep
        rcases hGuards with ⟨hUsedLe, hResLeAcct, hResLeGlobal⟩
        subst hStep
        have hLen : tid < s.accounts.toList.length := by simpa using hIdx
        let acct' : Account :=
          { balance := s.accounts[tid].balance + (reservedTokens - actualUsed)
            reserved := s.accounts[tid].reserved - reservedTokens }
        have hB := sumBalances_set s.accounts.toList tid acct' hLen
        have hR := sumReserved_set s.accounts.toList tid acct' hLen
        simp only [Array.getElem_toList hLen, acct'] at hB hR
        dsimp [ValidKernel]
        refine ⟨by omega, by omega, by omega⟩
      · simp [hGuards] at hStep
    · simp [hIdx] at hStep
  | cancel tid reservedTokens =>
    simp only [stepKernel] at hStep
    by_cases hIdx : tid < s.accounts.size
    · simp only [hIdx, ↓reduceDIte] at hStep
      by_cases hGuards : reservedTokens ≤ s.accounts[tid].reserved ∧ reservedTokens ≤ s.globalInflight
      · simp [hGuards] at hStep
        rcases hGuards with ⟨hResLeAcct, hResLeGlobal⟩
        subst hStep
        have hLen : tid < s.accounts.toList.length := by simpa using hIdx
        let acct' : Account :=
          { balance := s.accounts[tid].balance + reservedTokens
            reserved := s.accounts[tid].reserved - reservedTokens }
        have hB := sumBalances_set s.accounts.toList tid acct' hLen
        have hR := sumReserved_set s.accounts.toList tid acct' hLen
        simp only [Array.getElem_toList hLen, acct'] at hB hR
        dsimp [ValidKernel]
        refine ⟨by omega, by omega, by omega⟩
      · simp [hGuards] at hStep
    · simp [hIdx] at hStep

/-- Multi-step batch execution preserves `ValidKernel`. -/
theorem runKernel_preserves_valid {s s' : KernelState} {ops : List KernelOp}
    (hValid : ValidKernel s) (hRun : runKernel s ops = some s') :
    ValidKernel s' := by
  induction ops generalizing s with
  | nil =>
    simp only [runKernel, Option.some.injEq] at hRun
    subst hRun
    exact hValid
  | cons op rest ih =>
    simp only [runKernel] at hRun
    cases hStep : stepKernel s op with
    | none => simp [hStep] at hRun
    | some sMid =>
      simp only [hStep] at hRun
      exact ih (stepKernel_preserves_valid hValid hStep) hRun

/-! ## 5. Mandatory Non-Vacuity Witness (`non_vacuous`) -/

/--
  **Mandatory Non-Vacuity Witness (`non_vacuous`)**:
  Proves that `stepKernel` is not a vacuous always-`none` stub: a multi-tenant workload
  depositing credits, reserving quota across two tenants, settling partial usage, and
  refunding unused quota succeeds (`some`) and produces positive settled revenue!
-/
theorem non_vacuous :
    ∃ finalState : KernelState,
      runKernel (initKernel 2 100)
        [ .deposit 0 80
        , .deposit 1 50
        , .reserve 0 60
        , .reserve 1 30
        , .settle 0 60 45
        , .cancel 1 30
        ] = some finalState ∧
      finalState.platformRevenue = 45 ∧
      finalState.globalInflight = 0 ∧
      finalState.totalDeposited = 130 := by
  refine ⟨{
    clusterCapacity := 100
    totalDeposited := 130
    platformRevenue := 45
    globalInflight := 0
    accounts := #[{ balance := 35, reserved := 0 }, { balance := 50, reserved := 0 }]
  }, ?_⟩
  decide

end VeriGateLab
