/-
  Capstone 4 — VeriGateLab (Learner Starter)
  AI Proof-Carrying Code Challenge: Multi-Tenant Token Quota & Settlement Kernel

  Read `capstones/verigate/README.md` for the Socratic brief and roadmap,
  and `capstones/verigate/DESIGN.md` for proof-engineering guidance.

  IMPORTANT: Do NOT edit anything between `BEGIN VERIGATE SPEC` and `END VERIGATE SPEC`!
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

/-! ## 2. O(1) State Transition Implementation -/

def initKernel (numTenants : Nat) (capacity : Nat) : KernelState :=
  { clusterCapacity := capacity
    totalDeposited := 0
    platformRevenue := 0
    globalInflight := 0
    accounts := Array.replicate numTenants {} }

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

def runKernel (s : KernelState) : List KernelOp → Option KernelState
  | [] => some s
  | op :: rest =>
      match stepKernel s op with
      | none => none
      | some s' => runKernel s' rest

/-! ## 3. Verification Milestones -/

/--
  Milestone 1a (**List Update Delta Lemma — Balances**):
  Prove by induction on `xs generalizing i` that overwriting `xs[i]` shifts `sumBalances`
  by the exact difference between `a'.balance` and `xs[i].balance`.
-/
theorem sumBalances_set (xs : List Account) (i : Nat) (a' : Account) (h : i < xs.length) :
    sumBalances (xs.set i a') + xs[i].balance = sumBalances xs + a'.balance := by
  sorry

/-- Milestone 1b (**List Update Delta Lemma — Reservations**): -/
theorem sumReserved_set (xs : List Account) (i : Nat) (a' : Account) (h : i < xs.length) :
    sumReserved (xs.set i a') + xs[i].reserved = sumReserved xs + a'.reserved := by
  sorry

/-- Milestone 2a (**Initialization Validity**): -/
theorem initKernel_valid (numTenants capacity : Nat) :
    ValidKernel (initKernel numTenants capacity) := by
  sorry

/--
  Milestone 2b (**Single-Step Conservation & Quota Safety**):
  Prove every accepted O(1) `stepKernel` transition preserves `ValidKernel`.
-/
theorem stepKernel_preserves_valid {s s' : KernelState} {op : KernelOp}
    (hValid : ValidKernel s) (hStep : stepKernel s op = some s') :
    ValidKernel s' := by
  sorry

/-- Milestone 2c (**Batch Execution Soundness**): -/
theorem runKernel_preserves_valid {s s' : KernelState} {ops : List KernelOp}
    (hValid : ValidKernel s) (hRun : runKernel s ops = some s') :
    ValidKernel s' := by
  sorry

/--
  Milestone 3 (**Mandatory Non-Vacuity Witness `non_vacuous`**):
  Required by `lake exe verigate`! Exhibit the concrete `finalState` produced by
  running this multi-tenant workload and discharge with `decide`.
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
  sorry

end VeriGateLab
