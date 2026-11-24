set_option autoImplicit false

/-!
# Checkpoint 2 (Closed-Notes): Crash-Safe Idempotent Write-Ahead Ledger (Reference Solutions)

This checkpoint synthesizes Part II (Chapters 5–8):
- Chapter 5: Logical contracts (`→`, `∧`, `∀`) and structured proof composition.
- Chapter 6: Non-brittle control-flow proofs (`fun_cases`, `simp only`, `omega`, `grind`).
- Chapter 7: Modular helper lemmas and exact preconditions.
- Chapter 8: Inductive invariants over unbounded TLA+-style `Reachable` traces.
-/

namespace Cp2

/-!
## 1. Write-Ahead Ledger Data Model
-/

structure WalEntry where
  txId   : Nat
  amount : Nat
  deriving Repr, DecidableEq

structure LedgerState where
  vaultBalance    : Nat
  clearingBalance : Nat
  appliedIds      : List Nat
  deriving Repr, DecidableEq

@[grind =]
def LedgerState.totalFunds (s : LedgerState) : Nat :=
  s.vaultBalance + s.clearingBalance

/-!
## 2. Idempotent Entry Application
-/

/--
Task 2.1: Implement `applyEntry` with crash-safe idempotency:
- If `entry.txId ∈ s.appliedIds`, return `s` unchanged (duplicate WAL replay).
- Otherwise, if `entry.amount ≤ s.vaultBalance`, move `entry.amount` from
  `vaultBalance` to `clearingBalance` and record `entry.txId :: s.appliedIds`.
- Otherwise (insufficient vault funds), leave balances unchanged and record
  `entry.txId :: s.appliedIds` so the rejected transaction ID is still deduplicated.
-/
@[grind =]
def applyEntry (s : LedgerState) (entry : WalEntry) : LedgerState :=
  if entry.txId ∈ s.appliedIds then
    s
  else if entry.amount ≤ s.vaultBalance then
    { vaultBalance    := s.vaultBalance - entry.amount
      clearingBalance := s.clearingBalance + entry.amount
      appliedIds      := entry.txId :: s.appliedIds }
  else
    { s with appliedIds := entry.txId :: s.appliedIds }

#guard applyEntry { vaultBalance := 500, clearingBalance := 100, appliedIds := [] } { txId := 1, amount := 200 } ==
  { vaultBalance := 300, clearingBalance := 300, appliedIds := [1] }

#guard applyEntry { vaultBalance := 300, clearingBalance := 300, appliedIds := [1] } { txId := 1, amount := 200 } ==
  { vaultBalance := 300, clearingBalance := 300, appliedIds := [1] }

/--
Task 2.2a (Helper Lemma for Resilient Proofs):
Prove that after `applyEntry s entry`, `entry.txId` is guaranteed to be a member
of `(applyEntry s entry).appliedIds`.
-/
theorem applyEntry_marks_seen (s : LedgerState) (entry : WalEntry) :
    entry.txId ∈ (applyEntry s entry).appliedIds := by
  fun_cases applyEntry s entry
  · assumption
  · simp only [List.mem_cons, true_or]
  · simp only [List.mem_cons, true_or]

/--
Helper: when `entry.txId ∈ s.appliedIds`, `applyEntry s entry` returns `s`.
-/
theorem applyEntry_of_seen (s : LedgerState) (entry : WalEntry)
    (hSeen : entry.txId ∈ s.appliedIds) :
    applyEntry s entry = s := by
  unfold applyEntry
  simp only [hSeen, ↓reduceIte]

/--
Task 2.2b (Crash-Recovery Replay Idempotency):
Combine `applyEntry_of_seen` and `applyEntry_marks_seen` to prove that replaying
the same `WalEntry` a second time is a strict no-op—regardless of which branch
the first application took!
-/
theorem applyEntry_idempotent (s : LedgerState) (entry : WalEntry) :
    applyEntry (applyEntry s entry) entry = applyEntry s entry :=
  applyEntry_of_seen (applyEntry s entry) entry (applyEntry_marks_seen s entry)

/--
Task 2.3 (Single-Step Conservation of Funds):
Prove that `applyEntry` neither creates nor destroys money across `vaultBalance`
and `clearingBalance`.
-/
theorem applyEntry_conserves_funds (s : LedgerState) (entry : WalEntry) :
    (applyEntry s entry).totalFunds = s.totalFunds := by
  fun_cases applyEntry s entry <;> simp only [LedgerState.totalFunds] <;> omega

/-!
## 3. Multi-Entry WAL Replay & Unbounded Reachability
-/

def replayWal : LedgerState → List WalEntry → LedgerState
  | s, []            => s
  | s, entry :: rest => replayWal (applyEntry s entry) rest

/--
Task 2.4: Prove by induction on `wal` (`induction wal generalizing s`) that
replaying any arbitrarily long write-ahead log batch conserves `totalFunds`.
-/
theorem replayWal_conserves_funds (wal : List WalEntry) (s : LedgerState) :
    (replayWal s wal).totalFunds = s.totalFunds := by
  induction wal generalizing s with
  | nil => rfl
  | cons entry rest ih =>
    dsimp [replayWal]
    rw [ih (applyEntry s entry)]
    exact applyEntry_conserves_funds s entry

/-!
## 4. Gear 2: TLA+ Unbounded Crash/Replay Protocol
-/

def LedgerInit (initialVault : Nat) (s : LedgerState) : Prop :=
  s = { vaultBalance    := initialVault
        clearingBalance := 0
        appliedIds      := [] }

inductive LedgerNext : LedgerState → LedgerState → Prop where
  | processEntry (s : LedgerState) (entry : WalEntry) :
      LedgerNext s (applyEntry s entry)
  | replayBatch (s : LedgerState) (wal : List WalEntry) :
      LedgerNext s (replayWal s wal)

inductive LedgerReachable (initialVault : Nat) : LedgerState → Prop where
  | init {s : LedgerState} (hInit : LedgerInit initialVault s) :
      LedgerReachable initialVault s
  | step {s s' : LedgerState}
      (hReach : LedgerReachable initialVault s)
      (hNext : LedgerNext s s') :
      LedgerReachable initialVault s'

/--
Task 2.5: Prove that across *every* reachable ledger state—under arbitrarily many
new transactions and crash-recovery WAL batch replays—total funds equal `initialVault`.
-/
theorem reachable_ledger_conserves (initialVault : Nat) {s : LedgerState}
    (hReach : LedgerReachable initialVault s) :
    s.totalFunds = initialVault := by
  induction hReach with
  | init hInit =>
    rw [hInit]
    simp only [LedgerState.totalFunds]
    omega
  | step _ hNext ih =>
    cases hNext with
    | processEntry entry =>
      rw [applyEntry_conserves_funds, ih]
    | replayBatch wal =>
      rw [replayWal_conserves_funds, ih]

/-- info: 'Cp2.applyEntry_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms applyEntry_idempotent

/-- info: 'Cp2.reachable_ledger_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reachable_ledger_conserves

end Cp2
