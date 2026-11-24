set_option autoImplicit false

/-!
# Checkpoint 2 (Closed-Notes): Crash-Safe Idempotent Write-Ahead Ledger

Complete this checkpoint without consulting Chapters 5–8 or `Solutions/`.
You are building and verifying a settlement ledger backed by a write-ahead log
(WAL) that recovers from crashes by replaying log entries:
1. Every applied or rejected `WalEntry` records its `txId` in `appliedIds` so
   duplicate replays become strict no-ops.
2. Replaying any `WalEntry` is idempotent: `applyEntry (applyEntry s e) e = applyEntry s e`.
3. Neither single entries, batch WAL replays, nor unbounded sequences of crash
   recoveries ever create or destroy funds (`vaultBalance + clearingBalance`).
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
- If `entry.txId ∈ s.appliedIds`, return `s` unchanged.
- Otherwise, if `entry.amount ≤ s.vaultBalance`, deduct `entry.amount` from
  `vaultBalance`, add `entry.amount` to `clearingBalance`, and prepend
  `entry.txId :: s.appliedIds`.
- Otherwise (insufficient vault funds), leave both balances unchanged and prepend
  `entry.txId :: s.appliedIds` so the rejected `txId` is also deduplicated.
-/
def applyEntry (s : LedgerState) (entry : WalEntry) : LedgerState :=
  sorry

-- PREDICT: Why is recording `entry.txId :: s.appliedIds` even when `vaultBalance < entry.amount`
-- helpful if `vaultBalance` later receives a deposit during multi-entry WAL replay?
example :
    applyEntry { vaultBalance := 500, clearingBalance := 100, appliedIds := [] } { txId := 1, amount := 200 } =
    { vaultBalance := 300, clearingBalance := 300, appliedIds := [1] } := by
  sorry

/--
Task 2.2a: Prove that after `applyEntry s entry`, `entry.txId` belongs to
`(applyEntry s entry).appliedIds`.
-/
theorem applyEntry_marks_seen (s : LedgerState) (entry : WalEntry) :
    entry.txId ∈ (applyEntry s entry).appliedIds := by
  sorry

/--
Helper for Task 2.2b: Prove that when `entry.txId ∈ s.appliedIds`, `applyEntry`
returns `s` unchanged.
-/
theorem applyEntry_of_seen (s : LedgerState) (entry : WalEntry)
    (hSeen : entry.txId ∈ s.appliedIds) :
    applyEntry s entry = s := by
  sorry

/--
Task 2.2b (Crash-Recovery Replay Idempotency):
Prove that replaying the same `WalEntry` a second time is a strict no-op.
-/
theorem applyEntry_idempotent (s : LedgerState) (entry : WalEntry) :
    applyEntry (applyEntry s entry) entry = applyEntry s entry := by
  sorry

/--
Task 2.3 (Single-Step Conservation of Funds):
Prove that `applyEntry` preserves `LedgerState.totalFunds`.
-/
theorem applyEntry_conserves_funds (s : LedgerState) (entry : WalEntry) :
    (applyEntry s entry).totalFunds = s.totalFunds := by
  sorry

/-!
## 3. Multi-Entry WAL Replay & Unbounded Reachability
-/

def replayWal : LedgerState → List WalEntry → LedgerState
  | s, []            => s
  | s, entry :: rest => replayWal (applyEntry s entry) rest

/--
Task 2.4: Prove by induction on `wal` (`induction wal generalizing s`) that
replaying any WAL batch preserves `totalFunds`.
-/
theorem replayWal_conserves_funds (wal : List WalEntry) (s : LedgerState) :
    (replayWal s wal).totalFunds = s.totalFunds := by
  sorry

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
transactions and crash-recovery WAL batch replays—total funds equal `initialVault`.
-/
theorem reachable_ledger_conserves (initialVault : Nat) {s : LedgerState}
    (hReach : LedgerReachable initialVault s) :
    s.totalFunds = initialVault := by
  sorry

end Cp2
