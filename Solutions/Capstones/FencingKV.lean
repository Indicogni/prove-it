/-
  Capstone 2 — FencingKV (Model Solution)
  Distributed Fencing-Token Lease Protocol & Crash-Safe Tombstone KV Store

  Gear 1: Bounded BFS model checker catching stale-leader split-brain on unfenced storage.
  Gear 2: Unbounded inductive invariant proving fencing blocks stale writes across arbitrary
          network duplication/reordering + stuttering refinement of tombstone compaction
          against a 15-line abstract `SpecKV`.
-/
set_option autoImplicit false

namespace FencingKV

/-! ## 1. The 15-Line Abstract Key-Value Specification (`SpecKV`) -/

abbrev SpecKV := String → Option String

def SpecKV.empty : SpecKV := fun _ => none

def SpecKV.get (m : SpecKV) (k : String) : Option String := m k

def SpecKV.put (m : SpecKV) (k v : String) : SpecKV :=
  fun k' => if k' == k then some v else m k'

def SpecKV.del (m : SpecKV) (k : String) : SpecKV :=
  fun k' => if k' == k then none else m k'

/-! ## 2. Crash-Safe Concrete Tombstone KV Store (`TombstoneKV`) -/

/-- Log-structured storage entry: either a live value or a deletion tombstone. -/
inductive Entry where
  | val (v : String)
  | tombstone
  deriving Repr, DecidableEq

/-- Append-only log-structured table ordered from newest entry (head) to oldest (tail). -/
abbrev TombstoneKV := List (String × Entry)

/-- Point lookup scanning from newest entry to oldest; tombstones mask older values. -/
def TombstoneKV.get (db : TombstoneKV) (k : String) : Option String :=
  match db with
  | [] => none
  | (k', entry) :: rest =>
      if k' == k then
        match entry with
        | .val v => some v
        | .tombstone => none
      else
        TombstoneKV.get rest k

/-- Append-only write. -/
def TombstoneKV.put (db : TombstoneKV) (k v : String) : TombstoneKV :=
  (k, .val v) :: db

/-- Append-only crash-safe delete via tombstone insertion. -/
def TombstoneKV.del (db : TombstoneKV) (k : String) : TombstoneKV :=
  (k, .tombstone) :: db

/-- Single-pass deduplicating compaction helper tracking already-seen newer keys. -/
def compactAux (seen : List String) : TombstoneKV → TombstoneKV
  | [] => []
  | (k, entry) :: rest =>
      if decide (k ∈ seen) then
        compactAux seen rest
      else
        match entry with
        | .val v => (k, .val v) :: compactAux (k :: seen) rest
        | .tombstone => compactAux (k :: seen) rest

/--
  Bottommost compaction: drops shadowed historical versions and purges tombstones
  without resurrecting older overwritten values.
-/
def TombstoneKV.compact (db : TombstoneKV) : TombstoneKV :=
  compactAux [] db

/-- Abstraction function (refinement mapping) from concrete `TombstoneKV` to `SpecKV`. -/
def absKV (db : TombstoneKV) : SpecKV :=
  fun k => TombstoneKV.get db k

/-! ## 3. Distributed Lease + Network + Storage Protocol -/

/-- An in-flight write/delete packet carrying the sender's lease fencing token. -/
inductive Payload where
  | put (key : String) (val : String)
  | del (key : String)
  deriving Repr, DecidableEq

structure Packet where
  token : Nat
  payload : Payload
  deriving Repr, DecidableEq

/-- Global state of lease service, asynchronous network bag, and storage node. -/
structure DistState where
  latestIssued : Nat := 0
  storageFence : Nat := 0
  committedEpoch : Nat := 0
  highWaterEpoch : Nat := 0
  inFlight : List Packet := []
  store : TombstoneKV := []
  deriving Repr, DecidableEq

def initDistState : DistState := {}

/-- Apply a packet's KV payload to a `TombstoneKV`. -/
def applyPayload (db : TombstoneKV) (p : Payload) : TombstoneKV :=
  match p with
  | .put k v => TombstoneKV.put db k v
  | .del k => TombstoneKV.del db k

/--
  Safety predicate: storage never regresses its committed epoch below the highest
  epoch ever committed (i.e., no delayed zombie leader overwrites a newer leader).
-/
def NoSplitBrainOverwrite (s : DistState) : Bool :=
  decide (s.committedEpoch = s.highWaterEpoch)

/-! ## 4. Gear 1 — Bounded BFS Counterexample Finder (Buggy Unfenced Storage) -/

/-- Actions explored by the bounded model checker on concrete test payloads. -/
inductive BuggyStep where
  | acquireAndSendPut (key : String) (val : String)
  | deliverUnfenced (idx : Nat)
  deriving Repr, DecidableEq

/-- Execute one step against a BUGGY storage server that ignores fencing tokens! -/
def stepBuggy (s : DistState) (act : BuggyStep) : Option DistState :=
  match act with
  | .acquireAndSendPut k v =>
      let tok := s.latestIssued + 1
      let pkt : Packet := { token := tok, payload := .put k v }
      some { s with
        latestIssued := tok
        inFlight := pkt :: s.inFlight }
  | .deliverUnfenced idx =>
      match s.inFlight[idx]? with
      | none => none
      | some pkt =>
          -- BUG: Storage applies `pkt` without checking `s.storageFence ≤ pkt.token`!
          let rest := s.inFlight.eraseIdx idx
          some { s with
            committedEpoch := pkt.token
            highWaterEpoch := Nat.max s.highWaterEpoch pkt.token
            inFlight := rest
            store := applyPayload s.store pkt.payload }

/-- Execute a trace of `BuggyStep`s from `s`. -/
def runBuggyTrace (s : DistState) : List BuggyStep → Option DistState
  | [] => some s
  | act :: rest =>
      match stepBuggy s act with
      | none => none
      | some s' => runBuggyTrace s' rest

/-- Candidate steps from a state during bounded exploration (up to 2 leader epochs). -/
def candidateBuggySteps (s : DistState) : List BuggyStep :=
  let issueSteps :=
    if s.latestIssued < 2 then
      [.acquireAndSendPut "cfg" s!"leader-{s.latestIssued + 1}"]
    else
      []
  let deliverSteps := (List.range s.inFlight.length).map BuggyStep.deliverUnfenced
  issueSteps ++ deliverSteps

/-- Fuel-bounded BFS searching for a trace that violates `NoSplitBrainOverwrite`. -/
def bfsSearch (fuel : Nat) (visited : List DistState)
    (queue : List (DistState × List BuggyStep)) : Option (List BuggyStep) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      match queue with
      | [] => none
      | (s, trace) :: rest =>
          if !NoSplitBrainOverwrite s then
            some trace.reverse
          else
            let nextPairs := (candidateBuggySteps s).filterMap fun act =>
              match stepBuggy s act with
              | none => none
              | some s' =>
                  if decide (s' ∈ visited) then none else some (s', act :: trace)
            let newVisited := (nextPairs.map Prod.fst) ++ visited
            bfsSearch fuel' newVisited (rest ++ nextPairs)

/-- Run bounded BFS from `initDistState` to catch the unfenced split-brain bug. -/
def findSplitBrainCounterexample : Option (List BuggyStep) :=
  bfsSearch 40 [initDistState] [(initDistState, [])]

/-- Boolean verifier checking that an optional trace witnesses a genuine split-brain overwrite. -/
def isValidSplitBrainWitness (optTrace : Option (List BuggyStep)) : Bool :=
  match optTrace with
  | none => false
  | some trace =>
      match runBuggyTrace initDistState trace with
      | none => false
      | some finalState =>
          !NoSplitBrainOverwrite finalState &&
          decide (TombstoneKV.get finalState.store "cfg" = some "leader-1")

/--
  **Gear 1 Theorem**: Bounded BFS automatically discovers a concrete split-brain
  execution on unfenced storage where delayed leader-1 overwrites leader-2!
-/
theorem gear1_split_brain_caught :
    isValidSplitBrainWitness findSplitBrainCounterexample = true := by
  decide

/-! ## 5. Gear 2A — Unbounded Fencing-Token Safety Invariant -/

/-- Unbounded asynchronous protocol actions including duplication, reordering, and compaction. -/
inductive ProtocolAction where
  | issuePacket (payload : Payload)
  | duplicatePacket (pkt : Packet)
  | reorderNetwork (newBag : List Packet)
  | deliverFenced (pkt : Packet)
  | compactStorage
  deriving Repr, DecidableEq

/-- Executable fenced delivery step (also used by the differential fuzzing oracle). -/
def deliverFencedExec (s : DistState) (pkt : Packet) : DistState :=
  if decide (s.storageFence ≤ pkt.token) then
    { s with
      storageFence := pkt.token
      committedEpoch := pkt.token
      highWaterEpoch := max s.highWaterEpoch pkt.token
      store := applyPayload s.store pkt.payload }
  else
    s

/-- Unbounded transition relation for the fenced distributed KV system. -/
inductive Step : DistState → ProtocolAction → DistState → Prop where
  | issue {s : DistState} (payload : Payload) :
      Step s (.issuePacket payload)
        { s with
          latestIssued := s.latestIssued + 1
          inFlight := { token := s.latestIssued + 1, payload := payload } :: s.inFlight }
  | duplicate {s : DistState} {pkt : Packet} (hMem : pkt ∈ s.inFlight) :
      Step s (.duplicatePacket pkt)
        { s with inFlight := pkt :: s.inFlight }
  | reorder {s : DistState} {newBag : List Packet}
      (hSub : ∀ p ∈ newBag, p ∈ s.inFlight) :
      Step s (.reorderNetwork newBag)
        { s with inFlight := newBag }
  | deliver {s : DistState} {pkt : Packet} (hMem : pkt ∈ s.inFlight) :
      Step s (.deliverFenced pkt) (deliverFencedExec s pkt)
  | compact {s : DistState} :
      Step s .compactStorage
        { s with store := TombstoneKV.compact s.store }

/-- Multi-step reachability from `initDistState`. -/
inductive Reachable : DistState → Prop where
  | init : Reachable initDistState
  | step {s s' : DistState} {act : ProtocolAction} :
      Reachable s → Step s act s' → Reachable s'

/--
  **Strengthened Inductive Invariant**:
  Relates `committedEpoch` and `highWaterEpoch` directly to `storageFence`, and bounds
  every in-flight packet's token by `latestIssued`.
-/
def FencingInv (s : DistState) : Prop :=
  s.committedEpoch = s.storageFence ∧
  s.highWaterEpoch = s.storageFence ∧
  s.storageFence ≤ s.latestIssued ∧
  ∀ pkt ∈ s.inFlight, pkt.token ≤ s.latestIssued

theorem init_fencingInv : FencingInv initDistState := by
  refine ⟨rfl, rfl, Nat.le_refl 0, ?_⟩
  intro pkt hMem
  cases hMem

theorem step_preserves_fencingInv {s s' : DistState} {act : ProtocolAction}
    (hInv : FencingInv s) (hStep : Step s act s') :
    FencingInv s' := by
  rcases hInv with ⟨hComm, hHigh, hFenceLe, hPackets⟩
  cases hStep with
  | issue payload =>
    dsimp [FencingInv]
    refine ⟨hComm, hHigh, by omega, ?_⟩
    intro pkt hMem
    simp only [List.mem_cons] at hMem
    rcases hMem with rfl | hOld
    · dsimp; omega
    · have := hPackets pkt hOld
      omega
  | @duplicate pkt hMem =>
    dsimp [FencingInv]
    refine ⟨hComm, hHigh, hFenceLe, ?_⟩
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hOld
    · exact hPackets q hMem
    · exact hPackets q hOld
  | @reorder newBag hSub =>
    dsimp [FencingInv]
    refine ⟨hComm, hHigh, hFenceLe, ?_⟩
    intro q hq
    exact hPackets q (hSub q hq)
  | @deliver pkt hMem =>
    unfold deliverFencedExec
    by_cases hOk : s.storageFence ≤ pkt.token
    · simp only [hOk, decide_true, ↓reduceIte]
      dsimp [FencingInv]
      have hPktLe : pkt.token ≤ s.latestIssued := hPackets pkt hMem
      refine ⟨rfl, ?_, hPktLe, hPackets⟩
      omega
    · simp only [hOk, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hComm, hHigh, hFenceLe, hPackets⟩
  | compact =>
    exact ⟨hComm, hHigh, hFenceLe, hPackets⟩

theorem reachable_fencingInv {s : DistState} (hReach : Reachable s) :
    FencingInv s := by
  induction hReach with
  | init => exact init_fencingInv
  | step _ hStep ih => exact step_preserves_fencingInv ih hStep

/--
  **Gear 2A Main Safety Theorem**:
  Every reachable state of the fenced protocol—across unbounded epochs and arbitrary
  packet duplication, delay, and reordering—satisfies `NoSplitBrainOverwrite`.
-/
theorem reachable_no_split_brain {s : DistState} (hReach : Reachable s) :
    NoSplitBrainOverwrite s = true := by
  rcases reachable_fencingInv hReach with ⟨hComm, hHigh, _, _⟩
  unfold NoSplitBrainOverwrite
  rw [hComm, hHigh]
  simp

/-- Any stale packet strictly older than `storageFence` is rejected without mutating state. -/
theorem stale_packet_rejected (s : DistState) (pkt : Packet)
    (hStale : pkt.token < s.storageFence) :
    deliverFencedExec s pkt = s := by
  unfold deliverFencedExec
  have hNotLe : ¬ (s.storageFence ≤ pkt.token) := by omega
  simp [hNotLe]

/-! ## 6. Gear 2B — Tombstone Compaction Stuttering Refinement against `SpecKV` -/

theorem absKV_empty : absKV [] = SpecKV.empty := by
  rfl

theorem absKV_put (db : TombstoneKV) (k v : String) :
    absKV (TombstoneKV.put db k v) = SpecKV.put (absKV db) k v := by
  funext k'
  simp only [absKV, TombstoneKV.put, TombstoneKV.get, SpecKV.put]
  by_cases h : k = k'
  · subst h
    simp
  · have h1 : (k == k') = false := beq_eq_false_iff_ne.mpr h
    have h2 : (k' == k) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
    simp [h1, h2]

theorem absKV_del (db : TombstoneKV) (k : String) :
    absKV (TombstoneKV.del db k) = SpecKV.del (absKV db) k := by
  funext k'
  simp only [absKV, TombstoneKV.del, TombstoneKV.get, SpecKV.del]
  by_cases h : k = k'
  · subst h
    simp
  · have h1 : (k == k') = false := beq_eq_false_iff_ne.mpr h
    have h2 : (k' == k) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
    simp [h1, h2]

/-- Helper 1: Keys already recorded in `seen` are absent from `compactAux seen db`. -/
theorem get_compactAux_of_mem (db : TombstoneKV) (seen : List String) (k : String)
    (hMem : k ∈ seen) :
    TombstoneKV.get (compactAux seen db) k = none := by
  induction db generalizing seen with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨k', entry⟩
    simp only [compactAux]
    by_cases hk' : k' ∈ seen
    · simp only [hk', decide_true, ↓reduceIte]
      exact ih seen hMem
    · simp only [hk', decide_false, Bool.false_eq_true, ↓reduceIte]
      have hNe : (k' == k) = false := by
        simp only [beq_eq_false_iff_ne]
        intro hEq
        subst hEq
        exact hk' hMem
      cases entry with
      | val v =>
        simp only [TombstoneKV.get, hNe, Bool.false_eq_true, ↓reduceIte]
        exact ih (k' :: seen) (List.mem_cons_of_mem k' hMem)
      | tombstone =>
        exact ih (k' :: seen) (List.mem_cons_of_mem k' hMem)

/-- Helper 2: Keys not in `seen` preserve their exact lookup result across `compactAux`. -/
theorem get_compactAux_of_not_mem (db : TombstoneKV) (seen : List String) (k : String)
    (hNotMem : k ∉ seen) :
    TombstoneKV.get (compactAux seen db) k = TombstoneKV.get db k := by
  induction db generalizing seen with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨k', entry⟩
    simp only [compactAux]
    by_cases hEq : k' = k
    · subst hEq
      simp only [hNotMem, decide_false, Bool.false_eq_true, ↓reduceIte,
                 TombstoneKV.get, beq_self_eq_true]
      cases entry with
      | val v => simp [TombstoneKV.get]
      | tombstone => exact get_compactAux_of_mem rest (k' :: seen) k' (.head seen)
    · have hBeqFalse : (k' == k) = false := beq_eq_false_iff_ne.mpr hEq
      by_cases hk' : k' ∈ seen
      · simp only [hk', decide_true, ↓reduceIte, TombstoneKV.get, hBeqFalse, Bool.false_eq_true]
        exact ih seen hNotMem
      · have hNotMem' : k ∉ k' :: seen := by
          simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm hEq, hNotMem⟩
        simp only [hk', decide_false, Bool.false_eq_true, ↓reduceIte]
        cases entry with
        | val v =>
          simp only [TombstoneKV.get, hBeqFalse, Bool.false_eq_true, ↓reduceIte]
          exact ih (k' :: seen) hNotMem'
        | tombstone =>
          simp only [TombstoneKV.get, hBeqFalse, Bool.false_eq_true, ↓reduceIte]
          exact ih (k' :: seen) hNotMem'

/--
  **Gear 2B Main Refinement Theorem (`compact_stutters`)**:
  Tombstone compaction is an exact stuttering step with respect to `SpecKV`:
  every key lookup before and after compaction returns the identical `Option String`,
  with zero zombie value resurrection!
-/
theorem compact_stutters (db : TombstoneKV) :
    absKV (TombstoneKV.compact db) = absKV db := by
  funext k
  exact get_compactAux_of_not_mem db [] k (by simp)

/-- Compaction genuinely eliminates every `.tombstone` entry from physical storage. -/
theorem compactAux_no_tombstones (db : TombstoneKV) (seen : List String) :
    ∀ k, (k, Entry.tombstone) ∉ compactAux seen db := by
  induction db generalizing seen with
  | nil => simp [compactAux]
  | cons hd rest ih =>
    rcases hd with ⟨k', entry⟩
    intro k
    simp only [compactAux]
    by_cases hk' : k' ∈ seen
    · simp only [hk', decide_true, ↓reduceIte]
      exact ih seen k
    · simp only [hk', decide_false, Bool.false_eq_true, ↓reduceIte]
      cases entry with
      | val v =>
        simp only [List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false, false_or]
        exact ih (k' :: seen) k
      | tombstone =>
        exact ih (k' :: seen) k

theorem compact_purges_all_tombstones (db : TombstoneKV) (k : String) :
    (k, Entry.tombstone) ∉ TombstoneKV.compact db :=
  compactAux_no_tombstones db [] k

/-! ## 7. Non-Vacuity Witness -/

/-- Non-vacuity: The fenced protocol accepts monotonically newer writes, deletes, and compacts. -/
theorem non_vacuous_fenced_lifecycle :
    let s1 := deliverFencedExec initDistState { token := 1, payload := .put "k" "v1" }
    let s2 := deliverFencedExec s1 { token := 2, payload := .del "k" }
    let compacted := TombstoneKV.compact s2.store
    NoSplitBrainOverwrite s2 = true ∧
    TombstoneKV.get compacted "k" = none ∧
    compacted = [] := by
  decide

end FencingKV
