/-
  Capstone 2 — FencingKV (Learner Starter)
  Distributed Fencing-Token Lease Protocol & Crash-Safe Tombstone KV Store

  Read `capstones/fencing-kv/README.md` for the Socratic brief and roadmap,
  and `capstones/fencing-kv/DESIGN.md` for proof-engineering guidance.

  Your mission: replace every `sorry` below with a complete kernel-checked proof!
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

inductive Entry where
  | val (v : String)
  | tombstone
  deriving Repr, DecidableEq

abbrev TombstoneKV := List (String × Entry)

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

def TombstoneKV.put (db : TombstoneKV) (k v : String) : TombstoneKV :=
  (k, .val v) :: db

def TombstoneKV.del (db : TombstoneKV) (k : String) : TombstoneKV :=
  (k, .tombstone) :: db

def compactAux (seen : List String) : TombstoneKV → TombstoneKV
  | [] => []
  | (k, entry) :: rest =>
      if decide (k ∈ seen) then
        compactAux seen rest
      else
        match entry with
        | .val v => (k, .val v) :: compactAux (k :: seen) rest
        | .tombstone => compactAux (k :: seen) rest

def TombstoneKV.compact (db : TombstoneKV) : TombstoneKV :=
  compactAux [] db

def absKV (db : TombstoneKV) : SpecKV :=
  fun k => TombstoneKV.get db k

/-! ## 3. Distributed Lease + Network + Storage Protocol -/

inductive Payload where
  | put (key : String) (val : String)
  | del (key : String)
  deriving Repr, DecidableEq

structure Packet where
  token : Nat
  payload : Payload
  deriving Repr, DecidableEq

structure DistState where
  latestIssued : Nat := 0
  storageFence : Nat := 0
  committedEpoch : Nat := 0
  highWaterEpoch : Nat := 0
  inFlight : List Packet := []
  store : TombstoneKV := []
  deriving Repr, DecidableEq

def initDistState : DistState := {}

def applyPayload (db : TombstoneKV) (p : Payload) : TombstoneKV :=
  match p with
  | .put k v => TombstoneKV.put db k v
  | .del k => TombstoneKV.del db k

def NoSplitBrainOverwrite (s : DistState) : Bool :=
  decide (s.committedEpoch = s.highWaterEpoch)

/-! ## 4. Gear 1 — Bounded BFS Counterexample Finder (Buggy Unfenced Storage) -/

inductive BuggyStep where
  | acquireAndSendPut (key : String) (val : String)
  | deliverUnfenced (idx : Nat)
  deriving Repr, DecidableEq

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
          let rest := s.inFlight.eraseIdx idx
          some { s with
            committedEpoch := pkt.token
            highWaterEpoch := Nat.max s.highWaterEpoch pkt.token
            inFlight := rest
            store := applyPayload s.store pkt.payload }

def runBuggyTrace (s : DistState) : List BuggyStep → Option DistState
  | [] => some s
  | act :: rest =>
      match stepBuggy s act with
      | none => none
      | some s' => runBuggyTrace s' rest

def candidateBuggySteps (s : DistState) : List BuggyStep :=
  let issueSteps :=
    if s.latestIssued < 2 then
      [.acquireAndSendPut "cfg" s!"leader-{s.latestIssued + 1}"]
    else
      []
  let deliverSteps := (List.range s.inFlight.length).map BuggyStep.deliverUnfenced
  issueSteps ++ deliverSteps

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

def findSplitBrainCounterexample : Option (List BuggyStep) :=
  bfsSearch 40 [initDistState] [(initDistState, [])]

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
  Milestone 1 (**Gear 1 — Split-Brain Bug Finder**):
  Verify via kernel evaluation (`decide`) that `findSplitBrainCounterexample`
  discovers a concrete trace where stale `leader-1` overwrites `leader-2`.
-/
theorem gear1_split_brain_caught :
    isValidSplitBrainWitness findSplitBrainCounterexample = true := by
  sorry

/-! ## 5. Gear 2A — Unbounded Fencing-Token Safety Invariant -/

inductive ProtocolAction where
  | issuePacket (payload : Payload)
  | duplicatePacket (pkt : Packet)
  | reorderNetwork (newBag : List Packet)
  | deliverFenced (pkt : Packet)
  | compactStorage
  deriving Repr, DecidableEq

def deliverFencedExec (s : DistState) (pkt : Packet) : DistState :=
  if decide (s.storageFence ≤ pkt.token) then
    { s with
      storageFence := pkt.token
      committedEpoch := pkt.token
      highWaterEpoch := max s.highWaterEpoch pkt.token
      store := applyPayload s.store pkt.payload }
  else
    s

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

inductive Reachable : DistState → Prop where
  | init : Reachable initDistState
  | step {s s' : DistState} {act : ProtocolAction} :
      Reachable s → Step s act s' → Reachable s'

/-- Strengthened inductive invariant tying epoch watermarks to `storageFence`. -/
def FencingInv (s : DistState) : Prop :=
  s.committedEpoch = s.storageFence ∧
  s.highWaterEpoch = s.storageFence ∧
  s.storageFence ≤ s.latestIssued ∧
  ∀ pkt ∈ s.inFlight, pkt.token ≤ s.latestIssued

/-- Milestone 2a: Base case of the fencing invariant. -/
theorem init_fencingInv : FencingInv initDistState := by
  sorry

/--
  Milestone 2b (**Inductive Step**):
  Prove `FencingInv` is preserved across packet issuance, arbitrary duplication,
  reordering, fenced delivery, and background storage compaction.
-/
theorem step_preserves_fencingInv {s s' : DistState} {act : ProtocolAction}
    (hInv : FencingInv s) (hStep : Step s act s') :
    FencingInv s' := by
  sorry

/--
  Milestone 2c (**Unbounded Split-Brain Freedom**):
  Conclude that every reachable state of the fenced protocol satisfies `NoSplitBrainOverwrite`.
-/
theorem reachable_no_split_brain {s : DistState} (hReach : Reachable s) :
    NoSplitBrainOverwrite s = true := by
  sorry

/-- Milestone 2d: Stale packets (`pkt.token < s.storageFence`) act as exact no-ops. -/
theorem stale_packet_rejected (s : DistState) (pkt : Packet)
    (hStale : pkt.token < s.storageFence) :
    deliverFencedExec s pkt = s := by
  sorry

/-! ## 6. Gear 2B — Tombstone Compaction Stuttering Refinement against `SpecKV` -/

/-- Milestone 3a: Concrete `put` refines `SpecKV.put`. -/
theorem absKV_put (db : TombstoneKV) (k v : String) :
    absKV (TombstoneKV.put db k v) = SpecKV.put (absKV db) k v := by
  sorry

/-- Milestone 3b: Concrete tombstone `del` refines `SpecKV.del`. -/
theorem absKV_del (db : TombstoneKV) (k : String) :
    absKV (TombstoneKV.del db k) = SpecKV.del (absKV db) k := by
  sorry

/--
  Milestone 3c (**Compaction Stuttering Refinement**):
  Prove that `TombstoneKV.compact` preserves the exact abstract key-value map `absKV`
  (zero zombie value resurrection!).
  *Hint*: Prove two helpers on `compactAux seen db`:
  1. `get_compactAux_of_mem` (`k ∈ seen → get (compactAux seen db) k = none`)
  2. `get_compactAux_of_not_mem` (`k ∉ seen → get (compactAux seen db) k = get db k`)
-/
theorem compact_stutters (db : TombstoneKV) :
    absKV (TombstoneKV.compact db) = absKV db := by
  sorry

/-- Milestone 4: Non-vacuity witness for fenced write, delete, and full tombstone purge. -/
theorem non_vacuous_fenced_lifecycle :
    let s1 := deliverFencedExec initDistState { token := 1, payload := .put "k" "v1" }
    let s2 := deliverFencedExec s1 { token := 2, payload := .del "k" }
    let compacted := TombstoneKV.compact s2.store
    NoSplitBrainOverwrite s2 = true ∧
    TombstoneKV.get compacted "k" = none ∧
    compacted = [] := by
  sorry

end FencingKV
