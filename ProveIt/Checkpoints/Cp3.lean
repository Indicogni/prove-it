/-
  Checkpoint 3 (Closed-Notes): Verified Fixed-Capacity Ring Buffer
  ================================================================

  Synthesize Part III (Chapters 9–12) on a classic systems structure:
  a pre-allocated, zero-allocation circular ring buffer backed by a flat `Array α`.

  Architecture & Design for Verifiability:
  - Instead of `% cap` (hardware `DIV` + painful modular-arithmetic proofs),
    since `head < cap` and `offset < cap`, `head + offset < 2 * cap`, so
    `wrapAdd cap head offset` needs only a single branch (`if head + offset < cap ...`),
    making BOTH CPU execution faster AND `split` + `omega` proofs automatic!
  - In `pop`, we do NOT zero out stale slots in `data`—just like Linux `kfifo`
    and DPDK rings, advancing `head` and decrementing `count` leaves stale bytes
    untouched in physical memory while refining cleanly to `List` dequeue!
-/
set_option autoImplicit false

namespace ProveIt.Checkpoints.Cp3

/-! ## 1. Branch-Only Circular Indexing & Proof-Carrying Structure -/

/--
  Fast branch-only modular addition `(head + offset) mod cap` valid whenever
  `head < cap` and `offset ≤ cap`.
-/
def wrapAdd (cap head offset : Nat) : Nat :=
  if head + offset < cap then head + offset else head + offset - cap

/--
  A fixed-capacity circular buffer storing `count` logical elements starting at
  physical index `head` inside a flat array of size `cap`.
-/
structure RingBuffer (α : Type) (cap : Nat) where
  data   : Array α
  head   : Nat
  count  : Nat
  hCap   : 0 < cap
  hSize  : data.size = cap
  hHead  : head < cap
  hCount : count ≤ cap
  deriving Repr, DecidableEq

/-- Allocate an empty ring buffer of capacity `cap > 0` pre-filled with `dummy`. -/
def RingBuffer.empty {α : Type} (cap : Nat) (hCap : 0 < cap) (dummy : α) :
    RingBuffer α cap :=
  { data   := Array.replicate cap dummy
    head   := 0
    count  := 0
    hCap   := hCap
    hSize  := Array.size_replicate
    hHead  := hCap
    hCount := Nat.zero_le cap }

/-! ## 2. Exercise 1: Bounds-Safe Circular Indexing -/

/--
  EXERCISE 1a: Prove that for any `head < cap` and `offset < cap`,
  `wrapAdd cap head offset` is strictly in bounds (`< cap`).
-/
theorem wrapAdd_lt (cap head offset : Nat) (hHead : head < cap) (hOff : offset < cap) :
    wrapAdd cap head offset < cap := by
  sorry

/--
  EXERCISE 1b: Prove that distinct logical offsets `o1 ≠ o2` below `cap`
  never collide on the same physical slot.
-/
theorem wrapAdd_inj (cap head o1 o2 : Nat)
    (h1 : o1 < cap) (h2 : o2 < cap)
    (hNe : o1 ≠ o2) :
    wrapAdd cap head o1 ≠ wrapAdd cap head o2 := by
  sorry

/-! ## 3. Abstract Queue Refinement Mapping (`toQueue`) -/

/-- Read `len` logical elements starting at logical offset `start` from `head`. -/
def readSlice {α : Type} (data : Array α) (cap : Nat) (hSize : data.size = cap)
    (head : Nat) (hHead : head < cap) :
    (start len : Nat) → (hBound : start + len ≤ cap) → List α
  | _, 0, _ => []
  | start, len + 1, hBound =>
    let idx := wrapAdd cap head start
    have hIdx : idx < data.size := by
      rw [hSize]
      exact wrapAdd_lt cap head start hHead (by omega)
    data[idx] :: readSlice data cap hSize head hHead (start + 1) len (by omega)

/-- Refinement mapping (`abs`): view a concrete `RingBuffer` as an abstract FIFO `List α`. -/
def RingBuffer.toQueue {α : Type} {cap : Nat} (rb : RingBuffer α cap) : List α :=
  readSlice rb.data cap rb.hSize rb.head rb.hHead 0 rb.count (by have := rb.hCount; omega)

theorem toQueue_empty {α : Type} (cap : Nat) (hCap : 0 < cap) (dummy : α) :
    (RingBuffer.empty cap hCap dummy).toQueue = [] := rfl

/--
  EXERCISE 2: Prove that `readSlice` (and hence `toQueue`) has exact length `len` (`rb.count`).
-/
theorem readSlice_length {α : Type} (data : Array α) (cap : Nat) (hSize : data.size = cap)
    (head : Nat) (hHead : head < cap) (start len : Nat) (hBound : start + len ≤ cap) :
    (readSlice data cap hSize head hHead start len hBound).length = len := by
  sorry

theorem toQueue_length {α : Type} {cap : Nat} (rb : RingBuffer α cap) :
    rb.toQueue.length = rb.count :=
  readSlice_length rb.data cap rb.hSize rb.head rb.hHead 0 rb.count (by have := rb.hCount; omega)

/-! ## 4. Exercise 3 & 4: Enqueue (`push`) & FIFO Tail Refinement -/

/--
  EXERCISE 3: Implement bounds-safe `push`.
  - If `hRoom : rb.count < cap`, write `x` into physical slot `wrapAdd cap rb.head rb.count`
    using `rb.data.set tailIdx x` and increment `count` by `1`.
  - Otherwise return `none` (buffer full).
-/
def RingBuffer.push {α : Type} {cap : Nat} (rb : RingBuffer α cap) (x : α) :
    Option (RingBuffer α cap) :=
  let _ := (rb, x)
  sorry

/-- Provided slice helper: splitting the last element off `readSlice`. -/
theorem readSlice_succ_snoc {α : Type} (data : Array α) (cap : Nat) (hSize : data.size = cap)
    (head : Nat) (hHead : head < cap) (start len : Nat) (hBound : start + (len + 1) ≤ cap) :
    readSlice data cap hSize head hHead start (len + 1) hBound =
      readSlice data cap hSize head hHead start len (by omega) ++
      [data[wrapAdd cap head (start + len)]'(by
        rw [hSize]; exact wrapAdd_lt cap head (start + len) hHead (by omega))] := by
  induction len generalizing start with
  | zero =>
    simp only [readSlice, Nat.add_zero, List.nil_append]
  | succ n ih =>
    conv => lhs; unfold readSlice
    conv => rhs; lhs; unfold readSlice
    simp only [List.cons_append]
    congr 1
    rw [ih (start + 1) (by omega)]
    have hAssoc : start + 1 + n = start + (n + 1) := by omega
    simp only [hAssoc]

/-- Provided slice helper: writing to `writeOff` leaves earlier slots `[start .. start + len)` untouched. -/
theorem readSlice_set_unreached {α : Type} (data : Array α) (cap : Nat) (hSize : data.size = cap)
    (head : Nat) (hHead : head < cap) (writeOff : Nat) (hWrite : writeOff < cap)
    (x : α) (hIdx : wrapAdd cap head writeOff < data.size)
    (start len : Nat) (hBefore : start + len ≤ writeOff) :
    readSlice (data.set (wrapAdd cap head writeOff) x) cap
      (by simp only [Array.size_set, hSize]) head hHead start len (by omega) =
    readSlice data cap hSize head hHead start len (by omega) := by
  induction len generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [readSlice]
    have hNe : wrapAdd cap head writeOff ≠ wrapAdd cap head start :=
      wrapAdd_inj cap head writeOff start hWrite (by omega) (by omega)
    congr 1
    · exact Array.getElem_set_ne (xs := data) (v := x) hIdx _ hNe
    · exact ih (start + 1) (by omega)

/--
  EXERCISE 4: Prove that `push` refines FIFO queue append (`rb'.toQueue = rb.toQueue ++ [x]`)
  whenever capacity is available.
-/
theorem push_refines {α : Type} {cap : Nat} (rb rb' : RingBuffer α cap) (x : α)
    (hPush : rb.push x = some rb') :
    rb.count < cap ∧ rb'.toQueue = rb.toQueue ++ [x] := by
  sorry

/-! ## 5. Exercise 5 & 6: Dequeue (`pop`) & FIFO Head Refinement -/

/--
  EXERCISE 5: Implement bounds-safe `pop`.
  - If `hPos : 0 < rb.count`, read `rb.data[rb.head]` (without clearing `data`!),
    advance `head := wrapAdd cap rb.head 1`, and decrement `count`.
  - Otherwise return `none`.
-/
def RingBuffer.pop {α : Type} {cap : Nat} (rb : RingBuffer α cap) :
    Option (α × RingBuffer α cap) :=
  let _ := rb
  sorry

/-- Provided slice helper: shifting `head` by `1` matches shifting `start` by `1`. -/
theorem readSlice_shift_head {α : Type} (data : Array α) (cap : Nat) (hSize : data.size = cap)
    (head : Nat) (hHead : head < cap) (hNext : wrapAdd cap head 1 < cap)
    (start len : Nat) (hBound : start + 1 + len ≤ cap) :
    readSlice data cap hSize (wrapAdd cap head 1) hNext start len (by omega) =
    readSlice data cap hSize head hHead (start + 1) len hBound := by
  induction len generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [readSlice]
    have hSlot : wrapAdd cap (wrapAdd cap head 1) start = wrapAdd cap head (start + 1) := by
      unfold wrapAdd
      split <;> split <;> split <;> omega
    congr 1
    · congr 1
    · exact ih (start + 1) (by omega)

/--
  EXERCISE 6: Prove that `pop` refines FIFO queue head extraction
  (`rb.toQueue = val :: rb'.toQueue`).
  Hint: Destructuring `rcases rb with ⟨data, head, _ | c, hCap, hSize, hHead, hCount⟩`
  before unfolding `pop` avoids dependent generalization headaches!
-/
theorem pop_refines {α : Type} {cap : Nat} (rb rb' : RingBuffer α cap) (val : α)
    (hPop : rb.pop = some (val, rb')) :
    rb.toQueue = val :: rb'.toQueue := by
  sorry

-- Uncomment after implementing `push` and `pop`:
-- #guard (
--   let rb0 := RingBuffer.empty 3 (by omega) 0
--   match rb0.push 10 with
--   | none => false
--   | some rb1 =>
--     match rb1.push 20 with
--     | none => false
--     | some rb2 =>
--       match rb2.pop with
--       | none => false
--       | some (v1, rb3) =>
--         match rb3.push 30 >>= (·.push 40) with
--         | none => false
--         | some rb4 => v1 == 10 && rb4.toQueue == [20, 30, 40]
-- )

end ProveIt.Checkpoints.Cp3
