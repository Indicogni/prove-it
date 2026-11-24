/-
  Chapter 15: Verified Wire Formats (Solutions)
  =============================================

  Why is `decode (encode pkt) = some pkt` dangerously weak for network protocols?
  Because on TCP streams, pipe buffers, and WAL files, frames arrive back-to-back:
    `encode pkt₁ ++ encode pkt₂ ++ rest`
  or truncated mid-header!
  - A parser that greedily reads to EOF passes `decode (encode pkt) = some pkt`
    yet catastrophically merges `pkt₁` and `pkt₂` on a live socket.
  - A parser that slices `List.take declaredLen buf` without checking `buf.length`
    silently accepts truncated frames (the exact shape of TLS Heartbleed!).

  The Gold-Standard Stream Framing Specification is:
    `∀ pkt rest, decodePacket (encodePacket pkt ++ rest) = some (pkt, rest)`
  which simultaneously guarantees lossless round-tripping, exact frame boundaries
  (zero overread / zero desync), and wire-format injectivity (zero smuggling).
-/
set_option autoImplicit false

namespace Solutions.Ch15

/-! ## 1. Big-Endian 16-Bit Length Headers (`UInt8`) -/

/-- Encode `n < 65_536` as two big-endian `UInt8` bytes `[hi, lo]`. -/
def encodeU16BE (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

/-- Decode two big-endian `UInt8` bytes from the head of a byte stream. -/
def decodeU16BE : List UInt8 → Option (Nat × List UInt8)
  | hi :: lo :: rest => some (hi.toNat * 256 + lo.toNat, rest)
  | _ => none

/-- Worked Example: Exact stream round-trip for 16-bit big-endian lengths. -/
theorem decodeU16BE_encodeU16BE (n : Nat) (hLt : n < 65_536) (rest : List UInt8) :
    decodeU16BE (encodeU16BE n ++ rest) = some (n, rest) := by
  simp [encodeU16BE, decodeU16BE]
  omega

#guard decodeU16BE (encodeU16BE 1029 ++ [99]) == some (1029, [99])

/-! ## 2. TLV Tags & Proof-Carrying `Packet` -/

inductive Tag where
  | heartbeat
  | auth
  | payload
  | close
  deriving Repr, DecidableEq

def encodeTag : Tag → UInt8
  | .heartbeat => 0x01
  | .auth      => 0x02
  | .payload   => 0x03
  | .close     => 0x04

def decodeTag (b : UInt8) : Option Tag :=
  if b == 0x01 then some .heartbeat
  else if b == 0x02 then some .auth
  else if b == 0x03 then some .payload
  else if b == 0x04 then some .close
  else none

/--
  A TLV frame whose payload is guaranteed by construction to fit inside a
  16-bit length header (`< 65_536` bytes).
-/
structure Packet where
  tag  : Tag
  body : List UInt8
  hLen : body.length < 65_536
  deriving Repr, DecidableEq

theorem Packet.ext {p₁ p₂ : Packet} (hTag : p₁.tag = p₂.tag) (hBody : p₁.body = p₂.body) :
    p₁ = p₂ := by
  rcases p₁ with ⟨t1, b1, h1⟩
  rcases p₂ with ⟨t2, b2, h2⟩
  subst hTag hBody
  rfl

/-! ## 3. Anti-Heartbleed Exact Byte Slicing (`takeExact`) -/

/--
  Read *exactly* `n` elements from `xs`, returning `none` if `xs` has fewer
  than `n` bytes remaining (never silently returning a truncated slice!).
-/
def takeExact {α : Type} : Nat → List α → Option (List α × List α)
  | 0, xs => some ([], xs)
  | _ + 1, [] => none
  | n + 1, x :: xs =>
    match takeExact n xs with
    | some (chunk, rem) => some (x :: chunk, rem)
    | none => none

/-- Serialize a TLV `Packet`: 1-byte `Tag` + 2-byte `Length` + `Length`-byte `Value`. -/
def encodePacket (pkt : Packet) : List UInt8 :=
  encodeTag pkt.tag :: (encodeU16BE pkt.body.length ++ pkt.body)

/--
  Deserialize one TLV `Packet` from the front of `stream`, returning both the
  parsed `Packet` and the unconsumed trailing bytes `rem`.
-/
def decodePacket (stream : List UInt8) : Option (Packet × List UInt8) :=
  match stream with
  | [] => none
  | tagByte :: afterTag =>
    match decodeTag tagByte with
    | none => none
    | some tag =>
      match decodeU16BE afterTag with
      | none => none
      | some (len, afterLen) =>
        if hLt : len < 65_536 then
          match takeExact len afterLen with
          | none => none
          | some (body, rem) =>
            if hBodyLen : body.length = len then
              some ({ tag := tag, body := body, hLen := by omega }, rem)
            else
              none
        else
          none

/-! ## Exercises -/

/--
  EXERCISE 1: Prove that `decodeTag` inverts `encodeTag` on every `Tag`.
-/
theorem decodeTag_encodeTag (t : Tag) : decodeTag (encodeTag t) = some t := by
  cases t <;> rfl

/--
  EXERCISE 2 (Anti-Heartbleed Bounds & Conservation):
  Prove that whenever `takeExact n xs = some (chunk, rem)`, `chunk` has *exact*
  length `n` (rejecting truncated buffers!) and `chunk ++ rem = xs` (zero byte loss).
-/
theorem takeExact_sound {α : Type} (n : Nat) (xs chunk rem : List α)
    (hTake : takeExact n xs = some (chunk, rem)) :
    chunk.length = n ∧ chunk ++ rem = xs := by
  induction n generalizing xs chunk rem with
  | zero =>
    simp only [takeExact] at hTake
    injection hTake with hPair
    injection hPair with hChunk hRem
    subst hChunk hRem
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    cases xs with
    | nil => nomatch hTake
    | cons x rest =>
      simp only [takeExact] at hTake
      split at hTake
      · rename_i subChunk subRem hRec
        injection hTake with hPair
        injection hPair with hChunk hRem
        subst hChunk hRem
        obtain ⟨hLen, hApp⟩ := ih rest subChunk subRem hRec
        simp [List.length_cons, List.cons_append, hLen, hApp]
      · nomatch hTake

-- Rejects truncated 5-byte claim when only 3 bytes arrive:
#guard (decodePacket [0x03, 0x00, 0x05, 10, 20, 30]).isNone

/--
  EXERCISE 3 (Exact Frame Boundary Lemma):
  Prove that `takeExact body.length (body ++ rest)` stops at the exact end of
  `body`, leaving `rest` completely untouched!
-/
theorem takeExact_append {α : Type} (body rest : List α) :
    takeExact body.length (body ++ rest) = some (body, rest) := by
  induction body with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, List.cons_append, takeExact, ih]

/--
  EXERCISE 4 (Stream-Safe TLV Round-Trip Theorem):
  Prove that for ANY `pkt : Packet` and ANY trailing stream `rest : List UInt8`,
  `decodePacket (encodePacket pkt ++ rest) = some (pkt, rest)`.
-/
theorem decodePacket_encodePacket_stream (pkt : Packet) (rest : List UInt8) :
    decodePacket (encodePacket pkt ++ rest) = some (pkt, rest) := by
  have hAssoc : encodePacket pkt ++ rest =
      encodeTag pkt.tag :: (encodeU16BE pkt.body.length ++ (pkt.body ++ rest)) := by
    simp only [encodePacket, List.cons_append, List.append_assoc]
  rw [hAssoc]
  unfold decodePacket
  simp only [decodeTag_encodeTag, decodeU16BE_encodeU16BE pkt.body.length pkt.hLen,
    pkt.hLen, dite_true, takeExact_append]

/-- Decode two consecutive packets from a TCP stream. -/
def decodeTwoPackets (stream : List UInt8) : Option (Packet × Packet × List UInt8) :=
  match decodePacket stream with
  | none => none
  | some (p1, rem1) =>
    match decodePacket rem1 with
    | none => none
    | some (p2, rem2) => some (p1, p2, rem2)

/--
  EXERCISE 5 (Back-to-Back Stream Framing & Wire Injectivity):
  Prove BOTH:
  1. Two concatenated packets on a stream decode cleanly without frame desync.
  2. `encodePacket` is injective (two distinct packets can never produce the
     same wire bytes—ruling out parser-differential smuggling!).
-/
theorem decodeTwoPackets_stream (p1 p2 : Packet) (rest : List UInt8) :
    decodeTwoPackets (encodePacket p1 ++ encodePacket p2 ++ rest) =
      some (p1, p2, rest) := by
  rw [List.append_assoc]
  unfold decodeTwoPackets
  simp only [decodePacket_encodePacket_stream]

theorem encodePacket_injective (p1 p2 : Packet)
    (hWire : encodePacket p1 = encodePacket p2) :
    p1 = p2 := by
  have h1 := decodePacket_encodePacket_stream p1 []
  have h2 := decodePacket_encodePacket_stream p2 []
  simp only [List.append_nil] at h1 h2
  rw [hWire, h2] at h1
  injection h1 with hPair
  injection hPair with hPkt _
  exact hPkt.symm

/-- info: 'Solutions.Ch15.decodePacket_encodePacket_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodePacket_encodePacket_stream

/-- info: 'Solutions.Ch15.encodePacket_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encodePacket_injective

end Solutions.Ch15
