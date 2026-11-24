/-
  Chapter 9: Packing Proofs into Types
  ====================================

  "Parse, don't validate" reaches its ultimate form in Lean 4:
  when a type carries a `Prop` witness—via `{ x : α // P x }`, `Fin n`, or custom
  invariant-carrying structures—illegal states become unrepresentable at compile time.

  Crucially, every `Prop` field is erased by Lean's code generator:
  at runtime, `{ n : Nat // 0 < n }` has the exact same memory representation as `Nat`,
  and `Fin cap` has the exact same runtime layout as `Nat` (or a machine word).
  You get ironclad invariants with zero runtime proof allocation.
-/
set_option autoImplicit false

namespace ProveIt.Ch09

/-! ## 1. Subtypes `{ x : α // P x }` and Proof Erasure -/

/-- Strictly positive natural numbers, suitable as divisors or shard counts. -/
abbrev PosNat := { n : Nat // 0 < n }

/-- Total integer division that never silently returns `0` on a zero divisor. -/
def safeDiv (num : Nat) (den : PosNat) : Nat :=
  num / den.val

/-- Worked Example: `den.property` feeds arithmetic lemmas directly. -/
theorem safeMod_lt (num : Nat) (den : PosNat) : num % den.val < den.val :=
  Nat.mod_lt num den.property

theorem safeDiv_euclid (num : Nat) (den : PosNat) :
    den.val * safeDiv num den + num % den.val = num :=
  Nat.div_add_mod num den.val

#guard safeDiv 42 ⟨5, by omega⟩ == 8

/-- info: 'ProveIt.Ch09.safeDiv_euclid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms safeDiv_euclid

/-! ## 2. Dependent `if h : c then ... else ...` and `Fin n` -/

/--
  Worked Example: Advancing a circular cursor inside `Fin cap`.
  Notice `if h : cur.val + 1 < cap`: unlike an ordinary boolean `if`,
  naming `h` introduces `h : cur.val + 1 < cap` inside the `then` branch
  and `h : ¬ (cur.val + 1 < cap)` inside the `else` branch!
-/
def advanceCursor (cap : Nat) (hCap : 0 < cap) (cur : Fin cap) : Fin cap :=
  if h : cur.val + 1 < cap then
    ⟨cur.val + 1, h⟩
  else
    ⟨0, hCap⟩

theorem advanceCursor_wraps_only_at_end (cap : Nat) (hCap : 0 < cap) (cur : Fin cap)
    (hWrap : (advanceCursor cap hCap cur).val = 0) :
    cur.val + 1 = cap := by
  unfold advanceCursor at hWrap
  split at hWrap
  · simp only at hWrap
    omega
  · have hLt : cur.val < cap := cur.isLt
    omega

#guard (advanceCursor 4 (by omega) ⟨2, by omega⟩).val == 3
#guard (advanceCursor 4 (by omega) ⟨3, by omega⟩).val == 0

/-! ## 3. Structural Invariants: `NonEmptyList` -/

/-- A list guaranteed by construction to have at least one element. -/
structure NonEmptyList (α : Type) where
  head : α
  tail : List α
  deriving Repr, DecidableEq

/-- Total `first` projection: no `Option`, no default fallback value, no panic. -/
def NonEmptyList.first {α : Type} (xs : NonEmptyList α) : α :=
  xs.head

def NonEmptyList.toList {α : Type} (xs : NonEmptyList α) : List α :=
  xs.head :: xs.tail

@[simp]
theorem NonEmptyList.length_toList {α : Type} (xs : NonEmptyList α) :
    xs.toList.length = xs.tail.length + 1 := rfl

theorem NonEmptyList.length_pos {α : Type} (xs : NonEmptyList α) :
    0 < xs.toList.length := by
  simp only [length_toList]
  omega

/-! ## Exercises -/

/-- Basis points in `[0, 10_000]` (where `10_000` = 100.00%). -/
abbrev BasisPoints := { bps : Nat // bps ≤ 10_000 }

/--
  EXERCISE 1: Clamp an arbitrary `Nat` into `BasisPoints` using dependent
  `if h : n ≤ 10_000 then ... else ...`.
-/
def clampBps (n : Nat) : BasisPoints :=
  let _ := n
  sorry

-- Uncomment after completing Exercise 1:
-- #guard (clampBps 250).val == 250
-- #guard (clampBps 99_999).val == 10_000

/--
  EXERCISE 2: Prove that `clampBps` leaves any already-valid `BasisPoints` unchanged.
  Hint: `Subtype.ext` reduces equality of subtypes `{ x // P x }` to equality of `.val`!
-/
theorem clampBps_idempotent (b : BasisPoints) : clampBps b.val = b := by
  sorry

/--
  EXERCISE 3: Prove that a fee computed from `BasisPoints` never exceeds `principal`.
  Because `rate : BasisPoints` packs `rate.val ≤ 10_000` into its type, callers never
  have to pass a separate precondition!
-/
theorem fee_le_principal (principal : Nat) (rate : BasisPoints) :
    (principal * rate.val) / 10_000 ≤ principal := by
  sorry

/--
  EXERCISE 4: Bounded connection-pool acquisition.
  Given `used : { u : Nat // u ≤ cap }`, acquire one more slot if `used.val < cap`,
  returning `some ⟨used.val + 1, ...⟩`, or `none` when at capacity.
-/
def tryAcquire (cap : Nat) (used : { u : Nat // u ≤ cap }) :
    Option { u : Nat // u ≤ cap } :=
  let _ := (cap, used)
  sorry

-- Uncomment after completing Exercise 4:
-- #guard (tryAcquire 2 ⟨1, by omega⟩).map Subtype.val == some 2
-- #guard (tryAcquire 2 ⟨2, by omega⟩).isNone

/--
  EXERCISE 5: Prove that whenever `tryAcquire` succeeds, capacity was strictly available
  and usage increments by exactly `1`.
-/
theorem tryAcquire_spec (cap : Nat) (used next : { u : Nat // u ≤ cap })
    (hAcq : tryAcquire cap used = some next) :
    used.val < cap ∧ next.val = used.val + 1 := by
  sorry

/--
  EXERCISE 6: Concatenate two `NonEmptyList`s and prove that `toList` distributes
  cleanly over `append`.
-/
def NonEmptyList.append {α : Type} (xs ys : NonEmptyList α) : NonEmptyList α :=
  let _ := (xs, ys)
  sorry

theorem NonEmptyList.toList_append {α : Type} (xs ys : NonEmptyList α) :
    (xs.append ys).toList = xs.toList ++ ys.toList := by
  sorry

end ProveIt.Ch09
