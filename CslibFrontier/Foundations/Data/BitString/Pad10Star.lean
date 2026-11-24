/-
Copyright (c) 2026 Karn Seth, Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.PadBlocks
import Mathlib.Data.List.GetD

/-!
# Padding with a one and zeros

`BitString.pad10star r msg` appends to a bit list a `1` and then the fewest zeros that make its
length a multiple of `r`: the padding `m ↦ m ‖ 1 ‖ 0^*` of the sponge construction
([KatzLindell2020], Construction 7.6), called `pad10*` in the Keccak literature. Padding and then
cutting into blocks of `r` bits (`BitString.toBlocks`) is injective
(`BitString.toBlocks_pad10star_injective`), so a bit list of any length can be recovered from its
padded blocks.

## Main definitions

* `Cslib.BitString.pad10star`: the padding `m ‖ 1 ‖ 0^*` to a multiple of `r` bits.

## Main results

* `Cslib.BitString.pad10star_injective`, `Cslib.BitString.toBlocks_pad10star_injective`:
  distinct bit lists have distinct paddings and distinct padded block sequences.
* `Cslib.BitString.length_pad10star`: the padded length is `(msg.length / r + 1) * r`, one block
  more than the whole blocks of the message.
* `Cslib.BitString.getD_pad10star`: the padded list read with default `false` is `msg ++ [true]`
  read with default `false`.
* `Cslib.BitString.toBlocks_pad10star_append_ofFn`: the padded blocks of whole blocks followed by
  one more block.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Construction 7.6
-/

public section

namespace Cslib.BitString

/-- The padding of [KatzLindell2020], Construction 7.6: append a `1` and then the fewest zeros
making the length a multiple of `r`. -/
@[expose]
def pad10star (r : ℕ) (msg : List Bool) : List Bool :=
  msg ++ true :: List.replicate ((r - (msg.length + 1) % r) % r) false

private theorem replicate_false_append_true_inj :
    ∀ (k k' : ℕ) (a b : List Bool),
      List.replicate k false ++ true :: a = List.replicate k' false ++ true :: b → a = b
  | 0, 0, a, b, h => by simpa using h
  | k + 1, 0, a, b, h => by simp [List.replicate_succ] at h
  | 0, k' + 1, a, b, h => by simp [List.replicate_succ] at h
  | k + 1, k' + 1, a, b, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    exact replicate_false_append_true_inj k k' a b h

/-- Padding is injective: distinct messages have distinct padded strings. -/
theorem pad10star_injective (r : ℕ) : Function.Injective (pad10star r) := by
  intro a b h
  have h' := congrArg List.reverse h
  simp only [pad10star, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append] at h'
  simpa using congrArg List.reverse (replicate_false_append_true_inj _ _ _ _ h')

/-- The padded length: one block more than the whole blocks of the message. -/
theorem length_pad10star {r : ℕ} (hr : 0 < r) (msg : List Bool) :
    (pad10star r msg).length = (msg.length / r + 1) * r := by
  have hs := Nat.mod_lt msg.length hr
  have hd := Nat.div_add_mod' msg.length r
  simp only [pad10star, List.length_append, List.length_cons, List.length_replicate,
    Nat.add_mul, Nat.one_mul, ← Nat.mod_add_mod msg.length r 1]
  rcases Nat.lt_or_ge (msg.length % r + 1) r with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show msg.length % r + 1 = r by omega, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
    omega

theorem dvd_length_pad10star {r : ℕ} (hr : 0 < r) (msg : List Bool) :
    r ∣ (pad10star r msg).length :=
  length_pad10star hr msg ▸ Nat.dvd_mul_left _ _

/-- The padded length in blocks: one more than the whole blocks of the message. -/
theorem length_pad10star_div {r : ℕ} (hr : 0 < r) (msg : List Bool) :
    (pad10star r msg).length / r = msg.length / r + 1 := by
  rw [length_pad10star hr, Nat.mul_div_cancel _ hr]

/-- Padding adds at most one block: a `1` and fewer than `r` zeros. -/
theorem length_pad10star_le {r : ℕ} (hr : 0 < r) (msg : List Bool) :
    (pad10star r msg).length ≤ msg.length + r := by
  rw [length_pad10star hr, Nat.add_mul, Nat.one_mul]
  exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

/-- On a message whose length is a multiple of `r`, padding appends one full block
`1 ‖ 0^(r - 1)`. -/
theorem pad10star_of_dvd {r : ℕ} (hr : 0 < r) {msg : List Bool} (h : r ∣ msg.length) :
    pad10star r msg = msg ++ true :: List.replicate (r - 1) false := by
  obtain ⟨k, hk⟩ := h
  have : (r - (msg.length + 1) % r) % r = r - 1 := by
    rw [hk, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    rcases Nat.lt_or_ge 1 r with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]
    · obtain rfl : r = 1 := by omega
      rfl
  simp only [pad10star, this]

/-- Reading the padded list with default `false` is reading `msg ++ [true]` with default
`false`: the zeros of the padding are the default. -/
theorem getD_pad10star (r : ℕ) (msg : List Bool) (i : ℕ) :
    (pad10star r msg).getD i false = (msg ++ [true]).getD i false := by
  rw [pad10star, ← List.singleton_append, ← List.append_assoc]
  rcases Nat.lt_or_ge i (msg ++ [true]).length with h | h
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_append_right _ _ _ _ h, List.getD_eq_default _ _ h, List.getD_eq_getElem?_getD,
      List.getElem?_getD_replicate_default_eq]

/-- Distinct messages have distinct padded block sequences. -/
theorem toBlocks_pad10star_injective {r : ℕ} (hr : 0 < r) :
    Function.Injective fun msg => toBlocks r (pad10star r msg) := fun _ _ h =>
  pad10star_injective r (toBlocks_injOn (dvd_length_pad10star hr _) (dvd_length_pad10star hr _) h)

theorem toBlocks_pad10star_ne_nil {r : ℕ} (hr : 0 < r) (msg : List Bool) :
    toBlocks r (pad10star r msg) ≠ [] :=
  List.ne_nil_of_length_pos <| by
    rw [length_toBlocks, length_pad10star_div hr]
    exact Nat.succ_pos _

/-- The padded blocks of a full-block list `u` followed by one more block `m` are the blocks of
`u`, then `m`, then the padding block. -/
theorem toBlocks_pad10star_append_ofFn {r : ℕ} (hr : 0 < r) {u : List Bool} (hu : r ∣ u.length)
    (m : BitString r) :
    toBlocks r (pad10star r (u ++ List.ofFn m)) =
      toBlocks r u ++ m :: toBlocks r (true :: List.replicate (r - 1) false) := by
  have hum : r ∣ (u ++ List.ofFn m).length := by
    simpa using Nat.dvd_add hu (Nat.dvd_refl r)
  rw [pad10star_of_dvd hr hum, List.append_assoc, toBlocks_append hu,
    toBlocks_append (a := List.ofFn m) (by simp), toBlocks_ofFn hr]
  rfl

end Cslib.BitString
