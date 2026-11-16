/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute
public import CslibFrontier.Foundations.Data.BitString.List

/-!
# Labels read from words

At parameter `k` a label is a `(k + 1)`-bit key and a colour bit, and its word `labelBits` is the
key's bits followed by the colour. This module reads labels back from words, for the garblers,
evaluators and simulators that work on words. `labelEquiv k` identifies `(k + 2)`-bit strings with
labels, splitting off the last bit as the colour, and `labelOfWord k word` is the label of the
first `k + 2` bits of `word`, padded with `false`. On a word of `k + 2` bits, `labelBits` undoes
it (`labelBits_labelOfWord`).

## Main definitions

* `Cslib.Crypto.Garbling.PointPermute.labelEquiv`: labels as `(k + 2)`-bit strings.
* `Cslib.Crypto.Garbling.PointPermute.labelOfWord`: the label of a word.

## Main results

* `Cslib.Crypto.Garbling.PointPermute.labelBits_labelOfWord`: the word of the label of a
  `(k + 2)`-bit word is that word.
-/

public section

namespace Cslib.Crypto.Garbling.PointPermute

/-- A label as a `(k + 2)`-bit string: the `k + 1` bits of its key, then its colour. -/
@[expose] def labelEquiv (k : ℕ) : BitString (k + 2) ≃ BitString (k + 1) × Bool where
  toFun bits := (Fin.init bits, bits (Fin.last _))
  invFun label := Fin.snoc label.1 label.2
  left_inv bits := Fin.snoc_init_self bits
  right_inv label := by simp

/-- The word of the label of a bit string is the bit string. -/
private theorem labelBits_labelEquiv {k : ℕ} (bits : BitString (k + 2)) :
    labelBits (labelEquiv k bits) = List.ofFn bits := by
  simp only [labelBits_apply, labelEquiv, Equiv.coe_fn_mk]
  rw [List.ofFn_succ' bits, List.concat_eq_append]
  rfl

/-- The label of a `(k + 2)`-bit word. -/
@[expose] def labelOfWord (k : ℕ) (word : List Bool) : BitString (k + 1) × Bool :=
  labelEquiv k (BitString.ofList (k + 2) word)

/-- The label of a `(k + 2)`-bit word has that word. -/
theorem labelBits_labelOfWord {k : ℕ} {word : List Bool} (hword : word.length = k + 2) :
    labelBits (labelOfWord k word) = word := by
  rw [labelOfWord, labelBits_labelEquiv, BitString.ofFn_ofList hword]

/-- The key of the label of a `(k + 2)`-bit word is its first `k + 1` bits. -/
theorem ofFn_labelOfWord_fst {k : ℕ} {word : List Bool} (hword : word.length = k + 2) :
    List.ofFn (labelOfWord k word).1 = word.take (k + 1) := by
  rw [← take_labelBits, labelBits_labelOfWord hword]

/-- The colour of the label of a word is its bit `k + 1`. -/
theorem labelOfWord_snd (k : ℕ) (word : List Bool) :
    (labelOfWord k word).2 = word.getD (k + 1) false := rfl

end Cslib.Crypto.Garbling.PointPermute
