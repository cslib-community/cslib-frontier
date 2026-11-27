/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Label
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Foundations.Data.BitString.List.Operations

/-!
# Garbling labels as words

At parameter `k` a garbling label is a `(k + 1)`-bit key and a colour bit,
`BitString (k + 1) × Bool`. Garbling schemes that work on words, and the circular correlation
robustness assumption on word hash families, write a label as its word `labelBits`: the key's bits
followed by the colour, `k + 2` bits, which is the reply of `labelCodec k`. The word of a sum of
labels is the XOR of their words (`labelBits_add`).

This module also reads labels back from words. `labelEquiv k` identifies `(k + 2)`-bit strings
with labels, splitting off the last bit as the colour, and `labelOfWord k word` is the label of the
first `k + 2` bits of `word`, padded with `false`. On a word of `k + 2` bits, `labelBits` undoes it
(`labelBits_labelOfWord`).

## Main definitions

* `Cslib.Crypto.Garbling.labelBits`: the word of a label.
* `Cslib.Crypto.Garbling.labelEquiv`: labels as `(k + 2)`-bit strings.
* `Cslib.Crypto.Garbling.labelOfWord`: the label of a word.

## Main results

* `Cslib.Crypto.Garbling.labelBits_labelOfWord`: the word of the label of a `(k + 2)`-bit word is
  that word.
-/

public section

namespace Cslib.Crypto.Garbling

/-! ### Words of labels -/

/-- The word of a label: the bits of its key, then its colour. It is the reply of `labelCodec k`,
through which a label oracle answers on words; that reply does not depend on the tweak, so
`labelBits label = (labelCodec k).encodeReply t label` by `rfl` for every tweak `t`. -/
@[expose] def labelBits {k : ℕ} (label : BitString (k + 1) × Bool) : List Bool :=
  (labelCodec k).encodeReply 0 label

/-- A label word is the bits of its key followed by its colour. -/
theorem labelBits_apply {k : ℕ} (label : BitString (k + 1) × Bool) :
    labelBits label = List.ofFn label.1 ++ [label.2] :=
  rfl

/-- A label word has `k + 2` bits. -/
@[simp] theorem length_labelBits {k : ℕ} (label : BitString (k + 1) × Bool) :
    (labelBits label).length = k + 2 := by
  simp [labelBits_apply]

/-- The word of a sum of labels is the XOR of their words. -/
theorem labelBits_add {k : ℕ} (x y : BitString (k + 1) × Bool) :
    labelBits (x + y) = List.zipWith xor (labelBits x) (labelBits y) := by
  simp only [labelBits_apply, Prod.fst_add, Prod.snd_add, BitString.ofFn_add]
  rw [List.zipWith_append (by simp)]
  simp [Bool.add_eq_xor]

/-- The colour of a label word is its last bit. -/
theorem getD_labelBits {k : ℕ} (label : BitString (k + 1) × Bool) :
    (labelBits label).getD (k + 1) false = label.2 := by
  simp [labelBits_apply, List.getD_eq_getElem?_getD]

/-- The key of a label word is its first `k + 1` bits. -/
@[simp] theorem take_labelBits {k : ℕ} (label : BitString (k + 1) × Bool) :
    (labelBits label).take (k + 1) = List.ofFn label.1 := by
  simp [labelBits_apply]

/-! ### Labels of words -/

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

end Cslib.Crypto.Garbling
