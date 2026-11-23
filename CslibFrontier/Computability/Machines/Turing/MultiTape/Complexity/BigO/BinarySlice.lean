/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import Mathlib.Data.List.GetD

/-!
# Binary-indexed slices with linear dependence on the stored word

The offset and length of a slice are binary. Measuring the encoded word and capping both counts
at its encoded length makes unary traversal safe even for arbitrarily large indices. Only the
binary counts and binary encoded length enter polynomial-time arithmetic; the list itself is
read by the existing linear unary cutters.

These are original native multitape machine certificates. In the bound `N + s ^ d`, `N` is the
complete encoded word length and `s` is the sum of the binary lengths of `N` and the two indices,
plus one. No output list or random-access operation is supplied to the machine.

## Main results

* `Turing.MultiTapeTM.ComputableInO.exists_listSlice_binary`: a slice of a framed list.
* `Turing.MultiTapeTM.ComputableInO.exists_bitsSlice_binary`: a slice of a raw bit word.
* `Turing.MultiTapeTM.ComputableInO.exists_listGetElem?_binary`: one framed list element.
* `Turing.MultiTapeTM.ComputableInO.exists_bitsGetD_binary`: one bit, defaulting to `false`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

private structure Header where
  /-- Encoded length of the stored list, in bits. -/
  bound : ℕ
  /-- First element of the requested slice. -/
  offset : ℕ
  /-- Number of requested elements. -/
  count : ℕ

private enc_structure encHeader : Header where
  bound : encNat, offset : encNat, count : encNat

private def cap (h : Header) : ℕ × ℕ := (min h.offset h.bound, min h.count h.bound)

private theorem cap_polyTime : ComputableInPolyTime cap encHeader (encPair encNat encNat) := by
  have hn := encHeader_bound_deg.computableInPolyTime
  have hi := encHeader_offset_deg.computableInPolyTime
  have hk := encHeader_count_deg.computableInPolyTime
  have hleft := (ComputableInPolyTime.binary_le' hi hn).ite hi hn
  have hright := (ComputableInPolyTime.binary_le' hk hn).ite hk hn
  exact (hleft.prod hright).of_enc_eq fun h => by simp [cap, min_def]

private theorem exists_slice_binary {α : Type} (encL : List α ↪ List Bool)
    (hlen : ∀ xs : List α, xs.length ≤ (encL xs).length)
    (hdrop : ComputableInDegree (fun p : List α × ℕ => p.1.drop p.2)
      (encPair encL encUnary) encL 1 1)
    (htake : ComputableInDegree (fun p : List α × ℕ => p.1.take p.2)
      (encPair encL encUnary) encL 1 1) :
    ∃ d, ComputableInO
      (fun ((xs, (offset, count)) : List α × (ℕ × ℕ)) => (xs.drop offset).take count)
      (encPair encL (encPair encNat encNat)) encL
      (fun ((xs, (offset, count)) : List α × (ℕ × ℕ)) => (encL xs).length +
        ((encL xs).length.size + offset.size + count.size + 1) ^ d)
      (fun ((xs, (offset, count)) : List α × (ℕ × ℕ)) => (encL xs).length +
        ((encL xs).length.size + offset.size + count.size + 1) ^ d) := by
  let encInput := encPair encL (encPair encNat encNat)
  let measure (q : List α × (ℕ × ℕ)) : Header :=
    ⟨(encL q.1).length, q.2.1, q.2.2⟩
  let short (q : List α × (ℕ × ℕ)) :=
    (encL q.1).length.size + q.2.1.size + q.2.2.size + 1
  have hx := fst encL (encPair encNat encNat)
  have hn := snd encL (encPair encNat encNat)
  have hw : ComputableInO (fun q : List α × (ℕ × ℕ) => encL q.1)
      encInput encBits (fun q => (encInput q).length) (fun q => (encInput q).length) :=
    hx.of_enc_eq fun _ => rfl
  have hm := encHeader_mk_inO (lengthNat.comp hw) hn.fst' hn.snd'
  have hm' : ComputableInO measure encInput encHeader
      (fun q => (encInput q).length) (fun q => (encInput q).length) := by
    refine hm.mono 4 (fun q => ?_) (fun q => ?_) <;>
      have h := length_le_encPair_left encL (encPair encNat encNat) q <;>
      dsimp only [encInput, measure, Function.comp_apply] at * <;> omega
  obtain ⟨T, S, hT, hS, hc⟩ := cap_polyTime.exists_computableInO
  have hc' := hc.comp hm'
  have ho := natToUnary.comp hc'.fst'
  have hk := natToUnary.comp hc'.snd'
  have hd := hdrop.inO_one.comp_linear (hx.prod ho)
  have ht := htake.inO_one.comp_linear (hd.prod hk)
  have heq (q : List α × (ℕ × ℕ)) :
      (q.1.drop (cap (measure q)).1).take (cap (measure q)).2 =
        (q.1.drop q.2.1).take q.2.2 := by
    have hh := hlen q.1
    dsimp only [cap, measure]
    by_cases hi : q.2.1 ≤ (encL q.1).length
    · rw [Nat.min_eq_left hi]
      by_cases hk : q.2.2 ≤ (encL q.1).length
      · rw [Nat.min_eq_left hk]
      · have hl : (q.1.drop q.2.1).length ≤ (encL q.1).length := by
          simpa only [List.length_drop] using (Nat.sub_le q.1.length q.2.1).trans hh
        rw [Nat.min_eq_right (by omega), List.take_of_length_le hl,
          List.take_of_length_le (by omega)]
    · have hbound : (encL q.1).length ≤ q.2.1 := by omega
      rw [Nat.min_eq_right hbound, List.drop_eq_nil_of_le hh,
        List.drop_eq_nil_of_le (hh.trans hbound), List.take_nil, List.take_nil]
  have hmSize : PolyBounded short (fun q => (encHeader (measure q)).length) :=
    PolyBounded.of_forall_le 2 1 fun q => by
      simp only [encHeader_apply, encHeaderFields, length_encPair, encNat_apply,
        Nat.size_eq_bits_len, measure, short, pow_one]
      omega
  let minor (q : List α × (ℕ × ℕ)) :=
    6 * short q + 2 * (T (measure q) + S (measure q))
  have hminor : PolyBounded short minor :=
    ((PolyBounded.const 6).mul PolyBounded.self).add
      ((PolyBounded.const 2).mul ((hT.comp hmSize).add (hS.comp hmSize)))
  obtain ⟨c, d, hb⟩ := hminor.exists_le_linear_add_pow
    (fun q => (encL q.1).length) 8 (fun q => by simp [short])
  refine ⟨d, (ht.of_enc_eq (fun q => congrArg encL (heq q).symm)).mono c
    (fun q => ?_) (fun q => ?_)⟩ <;>
    refine le_trans ?_ (hb q) <;>
    have ho := Nat.min_le_right q.2.1 (encL q.1).length <;>
    have hk := Nat.min_le_right q.2.2 (encL q.1).length <;>
    simp only [Function.comp_apply, cap, measure, encInput, length_encPair, encNat_apply,
      Nat.size_eq_bits_len, minor, short] at * <;> omega

/-- Slice a framed list at binary indices. The full list is charged linearly, and all
superlinear work depends only on the binary indices and binary encoded length. -/
theorem exists_listSlice_binary {α : Type} (encA : α ↪ List Bool) :
    ∃ d, ComputableInO
      (fun ((xs, (offset, count)) : List α × (ℕ × ℕ)) => (xs.drop offset).take count)
      (encPair (encList encA) (encPair encNat encNat)) (encList encA)
      (fun ((xs, (offset, count)) : List α × (ℕ × ℕ)) => (encList encA xs).length +
        ((encList encA xs).length.size + offset.size + count.size + 1) ^ d)
      (fun ((xs, (offset, count)) : List α × (ℕ × ℕ)) => (encList encA xs).length +
        ((encList encA xs).length.size + offset.size + count.size + 1) ^ d) :=
  exists_slice_binary (encList encA) (SizedListEncoding.length_le (encA := encA))
    (ComputableInDegree.dropUnary encA) (ComputableInDegree.takeUnary encA)

/-- Slice a raw bit word at binary indices, including empty words and out-of-range indices. -/
theorem exists_bitsSlice_binary :
    ∃ d, ComputableInO
      (fun ((xs, (offset, count)) : List Bool × (ℕ × ℕ)) => (xs.drop offset).take count)
      (encPair encBits (encPair encNat encNat)) encBits
      (fun ((xs, (offset, count)) : List Bool × (ℕ × ℕ)) => xs.length +
        (xs.length.size + offset.size + count.size + 1) ^ d)
      (fun ((xs, (offset, count)) : List Bool × (ℕ × ℕ)) => xs.length +
        (xs.length.size + offset.size + count.size + 1) ^ d) :=
  exists_slice_binary encBits (fun _ => le_rfl)
    ComputableInDegree.bitsDrop ComputableInDegree.bitsTake

private theorem exists_slice_one {α : Type} (encL : List α ↪ List Bool)
    (hslice : ∃ d, ComputableInO
      (fun ((xs, (offset, count)) : List α × (ℕ × ℕ)) => (xs.drop offset).take count)
      (encPair encL (encPair encNat encNat)) encL
      (fun ((xs, (offset, count)) : List α × (ℕ × ℕ)) => (encL xs).length +
        ((encL xs).length.size + offset.size + count.size + 1) ^ d)
      (fun ((xs, (offset, count)) : List α × (ℕ × ℕ)) => (encL xs).length +
        ((encL xs).length.size + offset.size + count.size + 1) ^ d)) :
    ∃ d, ComputableInO (fun ((xs, index) : List α × ℕ) => (xs.drop index).take 1)
      (encPair encL encNat) encL
      (fun ((xs, index) : List α × ℕ) => (encL xs).length +
        ((encL xs).length.size + index.size + 1) ^ d)
      (fun ((xs, index) : List α × ℕ) => (encL xs).length +
        ((encL xs).length.size + index.size + 1) ^ d) := by
  obtain ⟨d₀, hs⟩ := hslice
  have hp := (ComputableInDegree.fst encL encNat).prod
    ((ComputableInDegree.snd encL encNat).prod
      (ComputableInDegree.const (encIn := encPair encL encNat) (encMid := encNat) 1))
  have hread := hs.comp hp.inO_one
  let short (q : List α × ℕ) := (encL q.1).length.size + q.2.size + 1
  have hm : PolyBounded short (fun q => 2 * short q + (short q + 1) ^ d₀) :=
    ((PolyBounded.const 2).mul PolyBounded.self).add
      ((PolyBounded.self.add (PolyBounded.const 1)).pow d₀)
  obtain ⟨c, d, hb⟩ := hm.exists_le_linear_add_pow (fun q => (encL q.1).length) 3
    (fun q => by simp [short])
  refine ⟨d, hread.mono c (fun q => ?_) (fun q => ?_)⟩ <;>
    refine le_trans ?_ (hb q) <;>
    simp only [length_encPair, encNat_apply,
      Nat.size_eq_bits_len, short, Nat.size_one] at * <;> omega

/-- Read one framed list element at a binary index. Out-of-range indices return `none`, and
the complete encoded list occurs only linearly in both resource bounds. -/
theorem exists_listGetElem?_binary {α : Type} [Inhabited α] (encA : α ↪ List Bool) :
    ∃ d, ComputableInO (fun ((xs, index) : List α × ℕ) => xs[index]?)
      (encPair (encList encA) encNat) (encOption encA)
      (fun ((xs, index) : List α × ℕ) => (encList encA xs).length +
        ((encList encA xs).length.size + index.size + 1) ^ d)
      (fun ((xs, index) : List α × ℕ) => (encList encA xs).length +
        ((encList encA xs).length.size + index.size + 1) ^ d) := by
  obtain ⟨d, hs⟩ := exists_slice_one (encList encA) (exists_listSlice_binary encA)
  have h := ComputableInDegree.head?_one.inO_one.comp_linear hs
  exact ⟨d, h.of_enc_eq fun _ => by simp [List.head?_take]⟩

/-- Read one raw bit at a binary index, returning `false` outside the word. Measuring and
traversing the raw word costs linear time; only its binary length and index enter the polynomial. -/
theorem exists_bitsGetD_binary :
    ∃ d, ComputableInO (fun ((xs, index) : List Bool × ℕ) => xs.getD index false)
      (encPair encBits encNat) encBool
      (fun ((xs, index) : List Bool × ℕ) => xs.length + (xs.length.size + index.size + 1) ^ d)
      (fun ((xs, index) : List Bool × ℕ) => xs.length + (xs.length.size + index.size + 1) ^ d) := by
  obtain ⟨d, hs⟩ := exists_slice_one encBits exists_bitsSlice_binary
  have h := (ComputableInDegree.headD (enc₁ := encBool) (enc := encBits) false).inO_one
    |>.comp_linear hs
  exact ⟨d, h.of_enc_eq fun _ => by
    simp [List.headD_eq_head?_getD, List.head?_take, List.getD_eq_getElem?_getD]⟩

end Turing.MultiTapeTM.ComputableInO
