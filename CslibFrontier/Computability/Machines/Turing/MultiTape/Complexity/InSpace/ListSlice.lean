/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Mathlib.Data.List.GetD
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-!
# Native reversal and binary slicing of framed lists

Reversal and taking or dropping a binary-counted prefix use space linear in the actual encoded
list and counter. Every intermediate list is a prefix, suffix or reversal of stored input data;
large binary counts never cause a list of that length to be allocated.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.listReverse`: reverse a framed list.
* `Turing.MultiTapeTM.ComputableInSpace.listDrop`, `.listTake`: slice with a binary counter.
* `Turing.MultiTapeTM.ComputableInSpace.bitsDrop`, `.bitsGetD`, `.bitsReverse`: the same for a
  plain bit word, and reading one of its bits.
* `Turing.MultiTapeTM.ComputableInSpace.natShiftRight`: right shift by a binary offset.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

/-- Reverse a framed list in native space linear in its actual encoded storage. -/
theorem listReverse {α : Type} (enc : α ↪ List Bool) :
    ComputableInSpace List.reverse (encList enc) (encList enc)
      (fun l => (encList enc l).length) := by
  have hstate (l : List α) (i : ℕ) (_hi : i ≤ l.length) :
      (encList enc ((l.take i).foldl (fun acc a => a :: acc) [])).length ≤
        (encList enc l).length := by
    rw [List.foldl_flip_cons_eq_append', List.append_nil, length_encList_reverse]
    exact length_encList_take_le enc l i
  have hspace (l : List α) (i : ℕ) (hi : i < l.length) :
      (encPair (encList enc) enc
        ((l.take i).foldl (fun acc a => a :: acc) [], l[i])).length ≤
          4 * ((encList enc l).length + 1) := by
    have ha := length_le_encList_of_mem enc (List.getElem_mem hi)
    have hs := hstate l i hi.le
    enc_len
  have hfold := ComputableInSpace.foldl (encL := encList enc)
    (of_inO ComputableInDegree.id'.inO_one)
    (budget_const (Bs := fun l => (encList enc l).length) ([] : List α))
    (budget_cons (snd (encList enc) enc) (fst (encList enc) enc)) hspace hstate
  refine hfold.weaken (.of_le_linear 8 8 fun _ => by omega) |>.of_enc_eq fun l => ?_
  simp only [List.foldl_flip_cons_eq_append', List.append_nil]

/-- Drop a binary-counted prefix without allocating storage according to its numeric length. -/
theorem listDrop {α : Type} (enc : α ↪ List Bool) :
    ComputableInSpace (fun q : List α × ℕ => q.1.drop q.2)
      (encPair (encList enc) encNat) (encList enc)
      (fun q => (encPair (encList enc) encNat q).length) := by
  have htail : ComputableInSpace List.tail (encList enc) (encList enc)
      (fun l => (encList enc l).length) :=
    of_inO (.of_linear (ListEncoding.tail (enc₁ := enc)))
  have hlen (q : List α × ℕ) (k : ℕ) :
      (encList enc (List.tail^[k] q.1)).length ≤ (encList enc q.1).length := by
    rw [List.tail_iterate, ← q.1.take_append_drop k, encList_append, List.length_append]
    simp
  have h := iterate (snd (encList enc) encNat) (fst (encList enc) encNat) htail
    (Q := fun q => (encList enc q.1).length) (B := fun q => (encList enc q.1).length)
    (fun q k _ => hlen q k) (fun q k _ => hlen q k)
  exact (h.weaken (.of_le_linear 8 8 fun _ => by enc_len)).of_enc_eq fun q =>
    congrArg (encList enc) (List.tail_iterate q.1 q.2).symm

/-- Take a binary-counted prefix using space linear in the actual framed list and counter. -/
theorem listTake {α : Type} (enc : α ↪ List Bool) :
    ComputableInSpace (fun q : List α × ℕ => q.1.take q.2)
      (encPair (encList enc) encNat) (encList enc)
      (fun q => (encPair (encList enc) encNat q).length) := by
  have hl := fst (encList enc) encNat
  have hn := snd (encList enc) encNat
  have hrev := budget_comp_linear (listReverse enc) hl
  have hlen := budget_length hl
  have hcount := budget_natSub hlen hn
  have hdrop := budget_comp_linear (listDrop enc) (budget_prod hrev hcount)
  refine (budget_comp_linear (listReverse enc) hdrop).of_enc_eq ?_
  intro q
  rw [← List.reverse_take, List.reverse_reverse]

/-- Drop a binary-counted prefix of a bit word in space linear in the word and counter. -/
theorem bitsDrop : ComputableInSpace (fun p : List Bool × ℕ => p.1.drop p.2)
    (encPair encBits encNat) encBits (fun p => (encPair encBits encNat p).length) := by
  have htail : ComputableInSpace List.tail encBits encBits (fun w => w.length) :=
    of_inO (.of_linear (ListEncoding.tail encBool))
  have h := iterate (snd encBits encNat) (fst encBits encNat) htail
    (Q := fun p => p.1.length) (B := fun p => p.1.length)
    (fun p i _ => by simp [List.tail_iterate]) (fun p i _ => by simp [List.tail_iterate])
  refine h.weaken (.of_le_linear 8 8 fun p => ?_) |>.of_enc_eq ?_
  · enc_len
  · intro p
    rw [List.tail_iterate]

/-- Right shift a binary natural in space linear in the value and the binary offset.
The drop count is capped at the value's bit length. The suffix is already the canonical
encoding, including the empty word for zero. -/
theorem natShiftRight : ComputableInSpace (fun p : ℕ × ℕ => p.1 >>> p.2)
    (encPair encNat encNat) encNat (fun p => (encPair encNat encNat p).length) := by
  have hv := fst encNat encNat
  have ho := snd encNat encNat
  have hw := budget_comp_linear natSize hv
  have hbits := hv.of_enc_eq (encC := encBits) (g := fun p => p.1.bits) (fun _ => rfl)
  have hcount := budget_natMin ho hw
  refine (budget_comp_linear bitsDrop (budget_prod hbits hcount)).of_enc_eq fun p => ?_
  change (p.1 >>> p.2).bits = p.1.bits.drop (min p.2 p.1.size)
  rw [Nat.bits_shiftRight, ← Nat.size_eq_bits_len]
  exact List.drop_eq_drop_min

/-- Read the bit of a bit word at a binary index, or `fallback` beyond its end, in space linear in
the word and index. -/
theorem bitsGetD (fallback : Bool) : ComputableInSpace
    (fun p : List Bool × ℕ => p.1.getD p.2 fallback) (encPair encBits encNat) encBool
    (fun p => (encPair encBits encNat p).length) := by
  have hhead : ComputableInSpace (fun w : List Bool => w.headD fallback) encBits encBool
      (fun w => w.length) := of_inO (.of_linear (ListEncoding.headD fallback))
  -- Check the length before dropping, since an out-of-range binary index can be very large.
  have hlen := budget_comp_linear (of_inO ComputableInO.lengthNat) (fst encBits encNat)
  have hin := budget_natLt (snd encBits encNat) hlen
  have hread := budget_comp_linear hhead bitsDrop
  refine (budget_ite hin hread (budget_const fallback)).of_enc_eq fun p => ?_
  simp only [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop,
    decide_eq_true_eq]
  split_ifs with hi
  · rfl
  · rw [List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    rfl

/-- Reverse a bit word in space linear in its length. -/
theorem bitsReverse : ComputableInSpace List.reverse encBits encBits (fun w => w.length) :=
  of_inO ComputableInDegree.bitsReverse.inO_one

end Turing.MultiTapeTM.ComputableInSpace
