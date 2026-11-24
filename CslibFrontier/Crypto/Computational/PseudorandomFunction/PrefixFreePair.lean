/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Crypto.Primitives.PRF.PrefixFreeEncoding
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Foundations.Data.BitString.List.Rows

/-!
# Common block extension for a pair of flat queries

This is the query preparation step of [BonehShoup2023], v0.6, Theorem 7.3
(printed pp. 258–259). The algorithm appends a common block even when the queries are already
prefix-incomparable. Width is unary and the two queries are raw bit lists, framed as a pair.

## Main definitions

* `Cslib.Crypto.PRF.separatingWordBlock`: choose a shared block of the given width.

## Main results

* `Cslib.Crypto.PRF.separatingWordBlock_prefix_incomparable`: at positive width, appending the
  chosen block to two distinct aligned queries makes their words prefix-incomparable.
* `Cslib.Crypto.PRF.computableInPolyTime_separatingWordBlock`: the choice runs in polynomial time
  on all inputs.
-/

public section

namespace Cslib.Crypto.PRF

open Turing.MultiTapeTM

/-- Choose a common extension block from the all-zero and all-one blocks for two flat queries.
Only the complete input blocks inform the choice. -/
@[expose] def separatingWordBlock (width : ℕ) (u v : List Bool) : List Bool :=
  separatingBlock (List.replicate width false) (List.replicate width true)
    (BitString.listRows (u.length / width) width u)
    (BitString.listRows (v.length / width) width v)

/-- The result has the declared width on every input. -/
@[simp] theorem length_separatingWordBlock (width : ℕ) (u v : List Bool) :
    (separatingWordBlock width u v).length = width := by
  simp [separatingWordBlock, separatingBlock, apply_ite]

/-- The common extension makes two distinct, block-aligned queries prefix-incomparable
as bit lists. -/
theorem separatingWordBlock_prefix_incomparable {width : ℕ} (hwidth : 0 < width)
    {u v : List Bool} (hu : width ∣ u.length) (hv : width ∣ v.length) (hne : u ≠ v) :
    let c := separatingWordBlock width u v
    (¬ u ++ c <+: v ++ c) ∧ (¬ v ++ c <+: u ++ c) := by
  let us := BitString.listRows (u.length / width) width u
  let vs := BitString.listRows (v.length / width) width v
  let c := separatingWordBlock width u v
  change (¬ u ++ c <+: v ++ c) ∧ (¬ v ++ c <+: u ++ c)
  have huf : us.flatten = u := BitString.flatten_listRows_of_length (Nat.div_mul_cancel hu).symm
  have hvf : vs.flatten = v := BitString.flatten_listRows_of_length (Nat.div_mul_cancel hv).symm
  have hrows : us ≠ vs := fun he => hne (huf.symm.trans ((congrArg List.flatten he).trans hvf))
  have hblocks : List.replicate width false ≠ List.replicate width true := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hwidth.ne'
    simp [List.replicate_succ]
  have hsep : (¬ us ++ [c] <+: vs ++ [c]) ∧ (¬ vs ++ [c] <+: us ++ [c]) :=
    separatingBlock_prefix_incomparable hblocks hrows
  have rowWidth {rows : List (List Bool)} (h : ∀ row ∈ rows, row.length = width) :
      ∀ row ∈ rows ++ [c], row.length = width := by
    simpa only [List.forall_mem_append, List.forall_mem_singleton] using
      And.intro h (length_separatingWordBlock width u v)
  have hus : ∀ row ∈ us ++ [c], row.length = width :=
    rowWidth fun _ => BitString.length_of_mem_listRows
  have hvs : ∀ row ∈ vs ++ [c], row.length = width :=
    rowWidth fun _ => BitString.length_of_mem_listRows
  have huc : (us ++ [c]).flatten = u ++ c := by
    rw [List.flatten_append, List.flatten_singleton, huf]
  have hvc : (vs ++ [c]).flatten = v ++ c := by
    rw [List.flatten_append, List.flatten_singleton, hvf]
  rw [← huc, ← hvc]
  exact ⟨fun hp => hsep.1 (BitString.prefix_of_flatten_prefix hwidth hus hvs hp),
    fun hp => hsep.2 (BitString.prefix_of_flatten_prefix hwidth hvs hus hp)⟩

open ComputableInPolyTime in
/-- The input is a framed unary width, the framed first raw word, and the second raw word.
The common block is returned as a raw word in deterministic polynomial time. -/
theorem computableInPolyTime_separatingWordBlock :
    ComputableInPolyTime (fun p => separatingWordBlock p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  have hw := fst encUnary (encPair encBits encBits)
  have hu := (snd encUnary (encPair encBits encBits)).fst'
  have hv := (snd encUnary (encPair encBits encBits)).snd'
  have hnu := unary_div' hu.length_bits_comp hw
  have hnv := unary_div' hv.length_bits_comp hw
  have hru := bitsRowsWithInput hnu hw hu
  have hrv := bitsRowsWithInput hnv hw hv
  have hzero := (bitsReplicate false).comp hw
  have hone := (bitsReplicate true).comp hw
  have hnext := ite_decide (unary_le' hnu hnv)
    (optionGetDWithInput (getElem? hrv hnu) hzero)
    (optionGetDWithInput (getElem? hru hnv) hzero)
  simpa only [separatingWordBlock, separatingBlock, BitString.length_listRows,
    List.getD_eq_getElem?_getD, Function.comp_def] using ite' (beq hnext hzero) hone hzero

end Cslib.Crypto.PRF
