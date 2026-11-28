/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Certificate
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Foundations.Data.BitString.List.Binary

/-!
# Fixed-width binary certificates for labelled branches

Each occurrence index occupies one fixed-width binary block. The width is fixed by the machine,
not by its input. Distinct indices remain distinct even when their actions or successors agree.

## Main definitions

* `Turing.MultiTapeCTM.binaryCertificate`: concatenate the fixed-width index codes.
* `Turing.MultiTapeCTM.binaryIndices`: read a fixed number of binary blocks as indices.

## Main results

* `Turing.MultiTapeCTM.binaryIndices_binaryCertificate`: decoding the code recovers its indices.
* `Turing.MultiTapeCTM.binaryCertificate_binaryIndices`: full-width words are recovered exactly.
* `Turing.MultiTapeCTM.card_binaryCertificateAccepts`: binary words preserve exact branch counts.
* `Turing.MultiTapeCTM.decodeCertificate_indices_lt`: a transition-list bound also bounds every
  index in a successful canonical certificate, including terminal padding.
* `Turing.MultiTapeCTM.exists_branchWidth`: finite control and alphabet fix one positive block
  width whose codes cover every transition list.

## References

The binary representation is the existing `Cslib.BitString.binaryWord`; its module records the
original formalization credit. The occurrence and padding semantics are `MultiTape.Counting` and
`MultiTape.Counting.Certificate`.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib

/-- Encode each occurrence index as one fixed-width block, in chronological order. -/
def binaryCertificate (width : ℕ) (indices : List ℕ) : List Bool :=
  indices.flatMap (BitString.binaryWord width)

/-- Decode a specified number of fixed-width blocks using the existing bit-string row view. -/
def binaryIndices (count width : ℕ) (word : List Bool) : List ℕ :=
  (BitString.listRows count width word).map BitString.binaryValue

@[simp]
theorem length_binaryIndices (count width : ℕ) (word : List Bool) :
    (binaryIndices count width word).length = count := by
  simp [binaryIndices]

/-- Bounded indices each contribute exactly one full block. -/
theorem length_binaryCertificate {width : ℕ} {indices : List ℕ}
    (h : ∀ index ∈ indices, index < 2 ^ width) :
    (binaryCertificate width indices).length = indices.length * width := by
  induction indices with
  | nil => simp [binaryCertificate]
  | cons index rest ih =>
    rw [binaryCertificate, List.flatMap_cons, List.length_append, List.length_cons,
      BitString.length_binaryWord (h index List.mem_cons_self), ← binaryCertificate,
      ih fun i hi => h i (List.mem_cons_of_mem _ hi), Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Encoding followed by block decoding preserves every bounded occurrence index. -/
theorem binaryIndices_binaryCertificate {width : ℕ} {indices : List ℕ}
    (h : ∀ index ∈ indices, index < 2 ^ width) :
    binaryIndices indices.length width (binaryCertificate width indices) = indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [binaryCertificate, List.flatMap_cons, List.length_cons, binaryIndices,
      BitString.listRows_succ_append rest.length width
        (BitString.length_binaryWord (h index List.mem_cons_self)),
      List.map_cons, BitString.binaryValue_binaryWord]
    exact congrArg (index :: ·) (ih fun i hi => h i (List.mem_cons_of_mem _ hi))

/-- Decoding and re-encoding a full-width word preserves all bits, including leading zeros. -/
theorem binaryCertificate_binaryIndices {count width : ℕ} {word : List Bool}
    (h : word.length = count * width) :
    binaryCertificate width (binaryIndices count width word) = word := by
  induction count generalizing word with
  | zero =>
    cases List.length_eq_zero_iff.mp (by simpa using h)
    rfl
  | succ count ih =>
    have htake : (word.take width).length = width := by grind
    have hrows := List.take_append_drop width word ▸
      BitString.listRows_succ_append count width htake (word.drop width)
    have hblock : BitString.binaryWord width (BitString.binaryValue (word.take width)) =
        word.take width :=
      BitString.binaryValue_injective_of_length_eq
        (by rw [BitString.length_binaryWord
          ((BitString.binaryValue_lt_two_pow _).trans_eq (by rw [htake])), htake])
        (by simp)
    simp only [binaryIndices, hrows, List.map_cons, binaryCertificate, List.flatMap_cons, hblock]
    exact (congrArg (word.take width ++ ·)
      (ih (by simp only [List.length_drop, h, Nat.succ_mul, Nat.add_sub_cancel]))).trans
      (List.take_append_drop width word)

/-- Every used index is below the occurrence-list bound, without identifying equal successors. -/
theorem runBranch_indices_lt {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (machine : MultiTapeCTM k Symbol State) {bound : ℕ}
    (hbound : ∀ cfg : Cfg k Symbol State input, (machine.actions cfg).length ≤ bound)
    {cfg final : Cfg k Symbol State input} {choices : List ℕ}
    (hrun : machine.runBranch cfg choices = some final) :
    ∀ index ∈ choices, index < bound := by
  induction choices generalizing cfg with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hrun
    exact List.forall_mem_cons.mpr
      ⟨((machine.step?_eq_some_iff cfg next first).mp hstep).1.trans_le (hbound cfg), ih hrest⟩

/-- The same positive bound covers actual indices and the forced zero padding after halting. -/
theorem decodeCertificate_indices_lt {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (machine : MultiTapeCTM k Symbol State) {bound : ℕ} (hpos : 0 < bound)
    (hbound : ∀ cfg : Cfg k Symbol State input, (machine.actions cfg).length ≤ bound)
    {cfg final : Cfg k Symbol State input} {word choices : List ℕ}
    (hdecode : machine.decodeCertificate cfg word = some (choices, final)) :
    ∀ index ∈ word, index < bound := by
  obtain ⟨hrun, _, hword⟩ := machine.decodeCertificate_sound hdecode
  rw [hword]
  exact List.forall_mem_append.mpr ⟨machine.runBranch_indices_lt hbound hrun,
    fun _ h => (List.mem_replicate.mp h).2 ▸ hpos⟩

/-- Fixed-width binary words count the canonical occurrence certificates exactly, for any
terminal verdict. This is the common counting bijection for executable certificate checkers
and native binary-choice replay machines. The proof is extracted from
`Checker.acceptCount_checkBinary` by Samuel Schlesinger. -/
theorem card_binaryCertificateAccepts {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (machine : MultiTapeCTM k Symbol State) {width : ℕ}
    (cfg : Cfg k Symbol State input)
    (hbound : ∀ cfg : Cfg k Symbol State input, (machine.actions cfg).length ≤ 2 ^ width)
    (count : ℕ) (verdict : List Symbol → Bool) :
    (Finset.univ.filter fun word : BitString (count * width) =>
      machine.certificateAccepts verdict cfg
        (binaryIndices count width (List.ofFn word)) = true).card =
      machine.branchCount verdict count cfg := by
  rw [← machine.certificateCount_eq_branchCount]
  unfold certificateCount
  refine Finset.card_bij (fun word _ => binaryIndices count width (List.ofFn word)) ?_ ?_ ?_
  · intro word hword
    have hcheck := (Finset.mem_filter.mp hword).2
    refine Finset.mem_filter.mpr ⟨(machine.mem_certificates_iff _ _ _).mpr ⟨by simp, ?_⟩,
      hcheck⟩
    unfold certificateAccepts at hcheck
    cases hdecode : machine.decodeCertificate cfg
        (binaryIndices count width (List.ofFn word)) <;>
      simp_all
  · intro left _ right _ heq
    apply List.ofFn_injective
    calc
      List.ofFn left = binaryCertificate width (binaryIndices count width (List.ofFn left)) :=
        (binaryCertificate_binaryIndices List.length_ofFn).symm
      _ = binaryCertificate width (binaryIndices count width (List.ofFn right)) :=
        congrArg (binaryCertificate width) heq
      _ = List.ofFn right := binaryCertificate_binaryIndices List.length_ofFn
  · intro indices hindices
    obtain ⟨hcert, hverdict⟩ := Finset.mem_filter.mp hindices
    obtain ⟨hlen, hvalid⟩ := (machine.mem_certificates_iff _ _ _).mp hcert
    obtain ⟨⟨choices, final⟩, hdecode⟩ := Option.isSome_iff_exists.mp hvalid
    have hsmall := machine.decodeCertificate_indices_lt (Nat.two_pow_pos _) hbound hdecode
    have hround : binaryIndices count width
        (List.ofFn (BitString.ofList (count * width) (binaryCertificate width indices))) =
        indices := by
      rw [BitString.ofFn_ofList (by rw [length_binaryCertificate hsmall, hlen]),
        ← hlen, binaryIndices_binaryCertificate hsmall]
    exact ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hround.symm ▸ hverdict⟩, hround⟩

/-- A finite-control machine over a finite alphabet has one positive block width whose `2 ^ width`
codes cover every transition list, as `card_binaryCertificateAccepts` requires. -/
theorem exists_branchWidth {k : ℕ} {Symbol State : Type*} [Finite State] [Finite Symbol]
    (machine : MultiTapeCTM k Symbol State) :
    ∃ width : ℕ, 0 < width ∧ ∀ (input : List Symbol) (cfg : Cfg k Symbol State input),
      (machine.actions cfg).length ≤ 2 ^ width := by
  obtain ⟨bound, hbound⟩ := machine.exists_branchBound
  exact ⟨bound + 1, bound.succ_pos, fun input cfg =>
    (hbound input cfg).trans (Nat.lt_two_pow_self.trans' bound.lt_succ_self).le⟩

end Turing.MultiTapeCTM
