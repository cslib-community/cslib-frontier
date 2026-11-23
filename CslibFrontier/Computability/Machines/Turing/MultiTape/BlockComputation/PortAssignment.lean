/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.BinarySlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import Mathlib.Data.List.GetD

/-!
# Checking a proposed local assignment with one challenged bit

The proposed ports and local word are fixed before a universal binary index is chosen. The
terminal checks the local word's length on every branch and compares the challenged local bit
with its one addressed global bit. Padded indices accept only after the length guard succeeds.
Thus an empty port list still rejects every nonempty local word.

This original game accepts exactly `DescribedNetwork.wordBits`, including repeated ports and
ports beyond the global word. Its native terminal charges the global word linearly; only the
proposed ports, local bits, choice bits, and binary global length enter a polynomial.
-/

public section

namespace Turing.MultiTapeTM.PortAssignment

open Cslib Cslib.BitString Cslib.Circuits.Frontier
open ComputableInPolyTime MultiTapeATM QuantifiedWord

/-- A proposed ordered list of binary ports and its proposed local assignment. -/
structure Context where
  /-- Binary global bit positions, retained in their proposed order. -/
  ports : List ℕ
  /-- Proposed bits at those positions, with the same required length. -/
  bits : List Bool
  deriving DecidableEq

/-- A framed list of binary port numbers followed by the raw proposed bits. -/
enc_structure encContext : Context where ports : (encList encNat), bits : encBits

/-- One assignment restriction request, with its large global word separate from short data. -/
structure Input where
  /-- Proposed ports and local assignment, fixed before the challenge. -/
  context : Context
  /-- Raw global assignment, with missing positions interpreted as `false`. -/
  word : List Bool
  deriving DecidableEq

/-- Framed short context followed by the raw global word. -/
enc_structure encInput : Input where context : encContext, word : encBits

/-- Framed short context followed by the binary challenge word. -/
abbrev encData : Context × List Bool ↪ List Bool := encPair encContext encBits

/-- Framed complete input followed by the binary challenge word. -/
abbrev encChallenge : Input × List Bool ↪ List Bool := encPair encInput encBits

/-- Universal choices for a binary index into the proposed port list. -/
@[expose] def flags (a : Context) : List Bool := List.replicate a.ports.length.size true

/-- Only the binary length of the global word enters the short input size. -/
@[expose] def shortSize (a : Input) : ℕ :=
  (encContext a.context).length + a.word.length.size + 1

/-- Short terminal size includes the choice word and only the binary global length. -/
@[expose] def challengeSize (x : Input × List Bool) : ℕ :=
  (encData (x.1.context, x.2)).length + x.1.word.length.size + 1

/-- The length guard is checked even for a padded index or an empty port list. -/
@[expose] def check (x : Input × List Bool) : Bool :=
  let (a, choices) := x
  let j := ofBits choices
  decide (a.context.bits.length = a.context.ports.length) &&
    if j < a.context.ports.length then
      a.context.bits.getD j false == a.word.getD (a.context.ports.getD j 0) false
    else true

/-- One universally challenged position characterizes the entire proposed restriction. The
candidate is fixed before the challenge, and the conclusion retains port order and repetitions. -/
theorem plays_check (a : Input) :
    plays (fun xs => check (a, xs) = true) [] (flags a.context) ↔
      a.context.bits = DescribedNetwork.wordBits a.word a.context.ports := by
  have hfields : plays (fun xs => check (a, xs) = true) [] (flags a.context) ↔
      ∀ j : Fin (2 ^ a.context.ports.length.size),
        (decide (a.context.bits.length = a.context.ports.length) &&
          if j.val < a.context.ports.length then
            a.context.bits.getD j.val false ==
              a.word.getD (a.context.ports.getD j.val 0) false
          else true) = true := by
    rw [show flags a.context = List.replicate a.context.ports.length.size true ++ [] by
      simp [flags], plays_forall_field]
    apply forall_congr'
    intro j
    simp only [plays, List.nil_append, check, ofBits_lowBits j.isLt]
  rw [hfields]
  constructor
  · intro h
    have hlen : a.context.bits.length = a.context.ports.length :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp (h 0)).1
    apply List.ext_getElem (by simp [DescribedNetwork.wordBits, hlen])
    intro j hj hj'
    have hp : j < a.context.ports.length := by omega
    have hb := (Bool.and_eq_true_iff.mp (h ⟨j, hp.trans (Nat.lt_size_self _)⟩)).2
    simpa only [hp, ↓reduceIte, beq_iff_eq, DescribedNetwork.wordBits, List.getElem_map,
      List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hp] using hb
  · intro h j
    have hlen : a.context.bits.length = a.context.ports.length := by
      rw [h]
      simp [DescribedNetwork.wordBits]
    by_cases hj : j.val < a.context.ports.length
    · simp only [hlen, decide_true, Bool.true_and, hj, ↓reduceIte, beq_iff_eq]
      rw [h]
      simp [DescribedNetwork.wordBits, List.getD, List.getElem?_eq_getElem hj]
    · simp [hlen, hj]

private def data (x : Input × List Bool) : Context × List Bool := (x.1.context, x.2)

private def address (x : Context × List Bool) : ℕ := x.1.ports.getD (ofBits x.2) 0

private def finish (x : (Context × List Bool) × Bool) : Bool :=
  let ((a, choices), bit) := x
  decide (a.bits.length = a.ports.length) &&
    if ofBits choices < a.ports.length then a.bits.getD (ofBits choices) false == bit
    else true

private theorem data_deg : ComputableInDegree data encChallenge encData 1 1 :=
  ((encInput_context_deg.comp (ComputableInDegree.fst encInput encBits)).prod
    (ComputableInDegree.snd encInput encBits)).mono

private theorem address_polyTime : ComputableInPolyTime address encData encNat :=
  listGetD_binary 0 (encContext_ports_polyTime (fst encContext encBits))
    (bitsToNat.comp (snd encContext encBits))

private theorem finish_polyTime :
    ComputableInPolyTime finish (encPair encData encBool) encBool := by
  have hd := fst encData encBool
  have ha := hd.fst'
  have hp := encContext_ports_polyTime ha
  have hb := encContext_bits_polyTime ha
  have hj := bitsToNat.comp hd.snd'
  have hl := (length_list encNat).comp hp
  have hg := decide_eq' (length_bits.comp hb) hl
  have hlocal := listGetD_binary (encA := encBool) false hb hj
  exact bool_and' hg (ite_decide (binary_lt' hj (unary_to_binary.comp hl))
    (hlocal.beq (snd encData encBool)) (const true))

/-- All universal flags are computed from the short context alone. -/
theorem flags_polyTime : ComputableInPolyTime flags encContext encBits :=
  (bitsReplicate true).comp (binary_size.comp (unary_to_binary.comp
    ((length_list encNat).comp encContext_ports_deg.computableInPolyTime)))

/-- Framing charges the global word twice and the short challenge data by a fixed factor. -/
theorem length_encChallenge (x : Input × List Bool) :
    (encChallenge x).length ≤ 2 * x.1.word.length + 2 * challengeSize x + 1 := by
  simp only [encChallenge, encInput_apply, encInputFields, length_encPair,
    encBits_apply, challengeSize, encData]
  omega

/-- The terminal makes a fixed number of linear passes over the global word and computes only
on the short metadata otherwise. There is one global bit read on each branch. -/
theorem exists_check_inO : ∃ d, ComputableInO check encChallenge encBool
    (fun x => x.1.word.length + challengeSize x ^ d)
    (fun x => x.1.word.length + challengeSize x ^ d) := by
  obtain ⟨dA, eA, hA⟩ := address_polyTime.exists_degree
  obtain ⟨dB, hB⟩ := ComputableInO.exists_bitsGetD_binary
  have hword : ComputableInDegree (fun x : Input × List Bool => x.1.word)
      encChallenge encBits 1 1 :=
    (encInput_word_deg.comp (ComputableInDegree.fst encInput encBits)).mono
  have haddress := hA.inO.comp data_deg.inO_one
  have hbit := hB.comp (hword.inO_one.prod haddress)
  have hdataSize : PolyBounded challengeSize (fun x : Input × List Bool =>
      (encData (data x)).length) := PolyBounded.self.mono (fun x => by
    simp only [challengeSize, data]; omega)
  have haddressSize : PolyBounded challengeSize (fun x : Input × List Bool =>
      (address (data x)).size) := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using
      address_polyTime.polyBounded_length.comp (g := data) hdataSize
  have hwordSize : PolyBounded challengeSize (fun x : Input × List Bool =>
      x.1.word.length.size) := PolyBounded.self.mono (fun x => by
    simp only [challengeSize]; omega)
  let minor (x : Input × List Bool) := 4 * challengeSize x + 2 +
    (challengeSize x + 1) ^ dA + (x.1.word.length.size + (address (data x)).size + 1) ^ dB
  have hminor : PolyBounded challengeSize minor :=
    ((((PolyBounded.const 4).mul PolyBounded.self).add (.const 2)).add
      ((PolyBounded.self.add (.const 1)).pow dA)).add
        (((hwordSize.add haddressSize).add (.const 1)).pow dB)
  obtain ⟨cB, D, hboundB⟩ := hminor.exists_le_linear_add_pow
    (fun x => x.1.word.length) 5 (fun x => by simp [challengeSize])
  have hbit' : ComputableInO
      (fun x : Input × List Bool => x.1.word.getD (address (data x)) false)
      encChallenge encBool (fun x => x.1.word.length + challengeSize x ^ D)
      (fun x => x.1.word.length + challengeSize x ^ D) := by
    refine hbit.mono cB (fun x => ?_) (fun x => ?_) <;>
      refine le_trans ?_ (hboundB x) <;>
      have hlen := length_encChallenge x <;>
      have hp := Nat.pow_le_pow_left
        (show (encData (data x)).length + 1 ≤ challengeSize x + 1 by
          simp only [challengeSize, data]; omega) dA <;>
      dsimp only [Function.comp_apply, minor] at * <;> omega
  obtain ⟨dF, eF, hF⟩ := finish_polyTime.exists_degree
  have hcheck := hF.inO.comp (data_deg.inO_one.prod hbit')
  have hminorF : PolyBounded challengeSize (fun x : Input × List Bool =>
      2 * challengeSize x + 1 + challengeSize x ^ D + (2 * challengeSize x + 3) ^ dF) :=
    ((((PolyBounded.const 2).mul PolyBounded.self).add (.const 1)).add
      (PolyBounded.self.pow D)).add
        ((((PolyBounded.const 2).mul PolyBounded.self).add (.const 3)).pow dF)
  obtain ⟨c, d, hb⟩ := hminorF.exists_le_linear_add_pow
    (fun x => x.1.word.length) 3 (fun x => by simp [challengeSize])
  refine ⟨d, hcheck.mono c (fun x => ?_) (fun x => ?_)⟩ <;>
    refine le_trans ?_ (hb x) <;>
    have hlen := length_encChallenge x <;>
    have hp := Nat.pow_le_pow_left
      (show (encPair encData encBool (data x,
        x.1.word.getD (address (data x)) false)).length + 1 ≤
          2 * challengeSize x + 3 by
        simp only [length_encPair, encBool_apply, List.length_singleton,
          challengeSize, data]; omega) dF <;>
    dsimp only [Function.comp_apply] at * <;> omega

/-- Prepare the challenge flags while copying the global word only linearly. -/
theorem exists_flags_inO : ∃ d, ComputableInO (fun a : Input => (a, flags a.context))
    encInput (encPair encInput encBits)
    (fun a => a.word.length + shortSize a ^ d)
    (fun a => a.word.length + shortSize a ^ d) := by
  obtain ⟨dF, eF, hF⟩ := flags_polyTime.exists_degree
  have hid : ComputableInDegree (fun a : Input => a) encInput encInput 1 1 := .id'
  have h := hid.inO_one.prod (hF.inO.comp encInput_context_deg.inO_one)
  have hs : PolyBounded shortSize (fun a : Input => 4 * shortSize a + shortSize a ^ dF + 2) :=
    (((PolyBounded.const 4).mul PolyBounded.self).add (PolyBounded.self.pow dF)).add (.const 2)
  obtain ⟨c, d, hb⟩ := hs.exists_le_linear_add_pow (fun a => a.word.length) 2
    (fun a => by simp [shortSize])
  refine ⟨d, h.mono c (fun a => ?_) (fun a => ?_)⟩ <;>
    refine le_trans ?_ (hb a) <;>
    have hp := Nat.pow_le_pow_left
      (show (encContext a.context).length + 1 ≤ shortSize a by
        simp only [shortSize]; omega) dF <;>
    simp only [encInput_apply, encInputFields, length_encPair, encBits_apply,
      Function.comp_apply, shortSize] at * <;> omega

end Turing.MultiTapeTM.PortAssignment
