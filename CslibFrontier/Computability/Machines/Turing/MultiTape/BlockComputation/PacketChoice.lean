/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.CoeffWordSum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.BinarySlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.ShortInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# The packet row-choice validity factor

The binary assignment specifies one fixed-width field per row, most significant field first.
Zero selects the local term; a positive field selects the preceding dense mode number. Every
branch checks all row ranges and target predicates, then one universally challenged mode's
multiplicity. The dense exponent list is read once at a binary index, with missing entries zero.

`plays_check` identifies this game with `CoeffWordSum.Valid`. Its deterministic terminal scans
the encoded exponent list only linearly. The row count and target-coordinate index are unary;
mode count, mode block size, assignment and exponents are binary. Counts and row guards are
computed from the short context before a linear binary comparison with the selected exponent.
An oversized exponent therefore does not enter a polynomial running-time bound.

This is original infrastructure for the packet coefficient circuit. Native arithmetic row
terminals remain separate circuit-compiler work tracked in #4741.
-/

public section

namespace Turing.MultiTapeTM.PacketChoice

open Cslib Cslib.BitString Cslib.Circuits.Frontier.TensorNetwork Finset
open ComputableInPolyTime MultiTapeATM QuantifiedWord

/-- Binary mode data and assignment, with unary row and coordinate counts. -/
structure Context where
  /-- Number of dense mode labels, in binary. -/
  modes : ℕ
  /-- Number of row fields, in unary. -/
  rows : ℕ
  /-- Target-symbol coordinate, in unary. -/
  i : ℕ
  /-- Modes per tile, in binary; division follows the total natural-number convention at zero. -/
  nb : ℕ
  /-- Whether the first symbol is the target group. -/
  e₁ : Bool
  /-- Whether the second symbol is the target group. -/
  e₂ : Bool
  /-- The unsigned assignment with most-significant-first row fields, in binary. -/
  assignment : ℕ
  deriving DecidableEq

/-- Fields in declaration order, framing all except the final binary assignment. -/
enc_structure encContext : Context where
  modes : encNat, rows : encUnary, i : encUnary, nb : encNat,
  e₁ : encBool, e₂ : encBool, assignment : encNat

/-- A packet row-choice request with dense exponents separate from short metadata. -/
structure Input where
  /-- Row-choice context, fixed before the universal challenge. -/
  context : Context
  /-- Binary dense exponent entries; missing entries mean zero. -/
  exponents : List ℕ
  deriving DecidableEq

/-- Framed short context followed by the framed list of binary exponents. -/
enc_structure encInput : Input where context : encContext, exponents : (encList encNat)

/-- Framed short context followed by the raw challenge bits. -/
abbrev encData : Context × List Bool ↪ List Bool := encPair encContext encBits

/-- Framed complete input followed by the raw challenge bits. -/
abbrev encChallenge : Input × List Bool ↪ List Bool := encPair encInput encBits

/-- The mathematical target set. The native checker tests membership without constructing it. -/
@[expose] def targets (c : Context) : Finset (Fin c.modes) :=
  Finset.univ.filter fun k => modeTargets c.i c.e₁ c.e₂ (k.val / c.nb)

/-- One universal binary mode index. Even zero modes retain a terminal on the empty flag word. -/
@[expose] def flags (c : Context) : List Bool := List.replicate c.modes.size true

/-- Short input size includes only the binary length of the encoded exponent list. -/
@[expose] def shortSize (a : Input) : ℕ :=
  (encContext a.context).length + (encList encNat a.exponents).length.size + 1

/-- Short terminal size includes the challenge word and binary encoded-list length. -/
@[expose] def challengeSize (x : Input × List Bool) : ℕ :=
  (encData (x.1.context, x.2)).length + (encList encNat x.1.exponents).length.size + 1

private def field (c : Context) (j : ℕ) : ℕ :=
  binaryField c.rows c.modes.size c.assignment j

private def rowGuard (c : Context) : Bool :=
  (List.range c.rows).all fun j => decide (field c j ≤ c.modes) &&
    (decide (field c j = 0) || modeTargets c.i c.e₁ c.e₂ ((field c j - 1) / c.nb))

private def count (c : Context) (k : ℕ) : ℕ :=
  (List.range c.rows).countP fun j => decide (field c j = k + 1)

/-- Every terminal checks all row guards. It also checks the challenged target mode's count;
padded and nontarget challenges accept only after the row guards succeed. -/
def check (x : Input × List Bool) : Bool :=
  let c := x.1.context
  let k := ofBits x.2
  rowGuard c && if k < c.modes ∧ modeTargets c.i c.e₁ c.e₂ (k / c.nb) then
    decide (count c k = x.1.exponents.getD k 0)
  else true

private theorem rowGuard_iff (c : Context) :
    rowGuard c = true ↔
      (∀ j : Fin c.rows, binaryField c.rows c.modes.size c.assignment j ≤ c.modes) ∧
      (∀ (j : Fin c.rows) (k : Fin c.modes),
        fieldChoice c.modes (binaryField c.rows c.modes.size c.assignment j) = some k →
          k ∈ targets c) := by
  simp only [rowGuard, List.all_eq_true, List.mem_range, Bool.and_eq_true_iff,
    decide_eq_true_eq, Bool.or_eq_true_iff]
  constructor
  · intro h
    refine ⟨fun j => (h j j.isLt).1, ?_⟩
    intro j k hk
    have heq := (fieldChoice_eq_some k).mp hk
    have hz := (h j j.isLt).2
    have hk0 : field c j ≠ 0 := by simp only [field, heq]; omega
    have ht : modeTargets c.i c.e₁ c.e₂ (k.val / c.nb) = true := by
      rcases hz with hz | hz
      · exact False.elim (hk0 hz)
      · simpa only [field, heq, Nat.add_sub_cancel] using hz
    simpa only [targets, Finset.mem_filter, Finset.mem_univ, true_and] using ht
  · rintro ⟨hrange, htarget⟩ j hj
    refine ⟨hrange ⟨j, hj⟩, ?_⟩
    by_cases hz : field c j = 0
    · exact Or.inl hz
    · have hk : field c j - 1 < c.modes := by
        have := hrange ⟨j, hj⟩
        change field c j ≤ c.modes at this
        omega
      have ht := htarget ⟨j, hj⟩ ⟨field c j - 1, hk⟩
        ((fieldChoice_eq_some _).mpr (by change field c j = (field c j - 1) + 1; omega))
      exact Or.inr (by simpa [targets] using ht)

private theorem count_eq (c : Context) (k : Fin c.modes) :
    count c k = #{j : Fin c.rows |
      fieldChoice c.modes (binaryField c.rows c.modes.size c.assignment j) = some k} := by
  rw [count, List.countP_range_eq_card_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, field, fieldChoice_eq_some]
  exact decide_eq_true_iff

/-- Universal binary mode challenges verify precisely the validity factor of the padded
coefficient sum. Row guards still run with no modes, and zero rows still check target exponents. -/
theorem plays_check (a : Input) :
    plays (fun xs => check (a, xs) = true) [] (flags a.context) ↔
      CoeffWordSum.Valid a.context.modes a.context.rows a.context.modes.size
        (targets a.context) (fun k => a.exponents.getD k 0) a.context.assignment := by
  have hfields : plays (fun xs => check (a, xs) = true) [] (flags a.context) ↔
      ∀ k : Fin (2 ^ a.context.modes.size),
        (rowGuard a.context &&
          if k.val < a.context.modes ∧
              modeTargets a.context.i a.context.e₁ a.context.e₂ (k.val / a.context.nb) then
            decide (count a.context k.val = a.exponents.getD k.val 0)
          else true) = true := by
    rw [show flags a.context = List.replicate a.context.modes.size true ++ [] by
      simp [flags], plays_forall_field]
    apply forall_congr'
    intro k
    simp only [plays, List.nil_append, check, ofBits_lowBits k.isLt]
  rw [hfields]
  constructor
  · intro h
    have hg := (Bool.and_eq_true_iff.mp (h 0)).1
    refine ⟨(rowGuard_iff _).mp hg |>.1, (rowGuard_iff _).mp hg |>.2, ?_⟩
    intro k hk
    have ht : modeTargets a.context.i a.context.e₁ a.context.e₂ (k.val / a.context.nb) = true := by
      simpa [targets] using hk
    have hc := (Bool.and_eq_true_iff.mp (h ⟨k, k.isLt.trans (Nat.lt_size_self _)⟩)).2
    simpa only [k.isLt, ht, and_self, ↓reduceIte, decide_eq_true_eq, count_eq] using hc
  · rintro ⟨hrange, htarget, hcount⟩ k
    have hg := (rowGuard_iff _).mpr ⟨hrange, htarget⟩
    simp only [hg, Bool.true_and]
    split_ifs with hk
    · have hmem : (⟨k, hk.1⟩ : Fin a.context.modes) ∈ targets a.context := by
        simpa [targets] using hk.2
      simp only [decide_eq_true_eq]
      exact (count_eq a.context ⟨k, hk.1⟩).trans (hcount ⟨k, hk.1⟩ hmem)
    · rfl

private def data (x : Input × List Bool) : Context × List Bool := (x.1.context, x.2)

private theorem data_deg : ComputableInDegree data encChallenge encData 1 1 :=
  ((encInput_context_deg.comp (ComputableInDegree.fst encInput encBits)).prod
    (ComputableInDegree.snd encInput encBits)).mono

private theorem target_polyTime {α : Type} {enc : α ↪ List Bool} {c : α → Context}
    {k : α → ℕ} (hc : ComputableInPolyTime c enc encContext)
    (hk : ComputableInPolyTime k enc encNat) :
    ComputableInPolyTime (fun a => modeTargets (c a).i (c a).e₁ (c a).e₂ (k a / (c a).nb))
      enc encBool :=
  ite (binary_testBit (binary_div' hk (encContext_nb_polyTime hc)) (encContext_i_polyTime hc))
    (encContext_e₂_polyTime hc) (encContext_e₁_polyTime hc)

private theorem field_polyTime {α : Type} {enc : α ↪ List Bool} {c : α → Context}
    {j : α → ℕ} (hc : ComputableInPolyTime c enc encContext)
    (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (fun a => field (c a) (j a)) enc encNat := by
  have hw := binary_size.comp (encContext_modes_polyTime hc)
  have hr := unary_to_binary.comp (encContext_rows_polyTime hc)
  have hs := binary_mul' (unary_to_binary.comp hw) (binary_sub' (binary_sub' hr (const 1)) hj)
  have h := binary_mod' (binary_shiftRight' (encContext_assignment_polyTime hc) hs)
    (binary_two_pow.comp hw)
  simpa only [field, binaryField, Nat.shiftRight_eq_div_pow, pow_mul, Function.comp_apply] using h

private theorem rowGuard_polyTime : ComputableInPolyTime rowGuard encContext encBool := by
  have hc := fst encContext encUnary
  have hj := unary_to_binary.comp (snd encContext encUnary)
  have hf := field_polyTime hc hj
  exact allWith (bool_and' (binary_le' hf (encContext_modes_polyTime hc))
    (bool_or' (decide_eq' hf (const 0)) (target_polyTime hc (binary_sub' hf (const 1)))))
      id' (range.comp encContext_rows_deg.computableInPolyTime)

private theorem count_polyTime :
    ComputableInPolyTime (fun x : Context × ℕ => count x.1 x.2)
      (encPair encContext encNat) encNat := by
  have hc := (fst encContext encNat).comp (fst (encPair encContext encNat) encUnary)
  have hk := (snd encContext encNat).comp (fst (encPair encContext encNat) encUnary)
  have hj := unary_to_binary.comp (snd (encPair encContext encNat) encUnary)
  exact unary_to_binary.comp (countPWithInput
    (range.comp (encContext_rows_polyTime (fst encContext encNat)))
    (decide_eq' (field_polyTime hc hj) (binary_add' hk (const 1))))

/-- All universal flags are computed from the binary mode count in the short context. -/
theorem flags_polyTime : ComputableInPolyTime flags encContext encBits :=
  (bitsReplicate true).comp (binary_size.comp encContext_modes_deg.computableInPolyTime)

private structure Summary where
  /-- Whether every row field passes its guards. -/
  rowsValid : Bool
  /-- Whether the challenge is a target mode in range. -/
  active : Bool
  /-- Number of occurrences of the challenged mode. -/
  count : ℕ

private enc_structure encSummary : Summary where
  rowsValid : encBool, active : encBool, count : encNat

private def summary (x : Context × List Bool) : Summary :=
  ⟨rowGuard x.1, decide (ofBits x.2 < x.1.modes) &&
    modeTargets x.1.i x.1.e₁ x.1.e₂ (ofBits x.2 / x.1.nb), count x.1 (ofBits x.2)⟩

private theorem summary_polyTime : ComputableInPolyTime summary encData encSummary := by
  have hc := fst encContext encBits
  have hk := bitsToNat.comp (snd encContext encBits)
  exact encSummary_mk_polyTime (rowGuard_polyTime.comp hc)
    (bool_and' (binary_lt' hk (encContext_modes_polyTime hc)) (target_polyTime hc hk))
    (count_polyTime.comp (hc.prod hk))

private def finish (x : Summary × ℕ) : Bool :=
  x.1.rowsValid && (!x.1.active || decide (x.1.count = x.2))

private theorem finish_deg :
    ComputableInDegree finish (encPair encSummary encNat) encBool 1 1 := by
  have hs := ComputableInDegree.fst encSummary encNat
  have hc := (encSummary_count_deg.comp hs).prod (ComputableInDegree.snd encSummary encNat)
  have he := ComputableInDegree.natEq.comp hc
  have hd := (encSummary_rowsValid_deg.comp hs).prod ((encSummary_active_deg.comp hs).prod he)
  exact ((ComputableInDegree.of_finite
    (encIn := encPair encBool (encPair encBool encBool)) (encMid := encBool)
      fun q : Bool × Bool × Bool => q.1 && (!q.2.1 || q.2.2)).comp hd).mono

/-- Framing charges the long exponent encoding twice and the short data by a fixed factor. -/
theorem length_encChallenge (x : Input × List Bool) :
    (encChallenge x).length ≤ 2 * (encList encNat x.1.exponents).length +
      2 * challengeSize x + 1 := by
  simp only [encChallenge, encInput_apply, encInputFields, length_encPair,
    encBits_apply, challengeSize, encData]
  omega

/-- One sharp list lookup and linear binary equality keep the dense exponent encoding linear
in the terminal's native time and space bounds, even when the selected exponent is very long. -/
theorem exists_check_inO : ∃ d, ComputableInO check encChallenge encBool
    (fun x => (encList encNat x.1.exponents).length + challengeSize x ^ d)
    (fun x => (encList encNat x.1.exponents).length + challengeSize x ^ d) := by
  have hword : ComputableInDegree (fun x : Input × List Bool => x.1.exponents)
      encChallenge (encList encNat) 1 1 :=
    (encInput_exponents_deg.comp (ComputableInDegree.fst encInput encBits)).mono
  obtain ⟨d, h⟩ := ComputableInO.exists_listGetD_short (short := challengeSize) 0
    data_deg hword (bitsToNat.comp (snd encContext encBits)) summary_polyTime finish_deg 2
    (fun x => by simp [challengeSize])
    (fun x => by have := length_encChallenge x; omega)
    (fun x => by simp only [challengeSize, data]; omega)
    (fun x => by simp only [challengeSize]; omega)
  refine ⟨d, h.of_enc_eq fun x => ?_⟩
  by_cases hk : ofBits x.2 < x.1.context.modes <;>
    cases ht : modeTargets x.1.context.i x.1.context.e₁ x.1.context.e₂
      (ofBits x.2 / x.1.context.nb) <;>
    simp [finish, summary, data, check, hk, ht]

/-- Prepare the universal mode flags while copying the dense exponent encoding only linearly. -/
theorem exists_flags_inO : ∃ d, ComputableInO (fun a : Input => (a, flags a.context))
    encInput (encPair encInput encBits)
    (fun a => (encList encNat a.exponents).length + shortSize a ^ d)
    (fun a => (encList encNat a.exponents).length + shortSize a ^ d) := by
  apply ComputableInO.exists_pair_short encInput_context_deg flags_polyTime 2
  · intro a
    simp [shortSize]
  · intro a
    simp only [encInput_apply, encInputFields, length_encPair, shortSize]
    omega
  · intro a
    simp only [shortSize]
    omega

end Turing.MultiTapeTM.PacketChoice
