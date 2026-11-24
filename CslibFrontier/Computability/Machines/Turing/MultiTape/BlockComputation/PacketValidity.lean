/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.PacketChoice
public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Append
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ScalarInput
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.PacketWordSum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.ShortInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Signed bit queries for the packet validity factor

The validity factor is zero or one. Its only possible nonzero bit is coefficient zero,
bit zero, at positive precision. A true claim universally checks the row-choice predicate;
a false claim existentially chooses a failed check. The same program handles empty mode sets,
padding, zero precision and out-of-range bit coordinates.

The dense exponent word is charged linearly. The short header and the binary length of the
exponent word are the only arguments of the remaining polynomial. This supplies the signed
validity input of the packet circuit; arithmetic row and source inputs remain tracked in #4741.
-/

public section

namespace Turing.MultiTapeTM.PacketValidity

open Cslib Cslib.Circuits.Frontier TensorNetwork MultiTapeATM QuantifiedWord
open ComputableInPolyTime

/-- Short row-choice data and binary precision/bit coordinates, followed by the proposed bit. -/
structure Header where
  /-- Metadata of the row-choice validity predicate. -/
  context : PacketChoice.Context
  /-- Binary creation precision. -/
  precision : ℕ
  /-- Binary coefficient index. -/
  coefficient : ℕ
  /-- Binary precision-bit index. -/
  bit : ℕ
  /-- Proposed value of this coefficient bit. -/
  claim : Bool
  deriving DecidableEq

/-- The row context is framed, then the three binary indices are framed, then the claim bit. -/
enc_structure encHeader : Header where
  context : PacketChoice.encContext, precision : encNat, coefficient : encNat,
  bit : encNat, claim : encBool

/-- A signed validity query with its dense binary exponent list in a separate long component. -/
structure Input where
  /-- Short metadata and the selected bit claim. -/
  header : Header
  /-- Dense binary exponents, with missing entries interpreted as zero. -/
  exponents : List ℕ
  deriving DecidableEq

/-- Framed short header followed by the list of binary exponent entries. -/
enc_structure encInput : Input where header : encHeader, exponents : (encList encNat)

/-- Framed signed input followed by the raw binary mode challenge. -/
abbrev encChallenge : Input × List Bool ↪ List Bool := encPair encInput encBits

/-- The existing row-choice request, retaining the exponent list and assignment exactly. -/
@[expose] def choice (a : Input) : PacketChoice.Input := ⟨a.header.context, a.exponents⟩

/-- Short header and row-choice size; only the binary length of the exponent word is counted. -/
@[expose] def shortSize (a : Input) : ℕ :=
  (encHeader a.header).length + PacketChoice.shortSize (choice a) + 1

/-- Short metadata including the completed binary challenge. -/
@[expose] def challengeSize (x : Input × List Bool) : ℕ := shortSize x.1 + x.2.length + 1

/-- The sole coefficient-bit position at which a zero-or-one factor can be nonzero. -/
@[expose] def active (h : Header) : Bool :=
  decide (0 < h.precision ∧ h.coefficient = 0 ∧ h.bit = 0)

/-- Universal challenges for a true claim, existential challenges for a false claim. -/
@[expose] def flags (h : Header) : List Bool := List.replicate h.context.modes.size h.claim

/-- The terminal compares the selected validity-factor bit with the recorded claim. -/
@[expose] def check (x : Input × List Bool) : Bool :=
  decide ((active x.1.header && PacketChoice.check (choice x.1, x.2)) = x.1.header.claim)

open Classical in
/-- The selected bit of the zero-or-one validity factor, including precision zero. -/
@[expose] noncomputable def value (a : Input) : Bool :=
  active a.header && decide (CoeffWordSum.Valid
    a.header.context.modes a.header.context.rows a.header.context.modes.size
    (PacketChoice.targets a.header.context) (fun k => a.exponents.getD k 0)
    a.header.context.assignment)

/-- Both claim values have their correct quantifier polarity, even with zero-width challenges. -/
theorem plays_check (a : Input) :
    plays (fun xs => check (a, xs) = true) [] (flags a.header) ↔ value a = a.header.claim := by
  classical
  cases ha : active a.header with
  | false =>
    simpa only [check, ha, Bool.false_and, decide_eq_true_eq, value] using
      plays_constant (false = a.header.claim) [] (flags a.header)
  | true =>
    have hc := PacketChoice.plays_check (choice a)
    cases hclaim : a.header.claim with
    | true =>
      simpa only [check, ha, hclaim, Bool.true_and, decide_eq_true_eq, flags,
        PacketChoice.flags, value, choice] using hc
    | false =>
      have hn := (plays_not (fun xs => PacketChoice.check (choice a, xs) = true)
        [] (PacketChoice.flags a.header.context)).trans (not_congr hc)
      simpa only [check, ha, hclaim, Bool.true_and, decide_eq_true_eq, flags,
        PacketChoice.flags, List.map_replicate, Bool.not_true,
        Bool.eq_false_iff, ne_eq, value, choice, decide_eq_false_iff_not] using hn

private theorem choice_deg :
    ComputableInDegree choice encInput PacketChoice.encInput 1 1 := by
  exact (PacketChoice.encInput_mk_deg.comp
    ((encHeader_context_deg.comp encInput_header_deg).prod encInput_exponents_deg)).mono

private theorem data_deg : ComputableInDegree
    (fun x : Input × List Bool => (choice x.1, x.2)) encChallenge PacketChoice.encChallenge 1 1 :=
  ((choice_deg.comp (ComputableInDegree.fst encInput encBits)).prod
    (ComputableInDegree.snd encInput encBits)).mono

/-- Both challenge polarities are computed from the short binary header. -/
theorem flags_polyTime : ComputableInPolyTime flags encHeader encBits := by
  have hw := binary_size.comp (encHeader_context_polyTime ComputableInPolyTime.id' |>
    PacketChoice.encContext_modes_polyTime)
  have h := (encHeader_claim_polyTime ComputableInPolyTime.id').ite
    ((bitsReplicate true).comp hw) ((bitsReplicate false).comp hw)
  refine h.of_enc_eq fun x => ?_
  cases hc : x.claim <;> simp [flags, Function.comp_apply, hc]

private theorem summary_polyTime : ComputableInPolyTime
    (fun h : Header => (active h, h.claim)) encHeader (encPair encBool encBool) := by
  have h : ComputableInPolyTime (fun h : Header => h) encHeader encHeader := .id'
  exact (bool_and'
    (binary_lt' (const 0) (encHeader_precision_polyTime h))
    (bool_and' (decide_eq' (encHeader_coefficient_polyTime h) (const 0))
      (decide_eq' (encHeader_bit_polyTime h) (const 0)))).prod (encHeader_claim_polyTime h)

/-- The signed check preserves the sharp linear charge for the encoded exponent list. -/
theorem exists_check_inO : ∃ d, ComputableInO check encChallenge encBool
    (fun x => (encList encNat x.1.exponents).length + challengeSize x ^ d)
    (fun x => (encList encNat x.1.exponents).length + challengeSize x ^ d) := by
  obtain ⟨dC, hC⟩ := PacketChoice.exists_check_inO
  obtain ⟨dH, eH, hH⟩ := summary_polyTime.exists_degree
  have hh : ComputableInDegree (fun x : Input × List Bool => x.1.header)
      encChallenge encHeader 1 1 :=
    (encInput_header_deg.comp (ComputableInDegree.fst encInput encBits)).mono
  have hf : ComputableInDegree
      (fun x : (Bool × Bool) × Bool => decide ((x.1.1 && x.2) = x.1.2))
      (encPair (encPair encBool encBool) encBool) encBool 1 1 :=
    (ComputableInDegree.of_finite _).mono
  have h := hf.inO_one.comp_linear ((hH.inO.comp hh.inO_one).prod (hC.comp data_deg.inO_one))
  let minor (x : Input × List Bool) := 8 * challengeSize x + 6 +
    (challengeSize x + 1) ^ dH + (2 * challengeSize x + 1) ^ dC
  have hm : PolyBounded challengeSize minor := by
    dsimp only [minor]
    exact (((((PolyBounded.const 8).mul PolyBounded.self).add (.const 6)).add
      ((PolyBounded.self.add (.const 1)).pow dH)).add
        ((((PolyBounded.const 2).mul PolyBounded.self).add (.const 1)).pow dC))
  obtain ⟨c, d, hb⟩ := hm.exists_le_linear_add_pow
    (fun x => (encList encNat x.1.exponents).length) 5
    (fun x => by simp [challengeSize, shortSize])
  refine ⟨d, (h.of_enc_eq fun _ => rfl).mono c (fun x => ?_) (fun x => ?_)⟩
  all_goals
    refine le_trans ?_ (hb x)
    have hhead : (encHeader x.1.header).length + 1 ≤ challengeSize x + 1 := by
      simp only [challengeSize, shortSize]; omega
    have hold : PacketChoice.challengeSize (choice x.1, x.2) ≤ 2 * challengeSize x + 1 := by
      simp only [PacketChoice.challengeSize, PacketChoice.encData, length_encPair,
        encBits_apply, challengeSize, shortSize, PacketChoice.shortSize, choice]
      omega
    have hpH := Nat.pow_le_pow_left hhead dH
    have hpC := Nat.pow_le_pow_left hold dC
    simp only [Function.comp_apply, minor, encChallenge, encInput_apply, encInputFields,
      length_encPair, encBits_apply, choice] at *
    dsimp only [challengeSize, shortSize] at *
    omega

/-- Prepare signed flags while copying the exponent word only a constant number of times. -/
theorem exists_flags_inO : ∃ d, ComputableInO (fun a : Input => (a, flags a.header))
    encInput (encPair encInput encBits)
    (fun a => (encList encNat a.exponents).length + shortSize a ^ d)
    (fun a => (encList encNat a.exponents).length + shortSize a ^ d) := by
  apply ComputableInO.exists_pair_short encInput_header_deg flags_polyTime 2
  · intro a
    simp [shortSize]
  · intro a
    simp only [encInput_apply, encInputFields, length_encPair, shortSize]
    omega
  · intro a
    simp only [shortSize]
    omega

/-- The signed query denotes the actual representative bit of the coefficient circuit's
validity factor. The other row factors and the modulus scale do not affect this input. -/
theorem value_eq_factor_bit (m : ℕ) (a : Input)
    (term : Fin a.header.context.rows → Option (Fin a.header.context.modes) →
      GaloisRingArith.Ring a.header.precision (FastContraction.modulus m)) :
    value a = ((FastContraction.representative m a.header.precision
      (CoeffWordSum.factor a.header.context.modes a.header.context.rows
        a.header.context.modes.size (PacketChoice.targets a.header.context) term
        (fun k => a.exponents.getD k 0) a.header.context.assignment
        a.header.context.rows)).coeff a.header.coefficient).val.testBit a.header.bit := by
  classical
  simp only [CoeffWordSum.factor, lt_self_iff_false, ↓reduceDIte]
  split_ifs with hv
  · simp only [value, hv, decide_true, Bool.and_true]
    have h := FastContraction.ScalarInput.representative_shiftedInt_bit m a.header.precision
      0 a.header.coefficient a.header.bit 1
    have hb : (1 : ℤ).testBit a.header.bit = decide (a.header.bit = 0) := by
      apply Bool.eq_iff_iff.mpr
      simp [Int.testBit, Nat.testBit_one_eq_true_iff_self_eq_zero]
    simp only [Int.cast_one, pow_zero, mul_one, Nat.sub_zero, Nat.zero_le, and_true] at h
    rw [h]
    apply Bool.eq_iff_iff.mpr
    simp only [active, Bool.and_eq_true, decide_eq_true_eq, hb]
    omega
  · simp only [value, hv, decide_false, Bool.and_false]
    have h := FastContraction.ScalarInput.representative_shiftedInt_bit m a.header.precision
      0 a.header.coefficient a.header.bit 0
    simpa [Int.testBit] using h.symm

/-- The compact signed validity request for the existing packet sum-of-products circuit.
Only row count and target coordinate are unary; precision and numeric indices are binary. -/
@[expose] def Input.ofPacket (c : NativePacket.PacketCtx) (rows : List (ℕ × Bool)) (β : List ℕ)
    (assignment coefficient bit : ℕ) (claim : Bool) : Input :=
  ⟨⟨⟨c.tiles * c.nb, rows.length, c.i, c.nb, c.e₁, c.e₂, assignment⟩,
    c.p, coefficient, bit, claim⟩, β⟩

/-- The compact request names exactly the validity input of the actual native packet circuit,
at its creation precision and with default-zero coefficient and bit positions. -/
theorem value_ofPacket (m : ℕ) (c : NativePacket.PacketCtx) (hfl : c.fl = FastContraction.modulus m)
    (rows : List (ℕ × Bool)) (β : List ℕ) (assignment coefficient bit : ℕ) (claim : Bool) :
    value (Input.ofPacket c rows β assignment coefficient bit claim) =
      ((FastContraction.representative m c.p
        (hfl ▸ NativePacket.PacketWordSum.factor c rows β assignment rows.length :
          GaloisRingArith.Ring c.p (FastContraction.modulus m))).coeff coefficient).val.testBit
            bit := by
  classical
  rcases c with ⟨p, fl, a, L, i, tiles, t, nb, e₁, e₂, differ, cols, ζ⟩
  change fl = FastContraction.modulus m at hfl
  subst fl
  let c : NativePacket.PacketCtx := ⟨p, FastContraction.modulus m, a, L, i, tiles, t, nb,
    e₁, e₂, differ, cols, ζ⟩
  have h := value_eq_factor_bit m (Input.ofPacket c rows β assignment coefficient bit claim)
    (fun _ _ => 0)
  have ht : PacketChoice.targets
      (Input.ofPacket c rows β assignment coefficient bit claim).header.context =
        NativePacket.PacketWordSum.targets c := by
    unfold PacketChoice.targets NativePacket.PacketWordSum.targets
    rfl
  rw [ht] at h
  simp only [NativePacket.PacketWordSum.factor, Nat.lt_add_one, ↓reduceIte,
    Input.ofPacket, CoeffWordSum.factor, lt_self_iff_false, ↓reduceDIte, c] at h ⊢
  exact h

end Turing.MultiTapeTM.PacketValidity
