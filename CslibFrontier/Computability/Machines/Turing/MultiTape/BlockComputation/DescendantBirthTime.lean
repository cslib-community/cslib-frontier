/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantBirth
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.BinarySlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists

/-!
# Native access to compressed packet birth data

The stored exponent word is charged linearly. The packet's binary offset and slice length are
computed from the short creation parameters, and `ComputableInO.exists_listSlice_binary` returns
only the corresponding slice. Creation precision remains binary throughout this operation.

These are original native multitape machine certificates for the access functions. They do not
evaluate a packet entry or expand a unary packet context; those are separate steps of #4728.
-/

public section

namespace Turing.MultiTapeTM.DescendantBirth

open Cslib Circuits.Frontier NativeChild
open DescendantVertex (Origin encOrigin)

/-- The short data used to select a packet: its stored parameter word, binary packet number
and binary encoded exponent-word length. -/
@[expose] def selectSize (q : Call × ℕ) : ℕ :=
  (encParameters q.1.parameters).length + q.2.size +
    (encList encNat q.1.exponents).length.size + 1

private def sliceIndices (q : Parameters × ℕ) : ℕ × ℕ :=
  let count := 2 ^ (q.1.coordinate + 1) * q.1.precision
  (q.2 * count, count)

private theorem sliceIndices_polyTime : ComputableInPolyTime sliceIndices
    (encPair encParameters encNat) (encPair encNat encNat) := by
  have hp := ComputableInPolyTime.fst encParameters encNat
  have hq := ComputableInPolyTime.snd encParameters encNat
  have hi := encParameters_coordinate_polyTime hp
  have hc := ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.binary_two_pow.comp (ComputableInPolyTime.unary_succ.comp hi))
    (encParameters_precision_polyTime hp)
  exact (ComputableInPolyTime.binary_mul' hq hc).prod hc

/-- A packet's exact exponent slice and unchanged creation parameters are computed with
linear dependence on the entire exponent word and polynomial dependence on `selectSize`. -/
theorem exists_select_inO : ∃ d, ComputableInO (fun q : Call × ℕ => select q.1 q.2)
    (encPair encCall encNat) encBirth
    (fun q => (encList encNat q.1.exponents).length + selectSize q ^ d)
    (fun q => (encList encNat q.1.exponents).length + selectSize q ^ d) := by
  let data (q : Call × ℕ) := (q.1.parameters, q.2)
  have hcall := ComputableInDegree.fst encCall encNat
  have hp := encCall_parameters_deg.comp hcall
  have hq := ComputableInDegree.snd encCall encNat
  have hb := encCall_exponents_deg.comp hcall
  have hdata : ComputableInDegree data (encPair encCall encNat)
      (encPair encParameters encNat) 1 1 := hp.prod hq
  obtain ⟨T, S, hT, hS, hi⟩ := sliceIndices_polyTime.exists_computableInO
  have hi' := hi.comp hdata.inO_one
  obtain ⟨ds, hs⟩ := ComputableInO.exists_listSlice_binary encNat
  have hslice := hs.comp (hb.inO_one.prod hi')
  have hresult := encBirth_mk_inO hp.inO_one hq.inO_one hslice
  have hdataSize : PolyBounded selectSize
      (fun q => (encPair encParameters encNat (data q)).length) :=
    PolyBounded.of_forall_le 2 1 fun q => by
      simp only [data, length_encPair, encNat_apply, Nat.size_eq_bits_len, selectSize, pow_one]
      omega
  have hindices : PolyBounded selectSize
      (fun q => (encPair encNat encNat (sliceIndices (data q))).length) :=
    sliceIndices_polyTime.polyBounded_length.comp hdataSize
  let small (q : Call × ℕ) := (encList encNat q.1.exponents).length.size +
    (sliceIndices (data q)).1.size + (sliceIndices (data q)).2.size + 1
  have hsmall : PolyBounded selectSize small :=
    ((PolyBounded.self.add hindices).add (PolyBounded.const 1)).mono fun q => by
      simp only [small, selectSize, length_encPair, encNat_apply, Nat.size_eq_bits_len]
      omega
  let minor (q : Call × ℕ) := 20 * selectSize q + T (data q) + S (data q) + small q ^ ds
  have hm : PolyBounded selectSize minor :=
    ((((PolyBounded.const 20).mul PolyBounded.self).add (hT.comp hdataSize)).add
      (hS.comp hdataSize)).add (hsmall.pow ds)
  obtain ⟨c, d, hd⟩ := hm.exists_le_linear_add_pow
    (fun q => (encList encNat q.1.exponents).length) 9 (fun q => by simp [selectSize])
  have hinput (q : Call × ℕ) : (encPair encCall encNat q).length ≤
      2 * (encList encNat q.1.exponents).length + 5 * selectSize q := by
    simp only [length_encPair, encCall_apply, encCallFields, encNat_apply,
      Nat.size_eq_bits_len, selectSize]
    omega
  refine ⟨d, (hresult.of_enc_eq (fun _ => rfl)).mono c (fun q => ?_) (fun q => ?_)⟩ <;>
    refine le_trans ?_ (hd q) <;>
    have hl := hinput q <;>
    dsimp only [Function.comp_apply, minor, small, data] at * <;> omega

/-- The short size of birth lookup: the selected call's parameter word, binary origin and
binary complete log length. A missing call uses the fixed default parameters. -/
@[expose] def lookupSize (q : List Call × Origin) : ℕ :=
  (encParameters ((q.1[q.2.stage - 1]?).getD default).parameters).length +
    q.2.stage.size + q.2.index.size + (encList encCall q.1).length.size + 1

/-- The complete chronological call log is charged linearly. Every other charge is polynomial
in the selected short header and binary indices, even for invalid birth stages or packet numbers.
The result is the actual `lookup` function, not an assumed access continuation. -/
theorem exists_lookup_inO : ∃ d, ComputableInO (fun q : List Call × Origin => lookup q.1 q.2)
    (encPair (encList encCall) encOrigin) (encOption encBirth)
    (fun q => (encList encCall q.1).length + lookupSize q ^ d)
    (fun q => (encList encCall q.1).length + lookupSize q ^ d) := by
  let chosen (q : List Call × Origin) := (q.1[q.2.stage - 1]?).getD default
  let data (q : List Call × Origin) := (chosen q, q.2.index)
  have hl := ComputableInDegree.fst (encList encCall) encOrigin
  have ho := ComputableInDegree.snd (encList encCall) encOrigin
  have hstage := DescendantVertex.encOrigin_stage_deg.comp ho
  have hindex := ComputableInDegree.natPred.comp hstage
  have hpacket := DescendantVertex.encOrigin_index_deg.comp ho
  obtain ⟨dg, hg⟩ := ComputableInO.exists_listGetElem?_binary encCall
  have hget := hg.comp (hl.prod hindex).inO_one
  have hchosen := hget.optionGetD (default : Call)
  obtain ⟨ds, hs⟩ := exists_select_inO
  have hselect := hs.comp (hchosen.prod hpacket.inO_one)
  have hsome := (ComputableInDegree.optionSome (enc₁ := encBirth)
    (enc := encOption encBirth)).inO_one.comp_linear hselect
  have hactive := ComputableInO.and'
    (ComputableInO.not' (ComputableInO.natIsZero.comp_linear hstage.inO_one)) hget.optionIsSome
  have hresult := hactive.ite hsome (ComputableInO.const (none : Option Birth))
  have heq (q : List Call × Origin) :
      lookup q.1 q.2 =
        if !(decide (q.2.stage = 0)) && (q.1[q.2.stage - 1]?).isSome then
          some (select (chosen q) q.2.index) else none := by
    by_cases hz : q.2.stage = 0
    · simp [lookup, hz]
    · cases hc : q.1[q.2.stage - 1]? <;> simp [lookup, hz, chosen, hc]
  have hbeta (q : List Call × Origin) :
      (encList encNat (chosen q).exponents).length ≤ (encList encCall q.1).length := by
    cases hc : q.1[q.2.stage - 1]? with
    | none =>
      simp only [chosen, hc, Option.getD_none]
      exact Nat.zero_le _
    | some call =>
      have hm : call ∈ q.1 := List.mem_of_getElem? hc
      have hf := encCall_exponents_length_le call
      have hl := SizedListEncoding.length_elem_le (encA := encCall)
        (encL := encList encCall) q.1 call hm
      simpa only [chosen, hc, Option.getD_some] using hf.trans hl
  have hsmall (q : List Call × Origin) : selectSize (data q) ≤ lookupSize q := by
    have hn := Nat.size_le_size (hbeta q)
    dsimp only [selectSize, lookupSize, data, chosen] at *
    omega
  have hstageSize (q : List Call × Origin) :
      (encList encCall q.1).length.size + (q.2.stage - 1).size + 1 ≤ lookupSize q := by
    have hi := Nat.size_le_size (Nat.sub_le q.2.stage 1)
    dsimp only [lookupSize]
    omega
  let minor (q : List Call × Origin) :=
    8 * lookupSize q + 2 * lookupSize q ^ dg + lookupSize q ^ ds
  have hm : PolyBounded lookupSize minor :=
    (((PolyBounded.const 8).mul PolyBounded.self).add
      ((PolyBounded.const 2).mul (PolyBounded.self.pow dg))).add (PolyBounded.self.pow ds)
  obtain ⟨c, d, hd⟩ := hm.exists_le_linear_add_pow (fun q => (encList encCall q.1).length)
    11 (fun q => by simp [lookupSize])
  have hinput (q : List Call × Origin) :
      (encPair (encList encCall) encOrigin q).length ≤
        2 * (encList encCall q.1).length + 2 * lookupSize q := by
    simp only [length_encPair, DescendantVertex.encOrigin_apply,
      DescendantVertex.encOriginFields, encNat_apply, Nat.size_eq_bits_len, lookupSize]
    omega
  refine ⟨d, (hresult.of_enc_eq (fun q => congrArg (encOption encBirth) (heq q))).mono c
    (fun q => ?_) (fun q => ?_)⟩ <;>
    refine le_trans ?_ (hd q) <;>
    have hb := hbeta q <;>
    have hl := hinput q <;>
    have hp := Nat.pow_le_pow_left (hsmall q) ds <;>
    have hg := Nat.pow_le_pow_left (hstageSize q) dg <;>
    dsimp only [Function.comp_apply, chosen, data, minor] at * <;>
    split_ifs <;> omega

end Turing.MultiTapeTM.DescendantBirth
