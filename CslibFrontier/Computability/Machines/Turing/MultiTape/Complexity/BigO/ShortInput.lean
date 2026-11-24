/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.BinarySlice
public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import Mathlib.Data.Nat.Size

/-!
# Computing from a short component while retaining a long input

A linear projection extracts a short header, and a polynomial-time computation reads only that
header. Pairing the result with the original input charges the long component linearly and the
short component polynomially. This is the preparation bound used by native quantified programs.

A terminal may instead compute an index and a summary from the header, read one framed list
element at that binary index, and combine it with the summary in linear time. The selected
element can be arbitrarily long: it retains a linear charge, and only the encoded list length's
binary size enters the polynomial charge.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

/-- Retain the complete input and compute from its short header, with separate long-word and
short-data charges. Framing and the linear header projection are included. -/
theorem exists_pair_short {α β γ : Type} {enc : α ↪ List Bool} {encHeader : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {header : α → β} {f : β → γ} {long short : α → ℕ}
    (hheader : ComputableInDegree header enc encHeader 1 1)
    (hf : ComputableInPolyTime f encHeader encOut) (K : ℕ)
    (hshort : ∀ a, 1 ≤ short a)
    (hinput : ∀ a, (enc a).length ≤ long a + K * short a + K)
    (hsize : ∀ a, (encHeader (header a)).length ≤ short a) :
    ∃ d, ComputableInO (fun a => (a, f (header a))) enc (encPair enc encOut)
      (fun a => long a + short a ^ d) (fun a => long a + short a ^ d) := by
  obtain ⟨d, e, hd⟩ := hf.exists_degree
  have hid : ComputableInDegree (fun a : α => a) enc enc 1 1 := .id'
  have h := hid.inO_one.prod (hd.inO.comp hheader.inO_one)
  let minor (a : α) := 2 * (K * short a + K) + (short a + 1) ^ d
  have hm : PolyBounded short minor := by
    dsimp only [minor]
    exact ((PolyBounded.const 2).mul
      (((PolyBounded.const K).mul PolyBounded.self).add (.const K))).add
        ((PolyBounded.self.add (.const 1)).pow d)
  obtain ⟨c, D, hb⟩ := hm.exists_le_linear_add_pow long 2 hshort
  refine ⟨D, h.mono c (fun a => ?_) (fun a => ?_)⟩ <;>
    refine le_trans ?_ (hb a) <;>
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right (hsize a) 1) d <;>
    have hi := hinput a <;>
    dsimp only [Function.comp_apply, minor] at * <;> omega

/-- Compute an index and summary from short data, perform one sharp list lookup, and finish
linearly. The input framing, header length and binary encoded-list length are bounded explicitly;
the selected element never enters a polynomial-time subcomputation. -/
theorem exists_listGetD_short {α β γ δ ε : Type} {enc : α ↪ List Bool}
    {encHeader : β ↪ List Bool} {encElem : γ ↪ List Bool} {encSummary : δ ↪ List Bool}
    {encOut : ε ↪ List Bool} {header : α → β} {word : α → List γ} {index : β → ℕ}
    {summary : β → δ} {finish : δ × γ → ε} {short : α → ℕ} (fallback : γ)
    (hheader : ComputableInDegree header enc encHeader 1 1)
    (hword : ComputableInDegree word enc (encList encElem) 1 1)
    (hindex : ComputableInPolyTime index encHeader encNat)
    (hsummary : ComputableInPolyTime summary encHeader encSummary)
    (hfinish : ComputableInDegree finish (encPair encSummary encElem) encOut 1 1) (K : ℕ)
    (hshort : ∀ a, 1 ≤ short a)
    (hinput : ∀ a, (enc a).length ≤
      K * (encList encElem (word a)).length + K * short a + K)
    (hsize : ∀ a, (encHeader (header a)).length ≤ short a)
    (hwordSize : ∀ a, (encList encElem (word a)).length.size ≤ short a) :
    ∃ d, ComputableInO
      (fun a => finish (summary (header a), (word a).getD (index (header a)) fallback))
      enc encOut
      (fun a => (encList encElem (word a)).length + short a ^ d)
      (fun a => (encList encElem (word a)).length + short a ^ d) := by
  let : Inhabited γ := ⟨fallback⟩
  obtain ⟨dS, eS, hS⟩ := hsummary.exists_degree
  obtain ⟨dI, eI, hI⟩ := hindex.exists_degree
  obtain ⟨dB, hB⟩ := exists_listGetElem?_binary encElem
  have hi := hI.inO.comp hheader.inO_one
  have hread := (hB.comp (hword.inO_one.prod hi)).optionGetD fallback
  have h := hfinish.inO_one.comp_linear ((hS.inO.comp hheader.inO_one).prod hread)
  have hh : PolyBounded short (fun a => (encHeader (header a)).length) :=
    PolyBounded.self.mono hsize
  have hiSize : PolyBounded short (fun a => (index (header a)).size) := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len, Function.comp_apply] using
      hindex.polyBounded_length.comp (g := header) hh
  have hw : PolyBounded short (fun a => (encList encElem (word a)).length.size) :=
    PolyBounded.self.mono hwordSize
  let minor (a : α) := 3 * (K * short a + K) +
    (short a + 1) ^ dS + (short a + 1) ^ dI +
      ((encList encElem (word a)).length.size + (index (header a)).size + 1) ^ dB
  have hm : PolyBounded short minor := by
    dsimp only [minor]
    exact ((((PolyBounded.const 3).mul
      (((PolyBounded.const K).mul PolyBounded.self).add (.const K))).add
        ((PolyBounded.self.add (.const 1)).pow dS)).add
          ((PolyBounded.self.add (.const 1)).pow dI)).add
            (((hw.add hiSize).add (.const 1)).pow dB)
  obtain ⟨c, d, hb⟩ := hm.exists_le_linear_add_pow
    (fun a => (encList encElem (word a)).length) (3 * K + 1) hshort
  refine ⟨d, (h.of_enc_eq fun a => ?_).mono c (fun a => ?_) (fun a => ?_)⟩
  · simp only [Function.comp_apply, List.getD_eq_getElem?_getD]
  all_goals
    refine le_trans ?_ (hb a)
    have hpS := Nat.pow_le_pow_left (Nat.add_le_add_right (hsize a) 1) dS
    have hpI := Nat.pow_le_pow_left (Nat.add_le_add_right (hsize a) 1) dI
    have hin := hinput a
    dsimp only [Function.comp_apply, minor] at *
    simp only [Nat.add_mul, Nat.mul_assoc, one_mul] at *
    omega

end Turing.MultiTapeTM.ComputableInO
