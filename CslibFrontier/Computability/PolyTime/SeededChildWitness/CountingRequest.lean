/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededChildWitness.Dispatch
public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.CountingInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Count parameters of a routed child witness

A selected count-bit branch installs the exact binary summation limit: the clamped vertex
prefix, the selected port bound, or every parent edge for a packing rank. It preserves the
bit index and Boolean claim from the shared proposal and uses the common field width.
-/

public section
namespace Cslib.SeededChildWitness.Dispatch

open Turing.MultiTapeTM ComputableInPolyTime Circuits.Boolean.CarryLookahead.Query

/-- Exact number of leaves in the selected count. -/
@[expose] def termCount (b : Public) : Count → ℕ
  | .inl n => min n b.vertices
  | .inr (.inl (_, n)) => n
  | .inr (.inr _) => b.edges

/-- Install the ordinary external counting parameters for a decoded count-bit query. -/
@[expose] def params (b : Public) (r : BitQuery) : CountingInput.Input :=
  let (request, bit, claim) := r
  ⟨termCount b request, ⟨width b, bit, claim⟩⟩

/-- A genuine routed bit always lies within the common precision, on arbitrary choice words. -/
theorem params_valid {b : Public} {xs : List Bool} {r : BitQuery}
    (h : (run (b, xs)).2 = .inr (some r)) : (params b r).query.bit < (params b r).query.width := by
  unfold run at h
  dsimp only at h
  unfold branch at h
  split_ifs at h with _ _ hj <;> cases h
  exact hj

private abbrev encPort := encPair encBool encNat
private abbrev encPack := encPair encNat (encPair encNat encNat)

/-- Selecting a count limit works in binary, including when a padded prefix is larger
than the vertex universe. -/
theorem computableInPolyTime_termCount {α : Type} {enc : α ↪ List Bool} {b : α → Public}
    {code : α → Count} (hb : ComputableInPolyTime b enc encPublic)
    (hc : ComputableInPolyTime code enc encCount) :
    ComputableInPolyTime (fun x => termCount (b x) (code x)) enc encNat := by
  let encSum' := encSum encPort encPack
  have left := ((ComputableInO.getLeft?_deg encNat encSum').computableInPolyTime.comp hc)
  have right := ((ComputableInO.getRight?_deg encNat encSum').computableInPolyTime.comp hc)
  have vert := optionGetDWithInput left (const 0)
  have rhs := optionGetDWithInput right (const (encOut := encSum') (Sum.inl (false, 0)))
  have port := optionGetDWithInput
    ((ComputableInO.getLeft?_deg encPort encPack).computableInPolyTime.comp rhs)
    (const (encOut := encPort) (false, 0))
  have hu := encPublic_vertices_polyTime hb
  have hn := encPublic_edges_polyTime hb
  have hlim := ite_decide (binary_lt' vert hu) vert hu
  have hout := ite ((ComputableInO.isLeft_deg encNat encSum').computableInPolyTime.comp hc) hlim
    (ite ((ComputableInO.isLeft_deg encPort encPack).computableInPolyTime.comp rhs) port.snd' hn)
  exact hout.of_enc_eq fun x => by
    cases h : code x with
    | inl n => simp [h, termCount, min_def]; split_ifs <;> congr 1 <;> omega
    | inr z => cases z <;> simp [h, termCount]

/-- A single machine produces the encoded native count request from the decoded branch. -/
theorem computableInPolyTime_params : ComputableInPolyTime (Function.uncurry params)
    (encPair encPublic encBitQuery) CountingInput.encInput := by
  have hb := fst encPublic encBitQuery
  have hr := snd encPublic encBitQuery
  exact CountingInput.encInput_mk_polyTime (computableInPolyTime_termCount hb hr.fst')
    (Initial.encInput_mk_polyTime (unary_to_binary.comp (computableInPolyTime_width.comp hb))
      hr.snd'.fst' hr.snd'.snd')

end Cslib.SeededChildWitness.Dispatch
