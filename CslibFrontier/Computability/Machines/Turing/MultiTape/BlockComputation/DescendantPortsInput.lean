/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantPorts
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DescendantEndpointTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Native requests for a compressed ordered-port check

The raw root schedule is separate from the ancestry and proposed ports. Preparing choices or
routing a completed word copies the schedule linearly and computes only on the short context.
A local verdict returns immediately; the other branch prepares the existing descendant endpoint
controller. No descendant edge list is part of the encoded request.
-/

public section

namespace Turing.MultiTapeTM.DescendantPorts

open ComputableInPolyTime MultiTapeATM SeededChildCounts

/-- Short data shared by every challenge to a proposed port list. -/
structure Context where
  /-- Boolean copies of each original block edge, in binary. -/
  copies : ℕ
  /-- Actual split seed headers, newest first. -/
  frames : List DescendantEndpoint.Frame
  /-- Exact graph sizes, the vertex, and its proposed increasing ports. -/
  query : Query

/-- Binary copy count, framed seed list, then the encoded port query. -/
enc_structure encContext : Context where
  copies : encNat, frames : (encList DescendantEndpoint.encFrame), query : encQuery

/-- A compressed port request with the root schedule kept as a raw word. -/
structure Input where
  /-- Marked raw movement schedule of the root block network. -/
  raw : List Bool
  /-- Short ancestry and proposed port list. -/
  context : Context

/-- A framed raw schedule followed by its short context. -/
enc_structure encInput : Input where raw : encBits, context : encContext

/-- Framed short context followed by the completed challenge bits. -/
abbrev encData : Context × List Bool ↪ List Bool := encPair encContext encBits

/-- Framed compressed input followed by the completed challenge bits. -/
abbrev encChallenge : Input × List Bool ↪ List Bool := encPair encInput encBits

/-- The short initial data includes the binary schedule length, never the schedule itself. -/
@[expose] def shortSize (a : Input) : ℕ :=
  (encContext a.context).length + a.raw.length.size + 1

/-- Discard the protected schedule before performing the polynomial terminal computation. -/
@[expose] def data (x : Input × List Bool) : Context × List Bool := (x.1.context, x.2)

/-- Short terminal size; the completed choice word has length fixed by the input graph sizes. -/
@[expose] def challengeSize (x : Input × List Bool) : ℕ :=
  (encData (data x)).length + x.1.raw.length.size + 1

/-- The port game emits either a local verdict or one genuine endpoint request. -/
@[expose] def outcome (x : Context × List Bool) : Joined.Instruction :=
  program (x.1.query, x.2)

/-- Prepare the existing compressed endpoint state; a local verdict uses a harmless default. -/
@[expose] def endpoint (x : Context × List Bool) : DescendantEndpoint.Position :=
  let (edge, answer) := (outcome x).getRight?.getD (0, (0, 0))
  DescendantEndpoint.root x.1.copies x.1.frames edge answer

/-- Continue precisely on the endpoint branch of the port program. -/
@[expose] def active (x : Context × List Bool) : Bool := (outcome x).getRight?.isSome

/-- A closed branch returns the port program's verdict. -/
@[expose] def answer (x : Context × List Bool) : Bool := (outcome x).getLeft?.getD false

/-- Guarded dispatch retains the same complete input for the selected endpoint continuation. -/
@[expose] def instruction (x : Input × List Bool) : List Bool :=
  [active (data x), false, answer (data x)] ++ encChallenge x

private theorem data_deg : ComputableInDegree data encChallenge encData 1 1 :=
  ((encInput_context_deg.comp (ComputableInDegree.fst encInput encBits)).prod
    (ComputableInDegree.snd encInput encBits)).mono

private theorem outcome_polyTime : ComputableInPolyTime outcome encData Joined.encInstruction :=
  program_polyTime.comp ((encContext_query_polyTime (fst encContext encBits)).prod
    (snd encContext encBits))

/-- Initialize a descendant query entirely from short runtime metadata. -/
theorem endpoint_polyTime :
    ComputableInPolyTime endpoint encData DescendantEndpoint.encPosition := by
  let encEnds := encPair encNat (encPair encNat encNat)
  have ho := (ComputableInO.getRight?_deg encBool encEnds).computableInPolyTime.comp
    outcome_polyTime
  have he := (ComputableInDegree.getD (enc₁ := encEnds) (enc := encOption encEnds)
    (0, (0, 0))).computableInPolyTime.comp ho
  have hc := fst encContext encBits
  exact DescendantEndpoint.root_polyTime (encContext_copies_polyTime hc)
    (encContext_frames_polyTime hc) he.fst' he.snd'.fst' he.snd'.snd'

private theorem header_polyTime : ComputableInPolyTime
    (fun x : Context × List Bool => [active x, false, answer x]) encData encBits := by
  let encEnds := encPair encNat (encPair encNat encNat)
  have hr := (ComputableInO.getRight?_deg encBool encEnds).computableInPolyTime.comp
    outcome_polyTime
  have hl := (ComputableInO.getLeft?_deg encBool encEnds).computableInPolyTime.comp
    outcome_polyTime
  have ha : ComputableInPolyTime active encData encBool :=
    (ComputableInDegree.isSome encEnds).computableInPolyTime.comp hr
  have hb := (ComputableInDegree.getD (enc₁ := encBool) (enc := encOption encBool)
    false).computableInPolyTime.comp hl
  exact (of_finite (encIn := encPair encBool encBool) (encOut := encBits)
    (fun p : Bool × Bool => [p.1, false, p.2])).comp (ha.prod hb)

/-- Framing a completed request preserves linear dependence on the root schedule. -/
theorem length_encChallenge (x : Input × List Bool) :
    (encChallenge x).length ≤ 4 * x.1.raw.length + 2 * challengeSize x + 3 := by
  simp only [encChallenge, encInput_apply, encInputFields, length_encPair,
    encBits_apply, challengeSize, encData, data]
  omega

private theorem short_computation {β : Type} {encB : β ↪ List Bool}
    {f : Context × List Bool → β} (hf : ComputableInPolyTime f encData encB) :
    ∃ d, ComputableInO (fun x => f (data x)) encChallenge encB
      (fun x => x.1.raw.length + challengeSize x ^ d)
      (fun x => x.1.raw.length + challengeSize x ^ d) := by
  obtain ⟨d, e, hd⟩ := hf.exists_degree
  have h := hd.inO.comp data_deg.inO_one
  have hs : PolyBounded challengeSize (fun x : Input × List Bool =>
      2 * challengeSize x + 3 + challengeSize x ^ d) := by growth_poly
  obtain ⟨c, D, hc⟩ := hs.exists_le_linear_add_pow (fun x => x.1.raw.length) 4
    (fun x => by simp [challengeSize])
  refine ⟨D, h.mono c (fun x => ?_) (fun x => ?_)⟩ <;>
    refine le_trans ?_ (hc x) <;>
    have hlen := length_encChallenge x <;>
    have hp := Nat.pow_le_pow_left (show (encData (data x)).length + 1 ≤ challengeSize x by
      simp only [challengeSize]; omega) d <;>
    omega

/-- Native endpoint preparation charges the schedule linearly and the short data polynomially. -/
theorem exists_endpoint_inO : ∃ d, ComputableInO (fun x => endpoint (data x))
    encChallenge DescendantEndpoint.encPosition
    (fun x => x.1.raw.length + challengeSize x ^ d)
    (fun x => x.1.raw.length + challengeSize x ^ d) :=
  short_computation endpoint_polyTime

/-- The guarded instruction is computed with the same separation of long and short data. -/
theorem exists_instruction_inO : ∃ d, ComputableInO instruction encChallenge encBits
    (fun x => x.1.raw.length + challengeSize x ^ d)
    (fun x => x.1.raw.length + challengeSize x ^ d) := by
  obtain ⟨d, hd⟩ := short_computation header_polyTime
  have hid : ComputableInDegree (fun x : Input × List Bool => x)
      encChallenge encChallenge 1 1 := .id'
  have h := hd.append hid.inO_one (g := instruction) (encOut := encBits) (fun _ => rfl)
  have hs : PolyBounded challengeSize (fun x : Input × List Bool =>
      challengeSize x ^ d + 2 * challengeSize x + 3) := by growth_poly
  obtain ⟨c, D, hc⟩ := hs.exists_le_linear_add_pow (fun x => x.1.raw.length) 5
    (fun x => by simp [challengeSize])
  refine ⟨D, h.mono c (fun x => ?_) (fun x => ?_)⟩ <;>
    refine le_trans ?_ (hc x) <;> have hlen := length_encChallenge x <;> omega

/-- Prepare the complete flag pattern before any universal challenge or endpoint guess. -/
theorem exists_flags_inO : ∃ d, ComputableInO (fun a : Input => (a, flags a.context.query))
    encInput (encPair encInput encBits)
    (fun a => a.raw.length + shortSize a ^ d)
    (fun a => a.raw.length + shortSize a ^ d) := by
  have hf := flags_polyTime.comp encContext_query_deg.computableInPolyTime
  obtain ⟨d, e, hd⟩ := hf.exists_degree
  have hid : ComputableInDegree (fun a : Input => a) encInput encInput 1 1 := .id'
  have h := hid.inO_one.prod (hd.inO.comp encInput_context_deg.inO_one)
  have hs : PolyBounded shortSize (fun a : Input => 2 * shortSize a + shortSize a ^ d) := by
    growth_poly
  obtain ⟨c, D, hc⟩ := hs.exists_le_linear_add_pow (fun a => a.raw.length) 4
    (fun a => by simp [shortSize])
  refine ⟨D, h.mono c (fun a => ?_) (fun a => ?_)⟩ <;>
    refine le_trans ?_ (hc a) <;>
    have hp := Nat.pow_le_pow_left (show (encContext a.context).length + 1 ≤ shortSize a by
      simp only [shortSize]; omega) d <;>
    simp only [encInput_apply, encInputFields, length_encPair, encBits_apply,
      Function.comp_apply, shortSize] at * <;> omega

end Turing.MultiTapeTM.DescendantPorts
