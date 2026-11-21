/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortFinish
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPredecessorQuery
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime

/-!
# A native port query on the represented root graph

The candidate edge is looked up directly in the copied and subdivided graph. Its endpoint pair
and the shared seed determine whether its row or column occupies the requested alphabet-64 group.
The deterministic machine makes a constant number of passes over the raw schedule. The subsequent
radix arithmetic uses the short port, seed and returned vertex numbers.
-/

public section

namespace Turing.MultiTapeTM.RootPortQuery

open Cslib

/-- The group and side to test, paired with the shared graph and seed context. -/
abbrev Input := RootPortFinish.Port × RootPredecessorQuery.Input

/-- The port is framed before the existing root query record. -/
abbrev encInput := encPair RootPortFinish.encPort RootPredecessorQuery.encInput

/-- The port, binary schedule length and short graph metadata. -/
@[expose] def shortSize (a : Input) :=
  (RootPortFinish.encPort a.1).length + RootPredecessorQuery.shortSize a.2 + 1

private def candidate (a : Input) := RootPredecessorQuery.request a.2 a.2.context.candidate

/-- Install the result of the candidate's physical endpoint scan. -/
@[expose] def finishInput (k : ℕ) (a : Input) : RootPortFinish.Input :=
  ⟨a.1, a.2.context, RootEndpointQuery.query k (RootPredecessorQuery.request a.2
      a.2.context.candidate)⟩

/-- Test the requested port on this graph, prefix and candidate. -/
@[expose] def query (k : ℕ) (a : Input) : Bool := RootPortFinish.run (finishInput k a)

private theorem candidate_size (a : Input) : RootEndpointInput.shortSize (candidate a) ≤
    shortSize a :=
  (RootPredecessorQuery.candidate_shortSize_le a.2).trans (by unfold shortSize; omega)

private theorem finish_size (k : ℕ) : PolyBounded shortSize
    (fun a => (RootPortFinish.encInput (finishInput k a)).length) := by
  have hp : PolyBounded shortSize (fun a => (RootPortFinish.encPort a.1).length) :=
    PolyBounded.self.mono fun a => by unfold shortSize; omega
  have hc : PolyBounded shortSize (fun a => (SeededPredecessor.encContext a.2.context).length) :=
    PolyBounded.self.mono fun a => by unfold shortSize RootPredecessorQuery.shortSize; omega
  have he := (RootEndpointAlgorithm.length_output_polyBounded k).comp (g := candidate)
    (PolyBounded.self.mono candidate_size)
  apply ((((PolyBounded.const 2).mul hp).add ((PolyBounded.const 2).mul hc)).add
    (he.add (PolyBounded.const 2))).mono
  intro a
  simp only [RootPortFinish.encInput_apply, RootPortFinish.encInputFields, length_encPair,
    finishInput, candidate, RootEndpointFinish.encOutput, SeededPredecessorFinish.encEnds]
  omega

/-- A fixed finite deterministic machine decides the candidate port within linear raw length
plus polynomial short arithmetic, in both time and charged workspace. -/
theorem exists_computableInO (k : ℕ) : ∃ d, ComputableInO (query k) encInput encBool
    (fun a => a.2.raw.length + shortSize a ^ d) (fun a => a.2.raw.length + shortSize a ^ d) := by
  obtain ⟨d₀, hroot⟩ := RootEndpointAlgorithm.exists_computableInO k
  have hright := ComputableInDegree.snd RootPortFinish.encPort RootPredecessorQuery.encInput
  have hp := (ComputableInDegree.fst RootPortFinish.encPort RootPredecessorQuery.encInput).inO_one
  have hc := (RootPredecessorQuery.encInput_context_deg.comp hright).inO_one
  have hr := (RootPredecessorQuery.candidate_deg.comp hright).inO_one
  have hprepare := (hp.prod (hc.prod (hroot.comp hr))).of_enc_eq (g := finishInput k)
    (encC := RootPortFinish.encInput) (fun _ => rfl)
  obtain ⟨t, s, ht, hs, hm⟩ := RootPortFinish.computableInPolyTime_run.exists_computableInO
  let cost (a : Input) := 6 * (shortSize a + 2) + shortSize a ^ d₀ +
    t (finishInput k a) + s (finishInput k a)
  have hcost : PolyBounded shortSize cost :=
    ((((PolyBounded.const 6).mul (PolyBounded.self.add (PolyBounded.const 2))).add
      (PolyBounded.self.pow d₀)).add (ht.comp (finish_size k))).add (hs.comp (finish_size k))
  obtain ⟨c, d, hd⟩ := hcost.exists_le_linear_add_pow (fun a => a.2.raw.length) 7
    (fun a => by simp [shortSize])
  have he (a : Input) : (encInput a).length ≤ 2 * a.2.raw.length + 2 * shortSize a + 4 := by
    rw [encInput, length_encPair, RootPredecessorQuery.length_encInput]
    unfold shortSize RootPredecessorQuery.shortSize
    omega
  refine ⟨d, (hm.comp hprepare).mono c (fun a => ?_) (fun a => ?_)⟩ <;>
    refine le_trans ?_ (hd a) <;>
    have hx := Nat.pow_le_pow_left (candidate_size a) d₀ <;>
    have hlen := he a <;>
    dsimp only [cost, Function.comp_apply, Prod.snd, candidate] at * <;>
    have hraw : (RootPredecessorQuery.request a.2 a.2.context.candidate).raw = a.2.raw := rfl <;>
    rw [hraw] <;> unfold encInput at hlen <;> omega

end Turing.MultiTapeTM.RootPortQuery
