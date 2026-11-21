/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointAlgorithm
public import CslibFrontier.Computability.PolyTime.SeededPredecessorFinish
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import Mathlib.Data.Nat.Size

/-!
# Seeded root-edge predecessors from a raw schedule

Both root-edge lookups run on the supplied movement table. Their short endpoint pairs and
the shared seed feed the predecessor comparison. The raw input contributes an additive
linear cost even though computing the two labels involves polynomial-time arithmetic.
-/

public section

namespace Turing.MultiTapeTM.RootPredecessorQuery

open Cslib

/-- The shared raw schedule, number of Boolean copies, seed and both root edge indices. -/
structure Input where
  /-- Encoded rows of movements of the input and work heads. -/
  raw : List Bool
  /-- Number of Boolean copies of each edge before subdivision. -/
  copies : ℕ
  /-- Seed data and the two numbered half-edges being compared. -/
  context : SeededPredecessor.Context

/-- The raw schedule and binary copy count each occupy one frame. -/
enc_structure encInput : Input where
  raw : encBits, copies : encNat, context : SeededPredecessor.encContext

/-- Size charged to arithmetic after both schedule lookups. -/
@[expose] def shortSize (a : Input) : ℕ :=
  a.raw.length.size + a.copies.size + (SeededPredecessor.encContext a.context).length + 1

/-- Input to one lookup in the shared root graph. -/
@[expose] def request (a : Input) (edge : ℕ) : RootEndpointQuery.Input :=
  ⟨a.raw, a.copies, edge⟩

/-- Short comparison input obtained from the two actual lookups. -/
@[expose] def finishInput (k : ℕ) (a : Input) : SeededPredecessorFinish.Input :=
  ⟨a.context, RootEndpointQuery.query k (request a a.context.edge),
    RootEndpointQuery.query k (request a a.context.candidate)⟩

/-- Decide whether the candidate precedes the requested edge in its seeded pair-label class. -/
@[expose] def query (k : ℕ) (a : Input) : Bool :=
  SeededPredecessorFinish.run (finishInput k a)

/-- The physical input size includes both frames. -/
theorem length_encInput (a : Input) :
    (encInput a).length = 2 * a.raw.length + 2 * a.copies.size +
      (SeededPredecessor.encContext a.context).length + 2 := by
  simp [encInput_apply, encInputFields, encPair_apply, encNat_apply, Nat.size_eq_bits_len]
  omega

private theorem index_sizes (a : Input) :
    a.context.edge.size ≤ (SeededPredecessor.encContext a.context).length ∧
    a.context.candidate.size ≤ (SeededPredecessor.encContext a.context).length := by
  simp [SeededPredecessor.encContext_apply, SeededPredecessor.encContextFields,
    encPair_apply, encNat_apply, Nat.size_eq_bits_len]
  omega

private theorem request_size (a : Input) (j : ℕ)
    (hj : j.size ≤ (SeededPredecessor.encContext a.context).length) :
    RootEndpointInput.shortSize (request a j) ≤ shortSize a := by
  change a.raw.length.size + a.copies.size + j.size + 1 ≤
    a.raw.length.size + a.copies.size + (SeededPredecessor.encContext a.context).length + 1
  omega

/-- Looking up the candidate only uses binary indices from the shared record. -/
theorem candidate_shortSize_le (a : Input) :
    RootEndpointInput.shortSize (request a a.context.candidate) ≤ shortSize a :=
  request_size a _ (index_sizes a).2

private theorem edge_deg : ComputableInDegree (fun a : Input => request a a.context.edge)
    encInput RootEndpointInput.encInput 1 1 := by
  exact RootEndpointInput.encInput_mk_deg.comp
    (encInput_raw_deg.prod (encInput_copies_deg.prod
      (SeededPredecessor.encContext_edge_deg.comp encInput_context_deg)))

/-- Reading the candidate endpoint request is linear in the shared external record. -/
theorem candidate_deg : ComputableInDegree (fun a : Input => request a a.context.candidate)
    encInput RootEndpointInput.encInput 1 1 := by
  exact RootEndpointInput.encInput_mk_deg.comp
    (encInput_raw_deg.prod (encInput_copies_deg.prod
      (SeededPredecessor.encContext_candidate_deg.comp encInput_context_deg)))

private theorem finish_size (k : ℕ) :
    PolyBounded shortSize
      (fun a => (SeededPredecessorFinish.encInput (finishInput k a)).length) := by
  have hctx : PolyBounded shortSize (fun a => (SeededPredecessor.encContext a.context).length) :=
    PolyBounded.self.mono fun a => by unfold shortSize; omega
  have he := (RootEndpointAlgorithm.length_output_polyBounded k).comp
    (g := fun a : Input => request a a.context.edge)
    (PolyBounded.self.mono fun a => request_size a _ (index_sizes a).1)
  have hf := (RootEndpointAlgorithm.length_output_polyBounded k).comp
    (g := fun a : Input => request a a.context.candidate)
    (PolyBounded.self.mono candidate_shortSize_le)
  apply ((((PolyBounded.const 2).mul hctx).add (((PolyBounded.const 2).mul he).add hf)).add
    (PolyBounded.const 2)).mono
  intro a
  simp [SeededPredecessorFinish.encInput_apply, SeededPredecessorFinish.encInputFields,
    finishInput, encPair_apply, SeededPredecessorFinish.encEnds, RootEndpointFinish.encOutput]
  omega

/-- A single finite native machine tests the two actual root endpoints with one shared seed.
Its time and charged work space are linear in the raw schedule plus a polynomial in the short
arithmetic input. The exponent and machine are uniform in both runtime edge indices. -/
theorem exists_computableInO (k : ℕ) : ∃ d, ComputableInO (query k) encInput encBool
    (fun a => a.raw.length + shortSize a ^ d) (fun a => a.raw.length + shortSize a ^ d) := by
  obtain ⟨d₀, hroot⟩ := RootEndpointAlgorithm.exists_computableInO k
  have hboth := encInput_context_deg.inO_one.prod
    ((hroot.comp edge_deg.inO_one).prod (hroot.comp candidate_deg.inO_one))
  have hfinish := hboth.of_enc_eq (g := finishInput k)
    (encC := SeededPredecessorFinish.encInput) (fun _ => rfl)
  obtain ⟨t, s, ht, hs, hm⟩ := SeededPredecessorFinish.computableInPolyTime_run.exists_computableInO
  have h := hm.comp hfinish
  let cost (a : Input) := 6 * shortSize a + 2 * shortSize a ^ d₀ + t (finishInput k a) +
    s (finishInput k a)
  have hcost : PolyBounded shortSize cost :=
    ((((PolyBounded.const 6).mul PolyBounded.self).add
      ((PolyBounded.const 2).mul (PolyBounded.self.pow d₀))).add
      (ht.comp (finish_size k))).add (hs.comp (finish_size k))
  obtain ⟨c, d, hd⟩ := hcost.exists_le_linear_add_pow (fun a => a.raw.length) 8
    (fun a => by simp [shortSize])
  refine ⟨d, h.mono c (fun a => ?_) (fun a => ?_)⟩ <;>
    refine le_trans ?_ (hd a) <;>
    have he := Nat.pow_le_pow_left (request_size a _ (index_sizes a).1) d₀ <;>
    have hf := Nat.pow_le_pow_left (request_size a _ (index_sizes a).2) d₀ <;>
    simp only [Function.comp_apply, length_encInput, request, cost] at * <;>
    unfold shortSize at * <;> omega

end Turing.MultiTapeTM.RootPredecessorQuery
