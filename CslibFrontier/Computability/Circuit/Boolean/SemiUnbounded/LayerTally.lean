/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Double-counting transcripts for a circuit layer

A transcript chooses at most one valid proof tree per gate of a layer. The expected tally
counts true gates and sums their minimum proof-tree weights. Matching the count forces all
true gates to be represented, and matching the sum then forces every selected tree to be
minimum. If the layer is min-isolated, exactly one transcript passes.

This is the transcript argument for PromiseWeightEval in Algorithm 2 of van Melkebeek and
Prakriya [VanMelkebeekPrakriya2019], March 20, 2017 preprint, Appendix A.
The stack implementation and its resource bounds are tracked in #7920.

## Main result

* `existsUnique_layerTranscript_of_min_isolation`: the exact tally forces a unique transcript.
-/

public section

open Finset

namespace Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit

variable {G : Type*} {C : LayeredSemiUnboundedCircuit G} {k : ℕ}

/-- For each gate of layer `k`, either skip it or supply a valid proof tree. -/
abbrev LayerTranscript (C : LayeredSemiUnboundedCircuit G) (k : ℕ) :=
  (g : {g // C.layer g = k}) → Option (ProofTree C g.val)

/-- Gates represented in a transcript. -/
noncomputable def LayerTranscript.selected [Fintype G] (t : LayerTranscript C k) :
    Finset {g // C.layer g = k} := by
  classical
  exact univ.filter fun g => (t g).isSome

/-- Weight contributed by a selected tree, with zero for a skipped gate. -/
def LayerTranscript.weightAt (t : LayerTranscript C k) (w : G → ℕ)
    (g : {g // C.layer g = k}) : ℕ :=
  ((t g).map (ProofTree.weight w)).getD 0

/-- A transcript matching the tally of minimum trees is uniquely determined when the layer
is min-isolated. -/
private theorem LayerTranscript.eq_of_matching_tally [Fintype G] {w : G → ℕ}
    {canonical candidate : LayerTranscript C k}
    (hmin : ∀ g, C.Eval g.val →
      ∃ p, canonical g = some p ∧ IsMinOn (ProofTree.weight w) Set.univ p)
    (hisolated : ∀ g : {g // C.layer g = k}, C.Eval g.val →
      ∃! p : ProofTree C g.val, IsMinOn (ProofTree.weight w) Set.univ p)
    (hcount : candidate.selected.card = canonical.selected.card)
    (hsum : ∑ g ∈ candidate.selected, candidate.weightAt w g =
      ∑ g ∈ canonical.selected, canonical.weightAt w g) :
    candidate = canonical := by
  classical
  have mem_selected (t : LayerTranscript C k) (g : {g // C.layer g = k}) :
      g ∈ t.selected ↔ ∃ p, t g = some p := by
    cases h : t g <;> simp [LayerTranscript.selected, h]
  have hsubset : candidate.selected ⊆ canonical.selected := by
    intro g hg
    obtain ⟨p, _⟩ := (mem_selected candidate g).mp hg
    obtain ⟨q, hq, _⟩ := hmin g ((C.eval_iff_nonempty_proofTree _).mpr ⟨p⟩)
    exact (mem_selected canonical g).mpr ⟨q, hq⟩
  have hsame := Finset.eq_of_subset_of_card_le hsubset hcount.ge
  have hle (g : {g // C.layer g = k}) (hg : g ∈ candidate.selected) :
      canonical.weightAt w g ≤ candidate.weightAt w g := by
    obtain ⟨p, hp⟩ := (mem_selected candidate g).mp hg
    obtain ⟨q, hq, hqmin⟩ := hmin g ((C.eval_iff_nonempty_proofTree _).mpr ⟨p⟩)
    simpa only [LayerTranscript.weightAt, hp, hq, Option.map_some, Option.getD_some] using
      isMinOn_univ_iff.mp hqmin p
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp (hsame ▸ hsum.symm)
  funext g
  by_cases hg : g ∈ candidate.selected
  · obtain ⟨p, hp⟩ := (mem_selected candidate g).mp hg
    have htrue := (C.eval_iff_nonempty_proofTree _).mpr ⟨p⟩
    obtain ⟨q, hq, hqmin⟩ := hmin g htrue
    have hweight : q.weight w = p.weight w := by
      simpa only [LayerTranscript.weightAt, hp, hq, Option.map_some, Option.getD_some] using
        heq g hg
    have hpmin : IsMinOn (ProofTree.weight w) Set.univ p :=
      isMinOn_univ_iff.mpr fun r => hweight ▸ isMinOn_univ_iff.mp hqmin r
    obtain ⟨_, _, huniq⟩ := hisolated g htrue
    rw [hp, hq, huniq p hpmin, huniq q hqmin]
  · have hnone (t : LayerTranscript C k) (ht : g ∉ t.selected) : t g = none :=
      Option.eq_none_iff_forall_not_mem.mpr fun p hp => ht ((mem_selected t g).mpr ⟨p, hp⟩)
    rw [hnone candidate hg, hnone canonical (hsame ▸ hg)]

open Classical in
/-- The reference transcript for the expected count and weight sum. It uses a minimum
tree for each true gate and skips every false gate. -/
noncomputable def LayerTranscript.minimum (C : LayeredSemiUnboundedCircuit G) (k : ℕ)
    (w : G → ℕ) : LayerTranscript C k :=
  fun g => if hg : C.Eval g.val then
    letI : Nonempty (ProofTree C g.val) := (C.eval_iff_nonempty_proofTree _).mp hg
    some (Function.argmin (ProofTree.weight w))
  else none

/-- Under layer min-isolation, the exact count and weight sum admit exactly one valid
transcript. This is the branch-counting step of the circuit weight scan. -/
theorem existsUnique_layerTranscript_of_min_isolation [Fintype G]
    (C : LayeredSemiUnboundedCircuit G) (k : ℕ) (w : G → ℕ)
    (hisolated : ∀ g : {g // C.layer g = k}, C.Eval g.val →
      ∃! p : ProofTree C g.val, IsMinOn (ProofTree.weight w) Set.univ p) :
    let ref := LayerTranscript.minimum C k w
    ∃! t : LayerTranscript C k, t.selected.card = ref.selected.card ∧
      (∑ g ∈ t.selected, t.weightAt w g) = ∑ g ∈ ref.selected, ref.weightAt w g := by
  classical
  intro ref
  refine ⟨ref, ⟨rfl, rfl⟩, fun t ht => ?_⟩
  refine LayerTranscript.eq_of_matching_tally (fun g hg => ?_) hisolated ht.1 ht.2
  let : Nonempty (ProofTree C g.val) := (C.eval_iff_nonempty_proofTree _).mp hg
  refine ⟨Function.argmin (ProofTree.weight w), ?_, ?_⟩
  · simp only [ref, LayerTranscript.minimum, dite_eq_left hg]
  · exact isMinOn_univ_iff.mpr fun q => le_of_not_gt (Function.not_lt_argmin _ q)

end Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit
