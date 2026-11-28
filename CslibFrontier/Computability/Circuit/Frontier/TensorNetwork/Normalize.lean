/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Open
import CslibFrontier.Foundations.Data.Nat.Card
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Separate equality leaves for the exterior bits

The exact compiler of [OpenAI2026EuclideanSpectrum, Proposition 14.1] takes a loopless
trivalent network with one equality leaf at each exterior bit. Subdivide every internal
edge and attach every exterior bit by an equality wire. An old internal labeling and a
fixed input determine exactly one nonzero choice of the new labels. The construction
preserves contraction over any commutative semiring and costs at most three times the
original volume.
-/

public section

namespace Cslib.Circuits.Frontier.OpenBitNetwork

variable {R I V E : Type*} [Finite I] [Finite V] [Finite E] [CommSemiring R]
  (N : OpenBitNetwork R I V E)

/-- A trivalent network has normalized wiring when it is loopless and its exterior bits
occupy distinct equality leaves adjacent to interior vertices. The witnessing leaf edge
can have either orientation. -/
structure IsNormalized : Prop where
  /-- At most three incidences per vertex. -/
  trivalent : N.Trivalent
  /-- No internal edge is a self-loop. -/
  loopless : N.Loopless
  /-- Distinct exterior bits have distinct leaf vertices. -/
  site_injective : Function.Injective N.site
  /-- The single edge at each leaf meets an interior vertex and transmits the exterior bit. -/
  leaf : ∀ i, ∃ e, N.incidenceSet (N.site i) = {e} ∧
    ((∀ j, N.src e ≠ N.site j) ∨ (∀ j, N.tgt e ≠ N.site j)) ∧
    (∀ α x, N.tensor (N.site i) α x = if α e = x i then 1 else 0)

open scoped Classical in
private noncomputable def splitEdges : OpenBitNetwork R I (V ⊕ E) (E ⊕ E) where
  toTensorNetwork := N.toTensorNetwork.subdivide
  site i := .inl (N.site i)
  exterior_congr v α x y h := by
    cases v with
    | inl v => exact N.exterior_congr _ _ _ _ fun i hi => h i (congrArg Sum.inl hi)
    | inr e =>
      rw [TensorNetwork.subdivide_tensor_inr]
      split <;> rfl

private theorem trivalent_splitEdges (hN : N.Trivalent) : (splitEdges N).Trivalent := by
  classical
  rintro (v | e)
  · simpa [Set.ncard_ofPred, Nat.card_subtype_sum, splitEdges, TensorNetwork.subdivide]
      using hN v
  · simp [Set.ncard_ofPred, Nat.card_subtype_sum, splitEdges, TensorNetwork.subdivide]

private def attachLeaves : OpenBitNetwork R I (V ⊕ I) (E ⊕ I) where
  src := Sum.elim (Sum.inl ∘ N.src) (Sum.inl ∘ N.site)
  tgt := Sum.elim (Sum.inl ∘ N.tgt) Sum.inr
  site := Sum.inr
  tensor v α x := match v with
    | .inl v => N.tensor v (α ∘ Sum.inl) (α ∘ Sum.inr)
    | .inr i => if α (.inr i) = x i then 1 else 0
  tensor_congr v α β h := by
    funext x
    rcases v with v | i <;> dsimp only
    · exact (congrFun (N.tensor_congr v (α ∘ Sum.inl) (β ∘ Sum.inl) (fun e he =>
        h (.inl e) (he.imp (congrArg Sum.inl) (congrArg Sum.inl)))) (α ∘ Sum.inr)).trans
          (N.exterior_congr _ _ _ _ fun i hi => h (.inr i) (Or.inl (congrArg Sum.inl hi)))
    · rw [h (.inr i) (Or.inr rfl)]
  exterior_congr v α x y h := by
    rcases v with v | i
    · rfl
    · dsimp only
      rw [h i rfl]

private theorem isNormalized_attachLeaves (hN : N.Trivalent) (hl : N.Loopless) :
    (attachLeaves N).IsNormalized where
  trivalent := by
    rintro (v | i)
    · simpa [Set.ncard_ofPred, Nat.card_subtype_sum, attachLeaves, Nat.add_right_comm]
        using hN v
    · simp [Set.ncard_ofPred, Nat.card_subtype_sum, attachLeaves]
  loopless := by
    rintro (e | i)
    · exact fun h => hl e (Sum.inl.inj h)
    · exact Sum.inl_ne_inr
  site_injective := Sum.inr_injective
  leaf i := by
    refine ⟨.inr i, ?_, Or.inl (fun _ => Sum.inl_ne_inr), fun _ _ => rfl⟩
    ext e
    rcases e with e | j <;> simp [Multigraph.mem_incidenceSet, attachLeaves]

private theorem contraction_attachLeaves [Fintype V] [Fintype E] [DecidableEq E] [Fintype I]
    [DecidableEq I] (x : I → Bool) : (attachLeaves N).contraction x = N.contraction x := by
  classical
  simp only [TensorNetwork.contraction, Finset.sum_apply, Finset.prod_apply]
  rw [← (Equiv.sumArrowEquivProdArrow E I Bool).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Fintype.prod_sum_type, attachLeaves, Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  change (∑ y : I → Bool, (∏ v, N.tensor v α y) * ∏ i, if y i = x i then 1 else 0) = _
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi))
  · simp

/-- Every trivalent open bit network has a normalized realization of its entire exterior
tensor with at most three times its volume. This includes networks with loops or multiple
exterior bits at one vertex. -/
theorem exists_normalized [Fintype V] [Fintype E] [DecidableEq E] [Fintype I]
    [DecidableEq I] (hN : N.Trivalent) :
    ∃ M : OpenBitNetwork R I ((V ⊕ E) ⊕ I) ((E ⊕ E) ⊕ I), M.IsNormalized ∧
      M.volume ≤ 3 * N.volume ∧ ∀ x, M.contraction x = N.contraction x := by
  classical
  let S := splitEdges N
  have hl : S.Loopless := by rintro (e | e) <;> exact Sum.inl_ne_inr
  refine ⟨attachLeaves S, isNormalized_attachLeaves S (trivalent_splitEdges N hN) hl, ?_, ?_⟩
  · simp only [volume, Nat.card_sum]
    lia
  · intro x
    exact (contraction_attachLeaves S x).trans (congrFun N.toTensorNetwork.contraction_subdivide x)

end Cslib.Circuits.Frontier.OpenBitNetwork
