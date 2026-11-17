/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PlantedClique.Model
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Probability.PlantedClique.CommonNeighborSize
import CslibFrontier.Probability.JohnsonLindenstrauss
import CslibFrontier.Foundations.Data.Finset.Density
import Mathlib.Data.NNRat.BigOperators

/-!
# Concentration in the planted-clique direction

The signed noise applied to the clique indicator is zero on the planted set. Outside it,
the coordinates are independent sums of `|S|` uniform signs. The existing upper-tail bound
for independent Rademacher rows therefore bounds its squared norm by
`(1 + ε) (n - |S|) |S|` with exponentially small failure probability.

The theorem is stated as a sum of squared row sums, before division by `|S|` to normalize
the indicator. It covers empty planted sets and empty complements as well. The bound holds
for every `ε ≥ 0` and decays exponentially in `n - |S|` when `0 < ε < 3/2`.

## Main results

* `Cslib.Probability.PlantedClique.dens_lt_sum_sq_noise_sum_le`: concentration of the
  noise in the planted direction, derived from the sampler's actual independent coins.
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.Probability.PlantedClique

private theorem sum_sq_noise_sum_eq {n : ℕ} (S : Finset (Fin n)) (ω : Coins n) :
    ∑ i, (∑ j ∈ S, noise S ω i j) ^ 2 =
      ∑ v : ↥Sᶜ, (∑ t : ↥S,
        BitString.signVal (ω (min (t : Fin n) v, max (t : Fin n) v))) ^ 2 := by
  have hzero (i : Fin n) (hi : i ∈ S) : ∑ j ∈ S, noise S ω i j = 0 :=
    sum_eq_zero fun j hj => noise_of_mem S ω hi hj
  have hout (i : Fin n) (hi : i ∈ Sᶜ) :
      ∑ j ∈ S, noise S ω i j =
        -(∑ t : ↥S, BitString.signVal (ω (min (t : Fin n) i, max (t : Fin n) i))) := by
    rw [sum_coe_sort S (fun t =>
      BitString.signVal (ω (min t i, max t i))), ← sum_neg_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hiS := mem_compl.mp hi
    rw [noise_of_not_mem S ω (i := i) (j := j)
      (fun hij => hiS (hij.symm ▸ hj)) (fun h => hiS h.1)]
    rw [min_comm, max_comm]
  calc
    ∑ i, (∑ j ∈ S, noise S ω i j) ^ 2 =
        ∑ i ∈ Sᶜ, (∑ j ∈ S, noise S ω i j) ^ 2 := by
      symm
      apply sum_subset (subset_univ _)
      intro i _ hi
      have hiS : i ∈ S := by simpa only [mem_compl, not_not] using hi
      rw [hzero i hiS, zero_pow two_ne_zero]
    _ = ∑ i ∈ Sᶜ, (∑ t : ↥S,
        BitString.signVal (ω (min (t : Fin n) i, max (t : Fin n) i))) ^ 2 := by
      exact sum_congr rfl fun i hi => by rw [hout i hi, neg_sq]
    _ = _ := (sum_coe_sort Sᶜ _).symm

/-- The squared norm of the signed noise applied to the clique indicator has an exponential
upper tail. The independence of the outside rows follows from the actual planting sampler;
the caller supplies only the nonnegative deviation `ε`. -/
theorem dens_lt_sum_sq_noise_sum_le {n : ℕ} (S : Finset (Fin n))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (dens ({ω : Coins n | (n - S.card : ℕ) * (1 + ε) * (S.card : ℝ) <
      ∑ i, (∑ j ∈ S, noise S ω i j) ^ 2} : Finset _) : ℝ) ≤
      exp (-((n - S.card : ℕ) : ℝ) / 2 * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
  classical
  let e : ↥Sᶜ ≃ Fin (Fintype.card ↥Sᶜ) := Fintype.equivFin _
  let E := e.arrowCongr (Equiv.refl (↥S → Bool))
  let P : (Fin (Fintype.card ↥Sᶜ) → ↥S → Bool) → Prop := fun b =>
    Fintype.card ↥Sᶜ * (1 + ε) * (S.card : ℝ) <
      ∑ j, (∑ i, BitString.signVal (b j i)) ^ 2
  have htail := dens_mul_lt_sum_sq_sum_mul_signVal_le (fun _ : ↥S => (1 : ℝ))
    (Fintype.card ↥Sᶜ) hε
  simp only [one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_coe, one_mul] at htail
  have hrows : (dens ({b : ↥Sᶜ → ↥S → Bool |
      (n - S.card : ℕ) * (1 + ε) * (S.card : ℝ) <
        ∑ j, (∑ i, BitString.signVal (b j i)) ^ 2} : Finset _) : ℝ) ≤
      exp (-((n - S.card : ℕ) : ℝ) / 2 * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
    have hden := Fintype.dens_filter_comp_equiv E P
    have hsum (b : ↥Sᶜ → ↥S → Bool) :
        ∑ j, (∑ i, BitString.signVal (E b j i)) ^ 2 =
          ∑ j, (∑ i, BitString.signVal (b j i)) ^ 2 :=
      e.symm.sum_comp (fun j => (∑ i, BitString.signVal (b j i)) ^ 2)
    simp only [P, hsum, Fintype.card_coe, card_compl, Fintype.card_fin] at hden
    simp only [card_compl, Fintype.card_fin] at htail
    rw [← hden] at htail
    simpa only [neg_div] using htail
  let event : Set (↥Sᶜ → ↥S → Bool) := {b |
    (n - S.card : ℕ) * (1 + ε) * (S.card : ℝ) <
      ∑ j, (∑ i, BitString.signVal (b j i)) ^ 2}
  have hlaw := congrArg (fun p : PMF (↥Sᶜ → ↥S → Bool) =>
    (p.toOuterMeasure event).toReal) (uniform_seedEdgeRows S S Subset.rfl)
  rw [PMF.toOuterMeasure_map_apply] at hlaw
  simp only [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal,
    ← nnratCast_dens] at hlaw
  have hgraph : (dens ({ω : Coins n |
      (n - S.card : ℕ) * (1 + ε) * (S.card : ℝ) <
        ∑ i, (∑ j ∈ S, noise S ω i j) ^ 2} : Finset _) : ℝ) =
      (dens ({b : ↥Sᶜ → ↥S → Bool |
        (n - S.card : ℕ) * (1 + ε) * (S.card : ℝ) <
          ∑ j, (∑ i, BitString.signVal (b j i)) ^ 2} : Finset _) : ℝ) := by
    simpa only [event, Set.mem_preimage, Set.mem_ofPred_eq, sum_sq_noise_sum_eq] using hlaw
  exact hgraph.le.trans hrows

end Cslib.Probability.PlantedClique
