/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
public import Mathlib.Logic.Function.DependsOn
import CslibFrontier.Foundations.Probability.SecondMoment

/-!
# Coordinate events in finite products

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_pi_eq`: the probability that coordinate `i` equals `a` is
  `p i a`.
* `Cslib.Probability.PMF.toOuterMeasure_pi_inter_eq_mul`,
  `Cslib.Probability.PMF.toOuterMeasure_pi_eq_inter`: events depending on disjoint sets of
  coordinates (in particular `x i = a` and an event avoiding `i`) are independent.
* `Cslib.Probability.PMF.toOuterMeasure_pi_forall`: the probability that every coordinate lies in
  its own event is the product of the probabilities.
* `Cslib.Probability.PMF.toOuterMeasure_pi_exists_le`: a union bound for coordinate events.
-/

public section

namespace Cslib.Probability.PMF

open MeasureTheory ProbabilityTheory

/-- Coordinate `i` of an independent tuple equals `a` with probability `p i a`. -/
theorem toOuterMeasure_pi_eq {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p : ∀ i, PMF (α i)) (i : ι) (a : α i) :
    (pi p).toOuterMeasure {x | x i = a} = p i a := by
  rw [show {x : ∀ i, α i | x i = a} = (fun x => x i) ⁻¹' {a} from rfl,
    ← PMF.toOuterMeasure_map_apply, pi_map_eval, PMF.toOuterMeasure_apply_singleton]

/-- **Events on disjoint coordinates are independent**: in an independent product, an event
depending only on the coordinates in `S` and an event depending only on the coordinates in a
disjoint set `T` are independent. This is the finite-PMF form of
`ProbabilityTheory.indepSet_pi_of_dependsOn`. -/
theorem toOuterMeasure_pi_inter_eq_mul {V : Type*} [Fintype V] {α : V → Type*} [∀ v, Finite (α v)]
    (p : ∀ v, PMF (α v)) {S T : Set V}
    (hST : Disjoint S T) {E F : Set (∀ v, α v)} (hE : DependsOn (· ∈ E) S)
    (hF : DependsOn (· ∈ F) T) :
    (pi p).toOuterMeasure (E ∩ F) = (pi p).toOuterMeasure E * (pi p).toOuterMeasure F := by
  let (v : V) : MeasurableSpace (α v) := ⊤
  have hmeas (B : Set (∀ v, α v)) : MeasurableSet B := B.to_countable.measurableSet
  have hind := toMeasure_pi p ▸ indepSet_pi_of_dependsOn (μ := fun v => (p v).toMeasure)
    (hmeas E) (hmeas F) hE hF hST
  simpa only [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (hmeas _)] using
    (indepSet_iff_measure_inter_eq_mul (hmeas E) (hmeas F) _).1 hind

/-- Fixing coordinate `i` to `a` is independent of any event `E` depending only on a coordinate set
`S` with `i ∉ S`. -/
theorem toOuterMeasure_pi_eq_inter {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p : ∀ i, PMF (α i)) {i : ι} {a : α i} {S : Set ι} (hi : i ∉ S)
    {E : Set (∀ i, α i)} (hE : DependsOn (· ∈ E) S) :
    (pi p).toOuterMeasure ({x | x i = a} ∩ E) = p i a * (pi p).toOuterMeasure E := by
  rw [toOuterMeasure_pi_inter_eq_mul p (Set.disjoint_singleton_left.2 hi)
    (fun _ _ h => propext <| by simp [h i rfl]) hE, toOuterMeasure_pi_eq]

/-- The probability that every coordinate of an independent tuple lies in its own event is the
product of the probabilities. -/
theorem toOuterMeasure_pi_forall {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p : ∀ i, PMF (α i)) (E : ∀ i, Set (α i)) :
    (pi p).toOuterMeasure {u | ∀ i, u i ∈ E i} = ∏ i, (p i).toOuterMeasure (E i) := by
  classical
  have := fun i => Fintype.ofFinite (α i)
  simp only [PMF.toOuterMeasure_apply, tsum_fintype, Set.indicator_apply, Set.mem_ofPred_eq,
    pi_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : ∀ i, u i ∈ E i
  · rw [ite_eq_left hu]
    exact Finset.prod_congr rfl fun i _ => (ite_eq_left (hu i)).symm
  · obtain ⟨i, hi⟩ := not_forall.mp hu
    rw [ite_eq_right hu]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

/-- The probability that some coordinate lies in its bad event is at most the sum of the
coordinate probabilities. The marginal identities supply the exact coordinate laws. -/
theorem toOuterMeasure_pi_exists_le {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Finite (α i)] (p : ∀ i, PMF (α i)) (bad : ∀ i, Set (α i)) :
    (pi p).toOuterMeasure {x | ∃ i, x i ∈ bad i} ≤ ∑ i, (p i).toOuterMeasure (bad i) := by
  classical
  have hset : {x : ∀ i, α i | ∃ i, x i ∈ bad i} = ⋃ i, (· i) ⁻¹' bad i := by
    ext
    simp
  rw [hset]
  calc _ ≤ ∑ i, (pi p).toOuterMeasure ((· i) ⁻¹' bad i) :=
        MeasureTheory.measure_iUnion_fintype_le _ _
    _ = _ := Finset.sum_congr rfl fun i _ => by rw [← PMF.toOuterMeasure_map_apply, pi_map_eval]

end Cslib.Probability.PMF
