/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.FiniteLineAvoidance
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteParity
import Mathlib.Data.Finset.DenselyOrdered

/-!
# Simultaneous perturbation of route bends

All interior point occurrences in a finite family can be separated from one another
and from a fixed set of points, including the route endpoints. The perturbed bends
avoid lines through any two other points of the final configuration. Small moves
preserve ray parity at every observation off the original routes. If three distinct
supporting lines meet away from their endpoints, all their defining points are fixed.
-/

public section

namespace Cslib.Polygonal.Route

/-- Keep the two endpoints, replacing only the interior listed points. -/
@[expose] def replaceBends (p : Route) (bend : Fin p.bends → ℂ) : Route where
  bends := p.bends
  point := Fin.lastCases p.finish (Fin.cases p.start bend)

@[simp] theorem start_replaceBends (p : Route) (bend : Fin p.bends → ℂ) :
    (p.replaceBends bend).start = p.start := by
  change (Fin.lastCases p.finish (Fin.cases p.start bend) (0 : Fin (p.bends + 1)).castSucc : ℂ) = _
  rw [Fin.lastCases_castSucc, Fin.cases_zero]

@[simp] theorem finish_replaceBends (p : Route) (bend : Fin p.bends → ℂ) :
    (p.replaceBends bend).finish = p.finish := by
  simp only [finish, replaceBends, Fin.lastCases_last]

@[simp] theorem point_replaceBends (p : Route) (bend : Fin p.bends → ℂ) (j : Fin p.bends) :
    (p.replaceBends bend).point j.castSucc.succ = bend j := by
  rw [← Fin.castSucc_succ]
  change (Fin.lastCases p.finish (Fin.cases p.start bend) j.succ.castSucc : ℂ) = _
  rw [Fin.lastCases_castSucc, Fin.cases_succ]

/-- Move all indexed bends by less than `η`, retaining the endpoints and the ray
parity in every direction at the observations. Each moved point is distinct from all
protected points, endpoints, and other moved points. The new bends avoid collinear triples
and exclude triple line contacts away from endpoints on every line they determine. -/
theorem exists_replaceBends_avoiding_spans {ι : Type*} [Finite ι]
    (p : ι → Route) (protectedPoints observations : Finset ℂ)
    (havoid : ∀ i z, z ∈ observations → z ∉ (p i).support)
    {η : ℝ} (hη : 0 < η) :
    let fixed := (↑protectedPoints : Set ℂ) ∪ Set.range (fun i => (p i).start) ∪
      Set.range (fun i => (p i).finish)
    ∃ bend : (i : ι) → Fin (p i).bends → ℂ,
      let placed := fun d : (i : ι) × Fin (p i).bends => bend d.1 d.2
      (∀ i j, dist (bend i j) ((p i).point j.succ.castSucc) < η) ∧
      (∀ i z, z ∈ observations → z ∉ ((p i).replaceBends (bend i)).support ∧
        ∀ u : ℂ, ((p i).replaceBends (bend i)).rayParity u z = (p i).rayParity u z) ∧
      Function.Injective placed ∧ (∀ d, placed d ∉ fixed) ∧
      (∀ d a b, a ∈ fixed ∪ Set.range placed → b ∈ fixed ∪ Set.range placed →
        a ≠ b → placed d ≠ a → placed d ≠ b → placed d ∉ affineSpan ℝ ({a, b} : Set ℂ)) ∧
      Cslib.NoTripleLineContact (fixed ∪ Set.range placed) (Set.range placed) := by
  classical
  let _ := Fintype.ofFinite ι
  let start := fun i => (p i).start
  let finish := fun i => (p i).finish
  let fixed := protectedPoints ∪ Finset.univ.image start ∪ Finset.univ.image finish
  have hfixed : (↑fixed : Set ℂ) = (↑protectedPoints : Set ℂ) ∪ Set.range start ∪
      Set.range finish := by
    simp only [fixed, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  choose tolerance hpositive hstable using fun i =>
    (p i).exists_pos_rayParity_eq_of_point_dist_lt_finset observations (havoid i)
  obtain ⟨δ, hδ, hsmall⟩ := Finset.exists_between' ({0} : Finset ℝ)
    (insert η (Finset.univ.image tolerance)) (by
      intro x hx y hy
      rw [Finset.mem_singleton.mp hx]
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hη
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
        exact hpositive i)
  have hδη : δ < η := hsmall _ (Finset.mem_insert_self _ _)
  have hδi (i : ι) : δ < tolerance i :=
    hsmall _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  let center := fun d : (i : ι) × Fin (p i).bends => (p d.1).point d.2.succ.castSucc
  obtain ⟨q, hnear, hinj, havoidFixed, hspans, htriple⟩ :=
    Cslib.exists_injective_perturbation_avoiding_spans_and_crossings center fixed
      (hδ _ (Finset.mem_singleton_self _))
  let bend := fun (i : ι) (j : Fin (p i).bends) => q ⟨i, j⟩
  refine ⟨bend, fun i j => (hnear ⟨i, j⟩).trans hδη, ?_, ?_, ?_, ?_, ?_⟩
  · intro i z hz
    let r := (p i).replaceBends (bend i)
    apply hstable i r.point (start_replaceBends _ _) (finish_replaceBends _ _) ?_ z hz
    intro j
    refine Fin.lastCases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j
    · change dist r.finish (p i).finish < tolerance i
      rw [finish_replaceBends, dist_self]
      exact hpositive i
    · change dist r.start (p i).start < tolerance i
      rw [start_replaceBends, dist_self]
      exact hpositive i
    · change dist (r.point l.succ.castSucc) _ < tolerance i
      rw [Fin.castSucc_succ, point_replaceBends]
      exact (hnear ⟨i, l⟩).trans (hδi i)
  · simpa only [bend, Sigma.eta] using hinj
  · intro d
    rw [← hfixed]
    exact havoidFixed ⟨d.1, d.2⟩
  · intro d a b ha hb hab hda hdb
    rw [← hfixed] at ha hb
    exact hspans d a b ha hb hab hda hdb
  · rw [← hfixed]
    simpa only [bend, Sigma.eta] using htriple

end Cslib.Polygonal.Route
