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
  · exact fun d => hfixed ▸ havoidFixed ⟨d.1, d.2⟩
  · exact fun d a b ha hb => hspans d a b (hfixed ▸ ha) (hfixed ▸ hb)
  · rw [← hfixed]
    simpa only [bend, Sigma.eta] using htriple

/-- An endpoint avoiding lines through every two other points in the pool forces
different endpoint pairs to have different supporting lines. -/
private theorem affineSpan_pair_ne_of_avoids_spans {pool : Set ℂ} {a b c d : ℂ}
    (hb : b ∈ pool) (hc : c ∈ pool) (hd : d ∈ pool)
    (hab : a ≠ b) (hcd : c ≠ d) (hpairs : ({a, b} : Set ℂ) ≠ {c, d})
    (havoid : ∀ x ∈ pool, ∀ y ∈ pool, x ≠ y → a ≠ x → a ≠ y →
      a ∉ affineSpan ℝ ({x, y} : Set ℂ)) :
    affineSpan ℝ ({a, b} : Set ℂ) ≠ affineSpan ℝ ({c, d} : Set ℂ) := by
  intro he
  have hcommon (x : ℂ) (hx : x ∈ pool) (hax : a ≠ x) (hbx : b ≠ x)
      (hline : x ∈ affineSpan ℝ ({a, b} : Set ℂ)) : False := by
    apply havoid b hb x hx hbx hab hax
    rw [affineSpan_pair_eq_of_mem_of_mem_of_ne (right_mem_affineSpan_pair ℝ a b) hline hbx]
    exact left_mem_affineSpan_pair ℝ a b
  by_cases hac : a = c
  · have hbd : b ≠ d := fun h => hpairs (by rw [hac, h])
    exact hcommon d hd (hac.trans_ne hcd) hbd (he.symm ▸ right_mem_affineSpan_pair ℝ c d)
  by_cases had : a = d
  · have hbc : b ≠ c := fun h => hpairs (by rw [had, h, Set.pair_comm])
    exact hcommon c hc hac hbc (he.symm ▸ left_mem_affineSpan_pair ℝ c d)
  · exact havoid c hc d hd hcd hac had (he ▸ left_mem_affineSpan_pair ℝ a b)

/-- A family with distinct ports and general-position bends has distinct listed
points along each route and distinct segment supporting lines. These lines differ
from those through two distinct fixed points. Each segment uses a moved point. -/
theorem family_affineSpan_separation {ι : Type*} (p : ι → Route) (protectedPoints : Set ℂ)
    (hbends : ∀ e, 0 < (p e).bends)
    (hends : Function.Injective (fun d : ι × Bool => (p d.1).endpoint d.2)) :
    let placed := fun d : (e : ι) × Fin (p e).bends => (p d.1).point d.2.castSucc.succ
    let fixed := protectedPoints ∪ Set.range (fun e => (p e).start) ∪
      Set.range (fun e => (p e).finish)
    let line (d : (e : ι) × Fin (p e).segments) :=
      affineSpan ℝ ({(p d.1).point d.2.castSucc, (p d.1).point d.2.succ} : Set ℂ)
    Function.Injective placed → (∀ d, placed d ∉ fixed) →
    (∀ d a b, a ∈ fixed ∪ Set.range placed → b ∈ fixed ∪ Set.range placed →
      a ≠ b → placed d ≠ a → placed d ≠ b → placed d ∉ affineSpan ℝ ({a, b} : Set ℂ)) →
    (∀ e, Function.Injective (p e).point) ∧
    (∀ d : (e : ι) × Fin (p e).segments,
      let a := (p d.1).point d.2.castSucc
      let b := (p d.1).point d.2.succ
      a ∈ fixed ∪ Set.range placed ∧ b ∈ fixed ∪ Set.range placed ∧
        (a ∈ Set.range placed ∨ b ∈ Set.range placed) ∧ a ≠ b) ∧
    Function.Injective line ∧
    ∀ d, ∀ a ∈ fixed, ∀ b ∈ fixed, a ≠ b → line d ≠ affineSpan ℝ ({a, b} : Set ℂ) := by
  dsimp only
  let B := (e : ι) × Fin (p e).bends
  let N := (e : ι) × Fin ((p e).segments + 1)
  let E := ι × Bool
  let placed := fun d : B => (p d.1).point d.2.castSucc.succ
  let fixed := protectedPoints ∪ Set.range (fun e => (p e).start) ∪
    Set.range (fun e => (p e).finish)
  intro hinj hfixed hspans
  let endNode (d : E) : N := ⟨d.1, if d.2 then Fin.last (p d.1).segments else 0⟩
  let bendNode (d : B) : N := ⟨d.1, d.2.castSucc.succ⟩
  let node : E ⊕ B → N := Sum.elim endNode bendNode
  let point (d : N) := (p d.1).point d.2
  have hnode : Function.Surjective node := by
    rintro ⟨e, k⟩
    refine Fin.lastCases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) k
    · exact ⟨.inl (e, true), rfl⟩
    · exact ⟨.inl (e, false), rfl⟩
    · exact ⟨.inr ⟨e, i⟩, congrArg (Sigma.mk e) (Fin.castSucc_succ i).symm⟩
  have hEnd (d : E) : point (endNode d) = (p d.1).endpoint d.2 := by
    rcases d with ⟨e, b⟩
    cases b <;> rfl
  have hEndFixed (d : E) : point (endNode d) ∈ fixed := by
    rw [hEnd]
    rcases d with ⟨e, _ | _⟩
    · exact Or.inl (Or.inr ⟨e, rfl⟩)
    · exact Or.inr ⟨e, rfl⟩
  have hpoint : Function.Injective point := by
    apply Function.Injective.of_comp_right _ hnode
    have heq : point ∘ node = Sum.elim (point ∘ endNode) (point ∘ bendNode) := by
      funext d
      cases d <;> rfl
    rw [heq]
    refine Sum.elim_injective.mpr ⟨?_, hinj, ?_⟩
    · exact fun x y h => hends ((hEnd x).symm.trans (h.trans (hEnd y)))
    · exact fun x y h => hfixed y (h ▸ hEndFixed x : (point ∘ bendNode) y ∈ fixed)
  have hpool (d : N) : point d ∈ fixed ∪ Set.range placed := by
    obtain ⟨s, rfl⟩ := hnode d
    cases s with
    | inl x => exact Or.inl (hEndFixed x)
    | inr y => exact Or.inr ⟨y, rfl⟩
  let S := (e : ι) × Fin (p e).segments
  let left (d : S) : N := ⟨d.1, d.2.castSucc⟩
  let right (d : S) : N := ⟨d.1, d.2.succ⟩
  have hnondeg (d : S) : point (left d) ≠ point (right d) := by
    intro h
    have hval := congrArg (fun d : N => d.2.val) (hpoint h)
    change d.2.val = d.2.val + 1 at hval
    omega
  have hmovable (d : S) : point (left d) ∈ Set.range placed ∨
      point (right d) ∈ Set.range placed := by
    rcases d with ⟨e, i⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · exact Or.inr ⟨⟨e, ⟨0, hbends e⟩⟩, rfl⟩
    · exact Or.inl ⟨⟨e, k⟩, rfl⟩
  have hpair (d f : S) (hEq : ({point (left d), point (right d)} : Set ℂ) =
      {point (left f), point (right f)}) : d = f := by
    have hl : point (left d) = point (left f) ∨ point (left d) = point (right f) := by
      have h : point (left d) ∈ ({point (left f), point (right f)} : Set ℂ) :=
        hEq ▸ Set.mem_insert _ _
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    rcases hl with h | h
    · have he := congrArg Sigma.fst (hpoint h)
      rcases d with ⟨e, i⟩
      rcases f with ⟨f, j⟩
      change e = f at he
      subst f
      have hv := congrArg (fun d : N => d.2.val) (hpoint h)
      exact congrArg (Sigma.mk e) (Fin.ext hv)
    · have hv := congrArg (fun d : N => d.2.val) (hpoint h)
      change d.2.val = f.2.val + 1 at hv
      have hr : point (right d) = point (left f) ∨ point (right d) = point (right f) := by
        have hmem : point (right d) ∈ ({point (left f), point (right f)} : Set ℂ) :=
          hEq ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
      rcases hr with hr | hr
      · have ht := congrArg (fun d : N => d.2.val) (hpoint hr)
        change d.2.val + 1 = f.2.val at ht
        omega
      · have ht := congrArg (fun d : N => d.2.val) (hpoint hr)
        change d.2.val + 1 = f.2.val + 1 at ht
        omega
  have hcompare (d : S) (a b : ℂ) (ha : a ∈ fixed ∪ Set.range placed)
      (hb : b ∈ fixed ∪ Set.range placed) (hab : a ≠ b)
      (hne : ({point (left d), point (right d)} : Set ℂ) ≠ {a, b}) :
      affineSpan ℝ ({point (left d), point (right d)} : Set ℂ) ≠
        affineSpan ℝ ({a, b} : Set ℂ) := by
    rcases hmovable d with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact affineSpan_pair_ne_of_avoids_spans (hpool (right d)) ha hb (hnondeg d) hab hne
        (fun x hx y hy hxy hdx hdy => hk ▸ hspans k x y hx hy hxy (hk.trans_ne hdx)
          (hk.trans_ne hdy))
    · rw [Set.pair_comm (point (left d)) (point (right d))] at hne ⊢
      exact affineSpan_pair_ne_of_avoids_spans (hpool (left d)) ha hb (hnondeg d).symm hab hne
        (fun x hx y hy hxy hdx hdy => hk ▸ hspans k x y hx hy hxy (hk.trans_ne hdx)
          (hk.trans_ne hdy))
  refine ⟨?_, fun d => ⟨hpool (left d), hpool (right d), hmovable d, hnondeg d⟩, ?_, ?_⟩
  · intro e i j he
    exact Fin.ext (congrArg (fun d : N => d.2.val)
      (hpoint (show point ⟨e, i⟩ = point ⟨e, j⟩ from he)))
  · intro d f he
    by_contra hdf
    exact hcompare d _ _ (hpool (left f)) (hpool (right f)) (hnondeg f)
      (fun hp => hdf (hpair d f hp)) he
  · intro d a ha b hb hab
    apply hcompare d a b (Or.inl ha) (Or.inl hb) hab
    intro hp
    have hsub : ({point (left d), point (right d)} : Set ℂ) ⊆ fixed :=
      hp ▸ Set.insert_subset_iff.mpr ⟨ha, Set.singleton_subset_iff.mpr hb⟩
    rcases hmovable d with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact hfixed k (hk.symm ▸ hsub (Set.mem_insert _ _) : placed k ∈ fixed)
    · exact hfixed k (hk.symm ▸ hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _)) :
        placed k ∈ fixed)

end Cslib.Polygonal.Route
