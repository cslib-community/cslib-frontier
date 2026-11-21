/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Segment order and simplicity of polygonal routes

A scalar observation that strictly increases on each segment agrees with the strict
order of chain positions. Shared knots represent one position. Equal evaluations
therefore force equal chain positions.
-/

public section

namespace Cslib.Polygonal.Route

variable {α : Type*} [LinearOrder α] (f : ℂ → α) {p : Route}

private theorem observed_nodes_strictMono
    (h : ∀ i : Fin p.segments, StrictMonoOn (fun t => f (p.eval i t)) (Set.Icc 0 1)) :
    StrictMono (fun k => f (p.point k)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  simpa only [eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
    h i (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_lt_one

private theorem observe_bounds
    (h : ∀ i : Fin p.segments, StrictMonoOn (fun t => f (p.eval i t)) (Set.Icc 0 1))
    (i : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    f (p.point i.castSucc) ≤ f (p.eval i t) ∧
      f (p.eval i t) ≤ f (p.point i.succ) := by
  have hm := (h i).monotoneOn
  simpa only [eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
    And.intro (hm (Set.left_mem_Icc.mpr zero_le_one) ht ht.1)
      (hm ht (Set.right_mem_Icc.mpr zero_le_one) ht.2)

private theorem observe_le_of_position_le
    (h : ∀ i : Fin p.segments, StrictMonoOn (fun t => f (p.eval i t)) (Set.Icc 0 1))
    (i j : Fin p.segments) {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (hp : p.position i s ≤ p.position j t) : f (p.eval i s) ≤ f (p.eval j t) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hnodes : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; exact hij
    exact (observe_bounds f h i hs).2.trans
      (((observed_nodes_strictMono f h).monotone hnodes).trans (observe_bounds f h j ht).1)
  · apply (h i).monotoneOn hs ht
    dsimp only [position] at hp
    linarith
  · have hstep : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hji
    have hpos := hp
    dsimp only [position] at hpos
    have hs0 : s = 0 := by linarith [hs.1, ht.2]
    have ht1 : t = 1 := by linarith [hs.1, ht.2]
    have he : (i.val : ℝ) = (j.val : ℝ) + 1 := by linarith [hs.1, ht.2]
    have heNat : i.val = j.val + 1 := by exact_mod_cast he
    have hk : i.castSucc = j.succ := Fin.ext heNat
    simp only [hs0, ht1, eval, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, hk, le_refl]

private theorem observe_lt_of_position_lt
    (h : ∀ i : Fin p.segments, StrictMonoOn (fun t => f (p.eval i t)) (Set.Icc 0 1))
    (i j : Fin p.segments) {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (hp : p.position i s < p.position j t) : f (p.eval i s) < f (p.eval j t) := by
  have hij : i.val ≤ j.val := by
    by_contra hn
    have hstep : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast Nat.lt_of_not_ge hn
    dsimp only [position] at hp
    linarith [hs.1, ht.2]
  rcases eq_or_lt_of_le hij with heq | hij
  · have he : i = j := Fin.ext heq
    subst j
    apply h i hs ht
    dsimp only [position] at hp
    linarith
  · have hnodes : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; exact hij
    by_cases hgap : i.succ < j.castSucc
    · exact (observe_bounds f h i hs).2.trans_lt
        (((observed_nodes_strictMono f h) hgap).trans_le (observe_bounds f h j ht).1)
    · have hk : i.succ = j.castSucc := le_antisymm hnodes (le_of_not_gt hgap)
      have hidx : i.val + 1 = j.val := congrArg Fin.val hk
      by_cases hs1 : s < 1
      · have hleft : f (p.eval i s) < f (p.point i.succ) := by
          simpa only [eval, AffineMap.lineMap_apply_one] using
            h i hs (Set.right_mem_Icc.mpr zero_le_one) hs1
        exact hleft.trans_le (hk.symm ▸ (observe_bounds f h j ht).1)
      · have hsEq : s = 1 := le_antisymm hs.2 (le_of_not_gt hs1)
        have hiCast : (i.val : ℝ) + 1 = j.val := by exact_mod_cast hidx
        have ht0 : 0 < t := by dsimp only [position] at hp; linarith
        have hright : f (p.point j.castSucc) < f (p.eval j t) := by
          simpa only [eval, AffineMap.lineMap_apply_zero] using
            h j (Set.left_mem_Icc.mpr zero_le_one) ht ht0
        simpa only [hsEq, eval, AffineMap.lineMap_apply_one, hk] using hright

/-- A scalar observation that strictly increases on each segment has exactly the
strict order of the chain positions, including adjacent knot descriptions. -/
theorem eval_lt_iff_position_lt_of_strictMonoOn (p : Route) (f : ℂ → α)
    (h : ∀ i : Fin p.segments, StrictMonoOn (fun t => f (p.eval i t)) (Set.Icc 0 1))
    (i j : Fin p.segments) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    f (p.eval i s) < f (p.eval j t) ↔ p.position i s < p.position j t := by
  constructor
  · intro he
    by_contra hp
    exact (not_lt_of_ge (observe_le_of_position_le f h j i ht hs (le_of_not_gt hp))) he
  · exact observe_lt_of_position_lt f h i j hs ht

/-- A scalar observation strictly increasing on every segment certifies simplicity. -/
theorem isSimple_of_strictMonoOn_eval
    (h : ∀ i : Fin p.segments, StrictMonoOn (fun t => f (p.eval i t)) (Set.Icc 0 1)) :
    p.IsSimple := by
  have hn (i j : Fin p.segments) (s t : ℝ)
      (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) (he : p.eval i s = p.eval j t) :
      ¬p.position i s < p.position j t := by
    intro hp
    have hr := observe_lt_of_position_lt f h i j hs ht hp
    exact (ne_of_lt hr) (congrArg f he)
  intro i j s t hs ht he
  left
  exact le_antisymm (le_of_not_gt (hn j i t s ht hs he.symm))
    (le_of_not_gt (hn i j s t hs ht he))

end Cslib.Polygonal.Route
