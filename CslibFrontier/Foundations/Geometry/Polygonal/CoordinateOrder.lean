/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Real coordinate order on polygonal routes

Strictly increasing real coordinates of the listed nodes order the entire continuous
route by its existing chain position. Adjacent descriptions of a shared knot have equal
positions and coordinates. Parameters must belong to the closed unit interval.

## Main results

* `Cslib.Polygonal.Route.eval_re_lt_iff_position_lt_of_strictMono`: actual evaluation
  coordinates have exactly the strict order of their chain positions.
* `Cslib.Polygonal.Route.isSimple_of_strictMono_re`: strict real node order implies simplicity.

This original geometric criterion supports simplicity proofs for future ordered local
patch assembly. It is sufficient, not necessary: closed routes and routes with vertical
segments need not satisfy the premise. A route always has at least one segment.
Global assembly/contact/parity and the HT/query/source objectives remain open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Polygonal.Route

private theorem eval_re (p : Route) (i : Fin p.segments) (t : ℝ) :
    (p.eval i t).re = AffineMap.lineMap (p.point i.castSucc).re (p.point i.succ).re t := by
  change Complex.reCLM.toLinearMap.toAffineMap
    (AffineMap.lineMap (p.point i.castSucc) (p.point i.succ) t) = _
  exact AffineMap.apply_lineMap _ _ _ _

private theorem eval_re_bounds {p : Route}
    (h : StrictMono fun k => (p.point k).re) (i : Fin p.segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (p.point i.castSucc).re ≤ (p.eval i t).re ∧
      (p.eval i t).re ≤ (p.point i.succ).re := by
  have hi := (Fin.strictMono_iff_lt_succ.mp h) i
  rw [eval_re]
  exact ⟨(left_le_lineMap_iff_nonneg hi).mpr ht.1,
    (lineMap_le_right_iff_le_one hi).mpr ht.2⟩

private theorem eval_re_le_of_position_le {p : Route}
    (h : StrictMono fun k => (p.point k).re) (i j : Fin p.segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (hp : p.position i s ≤ p.position j t) : (p.eval i s).re ≤ (p.eval j t).re := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hnodes : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; exact hij
    exact (eval_re_bounds h i hs).2.trans
      ((h.monotone hnodes).trans (eval_re_bounds h j ht).1)
  · rw [eval_re, eval_re]
    apply (lineMap_le_lineMap_iff_of_lt'
      ((Fin.strictMono_iff_lt_succ.mp h) i)).mpr
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

private theorem eval_re_lt_of_position_lt {p : Route}
    (h : StrictMono fun k => (p.point k).re) (i j : Fin p.segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (hp : p.position i s < p.position j t) : (p.eval i s).re < (p.eval j t).re := by
  have hij : i.val ≤ j.val := by
    by_contra hn
    have hstep : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast Nat.lt_of_not_ge hn
    dsimp only [position] at hp
    linarith [hs.1, ht.2]
  rcases eq_or_lt_of_le hij with heq | hij
  · have he : i = j := Fin.ext heq
    subst j
    rw [eval_re, eval_re]
    apply (lineMap_lt_lineMap_iff_of_lt'
      ((Fin.strictMono_iff_lt_succ.mp h) i)).mpr
    dsimp only [position] at hp
    linarith
  · have hnodes : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; exact hij
    by_cases hgap : i.succ < j.castSucc
    · exact (eval_re_bounds h i hs).2.trans_lt
        ((h hgap).trans_le (eval_re_bounds h j ht).1)
    · have hk : i.succ = j.castSucc := le_antisymm hnodes (le_of_not_gt hgap)
      have hidx : i.val + 1 = j.val := congrArg Fin.val hk
      by_cases hs1 : s < 1
      · have hleft : (p.eval i s).re < (p.point i.succ).re := by
          rw [eval_re]
          exact (lineMap_lt_right_iff_lt hs1).mpr
            ((Fin.strictMono_iff_lt_succ.mp h) i)
        exact hleft.trans_le (hk.symm ▸ (eval_re_bounds h j ht).1)
      · have hsEq : s = 1 := le_antisymm hs.2 (le_of_not_gt hs1)
        have hiCast : (i.val : ℝ) + 1 = j.val := by exact_mod_cast hidx
        have ht0 : 0 < t := by dsimp only [position] at hp; linarith
        have hright : (p.point j.castSucc).re < (p.eval j t).re := by
          rw [eval_re]
          exact (left_lt_lineMap_iff_lt ht0).mpr
            ((Fin.strictMono_iff_lt_succ.mp h) j)
        simpa only [hsEq, eval, AffineMap.lineMap_apply_one, hk] using hright

/-- Strict node real-coordinate order agrees with actual continuum chain-position order.
Both local parameters are restricted to `[0,1]`, including adjacent knot descriptions. -/
theorem eval_re_lt_iff_position_lt_of_strictMono (p : Route)
    (h : StrictMono fun k : Fin (p.bends + 2) => (p.point k).re)
    (i j : Fin p.segments) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    (p.eval i s).re < (p.eval j t).re ↔ p.position i s < p.position j t := by
  constructor
  · intro he
    by_contra hp
    exact (not_lt_of_ge (eval_re_le_of_position_le h j i ht hs (le_of_not_gt hp))) he
  · exact eval_re_lt_of_position_lt h i j hs ht

/-- Strictly increasing real node coordinates imply simplicity on the closed parameter intervals. -/
theorem isSimple_of_strictMono_re {p : Route}
    (h : StrictMono fun k => (p.point k).re) : p.IsSimple := by
  have hn (i j : Fin p.segments) (s t : ℝ)
      (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) (he : p.eval i s = p.eval j t) :
      ¬p.position i s < p.position j t := by
    intro hp
    have hr := (eval_re_lt_iff_position_lt_of_strictMono p h i j s t hs ht).mpr hp
    exact (ne_of_lt hr) (congrArg Complex.re he)
  intro i j s t hs ht he
  left
  exact le_antisymm (le_of_not_gt (hn j i t s ht hs he.symm))
    (le_of_not_gt (hn i j s t hs ht he))

end Cslib.Polygonal.Route
