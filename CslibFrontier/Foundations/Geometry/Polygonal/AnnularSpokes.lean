/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import CslibFrontier.Foundations.Geometry.Polygonal.AnnularPaths
import CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters
import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitFan
import CslibFrontier.Foundations.Geometry.Polygonal.RadialOrder
import CslibFrontier.Foundations.Geometry.Polygonal.SampledRoute
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Polygonal spokes through an annulus

Matching clockwise lists of inner and outer ports give simple polygonal spokes with the
prescribed initial directions. The spokes meet only at their common center and reach the
outer circle only at their assigned endpoints. The proof joins straight inner rays to a
common fine sampling of the continuous annular paths. This is original finite geometry.
-/

public section

namespace Cslib.Polygonal

open AffineMap Set

/-- Connect the center to matching outer ports along prescribed inner rays. Each route is
simple, meets the complement of the open outer disk only at its finish, and shares only
its start with any other route in the family. -/
theorem exists_annular_spokes (n : ℕ) (z : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (p q : Fin (n + 1) → ℂ) (hp : ∀ i, ‖p i - z‖ = r) (hq : ∀ i, ‖q i - z‖ = R)
    (hp' : Function.Injective (fun i => ((p i - z).arg : Real.Angle)))
    (hq' : Function.Injective (fun i => ((q i - z).arg : Real.Angle)))
    (hpo : ∀ i j, i ≠ Fin.last n → j ≠ Fin.last n → i ≠ j →
      (sbtw ((p (Fin.last n) - z).arg : Real.Angle) ((p i - z).arg : Real.Angle)
        ((p j - z).arg : Real.Angle) ↔ j.val < i.val))
    (hqo : ∀ i j, i ≠ Fin.last n → j ≠ Fin.last n → i ≠ j →
      (sbtw ((q (Fin.last n) - z).arg : Real.Angle) ((q i - z).arg : Real.Angle)
        ((q j - z).arg : Real.Angle) ↔ j.val < i.val)) :
    ∃ T : Fin (n + 1) → Route,
      (∀ i, (T i).start = z ∧ (T i).finish = q i ∧ (T i).germ false = p i - z ∧
        (T i).IsSimple ∧ (T i).support \ Metric.ball z R = {q i}) ∧
      Pairwise (fun i j => (T i).support ∩ (T j).support = {z}) := by
  obtain ⟨γ, hcont, hlip, hstart, hfinish, hnorm, hinj⟩ :=
    exists_annular_paths n z hr hrR p q hp hq hp' hq' hpo hqo
  have hsep : Pairwise (fun i j => Disjoint (γ i '' Icc 0 1) (γ j '' Icc 0 1)) :=
    fun i j hij => Set.disjoint_left.mpr fun _ ⟨s, hs, hx⟩ ⟨t, ht, heq⟩ =>
      hij (congrArg Prod.fst (hinj hs ht (hx.trans heq.symm) : (i, s) = (j, t)))
  choose K hK using hlip
  have hout (i : Fin (n + 1)) := Route.eventually_sampled_outward (γ i) z (hK i) hr hrR (hnorm i)
  have hdisj := Route.eventually_pairwise_disjoint_sampled γ (fun i => (hcont i).continuousOn) hsep
  obtain ⟨m, hchord, hpair⟩ := ((Filter.eventually_all.mpr hout).and hdisj).exists
  let P (i : Fin (n + 1)) := Route.sampled (γ i) m
  let T (i : Fin (n + 1)) := Route.prepend z (P i)
  have hPstart (i : Fin (n + 1)) : (P i).start = p i :=
    (Route.sampled_start (γ i) m).trans (hstart i)
  have hPfinish (i : Fin (n + 1)) : (P i).finish = q i :=
    (Route.sampled_finish (γ i) m).trans (hfinish i)
  have hnear (i : Fin (n + 1)) (k : Fin (P i).segments) {t : ℝ} (ht : t ∈ Icc 0 1)
      (h : ‖(P i).eval k t - z‖ ≤ r) : (P i).AtEnd k t false := by
    by_contra hne
    have hpos : (P i).position 0 0 < (P i).position k t := by
      simpa only [Route.position, Fin.val_zero, Nat.cast_zero, zero_add, add_zero] using
        (lt_of_le_of_ne ((P i).position_mem k ht).1 (Ne.symm hne))
    have hlt := ((P i).norm_eval_lt_iff_position_lt_of_outward z (hchord i)
      0 k 0 t ⟨le_rfl, zero_le_one⟩ ht).mpr hpos
    rw [(P i).at_eq_start 0 ⟨le_rfl, zero_le_one⟩ (by simp [Route.position]), hPstart, hp] at hlt
    exact h.not_gt hlt
  have hfar (i : Fin (n + 1)) (k : Fin (P i).segments) {t : ℝ} (ht : t ∈ Icc 0 1)
      (h : R ≤ ‖(P i).eval k t - z‖) : (P i).AtEnd k t true := by
    by_contra hne
    have hlast : (P i).position (Fin.last (P i).bends) 1 = (P i).segments := by
      simp [Route.position, Route.segments]
    have hpos : (P i).position k t < (P i).position (Fin.last (P i).bends) 1 := by
      rw [hlast]
      exact lt_of_le_of_ne ((P i).position_mem k ht).2 hne
    have hlt := ((P i).norm_eval_lt_iff_position_lt_of_outward z (hchord i) k
      (Fin.last (P i).bends) t 1 ht ⟨zero_le_one, le_rfl⟩).mpr hpos
    rw [(P i).at_eq_finish _ ⟨zero_le_one, le_rfl⟩ hlast, hPfinish, hq] at hlt
    exact h.not_gt hlt
  have hcenter : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hport (i : Fin (n + 1)) : p i ∈ Metric.sphere z r := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hp i
  have hpinj : Function.Injective p := fun _ _ h =>
    hp' (congrArg (fun x : ℂ => ((x - z).arg : Real.Angle)) h)
  have hray (i : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc 0 1) :
      ‖lineMap z (p i) t - z‖ ≤ r := by
    rw [← dist_eq_norm, dist_lineMap_left, dist_comm z (p i), dist_eq_norm, hp i,
      Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left hr.le ht.2
  have hray_end (i : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc 0 1)
      (h : ‖lineMap z (p i) t - z‖ = r) : t = 1 :=
    lineMap_sphere_parameter hcenter (hport i) ht
      (by simpa only [Metric.mem_sphere, dist_eq_norm] using h)
  have hTend (i : Fin (n + 1)) : (T i).finish = q i := by
    change (Route.prepend z (P i)).endpoint true = _
    simp only [Route.endpoint_prepend, ↓reduceIte, hPfinish]
  have hsimple (i : Fin (n + 1)) : (T i).IsSimple := by
    apply ((P i).isSimple_of_outward z (hchord i)).prepend
    · intro heq
      have h := hp i
      rw [← hPstart i, ← heq, sub_self, norm_zero] at h
      exact hr.ne h
    · intro k s t hs ht heq
      rw [hPstart i] at heq
      have hend := hnear i k ht (heq ▸ hray i hs)
      have hcontact := ((P i).at_eq_start k ht hend).trans (hPstart i)
      have hs1 := hray_end i hs (by rw [heq, hcontact, hp])
      exact Or.inl ⟨hs1, hend⟩
  have hcases (i : Fin (n + 1)) {x : ℂ} (hx : x ∈ (T i).support) :
      x ∈ (P i).support ∨ ∃ t : ℝ, t ∈ Icc 0 1 ∧ lineMap z (p i) t = x := by
    obtain ⟨k, t, ht, heq⟩ := ((T i).mem_support_iff x).mp hx
    rcases Route.prepend_eval_cases z (P i) k t with ⟨j, hj, _⟩ | ⟨hj, _⟩
    · exact Or.inl (((P i).mem_support_iff x).mpr ⟨j, t, ht, hj.symm.trans heq⟩)
    · exact Or.inr ⟨t, ht, by rw [← hPstart i, ← hj, heq]⟩
  have hboundary (i : Fin (n + 1)) : (T i).support \ Metric.ball z R = {q i} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨?_, ?_⟩, fun x hx => ?_⟩
    · have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
      have hm := (T i).at_mem_support (Fin.last (T i).bends) ht
      rwa [(T i).at_eq_finish _ ht (by simp [Route.position, Route.segments]), hTend] at hm
    · simp only [Metric.mem_ball, dist_eq_norm, hq, lt_irrefl, not_false_eq_true]
    have hxR : R ≤ ‖x - z‖ := by
      simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hx.2
    rcases hcases i hx.1 with hp' | ⟨t, ht, heq⟩
    · obtain ⟨k, t, ht, heq⟩ := ((P i).mem_support_iff x).mp hp'
      exact heq.symm.trans (((P i).at_eq_finish k ht (hfar i k ht (heq.symm ▸ hxR))).trans
        (hPfinish i))
    · exact ((not_le_of_gt hrR) (hxR.trans (heq ▸ hray i ht))).elim
  have hsample_ray {i j : Fin (n + 1)} (hij : i ≠ j) {x : ℂ}
      (hx : x ∈ (P i).support) {t : ℝ} (ht : t ∈ Icc 0 1)
      (heq : lineMap z (p j) t = x) : False := by
    obtain ⟨k, s, hs, hk⟩ := ((P i).mem_support_iff x).mp hx
    have h0 := hnear i k hs (hk.symm ▸ (heq ▸ hray j ht))
    have hx' : x = p i := hk.symm.trans (((P i).at_eq_start k hs h0).trans (hPstart i))
    have ht1 := hray_end j ht (by rw [heq, hx', hp])
    rw [ht1, lineMap_apply_one] at heq
    exact hij (hpinj (hx'.symm.trans heq.symm))
  refine ⟨T, ?_, ?_⟩
  · intro i
    refine ⟨rfl, hTend i, ?_, hsimple i, hboundary i⟩
    simp only [T, Route.germ_prepend, Bool.false_eq_true, ↓reduceIte, hPstart]
  · intro i j hij
    apply Set.eq_singleton_iff_unique_mem.mpr
    have hmem (k : Fin (n + 1)) : z ∈ (T k).support :=
      ((T k).mem_support_iff z).mpr ⟨0, 0, ⟨le_rfl, zero_le_one⟩, by
        simp only [T, Route.eval_prepend_zero, lineMap_apply_zero]⟩
    refine ⟨⟨hmem i, hmem j⟩, fun x hx => ?_⟩
    obtain hi | ⟨s, hs, heqs⟩ := hcases i hx.1 <;> obtain hj | ⟨t, ht, heqt⟩ := hcases j hx.2
    · exact (Set.disjoint_left.mp (hpair hij) hi hj).elim
    · exact (hsample_ray hij hi ht heqt).elim
    · exact (hsample_ray hij.symm hj hs heqs).elim
    · have h := fan_contact hcenter (hport i) (hport j)
        (fun heq => hij (hpinj heq)) hs ht (heqs.trans heqt.symm)
      simpa only [h.1, lineMap_apply_zero] using heqs.symm

end Cslib.Polygonal
