/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith

/-!
# A generic ray direction for finite planar data

Multiplication by a nonzero complex number makes the heights of every two distinct points
in a prescribed finite set different. The multiplier is constructed by avoiding finitely
many forbidden real slopes; no rational-coordinate or existing generic-position assumption
is used. In particular, every nondegenerate segment with ends in the set becomes
nonhorizontal. This is an original finite-avoidance argument.
-/

public section

namespace Cslib.Polygonal

/-- A complex rotation and positive scaling separates the heights of all distinct points
of any finite set. Coincident listed occurrences require no separation and remain coincident. -/
theorem exists_mul_im_injOn (s : Finset ℂ) :
    ∃ u : ℂ, u ≠ 0 ∧ Set.InjOn (fun z => (u * z).im) (↑s : Set ℂ) := by
  classical
  let bad := (s ×ˢ s).image (fun p => (p.2.im - p.1.im) / (p.1.re - p.2.re))
  obtain ⟨m, hm⟩ := bad.exists_notMem
  refine ⟨⟨1, m⟩, fun h => one_ne_zero (congrArg Complex.re h), fun a ha b hb h => ?_⟩
  simp only [Complex.mul_im, one_mul] at h
  by_cases hre : a.re = b.re
  · exact Complex.ext hre (by rw [hre] at h; linarith)
  · refine (hm (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩)).elim
    exact ((eq_div_iff (sub_ne_zero.mpr hre)).mpr (by linarith)).symm

end Cslib.Polygonal
