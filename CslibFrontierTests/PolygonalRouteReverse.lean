/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary clients of indexed polygonal reversal)

public import CslibFrontier.Foundations.Geometry.Polygonal.Reverse
public import CslibFrontier.Foundations.Geometry.Polygonal.SlopeDetour
import Mathlib.Tactic.NormNum

/-!
Ordinary public API clients exercise literal line reversal, multiple nodes and actual
parameters, the two distinct outgoing germs of a closed triangle, and internally
constructed simple detours. A retracing closed chain is rejected without proving a
separate triangle embedding or importing private helpers.
-/

public section

namespace Cslib.Tests.PolygonalRouteReverse

open Cslib.Polygonal Cslib.Polygonal.Route

private def bent : Route := (line (0 : ℂ) 1).append ⟨1, 2⟩

-- Reversal retains all three listed nodes, in their opposite order.
example : bent.reverse.point 0 = (⟨1, 2⟩ : ℂ) ∧
    bent.reverse.point 1 = 1 ∧ bent.reverse.point 2 = 0 := by
  change (⟨1, 2⟩ : ℂ) = ⟨1, 2⟩ ∧ (1 : ℂ) = 1 ∧ (0 : ℂ) = 0
  exact ⟨rfl, rfl, rfl⟩

-- The old first piece is the LAST source piece after reversal.
example (t : ℝ) : bent.reverse.eval (1 : Fin 2) t = bent.eval 0 (1 - t) := by
  have hi : (1 : Fin bent.reverse.segments).rev = (0 : Fin bent.segments) := rfl
  exact (eval_reverse bent (1 : Fin bent.reverse.segments) t).trans
    (congrArg (fun i => bent.eval i (1 - t)) hi)

example : bent.reverse.eval (0 : Fin 2) (1 / 4) = (⟨1, 3 / 2⟩ : ℂ) := by
  change bent.reverse.eval (0 : Fin bent.reverse.segments) _ = _
  rw [eval_reverse]
  change AffineMap.lineMap (1 : ℂ) ⟨1, 2⟩ _ = _
  apply Complex.ext <;> norm_num [AffineMap.lineMap_apply_module, Complex.real_smul]

-- Evaluation transport is not restricted to the closed unit interval.
example : bent.reverse.eval (0 : Fin 2) 3 = (⟨1, -4⟩ : ℂ) := by
  change bent.reverse.eval (0 : Fin bent.reverse.segments) _ = _
  rw [eval_reverse]
  change AffineMap.lineMap (1 : ℂ) ⟨1, 2⟩ _ = _
  apply Complex.ext <;> norm_num [AffineMap.lineMap_apply_module, Complex.real_smul]

example (z : ℂ) : z ∈ bent.reverse.support ↔ z ∈ bent.support := by
  rw [support_reverse]

private def triangle : Route := ((line (0 : ℂ) 1).append ⟨0, 1⟩).append 0

-- Closure does not identify the outgoing germ tags: the vectors are 1 and i.
example : triangle.start = triangle.finish ∧ triangle.germ false = 1 ∧
    triangle.germ true = (⟨0, 1⟩ : ℂ) ∧
    triangle.reverse.germ false = (⟨0, 1⟩ : ℂ) ∧ triangle.reverse.germ true = 1 ∧
    triangle.germ false ≠ triangle.germ true := by
  simp only [germ_reverse, Bool.not_false, Bool.not_true]
  change (0 : ℂ) = 0 ∧ (1 : ℂ) - 0 = 1 ∧ (⟨0, 1⟩ : ℂ) - 0 = ⟨0, 1⟩ ∧
    (⟨0, 1⟩ : ℂ) - 0 = ⟨0, 1⟩ ∧ (1 : ℂ) - 0 = 1 ∧
    (1 : ℂ) - 0 ≠ (⟨0, 1⟩ : ℂ) - 0
  norm_num [Complex.ext_iff]

/-- Checked slope-detour separation supplies genuine simple two-piece routes; reversal
uses only the public simplicity transport, with no geometric provider assumption. -/
theorem reversed_detour_family : ∃ d : Fin 2 → ℝ, ∀ i : Fin 2,
    (slopeDetour 1 (i.val : ℝ) (d i)).reverse.IsSimple := by
  classical
  have hs : Function.Injective (fun i : Fin 2 => (i.val : ℝ)) := by
    intro i j h
    exact Fin.ext (Nat.cast_injective h)
  obtain ⟨d, h⟩ := exists_slopeDetour_separation (fun i : Fin 2 => (i.val : ℝ)) hs
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 100) none
  refine ⟨d, fun i => ?_⟩
  have hp : (slopeDetour 1 (i.val : ℝ) (d i)).IsSimple := by
    simpa using (h.1 i).2.2.1
  exact hp.reverse

-- Reversing does not make a degenerate segment simple.
example : ¬(line (0 : ℂ) 0).reverse.IsSimple := by
  rw [reverse_line, isSimple_line_iff]
  exact not_ne_iff.mpr rfl

private def retraced : Route := (line (0 : ℂ) 1).append 0

-- The two middle parameters coincide geometrically but are neither the same chain
-- parameter nor the two original ends. Permitted loop closure does not allow retracing.
example : ¬retraced.reverse.IsSimple := by
  intro h
  have hp : retraced.IsSimple := by simpa only [reverse_reverse] using h.reverse
  have heq : retraced.eval (0 : Fin 2) (1 / 2) = retraced.eval (1 : Fin 2) (1 / 2) := by
    change AffineMap.lineMap (0 : ℂ) 1 (1 / 2) = AffineMap.lineMap 1 0 (1 / 2)
    norm_num [AffineMap.lineMap_apply_module, Complex.real_smul]
  have hc := hp (0 : Fin 2) (1 : Fin 2) (1 / 2) (1 / 2)
    (by constructor <;> norm_num) (by constructor <;> norm_num) heq
  rcases hc with hc | ⟨hc, _⟩ | ⟨hc, _⟩ <;>
    norm_num [position, AtEnd, retraced, segments, line, append] at hc

end Cslib.Tests.PolygonalRouteReverse
