/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Complex multiplication of indexed polygonal routes

The factor-first constructor retains every listed node and its index. Multiplication
commutes with actual affine evaluation for ALL real parameters; for a nonzero factor it
preserves continuum simplicity, including the two-end identification of a closed route.

`mulComplex` and `support_mulComplex` are extracted once from the positioned-embedding
necessity construction. The low API is also used by actual conjugated vertex transport.
This is original finite geometry, not an arbitrary affine-map or ambient-extension framework.

## Interface laws

* `mulComplex`, `eval_mulComplex`, `endpoint_mulComplex`, `germ_mulComplex`.
* `support_mulComplex`: actual full support image, without a nonzero-factor premise.
* `IsSimple.mulComplex`: nonzero multiplication preserves the actual route model.
-/

public section

namespace Cslib.Polygonal.Route

/-- Multiply every listed node by the complex factor, retaining bends and source indices.
The explicit factor-first order is intentional. Zero factors remain admitted route data. -/
@[expose] def mulComplex (u : ℂ) (p : Route) : Route where
  bends := p.bends
  point := fun k => u * p.point k

/-- Full real affine evaluation commutes with complex multiplication. -/
theorem eval_mulComplex (u : ℂ) (p : Route) (i : Fin p.segments) (t : ℝ) :
    (mulComplex u p).eval i t = u * p.eval i t := by
  let f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ u).restrictScalars ℝ
  exact (f.toAffineMap.apply_lineMap _ _ t).symm

/-- Multiplication preserves either literal end tag, including both ends of a loop. -/
theorem endpoint_mulComplex (u : ℂ) (p : Route) (b : Bool) :
    (mulComplex u p).endpoint b = u * p.endpoint b := by
  cases b <;> rfl

/-- Outgoing germs are multiplied, without swapping their tags or adding a sign. -/
theorem germ_mulComplex (u : ℂ) (p : Route) (b : Bool) :
    (mulComplex u p).germ b = u * p.germ b := by
  cases b <;> simp only [germ, start, finish, mulComplex,
    Bool.false_eq_true, ↓reduceIte, mul_sub]; rfl

/-- Complex multiplication carries the complete continuous support to its image,
including degenerate or closed routes and the zero factor. -/
theorem support_mulComplex (u : ℂ) (p : Route) :
    (mulComplex u p).support = (fun z => u * z) '' p.support := by
  let f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ u).restrictScalars ℝ
  change (⋃ j : Fin p.segments, segment ℝ (f (p.point j.castSucc)) (f (p.point j.succ))) =
    f '' (⋃ j : Fin p.segments, segment ℝ (p.point j.castSucc) (p.point j.succ))
  rw [Set.image_iUnion]
  congr 1
  funext j
  exact (image_segment ℝ f.toAffineMap _ _).symm

/-- Nonzero complex multiplication preserves actual simplicity and both closed-end alternatives. -/
theorem IsSimple.mulComplex {p : Route} (hp : p.IsSimple) {u : ℂ} (hu : u ≠ 0) :
    (mulComplex u p).IsSimple := by
  intro i j s t hs ht he
  change Fin p.segments at i j
  have heq := (eval_mulComplex u p i s).symm.trans
    (he.trans (eval_mulComplex u p j t))
  exact hp i j s t hs ht (mul_left_cancel₀ hu heq)

end Cslib.Polygonal.Route
