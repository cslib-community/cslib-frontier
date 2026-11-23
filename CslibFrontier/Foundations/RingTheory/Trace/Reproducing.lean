/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, finite free algebra traces)

public import CslibFrontier.Init
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic.Ring

/-!
# Multiplication traces from finite reproducing identities

A finite identity `x = ∑ i ∈ s, L (m i * x) • c i` expresses every multiplication map
as a sum of rank-one maps. Mathlib's `LinearMap.trace_smulRight` then identifies its trace
with `L` applied to the multiplier times the diagonal `∑ i ∈ s, c i * m i`.
The algebra may be any finite free commutative algebra; there is no root or separability
hypothesis and no chosen basis in the statement.

Ported from `LeanCanny.CountingHierarchy.ReproducingTrace` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. This is the linear-algebra step used by the
pure-power quotient residue trace identity.
-/

public section

namespace Algebra

open scoped BigOperators

variable {S A κ : Type*} [CommRing S] [CommRing A] [Algebra S A]
  [Module.Free S A] [Module.Finite S A]

/-- A finite reproducing identity computes every multiplication trace through its diagonal. -/
theorem trace_eq_of_reproducing (L : A →ₗ[S] S) (s : Finset κ) (c m : κ → A)
    (h : ∀ x : A, ∑ i ∈ s, L (m i * x) • c i = x) (v : A) :
    trace S A v = L (v * ∑ i ∈ s, c i * m i) := by
  have hdecomp : lmul S A v =
      ∑ i ∈ s, (L.comp (lmul S A (m i * v))).smulRight (c i) := by
    ext x
    simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
      coe_lmul_eq_mul, LinearMap.mul_apply', mul_assoc] using (h (v * x)).symm
  rw [trace_apply, hdecomp, map_sum]
  simp only [LinearMap.trace_smulRight, LinearMap.comp_apply, coe_lmul_eq_mul,
    LinearMap.mul_apply']
  rw [← map_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end Algebra
