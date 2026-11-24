/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Duality
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Extension
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.WireExponent
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Tests for tensors over parties, upper functionals and spectral points

The structures `Cslib.PartyTensor.UpperFunctional` and `Cslib.PartyTensor.SpectralPoint` bundle
several conditions. The *support point*, `1` at a tensor with a nonzero entry and `0` at the zero
tensor, is a spectral point over every field (an example of Definition A.1 of
[AnthropicVPVNP2026]), so the bundle is satisfiable; the lemmas of the library then give
`1 ≤ F (unit K I n) ≤ n` for it. A smaller unit tensor is a restriction of a larger one, and
a wire of dimension one is equivalent to `1`.
-/

public section

namespace Cslib.PartyTensorTests

open Cslib PartyTensor Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- The support point (`Cslib.PartyTensor.SpectralPoint.support`). -/
noncomputable abbrev supportPoint : SpectralPoint K I := SpectralPoint.support K I

/-- The support point of the unit tensor of size `n ≥ 1` on a nonempty set of parties is
between `1` and `n`. -/
example [Nonempty I] (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ (supportPoint (K := K) (I := I)).toUpperFunctional (push id (unit K I n)) ∧
      (supportPoint (K := K) (I := I)).toUpperFunctional (push id (unit K I n)) ≤ n :=
  ⟨UpperFunctional.one_le_unit _ id hn, UpperFunctional.unit_le _ id n⟩

/-- A smaller unit tensor is a restriction of a larger one. -/
example : unit K I 1 ≤ unit K I 2 := unit_le_unit (by norm_num)

/-- A wire of dimension one is equivalent to `1`. -/
example (p q : I) : AntisymmRel (· ≤ ·) (wire K 1 p q) 1 := antisymmRel_wire_one p q

/-- The support point has wire exponent `0`. -/
example (p q : I) : (supportPoint (K := K) (I := I)).wireExponent p q = 0 :=
  SpectralPoint.wireExponent_support p q

/-- At a wire of dimension `3`, the support point is `1`. -/
example (p q : I) : (supportPoint (K := K) (I := I)) (wire K 3 p q) = 1 := by
  rw [SpectralPoint.apply_wire _ p q (by norm_num), SpectralPoint.wireExponent_support,
    Real.rpow_zero]

/-- The square root of a spectral point, at a wire of dimension `4`: `4 ^ (d / 2)`. -/
example (F : SpectralPoint K I) (p q : I) :
    F.rpow (1 / 2) (by norm_num) (by norm_num) (wire K 4 p q) =
      (4 : ℝ) ^ (1 / 2 * F.wireExponent p q) := by
  rw [SpectralPoint.apply_wire _ p q (by norm_num), SpectralPoint.wireExponent_rpow]
  norm_num

/-- The wire exponent of a spectral point is a pseudometric with values in `[0, 1]`. -/
example (F : SpectralPoint K I) (p q r : I) :
    0 ≤ F.wireExponent p q ∧ F.wireExponent p q ≤ 1 ∧ F.wireExponent p p = 0 ∧
      F.wireExponent p q = F.wireExponent q p ∧
      F.wireExponent p r ≤ F.wireExponent p q + F.wireExponent q r :=
  ⟨F.wireExponent_nonneg p q, F.wireExponent_le_one p q, F.wireExponent_self p,
    F.wireExponent_comm p q, F.wireExponent_triangle p q r⟩

/-- Below the upper functional of a spectral point there is a spectral point (Proposition A.5
(prop:gauge)). -/
example (F : SpectralPoint K I) : ∃ G : SpectralPoint K I, ∀ t, G t ≤ F t :=
  (F.toUpperFunctional.exists_spectralPoint_le).imp fun _ h => h.1

/-- Extending along the identity, with one map and weight `1` (Proposition A.7 (prop:extend)): some
spectral point agrees with `F` at `C` and is at most `F` everywhere. -/
example (F : SpectralPoint K I) (C : PartyTensor K I) :
    ∃ F' : SpectralPoint K I, (∀ t, F' t ≤ ∏ _l : Unit, F (push id t) ^ (1 : ℝ)) ∧
      F' (push id C) = F C :=
  SpectralPoint.exists_extend id (fun _ : Unit => id) (fun _ _ => rfl) (fun _ => 1)
    (fun _ => zero_le_one) (by simp) F C

/-- Theorem A.6 for the family with the one member `C = 1` over one party: every power of `1` is
covered by at most `2 ^ (ε N)` products of `N` factors `1`, for all large `N`. -/
example {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ (m : ℕ) (v : Fin m → Unit → ℕ), (m : ℝ) ≤ 2 ^ (ε * N) ∧
      (∀ i, ∑ β, v i β = N) ∧
      ((1 : PartyTensor K Unit) ^ N).CoveredBy fun i =>
        prod fun β => (fun _ : Unit => (1 : PartyTensor K Unit)) β ^ v i β :=
  exists_coveredBy_pow_of_forall_le (C := 1) (A := fun _ : Unit => 1)
    ⟨fun _ => (), one_ne_zero⟩ ⟨(), fun _ => (), one_ne_zero⟩ (fun _ => ⟨(), le_rfl⟩) hε

end Cslib.PartyTensorTests
