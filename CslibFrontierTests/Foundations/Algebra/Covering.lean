/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.Algebra.Covering.Duality
import CslibFrontier.Foundations.Algebra.Covering.Gauge

/-!
# Tests for upper functionals in a covering monoid

Clients of Proposition A.5 and of the two halves of Theorem A.6 of [AnthropicVPVNP2026] in a
commutative monoid with a covering relation, under ordinary imports.
-/

namespace Cslib.CoveringTests

open Cslib Covering

variable {M : Type} [CommMonoid M] {D : Covering M} {p : M → ℝ}

/-- Below every upper functional there is a multiplicative one (Proposition A.5). -/
example (h : IsUpperFunctional D p) :
    ∃ F : M → ℝ, IsUpperFunctional D F ∧ (∀ s t, F (s * t) = F s * F t) ∧ ∀ t, F t ≤ p t :=
  let ⟨F, hF, hmul, hle, _⟩ := h.exists_map_mul
  ⟨F, hF, hmul, hle⟩

/-- Localizing at an element `f` with `p (f ^ n) = p f ^ n` gives an upper functional below `p`
with `p f * q t ≤ q (t * f)`. -/
example (h : IsUpperFunctional D p) {f : M} (hf : 0 < p f) (hpow : ∀ n, p (f ^ n) = p f ^ n) :
    ∃ q : M → ℝ, IsUpperFunctional D q ∧ (∀ t, q t ≤ p t) ∧ ∀ t, p f * q t ≤ q (t * f) := by
  obtain ⟨q, hq, hle, h1, -⟩ := h.exists_localize hf hpow
  refine ⟨q, hq, hle, fun t => ?_⟩
  have := h1 t
  rw [mul_one, ← div_eq_inv_mul, le_div_iff₀ hf] at this
  rwa [mul_comm]

/-- The infimum of the radius set of an upper functional at `1` is `1`. -/
example (h : IsUpperFunctional D p) : sInf (radiusSet p 1) = 1 := by
  rw [h.sInf_radiusSet_eq]
  simp [h.map_one]

variable {B : Type} [Fintype B] {C : M} {A : B → M} {η : ℝ}

/-- First half of Theorem A.6: without certificates of `1` below `1`, the infimum of the weights
of certificates is an upper functional. -/
example (hη : 0 < η) (hone : ∀ t : M, ∃ r : ℕ, D.CoveredBy t (fun _ : Fin r => (1 : M)))
    (h : ∀ k W, Nonempty (Certificate D C A η 1 k W) → 1 ≤ W) :
    IsUpperFunctional D (fun t => sInf {W | ∃ k, Nonempty (Certificate D C A η t k W)}) :=
  (isUpperFunctional_sInf_certificate hη hone h).1

/-- Second half of Theorem A.6: a certificate of `1` below `1` covers `C ^ N` by few products of
`N` factors. -/
example (hη : 0 < η) (hη1 : η < 1) {β₀ : B} {c : ℕ} (hcA : D.CoveredBy C (fun _ : Fin c => A β₀))
    {k₀ : ℕ} {W : ℝ} (h : Certificate D C A η 1 k₀ W) (hW1 : W < 1) (N : ℕ) :
    ∃ (κ : Type) (_ : Fintype κ) (v : κ → B → ℕ),
      (Fintype.card κ : ℝ) ≤ ((c : ℝ) + 1) ^ (k₀ + 1) * η⁻¹ ^ N ∧
        D.CoveredBy (C ^ N) (fun j => ∏ β, A β ^ v j β) :=
  let ⟨κ, _, v, hcard, _, hcov⟩ := exists_coveredBy_pow_of_certificate hη hη1 hcA h hW1 N
  ⟨κ, _, v, hcard, hcov⟩

end Cslib.CoveringTests
