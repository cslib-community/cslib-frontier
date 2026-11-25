/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Poincare.Lengths
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Poincare.Poincare
import CslibFrontier.Foundations.GroupTheory.SLTower.Gen

/-! Tests of Appendix F of [AnthropicVPVNP2026] as a client: the simple root elements generate
`U_3`; the constant `κ_1 = 0`; Lemma F.3 and the window size of Theorem F.6 for `μ = 2`, `s = 1`;
and Theorem F.6 applied to the zero price. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationPoincare

open Cslib.PartyTensor Cslib.SLTower Cslib.Circuits.Arithmetic.Separation.Poincare
open Cslib.Circuits.Arithmetic.Separation.Flag Cslib.Circuits.Arithmetic.Separation.TwoCases

/-- The two simple root elements generate `U_3`. -/
example : Subgroup.closure (Set.range (x 3)) = ⊤ := closure_range_x

/-- A function on `U_3` that is invariant under left multiplication by the `x_j` is constant. -/
example (f : U 3 → ℕ) (hf : ∀ j u, f (x 3 j * u) = f u) : f (x 3 0) = f 1 :=
  apply_eq_of_x_mul hf _ _

/-- `κ_1 = 0`: the group `U_1` is trivial. -/
example : kappa 2 1 1 = 0 := by simp [kappa]

/-- Lemma F.3 for `μ = 2`, `s = 1` and `n = 4`. -/
example : Bd 2 1 4 (kappa 2 1 4) := bd_kappa le_rfl le_rfl 4

/-- A window size `u` for `μ = 2`, `s = 1`. -/
example : ∃ u : ℕ, 2 ≤ u ∧
    4 * (kappa 2 1 (3 * u) ^ 2 * (3 * u : ℕ)) ≤ (1 / 32) ^ 2 * ((u : ℝ) - 1) ^ 2 :=
  exists_kappa_le le_rfl le_rfl (by norm_num)

/-- Theorem F.6 in the contracting case. -/
example {K : Type} [Field K] (hK : ContractingCase K) :
    ∃ u : ℕ, 2 ≤ u ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ PoincareBound K u C₀ :=
  exists_poincareBound hK

/-- The Poincaré bound at `l = 2` for a price `w` on `U_{2u}`. -/
example {K : Type} [Field K] {u : ℕ} {C₀ : ℝ} (hP : PoincareBound K u C₀)
    (w : U (2 * u) → U (2 * u) → ℝ) (hw : IsPrice K w) :
    (∑ g, ∑ k, w k (g * k) ^ 2) / (Fintype.card (U (2 * u)) : ℝ) ^ 2 ≤
      C₀ * ∑ j, (∑ k, w k (x (2 * u) j * k) ^ 2) / Fintype.card (U (2 * u)) :=
  hP 2 le_rfl w hw

/-- The displacement lengths of maps into a price space contract in the contracting case. -/
example {K : Type} [Field K] {μ : ℕ} {s : ℝ}
    (hcase : ∀ w : Mt μ → Mt μ → ℝ, IsPrice K w → distAtRank w μ ≤ s * distAtRank w 1)
    {Y : Type} [MetricSpace Y] (hY : IsPrice K fun a b : Y => dist a b)
    (z : PiLp 2 fun _ : U 3 => Y) : Contr ((transAct (U 3) Y).len z) μ s :=
  contr_len_transAct hcase hY z

end CslibFrontierTests.SeparationPoincare
