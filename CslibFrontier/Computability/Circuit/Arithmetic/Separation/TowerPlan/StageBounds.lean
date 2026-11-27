/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Counts
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Norms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.StartLoads
import Mathlib.Tactic.LinearCombination

/-!
# The tower plan: bounds for all stages

Under the conditions `StageRate` on the tower, the laws and a rate `ρ`, the norm of the loads of
the level `j` of the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; module
`Nc.Tow.Load4`) is at most `ρ ^ j` times `normBound`, by induction on the stage from the loads
after the start (`load_start_le`) and one stage at a time (`norm_load_le`); the condition
`2 ≤ ρ D` absorbs the error terms. Hence the units between a chamber and its parent are at most
`edgeBound`, and those of all chambers of the level `j` at most `2 √h ρ ^ j normBound`.

## Main definitions

* `StageRate`: the conditions on the tower, the laws and the rate.
* `startBound`, `normBound`, `edgeBound`: the bounds for the loads after the start, for the norms,
  and for the units between a chamber and its parent.

## Main results

* `normBound_nonneg`, `kap_edgeLoads_le`: the norm of the loads of the level `j`.
* `incidentSum_le_edgeBound`, `sum_incidentSum_edgeLoads_le`: the units between the chambers and
  their parents.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof: "Loads", "One stage" and "Bounds", p. 47); module `Nc.Tow.Load4`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {lhat : ℕ}
  {n : Fin A → Fin A → ℕ} {o : MoveChannel R ch FL → ℕ} {ρ : ℝ}

/-- The conditions on the tower, the laws and the rate `ρ` under which every stage multiplies the
norm of the loads by at most `ρ` (`norm_load_le`), up to a term that the factor `ρ D ≥ 2`
absorbs. -/
structure StageRate (FL : VertexLaws F T) (ρ : ℝ) : Prop where
  /-- There are edges of every type at the chambers. -/
  r_pos : 0 < r
  /-- There are places at the vertices. -/
  b_pos : 0 < b
  /-- There are types. -/
  h_pos : 0 < h
  /-- The places at a vertex are at most twice the ratio of the numbers of chambers. -/
  b_le : b ≤ 2 * D
  /-- The rate is positive. -/
  ρ_pos : 0 < ρ
  /-- The condition of `norm_load_le` on the contraction of the laws and the number of types. -/
  one_add_le : 1 + 8 * FL.contraction ≤ ρ ^ 2 * h
  /-- The rate absorbs the error terms of the stages. -/
  two_le : 2 ≤ ρ * D

variable (T) in
/-- The bound for the loads of the edges after the start (`load_start_le`). -/
@[expose] def startBound (Uu A lhat : ℕ) : ℕ := Uu * (lhat / Fintype.card (T.X 0) + 2 * A)

variable (FL) in
/-- The bound for the norms of the loads: the norm at the level `j` is at most `ρ ^ j` times it.
-/
@[expose] noncomputable def normBound (Uu A lhat : ℕ) : ℝ :=
  √h * (r * Fintype.card (T.X 0) / 2) * startBound T Uu A lhat +
    √FL.contraction * FL.scale / b * Fintype.card (T.X 0)

/-- The bound for the norms is nonnegative. -/
theorem normBound_nonneg : 0 ≤ normBound FL Uu A lhat := by
  have := Real.sqrt_nonneg FL.contraction
  unfold normBound
  positivity

/-- The norm of the loads after the start. -/
private theorem kap_zero_le : T.kap (edgeLoads (load lhat n o) 0) ≤
    √h * (r * Fintype.card (T.X 0) / 2) * startBound T Uu A lhat := by
  have h1 (e : T.Ed 0) : edgeLoads (load lhat n o) 0 e ≤ startBound T Uu A lhat :=
    edgeLoads_of_lt (load lhat n o) (Nat.succ_pos J) e ▸ load_start_le e
  have h2 : (2 * Fintype.card (T.Ed 0) : ℝ) = h * (r * Fintype.card (T.X 0)) := by
    exact_mod_cast T.two_mul_card_Ed (Nat.zero_le J)
  refine (pow_le_pow_iff_left₀ (Tower.kap_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [Tower.kap_sq, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc (r : ℝ) * Fintype.card (T.X 0) / 2 * ∑ e, (edgeLoads (load lhat n o) 0 e : ℝ) ^ 2 ≤
      r * Fintype.card (T.X 0) / 2 * ∑ _e : T.Ed 0, (startBound T Uu A lhat : ℝ) ^ 2 := by
        gcongr with e
        exact h1 e
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        linear_combination (r * Fintype.card (T.X 0) * (startBound T Uu A lhat : ℝ) ^ 2 / 4) * h2

/-- The norms of the loads with the error terms, by induction on the stage. -/
private theorem kap_add_le (hρ : StageRate FL ρ) {j : ℕ} (hj : j ≤ J) :
    T.kap (edgeLoads (load lhat n o) j) +
      √FL.contraction * FL.scale / b * Fintype.card (T.X j) ≤ ρ ^ j * normBound FL Uu A lhat := by
  induction j with
  | zero => simpa only [pow_zero, one_mul, normBound] using add_le_add_left kap_zero_le _
  | succ j ih =>
    have h1 := norm_load_le (lhat := lhat) (n := n) (o := o) hρ.r_pos hρ.b_pos hρ.h_pos hρ.b_le
      hρ.ρ_pos.le hρ.one_add_le ⟨j, by omega⟩
    have h2 := mul_le_mul_of_nonneg_left (ih (by omega)) hρ.ρ_pos.le
    have hX : (Fintype.card (T.X j) : ℝ) = D * Fintype.card (T.X (j + 1)) := by
      exact_mod_cast T.card_X j (by omega)
    have h3 := mul_le_mul_of_nonneg_right hρ.two_le
      (by positivity : 0 ≤ √FL.contraction * FL.scale / b * Fintype.card (T.X (j + 1)))
    rw [hX] at h2
    rw [pow_succ]; linarith

/-- The norm of the loads of the level `j` is at most `ρ ^ j` times the bound for the norms. -/
theorem kap_edgeLoads_le (hρ : StageRate FL ρ) {j : ℕ} (hj : j ≤ J) :
    T.kap (edgeLoads (load lhat n o) j) ≤ ρ ^ j * normBound FL Uu A lhat := by
  have := Real.sqrt_nonneg FL.contraction
  have : 0 ≤ √FL.contraction * FL.scale / b * Fintype.card (T.X j) := by positivity
  linarith [kap_add_le (lhat := lhat) (n := n) (o := o) (Uu := Uu) hρ hj]

variable (FL) in
/-- The bound for the units between a chamber and its parent. -/
@[expose] noncomputable def edgeBound (Uu A lhat : ℕ) (ρ : ℝ) : ℝ :=
  √(2 * h / Fintype.card (T.X 0)) * max 1 (√D * ρ) ^ J * normBound FL Uu A lhat

/-- **The units between a chamber and its parent** ([AnthropicVPVNP2026], Theorem H.2, proof,
"Bounds", p. 47): the loads of the edges at a chamber of a level `j ≤ J` add up to at most
`edgeBound`. -/
theorem incidentSum_le_edgeBound (hρ : StageRate FL ρ) {j : ℕ} (hj : j ≤ J) (c : T.X j) :
    (T.incidentSum (edgeLoads (load lhat n o) j) c : ℝ) ≤ edgeBound FL Uu A lhat ρ := by
  have hXj : (0 : ℝ) < Fintype.card (T.X j) := by exact_mod_cast Fintype.card_pos_iff.2 ⟨c⟩
  have hX : (Fintype.card (T.X 0) : ℝ) = D ^ j * Fintype.card (T.X j) := by
    exact_mod_cast T.card_X_zero hj
  have hD : (0 : ℝ) < D := Nat.cast_pos.2 (by linarith [hρ.b_pos, hρ.b_le])
  have hk := normBound_nonneg (FL := FL) (Uu := Uu) (A := A) (lhat := lhat)
  have e1 : √(2 * h / Fintype.card (T.X j)) = √(2 * h / Fintype.card (T.X 0)) * √D ^ j := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ √(2 * h / Fintype.card (T.X 0)) * √D ^ j), mul_pow,
      Real.sq_sqrt (by positivity), ← pow_mul, mul_comm j, pow_mul, Real.sq_sqrt hD.le, hX]
    congr 1
    field_simp
  refine (Tower.incidentSum_le hj _ c).trans ?_
  rw [e1, edgeBound]
  calc √(2 * h / Fintype.card (T.X 0)) * √D ^ j * T.kap (edgeLoads (load lhat n o) j) ≤
      √(2 * h / Fintype.card (T.X 0)) * √D ^ j * (ρ ^ j * normBound FL Uu A lhat) := by
        gcongr
        exact kap_edgeLoads_le hρ hj
    _ = √(2 * h / Fintype.card (T.X 0)) * (√D * ρ) ^ j * normBound FL Uu A lhat := by ring
    _ ≤ _ := by
        gcongr
        calc (√D * ρ) ^ j ≤ max 1 (√D * ρ) ^ j :=
              pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hρ.ρ_pos.le) (le_max_right _ _) j
          _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) hj

/-- The units between the chambers of a level `j ≤ J` and their parents. -/
theorem sum_incidentSum_edgeLoads_le (hρ : StageRate FL ρ) {j : ℕ} (hj : j ≤ J) :
    ((∑ c, T.incidentSum (edgeLoads (load lhat n o) j) c : ℕ) : ℝ) ≤
      2 * √h * ρ ^ j * normBound FL Uu A lhat := by
  refine (Tower.sum_incidentSum_le hj _).trans ?_
  have := kap_edgeLoads_le (lhat := lhat) (n := n) (o := o) (Uu := Uu) hρ hj
  calc 2 * (√h * T.kap (edgeLoads (load lhat n o) j)) ≤
      2 * (√h * (ρ ^ j * normBound FL Uu A lhat)) := by gcongr
    _ = _ := by ring

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
