/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.BoundedFanIn
public import CslibFrontier.Computability.Circuit.Frontier.Correlation
public import CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.BijectiveSubmatrixRobust
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Components
import CslibFrontier.Foundations.Data.Set.Card

/-!
# Frontier lower bounds for quantum circuits

Building on the active-qubit wire-segment tensor network compiler
(`Cslib.Circuits.Frontier.CompiledQuantumNet` in
`CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork`), this module establishes four
families of unconditional quantum two-qubit gate lower bounds over `Cslib.Quantum.Circuit N`
(allowing unlimited ancillas `N` and unlimited free single-qubit `U(2)` gates):

1. **`BQP` correlation decay and bounded-error decision**
   (`eventually_abs_quantumCorrelation_hardForm_le_of_layoutBound`,
   `eventually_abs_quantumCorrelation_hardForm_le_switched`,
   `eventually_lt_twoQubitCount_bqp_hardForm_switched`). Correlation of single-qubit measurement
   acceptance probability with the nonconstructively chosen bilinear form `hardForm n` decays as
   `2 ^ (-γ n)` below `(1 + π / (6 arccos (5 / 6)) - ε) n ≈ 1.893993 n` bond-rank-two gates
   (`CNOT`, `CZ`, `Gate.controlled V`), `(13 / 8 - ε) n` general `U(4)` gates via
   `layoutBound_two_fifths_four` (`A₄ = 2 / 5`), and `(7 / 4 - ε) n` under `LayoutBound 4 (1 / 3)`.
2. **`UQP` unbounded-error sign-rank**
   (`eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound`,
   `eventually_lt_twoQubitCount_uqp_hardForm_switched`). Deciding `hardForm n` with strict threshold
   `θ` (`θ < prob x ↔ hardForm n x`, with arbitrarily small margin) requires more than
   `(1 + π / (12 arccos (5 / 6)) - ε) n ≈ 1.446996 n` bond-rank-two gates and `(21 / 16 - ε) n`
   general `U(4)` gates (`(11 / 8 - ε) n` under `LayoutBound 4 (1 / 3)`).
3. **Quadratic phase-state preparation fidelity decay**
   (`eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound`,
   `eventually_fidelity_phaseState_hardMatrix_le_switched`). Squared overlap
   `‖⟪ψ_{hardMatrix n}, C |x₀⟩⟫‖²` with the `n`-qubit computational-basis phase state of the
   nonconstructively chosen `hardMatrix n` decays as `2 ^ (-γ n)` below
   `(1 + π / (3 arccos (5 / 6)) - ε) n ≈ 2.787986 n` bond-rank-two gates and `(9 / 4 - ε) n` general
   `U(4)` gates (`(5 / 2 - ε) n` under `LayoutBound 4 (1 / 3)`).
4. **Reversible and quantum `𝔽₂` linear synthesis**
   (`eventually_lt_twoQubitCount_linear_of_layoutBound`,
   `eventually_lt_twoQubitCount_linear_switched`). Coherently computing the nonconstructively chosen
   invertible submatrix-robust linear bijection `boolMulVec (robustBijectiveMatrix n)` requires more
   than `(1 + 2π / (3 arccos (5 / 6)) - ε) n ≈ 4.575972 n` bond-rank-two gates and `(7 / 2 - ε) n`
   general `U(4)` gates (`(4 - ε) n` under `LayoutBound 4 (1 / 3)`).

## Main definitions

* `Cslib.Circuits.Frontier.robustBijectiveMatrix`: nonconstructively chosen family of invertible
  submatrix-robust `n × n` matrices over `𝔽₂` (via `Matrix.exists_bijective_submatrixRobust`).

## Main results

* `Cslib.Circuits.Frontier.layoutBound_two_fifths_four`: unconditional `LayoutBound 4 (2 / 5)`.
* `Cslib.Circuits.Frontier.robustBijectiveMatrix_bijective`,
  `Cslib.Circuits.Frontier.robustBijectiveMatrix_submatrixRobust`,
  `Cslib.Circuits.Frontier.boolMulVec_robustBijectiveMatrix_bijective`: bijectivity and square-block
  robustness of `robustBijectiveMatrix n`.
* `Cslib.Circuits.Frontier.eventually_abs_quantumCorrelation_hardForm_le_of_layoutBound`,
  `Cslib.Circuits.Frontier.eventually_abs_quantumCorrelation_hardForm_le_switched`,
  `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_bqp_hardForm_switched`: `BQP` single-qubit
  measurement correlation decay and decision bounds (`1.893993 n` / `1.625 n` / `1.75 n`).
* `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound`,
  `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_uqp_hardForm_switched`: `UQP` unbounded-error
  sign-rank lower bounds (`1.446996 n` / `1.3125 n` / `1.375 n`).
* `Cslib.Circuits.Frontier.eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound`,
  `Cslib.Circuits.Frontier.eventually_fidelity_phaseState_hardMatrix_le_switched`: quadratic phase
  state preparation fidelity decay (`2.787986 n` / `2.25 n` / `2.5 n`).
* `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_linear_of_layoutBound`,
  `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_linear_switched`: reversible and quantum
  linear synthesis lower bounds (`4.575972 n` / `3.5 n` / `4.0 n`).
-/

public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics Real Matrix
open scoped Finset

/-- **Unconditional `LayoutBound 4 (2 / 5)`** via `Gaussian.degreeCoefficient_four`. -/
theorem layoutBound_two_fifths_four : LayoutBound 4 (2 / 5) :=
  Gaussian.degreeCoefficient_four ▸ layoutBound_degree (by norm_num)

/-! ### Chosen family of invertible submatrix-robust linear maps over `𝔽₂` -/

/-- Nonconstructively chosen family of invertible submatrix-robust `n × n` matrices over `𝔽₂`. -/
noncomputable def robustBijectiveMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Classical.choose (Matrix.exists_bijective_submatrixRobust n)

theorem robustBijectiveMatrix_bijective (n : ℕ) :
    Function.Bijective (robustBijectiveMatrix n).mulVec :=
  (Classical.choose_spec (Matrix.exists_bijective_submatrixRobust n)).1

theorem robustBijectiveMatrix_submatrixRobust (n : ℕ) :
    (robustBijectiveMatrix n).SubmatrixRobust (2 * (2 * Nat.sqrt n + 1)) :=
  (Classical.choose_spec (Matrix.exists_bijective_submatrixRobust n)).2

/-- `boolMulVec (robustBijectiveMatrix n)` is a bijection of `Fin n → Bool` (hence a genuine
classical reversible `n`-qubit gate via `Quantum.Gate.ofPerm`). -/
theorem boolMulVec_robustBijectiveMatrix_bijective (n : ℕ) :
    Function.Bijective (boolMulVec (robustBijectiveMatrix n)) := by
  let bitEquiv : Bool ≃ ZMod 2 :=
    { toFun := BitString.bitVal (ZMod 2)
      invFun := fun z => decide (z = 1)
      left_inv := fun b => by cases b <;> decide
      right_inv := fun z => by revert z; decide }
  let vecEquiv : (Fin n → Bool) ≃ (Fin n → ZMod 2) := Equiv.piCongrRight fun _ => bitEquiv
  have heq : boolMulVec (robustBijectiveMatrix n) =
      vecEquiv.symm ∘ (robustBijectiveMatrix n).mulVec ∘ vecEquiv := by
    ext x i
    rfl
  rw [heq]
  exact vecEquiv.symm.bijective.comp ((robustBijectiveMatrix_bijective n).comp vecEquiv.bijective)

/-! ### Shared closed-set bisection supply-demand and asymptotic helpers -/

section MainBounds

open Classical in
/-- Given a vertex layout `lay` of `V_fin` and `n` embedded leaf vertices `leaf : Fin n ↪ V_fin`,
there is a step `t < Nat.card V_fin` where `{i | leaf i ∈ lay.initial t}.ncard = n / 2`
(whenever `1 ≤ n`). -/
private theorem exists_bisection_step {V_fin : Type}
    {n : ℕ} (hn : 1 ≤ n) (leaf : Fin n ↪ V_fin) (lay : Layout V_fin) :
    ∃ t < Nat.card V_fin, {i : Fin n | leaf i ∈ lay.initial t}.ncard = n / 2 := by
  let f (t : ℕ) : ℕ := {i : Fin n | leaf i ∈ lay.initial t}.ncard
  have hf0 : f 0 = 0 := by simp only [f, Layout.initial_zero, mem_empty_iff_false, ofPred_false,
    ncard_empty]
  have hfV : f (Nat.card V_fin) = n := by
    have hinit : lay.initial (Nat.card V_fin) = univ := lay.initial_of_card_le le_rfl
    simp only [f, hinit, mem_univ, ofPred_true, ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hstep : ∀ t < Nat.card V_fin, f (t + 1) ≤ f t + 1 := by
    intro t ht
    simp only [f, lay.initial_succ ht]
    have hsub : {i : Fin n | leaf i ∈ insert (lay.symm ⟨t, ht⟩) (lay.initial t)} ⊆
        {i : Fin n | leaf i = lay.symm ⟨t, ht⟩} ∪ {i : Fin n | leaf i ∈ lay.initial t} :=
      fun _ hi => hi
    have hle1 : {i : Fin n | leaf i = lay.symm ⟨t, ht⟩}.ncard ≤ 1 := by
      by_cases hex : ∃ i, leaf i = lay.symm ⟨t, ht⟩
      · obtain ⟨i₀, hi₀⟩ := hex
        have hsing : {i : Fin n | leaf i = lay.symm ⟨t, ht⟩} = {i₀} := by
          ext i; simp only [mem_ofPred_eq, mem_singleton_iff]
          exact ⟨fun h => leaf.injective (h.trans hi₀.symm), fun h => h ▸ hi₀⟩
        rw [hsing, ncard_singleton]
      · push Not at hex
        have hemp : {i : Fin n | leaf i = lay.symm ⟨t, ht⟩} = ∅ := by
          ext i; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; exact hex i
        rw [hemp, ncard_empty]; exact Nat.zero_le 1
    have h1 := (ncard_le_ncard hsub (toFinite _)).trans (ncard_union_le _ _)
    omega
  have hgoal_le : n / 2 ≤ f (Nat.card V_fin) := by rw [hfV]; exact Nat.div_le_self n 2
  have hex : ∃ t ≤ Nat.card V_fin, f t = n / 2 := by
    suffices ∀ m ≤ Nat.card V_fin, n / 2 ≤ f m → ∃ t ≤ m, f t = n / 2 from
      this (Nat.card V_fin) le_rfl hgoal_le
    intro m
    induction m with
    | zero =>
      intro _ hm0
      exact ⟨0, le_rfl, by omega⟩
    | succ m ihm =>
      intro hmV hge
      by_cases hprev : n / 2 ≤ f m
      · obtain ⟨t, htm, ht_eq⟩ := ihm (by omega) hprev
        exact ⟨t, by omega, ht_eq⟩
      · have hst := hstep m (by omega)
        exact ⟨m + 1, le_rfl, by omega⟩
  obtain ⟨t, ht_le, ht_eq⟩ := hex
  refine ⟨t, ?_, ht_eq⟩
  rcases eq_or_lt_of_le ht_le with rfl | hlt
  · exfalso; rw [hfV] at ht_eq; omega
  · exact hlt

/-- **Shared finite closed-set bisection supply-demand inequality** on a compiled multigraph `G`
with embedded leaves `leaf : Fin m ↪ V_fin`. Every closed set (`edgeCut = ∅`) takes either at most
`slack + e_defic` or at least `m - (slack + e_defic)` leaves; at the bisection step `t` where
`lay.initial t` contains `m / 2` leaves, `lay.initial t \ W` cannot have intermediate size, forcing
component `W` to contain at least `m - (slack + e_defic)` leaves and bounding `cycleRankOn W`. -/
private theorem finite_bisection_supply_demand {V_fin E_fin : Type}
    [Finite E_fin]
    (G : Multigraph V_fin E_fin) (lay : Layout V_fin)
    {A η C_lay : ℝ} (hAη : 0 ≤ A + η)
    (hlay : ∀ t (ht : t < Nat.card V_fin),
      G.frontier lay t ⊆ G.touching (G.component (lay.symm ⟨t, ht⟩)) ∧
      ((G.frontier lay t).ncard : ℝ) ≤
        (A + η) * G.cycleRankOn (G.component (lay.symm ⟨t, ht⟩)) + η * Nat.card V_fin + C_lay)
    {m s : ℕ} {w_r : ℝ} (hm : 1 ≤ m) (hw : 0 < w_r) (leaf : Fin m ↪ V_fin)
    {M_pol : Matrix (Fin m) (Fin m) (ZMod 2)} {e_defic c_edge slack : ℝ}
    (hc_edge : 0 < c_edge)
    (hbis_M : ∀ U : Set (Fin m), U.ncard = m / 2 → ((m / 2 : ℕ) : ℝ) ≤ M_pol.cutRank U + e_defic)
    (hcr_le : ∀ P : Set V_fin,
      (M_pol.cutRank {j | leaf j ∈ P} : ℝ) ≤ c_edge * (G.edgeCut P).ncard + slack)
    (hρ_comp : ∀ Comp : Set V_fin, G.edgeCut Comp = ∅ → Comp.ncard ≤ (G.touching Comp).ncard + 1 →
      w_r * (G.cycleRankOn Comp : ℝ) + ({j : Fin m | leaf j ∈ Comp}.ncard : ℝ) ≤
        w_r * ((s : ℝ) + 1))
    (hsmall_slack : 4 * (slack + e_defic) + 4 ≤ (m : ℝ)) :
    w_r * ((m : ℝ) / 2 - 1 - (slack + e_defic)) ≤
      c_edge * ((A + η) * (w_r * ((s : ℝ) + 1) - m + (slack + e_defic)) +
        w_r * η * Nat.card V_fin + w_r * C_lay) := by
  obtain ⟨t, ht_lt, hXt⟩ := exists_bisection_step hm leaf lay
  have hclosed_dich (Qset : Set V_fin) (hQ : G.edgeCut Qset = ∅) :
      ({j | leaf j ∈ Qset}.ncard : ℝ) ≤ slack + e_defic ∨
        (m : ℝ) - (slack + e_defic) ≤ ({j | leaf j ∈ Qset}.ncard : ℝ) := by
    have hsmall_side (Pset : Set V_fin) (hP : G.edgeCut Pset = ∅)
        (hPhalf : {j | leaf j ∈ Pset}.ncard ≤ m / 2) :
        ({j | leaf j ∈ Pset}.ncard : ℝ) ≤ slack + e_defic := by
      have hcrP := hcr_le Pset
      rw [hP, ncard_empty, Nat.cast_zero, mul_zero, zero_add] at hcrP
      have hbis := ncard_le_cutRank_add_of_bisection hbis_M hPhalf
      linarith
    by_cases hh : {j | leaf j ∈ Qset}.ncard ≤ m / 2
    · exact Or.inl (hsmall_side Qset hQ hh)
    · refine Or.inr ?_
      have hQc_cut : G.edgeCut Qsetᶜ = ∅ :=
        G.edgeCut_eq_empty_iff.mpr fun e' => not_iff_not.mpr (G.edgeCut_eq_empty_iff.mp hQ e')
      have hcompl_set : {j | leaf j ∈ Qsetᶜ} = {j | leaf j ∈ Qset}ᶜ := rfl
      have hsum_m : {j | leaf j ∈ Qset}.ncard + {j | leaf j ∈ Qsetᶜ}.ncard = m := by
        rw [hcompl_set]
        have := ncard_add_ncard_compl {j | leaf j ∈ Qset}
        rwa [Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at this
      have hsum_r : ({j | leaf j ∈ Qset}.ncard : ℝ) + ({j | leaf j ∈ Qsetᶜ}.ncard : ℝ) = m := by
        exact_mod_cast hsum_m
      have hh' : {j | leaf j ∈ Qsetᶜ}.ncard ≤ m / 2 := by omega
      linarith [hsmall_side Qsetᶜ hQc_cut hh']
  set W := G.component (lay.symm ⟨t, ht_lt⟩)
  have hW_cut : G.edgeCut W = ∅ := G.edgeCut_component _
  obtain ⟨hfront_W, hfront_le⟩ := hlay t ht_lt
  have hm_div2_lb : (m : ℝ) / 2 - 1 ≤ ((m / 2 : ℕ) : ℝ) := by
    have h1 : m ≤ 2 * (m / 2) + 1 := by omega
    have hr : (m : ℝ) ≤ (2 * (m / 2) + 1 : ℕ) := by exact_mod_cast h1
    push_cast at hr; linarith
  have hm_div2_ub : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
    have h1 : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
    have hr : ((2 * (m / 2) : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr h1
    push_cast at hr; linarith
  have hW_large : (m : ℝ) - (slack + e_defic) ≤ ({j | leaf j ∈ W}.ncard : ℝ) := by
    rcases hclosed_dich W hW_cut with hWs | hWb
    · exfalso
      set Bset := lay.initial t \ W
      have hB_cut : G.edgeCut Bset = ∅ := Multigraph.edgeCut_sdiff_eq_empty hW_cut hfront_W
      have hB_sub : {j | leaf j ∈ Bset} ⊆ {j | leaf j ∈ lay.initial t} := fun _ hj => hj.1
      have hinit_sub : {j | leaf j ∈ lay.initial t} ⊆
          {j | leaf j ∈ Bset} ∪ {j | leaf j ∈ W} := by
        intro j hj
        by_cases hjW : leaf j ∈ W
        · exact Or.inr hjW
        · exact Or.inl ⟨hj, hjW⟩
      have hB_le : {j | leaf j ∈ Bset}.ncard ≤ m / 2 :=
        (ncard_le_ncard hB_sub (toFinite _)).trans_eq hXt
      have hB_ge : m / 2 ≤ {j | leaf j ∈ Bset}.ncard + {j | leaf j ∈ W}.ncard :=
        hXt ▸ (ncard_le_ncard hinit_sub (toFinite _)).trans (ncard_union_le _ _)
      have hB_ge_r : ((m / 2 : ℕ) : ℝ) ≤
          ({j | leaf j ∈ Bset}.ncard : ℝ) + ({j | leaf j ∈ W}.ncard : ℝ) := by
        exact_mod_cast hB_ge
      have hB_le_r : ({j | leaf j ∈ Bset}.ncard : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by
        exact_mod_cast hB_le
      rcases hclosed_dich Bset hB_cut with hBs | hBl <;> linarith
    · exact hWb
  have hρ_W := hρ_comp W hW_cut (G.ncard_component_le_ncard_touching_add_one _)
  have hw_ρ_le : w_r * (G.cycleRankOn W : ℝ) ≤ w_r * ((s : ℝ) + 1) - m + (slack + e_defic) := by
    linarith
  have hw_front_le : w_r * ((G.frontier lay t).ncard : ℝ) ≤
      (A + η) * (w_r * ((s : ℝ) + 1) - m + (slack + e_defic)) +
        w_r * η * Nat.card V_fin + w_r * C_lay := by
    have hmul := mul_le_mul_of_nonneg_left hfront_le hw.le
    have hmul_ρ := mul_le_mul_of_nonneg_left hw_ρ_le hAη
    linarith
  have hcr_t := hcr_le (lay.initial t)
  change _ ≤ c_edge * ((G.frontier lay t).ncard : ℝ) + slack at hcr_t
  have hbis_t := hbis_M {j | leaf j ∈ lay.initial t} hXt
  have hdem : (m : ℝ) / 2 - 1 - (slack + e_defic) ≤ c_edge * ((G.frontier lay t).ncard : ℝ) := by
    linarith
  have hw_dem := mul_le_mul_of_nonneg_left hdem hw.le
  have hcw := mul_le_mul_of_nonneg_left hw_front_le hc_edge.le
  linarith

/-- Pure real arithmetic contradiction combining `finite_bisection_supply_demand` with sublinear
error and slack bounds when `s ≤ (1 + w_r / (2 * c_edge * A) - ε₀) * n`. -/
private theorem step_contradiction_of_supply_demand {A η C_lay w_r c_edge ε₀ n_r s_r V_r
    γ_coeff sub_err : ℝ}
    (hA : 0 < A) (_hη_pos : 0 < η) (hη_le_A : η ≤ A) (hw : 1 ≤ w_r) (hc_edge : 0 < c_edge)
    (hε₀ : 0 < ε₀) (hn : 24 ≤ n_r) (_hs_nn : 0 ≤ s_r) (hγ_nn : 0 ≤ γ_coeff) (hsub_nn : 0 ≤ sub_err)
    (hsize : s_r ≤ (1 + w_r / (2 * c_edge * A) - ε₀) * n_r)
    (hV : V_r ≤ 2 * n_r + 6 * s_r + 2)
    (hη_bound : η * (7 * (1 + w_r / (2 * c_edge * A)) + 3) ≤ A * ε₀ / 4)
    (hγ_bound : (w_r + 2 * c_edge * A) * γ_coeff ≤ w_r * c_edge * A * ε₀ / 4)
    (herr_bound : (w_r + 2 * c_edge * A) * sub_err +
      w_r + c_edge * (2 * A * w_r + w_r * |C_lay|) ≤ w_r * c_edge * A * ε₀ / 4 * n_r)
    (hfin : w_r * (w_r * n_r / 2 - 1 - (γ_coeff * n_r + sub_err)) ≤
      c_edge * ((A + η) * (w_r * (s_r + 1) - w_r * n_r + (γ_coeff * n_r + sub_err)) +
        w_r * η * V_r + w_r * C_lay)) : False := by
  set c_star := 1 + w_r / (2 * c_edge * A)
  have hc_star_pos : 1 < c_star := by
    have : 0 < w_r / (2 * c_edge * A) := by positivity
    linarith
  have hs_ub : s_r ≤ c_star * n_r := by nlinarith
  have hmain : c_edge * A * (w_r * (s_r - n_r)) ≤
      w_r * (w_r * n_r / 2) - w_r * c_edge * A * ε₀ * n_r := by
    have h1 : s_r - n_r ≤ (w_r / (2 * c_edge * A) - ε₀) * n_r := by
      dsimp only [c_star] at hsize; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ c_edge * A * w_r)
    have h3 : c_edge * A * w_r * ((w_r / (2 * c_edge * A) - ε₀) * n_r) =
        w_r * (w_r * n_r / 2) - w_r * c_edge * A * ε₀ * n_r := by
      field_simp
    linarith
  have hη_term : c_edge * η * (w_r * (s_r - n_r + V_r)) ≤ w_r * c_edge * A * ε₀ / 4 * n_r := by
    have hsum_ub : s_r - n_r + V_r ≤ (7 * c_star + 3) * n_r := by linarith
    have h1 := mul_le_mul_of_nonneg_left hsum_ub (by positivity : 0 ≤ c_edge * w_r * η)
    have h2 := mul_le_mul_of_nonneg_left hη_bound (by positivity : 0 ≤ c_edge * w_r * n_r)
    nlinarith
  have hslack_coef : w_r + c_edge * (A + η) ≤ w_r + 2 * c_edge * A := by
    have := mul_le_mul_of_nonneg_left hη_le_A hc_edge.le
    linarith
  have hγ_term : (w_r + c_edge * (A + η)) * (γ_coeff * n_r) ≤
      w_r * c_edge * A * ε₀ / 4 * n_r := by
    have h1 : (w_r + c_edge * (A + η)) * (γ_coeff * n_r) ≤
        (w_r + 2 * c_edge * A) * (γ_coeff * n_r) :=
      mul_le_mul_of_nonneg_right hslack_coef (mul_nonneg hγ_nn (by linarith : 0 ≤ n_r))
    have h2 := mul_le_mul_of_nonneg_right hγ_bound (by linarith : 0 ≤ n_r)
    linarith
  have hsub_term : (w_r + c_edge * (A + η)) * sub_err +
      w_r + c_edge * ((A + η) * w_r + w_r * C_lay) ≤
      w_r * c_edge * A * ε₀ / 4 * n_r := by
    have h1 := mul_le_mul_of_nonneg_right hslack_coef hsub_nn
    have h2 : c_edge * ((A + η) * w_r + w_r * C_lay) ≤
        c_edge * (2 * A * w_r + w_r * |C_lay|) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right (by linarith : A + η ≤ 2 * A)
            (by linarith : 0 ≤ w_r))
          (mul_le_mul_of_nonneg_left (le_abs_self C_lay) (by linarith : 0 ≤ w_r))) hc_edge.le
    linarith
  have hpos_gap : 0 < w_r * c_edge * A * ε₀ / 4 * n_r := by positivity
  linarith

/-- Common asymptotic helper: `4 * (2 * ⌊√n⌋ + 1) + 6 = o(n)`. -/
private theorem isLittleO_sqrt_defic :
    (fun n : ℕ => ((4 * (2 * Nat.sqrt n + 1) + 6 : ℕ) : ℝ)) =o[atTop] fun n => (n : ℝ) := by
  rw [isLittleO_iff]
  intro δ hδ
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop ((16 / δ) ^ 2 + 20 / δ))] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsqrt : (Nat.sqrt n : ℝ) ≤ √n := Real.nat_sqrt_le_real_sqrt
  have hss : √n * √n = n := Real.mul_self_sqrt hn0
  have h20 : 0 ≤ 20 / δ := by positivity
  have hroot : 16 / δ ≤ √n := Real.le_sqrt_of_sq_le (by linarith)
  have h8 : 8 * √n ≤ δ / 2 * n := by
    have hm := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ δ / 2 * √n)
    have e1 : δ / 2 * √n * (16 / δ) = 8 * √n := by field_simp; ring
    have e2 : δ / 2 * √n * √n = δ / 2 * n := by rw [mul_assoc, hss]
    linarith
  have h10 : 10 ≤ δ / 2 * n := by
    have : 20 / δ * δ = 20 := by field_simp
    nlinarith [sq_nonneg (16 / δ)]
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  push_cast
  linarith

/-! #### 1. `BQP` single-qubit measurement correlation decay (`1.893993 n` / `1.625 n`) -/

/-- **`BQP` correlation decay with `hardForm n` under `LayoutBound d A` (`d ∈ {3, 4}`).**
For any `ε > 0`, there is `γ > 0` such that for all large `n`, every quantum circuit `C` on ANY
number of qubits `N` (with unlimited ancillas and unlimited `0`/`1`-qubit `U(2)` gates) whose
two-qubit gates have degree model `d` (`AllBondRankTwo C` for `d = 3`, or `TwoLocal C` for `d = 4`)
and satisfy `twoQubitCount C ≤ (1 + 1 / (4 A) - ε) n` has single-qubit measurement correlation at
most `2 ^ (-γ n)` with the nonconstructively chosen bilinear form `hardForm n`. -/
theorem eventually_abs_quantumCorrelation_hardForm_le_of_layoutBound {d : ℕ} (hd : d = 3 ∨ d = 4)
    {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound d A) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (C : Quantum.Circuit N),
      (if d = 3 then AllBondRankTwo C else TwoLocal C) →
      (twoQubitCount C : ℝ) ≤ (1 + 1 / (4 * A) - ε) * n →
        |quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀)| ≤
          (2 : ℝ) ^ (-γ * n) := by
  set ε₀ := min ε (1 / (4 * A))
  have hε₀ : 0 < ε₀ := lt_min hε (by positivity)
  set γ : ℝ := 2 * A * ε₀ / (8 * (1 + 4 * A))
  have hγ : 0 < γ := by positivity
  refine ⟨γ, hγ, ?_⟩
  set Bcoef : ℝ := 7 * (1 + 1 / (4 * A)) + 3
  set η : ℝ := min A (A * ε₀ / (4 * Bcoef))
  have hη : 0 < η := lt_min hA (by positivity)
  obtain ⟨C_lay, hC_lay⟩ := hlayout.exists_layout_componentwise hη
  set defic : ℕ → ℕ := fun n => 4 * (2 * Nat.sqrt n + 1) + 6
  have herr_o : (fun n : ℕ => (1 + 4 * A) * (defic n : ℝ) +
      (1 + 2 * (2 * A + |C_lay|))) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_sqrt_defic.const_mul_left _).add (isLittleO_const_id_atTop _).natCast_atTop
  have hsmall_d : ∀ᶠ n : ℕ in atTop, 24 ≤ n ∧ 4 * (defic n : ℝ) + 4 ≤ 1 / 2 * n := by
    filter_upwards [isLittleO_sqrt_defic.bound (by norm_num : (0 : ℝ) < 1 / 16),
      eventually_ge_atTop 24] with n hn hn24
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hn
    have hd1 : (defic n : ℝ) ≤ 1 / 16 * n := by linarith [le_abs_self (defic n : ℝ)]
    have hn24' : (24 : ℝ) ≤ n := by exact_mod_cast hn24
    exact ⟨hn24, by linarith⟩
  filter_upwards [herr_o.bound (show (0 : ℝ) < 2 * A * ε₀ / 4 by positivity), hsmall_d]
    with n herrn ⟨hn24, hdn⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herrn
  intro N e q_out x₀ C hmodel hsize_orig
  have hsize : (twoQubitCount C : ℝ) ≤ (1 + 1 / (2 * 2 * A) - ε₀) * n := by
    have h1 : 1 + 1 / (4 * A) - ε ≤ 1 + 1 / (2 * 2 * A) - ε₀ := by
      have heq : (1 : ℝ) / (2 * 2 * A) = 1 / (4 * A) := by ring
      linarith [min_le_left ε (1 / (4 * A))]
    exact hsize_orig.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n))
  obtain ⟨net⟩ := exists_compiledQuantumNet hd e q_out hmodel
  obtain ⟨lay, hlay⟩ := hC_lay net.V net.E net.G net.loopless net.maxDeg
  by_contra! hcorr_gt
  have hcorr_sq_gt : (2 : ℝ) ^ (-(2 * γ) * n) <
      quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀) ^ 2 := by
    have h1 := pow_lt_pow_left₀ hcorr_gt (by positivity) (n := 2) (by norm_num)
    rw [sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul two_pos.le] at h1
    push_cast at h1
    convert h1 using 2; ring
  have hcr_bound (P : Set net.V) :
      ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafIn i ∈ P} : ℝ) ≤
        2 * ((net.G.edgeCut P).ncard : ℝ) + (2 * γ * n + 2) := by
    have h1 := net.sq_quantumCorrelation_mul_le x₀ (hardMatrix n) P
    have hlt : (2 : ℝ) ^ (-(2 * γ) * n) *
        (2 : ℝ) ^ ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafIn i ∈ P} : ℝ) <
        4 * (4 : ℝ) ^ ((net.G.edgeCut P).ncard : ℝ) := by
      rw [Real.rpow_natCast, Real.rpow_natCast]
      exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hcorr_sq_gt (by positivity)) h1
    have hlhs : (2 : ℝ) ^ (-(2 * γ) * n +
        ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafIn i ∈ P} : ℝ)) =
        (2 : ℝ) ^ (-(2 * γ) * n) *
          (2 : ℝ) ^ ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafIn i ∈ P} : ℝ) :=
      Real.rpow_add two_pos _ _
    have hrhs : (4 : ℝ) * (4 : ℝ) ^ ((net.G.edgeCut P).ncard : ℝ) =
        (2 : ℝ) ^ (2 + 2 * ((net.G.edgeCut P).ncard : ℝ)) := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h4, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos]
    rw [← hlhs, hrhs] at hlt
    linarith [(Real.rpow_lt_rpow_left_iff one_lt_two).mp hlt]
  set e_def : ℝ := ((2 * (2 * Nat.sqrt (n / 2) + 1) + 1 : ℕ) : ℝ)
  have he_add_le : 2 + e_def ≤ (defic n : ℝ) := by
    have hs_le : Nat.sqrt (n / 2) ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (Nat.div_le_self n 2)
    have hnat : 2 + (2 * (2 * Nat.sqrt (n / 2) + 1) + 1) ≤ defic n := by dsimp only [defic]; omega
    dsimp only [e_def]
    exact_mod_cast hnat
  have h2γ_le : 2 * γ ≤ 1 / 8 := by
    have hε0_le : ε₀ ≤ 1 / (4 * A) := min_le_right _ _
    have hAε : 2 * A * ε₀ ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hε0_le (by positivity : (0 : ℝ) ≤ 2 * A)
      have heq : 2 * A * (1 / (4 * A)) = 1 / 2 := by field_simp; norm_num
      linarith
    calc 2 * γ = (2 * A * ε₀) / (4 * (1 + 4 * A)) := by dsimp only [γ]; field_simp; ring
      _ ≤ (1 / 2) / (4 * 1) := div_le_div₀ (by norm_num) hAε (by norm_num) (by linarith)
      _ = 1 / 8 := by norm_num
  have hfin := finite_bisection_supply_demand (e_defic := e_def) net.G lay (by positivity)
    (fun t ht => hlay t ht t le_rfl (by omega)) (by omega) one_pos net.leafIn (by norm_num)
    (fun U hU => by dsimp only [e_def]; exact_mod_cast half_le_cutRank_hardMatrix n hU) hcr_bound
    (fun Comp hcut hconn => by
      have hr : (net.G.cycleRankOn Comp : ℝ) + ({i | net.leafIn i ∈ Comp}.ncard : ℝ) ≤
          (twoQubitCount C : ℝ) + 1 := by exact_mod_cast net.cycleRank_leafIn_le Comp hcut hconn
      linarith)
    (by
      have h2γn : 4 * (2 * γ * n) ≤ 1 / 2 * n := by
        have := mul_le_mul_of_nonneg_right h2γ_le (Nat.cast_nonneg (α := ℝ) n)
        linarith
      linarith)
  exact step_contradiction_of_supply_demand (C_lay := C_lay) (w_r := 1) (c_edge := 2)
    (γ_coeff := 2 * γ) (sub_err := 2 + e_def)
    hA hη (min_le_left _ _) le_rfl (by norm_num) hε₀ (by exact_mod_cast hn24) (Nat.cast_nonneg _)
    (by positivity) (by positivity)
    (by convert hsize using 2) net.card_V_le
    (by
      have h1 : η ≤ A * ε₀ / (4 * Bcoef) := min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ Bcoef)
      have h3 : A * ε₀ / (4 * Bcoef) * Bcoef = A * ε₀ / 4 := by
        have hB : 0 < Bcoef := by dsimp only [Bcoef]; positivity
        field_simp
      have hBeq : 7 * (1 + (1 : ℝ) / (2 * 2 * A)) + 3 = Bcoef := by dsimp only [Bcoef]; ring
      rw [hBeq]
      linarith)
    (by
      have heq : (1 + 2 * 2 * A) * (2 * γ) = 1 * 2 * A * ε₀ / 4 := by
        dsimp only [γ]; field_simp; ring
      linarith)
    (by
      have hsub : (1 + 2 * 2 * A) * (2 + e_def) ≤ (1 + 4 * A) * (defic n : ℝ) := by
        have := mul_le_mul_of_nonneg_left he_add_le (by positivity : (0 : ℝ) ≤ 1 + 4 * A)
        linarith
      have herr_le := le_trans (le_abs_self _) herrn
      linarith)
    (by convert hfin using 2 <;> ring)

/-- **Median-switched `BQP` correlation decay (`1.893993 n`).** Below
`(1 + π / (6 arccos (5 / 6)) - ε) n ≈ 1.893993 n` bond-rank-two two-qubit gates (with unlimited
ancillas `N` and unlimited single-qubit `U(2)` gates), single-qubit measurement correlation with
`hardForm n` decays exponentially as `2 ^ (-γ n)`. -/
theorem eventually_abs_quantumCorrelation_hardForm_le_switched {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (C : Quantum.Circuit N),
      AllBondRankTwo C →
      (twoQubitCount C : ℝ) ≤ (1 + π / (6 * arccos (5 / 6)) - ε) * n →
        |quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀)| ≤
          (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_abs_quantumCorrelation_hardForm_le_of_layoutBound (Or.inl rfl)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hε
  have hcoef : 1 + 1 / (4 * (2 * Switched.switchedCoefficient)) =
      1 + π / (6 * arccos (5 / 6)) := by
    have h1 := Switched.one_add_inv_two_mul_switchedCoefficient
    have h2 : 1 / (2 * Switched.switchedCoefficient) = 2 * π / (3 * arccos (5 / 6)) := by linarith
    have h3 : 1 / (4 * (2 * Switched.switchedCoefficient)) =
        1 / (2 * Switched.switchedCoefficient) / 4 := by field_simp
    rw [h3, h2]; ring
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn N e q_out x₀ C hbond hsize
  exact hn N e q_out x₀ C (by simpa) (by rwa [hcoef])

/-- **Rational `(1.89399 - ε) n` `BQP` correlation decay** with `hardForm n`. -/
theorem eventually_abs_quantumCorrelation_hardForm_le_189399 {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (C : Quantum.Circuit N),
      AllBondRankTwo C →
      (twoQubitCount C : ℝ) ≤ (189399 / 100000 - ε) * n →
        |quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀)| ≤
          (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_abs_quantumCorrelation_hardForm_le_switched hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn N e q_out x₀ C hbond hsize
  refine hn N e q_out x₀ C hbond (hsize.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n)))
  have h45 := Switched.circuitCoefficient_ge_457597
  have hdiv : π / (6 * arccos (5 / 6)) = (2 * π / (3 * arccos (5 / 6))) / 4 := by ring
  linarith

/-- **Bounded-error `BQP` decision lower bound (`1.893993 n`).** Any bond-rank-two quantum circuit
`C` deciding `hardForm n` with acceptance probability `≥ 2 / 3` on `true` inputs and `≤ 1 / 3` on
`false` inputs requires more than `(1 + π / (6 arccos (5 / 6)) - ε) n` two-qubit gates. -/
theorem eventually_lt_twoQubitCount_bqp_hardForm_switched {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (∀ x, if hardForm n x then 2 / 3 ≤ quantumAcceptProb C q_out e x₀ x
        else quantumAcceptProb C q_out e x₀ x ≤ 1 / 3) →
        (1 + π / (6 * arccos (5 / 6)) - ε) * n < twoQubitCount C := by
  obtain ⟨γ, hγ, hev⟩ := eventually_abs_quantumCorrelation_hardForm_le_switched hε
  have hpow_lt : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (-γ * n) < 1 / 3 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (2 / γ))] with n hn
    have h1 : γ * (2 / γ) = 2 := by field_simp
    have h2 : -γ * (n : ℝ) ≤ -2 := by
      have hm := mul_le_mul_of_nonneg_left hn hγ.le
      linarith
    calc (2 : ℝ) ^ (-γ * (n : ℝ))
        ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_lt_two.le h2
      _ < 1 / 3 := by norm_num
  filter_upwards [hev, hpow_lt] with n hn hlt N e q_out x₀ C hbond hbqp
  by_contra! hsize
  have hub := hn N e q_out x₀ C hbond hsize
  have hpt (y : Fin n → Bool) :
      (1 / 3 : ℝ) ≤ (if y ∈ {x | hardForm n x} then (1 : ℝ) else -1) *
        (2 * quantumAcceptProb C q_out e x₀ y - 1) := by
    have hy := hbqp y
    simp only [mem_ofPred_eq]
    by_cases hf : hardForm n y = true
    · simp only [hf, ↓reduceIte] at hy ⊢; linarith
    · simp only [Bool.not_eq_true] at hf
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hy ⊢; linarith
  have hcorr_ge :
      1 / 3 ≤ quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀) := by
    rw [quantumCorrelation, le_div_iff₀ (by positivity)]
    calc (1 / 3 : ℝ) * (2 : ℝ) ^ n
        = ∑ _y : Fin n → Bool, (1 / 3 : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
            ring
      _ ≤ ∑ y : Fin n → Bool,
            (if y ∈ {x | hardForm n x} then (1 : ℝ) else -1) *
              (2 * quantumAcceptProb C q_out e x₀ y - 1) :=
          Finset.sum_le_sum fun y _ => hpt y
      _ = _ := Finset.sum_congr rfl fun y _ => by split_ifs <;> rfl
  linarith [le_abs_self (quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀))]

/-- **Unconditional general two-local `U(4)` `BQP` correlation decay (`(13 / 8 - ε) n = 1.625 n`)**
via `layoutBound_two_fifths_four` (`A₄ = 2 / 5`). -/
theorem eventually_abs_quantumCorrelation_hardForm_le_twoLocal_two_fifths {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (C : Quantum.Circuit N),
      TwoLocal C →
      (twoQubitCount C : ℝ) ≤ (13 / 8 - ε) * n →
        |quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀)| ≤
          (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_abs_quantumCorrelation_hardForm_le_of_layoutBound (Or.inr rfl)
    (by norm_num) layoutBound_two_fifths_four hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn N e q_out x₀ C htwo hsize
  exact hn N e q_out x₀ C (by simpa) (by convert hsize using 2; norm_num)

/-- **General two-local `U(4)` `BQP` correlation decay (`(7 / 4 - ε) n = 1.75 n`)** under
`LayoutBound 4 (1 / 3)`. -/
theorem eventually_abs_quantumCorrelation_hardForm_le_twoLocal_one_third
    (h4 : LayoutBound 4 (1 / 3)) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (C : Quantum.Circuit N),
      TwoLocal C →
      (twoQubitCount C : ℝ) ≤ (7 / 4 - ε) * n →
        |quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀)| ≤
          (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_abs_quantumCorrelation_hardForm_le_of_layoutBound (Or.inr rfl)
    (by norm_num) h4 hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn N e q_out x₀ C htwo hsize
  exact hn N e q_out x₀ C (by simpa) (by convert hsize using 2; norm_num)

/-! #### 2. `UQP` unbounded-error sign-rank bounds (`1.446996 n` / `1.3125 n` / `1.375 n`) -/

/-- **`UQP` unbounded-error lower bound on `hardForm n` under `LayoutBound d A` (`d ∈ {3, 4}`).**
Every quantum circuit `C` deciding `hardForm n` with strict threshold `θ` (`θ < prob x` on `true`,
`prob x < θ` on `false`, with arbitrarily small margin!) requires more than
`(1 + 1 / (8 A) - ε) n` two-qubit gates. -/
theorem eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound {d : ℕ} (hd : d = 3 ∨ d = 4)
    {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound d A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (θ : ℝ)
      (C : Quantum.Circuit N),
      (if d = 3 then AllBondRankTwo C else TwoLocal C) →
      (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
        else quantumAcceptProb C q_out e x₀ x < θ) →
        (1 + 1 / (8 * A) - ε) * n < twoQubitCount C := by
  set ε₀ := min ε (1 / (8 * A))
  have hε₀ : 0 < ε₀ := lt_min hε (by positivity)
  set Bcoef : ℝ := 7 * (1 + 1 / (8 * A)) + 3
  set η : ℝ := min A (A * ε₀ / (4 * Bcoef))
  have hη : 0 < η := lt_min hA (by positivity)
  obtain ⟨C_lay, hC_lay⟩ := hlayout.exists_layout_componentwise hη
  set defic : ℕ → ℕ := fun n => 4 * (2 * Nat.sqrt n + 1) + 6
  have herr_o : (fun n : ℕ => (1 + 8 * A) * (defic n : ℝ) +
      (1 + 4 * (2 * A + |C_lay|))) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_sqrt_defic.const_mul_left _).add (isLittleO_const_id_atTop _).natCast_atTop
  have hsmall_d : ∀ᶠ n : ℕ in atTop, 24 ≤ n ∧ 4 * (defic n : ℝ) + 4 ≤ n := by
    filter_upwards [isLittleO_sqrt_defic.bound (by norm_num : (0 : ℝ) < 1 / 8),
      eventually_ge_atTop 24] with n hn hn24
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hn
    have hd1 : (defic n : ℝ) ≤ 1 / 8 * n := by linarith [le_abs_self (defic n : ℝ)]
    have hn24' : (24 : ℝ) ≤ n := by exact_mod_cast hn24
    exact ⟨hn24, by linarith⟩
  filter_upwards [herr_o.bound (show (0 : ℝ) < 4 * A * ε₀ / 4 by positivity), hsmall_d]
    with n herrn ⟨hn24, hdn⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herrn
  intro N e q_out x₀ θ C hmodel huqp
  by_contra! hsize_orig
  have hsize : (twoQubitCount C : ℝ) ≤ (1 + 1 / (2 * 4 * A) - ε₀) * n := by
    have h1 : 1 + 1 / (8 * A) - ε ≤ 1 + 1 / (2 * 4 * A) - ε₀ := by
      have heq : (1 : ℝ) / (2 * 4 * A) = 1 / (8 * A) := by ring
      linarith [min_le_left ε (1 / (8 * A))]
    exact hsize_orig.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n))
  classical
  obtain ⟨net⟩ := exists_compiledQuantumNet hd e q_out hmodel
  obtain ⟨lay, hlay⟩ := hC_lay net.V net.E net.G net.loopless net.maxDeg
  have hcr_bound (P : Set net.V) :
      ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafIn i ∈ P} : ℝ) ≤
        4 * ((net.G.edgeCut P).ncard : ℝ) + 4 := by
    have hsr_up := net.signRank_uqp_le x₀ huqp P
    change Communication.signRank
      (fun a b => BitString.quadForm (hardMatrix n)
        ((Equiv.piEquivPiSubtypeProd (· ∈ {i | net.leafIn i ∈ P}) fun _ => Bool).symm (a, b))) ≤
      3 * 4 ^ (net.G.edgeCut P).ncard at hsr_up
    have hsr_lo := Communication.two_pow_cutRank_le_signRank_quadForm_sq
      (hardMatrix n) {i | net.leafIn i ∈ P}
    have hpow : 2 ^ (hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafIn i ∈ P} ≤
        2 ^ (4 * (net.G.edgeCut P).ncard + 4) := by
      calc 2 ^ (hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafIn i ∈ P}
          ≤ (3 * 4 ^ (net.G.edgeCut P).ncard) ^ 2 := hsr_lo.trans (Nat.pow_le_pow_left hsr_up 2)
        _ = 9 * 2 ^ (4 * (net.G.edgeCut P).ncard) := by
            have h4 : 4 ^ (net.G.edgeCut P).ncard = 2 ^ (2 * (net.G.edgeCut P).ncard) := by
              rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
            rw [mul_pow, h4, ← pow_mul]
            ring
        _ ≤ 2 ^ 4 * 2 ^ (4 * (net.G.edgeCut P).ncard) := Nat.mul_le_mul_right _ (by norm_num)
        _ = 2 ^ (4 * (net.G.edgeCut P).ncard + 4) := by rw [← pow_add, add_comm]
    have hnat : (hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafIn i ∈ P} ≤
        4 * (net.G.edgeCut P).ncard + 4 := by
      by_contra! hgt
      have := Nat.pow_lt_pow_right one_lt_two hgt
      omega
    exact_mod_cast hnat
  set e_def : ℝ := ((2 * (2 * Nat.sqrt (n / 2) + 1) + 1 : ℕ) : ℝ)
  have he_add_le : 4 + e_def ≤ (defic n : ℝ) := by
    have hs_le : Nat.sqrt (n / 2) ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (Nat.div_le_self n 2)
    have hnat : 4 + (2 * (2 * Nat.sqrt (n / 2) + 1) + 1) ≤ defic n := by dsimp only [defic]; omega
    dsimp only [e_def]
    exact_mod_cast hnat
  have hfin := finite_bisection_supply_demand (e_defic := e_def) net.G lay (by positivity)
    (fun t ht => hlay t ht t le_rfl (by omega)) (by omega) one_pos net.leafIn (by norm_num)
    (fun U hU => by dsimp only [e_def]; exact_mod_cast half_le_cutRank_hardMatrix n hU) hcr_bound
    (fun Comp hcut hconn => by
      have hr : (net.G.cycleRankOn Comp : ℝ) + ({i | net.leafIn i ∈ Comp}.ncard : ℝ) ≤
          (twoQubitCount C : ℝ) + 1 := by exact_mod_cast net.cycleRank_leafIn_le Comp hcut hconn
      linarith)
    (by linarith)
  exact step_contradiction_of_supply_demand (C_lay := C_lay) (w_r := 1) (c_edge := 4)
    (γ_coeff := 0) (sub_err := 4 + e_def)
    hA hη (min_le_left _ _) le_rfl (by norm_num) hε₀ (by exact_mod_cast hn24) (Nat.cast_nonneg _)
    le_rfl (by positivity)
    hsize net.card_V_le
    (by
      have h1 : η ≤ A * ε₀ / (4 * Bcoef) := min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ Bcoef)
      have h3 : A * ε₀ / (4 * Bcoef) * Bcoef = A * ε₀ / 4 := by
        have hB : 0 < Bcoef := by dsimp only [Bcoef]; positivity
        field_simp
      have hBeq : 7 * (1 + (1 : ℝ) / (2 * 4 * A)) + 3 = Bcoef := by dsimp only [Bcoef]; ring
      rw [hBeq]; linarith)
    (by rw [mul_zero]; positivity)
    (by
      have hsub : (1 + 2 * 4 * A) * (4 + e_def) ≤ (1 + 8 * A) * (defic n : ℝ) := by
        have := mul_le_mul_of_nonneg_left he_add_le (by positivity : (0 : ℝ) ≤ 1 + 8 * A)
        linarith
      have herr_le := le_trans (le_abs_self _) herrn
      linarith)
    (by convert hfin using 2 <;> ring)

/-- **Median-switched `UQP` unbounded-error lower bound (`1.446996 n`).** -/
theorem eventually_lt_twoQubitCount_uqp_hardForm_switched {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (θ : ℝ)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
        else quantumAcceptProb C q_out e x₀ x < θ) →
        (1 + π / (12 * arccos (5 / 6)) - ε) * n < twoQubitCount C := by
  have hev := eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound (Or.inl rfl)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hε
  have hcoef : 1 + 1 / (8 * (2 * Switched.switchedCoefficient)) =
      1 + π / (12 * arccos (5 / 6)) := by
    have h1 := Switched.one_add_inv_two_mul_switchedCoefficient
    have h2 : 1 / (2 * Switched.switchedCoefficient) = 2 * π / (3 * arccos (5 / 6)) := by linarith
    have h3 : 1 / (8 * (2 * Switched.switchedCoefficient)) =
        1 / (2 * Switched.switchedCoefficient) / 8 := by field_simp
    rw [h3, h2]; ring
  filter_upwards [hev] with n hn N e q_out x₀ θ C hbond huqp
  rw [← hcoef]
  exact hn N e q_out x₀ θ C (by simpa) huqp

/-- **Rational `(1.44699 - ε) n` `UQP` unbounded-error lower bound** on `hardForm n`. -/
theorem eventually_lt_twoQubitCount_uqp_hardForm_144699 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (θ : ℝ)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
        else quantumAcceptProb C q_out e x₀ x < θ) →
        (144699 / 100000 - ε) * n < twoQubitCount C := by
  filter_upwards [eventually_lt_twoQubitCount_uqp_hardForm_switched hε]
    with n hn N e q_out x₀ θ C hbond huqp
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n))
    (hn N e q_out x₀ θ C hbond huqp)
  have h45 := Switched.circuitCoefficient_ge_457597
  have hdiv : π / (12 * arccos (5 / 6)) = (2 * π / (3 * arccos (5 / 6))) / 8 := by ring
  linarith

/-- **Unconditional general two-local `U(4)` `UQP` lower bound (`(21 / 16 - ε) n = 1.3125 n`).** -/
theorem eventually_lt_twoQubitCount_uqp_hardForm_twoLocal_two_fifths {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (θ : ℝ)
      (C : Quantum.Circuit N), TwoLocal C →
      (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
        else quantumAcceptProb C q_out e x₀ x < θ) →
        (21 / 16 - ε) * n < twoQubitCount C := by
  filter_upwards [eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound (Or.inr rfl)
    (by norm_num) layoutBound_two_fifths_four hε] with n hn N e q_out x₀ θ C htwo huqp
  convert hn N e q_out x₀ θ C (by simpa) huqp using 2
  norm_num

/-- **General two-local `U(4)` `UQP` lower bound (`(11 / 8 - ε) n = 1.375 n`)** under
`LayoutBound 4 (1 / 3)`. -/
theorem eventually_lt_twoQubitCount_uqp_hardForm_twoLocal_one_third
    (h4 : LayoutBound 4 (1 / 3)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (θ : ℝ)
      (C : Quantum.Circuit N), TwoLocal C →
      (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
        else quantumAcceptProb C q_out e x₀ x < θ) →
        (11 / 8 - ε) * n < twoQubitCount C := by
  filter_upwards [eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound (Or.inr rfl)
    (by norm_num) h4 hε] with n hn N e q_out x₀ θ C htwo huqp
  convert hn N e q_out x₀ θ C (by simpa) huqp using 2
  norm_num

/-! #### 3. Quadratic phase-state preparation fidelity decay (`2.787986 n` / `2.25 n` / `2.5 n`) -/

/-- **Quadratic phase-state preparation fidelity decay under `LayoutBound d A` (`d ∈ {3, 4}`).**
Below `(1 + 1 / (2 A) - ε) n` two-qubit gates (with unlimited ancillas `N` and unlimited
single-qubit `U(2)` gates), the squared fidelity `‖inner ℂ (phaseState (hardMatrix n) e x₀)
(C.run x₀)‖ ^ 2` decays exponentially as `2 ^ (-γ n)`. -/
theorem eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound {d : ℕ} (hd : d = 3 ∨ d = 4)
    {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound d A) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N),
      (if d = 3 then AllBondRankTwo C else TwoLocal C) →
      (twoQubitCount C : ℝ) ≤ (1 + 1 / (2 * A) - ε) * n →
        ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) := by
  set ε₀ := min ε (1 / (2 * A))
  have hε₀ : 0 < ε₀ := lt_min hε (by positivity)
  set γ : ℝ := A * ε₀ / (4 * (1 + 2 * A))
  have hγ : 0 < γ := by positivity
  refine ⟨γ, hγ, ?_⟩
  set Bcoef : ℝ := 7 * (1 + 1 / (2 * A)) + 3
  set η : ℝ := min A (A * ε₀ / (4 * Bcoef))
  have hη : 0 < η := lt_min hA (by positivity)
  obtain ⟨C_lay, hC_lay⟩ := hlayout.exists_layout_componentwise hη
  set defic : ℕ → ℕ := fun n => 4 * (2 * Nat.sqrt n + 1) + 6
  have herr_o : (fun n : ℕ => (1 + 2 * A) * (defic n : ℝ) +
      (1 + (2 * A + |C_lay|))) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_sqrt_defic.const_mul_left _).add (isLittleO_const_id_atTop _).natCast_atTop
  have hsmall_d : ∀ᶠ n : ℕ in atTop, 24 ≤ n ∧ 4 * (defic n : ℝ) + 4 ≤ 1 / 2 * n := by
    filter_upwards [isLittleO_sqrt_defic.bound (by norm_num : (0 : ℝ) < 1 / 16),
      eventually_ge_atTop 24] with n hn hn24
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hn
    have hd1 : (defic n : ℝ) ≤ 1 / 16 * n := by linarith [le_abs_self (defic n : ℝ)]
    have hn24' : (24 : ℝ) ≤ n := by exact_mod_cast hn24
    exact ⟨hn24, by linarith⟩
  filter_upwards [herr_o.bound (show (0 : ℝ) < A * ε₀ / 4 by positivity), hsmall_d]
    with n herrn ⟨hn24, hdn⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herrn
  intro N e x₀ C hmodel hsize_orig
  have hsize : (twoQubitCount C : ℝ) ≤ (1 + 1 / (2 * 1 * A) - ε₀) * n := by
    have h1 : 1 + 1 / (2 * A) - ε ≤ 1 + 1 / (2 * 1 * A) - ε₀ := by
      have heq : (1 : ℝ) / (2 * 1 * A) = 1 / (2 * A) := by ring
      linarith [min_le_left ε (1 / (2 * A))]
    exact hsize_orig.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n))
  obtain ⟨net⟩ := exists_compiledQuantumNet hd e (e ⟨0, by omega⟩) hmodel
  obtain ⟨lay, hlay⟩ := hC_lay net.V net.E net.G net.loopless net.maxDeg
  by_contra! hfid_gt
  have hcr_bound (P : Set net.V) :
      ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafOut i ∈ P} : ℝ) ≤
        1 * ((net.G.edgeCut P).ncard : ℝ) + (γ * n + 2) := by
    have h1 := net.sq_fidelity_phaseState_mul_le x₀ (hardMatrix n) P
    have hlt : (2 : ℝ) ^ (-γ * n) *
        (2 : ℝ) ^ ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafOut i ∈ P} : ℝ) <
        4 * (2 : ℝ) ^ ((net.G.edgeCut P).ncard : ℝ) := by
      rw [Real.rpow_natCast, Real.rpow_natCast]
      exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hfid_gt (by positivity)) h1
    have hlhs : (2 : ℝ) ^ (-γ * n +
        ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafOut i ∈ P} : ℝ)) =
        (2 : ℝ) ^ (-γ * n) *
          (2 : ℝ) ^ ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | net.leafOut i ∈ P} : ℝ) :=
      Real.rpow_add two_pos _ _
    have hrhs : (4 : ℝ) * (2 : ℝ) ^ ((net.G.edgeCut P).ncard : ℝ) =
        (2 : ℝ) ^ (2 + ((net.G.edgeCut P).ncard : ℝ)) := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h4, ← Real.rpow_add two_pos]
    rw [← hlhs, hrhs] at hlt
    linarith [(Real.rpow_lt_rpow_left_iff one_lt_two).mp hlt]
  set e_def : ℝ := ((2 * (2 * Nat.sqrt (n / 2) + 1) + 1 : ℕ) : ℝ)
  have he_add_le : 2 + e_def ≤ (defic n : ℝ) := by
    have hs_le : Nat.sqrt (n / 2) ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (Nat.div_le_self n 2)
    have hnat : 2 + (2 * (2 * Nat.sqrt (n / 2) + 1) + 1) ≤ defic n := by dsimp only [defic]; omega
    dsimp only [e_def]
    exact_mod_cast hnat
  have hγ_le : γ ≤ 1 / 8 := by
    have hε0_le : ε₀ ≤ 1 / (2 * A) := min_le_right _ _
    have hAε : A * ε₀ ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hε0_le hA.le
      have heq : A * (1 / (2 * A)) = 1 / 2 := by field_simp
      linarith
    calc γ = (A * ε₀) / (4 * (1 + 2 * A)) := rfl
      _ ≤ (1 / 2) / (4 * 1) := div_le_div₀ (by norm_num) hAε (by norm_num) (by linarith)
      _ = 1 / 8 := by norm_num
  have hfin := finite_bisection_supply_demand (e_defic := e_def) net.G lay (by positivity)
    (fun t ht => hlay t ht t le_rfl (by omega)) (by omega) one_pos net.leafOut (by norm_num)
    (fun U hU => by dsimp only [e_def]; exact_mod_cast half_le_cutRank_hardMatrix n hU) hcr_bound
    (fun Comp hcut hconn => by
      have hr : (net.G.cycleRankOn Comp : ℝ) + ({i | net.leafOut i ∈ Comp}.ncard : ℝ) ≤
          (twoQubitCount C : ℝ) + 1 := by exact_mod_cast net.cycleRank_leafOut_le Comp hcut hconn
      linarith)
    (by
      have hγn : 4 * (γ * n) ≤ 1 / 2 * n := by
        have := mul_le_mul_of_nonneg_right hγ_le (Nat.cast_nonneg (α := ℝ) n)
        linarith
      linarith)
  exact step_contradiction_of_supply_demand (C_lay := C_lay) (w_r := 1) (c_edge := 1)
    (γ_coeff := γ) (sub_err := 2 + e_def)
    hA hη (min_le_left _ _) le_rfl (by norm_num) hε₀ (by exact_mod_cast hn24) (Nat.cast_nonneg _)
    hγ.le (by positivity)
    hsize net.card_V_le
    (by
      have h1 : η ≤ A * ε₀ / (4 * Bcoef) := min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ Bcoef)
      have h3 : A * ε₀ / (4 * Bcoef) * Bcoef = A * ε₀ / 4 := by
        have hB : 0 < Bcoef := by dsimp only [Bcoef]; positivity
        field_simp
      have hBeq : 7 * (1 + (1 : ℝ) / (2 * 1 * A)) + 3 = Bcoef := by dsimp only [Bcoef]; ring
      rw [hBeq]; linarith)
    (by
      have heq : (1 + 2 * 1 * A) * γ = 1 * 1 * A * ε₀ / 4 := by
        dsimp only [γ]; field_simp
      linarith)
    (by
      have hsub : (1 + 2 * 1 * A) * (2 + e_def) ≤ (1 + 2 * A) * (defic n : ℝ) := by
        have := mul_le_mul_of_nonneg_left he_add_le (by positivity : (0 : ℝ) ≤ 1 + 2 * A)
        linarith
      have herr_le := le_trans (le_abs_self _) herrn
      linarith)
    (by convert hfin using 2 <;> ring)

/-- **Median-switched quadratic phase-state preparation fidelity decay (`2.787986 n`).** -/
theorem eventually_fidelity_phaseState_hardMatrix_le_switched {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (twoQubitCount C : ℝ) ≤ (1 + π / (3 * arccos (5 / 6)) - ε) * n →
        ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound (Or.inl rfl)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hε
  have hcoef : 1 + 1 / (2 * (2 * Switched.switchedCoefficient)) =
      1 + π / (3 * arccos (5 / 6)) := by
    have h1 := Switched.one_add_inv_two_mul_switchedCoefficient
    have h2 : 1 / (2 * Switched.switchedCoefficient) = 2 * π / (3 * arccos (5 / 6)) := by linarith
    have h3 : 1 / (2 * (2 * Switched.switchedCoefficient)) =
        1 / (2 * Switched.switchedCoefficient) / 2 := by field_simp
    rw [h3, h2]; ring
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn N e x₀ C hbond hsize
  exact hn N e x₀ C (by simpa) (by rwa [hcoef])

/-- **Rational `(2.78798 - ε) n` phase-state preparation fidelity decay.** -/
theorem eventually_fidelity_phaseState_hardMatrix_le_278798 {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (twoQubitCount C : ℝ) ≤ (278798 / 100000 - ε) * n →
        ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_fidelity_phaseState_hardMatrix_le_switched hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn N e x₀ C hbond hsize
  refine hn N e x₀ C hbond (hsize.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n)))
  have h45 := Switched.circuitCoefficient_ge_457597
  have hdiv : π / (3 * arccos (5 / 6)) = (2 * π / (3 * arccos (5 / 6))) / 2 := by ring
  linarith

/-- **Unconditional general two-local `U(4)` phase-state fidelity decay
(`(9 / 4 - ε) n = 2.25 n`).** -/
theorem eventually_fidelity_phaseState_hardMatrix_le_twoLocal_two_fifths {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), TwoLocal C →
      (twoQubitCount C : ℝ) ≤ (9 / 4 - ε) * n →
        ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound (Or.inr rfl)
    (by norm_num) layoutBound_two_fifths_four hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn N e x₀ C htwo hsize
  exact hn N e x₀ C (by simpa) (by convert hsize using 2; norm_num)

/-- **General two-local `U(4)` phase-state fidelity decay (`(5 / 2 - ε) n = 2.5 n`)** under
`LayoutBound 4 (1 / 3)`. -/
theorem eventually_fidelity_phaseState_hardMatrix_le_twoLocal_one_third
    (h4 : LayoutBound 4 (1 / 3)) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), TwoLocal C →
      (twoQubitCount C : ℝ) ≤ (5 / 2 - ε) * n →
        ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound (Or.inr rfl)
    (by norm_num) h4 hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn N e x₀ C htwo hsize
  exact hn N e x₀ C (by simpa) (by convert hsize using 2; norm_num)

/-! #### 4. Reversible and quantum linear synthesis (`4.575972 n` / `3.5 n` / `4.0 n`) -/

/-- **Reversible and quantum linear synthesis lower bound under `LayoutBound d A` (`d ∈ {3, 4}`).**
Every quantum circuit `C` on ANY number of qubits `N` (with unlimited clean ancillas restored to
`x₀` and unlimited single-qubit `U(2)` gates) computing the invertible linear bijection
`boolMulVec (robustBijectiveMatrix n)` on `e : Fin n ↪ Fin N` requires more than
`(1 + 1 / A - ε) n` two-qubit gates. -/
theorem eventually_lt_twoQubitCount_linear_of_layoutBound {d : ℕ} (hd : d = 3 ∨ d = 4)
    {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound d A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N),
      (if d = 3 then AllBondRankTwo C else TwoLocal C) →
      (∀ x, C.run (embedBits e x₀ x) =
        Quantum.ket (embedBits e x₀ (boolMulVec (robustBijectiveMatrix n) x))) →
        (1 + 1 / A - ε) * n < twoQubitCount C := by
  set ε₀ := min ε (1 / A)
  have hε₀ : 0 < ε₀ := lt_min hε (by positivity)
  set Bcoef : ℝ := 7 * (1 + 2 / (2 * 1 * A)) + 3
  set η : ℝ := min A (A * ε₀ / (4 * Bcoef))
  have hη : 0 < η := lt_min hA (by positivity)
  obtain ⟨C_lay, hC_lay⟩ := hlayout.exists_layout_componentwise hη
  set defic : ℕ → ℕ := fun n => 4 * (2 * Nat.sqrt n + 1) + 6
  have herr_o : (fun n : ℕ => (2 + 2 * A) * (defic n : ℝ) +
      (2 + (4 * A + 2 * |C_lay|))) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_sqrt_defic.const_mul_left _).add (isLittleO_const_id_atTop _).natCast_atTop
  have hsmall_d : ∀ᶠ n : ℕ in atTop, 24 ≤ n ∧ 4 * (defic n : ℝ) + 4 ≤ 2 * n := by
    filter_upwards [isLittleO_sqrt_defic.bound (by norm_num : (0 : ℝ) < 1 / 4),
      eventually_ge_atTop 24] with n hn hn24
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hn
    have hd1 : (defic n : ℝ) ≤ 1 / 4 * n := by linarith [le_abs_self (defic n : ℝ)]
    have hn24' : (24 : ℝ) ≤ n := by exact_mod_cast hn24
    exact ⟨hn24, by linarith⟩
  filter_upwards [herr_o.bound (show (0 : ℝ) < 2 * 1 * A * ε₀ / 4 by positivity), hsmall_d]
    with n herrn ⟨hn24, hdn⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herrn
  intro N e x₀ C hmodel hlin
  by_contra! hsize_orig
  have hsize : (twoQubitCount C : ℝ) ≤ (1 + 2 / (2 * 1 * A) - ε₀) * n := by
    have h1 : 1 + 1 / A - ε ≤ 1 + 2 / (2 * 1 * A) - ε₀ := by
      have heq : (2 : ℝ) / (2 * 1 * A) = 1 / A := by ring
      linarith [min_le_left ε (1 / A)]
    exact hsize_orig.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n))
  obtain ⟨net⟩ := exists_compiledQuantumNet hd e (e ⟨0, by omega⟩) hmodel
  obtain ⟨lay, hlay⟩ := hC_lay net.V net.E net.G net.loopless net.maxDeg
  have hcr_bound (P : Set net.V) :
      ((linBlockMatrix n (robustBijectiveMatrix n) +
        (linBlockMatrix n (robustBijectiveMatrix n))ᵀ).cutRank {k | net.leaf2n k ∈ P} : ℝ) ≤
        1 * ((net.G.edgeCut P).ncard : ℝ) + 1 := by
    have hr : ((linBlockMatrix n (robustBijectiveMatrix n) +
        (linBlockMatrix n (robustBijectiveMatrix n))ᵀ).cutRank {k | net.leaf2n k ∈ P} : ℝ) ≤
        (net.G.edgeCut P).ncard + 1 := by exact_mod_cast net.cutRank_linBlockMatrix_le x₀ hlin P
    linarith
  set e_def : ℝ := ((2 * (2 * (2 * Nat.sqrt n + 1)) + 1 : ℕ) : ℝ)
  have he_add_le : 1 + e_def ≤ (defic n : ℝ) := by
    have hnat : 1 + (2 * (2 * (2 * Nat.sqrt n + 1)) + 1) ≤ defic n := by dsimp only [defic]; omega
    dsimp only [e_def]
    exact_mod_cast hnat
  have hfin := finite_bisection_supply_demand (w_r := 2) (e_defic := e_def) net.G lay
    (by positivity) (fun t ht => hlay t ht t le_rfl (by omega)) (by omega) (by norm_num) net.leaf2n
    (by norm_num)
    (fun U hU => by
      dsimp only [e_def]
      exact_mod_cast half_le_cutRank_linBlockMatrix n (robustBijectiveMatrix_submatrixRobust n) hU)
    hcr_bound
    (fun Comp hcut hconn => by
      have hr : (2 : ℝ) * (net.G.cycleRankOn Comp : ℝ) +
          ({k : Fin (2 * n) | net.leaf2n k ∈ Comp}.ncard : ℝ) ≤
          2 * ((twoQubitCount C : ℝ) + 1) := by
        exact_mod_cast net.cycleRank_leaf2n_le Comp hcut hconn
      linarith)
    (by push_cast; linarith)
  exact step_contradiction_of_supply_demand (C_lay := C_lay) (w_r := 2) (c_edge := 1)
    (γ_coeff := 0) (sub_err := 1 + e_def)
    hA hη (min_le_left _ _) (by norm_num) (by norm_num) hε₀ (by exact_mod_cast hn24)
    (Nat.cast_nonneg _) le_rfl (by positivity)
    hsize net.card_V_le
    (by
      have h1 : η ≤ A * ε₀ / (4 * Bcoef) := min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ Bcoef)
      have h3 : A * ε₀ / (4 * Bcoef) * Bcoef = A * ε₀ / 4 := by
        have hB : 0 < Bcoef := by dsimp only [Bcoef]; positivity
        field_simp
      change η * Bcoef ≤ A * ε₀ / 4
      linarith)
    (by rw [mul_zero]; positivity)
    (by
      have hsub : (2 + 2 * 1 * A) * (1 + e_def) ≤ (2 + 2 * A) * (defic n : ℝ) := by
        have := mul_le_mul_of_nonneg_left he_add_le (by positivity : (0 : ℝ) ≤ 2 + 2 * A)
        linarith
      have herr_le := le_trans (le_abs_self _) herrn
      linarith)
    (by rw [Nat.cast_mul, Nat.cast_ofNat] at hfin; convert hfin using 2 <;> ring)

/-- **Median-switched reversible and quantum linear synthesis lower bound (`4.575972 n`).**
Synthesizing `boolMulVec (robustBijectiveMatrix n)` using bond-rank-two two-qubit gates (`CNOT`,
`CZ`, `Gate.controlled V`) plus arbitrary free single-qubit `U(2)` gates and clean ancillas requires
more than `(1 + 2π / (3 arccos (5 / 6)) - ε) n ≈ 4.575972 n` two-qubit gates. -/
theorem eventually_lt_twoQubitCount_linear_switched {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (∀ x, C.run (embedBits e x₀ x) =
        Quantum.ket (embedBits e x₀ (boolMulVec (robustBijectiveMatrix n) x))) →
        (1 + 2 * π / (3 * arccos (5 / 6)) - ε) * n < twoQubitCount C := by
  have hev := eventually_lt_twoQubitCount_linear_of_layoutBound (Or.inl rfl)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hε
  filter_upwards [hev] with n hn N e x₀ C hbond hlin
  rw [← Switched.one_add_inv_two_mul_switchedCoefficient]
  exact hn N e x₀ C (by simpa) hlin

/-- **Rational `(4.57597 - ε) n` reversible and quantum linear synthesis lower bound.** -/
theorem eventually_lt_twoQubitCount_linear_457597 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (∀ x, C.run (embedBits e x₀ x) =
        Quantum.ket (embedBits e x₀ (boolMulVec (robustBijectiveMatrix n) x))) →
        (457597 / 100000 - ε) * n < twoQubitCount C := by
  filter_upwards [eventually_lt_twoQubitCount_linear_switched hε] with n hn N e x₀ C hbond hlin
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n))
    (hn N e x₀ C hbond hlin)
  linarith [Switched.circuitCoefficient_ge_457597]

/-- **Unconditional general two-local `U(4)` linear synthesis lower bound
(`(7 / 2 - ε) n = 3.5 n`)** via `layoutBound_two_fifths_four` (`A₄ = 2 / 5`). -/
theorem eventually_lt_twoQubitCount_linear_twoLocal_two_fifths {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), TwoLocal C →
      (∀ x, C.run (embedBits e x₀ x) =
        Quantum.ket (embedBits e x₀ (boolMulVec (robustBijectiveMatrix n) x))) →
        (7 / 2 - ε) * n < twoQubitCount C := by
  filter_upwards [eventually_lt_twoQubitCount_linear_of_layoutBound (Or.inr rfl)
    (by norm_num) layoutBound_two_fifths_four hε] with n hn N e x₀ C htwo hlin
  convert hn N e x₀ C (by simpa) hlin using 2
  norm_num

/-- **General two-local `U(4)` linear synthesis lower bound (`(4 - ε) n`)** under
`LayoutBound 4 (1 / 3)`. -/
theorem eventually_lt_twoQubitCount_linear_twoLocal_one_third
    (h4 : LayoutBound 4 (1 / 3)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), TwoLocal C →
      (∀ x, C.run (embedBits e x₀ x) =
        Quantum.ket (embedBits e x₀ (boolMulVec (robustBijectiveMatrix n) x))) →
        (4 - ε) * n < twoQubitCount C := by
  filter_upwards [eventually_lt_twoQubitCount_linear_of_layoutBound (Or.inr rfl)
    (by norm_num) h4 hε] with n hn N e x₀ C htwo hlin
  convert hn N e x₀ C (by simpa) hlin using 2
  norm_num

end MainBounds

end Cslib.Circuits.Frontier
