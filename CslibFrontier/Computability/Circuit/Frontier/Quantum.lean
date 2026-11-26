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
   (`CNOT`, `CZ`, `Gate.controlled V`) and `(7 / 4 - ε) n` general `U(4)` gates via
   `layoutBound_four_one_third` (`A₄ = 1 / 3`).
2. **`UQP` unbounded-error sign-rank**
   (`eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound`,
   `eventually_lt_twoQubitCount_uqp_hardForm_switched`). Deciding `hardForm n` with strict threshold
   `θ` (`θ < prob x ↔ hardForm n x`, with arbitrarily small margin) requires more than
   `(1 + π / (12 arccos (5 / 6)) - ε) n ≈ 1.446996 n` bond-rank-two gates and
   `(11 / 8 - ε) n` general `U(4)` gates.
3. **Quadratic phase-state preparation fidelity decay**
   (`eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound`,
   `eventually_fidelity_phaseState_hardMatrix_le_switched`). Squared overlap
   `‖⟪ψ_{hardMatrix n}, C |x₀⟩⟫‖²` with the `n`-qubit computational-basis phase state of the
   nonconstructively chosen `hardMatrix n` decays as `2 ^ (-γ n)` below
   `(1 + π / (3 arccos (5 / 6)) - ε) n ≈ 2.787986 n` bond-rank-two gates and
   `(5 / 2 - ε) n` general `U(4)` gates.
4. **Reversible and quantum `𝔽₂` linear synthesis**
   (`eventually_lt_twoQubitCount_linear_of_layoutBound`,
   `eventually_lt_twoQubitCount_linear_switched`). Coherently computing the nonconstructively chosen
   invertible submatrix-robust linear bijection `boolMulVec (robustBijectiveMatrix n)` requires more
   than `(1 + 2π / (3 arccos (5 / 6)) - ε) n ≈ 4.575972 n` bond-rank-two gates and
   `(4 - ε) n` general `U(4)` gates, with clean ancillas restored exactly.

The active-qubit wire-segment tensor network compiler and the four quantum frontier lower-bound
families developed here and in `CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork`
are original to this library.

## Main definitions

* `Cslib.Circuits.Frontier.robustBijectiveMatrix`: nonconstructively chosen family of invertible
  submatrix-robust `n × n` matrices over `𝔽₂` (via `Matrix.exists_bijective_submatrixRobust`).

## Main results

* `Cslib.Circuits.Frontier.robustBijectiveMatrix_bijective`,
  `Cslib.Circuits.Frontier.robustBijectiveMatrix_submatrixRobust`,
  `Cslib.Circuits.Frontier.boolMulVec_robustBijectiveMatrix_bijective`: bijectivity and square-block
  robustness of `robustBijectiveMatrix n`.
* `Cslib.Circuits.Frontier.eventually_abs_quantumCorrelation_hardForm_le_of_layoutBound`,
  `Cslib.Circuits.Frontier.eventually_abs_quantumCorrelation_hardForm_le_switched`,
  `Cslib.Circuits.Frontier.eventually_abs_quantumCorrelation_hardForm_le_twoLocal`,
  `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_bqp_hardForm_switched`: `BQP` single-qubit
  measurement correlation decay and decision bounds (`1.893993 n` / `1.75 n`).
* `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound`,
  `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_uqp_hardForm_switched`,
  `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_uqp_hardForm_twoLocal`: `UQP` unbounded-error
  sign-rank lower bounds (`1.446996 n` / `1.375 n`).
* `Cslib.Circuits.Frontier.eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound`,
  `Cslib.Circuits.Frontier.eventually_fidelity_phaseState_hardMatrix_le_switched`,
  `Cslib.Circuits.Frontier.eventually_fidelity_phaseState_hardMatrix_le_twoLocal`: quadratic phase
  state preparation fidelity decay (`2.787986 n` / `2.5 n`).
* `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_linear_of_layoutBound`,
  `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_linear_switched`,
  `Cslib.Circuits.Frontier.eventually_lt_twoQubitCount_linear_twoLocal`: reversible and quantum
  linear synthesis lower bounds (`4.575972 n` / `4 n`).

## References

* [J. Forster, *A linear lower bound on the unbounded error probabilistic communication
  complexity*][Forster2002]
* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
* [A. A. Sherstov, P. Wu, *Near-Optimal Lower Bounds on the Threshold Degree and Sign-Rank of
  AC⁰*][SherstovWu2019]
-/

public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics Real Matrix
open scoped Finset

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
  let vecEquiv := (BitString.toZModSpace (Fin n)).toEquiv
  have heq : boolMulVec (robustBijectiveMatrix n) =
      vecEquiv.symm ∘ (robustBijectiveMatrix n).mulVec ∘ vecEquiv := by
    ext x i
    simp only [Function.comp_apply, vecEquiv, LinearEquiv.coe_toEquiv,
      LinearEquiv.coe_symm_toEquiv, BitString.toZModSpace_symm_apply, boolMulVec, Matrix.mulVec,
      dotProduct, BitString.toZModSpace_apply, BitString.bitEquiv_symm_apply]
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
    simp only [f, lay.initial_of_card_le le_rfl, mem_univ, ofPred_true, ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hstep : ∀ t < Nat.card V_fin, f (t + 1) ≤ f t + 1 := by
    intro t ht
    simp only [f, lay.initial_succ ht]
    have hsub : {i : Fin n | leaf i ∈ insert (lay.symm ⟨t, ht⟩) (lay.initial t)} ⊆
        {i : Fin n | leaf i = lay.symm ⟨t, ht⟩} ∪ {i : Fin n | leaf i ∈ lay.initial t} :=
      fun _ hi => hi
    have hle1 : {i : Fin n | leaf i = lay.symm ⟨t, ht⟩}.ncard ≤ 1 :=
      (ncard_le_one (toFinite _)).mpr fun a (ha : leaf a = _) b (hb : leaf b = _) =>
        leaf.injective (ha.trans hb.symm)
    have h1 := (ncard_le_ncard hsub (toFinite _)).trans (ncard_union_le _ _)
    omega
  have hgoal_le : n / 2 ≤ f (Nat.card V_fin) := by rw [hfV]; exact Nat.div_le_self n 2
  have hP : ∃ t, n / 2 ≤ f t := ⟨_, hgoal_le⟩
  have hfeq : f (Nat.find hP) = n / 2 := by
    have hspec := Nat.find_spec hP
    by_cases h0 : Nat.find hP = 0
    · rw [h0, hf0] at hspec ⊢; omega
    · have := Nat.find_min hP (by omega : Nat.find hP - 1 < Nat.find hP)
      have := hstep (Nat.find hP - 1) (by have := Nat.find_min' hP hgoal_le; omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hP)] at this
      omega
  refine ⟨Nat.find hP, (Nat.find_min' hP hgoal_le).lt_of_ne fun h => ?_, hfeq⟩
  rw [h, hfV] at hfeq; omega

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
      linarith [ncard_le_cutRank_add_of_bisection hbis_M hPhalf]
    by_cases hh : {j | leaf j ∈ Qset}.ncard ≤ m / 2
    · exact Or.inl (hsmall_side Qset hQ hh)
    · refine Or.inr ?_
      have hQc_cut : G.edgeCut Qsetᶜ = ∅ :=
        G.edgeCut_eq_empty_iff.mpr fun e' => not_iff_not.mpr (G.edgeCut_eq_empty_iff.mp hQ e')
      have hsum_m : {j | leaf j ∈ Qset}.ncard + {j | leaf j ∈ Qsetᶜ}.ncard = m := by
        change {j | leaf j ∈ Qset}.ncard + ({j | leaf j ∈ Qset}ᶜ).ncard = m
        rw [ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
      linarith [hsmall_side Qsetᶜ hQc_cut (by omega),
        (Nat.cast_add _ _).symm.trans (congrArg (Nat.cast (R := ℝ)) hsum_m)]
  set W := G.component (lay.symm ⟨t, ht_lt⟩)
  have hW_cut : G.edgeCut W = ∅ := G.edgeCut_component _
  obtain ⟨hfront_W, hfront_le⟩ := hlay t ht_lt
  have hm_div2_lb : (m : ℝ) / 2 - 1 ≤ ((m / 2 : ℕ) : ℝ) := by
    have : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : m ≤ 2 * (m / 2) + 1)
    linarith
  have hm_div2_ub : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := Nat.cast_div_le
  have hW_large : (m : ℝ) - (slack + e_defic) ≤ ({j | leaf j ∈ W}.ncard : ℝ) := by
    refine (hclosed_dich W hW_cut).resolve_left fun hWs => ?_
    set Bset := lay.initial t \ W
    have hB_cut : G.edgeCut Bset = ∅ := Multigraph.edgeCut_sdiff_eq_empty hW_cut hfront_W
    have hB_sub : {j | leaf j ∈ Bset} ⊆ {j | leaf j ∈ lay.initial t} := fun _ hj => hj.1
    have hinit_sub : {j | leaf j ∈ lay.initial t} ⊆ {j | leaf j ∈ Bset} ∪ {j | leaf j ∈ W} :=
      fun j hj => (em (leaf j ∈ W)).elim Or.inr fun hjW => Or.inl ⟨hj, hjW⟩
    have hB_le : ({j | leaf j ∈ Bset}.ncard : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by
      exact_mod_cast (ncard_le_ncard hB_sub (toFinite _)).trans_eq hXt
    have hB_ge : ((m / 2 : ℕ) : ℝ) ≤
        ({j | leaf j ∈ Bset}.ncard : ℝ) + ({j | leaf j ∈ W}.ncard : ℝ) := by
      rw [← hXt]
      exact_mod_cast (ncard_le_ncard hinit_sub (toFinite _)).trans (ncard_union_le _ _)
    rcases hclosed_dich Bset hB_cut with hBs | hBl <;> linarith
  have hw_ρ_le : w_r * (G.cycleRankOn W : ℝ) ≤ w_r * ((s : ℝ) + 1) - m + (slack + e_defic) := by
    linarith [hρ_comp W hW_cut (G.ncard_component_le_ncard_touching_add_one _)]
  have hw_front_le : w_r * ((G.frontier lay t).ncard : ℝ) ≤
      (A + η) * (w_r * ((s : ℝ) + 1) - m + (slack + e_defic)) +
        w_r * η * Nat.card V_fin + w_r * C_lay := by
    linarith [mul_le_mul_of_nonneg_left hfront_le hw.le,
      mul_le_mul_of_nonneg_left hw_ρ_le hAη]
  have hcr_t : _ ≤ c_edge * ((G.frontier lay t).ncard : ℝ) + slack := hcr_le (lay.initial t)
  have hdem : (m : ℝ) / 2 - 1 - (slack + e_defic) ≤ c_edge * ((G.frontier lay t).ncard : ℝ) := by
    linarith [hbis_M {j | leaf j ∈ lay.initial t} hXt]
  linarith [mul_le_mul_of_nonneg_left hdem hw.le,
    mul_le_mul_of_nonneg_left hw_front_le hc_edge.le]

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
  have hc_star_pos : 1 < c_star := lt_add_of_pos_right 1 (by positivity)
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
    linarith [mul_le_mul_of_nonneg_left hη_le_A hc_edge.le]
  have hγ_term : (w_r + c_edge * (A + η)) * (γ_coeff * n_r) ≤
      w_r * c_edge * A * ε₀ / 4 * n_r := by
    have hn0 : 0 ≤ n_r := by linarith
    linarith [mul_le_mul_of_nonneg_right hslack_coef (mul_nonneg hγ_nn hn0),
      mul_le_mul_of_nonneg_right hγ_bound hn0]
  have hsub_term : (w_r + c_edge * (A + η)) * sub_err +
      w_r + c_edge * ((A + η) * w_r + w_r * C_lay) ≤
      w_r * c_edge * A * ε₀ / 4 * n_r := by
    have h2 : c_edge * ((A + η) * w_r + w_r * C_lay) ≤
        c_edge * (2 * A * w_r + w_r * |C_lay|) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right (by linarith : A + η ≤ 2 * A)
            (by linarith : 0 ≤ w_r))
          (mul_le_mul_of_nonneg_left (le_abs_self C_lay) (by linarith : 0 ≤ w_r))) hc_edge.le
    linarith [mul_le_mul_of_nonneg_right hslack_coef hsub_nn]
  linarith [show 0 < w_r * c_edge * A * ε₀ / 4 * n_r by positivity]

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

/-- Shared asymptotic contradiction driver over `CompiledQuantumNet`: selects layout slack `η`,
bounds sublinear deficiency `4 * (2 * ⌊√n⌋ + 1) + 6 = o(n)`, extracts a componentwise layout, and
combines `finite_bisection_supply_demand` with `step_contradiction_of_supply_demand`. -/
private theorem eventually_compiledQuantumNet_contradiction {d : ℕ} {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound d A) {w_nat c_slack : ℕ} (hw_pos : 1 ≤ w_nat)
    {c_edge ε γ_coeff : ℝ} (hc_edge : 0 < c_edge) (hε : 0 < ε) (hγ_nn : 0 ≤ γ_coeff)
    (hγ_le : 4 * γ_coeff ≤ (w_nat : ℝ) / 2)
    (hγ_bound : ((w_nat : ℝ) + 2 * c_edge * A) * γ_coeff ≤
      (w_nat : ℝ) * c_edge * A * min ε ((w_nat : ℝ) / (2 * c_edge * A)) / 4)
    (m_fn : ℕ → ℕ) (hm_eq : ∀ n, (m_fn n : ℝ) = (w_nat : ℝ) * n)
    (e_fn : ℕ → ℕ) (he_le : ∀ n, c_slack + e_fn n ≤ 4 * (2 * Nat.sqrt n + 1) + 6)
    (M_fn : ∀ n, Matrix (Fin (m_fn n)) (Fin (m_fn n)) (ZMod 2))
    (hbis_M : ∀ n (U : Set (Fin (m_fn n))), U.ncard = m_fn n / 2 →
      ((m_fn n / 2 : ℕ) : ℝ) ≤ (M_fn n).cutRank U + (e_fn n : ℝ)) :
    ∀ᶠ n in atTop, 24 ≤ n ∧ ∀ {N : ℕ} {e : Fin n ↪ Fin N} {q_out : Fin N} {C : Quantum.Circuit N}
      (net : CompiledQuantumNet d e q_out C) (leaf : Fin (m_fn n) ↪ net.V),
      (twoQubitCount C : ℝ) ≤ (1 + (w_nat : ℝ) / (2 * c_edge * A) - ε) * n →
      (∀ P : Set net.V,
        ((M_fn n).cutRank {j | leaf j ∈ P} : ℝ) ≤
          c_edge * (net.G.edgeCut P).ncard + (γ_coeff * n + c_slack)) →
      (∀ Comp : Set net.V, net.G.edgeCut Comp = ∅ →
        Comp.ncard ≤ (net.G.touching Comp).ncard + 1 →
        w_nat * net.G.cycleRankOn Comp + {j | leaf j ∈ Comp}.ncard ≤
          w_nat * (twoQubitCount C + 1)) →
      False := by
  set w_r : ℝ := (w_nat : ℝ)
  have hw_ge_one : 1 ≤ w_r := by dsimp only [w_r]; exact_mod_cast hw_pos
  have hw_pos_r : 0 < w_r := by linarith
  set ε₀ : ℝ := min ε (w_r / (2 * c_edge * A))
  have hε₀ : 0 < ε₀ := lt_min hε (by positivity)
  set Bcoef : ℝ := 7 * (1 + w_r / (2 * c_edge * A)) + 3
  set η : ℝ := min A (A * ε₀ / (4 * Bcoef))
  have hη : 0 < η := lt_min hA (by positivity)
  obtain ⟨C_lay, hC_lay⟩ := hlayout.exists_layout_componentwise hη
  set defic : ℕ → ℕ := fun n => 4 * (2 * Nat.sqrt n + 1) + 6
  have herr_o : (fun n : ℕ => (w_r + 2 * c_edge * A) * (defic n : ℝ) +
      (w_r + c_edge * (2 * A * w_r + w_r * |C_lay|))) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_sqrt_defic.const_mul_left _).add (isLittleO_const_id_atTop _).natCast_atTop
  have hsmall_d : ∀ᶠ n : ℕ in atTop, 24 ≤ n ∧ 4 * (defic n : ℝ) + 4 ≤ 1 / 2 * n := by
    filter_upwards [isLittleO_sqrt_defic.bound (by norm_num : (0 : ℝ) < 1 / 16),
      eventually_ge_atTop 24] with n hn hn24
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hn
    have hd1 : (defic n : ℝ) ≤ 1 / 16 * n := by linarith [le_abs_self (defic n : ℝ)]
    have hn24' : (24 : ℝ) ≤ n := by exact_mod_cast hn24
    exact ⟨hn24, by linarith⟩
  filter_upwards [herr_o.bound (show (0 : ℝ) < w_r * c_edge * A * ε₀ / 4 by positivity), hsmall_d]
    with n herrn ⟨hn24, hdn⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herrn
  refine ⟨hn24, fun {_ _ _ C} net leaf hsize_orig hcr_bound hρ_comp => ?_⟩
  have hsize : (twoQubitCount C : ℝ) ≤ (1 + w_r / (2 * c_edge * A) - ε₀) * n :=
    hsize_orig.trans (mul_le_mul_of_nonneg_right
      (by linarith [min_le_left ε (w_r / (2 * c_edge * A))]) (Nat.cast_nonneg n))
  have hρ_r (Comp : Set net.V) (hcut : net.G.edgeCut Comp = ∅)
      (hconn : Comp.ncard ≤ (net.G.touching Comp).ncard + 1) :
      w_r * (net.G.cycleRankOn Comp : ℝ) + ({j | leaf j ∈ Comp}.ncard : ℝ) ≤
        w_r * ((twoQubitCount C : ℝ) + 1) := by
    dsimp only [w_r]; exact_mod_cast hρ_comp Comp hcut hconn
  obtain ⟨lay, hlay⟩ := hC_lay net.V net.E net.G net.loopless net.maxDeg
  have hn24_r : (24 : ℝ) ≤ n := by exact_mod_cast hn24
  have hm_pos : 1 ≤ m_fn n := by
    exact_mod_cast (show (1 : ℝ) ≤ m_fn n by rw [hm_eq n]; nlinarith)
  have he_add_le : (c_slack : ℝ) + (e_fn n : ℝ) ≤ (defic n : ℝ) := by exact_mod_cast he_le n
  have hfin := finite_bisection_supply_demand (w_r := w_r) (e_defic := (e_fn n : ℝ)) net.G lay
    (by positivity) (fun t ht => hlay t ht t le_rfl (by omega)) hm_pos hw_pos_r leaf hc_edge
    (hbis_M n) hcr_bound hρ_r
    (by
      rw [hm_eq n]
      have hw_half : 1 / 2 * (n : ℝ) ≤ w_r / 2 * n :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
      linarith [mul_le_mul_of_nonneg_right hγ_le (Nat.cast_nonneg (α := ℝ) n)])
  exact step_contradiction_of_supply_demand (C_lay := C_lay) (w_r := w_r) (c_edge := c_edge)
    (γ_coeff := γ_coeff) (sub_err := (c_slack : ℝ) + (e_fn n : ℝ))
    hA hη (min_le_left _ _) hw_ge_one hc_edge hε₀ hn24_r (Nat.cast_nonneg _)
    hγ_nn (by positivity) hsize net.card_V_le
    (by
      have h1 : η ≤ A * ε₀ / (4 * Bcoef) := min_le_right _ _
      linarith [(le_div_iff₀ (by positivity : 0 < 4 * Bcoef)).mp h1])
    hγ_bound
    (by
      linarith [mul_le_mul_of_nonneg_left he_add_le (by positivity : 0 ≤ w_r + 2 * c_edge * A),
        (le_abs_self _).trans herrn])
    (by rw [hm_eq n] at hfin; linarith)

private theorem switched_coeff_eq (k c_sw : ℝ) (hk : k ≠ 0)
    (h : 1 + 2 * π / (3 * k * arccos (5 / 6)) = c_sw) :
    c_sw = 1 + 1 / (k * (2 * Switched.switchedCoefficient)) := by
  have h2 : 1 / (2 * Switched.switchedCoefficient) = 2 * π / (3 * arccos (5 / 6)) := by
    linarith [Switched.one_add_inv_two_mul_switchedCoefficient]
  rw [mul_comm k, ← div_div, h2, ← h]
  field_simp

private theorem rat_sub_mul_le_switched {k c_sw c_rat ε : ℝ} (hk : 0 < k) (n : ℕ)
    (hsw : 1 + 2 * π / (3 * k * arccos (5 / 6)) = c_sw)
    (hrat : c_rat ≤ 1 + (457597 / 100000 - 1) / k) :
    (c_rat - ε) * (n : ℝ) ≤ (c_sw - ε) * (n : ℝ) := by
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n)
  have h45 := Switched.circuitCoefficient_ge_457597
  have hdiv : (457597 / 100000 - 1) / k ≤ (2 * π / (3 * arccos (5 / 6))) / k :=
    div_le_div_of_nonneg_right (by linarith) hk.le
  have hrew : 1 + (2 * π / (3 * arccos (5 / 6))) / k = c_sw := by
    rw [← hsw, div_div, show 3 * arccos (5 / 6) * k = 3 * k * arccos (5 / 6) by ring]
  linarith

private theorem eventually_hardMatrix_contradiction {d : ℕ} {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound d A) {c_slack : ℕ} (hs : c_slack ≤ 4)
    {c_edge ε γ_coeff : ℝ} (hc_edge : 0 < c_edge) (hε : 0 < ε) (hγ_nn : 0 ≤ γ_coeff)
    (hγ_le : 4 * γ_coeff ≤ 1 / 2)
    (hγ_bound : (1 + 2 * c_edge * A) * γ_coeff ≤
      c_edge * A * min ε (1 / (2 * c_edge * A)) / 4) :
    ∀ᶠ n in atTop, 24 ≤ n ∧ ∀ {N : ℕ} {e : Fin n ↪ Fin N} {q_out : Fin N} {C : Quantum.Circuit N}
      (net : CompiledQuantumNet d e q_out C) (leaf : Fin n ↪ net.V),
      (twoQubitCount C : ℝ) ≤ (1 + 1 / (2 * c_edge * A) - ε) * n →
      (∀ P : Set net.V,
        ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {j | leaf j ∈ P} : ℝ) ≤
          c_edge * (net.G.edgeCut P).ncard + (γ_coeff * n + c_slack)) →
      (∀ Comp : Set net.V, net.G.edgeCut Comp = ∅ →
        Comp.ncard ≤ (net.G.touching Comp).ncard + 1 →
        net.G.cycleRankOn Comp + {j | leaf j ∈ Comp}.ncard ≤ twoQubitCount C + 1) →
      False := by
  have hev := eventually_compiledQuantumNet_contradiction hA hlayout (w_nat := 1)
    (c_slack := c_slack) le_rfl (c_edge := c_edge) (ε := ε) (γ_coeff := γ_coeff)
    hc_edge hε hγ_nn (by push_cast; exact hγ_le) (by push_cast; linarith)
    (fun n => n) (fun n => by simp)
    (fun n => 2 * (2 * Nat.sqrt (n / 2) + 1) + 1)
    (fun n => by have := Nat.sqrt_le_sqrt (Nat.div_le_self n 2); omega)
    (fun n => hardMatrix n + (hardMatrix n)ᵀ)
    (fun n U hU => by exact_mod_cast half_le_cutRank_hardMatrix n hU)
  filter_upwards [hev] with n ⟨hn24, hcontra⟩
  exact ⟨hn24, fun net leaf hsize hcr hρ =>
    hcontra net leaf (by simpa only [Nat.cast_one] using hsize) hcr
      fun Comp hcut hconn => by simpa only [one_mul] using hρ Comp hcut hconn⟩

/-- Shared exponential-decay driver on `hardMatrix n`: converts a single-cut inequality
`val_sq * 2 ^ cutRank ≤ 4 * 2 ^ (c_edge * edgeCut)` and component cycle-rank bound into
`val_sq ≤ 2 ^ (-γ_sq * n)` below `(1 + 1 / (2 * c_edge * A) - ε) * n` two-qubit gates. -/
private theorem eventually_hardMatrix_sq_le_of_layoutBound {d : ℕ}
    {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound d A) {c_edge ε : ℝ}
    (hc_edge : 0 < c_edge) (hε : 0 < ε) :
    ∃ γ_sq : ℝ, 0 < γ_sq ∧ ∀ᶠ n in atTop, 24 ≤ n ∧
      ∀ {N : ℕ} {e : Fin n ↪ Fin N} {q_out : Fin N} {C : Quantum.Circuit N}
        (net : CompiledQuantumNet d e q_out C) (leaf : Fin n ↪ net.V) (val_sq : ℝ),
        (twoQubitCount C : ℝ) ≤ (1 + 1 / (2 * c_edge * A) - ε) * n →
        (∀ P : Set net.V,
          val_sq * (2 : ℝ) ^ ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | leaf i ∈ P}) ≤
            4 * (2 : ℝ) ^ (c_edge * ((net.G.edgeCut P).ncard : ℝ))) →
        (∀ Comp : Set net.V, net.G.edgeCut Comp = ∅ →
          Comp.ncard ≤ (net.G.touching Comp).ncard + 1 →
          net.G.cycleRankOn Comp + {i | leaf i ∈ Comp}.ncard ≤ twoQubitCount C + 1) →
        val_sq ≤ (2 : ℝ) ^ (-γ_sq * n) := by
  set ε₀ := min ε (1 / (2 * c_edge * A))
  have hε₀ : 0 < ε₀ := lt_min hε (by positivity)
  set γ_sq : ℝ := c_edge * A * ε₀ / (4 * (1 + 2 * c_edge * A))
  have hγ : 0 < γ_sq := by positivity
  have hγ_le : γ_sq ≤ 1 / 8 := by
    have hAε : c_edge * A * ε₀ ≤ 1 / 2 :=
      calc c_edge * A * ε₀ ≤ c_edge * A * (1 / (2 * c_edge * A)) := by
            gcongr; exact min_le_right _ _
        _ = 1 / 2 := by field_simp
    dsimp only [γ_sq]
    rw [div_le_iff₀ (by positivity)]
    linarith [mul_pos hc_edge hA]
  refine ⟨γ_sq, hγ, ?_⟩
  have hev := eventually_hardMatrix_contradiction hA hlayout (c_slack := 2) (by norm_num)
    hc_edge hε hγ.le (by linarith)
    (le_of_eq (by dsimp only [γ_sq, ε₀]; field_simp))
  filter_upwards [hev] with n ⟨hn24, hcontra⟩
  refine ⟨hn24, fun net leaf val_sq hsize hcut_le hρ_le => ?_⟩
  by_contra! hgt
  refine hcontra net leaf hsize (fun P => ?_) hρ_le
  have hlt : (2 : ℝ) ^ (-γ_sq * n +
      ((hardMatrix n + (hardMatrix n)ᵀ).cutRank {i | leaf i ∈ P} : ℝ)) <
      (2 : ℝ) ^ (2 + c_edge * ((net.G.edgeCut P).ncard : ℝ)) := by
    rw [Real.rpow_add two_pos, Real.rpow_add two_pos, Real.rpow_natCast,
      show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
    exact (mul_lt_mul_of_pos_right hgt (by positivity)).trans_le (hcut_le P)
  push_cast
  linarith [(Real.rpow_lt_rpow_left_iff one_lt_two).mp hlt]

/-! #### 1. `BQP` single-qubit measurement correlation decay (`1.893993 n` / `1.75 n`) -/

/-- **`BQP` correlation decay with `hardForm n` under `LayoutBound d A` (`d ∈ {3, 4}`).**
For any `ε > 0`, there is `γ > 0` such that for all large `n`, every quantum circuit `C` on ANY
number of qubits `N` (with unlimited ancillas and unlimited `0`/`1`-qubit `U(2)` gates) whose
two-qubit gates have degree model `d` (`AllBondRankTwo C` for `d = 3`, or `TwoLocal C` for `d = 4`)
and satisfy `twoQubitCount C ≤ (1 + 1 / (4 A) - ε) n` has single-qubit measurement correlation at
most `2 ^ (-γ n)` with the nonconstructively chosen bilinear form `hardForm n` (selected via
`Classical.choose`). -/
theorem eventually_abs_quantumCorrelation_hardForm_le_of_layoutBound {d : ℕ} (hd : d = 3 ∨ d = 4)
    {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound d A) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (C : Quantum.Circuit N),
      (if d = 3 then AllBondRankTwo C else TwoLocal C) →
      (twoQubitCount C : ℝ) ≤ (1 + 1 / (4 * A) - ε) * n →
        |quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀)| ≤
          (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ_sq, hγ_sq, hev⟩ :=
    eventually_hardMatrix_sq_le_of_layoutBound hA hlayout (c_edge := 2) (by norm_num) hε
  refine ⟨γ_sq / 2, by positivity, ?_⟩
  filter_upwards [hev] with n ⟨_, hbound⟩ N e q_out x₀ C hmodel hsize
  obtain ⟨net⟩ := exists_compiledQuantumNet hd e q_out hmodel
  have hsq := hbound net net.leafIn
    (quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀) ^ 2)
    (by convert hsize using 3; ring)
    (fun P => by
      rw [Real.rpow_mul two_pos.le, show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num, Real.rpow_natCast]
      exact net.sq_quantumCorrelation_mul_le x₀ (hardMatrix n) P)
    net.cycleRank_leafIn_le
  have hrhs_sq : (2 : ℝ) ^ (-γ_sq * n) = ((2 : ℝ) ^ (-(γ_sq / 2) * n)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul two_pos.le]
    push_cast; congr 1; ring
  rw [hrhs_sq, ← sq_abs] at hsq
  by_contra! hgt
  linarith [pow_lt_pow_left₀ hgt (by positivity) (n := 2) (by norm_num)]

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
  rw [switched_coeff_eq 4 (1 + π / (6 * arccos (5 / 6))) (by norm_num) (by ring)]
  exact eventually_abs_quantumCorrelation_hardForm_le_of_layoutBound (Or.inl rfl)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hε

/-- **Rational `(1.89399 - ε) n` `BQP` correlation decay** with `hardForm n`. -/
theorem eventually_abs_quantumCorrelation_hardForm_le_189399 {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (C : Quantum.Circuit N),
      AllBondRankTwo C →
      (twoQubitCount C : ℝ) ≤ (189399 / 100000 - ε) * n →
        |quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀)| ≤
          (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_abs_quantumCorrelation_hardForm_le_switched hε
  exact ⟨γ, hγ, hev.mono fun n hn N e q_out x₀ C hC hsize => hn N e q_out x₀ C hC
    (hsize.trans (rat_sub_mul_le_switched (k := 4) (by norm_num) n (by ring) (by norm_num)))⟩

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
    have h2 : -γ * (n : ℝ) ≤ -2 := by linarith [(div_le_iff₀ hγ).mp hn]
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
    split_ifs at hy ⊢ <;> linarith
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

/-- **Unconditional general two-local `U(4)` `BQP` correlation decay below `(7 / 4 - ε) n` gates**
via `layoutBound_four_one_third` (`A₄ = 1 / 3`). -/
theorem eventually_abs_quantumCorrelation_hardForm_le_twoLocal {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (C : Quantum.Circuit N),
      TwoLocal C →
      (twoQubitCount C : ℝ) ≤ (7 / 4 - ε) * n →
        |quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀)| ≤
          (2 : ℝ) ^ (-γ * n) := by
  rw [show (7 / 4 : ℝ) = 1 + 1 / (4 * (1 / 3)) by norm_num]
  exact eventually_abs_quantumCorrelation_hardForm_le_of_layoutBound (Or.inr rfl) (by norm_num)
    layoutBound_four_one_third hε

/-! #### 2. `UQP` unbounded-error sign-rank bounds (`1.446996 n` / `1.375 n`) -/

/-- **`UQP` unbounded-error lower bound on `hardForm n` under `LayoutBound d A` (`d ∈ {3, 4}`).**
Every quantum circuit `C` deciding the nonconstructively chosen bilinear form `hardForm n`
(selected via `Classical.choose`) with strict threshold `θ` (`θ < prob x` on `true`, `prob x < θ`
on `false`, with arbitrarily small margin!) requires more than `(1 + 1 / (8 A) - ε) n` two-qubit
gates. -/
theorem eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound {d : ℕ} (hd : d = 3 ∨ d = 4)
    {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound d A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (θ : ℝ)
      (C : Quantum.Circuit N),
      (if d = 3 then AllBondRankTwo C else TwoLocal C) →
      (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
        else quantumAcceptProb C q_out e x₀ x < θ) →
        (1 + 1 / (8 * A) - ε) * n < twoQubitCount C := by
  have hev := eventually_hardMatrix_contradiction hA hlayout (c_slack := 4) le_rfl (c_edge := 4)
    (by norm_num) hε le_rfl (by norm_num) (by rw [mul_zero]; positivity)
  filter_upwards [hev] with n ⟨_, hcontra⟩ N e q_out x₀ θ C hmodel huqp
  by_contra! hsize
  classical
  obtain ⟨net⟩ := exists_compiledQuantumNet hd e q_out hmodel
  refine hcontra net net.leafIn (by convert hsize using 3; ring) (fun P => ?_)
    net.cycleRank_leafIn_le
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
          rw [mul_pow, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
          ring
      _ ≤ 2 ^ 4 * 2 ^ (4 * (net.G.edgeCut P).ncard) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (4 * (net.G.edgeCut P).ncard + 4) := by rw [← pow_add, add_comm]
  simp only [zero_mul, zero_add]
  exact_mod_cast (Nat.pow_le_pow_iff_right one_lt_two).mp hpow

/-- **Median-switched `UQP` unbounded-error lower bound (`1.446996 n`).** -/
theorem eventually_lt_twoQubitCount_uqp_hardForm_switched {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (θ : ℝ)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
        else quantumAcceptProb C q_out e x₀ x < θ) →
        (1 + π / (12 * arccos (5 / 6)) - ε) * n < twoQubitCount C := by
  rw [switched_coeff_eq 8 (1 + π / (12 * arccos (5 / 6))) (by norm_num) (by ring)]
  exact eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound (Or.inl rfl)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hε

/-- **Rational `(1.44699 - ε) n` `UQP` unbounded-error lower bound** on `hardForm n`. -/
theorem eventually_lt_twoQubitCount_uqp_hardForm_144699 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (θ : ℝ)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
        else quantumAcceptProb C q_out e x₀ x < θ) →
        (144699 / 100000 - ε) * n < twoQubitCount C :=
  (eventually_lt_twoQubitCount_uqp_hardForm_switched hε).mono fun n hn N e q_out x₀ θ C hC huqp =>
    (rat_sub_mul_le_switched (k := 8) (by norm_num) n (by ring) (by norm_num)).trans_lt
      (hn N e q_out x₀ θ C hC huqp)

/-- **Unconditional general two-local `U(4)` `UQP` lower bound `(11 / 8 - ε) n`**
via `layoutBound_four_one_third` (`A₄ = 1 / 3`). -/
theorem eventually_lt_twoQubitCount_uqp_hardForm_twoLocal {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (θ : ℝ)
      (C : Quantum.Circuit N), TwoLocal C →
      (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
        else quantumAcceptProb C q_out e x₀ x < θ) →
        (11 / 8 - ε) * n < twoQubitCount C := by
  rw [show (11 / 8 : ℝ) = 1 + 1 / (8 * (1 / 3)) by norm_num]
  exact eventually_lt_twoQubitCount_uqp_hardForm_of_layoutBound (Or.inr rfl) (by norm_num)
    layoutBound_four_one_third hε

/-! #### 3. Quadratic phase-state preparation fidelity decay (`2.787986 n` / `2.5 n`) -/

/-- **Quadratic phase-state preparation fidelity decay under `LayoutBound d A` (`d ∈ {3, 4}`).**
Below `(1 + 1 / (2 A) - ε) n` two-qubit gates (with unlimited ancillas `N` and unlimited
single-qubit `U(2)` gates), the squared fidelity `‖inner ℂ (phaseState (hardMatrix n) e x₀)
(C.run x₀)‖ ^ 2` against the phase state of the nonconstructively chosen matrix `hardMatrix n`
(selected via `Classical.choose`) decays exponentially as `2 ^ (-γ n)`. -/
theorem eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound {d : ℕ} (hd : d = 3 ∨ d = 4)
    {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound d A) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N),
      (if d = 3 then AllBondRankTwo C else TwoLocal C) →
      (twoQubitCount C : ℝ) ≤ (1 + 1 / (2 * A) - ε) * n →
        ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ :=
    eventually_hardMatrix_sq_le_of_layoutBound hA hlayout (c_edge := 1) (by norm_num) hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n ⟨hn24, hbound⟩ N e x₀ C hmodel hsize
  obtain ⟨net⟩ := exists_compiledQuantumNet hd e (e ⟨0, by omega⟩) hmodel
  exact hbound net net.leafOut _ (by convert hsize using 3; ring)
    (fun P => by
      rw [one_mul, Real.rpow_natCast]
      exact net.sq_fidelity_phaseState_mul_le x₀ (hardMatrix n) P)
    net.cycleRank_leafOut_le

/-- **Median-switched quadratic phase-state preparation fidelity decay (`2.787986 n`).** -/
theorem eventually_fidelity_phaseState_hardMatrix_le_switched {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (twoQubitCount C : ℝ) ≤ (1 + π / (3 * arccos (5 / 6)) - ε) * n →
        ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) := by
  rw [switched_coeff_eq 2 (1 + π / (3 * arccos (5 / 6))) (by norm_num) (by ring)]
  exact eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound (Or.inl rfl)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hε

/-- **Rational `(2.78798 - ε) n` phase-state preparation fidelity decay.** -/
theorem eventually_fidelity_phaseState_hardMatrix_le_278798 {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (twoQubitCount C : ℝ) ≤ (278798 / 100000 - ε) * n →
        ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_fidelity_phaseState_hardMatrix_le_switched hε
  exact ⟨γ, hγ, hev.mono fun n hn N e x₀ C hC hsize => hn N e x₀ C hC
    (hsize.trans (rat_sub_mul_le_switched (k := 2) (by norm_num) n (by ring) (by norm_num)))⟩

/-- **Unconditional general two-local `U(4)` phase-state fidelity decay below `(5 / 2 - ε) n`
gates** via `layoutBound_four_one_third` (`A₄ = 1 / 3`). -/
theorem eventually_fidelity_phaseState_hardMatrix_le_twoLocal {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), TwoLocal C →
      (twoQubitCount C : ℝ) ≤ (5 / 2 - ε) * n →
        ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) := by
  rw [show (5 / 2 : ℝ) = 1 + 1 / (2 * (1 / 3)) by norm_num]
  exact eventually_fidelity_phaseState_hardMatrix_le_of_layoutBound (Or.inr rfl) (by norm_num)
    layoutBound_four_one_third hε

/-! #### 4. Reversible and quantum linear synthesis (`4.575972 n` / `4 n`) -/

/-- **Reversible and quantum linear synthesis lower bound under `LayoutBound d A` (`d ∈ {3, 4}`).**
Every quantum circuit `C` on ANY number of qubits `N` (with unlimited clean ancillas restored to
`x₀` and unlimited single-qubit `U(2)` gates) computing the nonconstructively chosen invertible
linear bijection `boolMulVec (robustBijectiveMatrix n)` (selected via `Classical.choose`) on
`e : Fin n ↪ Fin N` requires more than `(1 + 1 / A - ε) n` two-qubit gates. -/
theorem eventually_lt_twoQubitCount_linear_of_layoutBound {d : ℕ} (hd : d = 3 ∨ d = 4)
    {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound d A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N),
      (if d = 3 then AllBondRankTwo C else TwoLocal C) →
      (∀ x, C.run (Quantum.glue e x x₀) =
        Quantum.ket (Quantum.glue e (boolMulVec (robustBijectiveMatrix n) x) x₀)) →
        (1 + 1 / A - ε) * n < twoQubitCount C := by
  have hev := eventually_compiledQuantumNet_contradiction hA hlayout (w_nat := 2)
    (c_slack := 1) (by norm_num) (c_edge := 1) (γ_coeff := 0) (by norm_num) hε le_rfl
    (by norm_num) (by rw [mul_zero]; positivity)
    (fun n => 2 * n) (fun n => by push_cast; rfl)
    (fun n => 2 * (2 * (2 * Nat.sqrt n + 1)) + 1)
    (fun n => by omega)
    (fun n => linBlockMatrix n (robustBijectiveMatrix n) +
      (linBlockMatrix n (robustBijectiveMatrix n))ᵀ)
    (fun n U hU => by
      exact_mod_cast half_le_cutRank_linBlockMatrix n (robustBijectiveMatrix_submatrixRobust n) hU)
  filter_upwards [hev] with n ⟨hn24, hcontra⟩ N e x₀ C hmodel hlin
  by_contra! hsize
  obtain ⟨net⟩ := exists_compiledQuantumNet hd e (e ⟨0, by omega⟩) hmodel
  refine hcontra net net.leaf2n (by convert hsize using 3; push_cast; field_simp) (fun P => ?_)
    net.cycleRank_leaf2n_le
  simp only [one_mul, zero_mul, zero_add, Nat.cast_one]
  exact_mod_cast net.cutRank_linBlockMatrix_le x₀ hlin P

/-- **Median-switched reversible and quantum linear synthesis lower bound (`4.575972 n`).**
Synthesizing `boolMulVec (robustBijectiveMatrix n)` using bond-rank-two two-qubit gates (`CNOT`,
`CZ`, `Gate.controlled V`) plus arbitrary free single-qubit `U(2)` gates and clean ancillas requires
more than `(1 + 2π / (3 arccos (5 / 6)) - ε) n ≈ 4.575972 n` two-qubit gates. -/
theorem eventually_lt_twoQubitCount_linear_switched {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (∀ x, C.run (Quantum.glue e x x₀) =
        Quantum.ket (Quantum.glue e (boolMulVec (robustBijectiveMatrix n) x) x₀)) →
        (1 + 2 * π / (3 * arccos (5 / 6)) - ε) * n < twoQubitCount C := by
  rw [← Switched.one_add_inv_two_mul_switchedCoefficient]
  exact eventually_lt_twoQubitCount_linear_of_layoutBound (Or.inl rfl)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hε

/-- **Rational `(4.57597 - ε) n` reversible and quantum linear synthesis lower bound.** -/
theorem eventually_lt_twoQubitCount_linear_457597 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), AllBondRankTwo C →
      (∀ x, C.run (Quantum.glue e x x₀) =
        Quantum.ket (Quantum.glue e (boolMulVec (robustBijectiveMatrix n) x) x₀)) →
        (457597 / 100000 - ε) * n < twoQubitCount C :=
  (eventually_lt_twoQubitCount_linear_switched hε).mono fun n hn N e x₀ C hC hlin =>
    (rat_sub_mul_le_switched (k := 1) one_pos n (by ring) (by norm_num)).trans_lt
      (hn N e x₀ C hC hlin)

/-- **Unconditional general two-local `U(4)` linear synthesis lower bound `(4 - ε) n`**
via `layoutBound_four_one_third` (`A₄ = 1 / 3`), with clean ancillas restored exactly. -/
theorem eventually_lt_twoQubitCount_linear_twoLocal {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
      (C : Quantum.Circuit N), TwoLocal C →
      (∀ x, C.run (Quantum.glue e x x₀) =
        Quantum.ket (Quantum.glue e (boolMulVec (robustBijectiveMatrix n) x) x₀)) →
        (4 - ε) * n < twoQubitCount C := by
  rw [show (4 : ℝ) = 1 + 1 / (1 / 3) by norm_num]
  exact eventually_lt_twoQubitCount_linear_of_layoutBound (Or.inr rfl) (by norm_num)
    layoutBound_four_one_third hε

end MainBounds

end Cslib.Circuits.Frontier
