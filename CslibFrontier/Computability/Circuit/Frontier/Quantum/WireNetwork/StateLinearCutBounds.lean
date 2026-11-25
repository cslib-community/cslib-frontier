/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
-- `import all`: reads private `ActiveGate`, `evalAct` from `ActiveSplit` and private
-- cut-factorization, real-matrix, and `2n`-block helpers from `Observables`.
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.ActiveSplit
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.Observables
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
import CslibFrontier.Computability.Circuit.Quantum.Input
import CslibFrontier.Computability.Communication.QuadFormSignRank
import CslibFrontier.Foundations.LinearAlgebra.Matrix.SubmatrixRobust
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Single-cut transition-amplitude, phase-state fidelity, and linear synthesis bounds

Internal transition-amplitude cut factorization (`exists_run_glue_cut_factorization`), quadratic
phase-state preparation fidelity bound (`sq_fidelity_phaseState_mul_le_of_capped`), and Walsh–
Hadamard coherent `𝔽₂` linear synthesis cut-rank bound (`cutRank_linBlockMatrix_le_of_capped`).
-/

-- This proof-only companion is intentionally private; sibling WireNetwork modules use import all.
set_option linter.privateModule false

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset Kronecker

open Classical in
/-- Across any vertex cut `P` of a `CappedWireNet` `G`, the transition amplitude
`(C.run (Quantum.glue e x x₀)).ofLp (Quantum.glue e y x₀)` factors across `(X, Xᶜ)` and `(Y, Yᶜ)`
into `2 ^ |G.edgeCut P|` rank-one complex terms. -/
private theorem exists_run_glue_cut_factorization {n N : ℕ}
    {C : Quantum.Circuit N} {e : Fin n ↪ Fin N} (x₀ : Fin N → Bool)
    {A : Set (Fin N)} (heA : Set.range e ⊆ A)
    {L : List (ActiveGate ↥A)} {inactU : {q : Fin N // q ∉ A} → unitaryGroup Bool ℂ}
    (hsplit : ∀ y x : Fin N → Bool,
      (C.matrix : Matrix _ _ ℂ) y x =
        (evalAct L : Matrix (↥A → Bool) (↥A → Bool) ℂ) (A.domRestrict y) (A.domRestrict x) *
          ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (y q.1) (x q.1))
    {V_fin E_fin : Type} [Fintype V_fin] [Fintype E_fin] [DecidableEq E_fin]
    (G : Multigraph V_fin E_fin) (inVert outVert : ↥A ↪ V_fin)
    (F : V_fin → (↥A → Bool) → (↥A → Bool) → (E_fin → Bool) → ℂ)
    (hcontract : ∀ y x : ↥A → Bool, evalAct L y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ)
    (hloc_in : ∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ)
    (hloc_out : ∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ)
    (hloc_edge : ∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)
    (P : Set V_fin) :
    let X : Set (Fin n) := {i | inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
    let Y : Set (Fin n) := {j | outVert ⟨e j, heA ⟨j, rfl⟩⟩ ∈ P}
    let Ecut : Set E_fin := G.edgeCut P
    ∃ (Φ' : (X → Bool) → (Y → Bool) → (Ecut → Bool) → ℂ)
      (Ψ' : (↥Xᶜ → Bool) → (↥Yᶜ → Bool) → (Ecut → Bool) → ℂ),
      ∀ (xP : X → Bool) (xPc : ↥Xᶜ → Bool) (yP : Y → Bool) (yPc : ↥Yᶜ → Bool),
        (C.run (Quantum.glue e
            ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (xP, xPc)) x₀)).ofLp
          (Quantum.glue e
            ((Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).symm (yP, yPc)) x₀) =
        ∑ τ : Ecut → Bool, Φ' xP yP τ * Ψ' xPc yPc τ := by
  classical
  intro X Y Ecut
  obtain ⟨Φ, Ψ, hamp⟩ := amplitude_cut_factorization G inVert outVert F
    hcontract hloc_in hloc_out hloc_edge P
  let XP : Set ↥A := {q | inVert q ∈ P}
  let YP : Set ↥A := {q | outVert q ∈ P}
  let glueX := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  let glueY := (Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).symm
  let c_inact : ℂ := ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (x₀ q.1) (x₀ q.1)
  obtain ⟨liftXP, liftXPc, hdom_XP', hdom_XPc'⟩ := exists_lift_domRestrict_glue e x₀ heA XP
  obtain ⟨liftYP, liftYPc, hdom_YP', hdom_YPc'⟩ := exists_lift_domRestrict_glue e x₀ heA YP
  have hdom_XP (a : X → Bool) (b : ↥Xᶜ → Bool) :
      {q | inVert q ∈ P}.domRestrict (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) =
        liftXP a := hdom_XP' a b
  have hdom_XPc (a : X → Bool) (b : ↥Xᶜ → Bool) :
      {q | inVert q ∈ P}ᶜ.domRestrict (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) =
        liftXPc b := hdom_XPc' a b
  have hdom_YP (yP : Y → Bool) (yPc : ↥Yᶜ → Bool) :
      {q | outVert q ∈ P}.domRestrict (A.domRestrict (Quantum.glue e (glueY (yP, yPc)) x₀)) =
        liftYP yP := hdom_YP' yP yPc
  have hdom_YPc (yP : Y → Bool) (yPc : ↥Yᶜ → Bool) :
      {q | outVert q ∈ P}ᶜ.domRestrict (A.domRestrict (Quantum.glue e (glueY (yP, yPc)) x₀)) =
        liftYPc yPc := hdom_YPc' yP yPc
  refine ⟨fun xP yP τ => c_inact * Φ (liftXP xP) (liftYP yP) τ,
    fun xPc yPc τ => Ψ (liftXPc xPc) (liftYPc yPc) τ, fun xP xPc yP yPc => ?_⟩
  have hamp1 :=
    hamp (A.domRestrict (Quantum.glue e (glueX (xP, xPc)) x₀))
      (A.domRestrict (Quantum.glue e (glueY (yP, yPc)) x₀))
  rw [hdom_XP xP xPc, hdom_XPc xP xPc, hdom_YP yP yPc, hdom_YPc yP yPc] at hamp1
  rw [run_ofLp_eq_matrix_apply, hsplit, hamp1]
  have hcin : (∏ q : {q : Fin N // q ∉ A},
      (inactU q : Matrix Bool Bool ℂ) (Quantum.glue e (glueY (yP, yPc)) x₀ q.1)
        (Quantum.glue e (glueX (xP, xPc)) x₀ q.1)) = c_inact := by
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [Quantum.glue_of_not e _ x₀ (fun i hi => q.2 (heA ⟨i, hi⟩)),
      Quantum.glue_of_not e _ x₀ (fun i hi => q.2 (heA ⟨i, hi⟩))]
  rw [hcin, mul_comm _ c_inact, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring


open Classical in
/-- Single-cut state-preparation fidelity inequality for `phaseState Q e x₀`: across any cut `P`
inducing `Y = {i | outVert ⟨e i, _⟩ ∈ P}`,
`‖inner ℂ (phaseState Q e x₀) (C.run x₀)‖ ^ 2 * 2 ^ (Q + Qᵀ).cutRank Y ≤ 4 * 2 ^ |G.edgeCut P|`. -/
private theorem sq_fidelity_phaseState_mul_le_of_capped {n N : ℕ}
    {C : Quantum.Circuit N} {e : Fin n ↪ Fin N} {x₀ : Fin N → Bool}
    {A : Set (Fin N)} (heA : Set.range e ⊆ A)
    {L : List (ActiveGate ↥A)} {inactU : {q : Fin N // q ∉ A} → unitaryGroup Bool ℂ}
    (hsplit : ∀ y x : Fin N → Bool,
      (C.matrix : Matrix _ _ ℂ) y x =
        (evalAct L : Matrix (↥A → Bool) (↥A → Bool) ℂ) (A.domRestrict y) (A.domRestrict x) *
          ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (y q.1) (x q.1))
    {V_fin E_fin : Type} [Fintype V_fin] [Fintype E_fin] [DecidableEq E_fin]
    (G : Multigraph V_fin E_fin) (inVert outVert : ↥A ↪ V_fin)
    (F : V_fin → (↥A → Bool) → (↥A → Bool) → (E_fin → Bool) → ℂ)
    (hcontract : ∀ y x : ↥A → Bool, evalAct L y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ)
    (hloc_in : ∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ)
    (hloc_out : ∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ)
    (hloc_edge : ∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (P : Set V_fin) :
    let Y : Set (Fin n) := {i | outVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
    ‖inner ℂ (phaseState Q e x₀) (C.run x₀)‖ ^ 2 * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y ≤
      4 * (2 : ℝ) ^ (G.edgeCut P).ncard := by
  classical
  intro Y
  let X : Set (Fin n) := {i | inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
  let Ecut : Set E_fin := G.edgeCut P
  let glueY := (Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).symm
  obtain ⟨Φ', Ψ', hrun_cut⟩ := exists_run_glue_cut_factorization x₀ heA hsplit G inVert outVert F
    hcontract hloc_in hloc_out hloc_edge P
  let p₀ := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool) (x₀ ∘ e)
  let amp (z : Fin n → Bool) : ℂ := (C.run x₀).ofLp (Quantum.glue e z x₀)
  have hamp_z (a : Y → Bool) (b : ↥Yᶜ → Bool) :
      amp (glueY (a, b)) = ∑ τ : Ecut → Bool, Φ' p₀.1 a τ * Ψ' p₀.2 b τ := by
    have hx₀ : Quantum.glue e ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm p₀) x₀ =
        x₀ := by
      rw [Equiv.symm_apply_apply]
      ext q
      by_cases h : ∃ i, e i = q
      · obtain ⟨i, rfl⟩ := h; exact Quantum.glue_apply_emb e (x₀ ∘ e) x₀ i
      · exact Quantum.glue_of_not e (x₀ ∘ e) x₀ fun i hi => h ⟨i, hi⟩
    have hrc := hrun_cut p₀.1 p₀.2 a b
    dsimp only [amp, glueY]
    rwa [Prod.mk.eta, hx₀] at hrc
  let U_re := realCutLeft (Φ' p₀.1)
  let V_re := realCutRight (Ψ' p₀.2)
  let U_im := realCutLeft (fun a τ => -Complex.I * Φ' p₀.1 a τ)
  let V_im := realCutRight (Ψ' p₀.2)
  have hUV_re (a : Y → Bool) (b : ↥Yᶜ → Bool) : (U_re * V_re) a b = (amp (glueY (a, b))).re := by
    rw [hamp_z, realCutLeft_mul_realCutRight_apply]
  have hUV_im (a : Y → Bool) (b : ↥Yᶜ → Bool) : (U_im * V_im) a b = (amp (glueY (a, b))).im := by
    rw [hamp_z, realCutLeft_neg_I_mul_realCutRight_apply]
  have hnorm_sum_le : (∑ a : Y → Bool, ∑ b : ↥Yᶜ → Bool,
      ((U_re * V_re) a b ^ 2 + (U_im * V_im) a b ^ 2)) ≤ 1 := by
    have h1 (a : Y → Bool) (b : ↥Yᶜ → Bool) :
        (U_re * V_re) a b ^ 2 + (U_im * V_im) a b ^ 2 = ‖amp (glueY (a, b))‖ ^ 2 := by
      rw [hUV_re, hUV_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    simp_rw [h1]
    rw [← Fintype.sum_prod_type']
    have hbij : (∑ p : (Y → Bool) × (↥Yᶜ → Bool), ‖amp (glueY (p.1, p.2))‖ ^ 2) =
        ∑ z : Fin n → Bool, ‖(C.run x₀).ofLp (Quantum.glue e z x₀)‖ ^ 2 :=
      Fintype.sum_equiv glueY _ _ fun p => by simp only [Prod.mk.eta, amp]
    rw [hbij, ← Finset.sum_image (f := fun y => ‖(C.run x₀).ofLp y‖ ^ 2)
      (fun _ _ _ _ h => glue_left_injective e x₀ h)]
    calc ∑ y ∈ Finset.univ.image (fun z => Quantum.glue e z x₀), ‖(C.run x₀).ofLp y‖ ^ 2
        ≤ Quantum.measureProb (C.run x₀) Finset.univ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
      _ = ‖C.run x₀‖ ^ 2 := Quantum.measureProb_univ _
      _ = 1 := by rw [Quantum.Circuit.norm_run, one_pow]
  set S_mat := Communication.signMatrix ℝ (fun a' b' => BitString.quadForm Q (glueY (a', b')))
  have hinner_eq : inner ℂ (phaseState Q e x₀) (C.run x₀) =
      (((1 / √2) ^ n : ℝ) : ℂ) *
        (((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b : ℝ) : ℂ) +
          Complex.I * ((∑ a, ∑ b, S_mat a b * (U_im * V_im) a b : ℝ) : ℂ)) := by
    rw [PiLp.inner_apply]
    have hsum_z : (∑ y : Fin N → Bool, inner ℂ ((phaseState Q e x₀).ofLp y) ((C.run x₀).ofLp y)) =
        ∑ z : Fin n → Bool,
          (((1 / √2) ^ n : ℝ) : ℂ) *
            ((if BitString.quadForm Q z then -1 else 1) * amp z) := by
      have hite (y : Fin N → Bool) :
          inner ℂ ((phaseState Q e x₀).ofLp y) ((C.run x₀).ofLp y) =
            if Quantum.AgreeOff e y x₀ then
              inner ℂ ((((1 / √2) ^ n : ℝ) : ℂ) * (if BitString.quadForm Q (y ∘ e) then -1 else 1))
                ((C.run x₀).ofLp y)
            else 0 := by
        rw [phaseState, Quantum.embedState_apply]
        split_ifs <;> simp_all
      simp_rw [hite]
      rw [Quantum.sum_agreeOff e x₀]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Quantum.glue_comp, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
      have hconj_sign : (starRingEnd ℂ) (if BitString.quadForm Q z then (-1 : ℂ) else 1) =
          if BitString.quadForm Q z then -1 else 1 := by
        cases BitString.quadForm Q z <;> simp
      rw [hconj_sign]
      dsimp only [amp]
      ring
    rw [hsum_z, ← Finset.mul_sum]
    congr 1
    refine (Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool) _
      (fun p => (if BitString.quadForm Q (glueY p) then (-1 : ℂ) else 1) * amp (glueY p))
      (fun z => congrArg (fun w => (if BitString.quadForm Q w then (-1 : ℂ) else 1) * amp w)
        ((Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).symm_apply_apply z).symm)).trans ?_
    rw [Fintype.sum_prod_type]
    push_cast
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hsign_eq : (if BitString.quadForm Q (glueY (a, b)) then (-1 : ℂ) else 1) =
        ((S_mat a b : ℝ) : ℂ) := by
      simp only [S_mat, Communication.signMatrix_apply]
      cases BitString.quadForm Q (glueY (a, b)) <;> simp
    rw [← Complex.re_add_im (amp (glueY (a, b))), hUV_re, hUV_im, hsign_eq]
    ring
  have hnorm_inner : ‖inner ℂ (phaseState Q e x₀) (C.run x₀)‖ ^ 2 =
      (1 / (2 : ℝ) ^ n) *
        ((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 +
          (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2) := by
    rw [hinner_eq, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / √2) ^ n)]
    have h12 : ((1 / √2) ^ n) ^ 2 = 1 / (2 : ℝ) ^ n := by
      rw [sq_one_div_sqrt_two_pow, div_pow, one_pow]
    have hre_im (x_r y_r : ℝ) : ‖(x_r : ℂ) + Complex.I * (y_r : ℂ)‖ ^ 2 = x_r ^ 2 + y_r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, one_mul, zero_add]
      ring
    rw [h12, hre_im]
  have hfrob (U_m : Matrix (Y → Bool) ((Ecut → Bool) × Bool) ℝ)
      (V_m : Matrix ((Ecut → Bool) × Bool) (↥Yᶜ → Bool) ℝ) :
      (∑ a, ∑ b, S_mat a b * (U_m * V_m) a b) ^ 2 * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y ≤
        (2 * (2 : ℝ) ^ Ecut.ncard) * (2 : ℝ) ^ n * ∑ a, ∑ b, (U_m * V_m) a b ^ 2 :=
    (Communication.sq_sum_mul_signMatrix_quadForm_le_card_of_mul Q Y U_m V_m).trans_eq
      (by rw [Fintype.card_fin, card_cut_prod_bool Ecut])
  rw [hnorm_inner]
  have hsum_frob : ((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 +
        (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2) * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y ≤
      2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n := by
    calc ((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 +
            (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2) * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y
        ≤ 2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n *
            (∑ a, ∑ b, (U_re * V_re) a b ^ 2 + ∑ a, ∑ b, (U_im * V_im) a b ^ 2) := by
          rw [add_mul, mul_add]
          exact add_le_add (hfrob U_re V_re) (hfrob U_im V_im)
      _ = 2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n *
            ∑ a, ∑ b, ((U_re * V_re) a b ^ 2 + (U_im * V_im) a b ^ 2) := by
          simp_rw [Finset.sum_add_distrib]
      _ ≤ 2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n * 1 := by gcongr
      _ = 2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n := mul_one _
  calc 1 / (2 : ℝ) ^ n *
        ((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 +
          (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2) *
        (2 : ℝ) ^ (Q + Qᵀ).cutRank Y
      = 1 / (2 : ℝ) ^ n * (((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 +
          (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2) * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y) := by ring
    _ ≤ 1 / (2 : ℝ) ^ n * (2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n) := by gcongr
    _ = 2 * (2 : ℝ) ^ Ecut.ncard := by field_simp
    _ ≤ 4 * (2 : ℝ) ^ Ecut.ncard := by linarith [pow_pos (two_pos : (0 : ℝ) < 2) Ecut.ncard]

open Classical in
/-- Single-cut linear synthesis bound via Walsh-Hadamard duality on `CappedWireNet`: if `C`
coherently computes `|Quantum.glue e x x₀⟩ ↦ |Quantum.glue e (boolMulVec R x) x₀⟩`, then across any
cut `P`, the joint input/output cut `U ⊆ Fin (2 * n)` satisfies
`(linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U ≤ |G.edgeCut P| + 1`. -/
private theorem cutRank_linBlockMatrix_le_of_capped {n N : ℕ}
    {C : Quantum.Circuit N} {e : Fin n ↪ Fin N} {x₀ : Fin N → Bool}
    {A : Set (Fin N)} (heA : Set.range e ⊆ A)
    {L : List (ActiveGate ↥A)} {inactU : {q : Fin N // q ∉ A} → unitaryGroup Bool ℂ}
    (hsplit : ∀ y x : Fin N → Bool,
      (C.matrix : Matrix _ _ ℂ) y x =
        (evalAct L : Matrix (↥A → Bool) (↥A → Bool) ℂ) (A.domRestrict y) (A.domRestrict x) *
          ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (y q.1) (x q.1))
    {V_fin E_fin : Type} [Fintype V_fin] [Fintype E_fin] [DecidableEq E_fin]
    (G : Multigraph V_fin E_fin) (inVert outVert : ↥A ↪ V_fin)
    (F : V_fin → (↥A → Bool) → (↥A → Bool) → (E_fin → Bool) → ℂ)
    (hcontract : ∀ y x : ↥A → Bool, evalAct L y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ)
    (hloc_in : ∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ)
    (hloc_out : ∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ)
    (hloc_edge : ∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)
    (R : Matrix (Fin n) (Fin n) (ZMod 2))
    (hlin : ∀ x : Fin n → Bool,
      C.run (Quantum.glue e x x₀) = Quantum.ket (Quantum.glue e (boolMulVec R x) x₀))
    (leaf2n : Fin (2 * n) ↪ V_fin)
    (hleaf_in : ∀ i : Fin n, leaf2n (inl2n n i) = inVert ⟨e i, heA ⟨i, rfl⟩⟩)
    (hleaf_out : ∀ j : Fin n, leaf2n (inr2n n j) = outVert ⟨e j, heA ⟨j, rfl⟩⟩)
    (P : Set V_fin) :
    (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank {k | leaf2n k ∈ P} ≤
      (G.edgeCut P).ncard + 1 := by
  classical
  let Ecut : Set E_fin := G.edgeCut P
  let U : Set (Fin (2 * n)) := {k | leaf2n k ∈ P}
  let X : Set (Fin n) := {i | inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
  let Y : Set (Fin n) := {j | outVert ⟨e j, heA ⟨j, rfl⟩⟩ ∈ P}
  let glueU := (Equiv.piEquivPiSubtypeProd (· ∈ U) fun _ => Bool).symm
  let glueX := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  let glueY := (Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).symm
  obtain ⟨Φ', Ψ', hrun_cut⟩ := exists_run_glue_cut_factorization x₀ heA hsplit G inVert outVert F
    hcontract hloc_in hloc_out hloc_edge P
  have hamp_wx (xP : X → Bool) (xPc : ↥Xᶜ → Bool) (wP : Y → Bool) (wPc : ↥Yᶜ → Bool) :
      (if glueY (wP, wPc) = boolMulVec R (glueX (xP, xPc)) then (1 : ℂ) else 0) =
        ∑ τ : Ecut → Bool, Φ' xP wP τ * Ψ' xPc wPc τ := by
    have hinj : (Quantum.glue e (glueY (wP, wPc)) x₀ =
        Quantum.glue e (boolMulVec R (glueX (xP, xPc))) x₀) ↔
        glueY (wP, wPc) = boolMulVec R (glueX (xP, xPc)) :=
      ⟨fun h => glue_left_injective e x₀ h, fun h => congrArg (Quantum.glue e · x₀) h⟩
    refine (if_congr hinj.symm rfl rfl).trans ?_
    simpa only [hlin, Quantum.ket_apply] using hrun_cut xP xPc wP wPc
  have hglue_emb (emb : Fin n → Fin (2 * n)) (S : Set (Fin n)) (hemb : ∀ i, emb i ∈ U ↔ i ∈ S)
      (a : U → Bool) (b : ↥Uᶜ → Bool) (i : Fin n) :
      glueU (a, b) (emb i) =
        (Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Bool).symm
          ((fun k => a ⟨emb k.1, (hemb k.1).mpr k.2⟩),
           (fun k => b ⟨emb k.1, fun h => k.2 ((hemb k.1).mp h)⟩)) i := by
    simp only [glueU, Equiv.piEquivPiSubtypeProd_symm_apply]
    by_cases hi : i ∈ S
    · simp only [hi, (hemb i).mpr hi, ↓reduceDIte]
    · have hiU : emb i ∉ U := fun h => hi ((hemb i).mp h)
      simp only [hi, hiU, ↓reduceDIte]
  have hinl_mem (i : Fin n) : inl2n n i ∈ U ↔ i ∈ X := by
    change leaf2n (inl2n n i) ∈ P ↔ inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P; rw [hleaf_in]
  have hinr_mem (j : Fin n) : inr2n n j ∈ U ↔ j ∈ Y := by
    change leaf2n (inr2n n j) ∈ P ↔ outVert ⟨e j, heA ⟨j, rfl⟩⟩ ∈ P; rw [hleaf_out]
  let x_of_a (a : U → Bool) : X → Bool := fun i => a ⟨inl2n n i.1, (hinl_mem i.1).mpr i.2⟩
  let y_of_a (a : U → Bool) : Y → Bool := fun j => a ⟨inr2n n j.1, (hinr_mem j.1).mpr j.2⟩
  let x_of_b (b : ↥Uᶜ → Bool) : ↥Xᶜ → Bool :=
    fun i => b ⟨inl2n n i.1, fun h => i.2 ((hinl_mem i.1).mp h)⟩
  let y_of_b (b : ↥Uᶜ → Bool) : ↥Yᶜ → Bool :=
    fun j => b ⟨inr2n n j.1, fun h => j.2 ((hinr_mem j.1).mp h)⟩
  have hglue_inl (a : U → Bool) (b : ↥Uᶜ → Bool) :
      (fun i => glueU (a, b) (inl2n n i)) = glueX (x_of_a a, x_of_b b) :=
    funext (hglue_emb (inl2n n) X hinl_mem a b)
  have hglue_inr (a : U → Bool) (b : ↥Uᶜ → Bool) (j : Fin n) :
      glueU (a, b) (inr2n n j) = glueY (y_of_a a, y_of_b b) j :=
    hglue_emb (inr2n n) Y hinr_mem a b j
  let Φ_lin (a : U → Bool) (τ : Ecut → Bool) : ℂ :=
    ∑ wP : Y → Bool,
      (∏ j : Y, if y_of_a a j && wP j then (-1 : ℂ) else 1) * Φ' (x_of_a a) wP τ
  let Ψ_lin (b : ↥Uᶜ → Bool) (τ : Ecut → Bool) : ℂ :=
    ∑ wPc : ↥Yᶜ → Bool,
      (∏ j : ↥Yᶜ, if y_of_b b j && wPc j then (-1 : ℂ) else 1) * Ψ' (x_of_b b) wPc τ
  set S_mat := Communication.signMatrix ℝ
    (fun a' b' => BitString.quadForm (linBlockMatrix n R) (glueU (a', b')))
  have hsum_τ (a : U → Bool) (b : ↥Uᶜ → Bool) :
      (∑ τ : Ecut → Bool, Φ_lin a τ * Ψ_lin b τ) = ((S_mat a b : ℝ) : ℂ) := by
    have hswap : (∑ τ : Ecut → Bool, Φ_lin a τ * Ψ_lin b τ) =
        ∑ wP : Y → Bool, ∑ wPc : ↥Yᶜ → Bool,
          ((∏ j : Y, if y_of_a a j && wP j then (-1 : ℂ) else 1) *
            (∏ j : ↥Yᶜ, if y_of_b b j && wPc j then (-1 : ℂ) else 1)) *
          ∑ τ : Ecut → Bool, Φ' (x_of_a a) wP τ * Ψ' (x_of_b b) wPc τ := by
      dsimp only [Φ_lin, Ψ_lin]
      simp_rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun wP _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun wPc _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [hswap]
    simp_rw [← hamp_wx (x_of_a a) (x_of_b b)]
    have hprod_y (wP : Y → Bool) (wPc : ↥Yᶜ → Bool) :
        (∏ j : Y, if y_of_a a j && wP j then (-1 : ℂ) else 1) *
          (∏ j : ↥Yᶜ, if y_of_b b j && wPc j then (-1 : ℂ) else 1) =
        ∏ j : Fin n, if glueU (a, b) (inr2n n j) && glueY (wP, wPc) j then (-1 : ℂ) else 1 := by
      rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ Y)
        (fun j => if glueU (a, b) (inr2n n j) && glueY (wP, wPc) j then (-1 : ℂ) else 1)]
      congr 1
      · refine Finset.prod_congr rfl fun j _ => ?_
        simp only [hglue_inr, glueY, Equiv.piEquivPiSubtypeProd_symm_apply, j.2, ↓reduceDIte]
      · refine Finset.prod_congr rfl fun j _ => ?_
        have hnj : j.1 ∉ Y := j.2
        simp only [hglue_inr, glueY, Equiv.piEquivPiSubtypeProd_symm_apply, hnj, ↓reduceDIte]; rfl
    simp_rw [hprod_y, ← Fintype.sum_prod_type']
    refine (Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool)
      (fun w =>
        (∏ j : Fin n, if glueU (a, b) (inr2n n j) && w j then (-1 : ℂ) else 1) *
          if w = boolMulVec R (glueX (x_of_a a, x_of_b b)) then 1 else 0)
      (fun p =>
        (∏ j : Fin n, if glueU (a, b) (inr2n n j) && glueY (p.1, p.2) j then (-1 : ℂ) else 1) *
          if glueY (p.1, p.2) = boolMulVec R (glueX (x_of_a a, x_of_b b)) then 1 else 0)
      (fun w => congrArg
        (fun z => (∏ j : Fin n, if glueU (a, b) (inr2n n j) && z j then (-1 : ℂ) else 1) *
          if z = boolMulVec R (glueX (x_of_a a, x_of_b b)) then 1 else 0)
        ((Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).symm_apply_apply w).symm)).symm.trans
      ?_
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      ← hglue_inl a b]
    have hquad := BitString.quadForm_eq_of_submatrix (inr2n_injective n) (inl2n_injective n)
      (Matrix.submatrix_extendBlock (inr2n_injective n) (inl2n_injective n) R)
      (fun _ _ h => Matrix.extendBlock_eq_zero R h) (glueU (a, b))
    change BitString.quadForm (linBlockMatrix n R) (glueU (a, b)) = _ at hquad
    have hsgn := sign_dotProduct_eq_prod Finset.univ (fun j => glueU (a, b) (inr2n n j))
      (R *ᵥ fun i => BitString.bitVal (ZMod 2) (glueU (a, b) (inl2n n i)))
    simp only [dotProduct] at hquad
    refine hsgn.symm.trans ?_
    rw [← hquad]
    simp only [S_mat, Communication.signMatrix_apply]
    cases BitString.quadForm (linBlockMatrix n R) (glueU (a, b)) <;> simp
  let U_re := realCutLeft Φ_lin
  let V_re := realCutRight Ψ_lin
  have hUV (a : U → Bool) (b : ↥Uᶜ → Bool) : (U_re * V_re) a b = S_mat a b := by
    rw [realCutLeft_mul_realCutRight_apply, hsum_τ, Complex.ofReal_re]
  have hfrob :
      (∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 *
        (2 : ℝ) ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U ≤
      (2 * (2 : ℝ) ^ Ecut.ncard) * (2 : ℝ) ^ (2 * n) * ∑ a, ∑ b, (U_re * V_re) a b ^ 2 := by
    have h :=
      Communication.sq_sum_mul_signMatrix_quadForm_le_card_of_mul (linBlockMatrix n R) U U_re V_re
    exact h.trans_eq (by rw [Fintype.card_fin, card_cut_prod_bool Ecut])
  have hS_sq (a : U → Bool) (b : ↥Uᶜ → Bool) : S_mat a b ^ 2 = 1 := by
    simp only [S_mat, Communication.signMatrix_apply]
    cases BitString.quadForm (linBlockMatrix n R) (glueU (a, b)) <;> norm_num
  have hcard_ab := sum_prod_subtype_compl_one U
  have hsum1 : (∑ a : U → Bool, ∑ b : ↥Uᶜ → Bool, S_mat a b * (U_re * V_re) a b) =
      (2 : ℝ) ^ (2 * n) := by simp_rw [hUV, ← sq, hS_sq]; exact hcard_ab
  have hsum2 : (∑ a : U → Bool, ∑ b : ↥Uᶜ → Bool, (U_re * V_re) a b ^ 2) =
      (2 : ℝ) ^ (2 * n) := by simp_rw [hUV, hS_sq]; exact hcard_ab
  have hfrob' :
      ((2 : ℝ) ^ (2 * n)) ^ 2 * (2 : ℝ) ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U ≤
      (2 * (2 : ℝ) ^ Ecut.ncard) * (2 : ℝ) ^ (2 * n) * (2 : ℝ) ^ (2 * n) :=
    (congrArg (fun x => x ^ 2 * _) hsum1.symm).trans_le
      (hfrob.trans_eq (congrArg (2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ (2 * n) * ·) hsum2))
  have h2pos : (0 : ℝ) < ((2 : ℝ) ^ (2 * n)) ^ 2 := by positivity
  have hpow_r : (2 : ℝ) ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U ≤
      (2 : ℝ) ^ (Ecut.ncard + 1) := by
    refine le_of_mul_le_mul_right ?_ h2pos
    calc (2 : ℝ) ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U *
            ((2 : ℝ) ^ (2 * n)) ^ 2
        = ((2 : ℝ) ^ (2 * n)) ^ 2 *
            (2 : ℝ) ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U := mul_comm _ _
      _ ≤ (2 * (2 : ℝ) ^ Ecut.ncard) * (2 : ℝ) ^ (2 * n) * (2 : ℝ) ^ (2 * n) := hfrob'
      _ = (2 : ℝ) ^ (Ecut.ncard + 1) * ((2 : ℝ) ^ (2 * n)) ^ 2 := by
          rw [pow_succ' (2 : ℝ) Ecut.ncard]; ring
  have hpow_nat : 2 ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U ≤
      2 ^ (Ecut.ncard + 1) := by exact_mod_cast hpow_r
  dsimp only [U, Ecut] at hpow_nat
  by_contra! hgt
  have := Nat.pow_lt_pow_right one_lt_two hgt
  omega


end Cslib.Circuits.Frontier
