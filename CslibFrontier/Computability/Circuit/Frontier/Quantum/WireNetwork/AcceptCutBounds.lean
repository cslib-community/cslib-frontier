/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
-- `import all`: reads private `ActiveGate`, `evalAct` from `ActiveSplit` and private
-- `amplitude_cut_factorization`, `exists_lift_domRestrict_glue`, `realCutLeft`, `realCutRight`,
-- `run_ofLp_eq_matrix_apply`, `sum_prod_subtype_compl_one` from `Observables`.
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.ActiveSplit
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.Observables
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
import CslibFrontier.Computability.Circuit.Quantum.Input
import CslibFrontier.Computability.Communication.QuadFormSignRank
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Data.Fintype.Sum

/-!
# Single-cut acceptance-probability, correlation, and sign-rank bounds

Internal bilinear real factorization of single-qubit acceptance probabilities across any vertex cut
`P` (`exists_quantumAcceptProb_affine_mul`), yielding single-cut `BQP` quadratic correlation
(`sq_quantumCorrelation_mul_le_of_capped`) and `UQP` sign-rank (`signRank_uqp_le_of_capped`) bounds.
-/

-- This proof-only companion is intentionally private; sibling WireNetwork modules use import all.
set_option linter.privateModule false

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset Kronecker

open Classical in
/-- Across any vertex cut `P` of a `CappedWireNet` `G` inducing `X = {i | inVert ⟨e i, _⟩ ∈ P}`,
any affine transform `α_coef * quantumAcceptProb C q_out e x₀ + β_coef` factors as `U_mat * V_mat`
of inner dimension at most `3 * 4 ^ |G.edgeCut P|`. -/
private theorem exists_quantumAcceptProb_affine_mul {n N : ℕ}
    {C : Quantum.Circuit N} {q_out : Fin N} {e : Fin n ↪ Fin N} (x₀ : Fin N → Bool)
    {A : Set (Fin N)} (heA : Set.range e ⊆ A) (hqA : q_out ∈ A)
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
    (P : Set V_fin) (α_coef β_coef : ℝ) :
    let X : Set (Fin n) := {i | inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
    ∃ (κ : Type) (_ : Fintype κ) (U_mat : Matrix (X → Bool) κ ℝ)
      (V_mat : Matrix κ (↥Xᶜ → Bool) ℝ),
      Fintype.card κ ≤ 3 * 4 ^ (G.edgeCut P).ncard ∧
      ∀ (a : X → Bool) (b : ↥Xᶜ → Bool),
        (U_mat * V_mat) a b =
          α_coef * quantumAcceptProb C q_out e x₀
            ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (a, b)) + β_coef := by
  classical
  intro X
  let Ecut : Set E_fin := G.edgeCut P
  let q_act : ↥A := ⟨q_out, hqA⟩
  have hprob_act (x : Fin n → Bool) :
      quantumAcceptProb C q_out e x₀ x =
        ∑ yA : ↥A → Bool, (if yA q_act = true then (1 : ℝ) else 0) *
          ‖(evalAct L : Matrix _ _ ℂ) yA (A.domRestrict (Quantum.glue e x x₀))‖ ^ 2 := by
    rw [quantumAcceptProb, Quantum.measureProb, Finset.sum_filter, Finset.sum_congr rfl fun y _ =>
      show (if y q_out = true then ‖(C.run (Quantum.glue e x x₀)).ofLp y‖ ^ 2 else 0) =
        (if y q_out = true then (1 : ℝ) else 0) *
          ‖(C.matrix : Matrix _ _ ℂ) y (Quantum.glue e x x₀)‖ ^ 2 by
        rw [run_ofLp_eq_matrix_apply C _ y]; split_ifs <;> ring]
    simp_rw [hsplit _ (Quantum.glue e x x₀), norm_mul, mul_pow]
    have hsum_split : (∑ y : Fin N → Bool,
        (if y q_out = true then (1 : ℝ) else 0) *
          (‖(evalAct L : Matrix _ _ ℂ) (A.domRestrict y)
              (A.domRestrict (Quantum.glue e x x₀))‖ ^ 2 *
            ‖∏ q : {q : Fin N // q ∉ A},
              (inactU q : Matrix Bool Bool ℂ) (y q.1) (Quantum.glue e x x₀ q.1)‖ ^ 2)) =
        (∑ yA : ↥A → Bool, (if yA q_act = true then (1 : ℝ) else 0) *
          ‖(evalAct L : Matrix _ _ ℂ) yA (A.domRestrict (Quantum.glue e x x₀))‖ ^ 2) *
        ∑ yAc : {q : Fin N // q ∉ A} → Bool,
          ∏ q : {q : Fin N // q ∉ A},
            ‖(inactU q : Matrix Bool Bool ℂ) (yAc q) (x₀ q.1)‖ ^ 2 := by
      let fA (yA : ↥A → Bool) : ℝ :=
        (if yA q_act = true then (1 : ℝ) else 0) *
          ‖(evalAct L : Matrix _ _ ℂ) yA (A.domRestrict (Quantum.glue e x x₀))‖ ^ 2
      let fAc (yAc : {q : Fin N // q ∉ A} → Bool) : ℝ :=
        ∏ q : {q : Fin N // q ∉ A}, ‖(inactU q : Matrix Bool Bool ℂ) (yAc q) (x₀ q.1)‖ ^ 2
      let eqvN : (Fin N → Bool) ≃ (↥A → Bool) × ({q : Fin N // q ∉ A} → Bool) :=
        Equiv.piEquivPiSubtypeProd (· ∈ A) fun _ => Bool
      refine (Fintype.sum_equiv eqvN _ (fun p => fA p.1 * fAc p.2) fun y => ?_).trans
        (by rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum])
      have heq_p : (∏ q : {q : Fin N // q ∉ A},
            (inactU q : Matrix Bool Bool ℂ) (y q.1) (Quantum.glue e x x₀ q.1)) =
          ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (y q.1) (x₀ q.1) :=
        Finset.prod_congr (M := ℂ) rfl fun q _ =>
          congrArg _ (Quantum.glue_of_not e x x₀ fun i hi => q.2 (heA ⟨i, hi⟩))
      dsimp only [fA, fAc]
      rw [show (eqvN y).1 = A.domRestrict y from rfl, show (eqvN y).2 = (fun q => y q.1) from rfl,
        show y q_out = (A.domRestrict y) q_act from rfl, heq_p, norm_prod, Finset.prod_pow]
      ring
    have hinact_one : (∑ yAc : {q : Fin N // q ∉ A} → Bool,
        ∏ q : {q : Fin N // q ∉ A},
          ‖(inactU q : Matrix Bool Bool ℂ) (yAc q) (x₀ q.1)‖ ^ 2) = 1 := by
      refine (Fintype.prod_sum fun q b =>
        ‖(inactU q : Matrix Bool Bool ℂ) b (x₀ q.1)‖ ^ 2).symm.trans
        (Finset.prod_eq_one fun q _ => ?_)
      have hcol := congrArg Complex.re
        (congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp (inactU q).2) (x₀ q.1)) (x₀ q.1))
      rw [Matrix.mul_apply, Matrix.one_apply] at hcol
      simp only [↓reduceIte, Complex.one_re, Fintype.sum_bool] at hcol
      have hnorm_re (b : Bool) : ‖(inactU q : Matrix Bool Bool ℂ) b (x₀ q.1)‖ ^ 2 =
          (star ((inactU q : Matrix Bool Bool ℂ)) (x₀ q.1) b *
            (inactU q : Matrix Bool Bool ℂ) b (x₀ q.1)).re := by
        simp only [Matrix.star_apply, RCLike.star_def]
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      rw [Fintype.sum_bool, hnorm_re false, hnorm_re true, ← Complex.add_re, hcol]
    rw [hsum_split, hinact_one, mul_one]
  obtain ⟨Φ, Ψ, hamp⟩ := amplitude_cut_factorization G inVert outVert F
    hcontract hloc_in hloc_out hloc_edge P
  let XP : Set ↥A := {q | inVert q ∈ P}
  let YP : Set ↥A := {q | outVert q ∈ P}
  let glueX := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  obtain ⟨liftXP, liftXPc, hdom_XP', hdom_XPc'⟩ := exists_lift_domRestrict_glue e x₀ heA XP
  have hdom_XP (a : X → Bool) (b : ↥Xᶜ → Bool) :
      {q | inVert q ∈ P}.domRestrict (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) =
        liftXP a := hdom_XP' a b
  have hdom_XPc (a : X → Bool) (b : ↥Xᶜ → Bool) :
      {q | inVert q ∈ P}ᶜ.domRestrict (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) =
        liftXPc b := hdom_XPc' a b
  let wYP (yP : YP → Bool) : ℝ :=
    if hq : q_act ∈ YP then (if yP ⟨q_act, hq⟩ = true then 1 else 0) else 1
  let wYPc (yPc : ↥YPᶜ → Bool) : ℝ :=
    if hq : q_act ∈ YPᶜ then (if yPc ⟨q_act, hq⟩ = true then 1 else 0) else 1
  have hw_prod (yA : ↥A → Bool) :
      (if yA q_act = true then (1 : ℝ) else 0) =
        wYP (YP.domRestrict yA) * wYPc (YPᶜ.domRestrict yA) := by
    by_cases hqP : q_act ∈ YP
    · have hnotPc : q_act ∉ YPᶜ := fun h => h hqP
      simp only [wYP, wYPc, hqP, hnotPc, ↓reduceDIte, Set.domRestrict_apply, mul_one]
      by_cases hy : yA q_act = true <;> simp only [hy, Bool.false_eq_true, ↓reduceIte]
    · have hPc : q_act ∈ YPᶜ := hqP
      simp only [wYP, wYPc, hqP, hPc, ↓reduceDIte, Set.domRestrict_apply, one_mul]
      by_cases hy : yA q_act = true <;> simp only [hy, Bool.false_eq_true, ↓reduceIte]
  let A_pair (a : X → Bool) (p : (Ecut → Bool) × (Ecut → Bool)) : ℂ :=
    ∑ yP : YP → Bool, (wYP yP : ℂ) * Φ (liftXP a) yP p.1 * star (Φ (liftXP a) yP p.2)
  let B_pair (b : ↥Xᶜ → Bool) (p : (Ecut → Bool) × (Ecut → Bool)) : ℂ :=
    ∑ yPc : ↥YPᶜ → Bool, (wYPc yPc : ℂ) * Ψ (liftXPc b) yPc p.1 * star (Ψ (liftXPc b) yPc p.2)
  have hprob_re (a : X → Bool) (b : ↥Xᶜ → Bool) :
      quantumAcceptProb C q_out e x₀ (glueX (a, b)) =
        (∑ p : (Ecut → Bool) × (Ecut → Bool), A_pair a p * B_pair b p).re := by
    rw [hprob_act]
    have hstep1 : (∑ yA : ↥A → Bool,
        (if yA q_act = true then (1 : ℝ) else 0) *
          ‖(evalAct L : Matrix _ _ ℂ) yA (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀))‖ ^ 2) =
        ∑ yA : ↥A → Bool,
          (∑ p : (Ecut → Bool) × (Ecut → Bool),
            ((wYP (YP.domRestrict yA) : ℂ) * Φ (liftXP a) (YP.domRestrict yA) p.1 *
                star (Φ (liftXP a) (YP.domRestrict yA) p.2)) *
            ((wYPc (YPᶜ.domRestrict yA) : ℂ) * Ψ (liftXPc b) (YPᶜ.domRestrict yA) p.1 *
                star (Ψ (liftXPc b) (YPᶜ.domRestrict yA) p.2))).re := by
      refine Finset.sum_congr rfl fun yA _ => ?_
      have h1 := hamp (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) yA
      rw [hdom_XP a b, hdom_XPc a b] at h1
      rw [hw_prod yA, show ‖(evalAct L : Matrix _ _ ℂ) yA
          (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀))‖ ^ 2 =
          ((evalAct L : Matrix _ _ ℂ) yA (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) *
            star ((evalAct L : Matrix _ _ ℂ) yA
              (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)))).re by
          rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re],
        h1, ← Complex.re_ofReal_mul]
      congr 1; dsimp only [YP, Ecut]
      rw [star_sum, Finset.sum_mul_sum, ← Fintype.sum_prod_type', Complex.ofReal_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [star_mul']; ring
    rw [hstep1]
    simp_rw [← Complex.re_sum]
    rw [Finset.sum_comm, Complex.re_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => congrArg Complex.re ?_
    dsimp only [A_pair, B_pair]
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ YP) fun _ => Bool) _ _ fun _ => rfl
  let κ := (((Ecut → Bool) × (Ecut → Bool)) × Bool) ⊕ Unit
  let U_mat : Matrix (X → Bool) κ ℝ := fun a idx => match idx with
    | .inl p => α_coef * realCutLeft A_pair a p
    | .inr () => β_coef
  let V_mat : Matrix κ (↥Xᶜ → Bool) ℝ := fun idx b => match idx with
    | .inl p => realCutRight B_pair p b
    | .inr () => 1
  refine ⟨κ, inferInstance, U_mat, V_mat, ?_, fun a b => ?_⟩
  · have hE : Fintype.card Ecut = (G.edgeCut P).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hc : Fintype.card κ = 2 * 4 ^ (G.edgeCut P).ncard + 1 := by
      simp only [κ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_unit, hE]
      rw [← pow_add, ← two_mul, pow_mul]; ring
    have := Nat.one_le_pow (G.edgeCut P).ncard 4 (by norm_num)
    omega
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Fintype.sum_unique, U_mat, V_mat, mul_one]
    rw [show (∑ x : ((Ecut → Bool) × (Ecut → Bool)) × Bool,
        α_coef * realCutLeft A_pair a x * realCutRight B_pair x b) =
        α_coef * (realCutLeft A_pair * realCutRight B_pair) a b by
      rw [Matrix.mul_apply, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring,
      realCutLeft_mul_realCutRight_apply, ← hprob_re]

open Classical in
/-- Single-cut `BQP` correlation inequality for a `CappedWireNet`: across any vertex cut `P` of `G`
inducing `X = {i | inVert ⟨e i, _⟩ ∈ P}`,
`quantumCorrelation {x | BitString.quadForm Q x} prob ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
  4 * 4 ^ |G.edgeCut P|`. -/
private theorem sq_quantumCorrelation_mul_le_of_capped {n N : ℕ}
    {C : Quantum.Circuit N} {q_out : Fin N} {e : Fin n ↪ Fin N} {x₀ : Fin N → Bool}
    {A : Set (Fin N)} (heA : Set.range e ⊆ A) (hqA : q_out ∈ A)
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
    let X : Set (Fin n) := {i | inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
    quantumCorrelation {x | BitString.quadForm Q x} (quantumAcceptProb C q_out e x₀) ^ 2 *
        (2 : ℝ) ^ (Q + Qᵀ).cutRank X ≤
      4 * (4 : ℝ) ^ (G.edgeCut P).ncard := by
  classical
  intro X
  let glueX := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  obtain ⟨κ, _, U_mat, V_mat, hcard_nat, hUV'⟩ := exists_quantumAcceptProb_affine_mul x₀ heA hqA
    hsplit G inVert outVert F hcontract hloc_in hloc_out hloc_edge P 2 (-1)
  have hUV (a : X → Bool) (b : ↥Xᶜ → Bool) :
      (U_mat * V_mat) a b = 2 * quantumAcceptProb C q_out e x₀ (glueX (a, b)) - 1 := by
    rw [hUV' a b]; ring
  have hUV_sq : (∑ a : X → Bool, ∑ b : ↥Xᶜ → Bool, (U_mat * V_mat) a b ^ 2) ≤ (2 : ℝ) ^ n := by
    refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_).trans_eq
      (sum_prod_subtype_compl_one X)
    rw [hUV]
    nlinarith [quantumAcceptProb_nonneg C q_out e x₀ (glueX (a, b)),
      quantumAcceptProb_le_one C q_out e x₀ (glueX (a, b))]
  have hcorr_sum : quantumCorrelation {x | BitString.quadForm Q x}
        (quantumAcceptProb C q_out e x₀) * (2 : ℝ) ^ n =
      -(∑ a : X → Bool, ∑ b : ↥Xᶜ → Bool,
        Communication.signMatrix ℝ (fun a' b' => BitString.quadForm Q (glueX (a', b'))) a b *
          (U_mat * V_mat) a b) := by
    rw [quantumCorrelation, div_mul_cancel₀ _ (by positivity), ← Finset.sum_neg_distrib]
    simp_rw [← Finset.sum_neg_distrib]
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool) _ _ fun x => ?_
    simp only [Communication.signMatrix_apply, hUV, mem_ofPred_eq, Prod.mk.eta, glueX,
      (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm_apply_apply]
    by_cases hqx : BitString.quadForm Q x = true <;> simp [hqx]
  have hfrob := Communication.sq_sum_mul_signMatrix_quadForm_le_card_of_mul Q X U_mat V_mat
  rw [Fintype.card_fin] at hfrob
  have hcard_κ : (Fintype.card κ : ℝ) ≤ 4 * (4 : ℝ) ^ (G.edgeCut P).ncard := by
    have : (Fintype.card κ : ℝ) ≤ 3 * (4 : ℝ) ^ (G.edgeCut P).ncard := by exact_mod_cast hcard_nat
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (G.edgeCut P).ncard]
  refine le_of_mul_le_mul_right (a := ((2 : ℝ) ^ n) ^ 2) ?_ (by positivity)
  calc (quantumCorrelation {x | BitString.quadForm Q x}
          (quantumAcceptProb C q_out e x₀)) ^ 2 *
          (2 : ℝ) ^ (Q + Qᵀ).cutRank X * ((2 : ℝ) ^ n) ^ 2
      = (quantumCorrelation {x | BitString.quadForm Q x}
          (quantumAcceptProb C q_out e x₀) * (2 : ℝ) ^ n) ^ 2 *
          (2 : ℝ) ^ (Q + Qᵀ).cutRank X := by ring
    _ ≤ (Fintype.card κ : ℝ) * (2 : ℝ) ^ n * ∑ a, ∑ b, (U_mat * V_mat) a b ^ 2 := by
        rw [hcorr_sum, neg_sq]; exact hfrob
    _ ≤ (4 * (4 : ℝ) ^ (G.edgeCut P).ncard) * (2 : ℝ) ^ n * (2 : ℝ) ^ n := by gcongr
    _ = 4 * (4 : ℝ) ^ (G.edgeCut P).ncard * ((2 : ℝ) ^ n) ^ 2 := by ring

open Classical in
/-- Single-cut `UQP` sign-rank bound: if `quantumAcceptProb C q_out e x₀ x > θ ↔ f x = true`, then
across any cut `P`, `signRank` across `(X, Xᶜ)` is at most `3 * 4 ^ |G.edgeCut P|`. -/
private theorem signRank_uqp_le_of_capped {n N : ℕ}
    {C : Quantum.Circuit N} {q_out : Fin N} {e : Fin n ↪ Fin N} {x₀ : Fin N → Bool}
    {A : Set (Fin N)} (heA : Set.range e ⊆ A) (hqA : q_out ∈ A)
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
    {f : (Fin n → Bool) → Bool} {θ : ℝ}
    (huqp : ∀ x, (if f x then θ < quantumAcceptProb C q_out e x₀ x
      else quantumAcceptProb C q_out e x₀ x < θ))
    (P : Set V_fin) :
    let X : Set (Fin n) := {i | inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
    Communication.signRank (fun (a : X → Bool) (b : ↥Xᶜ → Bool) =>
        f ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (a, b))) ≤
      3 * 4 ^ (G.edgeCut P).ncard := by
  classical
  intro X
  let glueX := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  obtain ⟨κ, _, U_sr, V_sr, hcard_κ, hUV⟩ := exists_quantumAcceptProb_affine_mul x₀ heA hqA
    hsplit G inVert outVert F hcontract hloc_in hloc_out hloc_edge P (-1) θ
  have hrep : Communication.SignRepresents (U_sr * V_sr) (fun a b => f (glueX (a, b))) := by
    refine Communication.SignRepresents.iff_lt.mpr fun a b => ?_
    rw [hUV a b]
    have hu := huqp (glueX (a, b))
    cases hf_ab : f (glueX (a, b))
    · simp only [hf_ab, Bool.false_eq_true, ↓reduceIte] at hu ⊢; linarith
    · simp only [hf_ab, ↓reduceIte] at hu ⊢; linarith
  exact (Communication.signRank_le_card_of_mul hrep).trans hcard_κ


end Cslib.Circuits.Frontier
