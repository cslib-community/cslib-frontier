/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Input
public import CslibFrontier.Computability.Communication.QuadFormSignRank
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.SubmatrixRobust
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Quantum circuit observables, quadratic phase states, and cut-factorization helpers

Defines single-qubit acceptance probability `quantumAcceptProb`, Boolean correlation
`quantumCorrelation`, computational-basis quadratic phase states `phaseState`, Boolean matrix-vector
multiplication `boolMulVec`, and the bipartite `(2n) × (2n)` block matrix `linBlockMatrix` (proving
its bisection cut-rank lower bound `half_le_cutRank_linBlockMatrix`), along with internal vertex-cut
amplitude and real-matrix factorization helpers.

## Main definitions

* `Cslib.Circuits.Frontier.quantumAcceptProb`, `Cslib.Circuits.Frontier.quantumCorrelation`:
  single-qubit measurement acceptance probability and Boolean correlation.
* `Cslib.Circuits.Frontier.phaseState`: embedded `n`-qubit quadratic phase state.
* `Cslib.Circuits.Frontier.boolMulVec`, `Cslib.Circuits.Frontier.linBlockMatrix`: Boolean `𝔽₂`
  matrix-vector multiplication and bipartite `(2n) × (2n)` polar block matrix.

## Main results

* `Cslib.Circuits.Frontier.quantumAcceptProb_nonneg`,
  `Cslib.Circuits.Frontier.quantumAcceptProb_le_one`,
  `Cslib.Circuits.Frontier.norm_phaseState`: range and unit-norm properties of quantum observables.
* `Cslib.Circuits.Frontier.half_le_cutRank_linBlockMatrix`: bisection cut-rank lower bound for
  `linBlockMatrix n R` of a submatrix-robust matrix `R`.
-/

public section

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset Kronecker

open Classical in
/-- **Amplitude cut factorization.** In any `CappedWireNet`, across any vertex cut `P ⊆ V_fin`,
`M y x` factors as a sum over `τ : G.edgeCut P → Bool` of
`Φ_P(x_P, y_P, τ) * Ψ_{Pᶜ}(x_{Pᶜ}, y_{Pᶜ}, τ)`. -/
private theorem amplitude_cut_factorization {V_fin E_fin W : Type}
    [Fintype V_fin] [Fintype E_fin] [DecidableEq E_fin]
    (G : Multigraph V_fin E_fin) (inVert outVert : W ↪ V_fin)
    (F : V_fin → (W → Bool) → (W → Bool) → (E_fin → Bool) → ℂ)
    {M : Matrix (W → Bool) (W → Bool) ℂ}
    (hcontract : ∀ y x : W → Bool, M y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ)
    (hloc_in : ∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ)
    (hloc_out : ∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ)
    (hloc_edge : ∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)
    (P : Set V_fin) :
    let XP : Set W := {q | inVert q ∈ P}
    let YP : Set W := {q | outVert q ∈ P}
    let Ecut : Set E_fin := G.edgeCut P
    ∃ (Φ : (XP → Bool) → (YP → Bool) → (Ecut → Bool) → ℂ)
      (Ψ : (↥XPᶜ → Bool) → (↥YPᶜ → Bool) → (Ecut → Bool) → ℂ),
      ∀ (x : W → Bool) (y : W → Bool),
        M y x = ∑ τ : Ecut → Bool,
          Φ (XP.domRestrict x) (YP.domRestrict y) τ *
            Ψ (XPᶜ.domRestrict x) (YPᶜ.domRestrict y) τ := by
  classical
  intro XP YP Ecut
  let Ein : Set E_fin := {e | G.src e ∈ P ∧ G.tgt e ∈ P}
  let Eout : Set E_fin := {e | G.src e ∉ P ∧ G.tgt e ∉ P}
  -- Equivalence `(E_fin → Bool) ≃ (Ecut → Bool) × ((Ein → Bool) × (Eout → Bool))`.
  have hpart_e (e : E_fin) :
      (e ∈ Ecut ∧ e ∉ Ein ∧ e ∉ Eout) ∨
        (e ∉ Ecut ∧ e ∈ Ein ∧ e ∉ Eout) ∨
        (e ∉ Ecut ∧ e ∉ Ein ∧ e ∈ Eout) := by
    simp only [Ecut, Ein, Eout, Multigraph.mem_edgeCut, mem_ofPred_eq]
    by_cases hs : G.src e ∈ P <;> by_cases ht : G.tgt e ∈ P <;> tauto
  let glueE (τ : Ecut → Bool) (γ_in : Ein → Bool) (γ_out : Eout → Bool) (e : E_fin) : Bool :=
    if hc : e ∈ Ecut then τ ⟨e, hc⟩
    else if hi : e ∈ Ein then γ_in ⟨e, hi⟩
    else if ho : e ∈ Eout then γ_out ⟨e, ho⟩
    else false
  let eqvE : (E_fin → Bool) ≃ (Ecut → Bool) × ((Ein → Bool) × (Eout → Bool)) :=
    { toFun := fun γ => (Ecut.domRestrict γ, (Ein.domRestrict γ, Eout.domRestrict γ))
      invFun := fun p => glueE p.1 p.2.1 p.2.2
      left_inv := fun γ => funext fun e => by
        rcases hpart_e e with ⟨hc, _, _⟩ | ⟨hc, hi, _⟩ | ⟨hc, hi, ho⟩ <;>
          simp only [glueE, *, ↓reduceDIte, Set.domRestrict_apply]
      right_inv := fun ⟨τ, γ_in, γ_out⟩ =>
        Prod.ext
          (funext fun ⟨e, hc⟩ => by simp only [Set.domRestrict_apply, glueE, hc, ↓reduceDIte])
          (Prod.ext (funext fun ⟨e, hi⟩ => by
            rcases hpart_e e with ⟨_, hni, _⟩ | ⟨hc, _, _⟩ | ⟨_, hni, _⟩
            · exact absurd hi hni
            · simp only [Set.domRestrict_apply, glueE, hc, hi, ↓reduceDIte]
            · exact absurd hi hni)
          (funext fun ⟨e, ho⟩ => by
            rcases hpart_e e with ⟨_, _, hno⟩ | ⟨_, _, hno⟩ | ⟨hc, hi, _⟩
            · exact absurd ho hno
            · exact absurd ho hno
            · simp only [Set.domRestrict_apply, glueE, hc, hi, ho, ↓reduceDIte])) }
  let x0P (xP : XP → Bool) : W → Bool := fun q => if hq : q ∈ XP then xP ⟨q, hq⟩ else false
  let y0P (yP : YP → Bool) : W → Bool := fun q => if hq : q ∈ YP then yP ⟨q, hq⟩ else false
  let x0Pc (xPc : ↥XPᶜ → Bool) : W → Bool := fun q => if hq : q ∈ XPᶜ then xPc ⟨q, hq⟩ else false
  let y0Pc (yPc : ↥YPᶜ → Bool) : W → Bool := fun q => if hq : q ∈ YPᶜ then yPc ⟨q, hq⟩ else false
  let Φ (xP : XP → Bool) (yP : YP → Bool) (τ : Ecut → Bool) : ℂ :=
    ∑ γ_in : Ein → Bool, ∏ v ∈ Finset.univ.filter (· ∈ P),
      F v (x0P xP) (y0P yP) (glueE τ γ_in fun _ => false)
  let Ψ (xPc : ↥XPᶜ → Bool) (yPc : ↥YPᶜ → Bool) (τ : Ecut → Bool) : ℂ :=
    ∑ γ_out : Eout → Bool, ∏ v ∈ Finset.univ.filter (· ∉ P),
      F v (x0Pc xPc) (y0Pc yPc) (glueE τ (fun _ => false) γ_out)
  refine ⟨Φ, Ψ, fun x y => ?_⟩
  rw [hcontract y x,
    ← Fintype.sum_equiv eqvE.symm (fun p => ∏ v : V_fin, F v x y (eqvE.symm p)) _ (fun _ => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  dsimp only [Φ, Ψ]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun γ_in _ => Finset.sum_congr rfl fun γ_out _ => ?_
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ P)]
  congr 1
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hvP : v ∈ P := (Finset.mem_filter.mp hv).2
    exact (hloc_in v x (x0P (XP.domRestrict x)) y (glueE τ γ_in γ_out) fun q hq => by
        have hqP : q ∈ XP := show inVert q ∈ P from hq.symm ▸ hvP
        simp only [x0P, hqP, ↓reduceDIte, Set.domRestrict_apply]).trans <|
      (hloc_out v (x0P (XP.domRestrict x)) y (y0P (YP.domRestrict y))
        (glueE τ γ_in γ_out) fun q hq => by
          have hqP : q ∈ YP := show outVert q ∈ P from hq.symm ▸ hvP
          simp only [y0P, hqP, ↓reduceDIte, Set.domRestrict_apply]).trans <|
      hloc_edge v (x0P (XP.domRestrict x)) (y0P (YP.domRestrict y))
        (glueE τ γ_in γ_out) (glueE τ γ_in fun _ => false) fun e he => by
          have hnot_out : e ∉ Eout := he.elim (fun hs h => h.1 (hs.symm ▸ hvP))
            (fun ht h => h.2 (ht.symm ▸ hvP))
          simp only [glueE, hnot_out, ↓reduceDIte]
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hvPc : v ∉ P := (Finset.mem_filter.mp hv).2
    exact (hloc_in v x (x0Pc (XPᶜ.domRestrict x)) y (glueE τ γ_in γ_out) fun q hq => by
        have hqPc : q ∈ XPᶜ := show inVert q ∉ P from hq.symm ▸ hvPc
        simp only [x0Pc, hqPc, ↓reduceDIte, Set.domRestrict_apply]).trans <|
      (hloc_out v (x0Pc (XPᶜ.domRestrict x)) y (y0Pc (YPᶜ.domRestrict y))
        (glueE τ γ_in γ_out) fun q hq => by
          have hqPc : q ∈ YPᶜ := show outVert q ∉ P from hq.symm ▸ hvPc
          simp only [y0Pc, hqPc, ↓reduceDIte, Set.domRestrict_apply]).trans <|
      hloc_edge v (x0Pc (XPᶜ.domRestrict x)) (y0Pc (YPᶜ.domRestrict y))
        (glueE τ γ_in γ_out) (glueE τ (fun _ => false) γ_out) fun e he => by
          have hnot_in : e ∉ Ein := he.elim (fun hs h => hvPc (hs ▸ h.1))
            (fun ht h => hvPc (ht ▸ h.2))
          simp only [glueE, hnot_in, ↓reduceDIte]


private theorem glue_left_injective {n N : ℕ} (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) :
    Function.Injective (fun x : Fin n → Bool => Quantum.glue e x x₀) := fun x₁ x₂ h =>
  funext fun i => by
    have hi : Quantum.glue e x₁ x₀ (e i) = Quantum.glue e x₂ x₀ (e i) := congrFun h (e i)
    rwa [Quantum.glue_apply_emb, Quantum.glue_apply_emb] at hi

/-- Acceptance probability of measuring qubit `q_out` in `|1⟩` (`true`) after running `C` on
`|Quantum.glue e x x₀⟩`. -/
@[expose]
noncomputable def quantumAcceptProb {n N : ℕ} (C : Quantum.Circuit N) (q_out : Fin N)
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) (x : Fin n → Bool) : ℝ :=
  Quantum.measureProb (C.run (Quantum.glue e x x₀)) (Finset.univ.filter fun y => y q_out = true)

theorem quantumAcceptProb_nonneg {n N : ℕ} (C : Quantum.Circuit N) (q_out : Fin N)
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) (x : Fin n → Bool) :
    0 ≤ quantumAcceptProb C q_out e x₀ x :=
  Quantum.measureProb_nonneg _ _

theorem quantumAcceptProb_le_one {n N : ℕ} (C : Quantum.Circuit N) (q_out : Fin N)
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) (x : Fin n → Bool) :
    quantumAcceptProb C q_out e x₀ x ≤ 1 := by
  calc quantumAcceptProb C q_out e x₀ x
      ≤ Quantum.measureProb (C.run (Quantum.glue e x x₀)) Finset.univ :=
        Quantum.measureProb_le_measureProb_univ _ _
    _ = ‖C.run (Quantum.glue e x x₀)‖ ^ 2 := Quantum.measureProb_univ _
    _ = 1 := by rw [Quantum.Circuit.norm_run, one_pow]

/-- Correlation `𝔼_x [±1_{x ∈ S} · (2 p(x) - 1)]` between a target set `S ⊆ Bool^n` and an
acceptance-probability function `p : (Fin n → Bool) → ℝ`. -/
@[expose]
noncomputable def quantumCorrelation {n : ℕ} (S : Set (Fin n → Bool))
    (p : (Fin n → Bool) → ℝ) : ℝ :=
  open Classical in
  (∑ x : Fin n → Bool, (if x ∈ S then (1 : ℝ) else -1) * (2 * p x - 1)) / (2 : ℝ) ^ n

/-- The `n`-qubit computational-basis phase state
`2^{-n/2} ∑_{z : Bool^n} (-1)^{BitString.quadForm Q z} |Quantum.glue e z x₀⟩`, embedded via
`Quantum.embedState`. -/
noncomputable def phaseState {n N : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) : Quantum.Qubits N :=
  Quantum.embedState e x₀
    (WithLp.toLp 2 fun z : Fin n → Bool =>
      (((1 / √2) ^ n : ℝ) : ℂ) * (if BitString.quadForm Q z then -1 else 1))

private theorem sq_one_div_sqrt_two_pow (n : ℕ) :
    ((1 / √2 : ℝ) ^ n) ^ 2 = (1 / 2 : ℝ) ^ n := by
  rw [← pow_mul, mul_comm n 2, pow_mul, div_pow, one_pow, Real.sq_sqrt (by norm_num)]

theorem norm_phaseState {n N : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) : ‖phaseState Q e x₀‖ = 1 := by
  rw [phaseState, LinearIsometry.norm_map]
  set ψ : Quantum.Qubits n := WithLp.toLp 2 fun z : Fin n → Bool =>
    (((1 / √2) ^ n : ℝ) : ℂ) * (if BitString.quadForm Q z then -1 else 1)
  have hsq : ‖ψ‖ ^ 2 = 1 := by
    rw [← Quantum.measureProb_univ, Quantum.measureProb]
    have hterm (z : Fin n → Bool) : ‖ψ.ofLp z‖ ^ 2 = (1 / 2 : ℝ) ^ n := by
      simp only [ψ, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / √2) ^ n),
        (by split_ifs <;> simp : ‖(if BitString.quadForm Q z then (-1 : ℂ) else 1)‖ = 1),
        mul_one, sq_one_div_sqrt_two_pow]
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow, mul_one_div_cancel (by norm_num),
      one_pow]
  nlinarith [norm_nonneg ψ]

private theorem exists_lift_domRestrict {n N : ℕ} {α : Type*}
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) {A : Set (Fin N)} (heA : Set.range e ⊆ A)
    (Q_sub : Set ↥A) {T : Set (Fin n)}
    (hQT : ∀ i : Fin n, (⟨e i, heA ⟨i, rfl⟩⟩ : ↥A) ∈ Q_sub → i ∈ T)
    (inp : α → Fin n → Bool) (proj : α → T → Bool)
    (hinp : ∀ z (i : T), inp z i.1 = proj z i) :
    ∃ liftQ : (T → Bool) → (Q_sub → Bool),
      ∀ z : α, Q_sub.domRestrict (A.domRestrict (Quantum.glue e (inp z) x₀)) = liftQ (proj z) := by
  have hmem (q : Q_sub) (hq : ∃ i : Fin n, e i = q.1.1) : Classical.choose hq ∈ T :=
    hQT _ (by
      rw [show (⟨e (Classical.choose hq), heA ⟨_, rfl⟩⟩ : ↥A) = q.1 from
        Subtype.ext (Classical.choose_spec hq)]
      exact q.2)
  refine ⟨fun a q => open Classical in
    if hq : ∃ i : Fin n, e i = q.1 then a ⟨Classical.choose hq, hmem q hq⟩
    else x₀ q.1.1, fun z => funext fun q => ?_⟩
  simp only [Set.domRestrict_apply]
  by_cases hq : ∃ i : Fin n, e i = q.1.1
  · simp only [hq, ↓reduceDIte, ← hinp z ⟨Classical.choose hq, hmem q hq⟩]
    exact (congrArg (Quantum.glue e (inp z) x₀) (Classical.choose_spec hq)).symm.trans
      (Quantum.glue_apply_emb e (inp z) x₀ (Classical.choose hq))
  · simp only [hq, ↓reduceDIte]
    exact Quantum.glue_of_not e _ x₀ fun i hi => hq ⟨i, hi⟩

/-- Given `Q_sub ⊆ ↥A` inducing `S = {i : Fin n | ⟨e i, _⟩ ∈ Q_sub}`, restricting
`Quantum.glue e (glueS (a, b)) x₀` to `Q_sub` depends only on `a : S → Bool` and restricting to
`Q_subᶜ` depends only on `b : ↥Sᶜ → Bool`. -/
private theorem exists_lift_domRestrict_glue {n N : ℕ}
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) {A : Set (Fin N)} (heA : Set.range e ⊆ A)
    (Q_sub : Set ↥A)
    [DecidablePred (· ∈ ({i : Fin n | (⟨e i, heA ⟨i, rfl⟩⟩ : ↥A) ∈ Q_sub} : Set (Fin n)))] :
    let S : Set (Fin n) := {i | (⟨e i, heA ⟨i, rfl⟩⟩ : ↥A) ∈ Q_sub}
    let glueS := (Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Bool).symm
    ∃ (liftP : (S → Bool) → (Q_sub → Bool)) (liftPc : (↥Sᶜ → Bool) → (↥Q_subᶜ → Bool)),
      (∀ (a : S → Bool) (b : ↥Sᶜ → Bool),
        Q_sub.domRestrict (A.domRestrict (Quantum.glue e (glueS (a, b)) x₀)) = liftP a) ∧
      (∀ (a : S → Bool) (b : ↥Sᶜ → Bool),
        Q_subᶜ.domRestrict (A.domRestrict (Quantum.glue e (glueS (a, b)) x₀)) = liftPc b) := by
  intro S glueS
  obtain ⟨liftP, hP⟩ := exists_lift_domRestrict (T := S) e x₀ heA Q_sub (fun _ h => h)
    glueS Prod.fst fun ⟨a, b⟩ i => by
      simp only [glueS, Equiv.piEquivPiSubtypeProd_symm_apply, i.2, ↓reduceDIte]
  obtain ⟨liftPc, hPc⟩ := exists_lift_domRestrict (T := Sᶜ) e x₀ heA Q_subᶜ (fun _ h => h)
    glueS Prod.snd fun ⟨a, b⟩ i => by
      have hni : i.1 ∉ S := i.2
      simp only [glueS, Equiv.piEquivPiSubtypeProd_symm_apply, hni, ↓reduceDIte]; rfl
  exact ⟨liftP, liftPc, fun a b => hP (a, b), fun a b => hPc (a, b)⟩

/-! ### Core single-cut bounds from `CappedWireNet` -/

private def realCutLeft {α ι : Type*} (Φ : α → ι → ℂ) : Matrix α (ι × Bool) ℝ :=
  fun a p => if p.2 then -(Φ a p.1).im else (Φ a p.1).re

private def realCutRight {β ι : Type*} (Ψ : β → ι → ℂ) : Matrix (ι × Bool) β ℝ :=
  fun p b => if p.2 then (Ψ b p.1).im else (Ψ b p.1).re

private theorem realCutLeft_mul_realCutRight_apply {α β ι : Type*} [Fintype ι]
    (Φ : α → ι → ℂ) (Ψ : β → ι → ℂ) (a : α) (b : β) :
    (realCutLeft Φ * realCutRight Ψ) a b = (∑ τ : ι, Φ a τ * Ψ b τ).re := by
  rw [Complex.re_sum, Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_bool, Complex.mul_re]
  simp only [realCutLeft, realCutRight, Bool.false_eq_true, ↓reduceIte, neg_mul]
  ring

private theorem realCutLeft_neg_I_mul_realCutRight_apply {α β ι : Type*} [Fintype ι]
    (Φ : α → ι → ℂ) (Ψ : β → ι → ℂ) (a : α) (b : β) :
    (realCutLeft (fun a' τ => -Complex.I * Φ a' τ) * realCutRight Ψ) a b =
      (∑ τ : ι, Φ a τ * Ψ b τ).im := by
  rw [realCutLeft_mul_realCutRight_apply, Complex.re_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.mul_im]
  ring

private theorem card_cut_prod_bool {E_fin : Type} (Ecut : Set E_fin) [Fintype Ecut]
    [DecidableEq Ecut] :
    (Fintype.card ((Ecut → Bool) × Bool) : ℝ) = 2 * (2 : ℝ) ^ Ecut.ncard := by
  have hE : Fintype.card Ecut = Ecut.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, hE, mul_comm]
  push_cast; rfl

private theorem sum_prod_subtype_compl_one {m : ℕ} (S : Set (Fin m)) [Fintype S] [Fintype ↥Sᶜ] :
    (∑ _a : S → Bool, ∑ _b : ↥Sᶜ → Bool, (1 : ℝ)) = (2 : ℝ) ^ m := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_add, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem run_ofLp_eq_matrix_apply {N : ℕ} (C : Quantum.Circuit N)
    (x y : Fin N → Bool) :
    (C.run x).ofLp y = (C.matrix : Matrix _ _ ℂ) y x := by
  simp only [Quantum.Circuit.run, Quantum.Circuit.eval, Quantum.unitaryEquiv_apply,
    Matrix.mulVec, dotProduct, Quantum.ket_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Boolean matrix-vector multiplication `(x ↦ M *ᵥ x)` viewed on `Fin n → Bool`. -/
@[expose]
def boolMulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Fin n → Bool) (i : Fin n) :
    Bool :=
  decide ((M *ᵥ fun j => BitString.bitVal (ZMod 2) (x j)) i = 1)

private def inl2n (n : ℕ) (i : Fin n) : Fin (2 * n) :=
  ⟨i.1, by omega⟩

private def inr2n (n : ℕ) (j : Fin n) : Fin (2 * n) :=
  ⟨n + j.1, by omega⟩

private theorem inl2n_injective (n : ℕ) : Function.Injective (inl2n n) :=
  fun _ _ h => Fin.ext (Fin.mk.inj h)

private theorem inr2n_injective (n : ℕ) : Function.Injective (inr2n n) :=
  fun _ _ h => Fin.ext (Nat.add_left_cancel (Fin.mk.inj h))

private theorem disjoint_range_inl2n_inr2n (n : ℕ) :
    Disjoint (Set.range (inl2n n)) (Set.range (inr2n n)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  have hval := congrArg Fin.val hj
  simp only [inl2n, inr2n] at hval
  omega

/-- Bipartite `(2 n) × (2 n)` block matrix placing `R` on output rows `inr2n n` and input columns
`inl2n n`. -/
noncomputable def linBlockMatrix (n : ℕ) (R : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) :=
  Matrix.extendBlock (inr2n n) (inl2n n) R

/-- Bisection cut-rank lower bound for `linBlockMatrix n R` when `R` is `t`-submatrix-robust. -/
theorem half_le_cutRank_linBlockMatrix (n : ℕ) {t : ℕ}
    {R : Matrix (Fin n) (Fin n) (ZMod 2)} (hR : R.SubmatrixRobust t)
    {U : Set (Fin (2 * n))} (hU : U.ncard = (2 * n) / 2) :
    (2 * n) / 2 ≤ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U + (2 * t + 1) := by
  have hdiv : (2 * n) / 2 = n := by omega
  rw [hdiv] at hU ⊢
  exact hR.le_cutRank_add (inr2n_injective n) (inl2n_injective n)
    (disjoint_range_inl2n_inr2n n).symm
    (Matrix.submatrix_extendBlock (inr2n_injective n) (inl2n_injective n) R)
    (fun _ _ h => Matrix.extendBlock_eq_zero R h)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) hU

private theorem sign_dotProduct_eq_prod {α : Type*} (s : Finset α)
    (y : α → Bool) (v : α → ZMod 2) :
    (if decide (∑ j ∈ s, BitString.bitVal (ZMod 2) (y j) * v j = 1) then (-1 : ℂ) else 1) =
      ∏ j ∈ s, if y j && decide (v j = 1) then (-1 : ℂ) else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← ih]
    have hbool : ∀ (b : Bool) (va u : ZMod 2),
        decide (BitString.bitVal (ZMod 2) b * va + u = 1) =
          bne (b && decide (va = 1)) (decide (u = 1)) := by decide
    rw [hbool]
    cases (y a && decide (v a = 1)) <;>
      cases decide (∑ j ∈ s, BitString.bitVal (ZMod 2) (y j) * v j = 1) <;> norm_num


end Cslib.Circuits.Frontier
