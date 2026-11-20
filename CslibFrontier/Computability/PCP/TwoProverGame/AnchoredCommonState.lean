/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredNoisyStates
public import CslibFrontier.Foundations.Quantum.Measurement.LocalAlignment
public import CslibFrontier.Foundations.Analysis.Normed.Normalize
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Kronecker

/-!
# The common-state comparison for anchored repetition

Applying question-dependent local unitaries to the doubly anchored checked-answer
branch approximates the checked-answer branch at the selected question pair.
The two single-question errors use the ordinary branches. The third error uses the
same noisy Alice mixture at the sampled and anchored Bob questions. The proof compares
the Gram matrices of these filters without inverting them.

## Main results

* `norm_sub_checked_common_le`: the pointwise comparison for unnormalized checked branches.
* `norm_sub_normalized_checked_common_le`: compare the prepared and selected normalized states.

## References

* [Bavarian, Vidick and Yuen, Claim 5.19, equations (77)–(81)][BavarianVidickYuen2022]
  (arXiv:1509.07466v2, §5.4, printed pp. 31–33).
-/

public section

namespace Cslib.PCP.AnchoredDependency

open Matrix Quantum Cslib.Probability.PMF
open scoped unitInterval Kronecker ComplexOrder

variable {X Y A B ι κ : Type*} {n : ℕ}
  [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (G : TwoProverGame X Y A B) (α : I) (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Saved" => RestQuestions (Option X) (Option Y) C
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ
local notation "act" => toEuclideanCLM (𝕜 := ℂ)

omit [Fintype ι] [DecidableEq ι] in
private theorem inv_smul_mix_sub_posSemidef {P Q : Matrix ι ι ℂ} (hQ : Q.PosSemidef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (a⁻¹ • (a • P + b • Q) - P).PosSemidef := by
  rw [smul_add, smul_smul, inv_mul_cancel₀ ha.ne', one_smul, add_sub_cancel_left]
  exact (hQ.smul hb).smul (inv_nonneg.mpr ha.le)

/-- Alice's ordinary alignment error can be computed in the Bob-first order of her
noisy-branch API when its message fixes Bob's question at the anchor. -/
theorem norm_sub_checkedAlice_inr_none (S : RepeatedStrategy) (j : Free)
    (t : ParallelRepetition.Revealed (Option X) (Option Y) C) (x : Option X)
    (a : C → A) (b : C → B) (U : Matrix ι ι ℂ) (hm : t.halves j = .inr none) :
    let φ x' := checkedVectorGivenRest G α C S j (omitMessage C j t) (x', none) a b
    let φA x' := checkedVectorGivenAlice G α C S j t x' a b
    ‖act (U ⊗ₖ (1 : Matrix κ κ ℂ)) (φ none) - φ x‖ =
      ‖act ((1 : Matrix κ κ ℂ) ⊗ₖ U) (φA none) - φA x‖ := by
  intro φ φA
  let e := Equiv.prodComm κ ι
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm
  have hφ (x' : Option X) : φA x' = E (φ x') := by
    apply WithLp.ofLp_injective 2
    exact checkedVectorGivenAlice_inr_none G α C S j t x' a b hm
  have hact (v : EuclideanSpace ℂ (ι × κ)) :
      act ((1 : Matrix κ κ ℂ) ⊗ₖ U) (E v) = E (act (U ⊗ₖ (1 : Matrix κ κ ℂ)) v) := by
    apply WithLp.ofLp_injective 2
    change (((1 : Matrix κ κ ℂ) ⊗ₖ U) *ᵥ (v.ofLp ∘ e)) =
      ((U ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ v.ofLp) ∘ e
    rw [← submatrix_kronecker_prodComm, submatrix_mulVec_equiv, Function.comp_assoc,
      e.self_comp_symm, Function.comp_id]
  rw [hφ, hφ, hact, ← map_sub, E.norm_map]

/-- The two local actions on the doubly anchored branch approximate the ordinary selected branch.
The ordinary and noisy comparison errors are unnormalized. The two coefficients of the noisy
error are the inverse square roots of the two mixture weights. -/
theorem norm_sub_checked_common_le (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (x : Option X) (y : Option Y) (a : C → A) (b : C → B)
    (U : Matrix ι ι ℂ) (V W : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hW : W ∈ unitaryGroup κ ℂ) (hα : 0 < (α : ℝ)) :
    let φ x' y' := checkedVectorGivenRest G α C S j t (x', y') a b
    let φN y' := checkedVectorGivenBob G α C S j t (.inl x) y' a b
    let η := (noise α : ℝ)
    ‖act (U ⊗ₖ V) (φ none none) - φ x y‖ ≤
      ‖act ((1 : Matrix ι ι ℂ) ⊗ₖ V) (φ none none) - φ none y‖ +
      ‖act (U ⊗ₖ (1 : Matrix κ κ ℂ)) (φ none none) - φ x none‖ +
      (Real.sqrt η⁻¹ + Real.sqrt (1 - η)⁻¹) *
        ‖act ((1 : Matrix ι ι ℂ) ⊗ₖ W) (φN y) - φN none‖ := by
  intro φ φN η
  let PA (x' : Option X) := aliceQuestionsGivenRest G α C j t (x', none)
  let PB (y' : Option Y) := bobQuestionsGivenRest G α C j t (none, y')
  let AN := POVM.mixture ((coin (noise α)).bind fun erase =>
    if erase then PA none else PA x) (S.checkedAlice C)
  let MA (x' : Option X) := POVM.mixture (PA x') (S.checkedAlice C)
  let MB (y' : Option Y) := POVM.mixture (PB y') (S.checkedBob C)
  have hraw (x' : Option X) (y' : Option Y) :
      φ x' y' = act ((MA x').sqrtEffect a ⊗ₖ (MB y').sqrtEffect b) S.state := by
    dsimp only [φ]
    rw [checkedVectorGivenRest, QuantumStrategy.averagedCheckedVector_eq,
      aliceQuestionsGivenRest_congr G α C j t (x', y') (x', none) rfl,
      bobQuestionsGivenRest_congr G α C j t (x', y') (none, y') rfl]
    rfl
  have hnoisy (y' : Option Y) :
      φN y' = act (AN.sqrtEffect a ⊗ₖ (MB y').sqrtEffect b) S.state := by
    dsimp only [φN]
    rw [checkedVectorGivenBob_eq, bind_aliceQuestionsGivenRest_inl,
      QuantumStrategy.averagedCheckedVector_eq]
    rfl
  have hmix : AN.effect a = η • (MA none).effect a + (1 - η) • (MA x).effect a :=
    POVM.mixture_coin_bind_effect (noise α) (PA none) (PA x) (S.checkedAlice C) a
  have hη : 0 < η := by dsimp only [η]; rw [coe_noise]; positivity
  have hη' : 0 < 1 - η := by
    dsimp only [η]
    rw [coe_noise]
    linarith [α.2.2]
  have h₀ : (η⁻¹ • AN.effect a - (MA none).effect a).PosSemidef := by
    rw [hmix]
    exact inv_smul_mix_sub_posSemidef ((MA x).posSemidef a) hη hη'.le
  have h₁ : ((1 - η)⁻¹ • AN.effect a - (MA x).effect a).PosSemidef := by
    rw [hmix, add_comm]
    exact inv_smul_mix_sub_posSemidef ((MA none).posSemidef a) hη' hη.le
  simp only [hraw, hnoisy]
  apply norm_sub_joint_alignment_le _ _ _ _ _ _ _ _ _ hU hW
    (inv_nonneg.mpr hη.le) (inv_nonneg.mpr hη'.le)
  · simpa only [POVM.conjTranspose_sqrtEffect, POVM.sqrtEffect_mul_self] using h₀
  · simpa only [POVM.conjTranspose_sqrtEffect, POVM.sqrtEffect_mul_self] using h₁

/-- The state obtained by applying the two local unitaries to the normalized doubly
anchored branch is close to the normalized branch at the selected questions.
The bound uses three unnormalized comparison errors divided by the same anchor norm,
together with the ordinary branch's deviation from that norm. -/
theorem norm_sub_normalized_checked_common_le (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (x : Option X) (y : Option Y) (a : C → A) (b : C → B)
    (U : Matrix ι ι ℂ) (V W : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hW : W ∈ unitaryGroup κ ℂ) (hα : 0 < (α : ℝ)) :
    let φ x' y' := checkedVectorGivenRest G α C S j t (x', y') a b
    let φN y' := checkedVectorGivenBob G α C S j t (.inl x) y' a b
    let γ := ‖φ none none‖
    let η := (noise α : ℝ)
    ‖act (U ⊗ₖ V) (NormedSpace.normalize (φ none none)) - NormedSpace.normalize (φ x y)‖ ≤
      (‖act ((1 : Matrix ι ι ℂ) ⊗ₖ V) (φ none none) - φ none y‖ +
        ‖act (U ⊗ₖ (1 : Matrix κ κ ℂ)) (φ none none) - φ x none‖ +
        (Real.sqrt η⁻¹ + Real.sqrt (1 - η)⁻¹) *
          ‖act ((1 : Matrix ι ι ℂ) ⊗ₖ W) (φN y) - φN none‖) / γ +
      |‖φ x y‖ / γ - 1| := by
  intro φ φN γ η
  have h := NormedSpace.norm_sub_normalize_le ((act (U ⊗ₖ V)).restrictScalars ℝ)
    (φ none none) (φ x y)
  exact h.trans (add_le_add (div_le_div_of_nonneg_right
    (norm_sub_checked_common_le G α C S j t x y a b U V W hU hW hα) (norm_nonneg _)) le_rfl)

end Cslib.PCP.AnchoredDependency
