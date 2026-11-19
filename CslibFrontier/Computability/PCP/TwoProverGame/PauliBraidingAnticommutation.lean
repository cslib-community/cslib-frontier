/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingConsistency
public import CslibFrontier.Computability.PCP.TwoProverGame.AnticommutationTest
public import CslibFrontier.Foundations.Quantum.Algebra.MeasurementAverage
import CslibFrontier.Probability.PMF.Uniform

/-!
# The CHSH strategy on an odd pair in the braiding test

Restricting the tagged anticommutation questions of a single strategy to one odd
pair gives a commuting CHSH strategy. Its logical second player's observables
are exactly those checked in the matched consistency rounds.

The soundness estimate specializes [Natarajan and Vidick, Lemma 18][NatarajanVidick2017]
(arXiv:1610.03574v1, §4.3.2, p. 21) to CHSH. It uses the CHSH and consistency scores
of one commuting-operator strategy and bounds the squared state-norm anticommutator
averaged conditionally on odd pairs. The source treats a supplied
anticommutation game and also proves honest-strategy completeness.

## Main results

* `Cslib.PCP.commutingWinProb_pauliBraidingAnticommutation_eq_expect`: the branch score is
  the mean score over odd pairs and role assignments.
* `Cslib.PCP.expect_norm_pauliBraidingSpecial_anticomm_sq_le`: the CHSH deficit controls
  the special observables' averaged squared anticommutation defect.
* `Cslib.PCP.expect_norm_pauliBraidingBasis_anticomm_sq_le`: transfer of the
  anticommutation estimate to the uniformly averaged basis observables.
-/

public section

namespace Cslib.PCP

open BitString Quantum

variable {n : ℕ} {𝒜 : Type*} [Ring 𝒜] [PartialOrder 𝒜] [Algebra ℂ 𝒜]
variable [IsOrderedAddMonoid 𝒜]

/-- Extract CHSH on an odd pair. Use the two role tags of the anticommutation branch and
decode malformed answers as false. The Boolean role assignment selects the logical order. -/
@[expose] def pauliBraidingCHSHStrategy
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜)
    (roles : Bool) (p : ↥(oddPairs (Fin n))) : CommutingStrategy Bool Bool Bool Bool 𝒜 :=
  let logical := cond roles S.swap S
  let read : (Bool × Bool) ⊕ Bool → Bool := Sum.elim (fun _ => false) id
  logical.map (fun q => .anticommutation false q p) (fun q => .anticommutation true q p)
    (fun _ => read) (fun _ => read)

/-- The extracted CHSH strategy uses the original state. -/
@[simp] theorem pauliBraidingCHSHStrategy_state
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜)
    (roles : Bool) (p : ↥(oddPairs (Fin n))) :
    (pauliBraidingCHSHStrategy S roles p).state = S.state := by
  cases roles <;> rfl

variable [StarRing 𝒜] [StarOrderedRing 𝒜]

/-- The second-role observable of CHSH is exactly the special observable used in the
consistency estimate on the same pair. -/
theorem pauliBraidingCHSHStrategy_bob_observable
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜)
    (roles : Bool) (p : ↥(oddPairs (Fin n))) (q : Bool) :
    ((pauliBraidingCHSHStrategy S roles p).bob q).observable =
      pauliBraidingSpecialObservable (cond roles S.alice S.bob) q id p := by
  cases roles <;> rfl

/-- The CHSH branch conditioned on a single odd pair and role assignment, with the
verifier's original rejection rule for malformed answers. -/
@[expose] noncomputable def pauliBraidingCHSHGame (n : ℕ) [Nonempty (Fin n)]
    (roles : Bool) (p : ↥(oddPairs (Fin n))) :
    SeededGame (Bool × Bool) (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) :=
  (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).pullbackSeed
    TwoProverGame.chsh.questions fun (x, y) => .anticommutation roles p x y

open Finset in
/-- Scoring the decoded CHSH strategy can only increase acceptance, since the actual
verifier rejects every malformed answer before decoding. -/
theorem commutingWinProb_pauliBraidingCHSHGame_le [Nonempty (Fin n)]
    [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
    [NonnegSpectrumClass ℝ 𝒜]
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜)
    (roles : Bool) (p : ↥(oddPairs (Fin n))) :
    (pauliBraidingCHSHGame n roles p).commutingWinProb S ≤
      TwoProverGame.chsh.commutingWinProb (pauliBraidingCHSHStrategy S roles p) := by
  classical
  let game := pauliBraidingCHSHGame n roles p
  let logical := cond roles S.swap S
  let q₁ (x : Bool) : PauliBraidingQuestion n Bool := .anticommutation false x p
  let q₂ (y : Bool) : PauliBraidingQuestion n Bool := .anticommutation true y p
  let read : (Bool × Bool) ⊕ Bool → Bool := Sum.elim (fun _ => false) id
  change game.commutingWinProb S ≤ _
  rw [SeededGame.commutingWinProb_eq_sum]
  unfold TwoProverGame.commutingWinProb
  change _ ≤ TwoProverGame.chsh.toSeeded.commutingWinProb _
  let : ∀ q a b, Decidable (TwoProverGame.chsh.toSeeded.accepts q a b) :=
    fun q a b => inferInstanceAs (Decidable (TwoProverGame.chsh.accepts q.1 q.2 a b))
  rw [SeededGame.commutingWinProb_eq_sum]
  refine sum_le_sum fun ⟨x, y⟩ _ =>
    mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  change (∑ a, ∑ b, if game.accepts (x, y) a b then
    S.prob (game.query (x, y)).1 (game.query (x, y)).2 a b else 0) ≤
      (∑ a, ∑ b, if TwoProverGame.chsh.accepts x y a b then
        (logical.map q₁ q₂ (fun _ => read) (fun _ => read)).prob x y a b else 0)
  rw [logical.sum_ite_prob_map]
  have hquery : game.query (x, y) = cond roles Prod.swap id (q₁ x, q₂ y) := rfl
  have hswap : (∑ a, ∑ b, if game.accepts (x, y) a b then
      S.prob (game.query (x, y)).1 (game.query (x, y)).2 a b else 0) =
      ∑ a, ∑ b, if game.accepts (x, y) (cond roles b a) (cond roles a b) then
        logical.prob (q₁ x) (q₂ y) a b else 0 := by
    rw [hquery]
    cases roles
    · rfl
    · simp only [logical, Bool.cond_true, Prod.swap_prod_mk, S.prob_swap]
      exact sum_comm
  rw [hswap]
  refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
  have haccept (h : game.accepts (x, y) (cond roles b a) (cond roles a b)) :
      TwoProverGame.chsh.accepts x y (read a) (read b) := by
    cases roles <;> cases a <;> cases b <;> first | exact h | exact False.elim h
  split_ifs with h₁ h₂ h₂
  · exact le_rfl
  · exact False.elim (h₂ (haccept h₁))
  · exact logical.prob_nonneg _ _ _ _
  · exact le_rfl

section Scores

open scoped BigOperators Real

variable [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
  [NonnegSpectrumClass ℝ 𝒜] [Nonempty (Fin n)]

omit [IsOrderedAddMonoid 𝒜] in
/-- The anticommutation branch score is the uniform mean over physical role assignments
and odd pairs of the original verifier's conditioned CHSH score. -/
theorem commutingWinProb_pauliBraidingAnticommutation_eq_expect
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜) :
    (pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id) 1).commutingWinProb S =
      𝔼 roles : Bool, 𝔼 p : ↥(oddPairs (Fin n)),
        (pauliBraidingCHSHGame n roles p).commutingWinProb S := by
  let game := pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)
  let := oddPairs_nonempty (ι := Fin n)
  let law (roles : Bool) (p : ↥(oddPairs (Fin n))) :=
    TwoProverGame.chsh.questions.map fun (x, y) => PauliBraidingSeed.anticommutation roles p x y
  let odd := Probability.PMF.uniformOfFintype ↥(oddPairs (Fin n))
  let sampler := (Probability.PMF.uniformOfFintype Bool).bind fun roles => odd.bind (law roles)
  change ({ game with seed := sampler }).answersWinProb S.answers = _
  dsimp only [sampler]
  rw [SeededGame.answersWinProb_bind_uniformSeed]
  refine Finset.expect_congr rfl fun roles _ => ?_
  rw [SeededGame.answersWinProb_bind_uniformSeed]
  refine Finset.expect_congr rfl fun p _ => ?_
  exact (game.answersWinProb_pullbackSeed TwoProverGame.chsh.questions
    (fun (x, y) => .anticommutation roles p x y) S.answers).symm

variable [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜]

/-- At a fixed physical role assignment the mean CHSH deficit of the decoded strategies
is at most twice the deficit of the full anticommutation branch against the CHSH optimum. -/
theorem expect_chshDeficit_pauliBraiding_le
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜) (roles : Bool) :
    (𝔼 p : ↥(oddPairs (Fin n)),
      (Real.cos (π / 8) ^ 2 -
        TwoProverGame.chsh.commutingWinProb (pauliBraidingCHSHStrategy S roles p))) ≤
      2 * (Real.cos (π / 8) ^ 2 -
        (pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id) 1).commutingWinProb S) := by
  let deficit (r : Bool) : ℝ := 𝔼 p : ↥(oddPairs (Fin n)),
    (Real.cos (π / 8) ^ 2 - (pauliBraidingCHSHGame n r p).commutingWinProb S)
  have hnonneg (r : Bool) : 0 ≤ deficit r :=
    Finset.expect_nonneg fun p _ => sub_nonneg.mpr <|
      (commutingWinProb_pauliBraidingCHSHGame_le S r p).trans
        (TwoProverGame.commutingWinProb_chsh_le _)
  have hcompare :
      (𝔼 p : ↥(oddPairs (Fin n)), (Real.cos (π / 8) ^ 2 -
        TwoProverGame.chsh.commutingWinProb (pauliBraidingCHSHStrategy S roles p))) ≤
      deficit roles :=
    Finset.expect_le_expect fun p _ => sub_le_sub_left
      (commutingWinProb_pauliBraidingCHSHGame_le S roles p) _
  refine hcompare.trans ?_
  rw [commutingWinProb_pauliBraidingAnticommutation_eq_expect]
  have hdef : (𝔼 r : Bool, deficit r) = Real.cos (π / 8) ^ 2 -
      (𝔼 r : Bool, 𝔼 p : ↥(oddPairs (Fin n)),
        (pauliBraidingCHSHGame n r p).commutingWinProb S) := by
    have hrow (r : Bool) : deficit r = Real.cos (π / 8) ^ 2 -
        (𝔼 p : ↥(oddPairs (Fin n)), (pauliBraidingCHSHGame n r p).commutingWinProb S) := by
      unfold deficit
      rw [Finset.expect_sub_distrib]
      let := oddPairs_nonempty (ι := Fin n)
      rw [Fintype.expect_const]
    simp_rw [hrow]
    rw [Finset.expect_sub_distrib, Fintype.expect_const]
  rw [← hdef, Fintype.expect_eq_sum_div_card, Fintype.sum_bool, Fintype.card_bool]
  cases roles <;> push_cast <;> linarith [hnonneg false, hnonneg true]

omit [IsOrderedAddMonoid 𝒜] [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜] in
private theorem chsh_swap_score (S : CommutingStrategy Bool Bool Bool Bool 𝒜) :
    TwoProverGame.chsh.commutingWinProb S.swap = TwoProverGame.chsh.commutingWinProb S := by
  simp only [TwoProverGame.commutingWinProb_chsh, CommutingStrategy.correlation_eq,
    CommutingStrategy.prob_swap]
  ring

/-- Averaged over the odd pairs, the logical second player's special observables
nearly anticommute when the combined verifier's CHSH branch scores near the CHSH optimum. -/
theorem expect_norm_pauliBraidingSpecial_anticomm_sq_le
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜) (roles : Bool) :
    let special := pauliBraidingSpecialObservable (cond roles S.alice S.bob)
    (𝔼 p : ↥(oddPairs (Fin n)),
      S.state.norm (special false id p * special true id p +
        special true id p * special false id p) ^ 2) ≤
      (2 * chshAnticommConst) * (Real.cos (π / 8) ^ 2 -
        (pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id) 1).commutingWinProb S) := by
  intro special
  let deficit (p : ↥(oddPairs (Fin n))) :=
    Real.cos (π / 8) ^ 2 - TwoProverGame.chsh.commutingWinProb (pauliBraidingCHSHStrategy S roles p)
  have hlocal (p : ↥(oddPairs (Fin n))) :
      S.state.norm (special false id p * special true id p +
        special true id p * special false id p) ^ 2 ≤ chshAnticommConst * deficit p := by
    let G := pauliBraidingCHSHStrategy S roles p
    have hwin : Real.cos (π / 8) ^ 2 - deficit p ≤ TwoProverGame.chsh.commutingWinProb G.swap := by
      rw [chsh_swap_score]
      change Real.cos (π / 8) ^ 2 - (Real.cos (π / 8) ^ 2 - _) ≤ _
      rw [sub_sub_cancel]
    have h := norm_anticomm_sq_le_of_chsh G.swap hwin
    change G.state.norm ((G.bob false).observable * (G.bob true).observable +
      (G.bob true).observable * (G.bob false).observable) ^ 2 ≤ _ at h
    simpa only [G, pauliBraidingCHSHStrategy_state, pauliBraidingCHSHStrategy_bob_observable]
      using h
  have havg := Finset.expect_le_expect
    (s := (Finset.univ : Finset ↥(oddPairs (Fin n)))) fun p _ => hlocal p
  rw [← Finset.mul_expect] at havg
  exact havg.trans <| by
    rw [mul_comm (2 : ℝ), mul_assoc]
    exact mul_le_mul_of_nonneg_left (expect_chshDeficit_pauliBraiding_le S roles)
      chshAnticommConst_nonneg

variable [Module ℚ≥0 𝒜] [PosSMulMono ℚ≥0 𝒜]

open Finset in
/-- The uniformly averaged basis observables anticommute on odd pairs up to the
consistency and anticommutation deficits of the CHSH braiding verifier. -/
theorem expect_norm_pauliBraidingBasis_anticomm_sq_le
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜) (roles : Bool) :
    let measure := cond roles S.bob S.alice
    let X (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable measure false x d
    let Z (z : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable measure true z d
    let branch := pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id)
    (𝔼 p : ↥(oddPairs (Fin n)),
      S.state.norm (X p.val.1 * Z p.val.2 + Z p.val.2 * X p.val.1) ^ 2) ≤
      9 * (4096 * (1 - (branch 2).commutingWinProb S) +
        2 * chshAnticommConst * (Real.cos (π / 8) ^ 2 - (branch 1).commutingWinProb S)) := by
  intro measure X Z branch
  let logical := cond roles S.swap S
  let special := pauliBraidingSpecialObservable (cond roles S.alice S.bob)
  let P := ↥(oddPairs (Fin n))
  let basisQuestion (basis : Bool) (r : (Fin n → Bool) × (Fin n → Bool)) :=
    PauliConsistencyQuestion.ofChecked basis r.1 r.2
  let decoded (basis : Bool) (p : P) :=
    logical.map (fun r => (basisQuestion basis r).toBraidingQuestion)
      (fun q => .anticommutation true q p)
      (fun r => Sum.elim (basisQuestion basis r).braidingCheckedBit fun _ => false)
      (fun _ => Sum.elim (fun _ : Bool × Bool => false) id)
  let M (basis : Bool) (x d : Fin n → Bool) :=
    let q := PauliConsistencyQuestion.ofChecked basis x d
    (measure q.toBraidingQuestion).map (Sum.elim q.braidingCheckedBit fun _ => false)
  have hcontract (basis : Bool) (x : Fin n → Bool) :
      star (𝔼 d, (M basis x d).observable) * (𝔼 d, (M basis x d).observable) ≤ 1 := by
    rw [← Measurement.observable_average]
    exact (Measurement.average (M basis x)).star_observable_mul_self_le_one
  have hspecial (q : Bool) (p : P) : star (special q id p) * special q id p ≤ 1 := by
    have heq : ((pauliBraidingCHSHStrategy S roles p).bob q).observable = special q id p :=
      pauliBraidingCHSHStrategy_bob_observable S roles p q
    rw [← heq]
    exact ((pauliBraidingCHSHStrategy S roles p).bob q).star_observable_mul_self_le_one
  have hcomm (basis q : Bool) (x : Fin n → Bool) (p : P) :
      Commute (𝔼 d, (M basis x d).observable) (special q id p) := by
    rw [← Measurement.observable_average]
    refine Measurement.commute_observable_average _ _ fun d => ?_
    have h := (decoded basis p).commute_observable (x, d) q
    cases roles <;> exact h
  let density : ℝ := (oddPairs (Fin n)).dens
  have hdensity : 0 < density := by
    obtain ⟨p⟩ := oddPairs_nonempty (ι := Fin n)
    have hpos : 0 < (oddPairs (Fin n)).dens := Finset.dens_pos.mpr ⟨p.val, p.property⟩
    change 0 < ((oddPairs (Fin n)).dens : ℝ)
    exact_mod_cast hpos
  have hclose (basis : Bool) :
      (𝔼 p : P, S.state.norm ((𝔼 d, (M basis (if basis then p.val.2 else p.val.1) d).observable) -
        special basis id p) ^ 2) ≤ 2048 * (1 - (branch 2).commutingWinProb S) := by
    have h := weighted_expect_norm_pauliBraidingAverage_sub_special_sq_le
      TwoProverGame.chsh id (fun _ => id) roles basis S
    dsimp only at h
    rw [TwoProverGame.chsh_questions_snd_toReal] at h
    apply (mul_le_mul_iff_right₀ (show 0 < (1 / 2 : ℝ) * density by positivity)).mp
    convert h using 1 <;> first | rfl | ring
  have h := expect_norm_mul_sub_smul_mul_sq_le_of_consistent S.state
    (fun p : P => X p.val.1) (fun p => Z p.val.2)
    (special false id) (special true id) (fun _ => -1)
    (fun p => hcontract false p.val.1) (fun p => hcontract true p.val.2)
    (hspecial false) (hspecial true)
    (fun p => hcomm false true p.val.1 p) (fun p => hcomm true false p.val.2 p) (by simp)
  simp only [neg_one_smul, sub_neg_eq_add, add_comm (Z _ * X _)] at h
  have hx := hclose false
  have hz := hclose true
  have hac := expect_norm_pauliBraidingSpecial_anticomm_sq_le S roles
  change (𝔼 p : P, S.state.norm (X p.val.1 - special false id p) ^ 2) ≤ _ at hx
  change (𝔼 p : P, S.state.norm (Z p.val.2 - special true id p) ^ 2) ≤ _ at hz
  linarith only [h, hx, hz, hac]

end Scores

end Cslib.PCP
