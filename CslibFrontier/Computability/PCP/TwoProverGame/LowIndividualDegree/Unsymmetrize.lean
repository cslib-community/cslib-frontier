/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SymmetricSoundness
public import CslibFrontier.Computability.PCP.TwoProverGame.Symmetrize
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform

/-!
# Point agreement for general projective low-degree strategies

The low-individual-degree verifier is invariant under swapping the players. A
global polynomial measurement for the symmetrized strategy therefore yields a
local polynomial measurement for each of the original players, with the same
mean point disagreement across the two roles. This gives the first step in
the proof of [JNVWY2020LowIndividualDegree, Theorem 3.10].
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset
open Cslib.Probability.PMF (uniformOfFintype uniformOfFintype_map_equiv map_equiv_apply)
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {F ι κ : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem assignLineRoles_swap {m : ℕ} (line point : Question F m) :
    (assignLineRoles line point).map Prod.swap = assignLineRoles line point := by
  let e : Bool ≃ Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩
  let f (r : Bool) := if r then (line, point) else (point, line)
  have h : Prod.swap ∘ f = f ∘ e := by funext r; cases r <;> rfl
  change ((uniformOfFintype Bool).map f).map Prod.swap = (uniformOfFintype Bool).map f
  rw [PMF.map_comp, h, ← PMF.map_comp, uniformOfFintype_map_equiv e]

private theorem branchQuestions_swap (n : ℕ) (b : Branch) :
    (branchQuestions (F := F) n b).map Prod.swap = branchQuestions n b := by
  cases b
  · simp only [branchQuestions_axis, axisQuestions, PMF.map_bind, assignLineRoles_swap]
  · rw [branchQuestions_consistency, consistencyQuestions, PMF.map_comp]
    rfl
  · simp only [branchQuestions_diagonal, diagonalQuestions, PMF.map_bind, assignLineRoles_swap]

/-- Symmetrizing a tensor strategy preserves each branch score, including with
a separate cutoff for diagonal answers. -/
theorem commutingWinProb_branch_symmetrize {n : ℕ}
    (S : QuantumStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) ι κ)
    (d D : ℕ) (b : Branch) :
    (branchGameWithDiagonalCap (F := F) n d D b).commutingWinProb S.symmetrize.toCommuting =
      (branchGameWithDiagonalCap (F := F) n d D b).commutingWinProb S.toCommuting := by
  rw [TwoProverGame.commutingWinProb_toCommuting, TwoProverGame.commutingWinProb_toCommuting]
  apply TwoProverGame.quantumWinProb_symmetrize _ _ _ S
  · intro x y
    have he := map_equiv_apply (branchQuestions (F := F) n b) (Equiv.prodComm _ _) (x, y)
    simpa [branchGameWithDiagonalCap_questions, branchQuestions_swap] using he.symm
  · intro x y a c
    simpa only [branchGameWithDiagonalCap_accepts] using acceptsWithDiagonalCap_swap d D y x c a

variable {n d : ℕ}

local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)
local notation "Poly" => BoundedPolynomial F (n + 1) d

/-- A projective tensor strategy has two complete local polynomial POVMs on its
original spaces with bounded disagreement against the opposite player's
decoded points. The symmetrized bound is charged to both roles together. -/
theorem exists_local_polynomial_POVMs_of_projective {k : ℕ} (D : ℕ)
    (hk : (n + 1) * d ≤ k)
    (S : QuantumStrategy Q Q Ans Ans ι κ)
    (hA : ∀ q, (S.alice q).toMeasurement.IsProjective)
    (hB : ∀ q, (S.bob q).toMeasurement.IsProjective) :
    let C := S.toCommuting
    let ε := 1 - (branchGame (F := F) n d .axis).commutingWinProb C
    let δ := 1 - (branchGame (F := F) n d .consistency).commutingWinProb C
    let γ :=
      1 - (branchGameWithDiagonalCap (F := F) n d D .diagonal).commutingWinProb C
    let r := (d : ℝ) / Fintype.card F
    ∃ (Gₐ : POVM Poly ι) (Gᵦ : POVM Poly κ),
      let bound := 320000 * dimensionInductionError (n + 1) k ε δ γ r
      (𝔼 u : Point F (n + 1), (1 - Measurement.agreement C.state
        (decodedPoint C.alice u)
        ((QuantumStrategy.rightMeasurement (ι := ι) Gᵦ).map fun g => MvPolynomial.eval u g.val))) ≤
        bound ∧
      (𝔼 u : Point F (n + 1), (1 - Measurement.agreement C.state
        ((QuantumStrategy.leftMeasurement (κ := κ) Gₐ).map fun g => MvPolynomial.eval u g.val)
        (decodedPoint C.bob u))) ≤ bound := by
  classical
  intro C ε δ γ r
  let T := S.symmetrize
  obtain ⟨G, hG⟩ := exists_polynomial_POVM_of_symmetric D hk T
    (S.symmetrize_bob_eq_alice) (S.symmetrize_state_swap) (S.symmetrize_isProjective hA hB)
  have hscore (b : Branch) :
      (branchGame (F := F) n d b).commutingWinProb S.symmetrize.toCommuting =
        (branchGame (F := F) n d b).commutingWinProb C := by
    rw [branchGame_eq_withDiagonalCap]
    exact commutingWinProb_branch_symmetrize S d ((n + 1) * d) b
  simp only [T, hscore, commutingWinProb_branch_symmetrize S d D .diagonal] at hG
  let Gₐ := G.restrictBasis Function.Embedding.inl
  let Gᵦ := G.restrictBasis Function.Embedding.inr
  refine ⟨Gₐ, Gᵦ, ?_⟩
  have h (u : Point F (n + 1)) :
      Measurement.agreement T.toCommuting.state
          ((QuantumStrategy.rightMeasurement (ι := ι ⊕ κ) G).map
            fun g => MvPolynomial.eval u g.val) (decodedPoint T.toCommuting.alice u) =
        (Measurement.agreement C.state (decodedPoint C.alice u)
            ((QuantumStrategy.rightMeasurement (ι := ι) Gᵦ).map
              fun g => MvPolynomial.eval u g.val) +
          Measurement.agreement C.state
            ((QuantumStrategy.leftMeasurement (κ := κ) Gₐ).map fun g => MvPolynomial.eval u g.val)
            (decodedPoint C.bob u)) / 2 := by
    rw [decodedPoint, decodedPoint, decodedPoint]
    refine Eq.trans ?_ (S.symmetrize_agreement (.point u) G decodePoint
      (fun g => MvPolynomial.eval u g.val))
    apply Measurement.agreement_comm
    exact fun a => (Measurement.commute_map_map _ _
      (QuantumStrategy.commute_liftedEffects (T.alice (.point u)) G)
      decodePoint (fun g => MvPolynomial.eval u g.val) a a).symm
  simp only [T] at h
  simp only [h, expect_sub_distrib, expect_add_distrib, ← expect_div, Fintype.expect_const] at hG
  have hₐ := expect_nonneg (s := univ) fun (u : Point F (n + 1)) _ => sub_nonneg.mpr <|
    Measurement.agreement_le_one C.state (decodedPoint C.alice u) _ <|
      Measurement.commute_map_map _ _
        (QuantumStrategy.commute_liftedEffects (S.alice (.point u)) Gᵦ) decodePoint
        (fun g => MvPolynomial.eval u g.val)
  have hᵦ := expect_nonneg (s := univ) fun (u : Point F (n + 1)) _ => sub_nonneg.mpr <|
    Measurement.agreement_le_one C.state _ (decodedPoint C.bob u) <|
      Measurement.commute_map_map _ _
        (QuantumStrategy.commute_liftedEffects Gₐ (S.bob (.point u)))
        (fun g => MvPolynomial.eval u g.val) decodePoint
  dsimp only
  simp only [expect_sub_distrib, Fintype.expect_const] at hₐ hᵦ ⊢
  exact ⟨by linarith only [hG, hᵦ],
    by linarith only [hG, hₐ]⟩

end Cslib.PCP.LowIndividualDegree
