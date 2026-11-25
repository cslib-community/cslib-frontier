/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.ProjectiveSoundness
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.Soundness
import CslibFrontier.Probability.PMF.Event

/-!
# Classical soundness of the low-individual-degree test

Apply tensor soundness to the one-dimensional strategy given by two deterministic provers.
The polynomial POVM gives a probability distribution on bounded-individual-degree polynomials.
One polynomial in this finite space has at most the mean disagreement with Alice's decoded point
answers. The consistency branch bounds the added loss when we require both original answers to
be the correct field value, including the requirement that they are point answers.

## Main results

* `Cslib.PCP.LowIndividualDegree.exists_polynomial_of_classical_winProb`: one polynomial
  approximates both deterministic provers with error controlled by the full verifier score.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset
open scoped BigOperators Kronecker MatrixOrder ComplexOrder

variable {F : Type*} {n d : ℕ} [Field F] [Fintype F] [DecidableEq F]

local notation "Pt" => Point F (n + 1)
local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)
local notation "Poly" => BoundedPolynomial F (n + 1) d

open Classical in
private theorem consistency_loss_eq_expect (a b : Q → Ans) :
    1 - (branchGame (F := F) n d .consistency).winProb a b =
      𝔼 u : Pt, if accepts d (.point u) (.point u) (a (.point u)) (b (.point u))
        then (0 : ℝ) else 1 := by
  let event : Set Pt := {u | accepts d (.point u) (.point u) (a (.point u)) (b (.point u))}
  let U := Probability.PMF.uniformOfFintype Pt
  have hscore : (branchGame (F := F) n d .consistency).winProb a b =
      (U.toOuterMeasure event).toReal := by
    rw [TwoProverGame.winProb, branchGame_questions, branchQuestions_consistency,
      consistencyQuestions, branchGame_accepts, PMF.toOuterMeasure_map_apply]
    rfl
  rw [hscore]
  have hs := Probability.PMF.toOuterMeasure_toReal_add_compl U event
  have he : (U.toOuterMeasure eventᶜ).toReal =
      𝔼 u : Pt, if accepts d (.point u) (.point u) (a (.point u)) (b (.point u))
        then (0 : ℝ) else 1 := by
    rw [Probability.PMF.toOuterMeasure_toReal_eq_sum_ite, Fintype.expect_eq_sum_div_card,
      div_eq_inv_mul, Finset.mul_sum]
    simp only [U, Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Set.mem_compl_iff, event, Set.mem_ofPred_eq, ite_not]
  rw [← he]
  linarith

private theorem exists_poly_decoded_loss_le (a b : Q → Ans) {k : ℕ} (hk : (n + 1) * d ≤ k) :
    let ε := 1 - (game (F := F) n d).winProb a b
    ∃ g : Poly, (𝔼 u : Pt, if decodePoint (a (.point u)) = MvPolynomial.eval u g.val
        then (0 : ℝ) else 1) ≤
      (soundnessErrors (n + 1) k ε ((d : ℝ) / Fintype.card F)).point := by
  classical
  intro ε
  let S := QuantumStrategy.ofDeterministic a b
  let φ := S.toCommuting.state
  obtain ⟨_, P, h, _, _⟩ := exists_polynomial_POVMs_of_winProb hk S
  let R := QuantumStrategy.rightMeasurement (ι := Fin 1) P
  let w (g : Poly) := R.prob φ g
  let cost (g : Poly) (u : Pt) : ℝ :=
    if decodePoint (a (.point u)) = MvPolynomial.eval u g.val then 0 else 1
  have hw : ∑ g, w g = 1 := R.sum_prob φ
  have hw₀ (g : Poly) : 0 ≤ w g := φ.re_apply_nonneg (R.nonneg g)
  have hpoint (u : Pt) : Measurement.agreement φ (decodedPoint S.toCommuting.alice u)
      (R.map fun g => MvPolynomial.eval u g.val) =
      ∑ g, if decodePoint (a (.point u)) = MvPolynomial.eval u g.val then w g else 0 := by
    rw [decodedPoint, Measurement.agreement_map_map, sum_comm]
    refine sum_congr rfl fun g _ => ?_
    rw [sum_eq_single (a (.point u))]
    · simp [S, QuantumStrategy.toCommuting, QuantumStrategy.ofDeterministic,
        QuantumStrategy.leftMeasurement, POVM.const, w, Measurement.prob]
    · intro z _ hz
      simp [S, QuantumStrategy.toCommuting, QuantumStrategy.ofDeterministic,
        QuantumStrategy.leftMeasurement, POVM.const, hz]
    · simp
  have hcost (u : Pt) : 1 - Measurement.agreement φ (decodedPoint S.toCommuting.alice u)
      (R.map fun g => MvPolynomial.eval u g.val) = ∑ g, w g * cost g u := by
    rw [hpoint, ← hw, ← sum_sub_distrib]
    refine sum_congr rfl fun g _ => ?_
    unfold cost
    split_ifs <;> simp
  change (𝔼 u : Pt, (1 - Measurement.agreement φ (decodedPoint S.toCommuting.alice u)
    (R.map fun g => MvPolynomial.eval u g.val))) ≤ _ at h
  simp_rw [hcost, expect_sum_comm, ← mul_expect, S,
    TwoProverGame.quantumWinProb_ofDeterministic] at h
  let : Nonempty Poly := ⟨⟨0, by simp⟩⟩
  obtain ⟨g, hg⟩ := Finite.exists_min fun g : Poly => 𝔼 u : Pt, cost g u
  refine ⟨g, le_trans ?_ h⟩
  calc
    (𝔼 u : Pt, cost g u) = ∑ p, w p * (𝔼 u : Pt, cost g u) := by
      rw [← sum_mul, hw, one_mul]
    _ ≤ ∑ p, w p * (𝔼 u : Pt, cost p u) :=
      sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hg p) (hw₀ p)

open Classical in
/-- One bounded-individual-degree polynomial simultaneously explains the raw point answers
of both deterministic provers, except on a fraction bounded by the point error plus three times
the full verifier's rejection probability. -/
theorem exists_polynomial_of_classical_winProb (a b : Q → Ans) {k : ℕ} (hk : (n + 1) * d ≤ k) :
    let ε := 1 - (game (F := F) n d).winProb a b
    ∃ g : Poly,
      (𝔼 u : Pt, if a (.point u) = Sum.inl (MvPolynomial.eval u g.val) ∧
          b (.point u) = Sum.inl (MvPolynomial.eval u g.val) then (0 : ℝ) else 1) ≤
        (soundnessErrors (n + 1) k ε ((d : ℝ) / Fintype.card F)).point + 3 * ε := by
  intro ε
  obtain ⟨g, h⟩ := exists_poly_decoded_loss_le a b hk
  have hbranch : 1 - (branchGame (F := F) n d .consistency).winProb a b ≤ 3 * ε := by
    classical
    let S := QuantumStrategy.ofDeterministic a b
    have h0 : 1 - (branchGame (F := F) n d .consistency).quantumWinProb S ≤
        3 * (1 - (game (F := F) n d).quantumWinProb S) :=
      branch_loss_le_three_mul n d .consistency S.answers
    simpa only [S, TwoProverGame.quantumWinProb_ofDeterministic] using h0
  rw [consistency_loss_eq_expect] at hbranch
  refine ⟨g, le_trans ?_ (add_le_add h hbranch)⟩
  rw [← expect_add_distrib]
  refine expect_le_expect fun u _ => ?_
  by_cases hu : accepts d (.point u) (.point u) (a (.point u)) (b (.point u))
  · obtain ⟨c, ha, hb⟩ := exists_eq_of_accepts_points d u u _ _ hu
    rw [ite_eq_left hu, ha, hb]
    simp
  · rw [ite_eq_right hu]
    split_ifs <;> norm_num

end Cslib.PCP.LowIndividualDegree
