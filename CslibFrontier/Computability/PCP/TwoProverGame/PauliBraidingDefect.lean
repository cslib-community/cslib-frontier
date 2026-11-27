/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingAnticommutation
public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingRounding
public import CslibFrontier.Foundations.Quantum.PauliCompression
import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingZero
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Order
import CslibFrontier.Foundations.Quantum.Algebra.Expect

/-!
# The Pauli-family defect from the CHSH braiding verifier

The rounded character observables are exactly linear on each player's factor.
Cross-player consistency controls their transfer to the other player's basis
observables. Using the other player allows the mixed operators to commute, as
required by the anticommutator transfer. The odd-pair estimate then supplies the
remaining hypothesis of the Pauli-family defect bound. The same estimate controls
the twisted commutation error used when the compression isometry intertwines the
individual Pauli generators.

## Main results

* `Cslib.PCP.exists_local_pauliFamily_of_pauliBraidingBranchScores`: the local
  rounded measurements and their tested Pauli-family defects.
* `Cslib.PCP.exists_local_pauliCompression_of_pauliBraidingGame`: local isometries
  compress the products and intertwine the individual rounded Pauli families from the full
  verifier score.
-/

public section

namespace Cslib.PCP

open Quantum BitString Finset Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder Real Kronecker

universe u v w

variable {n : ℕ} [Nonempty (Fin n)] {ι : Type u} {κ : Type v}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The squared distance budget between the two players' rounded basis observables
when each branch deficit is bounded by `ε`. -/
noncomputable def pauliBraidingRoundedConsistencyError (ε : ℝ) : ℝ :=
  6 * pauliBraidingRoundingError ε + 4 * (832 * ε)

@[simp]
theorem pauliBraidingRoundedConsistencyError_zero : pauliBraidingRoundedConsistencyError 0 = 0 := by
  simp [pauliBraidingRoundedConsistencyError]

/-- The mean squared twisted commutation error of the rounded X and Z families. -/
noncomputable def pauliBraidingTwistedCommutationError (ε : ℝ) : ℝ :=
  let r := pauliBraidingRoundingError ε
  let c := 832 * ε
  let a := (9 / 2) * (4096 * ε + 2 * chshAnticommConst * ε)
  64 * pauliBraidingRoundedConsistencyError ε + 33 * (9 * (2 * r + 2 * c + a))

/-- The tested Pauli-family multiplication defect budget when all three branch deficits are
at most `ε`. The coefficients are independent of the string width. -/
noncomputable def pauliBraidingRoundedDefectError (ε : ℝ) : ℝ :=
  5 * (8 * pauliBraidingRoundedConsistencyError ε + pauliBraidingTwistedCommutationError ε)

@[simp]
theorem pauliBraidingTwistedCommutationError_zero : pauliBraidingTwistedCommutationError 0 = 0 := by
  simp [pauliBraidingTwistedCommutationError]

@[simp]
theorem pauliBraidingRoundedDefectError_zero : pauliBraidingRoundedDefectError 0 = 0 := by
  simp [pauliBraidingRoundedDefectError]

omit [Nonempty (Fin n)] in
private theorem masked_expect_le_uniform_of_nonneg (f : (Fin n → Bool) → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (𝔼 a, if a = 0 then 0 else f a) ≤ 𝔼 a, f a :=
  expect_le_expect fun a _ => by split_ifs <;> first | exact hf a | exact le_rfl

omit [Nonempty (Fin n)] in
private theorem rounded_defect_le
    (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ))
    (P Q B : Bool → (Fin n → Bool) → Matrix (ι × κ) (ι × κ) ℂ)
    (hP : ∀ b x, P b x ∈ unitary (Matrix (ι × κ) (ι × κ) ℂ))
    (hQ : ∀ b x, Q b x ∈ unitary (Matrix (ι × κ) (ι × κ) ℂ))
    (hB : ∀ b x, star (B b x) * B b x ≤ 1)
    (hPQ : ∀ b b' x y, Commute (P b x) (Q b' y))
    (hPB : ∀ b b' x y, Commute (P b x) (B b' y))
    (hP0 : P false 0 = 1)
    (hlin : ∀ b x y, P b x * P b y = P b (x + y))
    {r c a : ℝ}
    (hround : ∀ b, 𝔼 x, φ.norm (P b x - B b x) ^ 2 ≤ 2 * r + 2 * c)
    (hcons : ∀ b, 𝔼 x, φ.norm (P b x - Q b x) ^ 2 ≤ 6 * r + 4 * c)
    (hac : oddExpect (fun x z => φ.norm (B false x * B true z + B true z * B false x) ^ 2) ≤ a) :
    let ξ := 64 * (6 * r + 4 * c) + 33 * (9 * (2 * r + 2 * c + a))
    let δ := 5 * (8 * (6 * r + 4 * c) + ξ)
    let F := pauliFamily (P false) (P true)
    ((𝔼 p, 𝔼 q, φ.norm (F p * F q - F (p * q)) ^ 2) ≤ δ) ∧
    ((𝔼 x, 𝔼 z, φ.norm (P true z * P false x -
      (signVal (x ⬝ᵥ z) : ℂ) • (P false x * P true z)) ^ 2) ≤ ξ) := by
  intro ξ δ F
  have hx : oddExpect (fun x _ => φ.norm (P false x - B false x) ^ 2) ≤ r + c := by
    rw [oddExpect_fst]
    have h := masked_expect_le_uniform_of_nonneg
      (fun x => φ.norm (P false x - B false x) ^ 2) (fun _ => sq_nonneg _)
    linarith only [h, hround false]
  have hz : oddExpect (fun _ z => φ.norm (P true z - B true z) ^ 2) ≤ r + c := by
    rw [oddExpect_snd]
    have h := masked_expect_le_uniform_of_nonneg
      (fun z => φ.norm (P true z - B true z) ^ 2) (fun _ => sq_nonneg _)
    linarith only [h, hround true]
  have htransfer :
      oddExpect (fun x z => φ.norm (P false x * P true z + P true z * P false x) ^ 2) ≤
        9 * (2 * r + 2 * c + a) := by
    have h := oddExpect_mono (f := fun x z =>
        φ.norm (P false x * P true z + P true z * P false x) ^ 2)
      (g := fun x z => 9 * (φ.norm (P false x - B false x) ^ 2 +
        φ.norm (P true z - B true z) ^ 2 +
        φ.norm (B false x * B true z + B true z * B false x) ^ 2)) (fun x z _ => by
        have ht := norm_mul_sub_smul_mul_sq_le_of_consistent φ
          (Unitary.star_mul_self_of_mem (hP false x)).le
          (Unitary.star_mul_self_of_mem (hP true z)).le (hB false x) (hB true z)
          (hPB false true x z) (hPB true false z x) (s := -1) (by simp)
        simpa only [neg_one_smul, sub_neg_eq_add, add_comm (P true z * P false x)] using ht)
    rw [oddExpect_const_mul, oddExpect_add, oddExpect_add] at h
    linarith only [h, hx, hz, hac]
  have hb := expect_norm_braid_sq_le φ (P false) (P true) (Q false) (Q true)
    (hP false) (hP true) (hQ false) (hQ true)
    (hPQ false true) (hPQ true true) (hPQ true false) hP0
  have hf := expect_norm_pauliFamily_sub_sq_le φ (P false) (P true) (Q true)
    (hP false) (hP true) (hQ true) (hPQ false true) (hPQ true true)
  simp only [hlin, sub_self, AlgState.norm_zero, zero_pow (by decide : 2 ≠ 0),
    Fintype.expect_const, add_zero, zero_add] at hb hf
  dsimp only [δ, ξ, F]
  exact ⟨by linarith only [hf, hb, hcons false, hcons true, htransfer],
    by linarith only [hb, hcons false, hcons true, htransfer]⟩

private theorem basis_anticomm_oddExpect_le
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) (Matrix (ι × κ) (ι × κ) ℂ))
    (roles : Bool) {ε : ℝ}
    (hcons : 1 - (pauliBraidingBranchGame n TwoProverGame.chsh id
      (fun _ => id) 2).commutingWinProb S ≤ ε)
    (hac : Real.cos (π / 8) ^ 2 - (pauliBraidingBranchGame n TwoProverGame.chsh id
      (fun _ => id) 1).commutingWinProb S ≤ ε) :
    let M := cond roles S.bob S.alice
    let B (b : Bool) (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable M b x d
    oddExpect (fun x z => S.state.norm (B false x * B true z + B true z * B false x) ^ 2) ≤
      (9 / 2) * (4096 * ε + 2 * chshAnticommConst * ε) := by
  intro M B
  let F (x z : Fin n → Bool) := S.state.norm (B false x * B true z + B true z * B false x) ^ 2
  have h := expect_norm_pauliBraidingBasis_anticomm_sq_le S roles
  change (𝔼 p : ↥(oddPairs (Fin n)), F p.val.1 p.val.2) ≤ _ at h
  change oddExpect F ≤ _
  rw [oddExpect_eq_dens_mul_expect]
  have hnonneg : 0 ≤ 𝔼 p : ↥(oddPairs (Fin n)), F p.val.1 p.val.2 :=
    expect_nonneg fun p _ => sq_nonneg _
  refine (mul_le_mul_of_nonneg_right dens_oddPairs_le_half hnonneg).trans
    ((mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (1 / 2 : ℝ))).trans ?_)
  have hconst := mul_le_mul_of_nonneg_left hac (show 0 ≤ 2 * chshAnticommConst by
    exact mul_nonneg (by norm_num) chshAnticommConst_nonneg)
  linarith only [hcons, hconst]

omit [Nonempty (Fin n)] in
private theorem commute_average_basisObservable
    (N : PauliBraidingQuestion n Bool → Measurement ((Bool × Bool) ⊕ Bool)
      (Matrix (ι × κ) (ι × κ) ℂ))
    (C : Matrix (ι × κ) (ι × κ) ℂ) (b : Bool) (x : Fin n → Bool)
    (h : ∀ q a, Commute C ((N q).effect a)) :
    Commute C (𝔼 d, pauliBraidingBasisObservable N b x d) := by
  change Commute C (𝔼 d, (pauliBraidingBasisBitMeasurement N b x d).observable)
  rw [← Measurement.observable_average]
  apply Commute.symm
  refine Measurement.commute_observable_average _ _ fun d => ?_
  apply Commute.symm
  change Commute C (((N _).map _).effect false - ((N _).map _).effect true)
  simp only [Measurement.map_effect]
  exact (Commute.sum_right _ _ _ fun a _ => h _ a).sub_right
    (Commute.sum_right _ _ _ fun a _ => h _ a)

omit [Nonempty (Fin n)] in
private theorem expect_sq_distance_comm
    (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ))
    (U V : (Fin n → Bool) → Matrix (ι × κ) (ι × κ) ℂ) :
    (𝔼 x, φ.norm (U x - V x) ^ 2) = 𝔼 x, φ.norm (V x - U x) ^ 2 :=
  expect_congr rfl fun x _ => by rw [φ.norm_sub_comm (U x)]

omit [Nonempty (Fin n)] in
private theorem cross_distances_le
    (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ))
    (P Q A B : (Fin n → Bool) → Matrix (ι × κ) (ι × κ) ℂ) {r c : ℝ}
    (hP : 𝔼 x, φ.norm (A x - P x) ^ 2 ≤ r)
    (hQ : 𝔼 x, φ.norm (B x - Q x) ^ 2 ≤ r)
    (hAB : 𝔼 x, φ.norm (A x - B x) ^ 2 ≤ c) :
    (𝔼 x, φ.norm (P x - B x) ^ 2) ≤ 2 * r + 2 * c ∧
      (𝔼 x, φ.norm (P x - Q x) ^ 2) ≤ 6 * r + 4 * c := by
  have hPB := φ.expect_norm_sub_sq_le_through univ P A B
  rw [expect_sq_distance_comm φ P A] at hPB
  have hc : (𝔼 x, φ.norm (P x - B x) ^ 2) ≤ 2 * r + 2 * c := by
    linarith only [hP, hAB, hPB]
  exact ⟨hc, by linarith only [hc, hQ, φ.expect_norm_sub_sq_le_through univ P B Q]⟩

omit [Nonempty (Fin n)] in
private theorem rounded_character_defect_le
    {η : Type w} [Fintype η] [DecidableEq η]
    (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ))
    (e : Matrix η η ℂ →⋆ₐ[ℂ] Matrix (ι × κ) (ι × κ) ℂ)
    (P : Bool → Measurement (Fin n → Bool) (Matrix η η ℂ))
    (hP : ∀ b, (P b).IsProjective)
    (Q B : Bool → (Fin n → Bool) → Matrix (ι × κ) (ι × κ) ℂ)
    (hQ : ∀ b x, Q b x ∈ unitary (Matrix (ι × κ) (ι × κ) ℂ))
    (hB : ∀ b x, star (B b x) * B b x ≤ 1)
    (hPQ : ∀ b b' x y, Commute (e ((P b).charObs x)) (Q b' y))
    (hPB : ∀ b b' x y, Commute (e ((P b).charObs x)) (B b' y))
    {r c a : ℝ}
    (hround : ∀ b, 𝔼 x, φ.norm (e ((P b).charObs x) - B b x) ^ 2 ≤ 2 * r + 2 * c)
    (hcons : ∀ b, 𝔼 x, φ.norm (e ((P b).charObs x) - Q b x) ^ 2 ≤ 6 * r + 4 * c)
    (hac : oddExpect (fun x z => φ.norm (B false x * B true z + B true z * B false x) ^ 2) ≤ a) :
    let X := fun x => e ((P false).charObs x)
    let Z := fun z => e ((P true).charObs z)
    let F := pauliFamily X Z
    let ξ := 64 * (6 * r + 4 * c) + 33 * (9 * (2 * r + 2 * c + a))
    let δ := 5 * (8 * (6 * r + 4 * c) + ξ)
    ((𝔼 p, 𝔼 q, φ.norm (F p * F q - F (p * q)) ^ 2) ≤ δ) ∧
    ((𝔼 x, 𝔼 z, φ.norm (Z z * X x - (signVal (x ⬝ᵥ z) : ℂ) • (X x * Z z)) ^ 2) ≤ ξ) := by
  intro X Z F ξ δ
  let U (b : Bool) (x : Fin n → Bool) := e ((P b).charObs x)
  have hU (b : Bool) (x : Fin n → Bool) : U b x ∈ unitary (Matrix (ι × κ) (ι × κ) ℂ) :=
    Unitary.map_mem _ ((hP b).charObs_mem_unitary x)
  exact rounded_defect_le φ U Q B hU hQ hB hPQ hPB
    (by simp only [U, Measurement.charObs_zero, map_one])
    (fun b x y => by simp only [U, ← map_mul, (hP b).charObs_mul])
    hround hcons hac

private theorem basis_cross_distance_le
    (T : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) (Matrix (ι × κ) (ι × κ) ℂ))
    (b : Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (hlin : 1 - (pauliBraidingBranchGame n TwoProverGame.chsh id
      (fun _ => id) 0).commutingWinProb T ≤ ε)
    (hcons : 1 - (pauliBraidingBranchGame n TwoProverGame.chsh id
      (fun _ => id) 2).commutingWinProb T ≤ ε) :
    let A (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable T.alice b x d
    let B (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable T.bob b x d
    (𝔼 x, T.state.norm (A x - B x) ^ 2) ≤ 832 * ε := by
  intro A B
  have h := expect_norm_pauliBraidingBasisObservable_sub_sq_le
    TwoProverGame.chsh id (fun _ => id) b T
  change (𝔼 x, T.state.norm (A x - B x) ^ 2) ≤ _ at h
  have hd0 : 0 ≤ ((oddPairs (Fin n)).dens : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcons (mul_nonneg (by norm_num : 0 ≤ (896 : ℝ)) hd0)
  have hhalf := mul_le_mul_of_nonneg_right (dens_oddPairs_le_half (ι := Fin n)) hε
  have hcap := mul_le_mul_of_nonneg_left hhalf (by norm_num : 0 ≤ (896 : ℝ))
  linarith only [h, hmul, hlin, hcap]

/-- The three branch scores of a single projective-basis tensor strategy bound the
Pauli-group multiplication defects of exactly linear character families on both original
factors. The families retain their bounds against the corresponding consistency observables. -/
theorem exists_local_pauliFamily_of_pauliBraidingBranchScores
    (S : QuantumStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) ι κ)
    (hA : ∀ basis q, (S.alice (.basis basis q)).toMeasurement.IsProjective)
    (hB : ∀ basis q, (S.bob (.basis basis q)).toMeasurement.IsProjective)
    {ε : ℝ}
    (hlin : 1 - ε ≤ (pauliBraidingBranchGame n TwoProverGame.chsh id
      (fun _ => id) 0).quantumWinProb S)
    (hcons : 1 - (pauliBraidingBranchGame n TwoProverGame.chsh id
      (fun _ => id) 2).quantumWinProb S ≤ ε)
    (hac : Real.cos (π / 8) ^ 2 - (pauliBraidingBranchGame n TwoProverGame.chsh id
      (fun _ => id) 1).quantumWinProb S ≤ ε) :
    let T := S.toCommuting
    ∃ (P : Bool → Measurement (Fin n → Bool) (Matrix ι ι ℂ))
      (Q : Bool → Measurement (Fin n → Bool) (Matrix κ κ ℂ)),
      (∀ b, (P b).IsProjective ∧ (Q b).IsProjective) ∧
      (∀ b, (𝔼 x, T.state.norm ((𝔼 d, pauliBraidingBasisObservable T.alice b x d) -
        kroneckerOne ((P b).charObs x)) ^ 2) ≤ pauliBraidingRoundingError ε ∧
        (𝔼 x, T.state.norm ((𝔼 d, pauliBraidingBasisObservable T.bob b x d) -
          oneKronecker ((Q b).charObs x)) ^ 2) ≤ pauliBraidingRoundingError ε) ∧
      (∀ b, (𝔼 x, T.state.norm (kroneckerOne ((P b).charObs x) -
        oneKronecker ((Q b).charObs x)) ^ 2) ≤ pauliBraidingRoundedConsistencyError ε) ∧
      (let X := fun x => kroneckerOne ((P false).charObs x)
       let Z := fun z => kroneckerOne ((P true).charObs z)
       let F := pauliFamily X Z
       ((𝔼 p, 𝔼 q, T.state.norm (F p * F q - F (p * q)) ^ 2) ≤
         pauliBraidingRoundedDefectError ε) ∧
       ((𝔼 x, 𝔼 z, T.state.norm (Z z * X x - (signVal (x ⬝ᵥ z) : ℂ) • (X x * Z z)) ^ 2) ≤
         pauliBraidingTwistedCommutationError ε)) ∧
      (let X := fun x => oneKronecker ((Q false).charObs x)
       let Z := fun z => oneKronecker ((Q true).charObs z)
       let F := pauliFamily X Z
       ((𝔼 p, 𝔼 q, T.state.norm (F p * F q - F (p * q)) ^ 2) ≤
         pauliBraidingRoundedDefectError ε) ∧
       ((𝔼 x, 𝔼 z, T.state.norm (Z z * X x - (signVal (x ⬝ᵥ z) : ℂ) • (X x * Z z)) ^ 2) ≤
         pauliBraidingTwistedCommutationError ε)) := by
  intro T
  let branch := pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id)
  choose P Q hP hQ hUclose hVclose using fun b =>
    exists_local_charObs_of_pauliBraidingLinearity
      TwoProverGame.chsh id (fun _ => id) S hA hB b hlin
  let U (b : Bool) (x : Fin n → Bool) := kroneckerOne (κ := κ) ((P b).charObs x)
  let V (b : Bool) (x : Fin n → Bool) := oneKronecker (ι := ι) ((Q b).charObs x)
  let A (b : Bool) (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable T.alice b x d
  let B (b : Bool) (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable T.bob b x d
  let r := pauliBraidingRoundingError ε
  let c := 832 * ε
  have hε : 0 ≤ ε := by
    have hm := SeededGame.answersWinProb_le_one (branch 0) S.answers
    change (branch 0).quantumWinProb S ≤ 1 at hm
    linarith only [hm, hlin]
  have hlin' : 1 - (branch 0).commutingWinProb T ≤ ε := by
    dsimp only [T]
    rw [SeededGame.commutingWinProb_toCommuting]
    linarith only [hlin]
  have hcons' : 1 - (branch 2).commutingWinProb T ≤ ε := by
    simpa only [T, SeededGame.commutingWinProb_toCommuting] using hcons
  have hac' : Real.cos (π / 8) ^ 2 - (branch 1).commutingWinProb T ≤ ε := by
    simpa only [T, SeededGame.commutingWinProb_toCommuting] using hac
  have hAB (b : Bool) : 𝔼 x, T.state.norm (A b x - B b x) ^ 2 ≤ c :=
    basis_cross_distance_le T b hε hlin' hcons'
  have hU (b : Bool) (x : Fin n → Bool) : U b x ∈ unitary (Matrix (ι × κ) (ι × κ) ℂ) :=
    Unitary.map_mem _ ((hP b).charObs_mem_unitary x)
  have hV (b : Bool) (x : Fin n → Bool) : V b x ∈ unitary (Matrix (ι × κ) (ι × κ) ℂ) :=
    Unitary.map_mem _ ((hQ b).charObs_mem_unitary x)
  have hUV (b b' : Bool) (x y : Fin n → Bool) : Commute (U b x) (V b' y) :=
    commute_kroneckerOne_oneKronecker _ _
  have hUB (b b' : Bool) (x y : Fin n → Bool) : Commute (U b x) (B b' y) := by
    apply commute_average_basisObservable
    intro q a
    change Commute (kroneckerOne _) (oneKronecker ((S.bob q).effect a))
    exact commute_kroneckerOne_oneKronecker _ _
  have hVA (b b' : Bool) (x y : Fin n → Bool) : Commute (V b x) (A b' y) := by
    apply commute_average_basisObservable
    intro q a
    change Commute (oneKronecker _) (kroneckerOne ((S.alice q).effect a))
    exact (commute_kroneckerOne_oneKronecker _ _).symm
  have hBA (b : Bool) : 𝔼 x, T.state.norm (B b x - A b x) ^ 2 ≤ c :=
    (expect_sq_distance_comm T.state (B b) (A b)).le.trans (hAB b)
  have hUD (b : Bool) :=
    cross_distances_le T.state (U b) (V b) (A b) (B b) (hUclose b) (hVclose b) (hAB b)
  have hVD (b : Bool) :=
    cross_distances_le T.state (V b) (U b) (B b) (A b) (hVclose b) (hUclose b) (hBA b)
  exact ⟨P, Q, fun b => ⟨hP b, hQ b⟩, fun b => ⟨hUclose b, hVclose b⟩, fun b => (hUD b).2,
    rounded_character_defect_le T.state kroneckerOne P hP V B hV
      (star_pauliBraidingBasisObservable_average_mul_self_le_one T.bob) hUV hUB
      (fun b => (hUD b).1) (fun b => (hUD b).2) (basis_anticomm_oddExpect_le T true hcons' hac'),
    rounded_character_defect_le T.state oneKronecker Q hQ U A hU
      (star_pauliBraidingBasisObservable_average_mul_self_le_one T.alice)
      (fun b b' x y => (hUV b' b y x).symm) hVA (fun b => (hVD b).1) (fun b => (hVD b).2)
      (basis_anticomm_oddExpect_le T false hcons' hac')⟩

/-- Local Pauli compression in a state restricted to a player's factor. The same
isometry controls the products and both individual Pauli families. -/
structure PauliBraidingLocalCompression {η : Type w} [Fintype η] [DecidableEq η]
    {J : Type*} [Fintype J] [DecidableEq J]
    (φ : AlgState (Matrix η η ℂ)) (X Z : (Fin n → Bool) → Matrix η η ℂ)
    (W : Matrix ((Fin n → Bool) × J) η ℂ) (δ ξ : ℝ) : Prop where
  /-- The columns of the local map are orthonormal. -/
  isometry : Wᴴ * W = 1
  /-- The averaged product compression error in the restricted state. -/
  products : (𝔼 x, 𝔼 z, φ.norm (X x * Z z -
    Wᴴ * ((pauliXPow x * pauliZPow z) ⊗ₖ (1 : Matrix J J ℂ)) * W) ^ 2) ≤ δ
  /-- The rounded Z observables intertwine exactly with the ideal Z observables. -/
  intertwinesZ : ∀ z, W * Z z = (pauliZPow z ⊗ₖ (1 : Matrix J J ℂ)) * W
  /-- The average squared discrepancy of intertwining the rounded X observables,
  evaluated by applying the restricted state to the Gram matrix of the discrepancy. -/
  intertwinesX : (𝔼 x, let D := W * X x - (pauliXPow x ⊗ₖ (1 : Matrix J J ℂ)) * W
    (φ (Dᴴ * D)).re) ≤ ξ

omit [Nonempty (Fin n)] in
private theorem compress_in_joint_state {η : Type w} [Fintype η] [DecidableEq η]
    (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ))
    (e : Matrix η η ℂ →⋆ₐ[ℂ] Matrix (ι × κ) (ι × κ) ℂ) (he : Monotone e)
    (P : Bool → Measurement (Fin n → Bool) (Matrix η η ℂ)) (hP : ∀ b, (P b).IsProjective)
    {δ ξ : ℝ}
    (hdef : let X := e ∘ (P false).charObs
      let Z := e ∘ (P true).charObs
      let F := pauliFamily X Z
      ((𝔼 p, 𝔼 q, φ.norm (F p * F q - F (p * q)) ^ 2) ≤ δ) ∧
      ((𝔼 x, 𝔼 z, φ.norm (Z z * X x - (signVal (x ⬝ᵥ z) : ℂ) • (X x * Z z)) ^ 2) ≤ ξ)) :
    ∃ (J : Type w) (_ : Fintype J) (_ : DecidableEq J)
      (W : Matrix ((Fin n → Bool) × J) η ℂ),
      PauliBraidingLocalCompression (φ.comap e he) (P false).charObs (P true).charObs W δ ξ := by
  let X := (P false).charObs
  let Z := (P true).charObs
  have hunitary (b : Bool) (x : Fin n → Bool) : ((P b).charObs x)ᴴ * (P b).charObs x = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem ((hP b).charObs_mem_unitary x)
  obtain ⟨J, _, _, W, hW, hZ, hproduct, hX⟩ := exists_isometry_compress_intertwine_pauliFamily X Z
    (hunitary false) (hunitary true)
    (hP false).charObs_mul (hP true).charObs_mul
  have hLift (p : PauliGroup (Fin n)) :
      e (pauliFamily X Z p) = pauliFamily (e ∘ X) (e ∘ Z) p := by
    simp only [pauliFamily, map_smul, map_mul, Function.comp_apply]
  let ψ := φ.comap e he
  refine ⟨J, inferInstance, inferInstance, W, hW, (hproduct ψ).trans ?_, hZ, ?_⟩
  · simpa only [ψ, AlgState.norm_comap, map_sub, map_mul, hLift] using hdef.1
  · have hmean : (𝔼 x, let D := W * X x - (pauliXPow x ⊗ₖ (1 : Matrix J J ℂ)) * W
          (ψ (Dᴴ * D)).re) =
        𝔼 x, 𝔼 z, ψ.norm (Z z * X x - (signVal (x ⬝ᵥ z) : ℂ) • (X x * Z z)) ^ 2 := by
      refine expect_congr rfl fun x _ => ?_
      dsimp only
      rw [hX x, ψ.re_apply_expect]
      simp only [AlgState.norm_sq, Matrix.star_eq_conjTranspose]
    refine hmean.le.trans ?_
    simpa only [ψ, AlgState.norm_comap, map_sub, map_mul, map_smul, Function.comp_apply]
      using hdef.2

private theorem quantum_branch_deficits_le
    (S : QuantumStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) ι κ)
    {ε : ℝ}
    (hwin : (2 + Real.cos (π / 8) ^ 2) / 3 - ε ≤
      (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).quantumWinProb S) :
    let branch := pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id)
    (1 - 3 * ε ≤ (branch 0).quantumWinProb S) ∧
    (1 - (branch 2).quantumWinProb S ≤ 3 * ε) ∧
    (Real.cos (π / 8) ^ 2 - (branch 1).quantumWinProb S ≤ 3 * ε) := by
  intro branch
  let T := S.toCommuting
  let upper (i : Fin 3) := if i = 1 then Real.cos (π / 8) ^ 2 else 1
  have hscore (i : Fin 3) : (branch i).answersWinProb T.answers = (branch i).quantumWinProb S :=
    (branch i).commutingWinProb_toCommuting S
  have hupper (i : Fin 3) : (branch i).answersWinProb T.answers ≤ upper i := by
    by_cases hi : i = 1
    · subst i
      exact commutingWinProb_pauliBraidingAnticommutation_le T
    · simp only [upper, hi, ite_false]
      exact (branch i).answersWinProb_le_one _
  have hmean : (∑ i, upper i) / 3 = (2 + Real.cos (π / 8) ^ 2) / 3 := by
    rw [Fin.sum_univ_three]
    simp only [upper, Fin.reduceEq, ite_true, ite_false]
    ring
  have hfull : (∑ i, upper i) / 3 - ε ≤
      (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).answersWinProb T.answers := by
    rw [hmean]
    exact (hwin.trans_eq ((pauliBraidingGame n TwoProverGame.chsh id
      (fun _ => id)).commutingWinProb_toCommuting S).symm)
  have hδ (i : Fin 3) : upper i - (branch i).quantumWinProb S ≤ 3 * ε := by
    rw [← hscore]
    exact pauliBraidingBranch_deficit_le TwoProverGame.chsh id (fun _ => id) T.answers
      upper hupper hfull i
  have hzero := hδ 0
  simp only [upper, Fin.reduceEq, ite_false] at hzero
  refine ⟨by linarith only [hzero], ?_, ?_⟩
  · simpa only [upper, Fin.reduceEq, ite_false] using hδ 2
  · simpa only [upper, ite_true, eq_self] using hδ 1

/-- Near the mean of the branch upper bounds, a projective-basis tensor strategy admits
local isometries compressing the rounded products and intertwining the individual
Pauli families. The estimates use the original joint state via its restrictions to each factor. -/
theorem exists_local_pauliCompression_of_pauliBraidingGame
    (S : QuantumStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) ι κ)
    (hA : ∀ basis q, (S.alice (.basis basis q)).toMeasurement.IsProjective)
    (hB : ∀ basis q, (S.bob (.basis basis q)).toMeasurement.IsProjective)
    {ε : ℝ}
    (hwin : (2 + Real.cos (π / 8) ^ 2) / 3 - ε ≤
      (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).quantumWinProb S) :
    let T := S.toCommuting
    ∃ (P : Bool → Measurement (Fin n → Bool) (Matrix ι ι ℂ))
      (Q : Bool → Measurement (Fin n → Bool) (Matrix κ κ ℂ)),
      (∀ b, (P b).IsProjective ∧ (Q b).IsProjective) ∧
      (∀ b, (𝔼 x, T.state.norm ((𝔼 d, pauliBraidingBasisObservable T.alice b x d) -
        kroneckerOne ((P b).charObs x)) ^ 2) ≤ pauliBraidingRoundingError (3 * ε) ∧
        (𝔼 x, T.state.norm ((𝔼 d, pauliBraidingBasisObservable T.bob b x d) -
          oneKronecker ((Q b).charObs x)) ^ 2) ≤ pauliBraidingRoundingError (3 * ε)) ∧
      (∀ b, (𝔼 x, T.state.norm (kroneckerOne ((P b).charObs x) -
        oneKronecker ((Q b).charObs x)) ^ 2) ≤ pauliBraidingRoundedConsistencyError (3 * ε)) ∧
      (∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J)
        (W : Matrix ((Fin n → Bool) × J) ι ℂ),
        PauliBraidingLocalCompression (T.state.comap kroneckerOne (OrderHomClass.mono _))
          (P false).charObs (P true).charObs W (pauliBraidingRoundedDefectError (3 * ε))
          (pauliBraidingTwistedCommutationError (3 * ε))) ∧
      (∃ (J : Type v) (_ : Fintype J) (_ : DecidableEq J)
        (W : Matrix ((Fin n → Bool) × J) κ ℂ),
        PauliBraidingLocalCompression (T.state.comap oneKronecker (OrderHomClass.mono _))
          (Q false).charObs (Q true).charObs W (pauliBraidingRoundedDefectError (3 * ε))
          (pauliBraidingTwistedCommutationError (3 * ε))) := by
  intro T
  obtain ⟨hlin, hcons, hac⟩ := quantum_branch_deficits_le S hwin
  obtain ⟨P, Q, hproj, hclose, hcross, hP, hQ⟩ :=
    exists_local_pauliFamily_of_pauliBraidingBranchScores S hA hB hlin hcons hac
  exact ⟨P, Q, hproj, hclose, hcross,
    compress_in_joint_state T.state kroneckerOne (OrderHomClass.mono _) P (fun b => (hproj b).1) hP,
    compress_in_joint_state T.state oneKronecker (OrderHomClass.mono _) Q (fun b => (hproj b).2) hQ⟩

end Cslib.PCP
