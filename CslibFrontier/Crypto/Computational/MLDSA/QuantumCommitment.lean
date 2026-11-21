/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQueryUpdate
public import CslibFrontier.Crypto.Computational.MLDSA.SplitMatrix
public import Mathlib.Algebra.Ring.BooleanRing
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Reprogramming one ML-DSA commitment after coherent hash queries

A quantum adversary measures a 512-bit message representative after T coherent XOR queries.
The signing experiment draws a fresh ideal mask and programs the FIPS 204 commitment hash at
its literal bit-string input. The measured message, the programmed address, the current hash
table and the residual quantum state are available to the continuation.

For a uniform public matrix the mean square root of the largest commitment probability is
bounded by the rounded-commitment count and its kernel moment. This yields the numerical bound
at each FIPS 204 level after one refresh. The quantum step uses [BBBV1997].
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Quantum Finset
open scoped BigOperators ENNReal

variable (s : Level)

private def rawCommitment (p : BitString 512 × (Fin s.params.k → Poly)) : List Bool :=
  commitmentInput s (highBitsVec s.params p.2) (List.ofFn p.1)

/-- The finite oracle addresses contain every FIPS 204 commitment input, together with any
additional raw hash inputs admitted by the adversary's finite query register. Equal strings
from different uses name the same table entry. -/
noncomputable def commitmentAddresses (extra : Finset (List Bool)) : Finset (List Bool) :=
  extra ∪ univ.image (rawCommitment s)

/-- A coherent response register has one bit per bit of the commitment digest. -/
abbrev DigestRegister := BitString (8 * digestBytes s)

private theorem mem_extra_union_image {X Y : Type*} [Fintype X] [DecidableEq Y]
    (extra : Finset Y) (f : X → Y) (x : X) : f x ∈ extra ∪ univ.image f :=
  mem_union_right _ (mem_image_of_mem f (mem_univ x))

private def encodedAddress (extra : Finset (List Bool)) (μ : BitString 512)
    (r : Fin s.params.k → Poly) : commitmentAddresses s extra :=
  ⟨rawCommitment s (μ, r), mem_extra_union_image extra (rawCommitment s) (μ, r)⟩

private theorem gamma_pos : 0 < s.params.γ₁ := by cases s <;> decide

/-- The actual SHAKE input for a fresh ideal signing mask at a chosen message representative. -/
noncomputable def signingAddressLaw (extra : Finset (List Bool))
    (A : PublicMatrix s) (μ : BitString 512) :
    PMF (commitmentAddresses s extra) :=
  (signingMaskLaw s.params (gamma_pos s)).map fun y => encodedAddress s extra μ (moduleSISMap A y)

private theorem signingAddressLaw_le (extra : Finset (List Bool)) (A : PublicMatrix s)
    (μ : BitString 512) (i : commitmentAddresses s extra) :
    signingAddressLaw s extra A μ i ≤ commitmentGuessProbability s.params (gamma_pos s) A := by
  classical
  let d := signingMaskLaw s.params (gamma_pos s)
  let f (y : Fin s.params.ℓ → Poly) := highBitsVec s.params (moduleSISMap A y)
  let addr (y : Fin s.params.ℓ → Poly) := encodedAddress s extra μ (moduleSISMap A y)
  change d.map addr i ≤ _
  by_cases hi : i ∈ (d.map addr).support
  · obtain ⟨y, _, rfl⟩ := (PMF.mem_support_map_iff ..).1 hi
    refine le_trans ?_ (le_iSup (fun w => d.map f w) (f y))
    rw [PMF.map_apply, PMF.map_apply]
    refine tsum_le_tsum fun z => ?_
    by_cases eq : addr y = addr z
    · have hb (r : Fin s.params.k → Poly) (j k) : 0 ≤ highBits s.params.q s.params.γ₂ (r j k) ∧
          highBits s.params.q s.params.γ₂ (r j k) <
            (((s.params.q - 1) / (2 * s.params.γ₂) : ℕ) : ℤ) :=
        ⟨highBits_nonneg (by cases s <;> decide) _, highBits_lt (by cases s <;> decide)
          (by cases s <;> decide) (by cases s <;> decide) _⟩
      have hw : f y = f z := eq_of_commitmentInput_eq (hb _) (hb _) (congrArg Subtype.val eq)
      simp [eq, hw]
    · simp [eq]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hi]

variable (extra : Finset (List Bool)) {W κ : Type*} [Fintype W] [Fintype κ]

/-- Final acceptance probability of the one-commitment experiment, averaged over the public
matrix and the hash table. The adversary's query isometries, initial state and measurement
of the message may all depend on the public matrix. After the address is sampled, the
continuation sees either the original table or the table with a fresh uniform digest there. -/
noncomputable def commitmentRefreshProbability (refresh : Bool) (T : ℕ)
    (U : PublicMatrix s → ℕ →
      ValueState (commitmentAddresses s extra) (DigestRegister s) W →ₗᵢ[ℂ]
      ValueState (commitmentAddresses s extra) (DigestRegister s) W)
    (ψ : PublicMatrix s →
      ValueState (commitmentAddresses s extra) (DigestRegister s) W)
    (readout : PublicMatrix s →
      (commitmentAddresses s extra) × DigestRegister s × W → BitString 512)
    (post : PublicMatrix s →
      (commitmentAddresses s extra → DigestRegister s) → BitString 512 →
      commitmentAddresses s extra →
      ValueState (commitmentAddresses s extra) (DigestRegister s) W →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (accept : PublicMatrix s →
      (commitmentAddresses s extra → DigestRegister s) → BitString 512 →
      commitmentAddresses s extra → Finset κ) : ℝ :=
  𝔼 A, 𝔼 hv : (commitmentAddresses s extra → DigestRegister s) × DigestRegister s,
    ∑ m, ∑ i, (signingAddressLaw s extra A m i).toReal *
      let H := if refresh then Function.update hv.1 i hv.2 else hv.1
      measureProb (post A H m i (projOutcomes (fun x => readout A x = m)
        (runValue addStep (U A) (ψ A) hv.1 T))) (accept A H m i)

private theorem abs_refresh_sub_le_mean (T : ℕ)
    (U ψ readout post accept) (hψ : ∀ A, ‖ψ A‖ = 1) :
    |commitmentRefreshProbability s extra true (W := W) (κ := κ) T U ψ readout post accept -
      commitmentRefreshProbability s extra false T U ψ readout post accept| ≤
      2 * T * (𝔼 A, Real.sqrt (commitmentGuessProbability s.params (gamma_pos s) A).toReal) := by
  classical
  let d (A : PublicMatrix s) := (commitmentGuessProbability s.params (gamma_pos s) A).toNNReal
  have finite (A : PublicMatrix s) : commitmentGuessProbability s.params (gamma_pos s) A ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => PMF.coe_le_one _ _)
  unfold commitmentRefreshProbability
  rw [← expect_sub_distrib, mul_expect]
  refine (abs_expect_le _ _).trans (expect_le_expect fun A _ => ?_)
  simpa only [Bool.false_eq_true, ↓reduceIte, d, ENNReal.coe_toNNReal_eq_toReal] using
    abs_readout_reprogrammed_measureProb_sub_le addStep (U A) (ψ A) (hψ A) T (readout A)
        (signingAddressLaw s extra A) (δ := d A)
        (fun m i => ENNReal.toReal_mono (finite A) (signingAddressLaw_le s extra A m i))
        (post A) (accept A)

/-- The distinguishing advantage for one fresh ideal signing commitment after `T` coherent
queries. The right-hand side is numerical at every FIPS 204 level. -/
theorem abs_commitmentRefreshProbability_sub_le_fips (T : ℕ) (U ψ readout post accept)
    (hψ : ∀ A, ‖ψ A‖ = 1) :
    |commitmentRefreshProbability s extra true (W := W) (κ := κ) T U ψ readout post accept -
      commitmentRefreshProbability s extra false T U ψ readout post accept| ≤
      2 * T * ((11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits)) := by
  refine (abs_refresh_sub_le_mean s extra T U ψ readout post accept hψ).trans ?_
  exact mul_le_mul_of_nonneg_left (mean_sqrt_commitmentGuessProbability_le s) (by positivity)

end Cslib.Crypto.MLDSA.FIPS204
