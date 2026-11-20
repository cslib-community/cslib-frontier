/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PastingConsistency
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerticalAxis

/-!
# Pasting with the low-individual-degree verifier

The isolated slice mismatch in the pasting argument is the disagreement on successful
evaluated slice outcomes. This identifies the probabilistic comparison in pasting with
the operator estimate obtained from the verifier's axis and consistency branches.

## Main results

* `Cslib.PCP.LowIndividualDegree.average_pastedLineMismatch_le_of_verifier` bounds the
  successful pasted measurement's mismatch against the decoded vertical line.
* `Cslib.PCP.LowIndividualDegree.average_pastedPointMismatch_le_of_verifier` transfers
  this bound back to the verifier's decoded point measurement.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset Cslib.Quantum
open scoped BigOperators Real

variable {F A : Type*} {n d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local notation "RawStrategy" => CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
  (Answer F (n + 1)) (Answer F (n + 1)) A

/-- The slice-vs-line comparison against the verifier's decoded Bob measurement. -/
@[expose] noncomputable def decodedSliceLineStrategy (S : RawStrategy)
    (M : F → Measurement (Option (BoundedPolynomial F n d)) A)
    (hComm : ∀ t u a b, Commute ((M t).effect a) ((S.bob (.axis (verticalLine u))).effect b)) :
    CommutingStrategy F (Point F n) (Option (BoundedPolynomial F n d))
      (PolynomialFunction F d) A :=
  sliceLineStrategy S.state M (decodedVertical S.bob d) fun t u a b =>
    Measurement.commute_map_right _ (decodeVertical d u) _ (hComm t u a) b

/-- The isolated slice mismatch for the decoded vertical line is bounded by the slice
mismatch for Bob's point answer and the verifier's two branch losses. -/
theorem average_isolatedSliceMismatch_le (S : RawStrategy)
    (M : F → Measurement (Option (BoundedPolynomial F n d)) A)
    (hComm : ∀ t u a b, Commute ((M t).effect a) ((S.bob (.axis (verticalLine u))).effect b)) :
    (𝔼 u : Point F n, 𝔼 t : F,
      isolatedSliceMismatch (decodedSliceLineStrategy S M hComm)
        PolynomialFunction.value u t) ≤
    (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state
      (evaluatePolynomialMeasurement (M t) u) (decodedPoint S.bob (Fin.snoc u t))) +
      √(8 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) +
        4 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S)) := by
  simpa only [isolatedSliceMismatch_eq_successfulMismatch, decodedSliceLineStrategy,
    sliceLineStrategy] using
    successfulMismatch_vertical_le S d (fun u t => evaluatePolynomialMeasurement (M t) u)

/-- The successful mismatch of the pasted measurement against Bob's decoded vertical
line is controlled by the verifier losses, slice-point mismatch and slice defects. -/
theorem average_pastedLineMismatch_le_of_verifier (k : ℕ) [Nonempty (Fin k ↪ F)]
    (S : RawStrategy) (M R : F → Measurement (Option (BoundedPolynomial F n d)) A)
    (hM : ∀ t, (M t).IsProjective) (hR : ∀ t, (R t).IsProjective)
    (hComm : ∀ t u a b, Commute ((M t).effect a) ((S.bob (.axis (verticalLine u))).effect b))
    (hCopies : ∀ x y a b, Commute ((M x).effect a) ((R y).effect b))
    {χ ζ η : ℝ}
    (hpair : (𝔼 x : F, 𝔼 y : F, Measurement.successfulPairDefect S.state (M x) (M y)) ≤ χ)
    (hcopy : (𝔼 x : F, Measurement.successfulCopyDefect S.state (M x) (R x)) ≤ ζ)
    (hpoint : (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state
      (evaluatePolynomialMeasurement (M t) u) (decodedPoint S.bob (Fin.snoc u t))) ≤ η) :
    (𝔼 u : Point F n, 𝔼 t : F,
      Measurement.successfulMismatch S.state
        (evaluatePolynomialMeasurement (pasteSlices k M hM) (Fin.snoc u t))
        ((decodedVertical S.bob d u).map (fun f => f.value t))) ≤
      (k.choose 2 : ℝ) / Fintype.card F +
        k * (η + √(8 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) +
          4 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S))) +
        k * ((k - 1 : ℕ) : ℝ) * √(162 * χ + 176 * ζ) := by
  classical
  let _ : Fintype (Fin k ↪ F) := Fintype.ofFinite _
  let T := decodedSliceLineStrategy S M hComm
  have h (u : Point F n) (t : F) := successfulMismatch_pasteSlices_eq_expect k T hM
    PolynomialFunction.value u t
  change (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch T.state
    (evaluatePolynomialMeasurement (pasteSlices k T.alice hM) (Fin.snoc u t))
      ((T.bob u).map (fun f => f.value t))) ≤ _
  simp only [h, Finset.expect_comm (ι := F) (κ := Fin k ↪ F) univ univ]
  refine (average_pastedLineMismatch_le_of_successful k T
    hM R hR hCopies PolynomialFunction.value PolynomialFunction.exists_polynomial_value
    hpair hcopy).trans ?_
  gcongr
  exact (average_isolatedSliceMismatch_le S M hComm).trans (add_le_add_left hpoint _)

/-- Conditional consistency bound for the successful pasted polynomial measurement
against the verifier's original point measurement after decoding. The three slice bounds
are the inputs needed from the lower-dimensional construction. -/
theorem average_pastedPointMismatch_le_of_verifier (k : ℕ) [Nonempty (Fin k ↪ F)]
    (S : RawStrategy) (M R : F → Measurement (Option (BoundedPolynomial F n d)) A)
    (hM : ∀ t, (M t).IsProjective) (hR : ∀ t, (R t).IsProjective)
    (hComm : ∀ x q a b, Commute ((M x).effect a) ((S.bob q).effect b))
    (hCopies : ∀ x y a b, Commute ((M x).effect a) ((R y).effect b))
    {χ ζ η : ℝ}
    (hpair : (𝔼 x : F, 𝔼 y : F, Measurement.successfulPairDefect S.state (M x) (M y)) ≤ χ)
    (hcopy : (𝔼 x : F, Measurement.successfulCopyDefect S.state (M x) (R x)) ≤ ζ)
    (hpoint : (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state
      (evaluatePolynomialMeasurement (M t) u) (decodedPoint S.bob (Fin.snoc u t))) ≤ η) :
    (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state
      (evaluatePolynomialMeasurement (pasteSlices k M hM) (Fin.snoc u t))
      (decodedPoint S.bob (Fin.snoc u t))) ≤
        (k.choose 2 : ℝ) / Fintype.card F + k * η +
          (k + 1 : ℝ) *
            √(8 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) +
              4 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S)) +
          k * ((k - 1 : ℕ) : ℝ) * √(162 * χ + 176 * ζ) := by
  have hline := average_pastedLineMismatch_le_of_verifier k S M R hM hR
    (fun x u => hComm x (.axis (verticalLine u))) hCopies hpair hcopy hpoint
  have htransfer := sub_le_iff_le_add'.mp
    (abs_sub_le_iff.mp (successfulMismatch_vertical_abs_sub_le S d
      (fun u t => evaluatePolynomialMeasurement (pasteSlices k M hM) (Fin.snoc u t)))).2
  exact htransfer.trans ((add_le_add_left hline _).trans_eq (by ring))

end Cslib.PCP.LowIndividualDegree
