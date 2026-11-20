/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PastingCompleteness
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
* `Cslib.PCP.LowIndividualDegree.average_completedPaste_disagreement_le_of_verifier` bounds
  disagreement after assigning failed outcomes to a fixed polynomial.
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

/-- The polynomial measurement obtained by assigning failure to an arbitrary fixed polynomial. -/
noncomputable def completedPaste (k : ℕ) [Nonempty (Fin k ↪ F)]
    (M : F → Measurement (Option (BoundedPolynomial F n d)) A)
    (hM : ∀ t, (M t).IsProjective) (fallback : BoundedPolynomial F (n + 1) d) :
    Measurement (BoundedPolynomial F (n + 1) d) A := by
  classical
  exact (pasteSlices k M hM).map (fun q => q.getD fallback)

open scoped Classical in
/-- Completion maps the pasted failure outcome to the fallback. -/
theorem completedPaste_eq_map (k : ℕ) [Nonempty (Fin k ↪ F)]
    (M : F → Measurement (Option (BoundedPolynomial F n d)) A)
    (hM : ∀ t, (M t).IsProjective) (fallback : BoundedPolynomial F (n + 1) d) :
    completedPaste k M hM fallback = (pasteSlices k M hM).map (fun q => q.getD fallback) := by
  unfold completedPaste
  rfl

open scoped Classical in
/-- The fallback outcome receives the original failure effect in addition to its
successful pasted effect. -/
theorem completedPaste_effect (k : ℕ) [Nonempty (Fin k ↪ F)]
    (M : F → Measurement (Option (BoundedPolynomial F n d)) A)
    (hM : ∀ t, (M t).IsProjective) (fallback p : BoundedPolynomial F (n + 1) d) :
    (completedPaste k M hM fallback).effect p =
      (if fallback = p then (pasteSlices k M hM).effect none else 0) +
        (pasteSlices k M hM).effect (some p) := by
  rw [completedPaste_eq_map, Measurement.map_getD_effect]

private theorem completedPaste_disagreement_le (k : ℕ) [Nonempty (Fin k ↪ F)]
    (S : RawStrategy) (M : F → Measurement (Option (BoundedPolynomial F n d)) A)
    (hM : ∀ t, (M t).IsProjective)
    (hComm : ∀ x q a b, Commute ((M x).effect a) ((S.bob q).effect b))
    (fallback : BoundedPolynomial F (n + 1) d) (w : Point F (n + 1)) :
    1 - Measurement.agreement S.state
        ((completedPaste k M hM fallback).map (fun p => MvPolynomial.eval w p.val))
        (decodedPoint S.bob w) ≤
      Measurement.successfulMismatch S.state (evaluatePolynomialMeasurement (pasteSlices k M hM) w)
        (decodedPoint S.bob w) + (S.state ((pasteSlices k M hM).effect none)).re := by
  classical
  let P := pasteSlices k M hM
  let z := MvPolynomial.eval w fallback.val
  have he : (completedPaste k M hM fallback).map (fun p => MvPolynomial.eval w p.val) =
      (evaluatePolynomialMeasurement P w).map (fun a => a.getD z) := by
    rw [completedPaste_eq_map]
    unfold evaluatePolynomialMeasurement
    simp only [Measurement.map_map]
    congr 1
    funext q
    cases q <;> rfl
  have hc : Commute ((evaluatePolynomialMeasurement P w).effect none)
      ((decodedPoint S.bob w).effect z) := by
    rw [evaluatePolynomialMeasurement_effect_none]
    exact Measurement.commute_map_right (S.bob (.point w)) decodePoint _
      (fun a => commute_pasteSlices k M hM _ (fun x q => hComm x (.point w) q a) none) z
  rw [he, ← evaluatePolynomialMeasurement_effect_none P w]
  exact Measurement.one_sub_agreement_map_getD_le _ _ _ _ hc

/-- Conditional pasting bound for the completed polynomial measurement against the verifier's
decoded point answers. The loss includes both disagreement on successful pasted outcomes
and the mass of failure filled in by the default polynomial. -/
theorem average_completedPaste_disagreement_le_of_verifier (k : ℕ) [Nonempty (Fin k ↪ F)]
    (hk : 0 < k) (S : RawStrategy) (M R : F → Measurement (Option (BoundedPolynomial F n d)) A)
    (hM : ∀ t, (M t).IsProjective) (hR : ∀ t, (R t).IsProjective)
    (hComm : ∀ x q a b, Commute ((M x).effect a) ((S.bob q).effect b))
    (hCopies : ∀ x y a b, Commute ((M x).effect a) ((R y).effect b))
    (fallback : BoundedPolynomial F (n + 1) d) {κ θ χ ζ η : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hsize : 2 * (d : ℝ) ≤ θ * k)
    (hmass : 1 - κ ≤ (S.state (Measurement.averageSuccessEffect R Option.isSome)).re)
    (hpair : (𝔼 x : F, 𝔼 y : F, Measurement.successfulPairDefect S.state (M x) (M y)) ≤ χ)
    (hcopy : (𝔼 x : F, Measurement.successfulCopyDefect S.state (M x) (R x)) ≤ ζ)
    (hpoint : (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state
      (evaluatePolynomialMeasurement (M t) u) (decodedPoint S.bob (Fin.snoc u t))) ≤ η) :
    let verticalError :=
      √(8 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) +
        4 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S))
    let sliceError := √(162 * χ + 176 * ζ)
    (𝔼 u : Point F n, 𝔼 t : F, (1 - Measurement.agreement S.state
      ((completedPaste k M hM fallback).map (fun p => MvPolynomial.eval (Fin.snoc u t) p.val))
      (decodedPoint S.bob (Fin.snoc u t)))) ≤
        κ / (1 - θ) + Real.exp (-(θ ^ 2 * k) / 2) +
        (1 + √2) * (k * √(2 * ζ) + (k : ℝ) ^ 2 * sliceError) +
        3 * ((k.choose 2 : ℝ) / Fintype.card F) + (n * d : ℝ) / Fintype.card F +
        2 * k * η + (2 * k + 1 : ℝ) * verticalError + 2 * k * ((k - 1 : ℕ) : ℝ) * sliceError := by
  let hCommLine (x u) := hComm x (.axis (verticalLine u))
  let T := decodedSliceLineStrategy S M hCommLine
  have hlocal := (average_isolatedSliceMismatch_le S M hCommLine).trans (add_le_add_left hpoint _)
  have hsuccess := pastedSuccessfulEffect_lower_bound k hk T hM R hR hCopies
    PolynomialFunction.value PolynomialFunction.exists_polynomial_value
    hθ₀ hθ₁ hsize hmass hpair hcopy hlocal
  have hagreement := average_pastedPointMismatch_le_of_verifier k S M R hM hR hComm hCopies
    hpair hcopy hpoint
  have hcomplete := expect_le_expect (s := (univ : Finset (Point F n))) fun u _ =>
    expect_le_expect (s := (univ : Finset F)) fun t _ =>
      completedPaste_disagreement_le k S M hM hComm fallback (Fin.snoc u t)
  simp only [expect_add_distrib, Fintype.expect_const,
    Measurement.effect_none_eq_one_sub_successfulEffect, map_sub, Complex.sub_re, S.state.map_one,
    Complex.one_re] at hcomplete
  dsimp [T, decodedSliceLineStrategy, sliceLineStrategy] at hsuccess
  simp only [mul_div_assoc (2 : ℝ)] at hsuccess
  dsimp only
  linarith

end Cslib.PCP.LowIndividualDegree
