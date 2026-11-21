/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Sequential
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.Pasting
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialMeasurement
public import CslibFrontier.Foundations.Quantum.Algebra.CompletedMeasurement
public import CslibFrontier.Foundations.Quantum.Algebra.SuccessfulAgreement
public import CslibFrontier.Probability.PMF.Event
public import Mathlib.Algebra.BigOperators.Expect
import CslibFrontier.Probability.IID.Distinct
import Mathlib.Algebra.Order.BigOperators.Expect
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Union
import Mathlib.Algebra.Polynomial.Roots

/-!
# Pasted polynomial agreement with vertical lines

The polynomial comparison in [Ji, Natarajan, Vidick, Wright and Yuen, Lemma 12.17]
[JNVWY2020LowIndividualDegree] uses the successful transcript of the sequential slice
measurements. If a pasted polynomial disagrees with the vertical line answer, some successful
slice must already disagree at its sampled coordinate. Indeed, the line answer and the
restriction of the pasted polynomial have degree at most `d` and at least `d + 1` distinct
points of comparison. This gives a probability bound by the sum of the individual slice
mismatch probabilities under the joint law of the transcript and line answer.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset MvPolynomial Cslib.Probability.PMF
open scoped BigOperators Real

variable {F ι β : Type*} {m d : ℕ} [Field F]

/-- The vertical line above `u) of a pasted polynomial is determined by the successful
slice values on that line. -/
theorem evalPrefix_eq_of_paste_agrees [Fintype ι] (x : ι ↪ F) (u : Fin m → F)
    {g : ι → Option (BoundedPolynomial F m d)} {p : BoundedPolynomial F (m + 1) d}
    (hp : pasteOutcome x g = some p) {f : Polynomial F} (hf : f.natDegree ≤ d)
    (hagree : ∀ j q, g j = some q → eval u q.val = f.eval (x j)) :
    evalPrefix u p.val = f := by
  classical
  obtain ⟨hcard, hfits⟩ := (pasteOutcome_eq_some_iff x g p).mp hp
  let s := successfulSlices g
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (ι := s)
    ((x.injective.comp Subtype.val_injective) :
      Function.Injective fun j : s => x j.val)
  · intro j
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (mem_successfulSlices.mp j.prop)
    rw [eval_evalPrefix]
    have he := congrArg (fun q : BoundedPolynomial F m d => eval u q.val) (hfits j q hq)
    exact he.trans (hagree j q hq)
  · rw [Fintype.card_coe]
    exact max_lt ((natDegree_evalPrefix_le _ _).trans_lt
      ((p.prop (Fin.last m)).trans_lt hcard)) (hf.trans_lt hcard)

/-- Mismatch on a successful slice at the vertical line's intersection with it. -/
@[expose] def sliceLineMismatch (u : Fin m → F) (x : ι → F) (lineValue : β → F → F) (i : ι) :
    Set ((ι → Option (BoundedPolynomial F m d)) × β) :=
  {g | ∃ q, g.1 i = some q ∧ eval u q.val ≠ lineValue g.2 (x i)}

/-- Mismatch at a point of the vertical line when the pasted readout succeeded.
A failure outcome contributes zero to this event. -/
@[expose] def pastedLineMismatch (u : Fin m → F) (t : F) (lineValue : β → F → F) :
    Set (Option (BoundedPolynomial F (m + 1) d) × β) :=
  {g | ∃ p, g.1 = some p ∧ eval (Fin.snoc u t) p.val ≠ lineValue g.2 t}

/-- Postprocessing the transcript by polynomial pasting and comparing at a vertical point
costs at most the sum of the mismatch probabilities on all sampled slices. The law can
correlate the transcript with the line answer arbitrarily. -/
theorem pastedLineMismatch_le [Fintype ι] (x : ι ↪ F) (u : Fin m → F) (t : F)
    (lineValue : β → F → F)
    (hline : ∀ b, ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = lineValue b t)
    (law : PMF ((ι → Option (BoundedPolynomial F m d)) × β)) :
    ((law.map (Prod.map (pasteOutcome x) id)).toOuterMeasure
      (pastedLineMismatch (d := d) u t lineValue)).toReal ≤
        ∑ i, (law.toOuterMeasure (sliceLineMismatch u x lineValue i)).toReal := by
  rw [PMF.toOuterMeasure_map_apply]
  refine (toOuterMeasure_toReal_mono law
    (t := ⋃ i ∈ (univ : Finset ι), sliceLineMismatch u x lineValue i) ?_).trans
    (toOuterMeasure_toReal_biUnion_finset_le law _ _)
  rintro ⟨g, b⟩ ⟨p, hp, hne⟩
  by_contra h
  obtain ⟨f, hf, heval⟩ := hline b
  have hagree (i : ι) (q : BoundedPolynomial F m d) (hq : g i = some q) :
      eval u q.val = f.eval (x i) := by
    rw [heval]
    by_contra hne'
    exact h (Set.mem_iUnion₂.mpr ⟨i, mem_univ i, q, hq, hne'⟩)
  apply hne
  rw [← eval_specializeLast, ← eval_evalPrefix, evalPrefix_eq_of_paste_agrees x u hp hf hagree]
  exact heval t

/-- The vertical-line comparison averaged over a uniform prefix, a tuple of distinct
slices and a uniform vertical coordinate. Each slice's mismatch can be estimated using
independent draws, at a total cost of one birthday bound. -/
theorem average_pastedLineMismatch_le [Fintype F] (k : ℕ) [Nonempty (Fin k ↪ F)]
    (lineValue : β → F → F)
    (hline : ∀ b, ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = lineValue b t)
    (law : (Fin m → F) → (Fin k → F) → PMF ((Fin k → Option (BoundedPolynomial F m d)) × β)) :
    letI : Fintype (Fin k ↪ F) := Fintype.ofFinite _
    (𝔼 u : Fin m → F, 𝔼 x : Fin k ↪ F, 𝔼 t : F,
      (((law u x).map (Prod.map (pasteOutcome x) id)).toOuterMeasure
        (pastedLineMismatch (d := d) u t lineValue)).toReal) ≤
    (k.choose 2 : ℝ) / Fintype.card F + ∑ i : Fin k, 𝔼 u : Fin m → F, 𝔼 x : Fin k → F,
      ((law u x).toOuterMeasure (sliceLineMismatch u x lineValue i)).toReal := by
  classical
  let _ : Fintype (Fin k ↪ F) := Fintype.ofFinite _
  let eventProb (u : Fin m → F) (x : Fin k ↪ F) (t : F) :=
    (((law u x).map (Prod.map (pasteOutcome x) id)).toOuterMeasure
      (pastedLineMismatch (d := d) u t lineValue)).toReal
  let sliceProb (u : Fin m → F) (x : Fin k → F) (i : Fin k) :=
    ((law u x).toOuterMeasure (sliceLineMismatch u x lineValue i)).toReal
  change (𝔼 u, 𝔼 x, 𝔼 t, eventProb u x t) ≤
    (k.choose 2 : ℝ) / Fintype.card F + ∑ i, 𝔼 u, 𝔼 x, sliceProb u x i
  let score (u : Fin m → F) (x : Fin k → F) := min 1 (∑ i, sliceProb u x i)
  calc
    _ ≤ 𝔼 u, 𝔼 x : Fin k ↪ F, score u x := by
      refine Finset.expect_le_expect fun u _ => Finset.expect_le_expect fun x _ => ?_
      refine Finset.expect_le univ_nonempty fun t _ => le_min ?_ ?_
      · exact toOuterMeasure_toReal_le_one _ _
      · exact pastedLineMismatch_le x u t lineValue hline (law u x)
    _ ≤ 𝔼 u, ((𝔼 x, score u x) + (k.choose 2 : ℝ) / Fintype.card F) := by
      refine Finset.expect_le_expect fun u _ => expect_embedding_le_expect_add k (score u) ?_ ?_
      · intro x
        exact le_min zero_le_one (sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
      · intro x
        exact min_le_left _ _
    _ ≤ 𝔼 u, ((𝔼 x, ∑ i, sliceProb u x i) + (k.choose 2 : ℝ) / Fintype.card F) := by
      exact Finset.expect_le_expect fun _ _ =>
        add_le_add_left (Finset.expect_le_expect fun _ _ => min_le_right _ _) _
    _ = _ := by
      rw [Finset.expect_add_distrib, Fintype.expect_const, add_comm]
      simp only [Finset.expect_sum_comm]

section Strategy

open Cslib.Quantum

variable {A : Type*} [Finite F] [Fintype β] [Ring A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Algebra ℂ A]

/-- The isolated experiment with one slice question and one vertical-line question. -/
@[expose] def sliceLineStrategy (φ : AlgState A)
    (M : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (B : (Fin m → F) → Measurement β A)
    (hComm : ∀ t u a b, Commute ((M t).effect a) ((B u).effect b)) :
    CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A where
  state := φ
  alice := M
  bob := B
  commute := hComm

/-- The joint experiment in which Alice measures the slices in sequence and Bob answers
a vertical-line question. Tuple repetitions are allowed here, so the same strategy
defines the laws for both distinct and independent tuples. -/
noncomputable def transcriptLineStrategy (k : ℕ) (φ : AlgState A)
    (M : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hM : ∀ t, (M t).IsProjective) (B : (Fin m → F) → Measurement β A)
    (hComm : ∀ t u a b, Commute ((M t).effect a) ((B u).effect b)) :
    CommutingStrategy (Fin k → F) (Fin m → F) (Fin k → Option (BoundedPolynomial F m d)) β A :=
  (sliceLineStrategy φ M B hComm).sequential k hM

variable [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [StarModule ℂ A] [SelfAdjointDecompose A]

/-- The probability of mismatch at the intersection of the isolated slice and line.
The failure outcome on Alice's side does not count as a mismatch. -/
noncomputable def isolatedSliceMismatch
    (S : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (lineValue : β → F → F) (u : Fin m → F) (t : F) : ℝ :=
  ((S.answers t u).toOuterMeasure
    {ab | ∃ q, ab.1 = some q ∧ eval u q.val ≠ lineValue ab.2 t}).toReal

private theorem exists_successful_ne {α γ : Type*} (f : α → γ) (a : Option α) (z : γ) :
    (∃ q, a = some q ∧ f q ≠ z) ↔ (∃ v, a.map f = some v ∧ v ≠ z) := by
  cases a <;> simp

omit [StarModule ℂ A] [SelfAdjointDecompose A] in
/-- The isolated slice event has exactly the successful mismatch weight of its
evaluated outcomes. -/
theorem isolatedSliceMismatch_eq_successfulMismatch [Fintype F] [DecidableEq F]
    (T : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (lineValue : β → F → F) (u : Fin m → F) (t : F) :
    isolatedSliceMismatch T lineValue u t =
      Measurement.successfulMismatch T.state (evaluatePolynomialMeasurement (T.alice t) u)
        ((T.bob u).map (fun b => lineValue b t)) := by
  rw [isolatedSliceMismatch, evaluatePolynomialMeasurement,
    CommutingStrategy.successfulMismatch_map_map_eq_event]
  congr 2
  ext ⟨a, b⟩
  exact exists_successful_ne (fun q : BoundedPolynomial F m d => eval u q.val) a (lineValue b t)

omit [StarModule ℂ A] [SelfAdjointDecompose A] in
/-- The transcript event computes the successful mismatch of the actual pasted measurement
at a fixed tuple of distinct slice locations. -/
theorem pastedLineMismatch_eq_successfulMismatch [Fintype F] [DecidableEq F] {k : ℕ}
    (T : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (hM : ∀ t, (T.alice t).IsProjective) (lineValue : β → F → F)
    (u : Fin m → F) (x : Fin k ↪ F) (t : F) :
    ((((T.sequential k hM).answers x u).map (Prod.map (pasteOutcome x) id)).toOuterMeasure
        (pastedLineMismatch (d := d) u t lineValue)).toReal =
      Measurement.successfulMismatch T.state
        (evaluatePolynomialMeasurement (pasteProjectiveSlices x T.alice hM) (Fin.snoc u t))
        ((T.bob u).map (fun b => lineValue b t)) := by
  classical
  rw [PMF.toOuterMeasure_map_apply, evaluatePolynomialMeasurement, pasteProjectiveSlices,
    pasteMeasurement]
  simp only [Measurement.map_map]
  have h := (T.sequential k hM).successfulMismatch_map_map_eq_event x u
    (Option.map (fun q => eval (Fin.snoc u t) q.val) ∘ pasteOutcome x) (fun b => lineValue b t)
  refine Eq.trans ?_ h.symm
  congr 2
  ext ⟨a, b⟩
  change (∃ p, pasteOutcome x a = some p ∧ eval (Fin.snoc u t) p.val ≠ lineValue b t) ↔
    (∃ z, Option.map (fun p => eval (Fin.snoc u t) p.val) (pasteOutcome x a) = some z ∧
      z ≠ lineValue b t)
  exact exists_successful_ne _ _ _

/-- The contribution of a selected transcript coordinate to vertical-line inconsistency
is at most its isolated mismatch probability plus the disturbance of its prefix. -/
theorem sequentialSliceLineMismatch_le
    (S : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (hM : ∀ t, (S.alice t).IsProjective) {k : ℕ} (i : Fin k) (x : Fin k → F) (u : Fin m → F)
    (lineValue : β → F → F) :
    (((S.sequential k hM).answers x u).toOuterMeasure (sliceLineMismatch u x lineValue i)).toReal ≤
      isolatedSliceMismatch S lineValue u (x i) +
        2 * √(Measurement.prefixCommutatorDefect S.state (fun j => S.alice (x j)) i) := by
  unfold isolatedSliceMismatch sliceLineMismatch
  exact S.sequential_event_le hM x i u (fun a b =>
    ∃ q, a = some q ∧ eval u q.val ≠ lineValue b (x i))

/-- The average sequential mismatch is controlled by the isolated mismatch and the
mean squared prefix commutator norm. -/
theorem average_sequentialSliceLineMismatch_le [Fintype F]
    (S : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (hM : ∀ t, (S.alice t).IsProjective) {k : ℕ} (i : Fin k) (lineValue : β → F → F) :
    (𝔼 u : Fin m → F, 𝔼 x : Fin k → F,
      (((S.sequential k hM).answers x u).toOuterMeasure (sliceLineMismatch u x lineValue i)).toReal)
      ≤ (𝔼 u : Fin m → F, 𝔼 t : F, isolatedSliceMismatch S lineValue u t) +
        2 * √(𝔼 x : Fin k → F, Measurement.prefixCommutatorDefect S.state
          (fun j => S.alice (x j)) i) := by
  unfold isolatedSliceMismatch sliceLineMismatch
  exact S.average_sequential_event_le hM i
    (fun t u a b => ∃ q, a = some q ∧ eval u q.val ≠ lineValue b t)

/-- The pasted vertical-line comparison in terms of the isolated slice error and
the commutator defects of the sequential measurements. The birthday term accounts
for the use of distinct slice locations in the pasted readout. -/
theorem average_sequential_pastedLineMismatch_le [Fintype F] (k : ℕ) [Nonempty (Fin k ↪ F)]
    (S : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (hM : ∀ t, (S.alice t).IsProjective) (lineValue : β → F → F)
    (hline : ∀ b, ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = lineValue b t) :
    letI : Fintype (Fin k ↪ F) := Fintype.ofFinite _
    (𝔼 u : Fin m → F, 𝔼 x : Fin k ↪ F, 𝔼 t : F,
      ((((S.sequential k hM).answers x u).map (Prod.map (pasteOutcome x) id)).toOuterMeasure
        (pastedLineMismatch (d := d) u t lineValue)).toReal) ≤
    (k.choose 2 : ℝ) / Fintype.card F +
      k * (𝔼 u : Fin m → F, 𝔼 t : F, isolatedSliceMismatch S lineValue u t) +
      ∑ i : Fin k, 2 * √(𝔼 x : Fin k → F, Measurement.prefixCommutatorDefect S.state
        (fun j => S.alice (x j)) i) := by
  refine (average_pastedLineMismatch_le k lineValue hline
    (fun u x => (S.sequential k hM).answers x u)).trans ?_
  rw [add_assoc]
  apply add_le_add_right
  refine (sum_le_sum fun i _ => average_sequentialSliceLineMismatch_le S hM i lineValue).trans_eq ?_
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Vertical-line mismatch for the pasted measurement in terms of the isolated mismatch,
pairwise commutators and strong self-consistency of the slice measurements. -/
theorem average_pastedLineMismatch_le_of_pairwise [Fintype F] (k : ℕ) [Nonempty (Fin k ↪ F)]
    (S : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (hM : ∀ t, (S.alice t).IsProjective)
    (R : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hR : ∀ t, (R t).IsProjective)
    (hc : ∀ x y a b, Commute ((S.alice x).effect a) ((R y).effect b))
    (lineValue : β → F → F)
    (hline : ∀ b, ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = lineValue b t)
    {χ ζ : ℝ}
    (hpair : (𝔼 x : F, 𝔼 y : F, Measurement.pairCommutatorDefect S.state (S.alice x) (S.alice y))
      ≤ χ)
    (hcopy : (𝔼 x : F, Measurement.copyDefect S.state (S.alice x) (R x)) ≤ ζ) :
    letI : Fintype (Fin k ↪ F) := Fintype.ofFinite _
    (𝔼 u : Fin m → F, 𝔼 x : Fin k ↪ F, 𝔼 t : F,
      ((((S.sequential k hM).answers x u).map (Prod.map (pasteOutcome x) id)).toOuterMeasure
        (pastedLineMismatch (d := d) u t lineValue)).toReal) ≤
    (k.choose 2 : ℝ) / Fintype.card F +
      k * (𝔼 u : Fin m → F, 𝔼 t : F, isolatedSliceMismatch S lineValue u t) +
      k * ((k - 1 : ℕ) : ℝ) * √(2 * χ + 8 * ζ) := by
  refine (average_sequential_pastedLineMismatch_le k S hM lineValue hline).trans ?_
  apply add_le_add_right
  exact Measurement.sum_prefixDisturbance_le_of_pairwise k S.state S.alice R hM hR hc hpair hcopy

end Strategy


section Completed

open Cslib.Quantum

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype β]

/-- Averaging the pasted measurement over distinct slice tuples averages its successful
vertical-line mismatch with the same sampling law. -/
theorem successfulMismatch_pasteSlices_eq_expect [Fintype F] [DecidableEq F] (k : ℕ)
    [Nonempty (Fin k ↪ F)]
    (T : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (hM : ∀ t, (T.alice t).IsProjective) (lineValue : β → F → F)
    (u : Fin m → F) (t : F) :
    letI : Fintype (Fin k ↪ F) := Fintype.ofFinite _
    Measurement.successfulMismatch T.state
      (evaluatePolynomialMeasurement (pasteSlices k T.alice hM) (Fin.snoc u t))
      ((T.bob u).map (fun b => lineValue b t)) =
        𝔼 x : Fin k ↪ F,
          ((((T.sequential k hM).answers x u).map (Prod.map (pasteOutcome x) id)).toOuterMeasure
            (pastedLineMismatch (d := d) u t lineValue)).toReal := by
  classical
  let _ : Fintype (Fin k ↪ F) := Fintype.ofFinite _
  simp only [pastedLineMismatch_eq_successfulMismatch, Fintype.expect_eq_sum_div_card,
    evaluatePolynomialMeasurement, pasteSlices, Measurement.map_mixture,
    Measurement.successfulMismatch_mixture_left, uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, inv_mul_eq_div, sum_div]

/-- The pasted vertical-line estimate needs commutator and copy bounds only on successful
slice outcomes. The failure outcome is controlled by projectivity and completion. -/
theorem average_pastedLineMismatch_le_of_successful [Fintype F] (k : ℕ)
    [Nonempty (Fin k ↪ F)]
    (S : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (hM : ∀ t, (S.alice t).IsProjective)
    (R : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hR : ∀ t, (R t).IsProjective)
    (hc : ∀ x y a b, Commute ((S.alice x).effect a) ((R y).effect b))
    (lineValue : β → F → F)
    (hline : ∀ b, ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = lineValue b t)
    {χ ζ : ℝ}
    (hpair : (𝔼 x : F, 𝔼 y : F, Measurement.successfulPairDefect S.state
      (S.alice x) (S.alice y)) ≤ χ)
    (hcopy : (𝔼 x : F, Measurement.successfulCopyDefect S.state (S.alice x) (R x)) ≤ ζ) :
    letI : Fintype (Fin k ↪ F) := Fintype.ofFinite _
    (𝔼 u : Fin m → F, 𝔼 x : Fin k ↪ F, 𝔼 t : F,
      ((((S.sequential k hM).answers x u).map (Prod.map (pasteOutcome x) id)).toOuterMeasure
        (pastedLineMismatch (d := d) u t lineValue)).toReal) ≤
    (k.choose 2 : ℝ) / Fintype.card F +
      k * (𝔼 u : Fin m → F, 𝔼 t : F, isolatedSliceMismatch S lineValue u t) +
      k * ((k - 1 : ℕ) : ℝ) * √(162 * χ + 176 * ζ) := by
  obtain ⟨hp, hs⟩ := Measurement.average_completedDefects_le S.state S.alice R hM hR hc hpair hcopy
  have h := average_pastedLineMismatch_le_of_pairwise k S hM R hR hc lineValue hline hp hs
  have he : 2 * (81 * χ + 80 * ζ) + 8 * (2 * ζ) = 162 * χ + 176 * ζ := by ring
  simpa only [he] using h

end Completed

end Cslib.PCP.LowIndividualDegree
