/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.Pasting
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
open scoped BigOperators

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

/-- The joint experiment in which Alice measures the slices in sequence and Bob answers
a vertical-line question. Tuple repetitions are allowed here, so the same strategy
defines the laws for both distinct and independent tuples. -/
noncomputable def transcriptLineStrategy (k : ℕ) (φ : AlgState A)
    (M : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hM : ∀ t, (M t).IsProjective) (B : (Fin m → F) → Measurement β A)
    (hComm : ∀ t u a b, Commute ((M t).effect a) ((B u).effect b)) :
    CommutingStrategy (Fin k → F) (Fin m → F) (Fin k → Option (BoundedPolynomial F m d)) β A where
  state := φ
  alice x := Measurement.sequentialProjective (fun j => M (x j)) (fun j => hM (x j))
  bob := B
  commute x u g b :=
    Measurement.sequentialProjective_commute _ _ _ (fun j a => hComm (x j) u a b) g

end Strategy

end Cslib.PCP.LowIndividualDegree
