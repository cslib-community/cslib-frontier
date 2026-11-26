/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PastingConsistency
public import CslibFrontier.Foundations.Quantum.Algebra.SequentialBinomial
import CslibFrontier.Foundations.Data.MvPolynomial.SchwartzZippel
import CslibFrontier.Foundations.Data.MvPolynomial.Shift
import CslibFrontier.Probability.IID.Distinct
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Union
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Local agreement of incompatible slice transcripts

An unsuccessful readout with enough successful slices has an interpolant
through any selected `d + 1` slices, and an additional successful slice that
differs from this interpolant. Agreement with a univariate line at a prefix
forces the difference polynomial to vanish there. This is the algebraic
step of [Ji, Natarajan, Vidick, Wright and Yuen, Lemma 12.20]
[JNVWY2020LowIndividualDegree].

## Main results

* `Cslib.PCP.LowIndividualDegree.card_locallyInterpolable_mul_card_le` bounds the number of
  prefixes on which an incompatible transcript can agree with a line.
* `Cslib.PCP.LowIndividualDegree.enoughSlices_prob_le_paste_prob_add` bounds the probability
  lost when discarding incompatible transcripts at distinct slice locations.
* `Cslib.PCP.LowIndividualDegree.average_enoughSlices_le` bounds the probability of
  obtaining too few successful slices for independent uniform draws.
* `Cslib.PCP.LowIndividualDegree.pastedSuccessfulEffect_lower_bound` applies both estimates
  to the success mass of the pasted measurement on distinct slices.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset MvPolynomial

variable {F ι : Type*} {m d : ℕ} [Field F] [Fintype ι]

/-- The successful slices agree at `u` with some univariate polynomial of degree at most `d`. -/
@[expose] def LocallyInterpolable (x : ι → F)
    (g : ι → Option (BoundedPolynomial F m d)) (u : Fin m → F) : Prop :=
  ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ i q, g i = some q → eval u q.val = f.eval (x i)

open scoped Classical in
/-- When global pasting fails despite enough successful outcomes, local interpolation
on a line is possible on at most an `m d / |F|` fraction of its prefixes, in counting form. -/
theorem card_locallyInterpolable_mul_card_le [Fintype F] (x : ι ↪ F)
    (g : ι → Option (BoundedPolynomial F m d)) (hcard : d < (successfulSlices g).card)
    (hfail : pasteOutcome x g = none) :
    #{u | LocallyInterpolable x g u} * Fintype.card F ≤
      (m * d) * (Fintype.card F) ^ m := by
  classical
  obtain ⟨s, hs, hsize⟩ := exists_subset_card_eq (Nat.succ_le_of_lt hcard)
  let selected (i : ι) := if i ∈ s then g i else none
  have hselected : successfulSlices selected = s := by
    ext i
    by_cases hi : i ∈ s
    · simpa [selected, hi] using hs hi
    · simp [selected, hi]
  obtain ⟨p, hp⟩ := pasteOutcome_eq_some_of_card x selected ((congrArg card hselected).trans hsize)
  have hfit : ¬ FitsSlices x g p := fun h => by
    simpa [hfail] using (pasteOutcome_eq_some_iff x g p).2 ⟨hcard, h⟩
  obtain ⟨i, q, hq, hne⟩ := not_forall.mp hfit |>.imp fun j hj =>
    not_forall.mp hj |>.imp fun q hq => not_imp.mp hq
  have hsubset :
      ({u | LocallyInterpolable x g u} : Finset (Fin m → F)) ⊆
          ({u | eval u (p.specialize (x i)).val = eval u q.val} : Finset (Fin m → F)) := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    obtain ⟨f, hf, hagree⟩ := hu
    have hline : evalPrefix u p.val = f :=
      evalPrefix_eq_of_paste_agrees x u hp hf fun j r hr => hagree j r <|
        if hj : j ∈ s then (ite_eq_left hj).symm.trans hr
        else nomatch (ite_eq_right hj).symm.trans hr
    rw [hagree i q hq, ← hline, eval_evalPrefix]
    rfl
  exact (Nat.mul_le_mul_right _ (card_le_card hsubset)).trans
    (card_filter_eval_eq_mul_card_le (fun h => hne (Subtype.ext h))
      (p.specialize (x i)).prop q.prop)

open Cslib.Probability.PMF
open scoped BigOperators

/-- The loss from discarding incompatible transcripts with enough successful slices is
bounded by the sum of the slice-line mismatches and the Schwartz–Zippel error. The
transcript marginal must be independent of the prefix queried on the other side. -/
theorem enoughSlices_prob_le_paste_prob_add_union [Fintype F] {β : Type*}
    (x : ι ↪ F) (lineValue : β → F → F)
    (hline : ∀ b, ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = lineValue b t)
    (law : (Fin m → F) → PMF ((ι → Option (BoundedPolynomial F m d)) × β))
    (p : PMF (ι → Option (BoundedPolynomial F m d)))
    (hmarg : ∀ u, (law u).map Prod.fst = p) :
    (p.toOuterMeasure {g | d < (successfulSlices g).card}).toReal ≤
      ((p.map (pasteOutcome x)).toOuterMeasure {q | q.isSome}).toReal +
      (𝔼 u, ((law u).toOuterMeasure
        (⋃ i ∈ (univ : Finset ι), sliceLineMismatch u x lineValue i)).toReal) +
      (m * d : ℝ) / Fintype.card F := by
  classical
  let bad : Set (ι → Option (BoundedPolynomial F m d)) :=
    {g | d < (successfulSlices g).card ∧ pasteOutcome x g = none}
  let survives (u : Fin m → F) : Set (ι → Option (BoundedPolynomial F m d)) :=
    {g | g ∈ bad ∧ LocallyInterpolable x g u}
  have hsplit :
      (p.toOuterMeasure {g | d < (successfulSlices g).card}).toReal =
        ((p.map (pasteOutcome x)).toOuterMeasure {q | q.isSome}).toReal +
        (p.toOuterMeasure bad).toReal := by
    rw [PMF.toOuterMeasure_map_apply]
    simp only [toOuterMeasure_apply_toReal, ← sum_add_distrib]
    refine sum_congr rfl fun g _ => ?_
    cases hp : pasteOutcome x g with
    | none => simp [hp, bad]
    | some q => simp [hp, bad, ((pasteOutcome_eq_some_iff x g q).mp hp).1]
  rw [hsplit, add_assoc]
  apply add_le_add_right
  have hsurv (u : Fin m → F) :
      (p.toOuterMeasure bad).toReal ≤
        ((law u).toOuterMeasure
          (⋃ i ∈ (univ : Finset ι), sliceLineMismatch u x lineValue i)).toReal +
        (p.toOuterMeasure (survives u)).toReal := by
    let misses := ⋃ i ∈ (univ : Finset ι), sliceLineMismatch (d := d) u x lineValue i
    have hloc : Prod.fst ⁻¹' bad ⊆ misses ∪ Prod.fst ⁻¹' survives u := by
      rintro ⟨g, b⟩ hg
      refine or_iff_not_imp_left.2 fun hmiss => ⟨hg, ?_⟩
      obtain ⟨f, hf, he⟩ := hline b
      refine ⟨f, hf, fun i q hq => (he _).symm ▸ not_not.1 fun hne => ?_⟩
      exact hmiss (Set.mem_iUnion₂.mpr ⟨i, mem_univ i, q, hq, hne⟩)
    have hpre (e : Set (ι → Option (BoundedPolynomial F m d))) :
        ((law u).toOuterMeasure (Prod.fst ⁻¹' e)).toReal = (p.toOuterMeasure e).toReal := by
      rw [← PMF.toOuterMeasure_map_apply, hmarg u]
    have h := (toOuterMeasure_toReal_mono (law u) hloc).trans
      (ENNReal.toReal_le_add (MeasureTheory.measure_union_le _ _)
        (toOuterMeasure_ne_top _ _) (toOuterMeasure_ne_top _ _))
    rwa [hpre, hpre] at h
  have hlocal : (𝔼 u, (p.toOuterMeasure (survives u)).toReal) ≤ (m * d : ℝ) / Fintype.card F := by
    simp_rw [toOuterMeasure_toReal_eq_sum_ite (p := p), Finset.expect_sum_comm,
      ← Finset.mul_expect]
    calc
      _ ≤ ∑ g, (p g).toReal * ((m * d : ℝ) / Fintype.card F) := by
        refine sum_le_sum fun g _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        by_cases hg : g ∈ bad
        · rw [Fintype.expect_eq_sum_div_card]
          have hc : (∑ u : Fin m → F, if g ∈ survives u then (1 : ℝ) else 0) =
              (#{u | LocallyInterpolable x g u} : ℝ) := by
            simp [survives, hg]
          have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
          rw [hc, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
            div_le_div_iff₀ (pow_pos hF m) hF]
          exact_mod_cast card_locallyInterpolable_mul_card_le x g hg.1 hg.2
        · have hnonneg : 0 ≤ (m * d : ℝ) / Fintype.card F := by positivity
          simpa [survives, hg] using hnonneg
      _ = _ := by rw [← sum_mul, sum_toReal, one_mul]
  calc
    _ = 𝔼 _u : Fin m → F, (p.toOuterMeasure bad).toReal := (Fintype.expect_const _).symm
    _ ≤ _ := (expect_le_expect fun u _ => hsurv u).trans (by
      rw [expect_add_distrib]
      exact add_le_add_right hlocal _)

/-- The loss from discarding incompatible transcripts, estimated by the sum of
the individual slice-line mismatch probabilities. -/
theorem enoughSlices_prob_le_paste_prob_add [Fintype F] {β : Type*}
    (x : ι ↪ F) (lineValue : β → F → F)
    (hline : ∀ b, ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = lineValue b t)
    (law : (Fin m → F) → PMF ((ι → Option (BoundedPolynomial F m d)) × β))
    (p : PMF (ι → Option (BoundedPolynomial F m d)))
    (hmarg : ∀ u, (law u).map Prod.fst = p) :
    (p.toOuterMeasure {g | d < (successfulSlices g).card}).toReal ≤
      ((p.map (pasteOutcome x)).toOuterMeasure {q | q.isSome}).toReal +
      (∑ i, 𝔼 u, ((law u).toOuterMeasure (sliceLineMismatch u x lineValue i)).toReal) +
      (m * d : ℝ) / Fintype.card F := by
  refine (enoughSlices_prob_le_paste_prob_add_union x lineValue hline law p hmarg).trans ?_
  gcongr
  rw [← expect_sum_comm]
  exact expect_le_expect fun u _ => toOuterMeasure_toReal_biUnion_finset_le (law u) _ _

section Sequential

open Cslib.Quantum
open scoped Real

private theorem transcriptSuccessCount_eq_card {k : ℕ}
    (g : Fin k → Option (BoundedPolynomial F m d)) :
    Measurement.transcriptSuccessCount Option.isSome g = (successfulSlices g).card := by
  rw [Measurement.transcriptSuccessCount, ← card_filter]
  exact congrArg card (Finset.ext fun _ => by simp)

variable {A : Type*} [Fintype F] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A lower bound for the average probability of enough successful slice outcomes under
independent uniform sampling. This combines the sequential comparison of Lemma 12.21
with the concentration estimate of Lemma 12.22. -/
theorem average_enoughSlices_le (φ : AlgState A)
    (M R : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hM : ∀ x, (M x).IsProjective) (hR : ∀ x, (R x).IsProjective)
    (hc : ∀ x y a b, Commute ((M x).effect a) ((R y).effect b))
    {k : ℕ} (hk : 0 < k) {θ κ χ ζ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hsize : 2 * (d : ℝ) ≤ θ * k)
    (hmass : 1 - κ ≤ (φ (Measurement.averageSuccessEffect R Option.isSome)).re)
    (hpair : (𝔼 x : F, 𝔼 y : F, Measurement.successfulPairDefect φ (M x) (M y)) ≤ χ)
    (hcopy : (𝔼 x : F, Measurement.successfulCopyDefect φ (M x) (R x)) ≤ ζ) :
    1 - κ / (1 - θ) - Real.exp (-(θ ^ 2 * k) / 2) -
        (1 + √2) * (k * √(2 * ζ) + (k : ℝ) ^ 2 * √(162 * χ + 176 * ζ)) ≤
      𝔼 x : Fin k → F, ∑ g with d < (successfulSlices g).card,
        (φ ((Measurement.sequentialProjective (fun j => M (x j)) (fun j => hM (x j))).effect
          g)).re := by
  obtain ⟨hp, hs⟩ := Measurement.average_completedDefects_le φ M R hM hR hc hpair hcopy
  have h := Measurement.abs_sequentialSuccess_sub_binomialAtLeast_le φ M R hM hR hc
    Option.isSome k (d + 1) hp hs
  have he : 2 * (81 * χ + 80 * ζ) + 8 * (2 * ζ) = 162 * χ + 176 * ζ := by ring
  simp only [transcriptSuccessCount_eq_card, Nat.succ_le_iff, binomialAtLeast, Nat.succ_ne_zero,
    ite_false, Nat.add_sub_cancel, he] at h
  obtain ⟨hG₀, hG₁⟩ := Measurement.averageSuccessEffect_mem_Icc R Option.isSome
  have ht := φ.one_sub_le_re_binomialTail hk hθ₀ hθ₁ hsize hG₀ hG₁ hmass
  linarith [(abs_sub_le_iff.mp h).2]

omit [Fintype F] in
private theorem pasteSlices_success_prob_eq_expect [Finite F] (k : ℕ) [Nonempty (Fin k ↪ F)]
    (φ : AlgState A) (M : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hM : ∀ t, (M t).IsProjective) :
    letI : Fintype (Fin k ↪ F) := Fintype.ofFinite _
    (φ (pasteSlices k M hM).successfulEffect).re =
      𝔼 x : Fin k ↪ F, (((pasteProjectiveSlices x M hM).distribution φ).toOuterMeasure
        {q | q.isSome}).toReal := by
  let _ : Fintype (Fin k ↪ F) := Fintype.ofFinite _
  have h (N : Measurement (Option (BoundedPolynomial F (m + 1) d)) A) :
      (φ N.successfulEffect).re = 1 - (φ (N.effect none)).re := by
    rw [N.effect_none_eq_one_sub_successfulEffect, map_sub, Complex.sub_re, φ.map_one,
      Complex.one_re, sub_sub_cancel]
  simp only [← Measurement.successfulEffect_eq_success_prob, h, expect_sub_distrib,
    Fintype.expect_const]
  rw [pasteSlices_effect]
  simp only [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← smul_sum,
    φ.re_apply_uniformAverage]

private theorem enoughSlices_successfulEffect_le {β : Type*} [Fintype β]
    (k : ℕ) [Nonempty (Fin k ↪ F)]
    (S : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (hM : ∀ t, (S.alice t).IsProjective)
    (R : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hR : ∀ t, (R t).IsProjective)
    (hc : ∀ x y a b, Commute ((S.alice x).effect a) ((R y).effect b))
    (lineValue : β → F → F)
    (hline : ∀ b, ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = lineValue b t)
    {χ ζ η : ℝ}
    (hpair : (𝔼 x : F, 𝔼 y : F, Measurement.pairCommutatorDefect S.state (S.alice x) (S.alice y))
      ≤ χ)
    (hcopy : (𝔼 x : F, Measurement.copyDefect S.state (S.alice x) (R x)) ≤ ζ)
    (hlocal : (𝔼 u : Fin m → F, 𝔼 t : F, isolatedSliceMismatch S lineValue u t) ≤ η) :
    (𝔼 x : Fin k → F, ∑ g with d < (successfulSlices g).card,
        (S.state ((Measurement.sequentialProjective (fun j => S.alice (x j))
          (fun j => hM (x j))).effect g)).re) ≤
      (S.state (pasteSlices k S.alice hM).successfulEffect).re +
        2 * (k.choose 2 : ℝ) / Fintype.card F +
        (m * d : ℝ) / Fintype.card F + k * η +
        k * ((k - 1 : ℕ) : ℝ) * √(2 * χ + 8 * ζ) := by
  classical
  let _ : Fintype (Fin k ↪ F) := Fintype.ofFinite _
  let T := S.sequential k hM
  let score (x : Fin k → F) :=
    (((T.alice x).distribution S.state).toOuterMeasure {g | d < (successfulSlices g).card}).toReal
  let misses (u : Fin m → F) (x : Fin k → F) :=
    ((T.answers x u).toOuterMeasure
      (⋃ i ∈ (univ : Finset (Fin k)), sliceLineMismatch u x lineValue i)).toReal
  have hscore (x : Fin k → F) : score x = ∑ g with d < (successfulSlices g).card,
      (S.state ((Measurement.sequentialProjective (fun j => S.alice (x j))
        (fun j => hM (x j))).effect g)).re := by
    simp only [score, toOuterMeasure_apply_toReal, sum_filter, Set.mem_ofPred_eq,
      Measurement.distribution_apply, ENNReal.toReal_ofReal ((T.alice x).prob_nonneg S.state _)]
    simp only [Measurement.prob, T, CommutingStrategy.sequential]
  have htuple (x : Fin k ↪ F) : score x ≤
      (((pasteProjectiveSlices x S.alice hM).distribution S.state).toOuterMeasure
        {q | q.isSome}).toReal + (𝔼 u, misses u x) + (m * d : ℝ) / Fintype.card F := by
    have h := enoughSlices_prob_le_paste_prob_add_union x lineValue hline (T.answers x)
      ((T.alice x).distribution S.state) (T.answers_map_fst x)
    rwa [← Measurement.distribution_map] at h
  have hswap : (𝔼 x : Fin k ↪ F, 𝔼 u, misses u x) ≤
      (𝔼 u, 𝔼 x : Fin k → F, misses u x) + (k.choose 2 : ℝ) / Fintype.card F := by
    rw [expect_comm univ univ]
    calc
      _ ≤ 𝔼 u, ((𝔼 x : Fin k → F, misses u x) + (k.choose 2 : ℝ) / Fintype.card F) := by
        refine expect_le_expect fun u _ => ?_
        exact expect_embedding_le_expect_add k (misses u) (fun _ => ENNReal.toReal_nonneg)
          (fun x => toOuterMeasure_toReal_le_one (T.answers x u) _)
      _ = _ := by simp only [expect_add_distrib, Fintype.expect_const]
  have hmiss : (𝔼 u, 𝔼 x : Fin k → F, misses u x) ≤
      k * η + k * ((k - 1 : ℕ) : ℝ) * √(2 * χ + 8 * ζ) := by
    calc
      _ ≤ ∑ i : Fin k, 𝔼 u, 𝔼 x : Fin k → F,
          ((T.answers x u).toOuterMeasure (sliceLineMismatch u x lineValue i)).toReal := by
        simp only [← expect_sum_comm]
        exact expect_le_expect fun u _ => expect_le_expect fun x _ =>
          toOuterMeasure_toReal_biUnion_finset_le (T.answers x u) _ _
      _ ≤ _ := by
        have h := sum_le_sum fun (i : Fin k) (_ : i ∈ univ) =>
          average_sequentialSliceLineMismatch_le S hM i lineValue
        simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
        exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hlocal (by positivity))
          (Measurement.sum_prefixDisturbance_le_of_pairwise k S.state S.alice R hM hR hc
            hpair hcopy))
  have hscore' := expect_le_expect_embedding_add k score
    (fun x => ENNReal.toReal_nonneg) (fun x => toOuterMeasure_toReal_le_one _ _)
  have hpaste := expect_le_expect (s := (univ : Finset (Fin k ↪ F))) fun x _ =>
    htuple x
  simp only [expect_add_distrib, Fintype.expect_const,
    ← pasteSlices_success_prob_eq_expect] at hpaste
  simp only [← hscore, mul_div_assoc (2 : ℝ)]
  linarith

/-- The mass of successful outcomes in the actual pasted measurement. The bound
combines concentration, the birthday comparison in each direction, and the loss
from transcripts whose successful slices admit no global interpolant. -/
theorem pastedSuccessfulEffect_lower_bound {β : Type*} [Fintype β]
    (k : ℕ) [Nonempty (Fin k ↪ F)] (hk : 0 < k)
    (S : CommutingStrategy F (Fin m → F) (Option (BoundedPolynomial F m d)) β A)
    (hM : ∀ t, (S.alice t).IsProjective)
    (R : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hR : ∀ t, (R t).IsProjective)
    (hc : ∀ x y a b, Commute ((S.alice x).effect a) ((R y).effect b))
    (lineValue : β → F → F)
    (hline : ∀ b, ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = lineValue b t)
    {θ κ χ ζ η : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hsize : 2 * (d : ℝ) ≤ θ * k)
    (hmass : 1 - κ ≤ (S.state (Measurement.averageSuccessEffect R Option.isSome)).re)
    (hpair : (𝔼 x : F, 𝔼 y : F, Measurement.successfulPairDefect S.state (S.alice x) (S.alice y))
      ≤ χ)
    (hcopy : (𝔼 x : F, Measurement.successfulCopyDefect S.state (S.alice x) (R x)) ≤ ζ)
    (hlocal : (𝔼 u : Fin m → F, 𝔼 t : F, isolatedSliceMismatch S lineValue u t) ≤ η) :
    1 - κ / (1 - θ) - Real.exp (-(θ ^ 2 * k) / 2) -
        (1 + √2) * (k * √(2 * ζ) + (k : ℝ) ^ 2 * √(162 * χ + 176 * ζ)) -
        (2 * (k.choose 2 : ℝ) / Fintype.card F + (m * d : ℝ) / Fintype.card F +
          k * η + k * ((k - 1 : ℕ) : ℝ) * √(162 * χ + 176 * ζ)) ≤
      (S.state (pasteSlices k S.alice hM).successfulEffect).re := by
  have h₁ := average_enoughSlices_le S.state S.alice R hM hR hc hk hθ₀ hθ₁ hsize
    hmass hpair hcopy
  obtain ⟨hp, hs⟩ := Measurement.average_completedDefects_le S.state S.alice R hM hR hc hpair hcopy
  have h₂ := enoughSlices_successfulEffect_le k S hM R hR hc lineValue hline hp hs hlocal
  rw [show (2 : ℝ) * (81 * χ + 80 * ζ) + 8 * (2 * ζ) = 162 * χ + 176 * ζ by ring] at h₂
  linarith

end Sequential

end Cslib.PCP.LowIndividualDegree
