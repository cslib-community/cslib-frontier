/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Bipartite
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.ThreeLeafTree
import CslibFrontier.GameTheory.SocialChoice.SinglePeaked.Ching
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Single-peaked social choice, phantom-voter medians, and 3-leaf facility location: checked clients

Non-vacuous checked instances and boundary/separation witnesses for:

1. **Ordinal single-peaked preferences** (`SinglePeaked/Basic.lean`): distinct asymmetric vs.
   symmetric preferences at the same peak `1/2`, uniqueness of extreme preferences at `0` and `1`,
   and equivalence with the convex-combination definition ([SchummerVohra2007], §10.2, p. 245).
2. **Lemma 10.1, Exercise 10.1, and necessity of strategy-proofness**: a 2-agent unanimous onto
   rule that fails Pareto-optimality and strategy-proofness, a constant rule that is strongly group
   strategy-proof yet not surjective (on both ordinal and symmetric domains, exercising
   `symmetric_surjective_iff_paretoOptimal`), and a positive check on the 3-agent median.
3. **Exercise 10.3 & Ching's peaks-only theorem**: an explicit single-agent option set
   `[1/4, 3/4]` strictly inside `[0, 1]`, and peaks-only invariance across asymmetric reports.
4. **Theorems 10.2 & 10.4, Definition 10.3 duality, and Exercise 10.2**: explicit evaluations of
   the 3-agent phantom median `![1/4, 3/4]` matching `MoulinScheme.ofPhantoms` and `maxMinEval`;
   2-agent dictatorship separating Theorem 10.4 (non-anonymous GMVS) from Theorem 10.2 (anonymous
   phantom medians).
5. **Individual rationality uniqueness** (§10.2.2, p. 252): `minPeakScheme` is individually
   rational with respect to `0`, whereas `phantomMedian ![1/2, 1/2]` fails IR at `0`.
6. **Symmetric path-distance 3-leaf facility location (`ThreeLeafTree`, after Exercise 10.5)**:
   a concrete `Tripod` on the unit 3-star `star3`, checking both branches of
   `ThreeLeafScheme.dichotomy` (Family I single-leg two-phantom rule and Family II three-leg-cap
   rule `high = ![1/2, 1/2, 1/2]`) and both directions of
   `isStrategyProof_surjective_anonymous_iff_threeLeafScheme`.
-/

set_option linter.privateModule false
namespace CslibFrontierTests.GameTheory.SinglePeaked

open Cslib.GameTheory Cslib.GameTheory.SocialChoice Cslib.GameTheory.SocialChoice.SinglePeaked
open Cslib.GameTheory.FacilityLocation SimpleGraph SimpleGraph.MetricGraph

noncomputable local instance {V : Type*} (W : WeightedGraph V) [Finite V] :
    MeasurableSpace (MetricGraph W) := borel _

local instance {V : Type*} (W : WeightedGraph V) [Finite V] :
    BorelSpace (MetricGraph W) := ⟨rfl⟩

noncomputable local instance : MeasurableSpace (Set.Icc (0 : ℝ) 1) := borel _
local instance : BorelSpace (Set.Icc (0 : ℝ) 1) := ⟨rfl⟩

private def pt0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num, by norm_num⟩
private noncomputable def pt14 : Set.Icc (0 : ℝ) 1 := ⟨1 / 4, by norm_num, by norm_num⟩
private noncomputable def pt12 : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
private noncomputable def pt34 : Set.Icc (0 : ℝ) 1 := ⟨3 / 4, by norm_num, by norm_num⟩
private def pt1 : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num, by norm_num⟩

/-! ### 1. Ordinal single-peaked domain vs. symmetric preferences -/

/-- `preferLeft (1/2)` and `symmetric (1/2)` share peak `1/2` yet are distinct preferences:
`preferLeft (1/2)` strictly prefers `0` over `3/4`, whereas `symmetric (1/2)` strictly prefers
`3/4` over `0`. -/
example :
    (Preference.preferLeft pt12).peak = (Preference.symmetric pt12).peak ∧
    (Preference.preferLeft pt12).Prefers pt0 pt34 ∧
    (Preference.symmetric pt12).Prefers pt34 pt0 ∧
    Preference.preferLeft pt12 ≠ Preference.symmetric pt12 := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · exact Preference.preferLeft_prefers_of_le_of_gt (by norm_num [pt0, pt12])
      (by norm_num [pt12, pt34])
  · rw [Preference.symmetric_prefers_iff]
    norm_num [pt0, pt12, pt34]
  · intro h
    have h1 : (Preference.preferLeft pt12).Prefers pt0 pt34 :=
      Preference.preferLeft_prefers_of_le_of_gt (by norm_num [pt0, pt12])
        (by norm_num [pt12, pt34])
    rw [h, Preference.symmetric_prefers_iff] at h1
    norm_num [pt0, pt12, pt34] at h1

/-- Uniqueness of extreme single-peaked preferences at `0` and `1` ([SchummerVohra2007], p. 247). -/
example :
    Preference.symmetric pt0 = Preference.leftExtreme (show (0 : ℝ) ≤ 1 by norm_num) ∧
    Preference.preferRight pt1 = Preference.rightExtreme (show (0 : ℝ) ≤ 1 by norm_num) :=
  ⟨Preference.eq_leftExtreme_of_peak_eq (by simp [pt0]),
    Preference.eq_rightExtreme_of_peak_eq (by simp [pt1])⟩

/-- Positive and negative checks on `Preference.isSinglePeaked_iff_convex` ([SchummerVohra2007],
§10.2, p. 245): `preferLeft (1/2)` satisfies the convex-combination condition with peak `1/2`,
and fails it with candidate peak `0`. -/
example :
    (∀ (x : Set.Icc (0 : ℝ) 1), x ≠ pt12 → ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1),
      (Preference.preferLeft pt12).ranking.Prefers
        ⟨t * x + (1 - t) * pt12,
          ⟨by nlinarith [x.2.1, pt12.2.1], by nlinarith [x.2.2, pt12.2.2]⟩⟩ x) ∧
    ¬ (∀ (x : Set.Icc (0 : ℝ) 1), x ≠ pt0 → ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1),
      (Preference.preferLeft pt12).ranking.Prefers
        ⟨t * x + (1 - t) * pt0,
          ⟨by nlinarith [x.2.1, pt0.2.1], by nlinarith [x.2.2, pt0.2.2]⟩⟩ x) := by
  have hpos := (Preference.isSinglePeaked_iff_convex (Preference.preferLeft pt12).ranking
    (Preference.preferLeft pt12).peak).mp
      ⟨@(Preference.preferLeft pt12).prefers_of_between_right,
        @(Preference.preferLeft pt12).prefers_of_between_left⟩
  rw [Preference.preferLeft_peak] at hpos
  refine ⟨hpos, fun hconv => ?_⟩
  obtain ⟨hR, _⟩ :=
    (Preference.isSinglePeaked_iff_convex (Preference.preferLeft pt12).ranking pt0).mpr hconv
  have hbad : (Preference.preferLeft pt12).ranking.Prefers pt0 pt12 :=
    hR (le_rfl : (pt0 : ℝ) ≤ pt0) (show (pt0 : ℝ) < pt12 by norm_num [pt0, pt12])
  have hgood : (Preference.preferLeft pt12).ranking.Prefers pt12 pt0 :=
    (Preference.preferLeft pt12).prefers_of_between_left (by norm_num [pt0, pt12])
      (by rw [Preference.preferLeft_peak])
  exact (Preference.preferLeft pt12).ranking.prefers_asymm hbad hgood

/-! ### 2. Lemma 10.1: positive check and necessity of strategy-proofness -/

/-- A 2-agent unanimous onto rule that drops to `0` whenever the two peaks disagree: it is
unanimous and surjective, yet neither Pareto-optimal nor strategy-proof (showing strategy-proofness
is essential in Lemma 10.1). -/
example :
    let f : Rule (Fin 2) 0 1 := fun P =>
      by classical exact if (P 0).peak = (P 1).peak then (P 0).peak else pt0
    f.IsUnanimous ∧ Function.Surjective f ∧ ¬ f.IsParetoOptimal ∧ ¬ f.IsStrategyProof := by
  classical
  intro f
  have hU : f.IsUnanimous := by
    intro P x hpeaks
    change (if (P 0).peak = (P 1).peak then (P 0).peak else pt0) = x
    rw [hpeaks 0, hpeaks 1, ite_eq_left rfl]
  have hSurj : Function.Surjective f := hU.surjective
  have hNotPO : ¬ f.IsParetoOptimal := by
    intro hPO
    let P : Profile (Fin 2) 0 1 := ![Preference.symmetric pt12, Preference.symmetric pt34]
    have hneq : (P 0).peak ≠ (P 1).peak := by
      intro heq
      have hval : (1 / 2 : ℝ) = 3 / 4 := by
        simpa [P, pt12, pt34] using congrArg Subtype.val heq
      norm_num at hval
    have hfP : f P = pt0 := by
      change (if (P 0).peak = (P 1).peak then (P 0).peak else pt0) = pt0
      rw [ite_eq_right hneq]
    refine hPO P pt12 fun i => ?_
    rw [hfP]
    fin_cases i
    · change (Preference.symmetric pt12).Prefers pt12 pt0
      rw [Preference.symmetric_prefers_iff]
      norm_num [pt0, pt12]
    · change (Preference.symmetric pt34).Prefers pt12 pt0
      rw [Preference.symmetric_prefers_iff]
      norm_num [pt0, pt12, pt34]
  have hNotSP : ¬ f.IsStrategyProof := fun hSP =>
    hNotPO ((hSP.surjective_iff_isParetoOptimal).mp hSurj)
  exact ⟨hU, hSurj, hNotPO, hNotSP⟩

/-- A constant rule is strongly group strategy-proof yet not surjective, unanimous, or
Pareto-optimal. -/
example :
    let f : Rule (Fin 2) 0 1 := fun _ => pt12
    f.IsGroupStrategyProof ∧ ¬ Function.Surjective f ∧ ¬ f.IsUnanimous ∧ ¬ f.IsParetoOptimal := by
  intro f
  have hGSP : f.IsGroupStrategyProof := by
    rintro P Q A _ ⟨_, i, _, hlt⟩
    exact (P i).prefers_irrefl pt12 hlt
  have hNotSurj : ¬ Function.Surjective f := by
    intro hs
    obtain ⟨P, hP⟩ := hs pt0
    have hval : (1 / 2 : ℝ) = 0 := congrArg Subtype.val hP
    norm_num at hval
  have hNotU : ¬ f.IsUnanimous := fun hU => hNotSurj hU.surjective
  have hNotPO : ¬ f.IsParetoOptimal := fun hPO => hNotU hPO.isUnanimous
  exact ⟨hGSP, hNotSurj, hNotU, hNotPO⟩

/-! ### 3. Phantom medians (Theorem 10.2, Exercise 10.2, Exercise 10.3, Definition 10.3 duality) -/

private noncomputable def phantoms3 : Fin (Fintype.card (Fin 3) - 1) → Set.Icc (0 : ℝ) 1 :=
  ![pt14, pt34]

private theorem phantoms3_mono : Monotone phantoms3 := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · change (1 / 4 : ℝ) ≤ 3 / 4; norm_num
  · exact absurd hij (by decide)
  · exact le_rfl

/-- Exercise 10.1 (`symmetric_surjective_iff_paretoOptimal` and
`symmetric_surjective_iff_unanimous`): on symmetric Euclidean preferences over `[0, 1]`, the
surjective strategy-proof `phantomMedian ![1/4, 3/4]` is Pareto-optimal and unanimous, whereas the
constant strategy-proof rule at `1/2` is neither surjective nor Pareto-optimal. -/
example :
    (∀ (x : Fin 3 → Set.Icc (0 : ℝ) 1) (y : Set.Icc (0 : ℝ) 1),
      ¬ ∀ i, Dist.dist (x i) y < Dist.dist (x i) (phantomMedian phantoms3 x)) ∧
    (∀ y : Set.Icc (0 : ℝ) 1, phantomMedian (ι := Fin 3) phantoms3 (fun _ => y) = y) ∧
    ¬ (∀ (x : Fin 2 → Set.Icc (0 : ℝ) 1) (y : Set.Icc (0 : ℝ) 1),
      ¬ ∀ i, Dist.dist (x i) y < Dist.dist (x i) ((fun _ => pt12) x)) := by
  have hSP_pm : (Mechanism.deterministic (phantomMedian (ι := Fin 3) phantoms3)).IsStrategyProof :=
    (phantomMedian_isGroupStrategyProof (by norm_num) phantoms3).isStrategyProof
  have hSurj_pm : Function.Surjective (phantomMedian (ι := Fin 3) phantoms3) :=
    phantomMedian_surjective (by norm_num) phantoms3
  have hSP_const :
      (Mechanism.deterministic (fun _ : Fin 2 → Set.Icc (0 : ℝ) 1 => pt12)).IsStrategyProof :=
    (Mechanism.isStrategyProof_deterministic_iff _).mpr fun _ _ _ => le_rfl
  have hNotSurj_const : ¬ Function.Surjective (fun _ : Fin 2 → Set.Icc (0 : ℝ) 1 => pt12) := by
    intro hs
    obtain ⟨x, hx⟩ := hs pt0
    have hval : (1 / 2 : ℝ) = 0 := congrArg Subtype.val hx
    norm_num at hval
  exact ⟨(symmetric_surjective_iff_paretoOptimal (by norm_num) hSP_pm).mp hSurj_pm,
    (symmetric_surjective_iff_unanimous (by norm_num) hSP_pm).mp hSurj_pm,
    fun hPO => hNotSurj_const
      ((symmetric_surjective_iff_paretoOptimal (by norm_num) hSP_const).mpr hPO)⟩

private noncomputable def scheme3 : MoulinScheme (Fin 3) 0 1 :=
  MoulinScheme.ofPhantoms (by norm_num) phantoms3 phantoms3_mono

/-- Non-vacuous check of Theorems 10.2 and 10.4, Exercise 10.2 (`ofPhantoms`), and Definition 10.3
duality (`eval_eq_maxMinEval`) on 3 agents with phantoms `(1/4, 3/4)`. -/
example :
    let f : Rule (Fin 3) 0 1 := ofPhantomMedian phantoms3
    f.IsGroupStrategyProof ∧ f.IsStrategyProof ∧ Function.Surjective f ∧ f.IsAnonymous ∧
    f.IsParetoOptimal ∧ f.IsPeaksOnly ∧
    (∀ x, (scheme3.eval x : ℝ) = maxMinEval scheme3 x) ∧
    (∀ x, scheme3.eval x = phantomMedian phantoms3 x) := by
  intro f
  have hf_eq : f = ofMoulinScheme scheme3 := funext fun P => by
    dsimp only [f]
    rw [ofPhantomMedian_apply, ofMoulinScheme_apply]
    exact (MoulinScheme.ofPhantoms_eval_eq_phantomMedian (by norm_num) phantoms3 phantoms3_mono
      (fun i => (P i).peak)).symm
  have hGSP : f.IsGroupStrategyProof := hf_eq ▸ ofMoulinScheme_isGroupStrategyProof scheme3
  have hSP : f.IsStrategyProof := hGSP.isStrategyProof
  have hSurj : Function.Surjective f := hf_eq ▸ ofMoulinScheme_surjective scheme3
  have hAnon : f.IsAnonymous := fun σ P => by
    dsimp only [f]
    rw [ofPhantomMedian_apply, ofPhantomMedian_apply]
    exact phantomMedian_isAnonymous phantoms3 σ (fun i => (P i).peak)
  have hPO : f.IsParetoOptimal := (hSP.surjective_iff_isParetoOptimal).mp hSurj
  have hPeaks : f.IsPeaksOnly := hSP.isPeaksOnly_of_surjective hSurj
  exact ⟨hGSP, hSP, hSurj, hAnon, hPO, hPeaks, eval_eq_maxMinEval scheme3,
    MoulinScheme.ofPhantoms_eval_eq_phantomMedian (by norm_num) phantoms3 phantoms3_mono⟩

/-- Concrete evaluation of `phantomMedian ![1/4, 3/4]` at `![0, 0, 1]` yields `1/4`, and at
`![0, 1/2, 1]` yields `1/2`; furthermore, fixing agents `1` and `2` at `0` and `1`, agent `0`'s
option set (Exercise 10.3) is the closed interval `[1/4, 3/4]`. -/
example :
    phantomMedian (ι := Fin 3) phantoms3 ![pt0, pt0, pt1] = pt14 ∧
    phantomMedian (ι := Fin 3) phantoms3 ![pt0, pt12, pt1] = pt12 ∧
    (ofPhantomMedian (ι := Fin 3) phantoms3).optionSet
      ![Preference.symmetric pt12, Preference.leftExtreme (by norm_num),
        Preference.rightExtreme (by norm_num)] 0 = Set.Icc pt14 pt34 := by
  have hα2 : scheme3.alpha ({0, 1} : Finset (Fin 3)) = 1 / 4 := by
    rw [scheme3, MoulinScheme.ofPhantoms_alpha (by norm_num) phantoms3 phantoms3_mono
      (by decide) (by decide)]
    rfl
  have hα1_0 : scheme3.alpha ({0} : Finset (Fin 3)) = 3 / 4 := by
    rw [scheme3, MoulinScheme.ofPhantoms_alpha (by norm_num) phantoms3 phantoms3_mono
      (by decide) (by decide)]
    rfl
  have hα1_1 : scheme3.alpha ({1} : Finset (Fin 3)) = 3 / 4 := by
    rw [scheme3, MoulinScheme.ofPhantoms_alpha (by norm_num) phantoms3 phantoms3_mono
      (by decide) (by decide)]
    rfl
  have h1 : scheme3.eval ![pt0, pt0, pt1] = pt14 := by
    ext
    refine le_antisymm ?_ ?_
    · rw [← not_lt, scheme3.lt_eval_iff]
      have hS : (Finset.univ.filter fun i : Fin 3 =>
          ((![pt0, pt0, pt1] i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ pt14) = {0, 1} := by
        ext i; fin_cases i <;> simp [pt0, pt1, pt14]; norm_num
      rw [hS, hα2]; norm_num [pt14]
    · rw [← not_lt, scheme3.eval_lt_iff]
      have hS : (Finset.univ.filter fun i : Fin 3 =>
          ((![pt0, pt0, pt1] i : Set.Icc (0 : ℝ) 1) : ℝ) < pt14) = {0, 1} := by
        ext i; fin_cases i <;> simp [pt0, pt1, pt14]; norm_num
      rw [hS, hα2]; norm_num [pt14]
  have h2 : scheme3.eval ![pt0, pt12, pt1] = pt12 := by
    ext
    refine le_antisymm ?_ ?_
    · rw [← not_lt, scheme3.lt_eval_iff]
      have hS : (Finset.univ.filter fun i : Fin 3 =>
          ((![pt0, pt12, pt1] i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ pt12) = {0, 1} := by
        ext i; fin_cases i <;> simp [pt0, pt12, pt1]; norm_num
      rw [hS, hα2]; norm_num [pt12]
    · rw [← not_lt, scheme3.eval_lt_iff]
      have hS : (Finset.univ.filter fun i : Fin 3 =>
          ((![pt0, pt12, pt1] i : Set.Icc (0 : ℝ) 1) : ℝ) < pt12) = {0} := by
        ext i; fin_cases i <;> simp [pt0, pt12, pt1]; norm_num
      rw [hS, hα1_0]; norm_num [pt12]
  have h3 : scheme3.eval ![pt1, pt0, pt1] = pt34 := by
    ext
    refine le_antisymm ?_ ?_
    · rw [← not_lt, scheme3.lt_eval_iff]
      have hS : (Finset.univ.filter fun i : Fin 3 =>
          ((![pt1, pt0, pt1] i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ pt34) = {1} := by
        ext i; fin_cases i <;> simp [pt0, pt1, pt34] <;> norm_num
      rw [hS, hα1_1]; norm_num [pt34]
    · rw [← not_lt, scheme3.eval_lt_iff]
      have hS : (Finset.univ.filter fun i : Fin 3 =>
          ((![pt1, pt0, pt1] i : Set.Icc (0 : ℝ) 1) : ℝ) < pt34) = {1} := by
        ext i; fin_cases i <;> simp [pt0, pt1, pt34] <;> norm_num
      rw [hS, hα1_1]; norm_num [pt34]
  have hEq := MoulinScheme.ofPhantoms_eval_eq_phantomMedian (by norm_num) phantoms3 phantoms3_mono
  refine ⟨(hEq _).symm.trans h1, (hEq _).symm.trans h2, ?_⟩
  let P : Profile (Fin 3) 0 1 :=
    ![Preference.symmetric pt12, Preference.leftExtreme (by norm_num),
      Preference.rightExtreme (by norm_num)]
  have hf_eq : ofPhantomMedian (ι := Fin 3) phantoms3 = ofMoulinScheme scheme3 := funext fun Q => by
    rw [ofPhantomMedian_apply, ofMoulinScheme_apply]
    exact (hEq (fun i => (Q i).peak)).symm
  have hSP : (ofPhantomMedian (ι := Fin 3) phantoms3).IsStrategyProof :=
    hf_eq ▸ ofMoulinScheme_isStrategyProof scheme3
  have hSurj : Function.Surjective (ofPhantomMedian (ι := Fin 3) phantoms3) :=
    hf_eq ▸ ofMoulinScheme_surjective scheme3
  rw [hSP.optionSet_eq_Icc hSurj P 0 (by norm_num)]
  have hL : ofPhantomMedian (ι := Fin 3) phantoms3
      (Function.update P 0 (Preference.leftExtreme (by norm_num))) = pt14 := by
    rw [hf_eq, ofMoulinScheme_apply]
    have hpk : (fun i => (Function.update P 0 (Preference.leftExtreme (by norm_num)) i).peak) =
        ![pt0, pt0, pt1] := by
      ext i; fin_cases i <;> simp [P, pt0, pt1]
    rw [hpk]; exact h1
  have hU : ofPhantomMedian (ι := Fin 3) phantoms3
      (Function.update P 0 (Preference.rightExtreme (by norm_num))) = pt34 := by
    rw [hf_eq, ofMoulinScheme_apply]
    have hpk : (fun i => (Function.update P 0 (Preference.rightExtreme (by norm_num)) i).peak) =
        ![pt1, pt0, pt1] := by
      ext i; fin_cases i <;> simp [P, pt0, pt1]
    rw [hpk]; exact h3
  rw [hL, hU]

/-- Separation between Theorem 10.4 (all GMVS) and Theorem 10.2 (anonymous phantom medians):
dictatorship of agent `0` among two agents is strategy-proof and surjective, yet not anonymous
and therefore not equal to `ofPhantomMedian y` for any phantom `y`. -/
example :
    let dict0 : Rule (Fin 2) 0 1 := fun P => (P 0).peak
    dict0.IsStrategyProof ∧ Function.Surjective dict0 ∧ ¬ dict0.IsAnonymous ∧
    (∃ E : MoulinScheme (Fin 2) 0 1, dict0 = ofMoulinScheme E) ∧
    ¬ ∃ y : Fin (Fintype.card (Fin 2) - 1) → Set.Icc (0 : ℝ) 1, dict0 = ofPhantomMedian y := by
  intro dict0
  have hSP : dict0.IsStrategyProof := by
    intro P Q i hPQ
    by_cases hi : i = 0
    · subst hi; exact (P 0).atLeast_peak _
    · have h0 : P 0 = Q 0 := hPQ 0 (Ne.symm hi)
      change (P i).AtLeast (P 0).peak (Q 0).peak
      rw [h0]; exact (P i).refl _
  have hSurj : Function.Surjective dict0 := fun x =>
    ⟨fun _ => Preference.symmetric x, Preference.symmetric_peak x⟩
  have hNotAnon : ¬ dict0.IsAnonymous := by
    intro hanon
    let P : Profile (Fin 2) 0 1 :=
      ![Preference.leftExtreme (by norm_num), Preference.rightExtreme (by norm_num)]
    have h := hanon (Equiv.swap 0 1) P
    have hval : (1 : ℝ) = 0 := by
      simpa [dict0, P, pt0, pt1] using congrArg Subtype.val h
    norm_num at hval
  have hGMVS : ∃ E : MoulinScheme (Fin 2) 0 1, dict0 = ofMoulinScheme E :=
    (isStrategyProof_and_surjective_iff_exists_moulinScheme (by norm_num) dict0).mp ⟨hSP, hSurj⟩
  have hNotPM : ¬ ∃ y : Fin (Fintype.card (Fin 2) - 1) → Set.Icc (0 : ℝ) 1,
      dict0 = ofPhantomMedian y := fun h =>
    hNotAnon
      ((isStrategyProof_surjective_anonymous_iff_phantomMedian (by norm_num) dict0).mpr h).2.2
  exact ⟨hSP, hSurj, hNotAnon, hGMVS, hNotPM⟩

/-! ### 4. Individual rationality uniqueness (§10.2.2, p. 252) -/

/-- The minimum-peak rule is individually rational with respect to `0`, whereas the phantom rule
with phantoms `(1/4, 3/4)` fails individual rationality with respect to `0`. -/
example :
    let minRule : Rule (Fin 3) 0 1 := ofMoulinScheme (minPeakScheme (by norm_num))
    (minRule.IsStrategyProof ∧ Function.Surjective minRule ∧ minRule.IsIndividuallyRational pt0) ∧
    ¬ (ofPhantomMedian (ι := Fin 3) phantoms3).IsIndividuallyRational pt0 := by
  intro minRule
  have hMin :=
    (isStrategyProof_surjective_isIR_left_iff (by norm_num) minRule).mpr rfl
  refine ⟨hMin, fun hIR => ?_⟩
  have hpm := (isStrategyProof_surjective_anonymous_iff_phantomMedian (by norm_num)
    (ofPhantomMedian (ι := Fin 3) phantoms3)).mpr ⟨phantoms3, rfl⟩
  have hEq : ofPhantomMedian (ι := Fin 3) phantoms3 = minRule :=
    (isStrategyProof_surjective_isIR_left_iff (by norm_num)
      (ofPhantomMedian (ι := Fin 3) phantoms3)).mp ⟨hpm.1, hpm.2.1, hIR⟩
  let P : Profile (Fin 3) 0 1 :=
    ![Preference.leftExtreme (by norm_num), Preference.leftExtreme (by norm_num),
      Preference.rightExtreme (by norm_num)]
  have hval := congrArg Subtype.val (congrFun hEq P)
  have hα2 : scheme3.alpha ({0, 1} : Finset (Fin 3)) = 1 / 4 := by
    rw [scheme3, MoulinScheme.ofPhantoms_alpha (by norm_num) phantoms3 phantoms3_mono
      (by decide) (by decide)]
    rfl
  have hLHS : ((ofPhantomMedian (ι := Fin 3) phantoms3 P : Set.Icc (0 : ℝ) 1) : ℝ) = 1 / 4 := by
    have hpk : (fun i => (P i).peak) = ![pt0, pt0, pt1] := by
      ext i; fin_cases i <;> simp [P, pt0, pt1]
    rw [ofPhantomMedian_apply, hpk,
      ← MoulinScheme.ofPhantoms_eval_eq_phantomMedian (by norm_num) phantoms3 phantoms3_mono]
    change (scheme3.eval ![pt0, pt0, pt1] : ℝ) = 1 / 4
    have hS : (Finset.univ.filter fun i : Fin 3 =>
        ((![pt0, pt0, pt1] i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ pt14) = {0, 1} := by
      ext i; fin_cases i <;> simp [pt0, pt1, pt14]; norm_num
    have hS' : (Finset.univ.filter fun i : Fin 3 =>
        ((![pt0, pt0, pt1] i : Set.Icc (0 : ℝ) 1) : ℝ) < pt14) = {0, 1} := by
      ext i; fin_cases i <;> simp [pt0, pt1, pt14]; norm_num
    refine le_antisymm ?_ ?_
    · rw [← not_lt]
      have := (scheme3.lt_eval_iff ![pt0, pt0, pt1] pt14).not.mpr
      apply this
      rw [hS, hα2]; norm_num [pt14]
    · rw [← not_lt]
      have := (scheme3.eval_lt_iff ![pt0, pt0, pt1] pt14).not.mpr
      apply this
      rw [hS', hα2]; norm_num [pt14]
  have hRHS : ((minRule P : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by
    dsimp only [minRule]
    rw [ofMoulinScheme_apply, minPeakScheme_eval]
    refine le_antisymm ?_ ?_
    · exact (Finset.inf'_le (fun i : Fin 3 => ((P i).peak : ℝ)) (Finset.mem_univ 0)).trans
        (by simp [P])
    · exact (Finset.le_inf'_iff _ _).mpr fun i _ => (P i).peak.2.1
  linarith

/-! ### 5. Symmetric path-distance 3-leaf facility location (`star3`, after Exercise 10.5) -/

section ThreeLeafTreeClients

private def star3Graph : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with ⟨rfl, hne⟩ | ⟨rfl, hne⟩ <;> exact hne rfl⟩

private theorem star3Graph_connected : star3Graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv; exact Reachable.refl 0
  · exact Adj.reachable (Or.inl ⟨rfl, hv⟩)

private theorem star3Graph_isAcyclic : star3Graph.IsAcyclic := by
  intro v₀ c hc
  have hlen := hc.three_le_length
  have hnd := hc.support_nodup
  cases c with
  | nil => simp at hlen
  | @cons _ b _ h1 c1 =>
    cases c1 with
    | nil => simp at hlen
    | @cons _ w _ h2 c2 =>
      cases c2 with
      | nil => simp at hlen
      | @cons _ z _ h3 q =>
        rw [Walk.support_cons, List.tail_cons, Walk.support_cons, List.nodup_cons] at hnd
        rcases h1 with ⟨rfl, hb⟩ | ⟨rfl, hv⟩
        · rcases h2 with ⟨hbw, _⟩ | ⟨rfl, _⟩
          · exact absurd hbw hb
          · rw [Walk.support_cons, List.nodup_cons] at hnd
            exact hnd.2.1 (Walk.end_mem_support q)
        · rcases h2 with ⟨_, hw⟩ | ⟨_, hne0⟩
          · rcases h3 with ⟨hwz, _⟩ | ⟨rfl, _⟩
            · exact absurd hwz hw
            · exact hnd.1 (List.mem_cons_of_mem w (Walk.start_mem_support q))
          · exact absurd rfl hne0

private noncomputable def star3 : WeightedGraph (Fin 4) :=
  equalLength star3Graph star3Graph_connected 1 one_pos

private theorem star3_isTree : star3.graph.IsTree :=
  ⟨star3Graph_connected, star3Graph_isAcyclic⟩

private theorem star3_dist_center_leaf (r : Fin 3) :
    dist (vertex 0 : MetricGraph star3) (vertex r.succ) = 1 := by
  rw [dist_vertex, vertexDist_adj star3_isTree (Or.inl ⟨rfl, Fin.succ_ne_zero r⟩)]
  rfl

private noncomputable def star3Tripod : Tripod star3 where
  center := vertex 0
  leaf r := vertex r.succ
  leaf_ne_center r h := Fin.succ_ne_zero r (vertex_injective h)
  cover x := by
    induction x using MetricGraph.ind with
    | vertex v =>
      cases v using Fin.cases with
      | zero => exact ⟨0, left_mem_interval _ _⟩
      | succ r => exact ⟨r, right_mem_interval _ _⟩
    | edgePoint d t =>
      rcases d.adj with ⟨h0, hv⟩ | ⟨h0, hu⟩
      · obtain ⟨r, hr⟩ := Fin.exists_succ_eq.mpr hv
        refine ⟨r, ?_⟩
        have hd : d.fst = 0 ∧ d.snd = r.succ := ⟨h0, hr.symm⟩
        simpa only [hd.1, hd.2] using edgePoint_mem_interval_vertex star3_isTree d t
      · obtain ⟨r, hr⟩ := Fin.exists_succ_eq.mpr hu
        refine ⟨r, ?_⟩
        rw [interval_comm]
        have hd : d.fst = r.succ ∧ d.snd = 0 := ⟨hr.symm, h0⟩
        simpa only [hd.1, hd.2] using edgePoint_mem_interval_vertex star3_isTree d t
  inter_eq {r s} hrs := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hr, hs⟩
      by_contra hx0
      have hpos : 0 < dist (vertex 0 : MetricGraph star3) x := dist_pos.mpr (Ne.symm hx0)
      have hbr : ∀ t : Fin 3, x ∈ interval (vertex 0 : MetricGraph star3) (vertex t.succ) →
          x ∈ branch (vertex 0 : MetricGraph star3) (vertex t.succ) := fun t ht h0 => by
        rw [mem_interval_iff] at ht h0
        rw [_root_.dist_comm (vertex t.succ) (vertex 0),
          _root_.dist_comm (vertex t.succ) x] at h0
        linarith
      have hdisj := disjoint_branch_vertex_of_adj star3_isTree
        (Or.inl ⟨rfl, Fin.succ_ne_zero r⟩) (Or.inl ⟨rfl, Fin.succ_ne_zero s⟩)
        (fun h => hrs (Fin.succ_injective _ h))
      exact Set.disjoint_left.mp hdisj (hbr r hr) (hbr s hs)
    · rintro rfl
      exact ⟨left_mem_interval _ _, left_mem_interval _ _⟩

/-- **Family I** (two phantoms at `1/4` and `3/4` on leg `0`, zero on legs `1, 2`). -/
private noncomputable def familyIScheme : ThreeLeafScheme star3Tripod where
  low := ![1 / 4, 0, 0]
  high := ![3 / 4, 0, 0]
  low_nonneg r := by fin_cases r <;> norm_num
  low_le_high r := by fin_cases r <;> norm_num
  high_le_dist r := by
    dsimp only [star3Tripod]
    rw [star3_dist_center_leaf]
    fin_cases r <;> norm_num
  exclusive_legs {r s} hrs hr := by
    fin_cases r <;> fin_cases s <;> simp at hrs hr ⊢

/-- **Family II** (three positive leg caps `high = ![1/2, 1/2, 1/2]` and `low = 0`), witnessing
an anonymous strategy-proof surjective 3-agent rule on a 3-leaved tree that cannot be realized by
placing only two phantom voters in the tree. -/
private noncomputable def familyIIScheme : ThreeLeafScheme star3Tripod where
  low := ![0, 0, 0]
  high := ![1 / 2, 1 / 2, 1 / 2]
  low_nonneg r := by fin_cases r <;> norm_num
  low_le_high r := by fin_cases r <;> norm_num
  high_le_dist r := by
    dsimp only [star3Tripod]
    rw [star3_dist_center_leaf]
    fin_cases r <;> norm_num
  exclusive_legs {r s} _ hr := by fin_cases r <;> norm_num at hr

example :
    (Mechanism.deterministic (familyIScheme.eval star3_isTree)).IsGroupStrategyProof ∧
    Function.Surjective (familyIScheme.eval star3_isTree) ∧
    FacilityLocation.IsAnonymous (familyIScheme.eval star3_isTree) ∧
    (Mechanism.deterministic (familyIIScheme.eval star3_isTree)).IsGroupStrategyProof ∧
    Function.Surjective (familyIIScheme.eval star3_isTree) ∧
    FacilityLocation.IsAnonymous (familyIIScheme.eval star3_isTree) ∧
    (∀ r : Fin 3, 0 < familyIIScheme.high r) :=
  ⟨familyIScheme.eval_isGroupStrategyProof star3_isTree,
    familyIScheme.eval_surjective star3_isTree,
    familyIScheme.eval_isAnonymous star3_isTree,
    familyIIScheme.eval_isGroupStrategyProof star3_isTree,
    familyIIScheme.eval_surjective star3_isTree,
    familyIIScheme.eval_isAnonymous star3_isTree,
    fun r => by fin_cases r <;> norm_num [familyIIScheme]⟩

/-- Both branches of `ThreeLeafScheme.dichotomy` and both directions of
`isStrategyProof_surjective_anonymous_iff_threeLeafScheme` on `star3`: `familyIScheme` lies in the
single-leg branch, `familyIIScheme` lies in the `low = 0` branch and satisfies the symmetric
3-leaf characterization, while agent-`0` dictatorship is strategy-proof and surjective yet not
equal to `P.eval star3_isTree` for any `ThreeLeafScheme`. -/
example :
    (∃ r : Fin 3, 0 < familyIScheme.low r ∧
      ∀ s : Fin 3, s ≠ r → familyIScheme.low s = 0 ∧ familyIScheme.high s = 0) ∧
    (∀ r : Fin 3, familyIIScheme.low r = 0) ∧
    ((Mechanism.deterministic (familyIIScheme.eval star3_isTree)).IsStrategyProof ∧
      Function.Surjective (familyIIScheme.eval star3_isTree) ∧
      FacilityLocation.IsAnonymous (familyIIScheme.eval star3_isTree)) ∧
    ¬ ∃ P : ThreeLeafScheme star3Tripod,
      (fun x : Fin 3 → MetricGraph star3 => x 0) = P.eval star3_isTree := by
  have h1 : ∃ r : Fin 3, 0 < familyIScheme.low r ∧
      ∀ s : Fin 3, s ≠ r → familyIScheme.low s = 0 ∧ familyIScheme.high s = 0 := by
    rcases familyIScheme.dichotomy with h | h
    · exact h
    · exfalso
      have h0 := h 0
      norm_num [familyIScheme] at h0
  have h2 : ∀ r : Fin 3, familyIIScheme.low r = 0 := by
    rcases familyIIScheme.dichotomy with ⟨r, hr, _⟩ | h
    · exfalso
      fin_cases r <;> norm_num [familyIIScheme] at hr
    · exact h
  have hII :=
    (isStrategyProof_surjective_anonymous_iff_threeLeafScheme star3_isTree star3Tripod
      (familyIIScheme.eval star3_isTree)).mpr ⟨familyIIScheme, rfl⟩
  refine ⟨h1, h2, hII, fun hex => ?_⟩
  have hanon :=
    ((isStrategyProof_surjective_anonymous_iff_threeLeafScheme star3_isTree star3Tripod
      (fun x : Fin 3 → MetricGraph star3 => x 0)).mpr hex).2.2
  have hswap : (vertex 2 : MetricGraph star3) = vertex 1 :=
    hanon (Equiv.swap 0 1) ![vertex 1, vertex 2, vertex 1]
  exact absurd (vertex_injective hswap) (by decide)

end ThreeLeafTreeClients

end CslibFrontierTests.GameTheory.SinglePeaked
