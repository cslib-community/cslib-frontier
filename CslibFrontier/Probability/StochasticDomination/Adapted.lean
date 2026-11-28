/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Azuma
public import CslibFrontier.Probability.StochasticDomination.PoissonBinomial
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Process.Filtration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Adapted

/-!
# Stochastic domination for adapted Bernoulli event counts

First-order stochastic domination between adapted event counts `adaptedCount A n` under a
general filtration `ℱ : Filtration ℕ m` (and specifically under `ProbabilityTheory.Kernel.traj` /
`ProbabilityTheory.Kernel.trajMeasure`, as well as finite-horizon sequential `PMF` processes) and
the Poisson-binomial distribution `Cslib.Probability.PMF.poissonBinomial` (or Mathlib's
`ProbabilityTheory.binomial` in the uniform-envelope case).

Both lower-envelope domination (`ps[t] ≤ P[A t | ℱ t]`, giving `adaptedCount ≥_st poissonBinomial`)
and upper-envelope domination (`P[A t | ℱ t] ≤ ps[t]`, giving `poissonBinomial ≥_st adaptedCount`)
are proved, together with active-before-target variants requiring the conditional probability
bound only on `{ω | adaptedCount A t ω < r}`.

## Main definitions

* `Cslib.Probability.adaptedCount`: cumulative number of events among `A 0, ..., A (n - 1)`.
* `Cslib.Probability.shiftFiltration`: filtration shifted forward by a starting index `a`.
* `Cslib.Probability.PMF.seqCount`: finite-horizon sequential `PMF` success counts along
  `Cslib.Probability.PMF.seqProcess`.

## Main results

* `Cslib.Probability.adaptedCount_stochasticallyDominates_poissonBinomial`,
  `Cslib.Probability.poissonBinomial_stochasticallyDominates_adaptedCount`: unconditional adapted
  domination over a general filtration.
* `Cslib.Probability.adaptedCount_min_stochasticallyDominates_poissonBinomial`,
  `Cslib.Probability.adaptedCount_real_Iio_le_binomial`: active-before-target (`count < r`)
  domination and uniform binomial tail bounds.
* `Cslib.Probability.traj_adaptedCount_stochasticallyDominates_poissonBinomial`,
  `Cslib.Probability.poissonBinomial_stochasticallyDominates_traj_adaptedCount`,
  `Cslib.Probability.trajMeasure_adaptedCount_stochasticallyDominates_poissonBinomial`,
  `Cslib.Probability.poissonBinomial_stochasticallyDominates_trajMeasure_adaptedCount`:
  lower- and upper-envelope specializations to `ProbabilityTheory.Kernel.traj` and
  `Kernel.trajMeasure`.
* `Cslib.Probability.PMF.seqCount_stochasticallyDominates_poissonBinomial`,
  `Cslib.Probability.PMF.seqCount_active_toReal_Iio_le`,
  `Cslib.Probability.PMF.seqCount_ge_le`,
  `Cslib.Probability.PMF.seqCount_le_le`: sequential finite-horizon `PMF` domination and
  Azuma–Hoeffding tail bounds.
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal unitInterval

section AdaptedCount

/-- Number of events among `A 0, ..., A (n - 1)` occurring at outcome `ω`. -/
@[expose]
noncomputable def adaptedCount {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℕ :=
  ∑ t ∈ Finset.range n, (A t).indicator (fun _ => 1) ω

@[simp]
theorem adaptedCount_zero {Ω : Type*} (A : ℕ → Set Ω) (ω : Ω) :
    adaptedCount A 0 ω = 0 := by
  simp [adaptedCount]

theorem adaptedCount_succ {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    adaptedCount A (n + 1) ω = adaptedCount A n ω + (A n).indicator (fun _ => 1) ω := by
  simp [adaptedCount, Finset.sum_range_succ]

theorem adaptedCount_le {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    adaptedCount A n ω ≤ n := by
  calc adaptedCount A n ω
      ≤ ∑ _ ∈ Finset.range n, 1 :=
        Finset.sum_le_sum fun t _ => by by_cases h : ω ∈ A t <;> simp [h]
    _ = n := by simp

theorem adaptedCount_mono {Ω : Type*} (A : ℕ → Set Ω) (ω : Ω) :
    Monotone fun n => adaptedCount A n ω :=
  fun _ _ hmn => Finset.sum_le_sum_of_subset (Finset.range_mono hmn)

theorem measurable_adaptedCount {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℕ m) {A : ℕ → Set Ω} (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (n : ℕ) :
    Measurable[ℱ n] (adaptedCount A n) := by
  induction n with
  | zero => simpa only [show adaptedCount A 0 = fun _ => 0 from funext (adaptedCount_zero A)]
      using measurable_const
  | succ n ih =>
    rw [show adaptedCount A (n + 1) = fun ω => adaptedCount A n ω + (A n).indicator (fun _ => 1) ω
      from funext (adaptedCount_succ A n)]
    exact (ih.mono (ℱ.mono n.le_succ) le_rfl).add (measurable_const.indicator (hA n))

theorem adapted_adaptedCount {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℕ m) {A : ℕ → Set Ω} (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) :
    Adapted ℱ (adaptedCount A) :=
  fun n => measurable_adaptedCount ℱ hA n

end AdaptedCount

section BackwardInduction

private noncomputable def pbValue (ps : List I) (f : ℕ → ℝ) (k m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range ((ps.drop k).length + 1),
    (PMF.poissonBinomial (ps.drop k) j).toReal * f (m + j)

private theorem pbValue_mono {ps : List I} {f : ℕ → ℝ} (hf : Monotone f) (k : ℕ) :
    Monotone (pbValue ps f k) := by
  intro m₁ m₂ hm
  refine Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul_of_nonneg_left (hf (Nat.add_le_add_right hm j)) ENNReal.toReal_nonneg

private theorem pbValue_length (ps : List I) (f : ℕ → ℝ) (m : ℕ) :
    pbValue ps f ps.length m = f m := by
  simp [pbValue]

private theorem pbValue_zero (ps : List I) (f : ℕ → ℝ) :
    pbValue ps f 0 0 =
      ∑ j ∈ Finset.range (ps.length + 1), (PMF.poissonBinomial ps j).toReal * f j := by
  simp [pbValue]

private theorem pbValue_step (ps : List I) (f : ℕ → ℝ) {k : ℕ} (hk : k < ps.length)
    (m : ℕ) :
    pbValue ps f k m =
      pbValue ps f (k + 1) m +
        (ps[k] : ℝ) * (pbValue ps f (k + 1) (m + 1) - pbValue ps f (k + 1) m) := by
  let qs := ps.drop (k + 1)
  have hdrop : ps.drop k = ps[k] :: qs := List.drop_eq_getElem_cons hk
  have hlen : (ps.drop k).length = qs.length + 1 := by rw [hdrop, List.length_cons]
  have hpb0 : pbValue ps f (k + 1) m =
      (PMF.poissonBinomial qs 0).toReal * f (m + 0) +
        ∑ x ∈ Finset.range (qs.length + 1),
          (PMF.poissonBinomial qs (x + 1)).toReal * f (m + (x + 1)) := by
    have hpb2 : pbValue ps f (k + 1) m =
        ∑ j ∈ Finset.range (qs.length + 2), (PMF.poissonBinomial qs j).toReal * f (m + j) := by
      rw [Finset.sum_range_succ,
        PMF.poissonBinomial_eq_zero_of_lt (ps := qs) (Nat.lt_succ_self _)]
      simp [pbValue, qs]
    rw [hpb2, Finset.sum_range_succ' (fun j => (PMF.poissonBinomial qs j).toReal * f (m + j)),
      add_comm]
  have hpb1 : pbValue ps f (k + 1) (m + 1) =
      ∑ x ∈ Finset.range (qs.length + 1),
        (PMF.poissonBinomial qs x).toReal * f (m + (x + 1)) := by
    change (∑ x ∈ Finset.range (qs.length + 1),
      (PMF.poissonBinomial qs x).toReal * f (m + 1 + x)) = _
    exact Finset.sum_congr rfl fun x _ => by rw [Nat.add_assoc, Nat.add_comm 1 x]
  rw [pbValue, hlen, Finset.sum_range_succ']
  simp_rw [hdrop, PMF.poissonBinomial_cons_zero_toReal, PMF.poissonBinomial_cons_succ_toReal,
    add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hpb0, hpb1]
  ring

private theorem pbValue_abs_le {ps : List I} {f : ℕ → ℝ} {C : ℝ} (hC : ∀ j, |f j| ≤ C)
    (k m : ℕ) :
    |pbValue ps f k m| ≤ C := by
  have hsum : ∑ j ∈ Finset.range ((ps.drop k).length + 1),
      (PMF.poissonBinomial (ps.drop k) j).toReal = 1 := by
    rw [← PMF.tsum_toReal (PMF.poissonBinomial (ps.drop k))]
    exact (tsum_eq_sum fun j hj => by
      simp [PMF.poissonBinomial_eq_zero_of_lt (by simpa using hj : (ps.drop k).length < j)]).symm
  calc |pbValue ps f k m|
      ≤ ∑ j ∈ Finset.range ((ps.drop k).length + 1),
          (PMF.poissonBinomial (ps.drop k) j).toReal * C :=
        (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          exact mul_le_mul_of_nonneg_left (hC (m + j)) ENNReal.toReal_nonneg
    _ = C := by rw [← Finset.sum_mul, hsum, one_mul]

end BackwardInduction

section FiltrationComparison

private theorem integrable_pbValue {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (ps : List I) {f : ℕ → ℝ} {C : ℝ} (hC : ∀ j, |f j| ≤ C) (k n : ℕ) :
    Integrable (fun ω => pbValue ps f k (adaptedCount A n ω)) P := by
  have hm : Measurable (fun ω => pbValue ps f k (adaptedCount A n ω)) :=
    (measurable_from_top : Measurable (pbValue ps f k)).comp
      ((measurable_adaptedCount ℱ hA n).mono (ℱ.le n) le_rfl)
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun ω => pbValue_abs_le hC k _)

private theorem integral_pbValue_step_diff {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (ps : List I) {f : ℕ → ℝ} (hf : Monotone f) {C : ℝ} (hC : ∀ j, |f j| ≤ C)
    {k : ℕ} (hk : k < ps.length) :
    ∃ D : Ω → ℝ, (∀ ω, 0 ≤ D ω) ∧
      Integrable (fun ω => D ω * (ps[k] : ℝ)) P ∧
      Integrable (fun ω => D ω * P[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω) P ∧
      ∃ base : ℝ,
        ∫ ω, pbValue ps f k (adaptedCount A k ω) ∂P = base + ∫ ω, D ω * (ps[k] : ℝ) ∂P ∧
        ∫ ω, pbValue ps f (k + 1) (adaptedCount A (k + 1) ω) ∂P =
          base + ∫ ω, D ω * P[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω ∂P := by
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  let D : Ω → ℝ := fun ω =>
    pbValue ps f (k + 1) (adaptedCount A k ω + 1) - pbValue ps f (k + 1) (adaptedCount A k ω)
  let Iₖ : Ω → ℝ := (A k).indicator (fun _ => 1)
  have hD_sm : StronglyMeasurable[ℱ k] D :=
    ((measurable_from_top :
        Measurable fun m => pbValue ps f (k + 1) (m + 1) - pbValue ps f (k + 1) m).comp
      (measurable_adaptedCount ℱ hA k)).stronglyMeasurable
  have hI_int : Integrable Iₖ P := (integrable_const (1 : ℝ)).indicator (ℱ.le (k + 1) _ (hA k))
  have hD_bd (ω : Ω) : |D ω| ≤ 2 * C := (abs_sub _ _).trans <| by
    linarith [pbValue_abs_le (ps := ps) hC (k + 1) (adaptedCount A k ω + 1),
      pbValue_abs_le (ps := ps) hC (k + 1) (adaptedCount A k ω)]
  have hDI_int : Integrable (fun ω => D ω * Iₖ ω) P :=
    Integrable.of_bound ((hD_sm.mono (ℱ.le k)).aestronglyMeasurable.mul hI_int.aestronglyMeasurable)
      (2 * C) (ae_of_all _ fun ω => by
        have hI_bd : |Iₖ ω| ≤ 1 := by by_cases hω : ω ∈ A k <;> simp [Iₖ, hω]
        simpa [abs_mul] using mul_le_mul (hD_bd ω) hI_bd (abs_nonneg _) (by positivity))
  have hbase_int := integrable_pbValue (P := P) ℱ hA ps hC (k + 1) k
  have hDp_int : Integrable (fun ω => D ω * (ps[k] : ℝ)) P :=
    (Integrable.of_bound (hD_sm.mono (ℱ.le k)).aestronglyMeasurable (2 * C)
      (ae_of_all _ hD_bd)).mul_const _
  have hDce_int : Integrable (fun ω => D ω * P[Iₖ | ℱ k] ω) P := by
    have h0 : (fun _ : Ω => (0 : ℝ)) ≤ᵐ[P] P[Iₖ | ℱ k] :=
      condExp_nonneg (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    have h1 : P[Iₖ | ℱ k] ≤ᵐ[P] fun _ => (1 : ℝ) := by
      calc P[Iₖ | ℱ k] ≤ᵐ[P] P[fun _ : Ω => (1 : ℝ) | ℱ k] :=
            condExp_mono hI_int (integrable_const 1) <| ae_of_all _ fun ω => by
              by_cases hω : ω ∈ A k <;> simp [Iₖ, hω]
        _ =ᵐ[P] fun _ => (1 : ℝ) := by rw [condExp_const (ℱ.le k) (1 : ℝ)]
    refine Integrable.of_bound
      ((hD_sm.mono (ℱ.le k)).aestronglyMeasurable.mul
        (stronglyMeasurable_condExp.mono (ℱ.le k)).aestronglyMeasurable)
      (2 * C) ?_
    filter_upwards [h0, h1] with ω hω0 hω1
    simpa [Real.norm_eq_abs, abs_mul] using mul_le_mul (hD_bd ω) (abs_le.mpr ⟨by linarith, hω1⟩)
      (abs_nonneg _) (by positivity)
  have hsplit_lhs : (fun ω => pbValue ps f k (adaptedCount A k ω)) =
      fun ω => pbValue ps f (k + 1) (adaptedCount A k ω) + D ω * (ps[k] : ℝ) := funext fun ω => by
    rw [pbValue_step ps f hk (adaptedCount A k ω), mul_comm (ps[k] : ℝ)]
  have hsplit_rhs : (fun ω => pbValue ps f (k + 1) (adaptedCount A (k + 1) ω)) =
      fun ω => pbValue ps f (k + 1) (adaptedCount A k ω) + D ω * Iₖ ω := funext fun ω => by
    rw [adaptedCount_succ]
    by_cases hω : ω ∈ A k <;> simp [Iₖ, D, hω]
  refine ⟨D, fun ω => sub_nonneg.mpr (pbValue_mono hf (k + 1) (Nat.le_succ _)), hDp_int, hDce_int,
    ∫ ω, pbValue ps f (k + 1) (adaptedCount A k ω) ∂P, ?_, ?_⟩
  · rw [hsplit_lhs, integral_add hbase_int hDp_int]
  · rw [hsplit_rhs, integral_add hbase_int hDI_int]
    congr 1
    exact (integral_condExp (ℱ.le k)).symm.trans
      (integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hD_sm hDI_int hI_int))

private lemma add_integral_mul_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D f g : Ω → ℝ} {base lhs rhs : ℝ}
    (hl : lhs = base + ∫ ω, D ω * f ω ∂P) (hr : rhs = base + ∫ ω, D ω * g ω ∂P)
    (hD : ∀ ω, 0 ≤ D ω) (hf : Integrable (fun ω => D ω * f ω) P)
    (hg : Integrable (fun ω => D ω * g ω) P) (hfg : f ≤ᵐ[P] g) :
    lhs ≤ rhs := by
  rw [hl, hr]
  refine add_le_add_right (integral_mono_ae hf hg ?_) base
  filter_upwards [hfg] with ω hω
  exact mul_le_mul_of_nonneg_left hω (hD ω)

private theorem integral_pbValue_le_succ {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (ps : List I) {f : ℕ → ℝ} (hf : Monotone f) {C : ℝ} (hC : ∀ j, |f j| ≤ C)
    {k : ℕ} (hk : k < ps.length)
    (hp : (fun _ => (ps[k] : ℝ)) ≤ᵐ[P] P[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k]) :
    ∫ ω, pbValue ps f k (adaptedCount A k ω) ∂P ≤
      ∫ ω, pbValue ps f (k + 1) (adaptedCount A (k + 1) ω) ∂P := by
  rcases integral_pbValue_step_diff P ℱ hA ps hf hC hk with
    ⟨D, hD_nn, hDp_int, hDce_int, base, h1, h2⟩
  exact add_integral_mul_le h1 h2 hD_nn hDp_int hDce_int hp

private theorem integral_pbValue_succ_le {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (ps : List I) {f : ℕ → ℝ} (hf : Monotone f) {C : ℝ} (hC : ∀ j, |f j| ≤ C)
    {k : ℕ} (hk : k < ps.length)
    (hp : P[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ≤ᵐ[P] fun _ => (ps[k] : ℝ)) :
    ∫ ω, pbValue ps f (k + 1) (adaptedCount A (k + 1) ω) ∂P ≤
      ∫ ω, pbValue ps f k (adaptedCount A k ω) ∂P := by
  rcases integral_pbValue_step_diff P ℱ hA ps hf hC hk with
    ⟨D, hD_nn, hDp_int, hDce_int, base, h1, h2⟩
  exact add_integral_mul_le h2 h1 hD_nn hDce_int hDp_int hp

private theorem pbValue_zero_Ici_eq_real (ps : List I) (r : ℕ) :
    pbValue ps ((Set.Ici r).indicator (fun _ => (1 : ℝ))) 0 0 =
      (PMF.poissonBinomial ps).toMeasure.real (Set.Ici r) := by
  rw [pbValue_zero, measureReal_def, PMF.toMeasure_apply _ measurableSet_Ici]
  have hfin : (∑' j : ℕ, (Set.Ici r).indicator (⇑(PMF.poissonBinomial ps)) j) =
      ∑ j ∈ Finset.range (ps.length + 1),
        (Set.Ici r).indicator (⇑(PMF.poissonBinomial ps)) j :=
    tsum_eq_sum fun j hj => by
      simp [PMF.poissonBinomial_eq_zero_of_lt (by simpa using hj : ps.length < j)]
  rw [hfin, ENNReal.toReal_sum fun j _ => by
    dsimp only [Set.indicator]; split_ifs <;> simp [PMF.apply_ne_top]]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : r ≤ j <;> simp [hj]

private theorem monotone_indicator_Ici (r : ℕ) :
    Monotone ((Set.Ici r).indicator (fun _ => (1 : ℝ))) := by
  intro a b hab
  by_cases ha : r ≤ a
  · have hb : r ≤ b := ha.trans hab
    simp [ha, hb]
  · by_cases hb : r ≤ b <;> simp [ha, hb]

private theorem abs_indicator_Ici_le_one (r j : ℕ) :
    |(Set.Ici r).indicator (fun _ => (1 : ℝ)) j| ≤ 1 := by
  by_cases hj : r ≤ j <;> simp [hj]

private theorem integral_indicator_Ici_adaptedCount {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (n r : ℕ) :
    ∫ ω, (Set.Ici r).indicator (fun _ => (1 : ℝ)) (adaptedCount A n ω) ∂P =
      (P.map (adaptedCount A n)).real (Set.Ici r) := by
  have hm : Measurable (adaptedCount A n) :=
    (measurable_adaptedCount ℱ hA n).mono (ℱ.le _) le_rfl
  rw [measureReal_def, Measure.map_apply hm measurableSet_Ici, ← measureReal_def,
    ← integral_indicator_one (hm measurableSet_Ici)]
  rfl

private theorem Ici_le_of_measureReal_le {μ ν : Measure ℕ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {r : ℕ} (h : μ.real (Set.Ici r) ≤ ν.real (Set.Ici r)) :
    μ (Set.Ici r) ≤ ν (Set.Ici r) := by
  rw [measureReal_def, measureReal_def] at h
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm.trans_le
    ((ENNReal.ofReal_le_ofReal h).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _)))

/-- **Adapted Poisson-binomial domination (lower envelope)**: if `A t` is `ℱ (t + 1)`-measurable
and `P[A t | ℱ t] ≥ ps[t]` a.e. for all `t < ps.length`, then the law of `adaptedCount A ps.length`
stochastically dominates `PMF.poissonBinomial ps`. -/
theorem adaptedCount_stochasticallyDominates_poissonBinomial {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length),
      (fun _ => (ps[t] : ℝ)) ≤ᵐ[P] P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t]) :
    StochasticallyDominates (P.map (adaptedCount A ps.length))
      (PMF.poissonBinomial ps).toMeasure := by
  rw [stochasticallyDominates_nat_iff_Ici]
  intro r
  let f : ℕ → ℝ := (Set.Ici r).indicator (fun _ => 1)
  have hchain (k : ℕ) (hk : k ≤ ps.length) :
      pbValue ps f 0 0 ≤ ∫ ω, pbValue ps f k (adaptedCount A k ω) ∂P := by
    induction k with
    | zero => simp
    | succ k ih =>
      exact (ih (Nat.le_of_succ_le hk)).trans
        (integral_pbValue_le_succ ℱ hA ps (monotone_indicator_Ici r)
          (abs_indicator_Ici_le_one r) hk (hp k hk))
  have hmain : pbValue ps f 0 0 ≤ ∫ ω, f (adaptedCount A ps.length ω) ∂P := by
    simpa [pbValue_length] using hchain ps.length le_rfl
  rw [pbValue_zero_Ici_eq_real, integral_indicator_Ici_adaptedCount ℱ hA] at hmain
  exact Ici_le_of_measureReal_le hmain

/-- **Adapted Poisson-binomial domination (upper envelope)**: if `A t` is `ℱ (t + 1)`-measurable
and `P[A t | ℱ t] ≤ ps[t]` a.e. for all `t < ps.length`, then `PMF.poissonBinomial ps`
stochastically dominates the law of `adaptedCount A ps.length`. -/
theorem poissonBinomial_stochasticallyDominates_adaptedCount {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length),
      P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P] fun _ => (ps[t] : ℝ)) :
    StochasticallyDominates (PMF.poissonBinomial ps).toMeasure
      (P.map (adaptedCount A ps.length)) := by
  rw [stochasticallyDominates_nat_iff_Ici]
  intro r
  let f : ℕ → ℝ := (Set.Ici r).indicator (fun _ => 1)
  have hchain (k : ℕ) (hk : k ≤ ps.length) :
      ∫ ω, pbValue ps f k (adaptedCount A k ω) ∂P ≤ pbValue ps f 0 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      exact (integral_pbValue_succ_le ℱ hA ps (monotone_indicator_Ici r)
        (abs_indicator_Ici_le_one r) hk (hp k hk)).trans (ih (Nat.le_of_succ_le hk))
  have hmain : ∫ ω, f (adaptedCount A ps.length ω) ∂P ≤ pbValue ps f 0 0 := by
    simpa [pbValue_length] using hchain ps.length le_rfl
  rw [pbValue_zero_Ici_eq_real, integral_indicator_Ici_adaptedCount ℱ hA] at hmain
  exact Ici_le_of_measureReal_le hmain

/-- If `adaptedCount A n ω < r` and `B t` agrees with `A t` at `ω` for every `t < n` where
`adaptedCount A t ω < r`, then `adaptedCount B n ω = adaptedCount A n ω`. -/
theorem adaptedCount_congr_of_lt {Ω : Type*} {A B : ℕ → Set Ω} {r n : ℕ} {ω : Ω}
    (hlt : adaptedCount A n ω < r)
    (hiff : ∀ t < n, adaptedCount A t ω < r → (ω ∈ B t ↔ ω ∈ A t)) :
    adaptedCount B n ω = adaptedCount A n ω := by
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  have ht_lt : adaptedCount A t ω < r := (adaptedCount_mono A ω ht.le).trans_lt hlt
  by_cases hmem : ω ∈ A t <;> simp [hiff t ht ht_lt, hmem]

private theorem adaptedCount_min_eq_of_union {Ω : Type*} (A : ℕ → Set Ω) (r n : ℕ) (ω : Ω) :
    min (adaptedCount A n ω) r =
      min (adaptedCount (fun t => A t ∪ {ω' | r ≤ adaptedCount A t ω'}) n ω) r := by
  let A' := fun t => A t ∪ {ω' | r ≤ adaptedCount A t ω'}
  have hle : adaptedCount A n ω ≤ adaptedCount A' n ω := by
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases ht : ω ∈ A t <;> simp [A', ht]
  by_cases hreach : r ≤ adaptedCount A n ω
  · have hreach' : r ≤ adaptedCount A' n ω := hreach.trans hle
    rw [min_eq_right hreach, min_eq_right hreach']
  · have hlt : adaptedCount A n ω < r := not_le.mp hreach
    have heq : adaptedCount A' n ω = adaptedCount A n ω :=
      adaptedCount_congr_of_lt hlt fun t _ ht => by simp [A', not_le.mpr ht]
    rw [heq]

private theorem adaptedCount_min_eq_of_inter {Ω : Type*} (A : ℕ → Set Ω) (r n : ℕ) (ω : Ω) :
    min (adaptedCount A n ω) r =
      min (adaptedCount (fun t => A t ∩ {ω' | adaptedCount A t ω' < r}) n ω) r := by
  let A'' := fun t => A t ∩ {ω' | adaptedCount A t ω' < r}
  have heq_lt (k : ℕ) (hk : adaptedCount A k ω < r) : adaptedCount A'' k ω = adaptedCount A k ω :=
    adaptedCount_congr_of_lt hk fun _ _ ht => by simp [A'', ht]
  by_cases hreach : r ≤ adaptedCount A n ω
  · have hr_le : ∀ k, r ≤ adaptedCount A k ω → r ≤ adaptedCount A'' k ω := by
      intro k hk
      induction k with
      | zero => simpa using hk
      | succ k ih =>
        by_cases hk' : r ≤ adaptedCount A k ω
        · exact (ih hk').trans (adaptedCount_mono A'' ω k.le_succ)
        · have hklt := not_le.mp hk'
          rw [adaptedCount_succ] at hk
          have hmem : ω ∈ A k := by
            by_contra hnot
            simp only [Set.indicator_of_notMem hnot, add_zero] at hk
            exact hk' hk
          rw [adaptedCount_succ, heq_lt k hklt,
            Set.indicator_of_mem (show ω ∈ A'' k from ⟨hmem, hklt⟩)]
          simpa [Set.indicator_of_mem hmem] using hk
    rw [min_eq_right hreach, min_eq_right (hr_le n hreach)]
  · rw [heq_lt n (not_le.mp hreach)]

/-- Extending an `ℱ (t + 1)`-measurable event `E` by `Sᶜ` (`S` `ℱ t`-measurable) lifts an
a.e. conditional lower bound `p ≤ P[E | ℱ t]` on `P.restrict S` to all of `P`. -/
theorem ae_le_condExp_union_compl {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {t : ℕ}
    {E S : Set Ω} (hE : MeasurableSet[ℱ (t + 1)] E) (hS_ℱ : MeasurableSet[ℱ t] S) {p : I}
    (hp : (fun _ => (p : ℝ)) ≤ᵐ[P.restrict S] P[E.indicator (fun _ => (1 : ℝ)) | ℱ t]) :
    (fun _ => (p : ℝ)) ≤ᵐ[P] P[(E ∪ Sᶜ).indicator (fun _ => (1 : ℝ)) | ℱ t] := by
  have hS : MeasurableSet S := ℱ.le t _ hS_ℱ
  have hind_eq : (E ∪ Sᶜ).indicator (fun _ => (1 : ℝ)) =
      S.indicator (E.indicator (fun _ => 1)) + Sᶜ.indicator (fun _ => 1) := by
    ext ω
    by_cases hωS : ω ∈ S
    · by_cases hωE : ω ∈ E <;> simp [hωS, hωE]
    · simp [hωS]
  have hI_int : Integrable (E.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (ℱ.le (t + 1) _ hE)
  have hce : P[(E ∪ Sᶜ).indicator (fun _ => (1 : ℝ)) | ℱ t] =ᵐ[P]
      S.indicator (P[E.indicator (fun _ => (1 : ℝ)) | ℱ t]) + Sᶜ.indicator (fun _ => 1) := by
    rw [hind_eq]
    refine (condExp_add (hI_int.indicator hS)
      ((integrable_const 1).indicator hS.compl) (ℱ t)).trans ?_
    refine ((condExp_indicator hI_int hS_ℱ).add
      (condExp_indicator (integrable_const (1 : ℝ)) hS_ℱ.compl)).trans ?_
    rw [condExp_const (ℱ.le t) (1 : ℝ)]
  filter_upwards [hce, (ae_restrict_iff' hS).mp hp] with ω hω hSω
  rw [hω]
  by_cases hmem : ω ∈ S
  · simp [hmem, hSω hmem]
  · simp [hmem, p.property.2]

private theorem map_min_adaptedCount_eq {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    (ℱ : Filtration ℕ m) {A B : ℕ → Set Ω} (hB : ∀ t, MeasurableSet[ℱ (t + 1)] (B t))
    (n r : ℕ) (heq : ∀ ω, min (adaptedCount A n ω) r = min (adaptedCount B n ω) r) :
    (P.map (adaptedCount B n)).map (fun k => min k r) =
      P.map (fun ω => min (adaptedCount A n ω) r) := by
  have hm : Measurable (adaptedCount B n) := (measurable_adaptedCount ℱ hB n).mono (ℱ.le _) le_rfl
  rw [Measure.map_map measurable_from_top hm]
  congr 1
  ext ω
  exact (heq ω).symm

/-- **Active-before-target adapted domination (lower envelope)**: if `P[A t | ℱ t] ≥ ps[t]`
holds a.e. on the active event `{ω | adaptedCount A t ω < r}`, then the capped count
`min (adaptedCount A ps.length) r` dominates `min · r` of `PMF.poissonBinomial ps`. -/
theorem adaptedCount_min_stochasticallyDominates_poissonBinomial {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (ps : List I) (r : ℕ)
    (hp : ∀ t (ht : t < ps.length),
      (fun _ => (ps[t] : ℝ)) ≤ᵐ[P.restrict {ω | adaptedCount A t ω < r}]
        P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t]) :
    StochasticallyDominates (P.map fun ω => min (adaptedCount A ps.length ω) r)
      ((PMF.poissonBinomial ps).map fun k => min k r).toMeasure := by
  let A' : ℕ → Set Ω := fun t => A t ∪ ({ω | adaptedCount A t ω < r})ᶜ
  have hA'eq (t : ℕ) : A' t = A t ∪ {ω | r ≤ adaptedCount A t ω} := by
    ext ω
    simp [A', not_lt]
  have hA' : ∀ t, MeasurableSet[ℱ (t + 1)] (A' t) := fun t =>
    (hA t).union ((measurable_adaptedCount ℱ hA t).mono (ℱ.mono t.le_succ) le_rfl
      measurableSet_Iio).compl
  have hp' : ∀ t (ht : t < ps.length),
      (fun _ => (ps[t] : ℝ)) ≤ᵐ[P] P[(A' t).indicator (fun _ => (1 : ℝ)) | ℱ t] := fun t ht =>
    ae_le_condExp_union_compl ℱ (hA t) ((measurable_adaptedCount ℱ hA t) measurableSet_Iio)
      (hp t ht)
  have hdom' := adaptedCount_stochasticallyDominates_poissonBinomial ℱ hA' ps hp'
  have hmap := hdom'.map measurable_from_top (fun _ _ h => min_le_min_right r h)
  rw [map_min_adaptedCount_eq (A := A) ℱ hA' ps.length r (fun ω => by
      have heq := adaptedCount_min_eq_of_union A r ps.length ω
      simpa only [← hA'eq] using heq),
    PMF.toMeasure_map _ _ measurable_from_top] at hmap
  exact hmap

/-- **Active-before-target binomial tail bound**: if `P[A t | ℱ t] ≥ p` a.e. on
`{adaptedCount A t < r}` for every `t < n`, then
`P.real {ω | adaptedCount A n ω < r} ≤ (binomial n p).real (Set.Iio r)`. -/
theorem adaptedCount_real_Iio_le_binomial {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (n r : ℕ) (p : I)
    (hp : ∀ t, t < n →
      (fun _ => (p : ℝ)) ≤ᵐ[P.restrict {ω | adaptedCount A t ω < r}]
        P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t]) :
    P.real {ω | adaptedCount A n ω < r} ≤ (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
  let ps := List.replicate n p
  have hdom := adaptedCount_min_stochasticallyDominates_poissonBinomial ℱ hA ps r fun t ht => by
    simpa [ps] using hp t (by simpa [ps] using ht)
  rw [List.length_replicate] at hdom
  have hm_min : Measurable (fun ω => min (adaptedCount A n ω) r) :=
    (measurable_from_top : Measurable fun k => min k r).comp
      ((measurable_adaptedCount ℱ hA n).mono (ℱ.le _) le_rfl)
  have hle := hdom.le_real_Iio r
  have hL : (P.map fun ω => min (adaptedCount A n ω) r).real (Set.Iio r) =
      P.real {ω | adaptedCount A n ω < r} := by
    rw [measureReal_def, Measure.map_apply hm_min measurableSet_Iio, ← measureReal_def]
    congr 1; ext ω; simp [min_lt_iff]
  have hR : ((PMF.poissonBinomial ps).map fun k => min k r).toMeasure.real (Set.Iio r) =
      (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
    rw [measureReal_def, ← PMF.toMeasure_map (fun k => min k r) _ measurable_from_top,
      Measure.map_apply measurable_from_top measurableSet_Iio,
      show (fun k => min k r) ⁻¹' Set.Iio r = Set.Iio r from by ext k; simp [min_lt_iff],
      PMF.toMeasure_poissonBinomial_replicate, ← measureReal_def]
  rwa [hL, hR] at hle

/-- **Active-before-target adapted domination (upper envelope)**: if `P[A t | ℱ t] ≤ ps[t]` a.e.
on `{ω | adaptedCount A t ω < r}`, then `min · r` of `PMF.poissonBinomial ps` stochastically
dominates `min (adaptedCount A ps.length) r`. -/
theorem poissonBinomial_stochasticallyDominates_adaptedCount_min {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (ps : List I) (r : ℕ)
    (hp : ∀ t (ht : t < ps.length),
      P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P.restrict {ω | adaptedCount A t ω < r}]
        fun _ => (ps[t] : ℝ)) :
    StochasticallyDominates ((PMF.poissonBinomial ps).map fun k => min k r).toMeasure
      (P.map fun ω => min (adaptedCount A ps.length ω) r) := by
  let A'' : ℕ → Set Ω := fun t => A t ∩ {ω | adaptedCount A t ω < r}
  have hA'' : ∀ t, MeasurableSet[ℱ (t + 1)] (A'' t) := fun t =>
    (hA t).inter ((measurable_adaptedCount ℱ hA t).mono (ℱ.mono t.le_succ) le_rfl measurableSet_Iio)
  have hp'' : ∀ t (ht : t < ps.length),
      P[(A'' t).indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P] fun _ => (ps[t] : ℝ) := by
    intro t ht
    let S : Set Ω := {ω | adaptedCount A t ω < r}
    have hSm_ℱ : MeasurableSet[ℱ t] S := (measurable_adaptedCount ℱ hA t) measurableSet_Iio
    have hind_eq : (A'' t).indicator (fun _ => (1 : ℝ)) =
        S.indicator ((A t).indicator (fun _ => 1)) := by
      ext ω; by_cases hS : ω ∈ S <;> by_cases hAt : ω ∈ A t <;> simp [A'', S, hS, hAt]
    have hce : P[(A'' t).indicator (fun _ => (1 : ℝ)) | ℱ t] =ᵐ[P]
        S.indicator (P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t]) := by
      rw [hind_eq]
      exact condExp_indicator ((integrable_const (1 : ℝ)).indicator (ℱ.le (t + 1) _ (hA t))) hSm_ℱ
    filter_upwards [hce, (ae_restrict_iff' (ℱ.le t _ hSm_ℱ)).mp (hp t ht)] with ω hω hSω
    rw [hω]
    by_cases hmem : ω ∈ S
    · simpa [hmem] using hSω hmem
    · simp [hmem, (ps[t]).property.1]
  have hmap := (poissonBinomial_stochasticallyDominates_adaptedCount ℱ hA'' ps hp'').map
    measurable_from_top (fun _ _ h => min_le_min_right r h)
  rwa [map_min_adaptedCount_eq ℱ hA'' ps.length r (adaptedCount_min_eq_of_inter A r ps.length),
    PMF.toMeasure_map _ _ measurable_from_top] at hmap

end FiltrationComparison

section KernelTraj

/-- Shift a `ℕ`-indexed filtration forward by `a` steps. -/
@[expose]
def shiftFiltration {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℕ m) (a : ℕ) :
    Filtration ℕ m where
  seq t := ℱ (a + t)
  mono' _ _ hij := ℱ.mono (Nat.add_le_add_left hij a)
  le' t := ℱ.le (a + t)

@[simp]
theorem shiftFiltration_apply {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℕ m)
    (a t : ℕ) :
    shiftFiltration ℱ a t = ℱ (a + t) :=
  rfl

/-- Conditional expectation of a measurable event indicator under `Kernel.traj κ a x₀` at time
`b ≥ a` equals the `Kernel.traj κ b` real probability at `Preorder.frestrictLe b x`. -/
theorem traj_condExp_indicator_eq
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {a b : ℕ} (hab : a ≤ b) (x₀ : Π i : Finset.Iic a, X i)
    {E : Set (Π n, X n)} (hE : MeasurableSet E) :
    (Kernel.traj κ a x₀)[E.indicator (fun _ => (1 : ℝ)) | Filtration.piLE b] =ᵐ[
        Kernel.traj κ a x₀]
      fun x => (Kernel.traj κ b (Preorder.frestrictLe b x)).real E := by
  have hint : Integrable (E.indicator (1 : (Π n, X n) → ℝ)) (Kernel.traj κ a x₀) :=
    (integrable_const 1).indicator hE
  have htraj := Kernel.condExp_traj (κ := κ) (a := a) (b := b) hab (x₀ := x₀) hint
  filter_upwards [htraj] with x hx
  rw [integral_indicator_one hE] at hx
  exact hx

private theorem hA_shiftFiltration {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    {a : ℕ} {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (a + t + 1)] (A t)) :
    ∀ t, MeasurableSet[shiftFiltration Filtration.piLE a (t + 1)] (A t) := fun t => by
  change MeasurableSet[Filtration.piLE (a + (t + 1))] (A t)
  rw [← add_assoc]
  exact hA t

/-- Specialization of `adaptedCount_stochasticallyDominates_poissonBinomial` to Ionescu-Tulcea
trajectories `ProbabilityTheory.Kernel.traj κ a x₀`. -/
theorem traj_adaptedCount_stochasticallyDominates_poissonBinomial
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {a : ℕ} (x₀ : Π i : Finset.Iic a, X i)
    {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (a + t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length), ∀ᵐ x ∂Kernel.traj κ a x₀,
      (ps[t] : ℝ) ≤ (Kernel.traj κ (a + t) (Preorder.frestrictLe (a + t) x)).real (A t)) :
    StochasticallyDominates ((Kernel.traj κ a x₀).map (adaptedCount A ps.length))
      (PMF.poissonBinomial ps).toMeasure := by
  refine adaptedCount_stochasticallyDominates_poissonBinomial
    (shiftFiltration Filtration.piLE a) (hA_shiftFiltration hA) ps ?_
  intro t ht
  have hce := traj_condExp_indicator_eq κ (Nat.le_add_right a t) x₀
    (Filtration.piLE.le (a + t + 1) _ (hA t))
  filter_upwards [hce, hp t ht] with x hx hpx
  exact hpx.trans_eq hx.symm

/-- Upper-envelope specialization of `poissonBinomial_stochasticallyDominates_adaptedCount` to
`ProbabilityTheory.Kernel.traj κ a x₀`. -/
theorem poissonBinomial_stochasticallyDominates_traj_adaptedCount
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {a : ℕ} (x₀ : Π i : Finset.Iic a, X i)
    {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (a + t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length), ∀ᵐ x ∂Kernel.traj κ a x₀,
      (Kernel.traj κ (a + t) (Preorder.frestrictLe (a + t) x)).real (A t) ≤ (ps[t] : ℝ)) :
    StochasticallyDominates (PMF.poissonBinomial ps).toMeasure
      ((Kernel.traj κ a x₀).map (adaptedCount A ps.length)) := by
  refine poissonBinomial_stochasticallyDominates_adaptedCount
    (shiftFiltration Filtration.piLE a) (hA_shiftFiltration hA) ps ?_
  intro t ht
  have hce := traj_condExp_indicator_eq κ (Nat.le_add_right a t) x₀
    (Filtration.piLE.le (a + t + 1) _ (hA t))
  filter_upwards [hce, hp t ht] with x hx hpx
  exact hx.trans_le hpx

private theorem measurable_traj_real {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (t + 1)] (A t)) (t : ℕ) :
    Measurable fun x => (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A t) :=
  ENNReal.measurable_toReal.comp
    ((Kernel.measurable_coe _ (Filtration.piLE.le (t + 1) _ (hA t))).comp
      (Preorder.measurable_frestrictLe t))

private noncomputable abbrev trajInitMeasure {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0)) : Measure (Π i : Finset.Iic 0, X i) :=
  μ₀.map (MeasurableEquiv.piUnique fun i : Finset.Iic 0 => X i).symm

private instance trajInitMeasure_isProbability {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (trajInitMeasure μ₀) :=
  ⟨by
    rw [trajInitMeasure, Measure.map_apply (MeasurableEquiv.measurable _) MeasurableSet.univ,
      Set.preimage_univ, measure_univ]⟩

private theorem trajMeasure_ae_traj {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0))
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) {Q : (t : ℕ) → t < n → (Π n, X n) → Prop}
    (hQm : ∀ t (ht : t < n), MeasurableSet {x | ¬ Q t ht x})
    (hq : ∀ t (ht : t < n), ∀ᵐ x ∂Kernel.trajMeasure μ₀ κ, Q t ht x) :
    ∀ᵐ x₀ ∂trajInitMeasure μ₀,
      ∀ t (ht : t < n), ∀ᵐ x ∂Kernel.traj κ 0 x₀, Q t ht x := by
  rw [ae_all_iff]
  intro t
  rw [ae_all_iff]
  intro ht
  have hzero : (Kernel.trajMeasure μ₀ κ) {x | ¬ Q t ht x} = 0 := ae_iff.mp (hq t ht)
  change ((Kernel.traj κ 0) ∘ₘ trajInitMeasure μ₀) {x | ¬ Q t ht x} = 0 at hzero
  rw [Measure.bind_apply (hQm t ht) (Kernel.traj κ 0).measurable.aemeasurable,
    lintegral_eq_zero_iff (Kernel.measurable_coe (Kernel.traj κ 0) (hQm t ht))] at hzero
  filter_upwards [hzero] with x₀ hx₀
  exact ae_iff.mpr hx₀

private theorem trajMeasure_map_apply {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0))
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {f : (Π n, X n) → ℕ} (hf : Measurable f)
    {U : Set ℕ} (hU : MeasurableSet U) :
    ((Kernel.trajMeasure μ₀ κ).map f) U =
      ∫⁻ x₀, ((Kernel.traj κ 0 x₀).map f) U ∂trajInitMeasure μ₀ := by
  rw [Measure.map_apply hf hU]
  have hbind : (Kernel.trajMeasure μ₀ κ) (f ⁻¹' U) =
      ∫⁻ x₀, (Kernel.traj κ 0 x₀) (f ⁻¹' U) ∂trajInitMeasure μ₀ := by
    change ((Kernel.traj κ 0) ∘ₘ trajInitMeasure μ₀) (f ⁻¹' U) = _
    exact Measure.bind_apply (hf hU) (Kernel.traj κ 0).measurable.aemeasurable
  rw [hbind]
  exact lintegral_congr fun x₀ => (Measure.map_apply hf hU).symm

/-- Specialization of `adaptedCount_stochasticallyDominates_poissonBinomial` to
`ProbabilityTheory.Kernel.trajMeasure μ₀ κ` for events measurable at step `t + 1`. -/
theorem trajMeasure_adaptedCount_stochasticallyDominates_poissonBinomial
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)]
    {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length), ∀ᵐ x ∂Kernel.trajMeasure μ₀ κ,
      (ps[t] : ℝ) ≤ (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A t)) :
    StochasticallyDominates ((Kernel.trajMeasure μ₀ κ).map (adaptedCount A ps.length))
      (PMF.poissonBinomial ps).toMeasure := by
  have hm : Measurable (adaptedCount A ps.length) :=
    (measurable_adaptedCount Filtration.piLE hA ps.length).mono (Filtration.piLE.le _) le_rfl
  have hae_x₀ := trajMeasure_ae_traj μ₀ κ ps.length
    (fun t _ => (measurableSet_le measurable_const (measurable_traj_real κ hA t)).compl) hp
  intro U hUm hU
  rw [trajMeasure_map_apply μ₀ κ hm hUm]
  calc
    (PMF.poissonBinomial ps).toMeasure U
      = ∫⁻ _ : Π i : Finset.Iic 0, X i,
          (PMF.poissonBinomial ps).toMeasure U ∂trajInitMeasure μ₀ := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ x₀, ((Kernel.traj κ 0 x₀).map (adaptedCount A ps.length)) U ∂trajInitMeasure μ₀ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae_x₀] with x₀ hx₀
        refine (adaptedCount_stochasticallyDominates_poissonBinomial Filtration.piLE hA ps
          fun t ht => ?_) U hUm hU
        have hce := traj_condExp_indicator_eq κ (Nat.zero_le t) x₀
          (Filtration.piLE.le (t + 1) _ (hA t))
        filter_upwards [hce, hx₀ t ht] with x hx hpx
        exact hpx.trans_eq hx.symm

/-- Upper-envelope specialization of `poissonBinomial_stochasticallyDominates_adaptedCount` to
`ProbabilityTheory.Kernel.trajMeasure μ₀ κ` for events measurable at step `t + 1`. -/
theorem poissonBinomial_stochasticallyDominates_trajMeasure_adaptedCount
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)]
    {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length), ∀ᵐ x ∂Kernel.trajMeasure μ₀ κ,
      (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A t) ≤ (ps[t] : ℝ)) :
    StochasticallyDominates (PMF.poissonBinomial ps).toMeasure
      ((Kernel.trajMeasure μ₀ κ).map (adaptedCount A ps.length)) := by
  have hm : Measurable (adaptedCount A ps.length) :=
    (measurable_adaptedCount Filtration.piLE hA ps.length).mono (Filtration.piLE.le _) le_rfl
  have hae_x₀ := trajMeasure_ae_traj μ₀ κ ps.length
    (fun t _ => (measurableSet_le (measurable_traj_real κ hA t) measurable_const).compl) hp
  intro U hUm hU
  rw [trajMeasure_map_apply μ₀ κ hm hUm]
  calc
    ∫⁻ x₀, ((Kernel.traj κ 0 x₀).map (adaptedCount A ps.length)) U ∂trajInitMeasure μ₀
      ≤ ∫⁻ _ : Π i : Finset.Iic 0, X i,
          (PMF.poissonBinomial ps).toMeasure U ∂trajInitMeasure μ₀ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae_x₀] with x₀ hx₀
        refine (poissonBinomial_stochasticallyDominates_adaptedCount Filtration.piLE hA ps
          fun t ht => ?_) U hUm hU
        have hce := traj_condExp_indicator_eq κ (Nat.zero_le t) x₀
          (Filtration.piLE.le (t + 1) _ (hA t))
        filter_upwards [hce, hx₀ t ht] with x hx hpx
        exact hx.trans_le hpx
    _ = (PMF.poissonBinomial ps).toMeasure U := by
        rw [lintegral_const, measure_univ, mul_one]

end KernelTraj

end Cslib.Probability

namespace Cslib.Probability.PMF

open MeasureTheory
open scoped BigOperators ENNReal unitInterval

/-- Cumulative number of successes along a history `h : Fin n → α` for predicates
`E t : (Fin t → α) → Set α`. -/
@[expose]
noncomputable def seqCount {α : Type*} (E : ∀ t : ℕ, (Fin t → α) → Set α) (n : ℕ)
    (h : Fin n → α) : ℕ := by
  classical
  exact ∑ t : Fin n,
    if h t ∈ E t.val (fun j : Fin t.val => h (Fin.castLT j (lt_trans j.isLt t.isLt))) then 1 else 0

@[simp]
theorem seqCount_zero {α : Type*} (E : ∀ t : ℕ, (Fin t → α) → Set α) (h : Fin 0 → α) :
    seqCount E 0 h = 0 := by
  simp [seqCount]

private theorem snoc_castLT {α : Type*} {n : ℕ} (h : Fin n → α) (a : α)
    (k : ℕ) (hk : k < n) (hk' : k < n + 1) :
    Fin.snoc (α := fun _ => α) h a ⟨k, hk'⟩ = h ⟨k, hk⟩ := by
  simp [Fin.snoc, hk]

theorem seqCount_snoc {α : Type*} (E : ∀ t : ℕ, (Fin t → α) → Set α) (n : ℕ)
    (h : Fin n → α) (a : α) :
    seqCount E (n + 1) (Fin.snoc h a) =
      seqCount E n h + by classical exact if a ∈ E n h then 1 else 0 := by
  classical
  simp only [seqCount, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc,
    Fin.snoc_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    exact congrArg (fun p => if h t ∈ E t.val p then 1 else 0)
      (funext fun j => snoc_castLT h a j.val (lt_trans j.isLt t.isLt) _)
  · exact congrArg (fun p => if a ∈ E n p then 1 else 0)
      (funext fun j => snoc_castLT h a j.val j.isLt _)

private theorem abs_tsum_pmf_mul_le_one {α : Type*} (p : PMF α) (F : α → ℝ)
    (hF : ∀ a, |F a| ≤ 1) :
    |∑' a, (p a).toReal * F a| ≤ 1 := by
  have hs : Summable fun a => (p a).toReal * F a :=
    summable_toReal_mul_of_abs_le p F fun a _ => hF a
  calc |∑' a, (p a).toReal * F a| ≤ ∑' a, |(p a).toReal * F a| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' a, (p a).toReal := hs.abs.tsum_le_tsum (fun a => by
        calc |(p a).toReal * F a|
            = (p a).toReal * |F a| := by rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          _ ≤ (p a).toReal := mul_le_of_le_one_right ENNReal.toReal_nonneg (hF a))
        (PMF.summable_toReal p)
    _ = 1 := PMF.tsum_toReal p

private theorem tsum_indicator_pmf_toReal {α : Type*} (p : _root_.PMF α) (s : Set α) :
    (∑' a : α, s.indicator (fun a => (p a).toReal) a) = (p.toOuterMeasure s).toReal := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq fun a => by
    by_cases ha : a ∈ s <;> simp [ha, PMF.apply_ne_top]]
  exact tsum_congr fun a => by by_cases ha : a ∈ s <;> simp [ha]

private theorem seqCount_stochasticallyDominates_poissonBinomial_of_length {α : Type*}
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (E : ∀ t : ℕ, (Fin t → α) → Set α)
    (n : ℕ) (ps : List I) (hlen : ps.length = n)
    (hp : ∀ t (ht : t < ps.length) (h : Fin t → α),
      (ps[t] : ℝ) ≤ ((step t h).toOuterMeasure (E t h)).toReal) :
    StochasticallyDominates ((seqProcess step n).map (seqCount E n))
      (poissonBinomial ps) := by
  subst hlen
  rw [stochasticallyDominates_nat_iff_Ici]
  intro r
  rw [← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top (poissonBinomial ps) (Set.Ici r)),
    ← ENNReal.ofReal_toReal
      (PMF.toOuterMeasure_ne_top ((seqProcess step ps.length).map (seqCount E ps.length))
        (Set.Ici r))]
  refine ENNReal.ofReal_le_ofReal ?_
  let f : ℕ → ℝ := (Set.Ici r).indicator (fun _ => 1)
  have hf_mono : Monotone f := Cslib.Probability.monotone_indicator_Ici r
  have hC : ∀ j, |f j| ≤ 1 := Cslib.Probability.abs_indicator_Ici_le_one r
  have hchain (k : ℕ) (hk : k ≤ ps.length) :
      Cslib.Probability.pbValue ps f 0 0 ≤
        ∑' h : Fin k → α,
          ((seqProcess step k) h).toReal * Cslib.Probability.pbValue ps f k (seqCount E k h) := by
    induction k with
    | zero =>
      rw [tsum_eq_single (Fin.elim0 : Fin 0 → α) fun g hg =>
        absurd (Subsingleton.elim g _) hg]
      simp [seqProcess, Cslib.Probability.pbValue]
    | succ k ih =>
      refine (ih (Nat.le_of_succ_le hk)).trans ?_
      rw [tsum_toReal_seqProcess_step step k _ fun h =>
        Cslib.Probability.pbValue_abs_le hC (k + 1) _]
      refine Summable.tsum_le_tsum (fun h => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
        (summable_toReal_mul_of_abs_le _ _ fun h _ =>
          Cslib.Probability.pbValue_abs_le (ps := ps) hC k _)
        (summable_toReal_mul_of_abs_le (C := 1) _ _ fun _ _ =>
          abs_tsum_pmf_mul_le_one (step k _) _ fun _ =>
            Cslib.Probability.pbValue_abs_le (ps := ps) hC (k + 1) _)
      let D : ℝ :=
        Cslib.Probability.pbValue ps f (k + 1) (seqCount E k h + 1) -
          Cslib.Probability.pbValue ps f (k + 1) (seqCount E k h)
      have hD_nn : 0 ≤ D :=
        sub_nonneg.mpr (Cslib.Probability.pbValue_mono hf_mono (k + 1) (Nat.le_succ _))
      have hinner : ∑' a : α, ((step k h) a).toReal *
            Cslib.Probability.pbValue ps f (k + 1) (seqCount E (k + 1) (Fin.snoc h a)) =
          Cslib.Probability.pbValue ps f (k + 1) (seqCount E k h) +
            ((step k h).toOuterMeasure (E k h)).toReal * D := by
        classical
        have heq (a : α) : ((step k h) a).toReal *
              Cslib.Probability.pbValue ps f (k + 1) (seqCount E (k + 1) (Fin.snoc h a)) =
            ((step k h) a).toReal * Cslib.Probability.pbValue ps f (k + 1) (seqCount E k h) +
              (E k h).indicator (fun a => ((step k h) a).toReal) a * D := by
          rw [seqCount_snoc]
          by_cases ha : a ∈ E k h <;> simp [D, ha]; ring
        simp_rw [heq]
        rw [((PMF.summable_toReal _).mul_right _).tsum_add
            (((PMF.summable_toReal (step k h)).indicator (E k h)).mul_right D),
          tsum_mul_right, PMF.tsum_toReal, one_mul, tsum_mul_right, tsum_indicator_pmf_toReal]
      rw [Cslib.Probability.pbValue_step ps f hk (seqCount E k h), hinner]
      exact add_le_add_right (mul_le_mul_of_nonneg_right (hp k hk h) hD_nn) _
  have hmain := hchain ps.length le_rfl
  have hlhs : Cslib.Probability.pbValue ps f 0 0 =
      ((poissonBinomial ps).toOuterMeasure (Set.Ici r)).toReal := by
    rw [Cslib.Probability.pbValue_zero_Ici_eq_real ps r, measureReal_def,
      PMF.toMeasure_apply_eq_toOuterMeasure_apply _ measurableSet_Ici]
  have hrhs : (∑' h : Fin ps.length → α,
        ((seqProcess step ps.length) h).toReal *
          Cslib.Probability.pbValue ps f ps.length (seqCount E ps.length h)) =
      (((seqProcess step ps.length).map (seqCount E ps.length)).toOuterMeasure
        (Set.Ici r)).toReal := by
    simp_rw [Cslib.Probability.pbValue_length]
    rw [PMF.toOuterMeasure_map_apply, ← tsum_indicator_pmf_toReal]
    refine tsum_congr fun h => by by_cases hh : r ≤ seqCount E ps.length h <;> simp [f, hh]
  rwa [← hlhs, ← hrhs]

/-- **Sequential finite-horizon Poisson-binomial domination**: if at every step `t < ps.length` and
every prefix `h`, the conditional event probability `((step t h).toOuterMeasure (E t h)).toReal` is
at least `ps[t]`, then `seqCount E ps.length` under `seqProcess step ps.length` stochastically
dominates `poissonBinomial ps`. -/
theorem seqCount_stochasticallyDominates_poissonBinomial {α : Type*}
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (E : ∀ t : ℕ, (Fin t → α) → Set α) (ps : List I)
    (hp : ∀ t (ht : t < ps.length) (h : Fin t → α),
      (ps[t] : ℝ) ≤ ((step t h).toOuterMeasure (E t h)).toReal) :
    StochasticallyDominates ((seqProcess step ps.length).map (seqCount E ps.length))
      (poissonBinomial ps) :=
  seqCount_stochasticallyDominates_poissonBinomial_of_length step E ps.length ps rfl hp

/-- **Active-before-target sequential `PMF` bound**: if `((step t h).toOuterMeasure (E t h)).toReal`
is at least `p` whenever `t < n` and `seqCount E t h < r`, then the probability of strictly fewer
than `r` successes after `n` steps is at most
`(ProbabilityTheory.binomial n p).real (Set.Iio r)`. -/
theorem seqCount_active_toReal_Iio_le {α : Type*}
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (E : ∀ t : ℕ, (Fin t → α) → Set α)
    (n r : ℕ) (p : I)
    (hp : ∀ t, t < n → ∀ h : Fin t → α,
      seqCount E t h < r → (p : ℝ) ≤ ((step t h).toOuterMeasure (E t h)).toReal) :
    (((seqProcess step n).map (seqCount E n)).toOuterMeasure (Set.Iio r)).toReal ≤
      (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
  let E' : ∀ t : ℕ, (Fin t → α) → Set α :=
    fun t h => if r ≤ seqCount E t h then Set.univ else E t h
  let ps := List.replicate n p
  have hp' : ∀ t (ht : t < ps.length) (h : Fin t → α),
      (ps[t] : ℝ) ≤ ((step t h).toOuterMeasure (E' t h)).toReal := by
    intro t ht h
    by_cases hreach : r ≤ seqCount E t h
    · have huniv : (step t h).toOuterMeasure Set.univ = 1 := by
        let _ : MeasurableSpace α := ⊤
        rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply (step t h) MeasurableSet.univ,
          measure_univ]
      simpa [ps, E', hreach, huniv] using p.property.2
    · simpa [ps, E', hreach] using hp t (by simpa [ps] using ht) h (not_le.mp hreach)
  have hIio := ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top (poissonBinomial ps) (Set.Iio r))
    ((seqCount_stochasticallyDominates_poissonBinomial_of_length step E' n ps
      List.length_replicate hp').le_Iio r)
  have hle_count (k : ℕ) (h₀ : Fin k → α) : seqCount E k h₀ ≤ seqCount E' k h₀ := by
    classical
    refine Finset.sum_le_sum fun t _ => ?_
    dsimp only [E']; split_ifs <;> simp_all
  have hlt_eq (k : ℕ) (h₀ : Fin k → α) (hlt : seqCount E k h₀ < r) :
      seqCount E' k h₀ = seqCount E k h₀ := by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨hprev, a, rfl⟩ : ∃ hprev a, h₀ = Fin.snoc hprev a :=
        ⟨Fin.init h₀, h₀ (Fin.last k), (Fin.snoc_init_self h₀).symm⟩
      classical
      rw [seqCount_snoc] at hlt
      have hk_lt : seqCount E k hprev < r := lt_of_le_of_lt (Nat.le_add_right _ _) hlt
      rw [seqCount_snoc, seqCount_snoc, ih hprev hk_lt]
      simp [E', not_le.mpr hk_lt]
  have hL : ((seqProcess step n).map (seqCount E n)).toOuterMeasure (Set.Iio r) =
      ((seqProcess step n).map (seqCount E' n)).toOuterMeasure (Set.Iio r) := by
    simp only [PMF.toOuterMeasure_map_apply]
    congr 1; ext h
    simp only [Set.mem_preimage, Set.mem_Iio]
    refine ⟨fun hlt => (hlt_eq n h hlt).symm ▸ hlt, fun hlt => ?_⟩
    exact (hle_count n h).trans_lt hlt
  have hR : ((poissonBinomial ps).toOuterMeasure (Set.Iio r)).toReal =
      (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
    rw [← PMF.toMeasure_poissonBinomial_replicate n p, measureReal_def,
      PMF.toMeasure_apply_eq_toOuterMeasure_apply _ measurableSet_Iio]
  rwa [← hL, hR] at hIio

private theorem tsum_seqCount_sub_step {α : Type*} (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (p : ℕ → ℝ) (k : ℕ) (h : Fin k → α) :
    ∑' x : α, ((step k h) x).toReal *
        ((seqCount E (k + 1) (Fin.snoc h x) : ℝ) - ∑ t ∈ Finset.range (k + 1), p t) =
      ((seqCount E k h : ℝ) - ∑ t ∈ Finset.range k, p t) - p k +
        ((step k h).toOuterMeasure (E k h)).toReal := by
  classical
  have heq (x : α) :
      ((step k h) x).toReal *
          ((seqCount E (k + 1) (Fin.snoc h x) : ℝ) - ∑ t ∈ Finset.range (k + 1), p t) =
        ((step k h) x).toReal * (((seqCount E k h : ℝ) - ∑ t ∈ Finset.range k, p t) - p k) +
          (E k h).indicator (fun a => ((step k h) a).toReal) x := by
    rw [seqCount_snoc, Finset.sum_range_succ]
    by_cases hx : x ∈ E k h
    · simp only [hx, ↓reduceIte, Set.indicator_of_mem hx, Nat.cast_add, Nat.cast_one]
      ring
    · simp only [hx, ↓reduceIte, Set.indicator_of_notMem hx, add_zero]
      ring
  simp_rw [heq]
  rw [((PMF.summable_toReal (step k h)).mul_right _).tsum_add
      ((PMF.summable_toReal (step k h)).indicator (E k h)),
    tsum_mul_right, PMF.tsum_toReal, one_mul, tsum_indicator_pmf_toReal]

private theorem seqCount_sub_step_range {α : Type*}
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (p : ℕ → ℝ) (k : ℕ) (h : Fin k → α) :
    ∃ a b : ℝ, b - a ≤ 1 ∧ ∀ x : α,
      (seqCount E (k + 1) (Fin.snoc h x) : ℝ) - ∑ t ∈ Finset.range (k + 1), p t ∈ Set.Icc a b := by
  classical
  refine ⟨(seqCount E k h : ℝ) - ∑ t ∈ Finset.range (k + 1), p t,
    (seqCount E k h : ℝ) + 1 - ∑ t ∈ Finset.range (k + 1), p t, by linarith, fun x => ?_⟩
  rw [seqCount_snoc]
  split_ifs <;> push_cast <;> exact ⟨by linarith, by linarith⟩

/-- **Azuma–Hoeffding upper tail for sequential event counts**: if at every step `t < n` and
supported prefix `h`, the conditional probability of `E t h` is at most `p t`, then `seqCount E n`
exceeds `∑ t < n, p t + ε` (`ε ≥ 0`) with probability at most `exp (-2 ε² / n)`. -/
theorem seqCount_ge_le {α : Type*} (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (p : ℕ → ℝ) (n : ℕ)
    (hp : ∀ t, t < n → ∀ h ∈ (seqProcess step t).support,
      ((step t h).toOuterMeasure (E t h)).toReal ≤ p t)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ((seqProcess step n).toOuterMeasure
      {h | (∑ t ∈ Finset.range n, p t) + ε ≤ (seqCount E n h : ℝ)}).toReal ≤
      Real.exp (-2 * ε ^ 2 / n) := by
  let X : ∀ k : ℕ, (Fin k → α) → ℝ :=
    fun k h => (seqCount E k h : ℝ) - ∑ t ∈ Finset.range k, p t
  have hset : {h : Fin n → α | (∑ t ∈ Finset.range n, p t) + ε ≤ (seqCount E n h : ℝ)} =
      {h : Fin n → α | X 0 Fin.elim0 + ε ≤ X n h} := by
    ext h
    simp only [Set.mem_ofPred_eq, X, seqCount_zero, Nat.cast_zero, Finset.sum_range_zero, sub_zero,
      zero_add]
    exact ⟨fun hh => by linarith, fun hh => by linarith⟩
  rw [hset]
  refine (seqProcess_ge_le step X (fun _ => 1) n (fun k hk h hh => ?_)
    (fun k _ h _ => ?_) hε).trans_eq ?_
  · rw [tsum_seqCount_sub_step]
    linarith [hp k hk h hh]
  · obtain ⟨a, b, hab, hg⟩ := seqCount_sub_step_range E p k h
    exact ⟨a, b, hab, fun x _ => hg x⟩
  · simp

/-- **Azuma–Hoeffding lower tail for sequential event counts**: if at every step `t < n` and
supported prefix `h`, the conditional probability of `E t h` is at least `p t`, then `seqCount E n`
falls at or below `∑ t < n, p t - ε` (`ε ≥ 0`) with probability at most `exp (-2 ε² / n)`. -/
theorem seqCount_le_le {α : Type*} (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (p : ℕ → ℝ) (n : ℕ)
    (hp : ∀ t, t < n → ∀ h ∈ (seqProcess step t).support,
      p t ≤ ((step t h).toOuterMeasure (E t h)).toReal)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ((seqProcess step n).toOuterMeasure
      {h | (seqCount E n h : ℝ) ≤ (∑ t ∈ Finset.range n, p t) - ε}).toReal ≤
      Real.exp (-2 * ε ^ 2 / n) := by
  let X : ∀ k : ℕ, (Fin k → α) → ℝ :=
    fun k h => (seqCount E k h : ℝ) - ∑ t ∈ Finset.range k, p t
  have hset : {h : Fin n → α | (seqCount E n h : ℝ) ≤ (∑ t ∈ Finset.range n, p t) - ε} =
      {h : Fin n → α | X n h ≤ X 0 Fin.elim0 - ε} := by
    ext h
    simp only [Set.mem_ofPred_eq, X, seqCount_zero, Nat.cast_zero, Finset.sum_range_zero, sub_zero,
      zero_sub]
    exact ⟨fun hh => by linarith, fun hh => by linarith⟩
  rw [hset]
  refine (seqProcess_le_le step X (fun _ => 1) n (fun k hk h hh => ?_)
    (fun k _ h _ => ?_) hε).trans_eq ?_
  · rw [tsum_seqCount_sub_step]
    linarith [hp k hk h hh]
  · obtain ⟨a, b, hab, hg⟩ := seqCount_sub_step_range E p k h
    exact ⟨a, b, hab, fun x _ => hg x⟩
  · simp

end Cslib.Probability.PMF
