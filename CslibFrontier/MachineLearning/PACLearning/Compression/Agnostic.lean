/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Compression.Basic
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Foundations.Data.Nat.Choose.Sum
import CslibFrontier.MachineLearning.PACLearning.UniformConvergence
import CslibFrontier.Probability.Chernoff
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.Product.MapMeasure

/-!
# Agnostic sample compression generalization bounds

`CslibFrontier/MachineLearning/PACLearning/Compression/Basic.lean` proves the realizable sample
compression bound `(m + 1) ^ k (1 - ε) ^ (m - k)` for schemes that achieve zero empirical error on
every realizable sample. Here we drop the realizability and zero-error requirements and treat
*general* (agnostic) sample compression schemes (`GeneralCompressionScheme α β k`) of size `k` over
an arbitrary distribution `D` on `α × β` [LittlestoneWarmuth1986; FloydWarmuth1995;
ShalevShwartzBenDavid2014, Theorem 30.2] (locators unverified).

For each sample `S : LabeledSample α β m`, let `I = κ.compress S` (`I.length ≤ k`), let
`J = I.toFinset` be the set of distinct kept indices (`|J| ≤ k`), and let `h_S = κ.learner S` be
the hypothesis reconstructed from `I.map S`. Conditioning on the examples in `J`, the remaining
`|Jᶜ| = m - |J| ≥ m - k` examples are independent draws from `D`, so the held-out error
`heldOutError J h_S S` is an empirical average of independent `Bernoulli(error D h_S)` trials.

We establish two generalization bounds via a single union bound over the at most `(m + 1) ^ k`
index lists `Fin j → Fin m` (`j ≤ k`):

1. **Two-sided Hoeffding bound** (`GeneralCompressionScheme.measure_pi_abs_sub_heldOutError_le`
   and `measure_pi_hoeffding_gt_le`): for every `m > k` and `δ ∈ (0, 1]`, with probability at least
   `1 - δ` over `S ~ D ^ m`,
   `|heldOutError (keptSet S) (learner S) S - (error D (learner S)).toReal| ≤
      √((k log (m + 1) + log (2 / δ)) / (2 (m - k)))`.
2. **Multiplicative-Chernoff / Bernstein fast-rate bound**
   (`GeneralCompressionScheme.measure_pi_bernstein_gt_le` and
   `GeneralCompressionScheme.measure_pi_fastRate_gt_le`):
   via the lower-tail multiplicative Chernoff bound (`Cslib.Probability.PMF.pi_sum_le_one_sub_mul`),
   for `c = (k log (m + 1) + log (1 / δ)) / (m - k)` and `m > k`, with probability at least `1 - δ`,
   `error D h_S ≤ q + c + √(c² + 2 q c) ≤ q + √(2 c q) + 2 c`, where `q = heldOutError J h_S S`.
   This improves the constants `(4, 8)` of [ShalevShwartzBenDavid2014, Theorem 30.2] to `(1, 2)`
   and avoids the hypothesis `m ≥ 2 k` (requiring only `k < m`). When `q = 0`, it smoothly yields
   the fast rate `2 c = O((k log (m + 1) + log (1 / δ)) / (m - k))`
   (`GeneralCompressionScheme.measure_pi_zero_heldOut_gt_le`).

## Main definitions

- `GeneralCompressionScheme α β k`: size-`k` compression scheme without realizability or
  zero-error requirements.
- `SampleCompressionScheme.toGeneral`: views a realizable `SampleCompressionScheme C k` as a
  `GeneralCompressionScheme α β k` by truncating off-realizability lists to length `≤ k`.
- `heldOutMiscount J h S`, `heldOutError J h S`: misclassification count and empirical error rate
  of `h` on the held-out complement `Jᶜ`.

## Main results

- `measure_pi_bernstein_single_le`: single-hypothesis lower-tail Chernoff inversion on `Fin n`.
- `GeneralCompressionScheme.measure_pi_abs_sub_heldOutError_le`: raw Hoeffding tail
  `(m + 1) ^ k * 2 exp (-2 (m - k) ε²)`.
- `GeneralCompressionScheme.measure_pi_hoeffding_gt_le`: `δ`-parameterized two-sided Hoeffding
  compression bound.
- `GeneralCompressionScheme.measure_pi_bernstein_tail_le`: raw Bernstein/Chernoff tail
  `(m + 1) ^ k * exp (-(m - k) c)`.
- `GeneralCompressionScheme.measure_pi_bernstein_gt_le`: sharp quadratic form
  `q + c + √(c² + 2 q c)`.
- `GeneralCompressionScheme.measure_pi_fastRate_gt_le`: relaxed additive form
  `q + √(2 q c) + 2 c` (`[ShalevShwartzBenDavid2014, Theorem 30.2]`).
- `GeneralCompressionScheme.measure_pi_zero_heldOut_gt_le`: zero held-out error corollary
  `2 c = 2 (k log (m + 1) + log (1 / δ)) / (m - k)` (`[ShalevShwartzBenDavid2014, Corollary 30.3]`).

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Theorem 30.2 and Corollary 30.3 (locators unverified)
* [S. Floyd, M. K. Warmuth, *Sample compression, learnability, and the Vapnik–Chervonenkis
  dimension*][FloydWarmuth1995] (locator unverified)
* [N. Littlestone, M. K. Warmuth, *Relating data compression and learnability*]
  [LittlestoneWarmuth1986] (locator unverified)
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- A *general (agnostic) sample compression scheme of size `k`*: on every sample `S` of length
`m`, `compress S` returns a list of at most `k` indices into `S`, and `reconstruct` maps the kept
labeled examples to a hypothesis. Unlike `SampleCompressionScheme`, no realizability or zero-error
property is assumed. -/
structure GeneralCompressionScheme (α β : Type*) (k : ℕ) where
  /-- The indices of the kept examples. -/
  compress : ∀ {m : ℕ}, LabeledSample α β m → List (Fin m)
  /-- The hypothesis reconstructed from a list of kept examples. -/
  reconstruct : List (α × β) → α → β
  /-- At most `k` examples are kept on every sample. -/
  length_compress_le : ∀ {m : ℕ} (S : LabeledSample α β m), (compress S).length ≤ k

namespace GeneralCompressionScheme

variable {k : ℕ}

/-- The hypothesis reconstructed from the compressed sample. -/
@[expose] def learner (κ : GeneralCompressionScheme α β k) {m : ℕ} : Learner α β m :=
  fun S => κ.reconstruct ((κ.compress S).map S)

/-- The finite set of distinct indices kept by `κ` on `S`. -/
@[expose] def keptSet (κ : GeneralCompressionScheme α β k) {m : ℕ}
    (S : LabeledSample α β m) : Finset (Fin m) :=
  (κ.compress S).toFinset

theorem card_keptSet_le (κ : GeneralCompressionScheme α β k) {m : ℕ}
    (S : LabeledSample α β m) : (κ.keptSet S).card ≤ k :=
  (List.toFinset_card_le _).trans (κ.length_compress_le S)

end GeneralCompressionScheme

/-- View a realizable `SampleCompressionScheme C k` as a `GeneralCompressionScheme α β k` by
truncating lists to length at most `k`. On every sample realized by `C`, both the compressed list
and reconstructed learner are unchanged. -/
@[expose] def SampleCompressionScheme.toGeneral {C : ConceptClass α β} {k : ℕ}
    (κ : SampleCompressionScheme C k) : GeneralCompressionScheme α β k where
  compress S := (κ.compress S).take k
  reconstruct := κ.reconstruct
  length_compress_le S := List.length_take_le k (κ.compress S)

theorem SampleCompressionScheme.toGeneral_compress_eq {C : ConceptClass α β} {k : ℕ}
    (κ : SampleCompressionScheme C k) {m : ℕ} {S : LabeledSample α β m} (hS : Realizable C S) :
    κ.toGeneral.compress S = κ.compress S :=
  List.take_of_length_le (κ.length_compress_le S hS)

theorem SampleCompressionScheme.toGeneral_learner_eq {C : ConceptClass α β} {k : ℕ}
    (κ : SampleCompressionScheme C k) {m : ℕ} {S : LabeledSample α β m} (hS : Realizable C S) :
    κ.toGeneral.learner S = κ.learner S := by
  rw [GeneralCompressionScheme.learner, SampleCompressionScheme.learner,
    κ.toGeneral_compress_eq hS]
  rfl

/-! ### Held-out empirical error -/

section HeldOut

variable [DecidableEq β]

/-- Number of examples in `S` indexed outside `J` misclassified by `h`. -/
@[expose] def heldOutMiscount {m : ℕ} (J : Finset (Fin m)) (h : α → β)
    (S : LabeledSample α β m) : ℕ :=
  (Jᶜ.filter fun i => h (S i).1 ≠ (S i).2).card

/-- Empirical error rate of `h` on the held-out complement `Jᶜ` of `S`. Returns `0` when
`Jᶜ` is empty (i.e. `J = Finset.univ`). -/
@[expose] noncomputable def heldOutError {m : ℕ} (J : Finset (Fin m)) (h : α → β)
    (S : LabeledSample α β m) : ℝ :=
  (heldOutMiscount J h S : ℝ) / (Jᶜ.card : ℝ)

private theorem heldOutMiscount_le_card {m : ℕ} (J : Finset (Fin m)) (h : α → β)
    (S : LabeledSample α β m) : heldOutMiscount J h S ≤ Jᶜ.card :=
  Finset.card_filter_le _ _

private theorem heldOutMiscount_le_empiricalMiscount {m : ℕ} (J : Finset (Fin m)) (h : α → β)
    (S : LabeledSample α β m) : heldOutMiscount J h S ≤ empiricalMiscount h S := by
  refine Finset.card_le_card ?_
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.2

theorem heldOutError_nonneg {m : ℕ} (J : Finset (Fin m)) (h : α → β)
    (S : LabeledSample α β m) : 0 ≤ heldOutError J h S :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem heldOutError_le_one {m : ℕ} (J : Finset (Fin m)) (h : α → β)
    (S : LabeledSample α β m) : heldOutError J h S ≤ 1 := by
  rw [heldOutError]
  exact div_le_one_of_le₀ (Nat.cast_le.2 (heldOutMiscount_le_card J h S)) (Nat.cast_nonneg _)

theorem heldOutError_eq_zero_iff {m : ℕ} {J : Finset (Fin m)} (hJ : J.card < m) (h : α → β)
    (S : LabeledSample α β m) :
    heldOutError J h S = 0 ↔ ∀ i ∉ J, h (S i).1 = (S i).2 := by
  have hpos : 0 < Jᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  rw [heldOutError, div_eq_zero_iff]
  simp only [Nat.cast_eq_zero, ne_of_gt hpos, or_false, heldOutMiscount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, Finset.mem_compl, ne_eq, not_not]

theorem heldOutError_le_empiricalMiscount_div {m k : ℕ} {J : Finset (Fin m)}
    (hJk : J.card ≤ k) (hkm : k < m) (h : α → β) (S : LabeledSample α β m) :
    heldOutError J h S ≤ (empiricalMiscount h S : ℝ) / (m - k : ℕ) := by
  have hcard : m - k ≤ Jᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hpos : (0 : ℝ) < (m - k : ℕ) := Nat.cast_pos.2 (by omega)
  calc heldOutError J h S
      ≤ (heldOutMiscount J h S : ℝ) / (m - k : ℕ) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos (Nat.cast_le.2 hcard)
    _ ≤ (empiricalMiscount h S : ℝ) / (m - k : ℕ) :=
        div_le_div_of_nonneg_right (Nat.cast_le.2 (heldOutMiscount_le_empiricalMiscount J h S))
          hpos.le

end HeldOut

/-! ### Single-hypothesis multiplicative Chernoff / Bernstein tail -/

section SingleHypothesis

variable [MeasurableSpace α] [MeasurableSpace β] [DecidableEq β]

/-- Algebraic step: `√(c² + 2 q c) ≤ c + √(2 q c)` for `q, c ≥ 0`. -/
private theorem sqrt_sq_add_two_mul_le {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    Real.sqrt (c ^ 2 + 2 * q * c) ≤ c + Real.sqrt (2 * q * c) := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hsq : Real.sqrt (2 * q * c) ^ 2 = 2 * q * c := Real.sq_sqrt (by positivity)
  nlinarith [sq_nonneg c, Real.sqrt_nonneg (2 * q * c),
    mul_nonneg hc (Real.sqrt_nonneg (2 * q * c))]

/-- **Single-hypothesis lower-tail Chernoff inversion**: for a fixed hypothesis `h` with measurable
misclassification set, on `n > 0` i.i.d. examples from `D`,
`error D h > q + c + √(c² + 2 q c)` (where `q = empiricalMiscount h S / n`) with probability at
most `exp (-n c)`. Applies `Cslib.Probability.PMF.pi_sum_le_one_sub_mul` at `δ = √(2 c / p)`. -/
theorem measure_pi_bernstein_single_le (D : Measure (α × β)) [IsProbabilityMeasure D]
    {h : α → β} (hh : MeasurableSet {p : α × β | h p.1 ≠ p.2})
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 ≤ c) :
    Measure.pi (fun _ : Fin n => D)
        {S | (empiricalMiscount h S : ℝ) / n + c +
              Real.sqrt (c ^ 2 + 2 * ((empiricalMiscount h S : ℝ) / n) * c) <
            (error D h).toReal} ≤
      ENNReal.ofReal (Real.exp (-(n * c))) := by
  classical
  set p := (error D h).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  rcases eq_or_lt_of_le hp0 with hpz | hppos
  · refine (measure_mono_null (fun S hS => ?_) measure_empty).le.trans zero_le
    rw [mem_ofPred_eq, ← hpz] at hS
    exact absurd hS (not_lt.2 (by positivity))
  set f : α × β → Bool := fun x => decide (h x.1 ≠ x.2)
  have hft : f ⁻¹' {true} = {x : α × β | h x.1 ≠ x.2} := by ext x; simp [f]
  have hf : Measurable f := measurable_to_bool (hft ▸ hh)
  set qPmf : PMF Bool := (D.map f).toPMF
  have hmap : (Measure.pi fun _ : Fin n => D).map (fun S i => f (S i)) =
      (Cslib.Probability.PMF.pi fun _ : Fin n => qPmf).toMeasure :=
    Cslib.Probability.PMF.map_measurePi_eq_toMeasure_pi _ fun _ => hf.aemeasurable
  have hfm : Measurable fun (S : Fin n → α × β) i => f (S i) :=
    measurable_pi_iff.2 fun i => hf.comp (measurable_pi_apply i)
  have hqt : (qPmf true).toReal = p := by
    rw [Measure.toPMF_apply, Measure.map_apply hf (measurableSet_singleton _), hft]; rfl
  let score : Fin n → Bool → ℝ := fun _ b => if b = true then 1 else 0
  have hscore : ∀ i b, b ∈ qPmf.support → score i b ∈ Set.Icc (0 : ℝ) 1 := by
    intro _ b _; cases b <;> simp [score]
  have hmean : ∑ i : Fin n, ∑ a, (qPmf a).toReal * score i a = n * p := by
    simp only [score, Fintype.sum_bool, ite_true, mul_one, Bool.false_eq_true, ite_false,
      mul_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hqt]
  set δ : ℝ := Real.sqrt (2 * c / p)
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hcount (S : LabeledSample α β n) :
      (empiricalMiscount h S : ℝ) = ∑ i : Fin n, score i (f (S i)) := by
    simp only [empiricalMiscount, score, f, ← Finset.sum_boole, decide_eq_true_eq]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hsub : {S : LabeledSample α β n |
        (empiricalMiscount h S : ℝ) / n + c +
          Real.sqrt (c ^ 2 + 2 * ((empiricalMiscount h S : ℝ) / n) * c) < p} ⊆
      (fun S i => f (S i)) ⁻¹' {b : Fin n → Bool |
        ∑ i, score i (b i) ≤ (1 - δ) * (n * p)} := by
    intro S hS
    simp only [mem_ofPred_eq, mem_preimage, ← hcount]
    set q := (empiricalMiscount h S : ℝ) / n
    have hq0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg _) hnR.le
    have hlt_sqrt : Real.sqrt (c ^ 2 + 2 * q * c) < p - q - c := by
      linarith [show q + c + Real.sqrt (c ^ 2 + 2 * q * c) < p from hS]
    have hpos_rhs : 0 < p - q - c := (Real.sqrt_nonneg _).trans_lt hlt_sqrt
    have hsq := (Real.sqrt_lt' hpos_rhs).1 hlt_sqrt
    have hδp : δ * p ≤ p - q := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by linarith) two_ne_zero).1 ?_
      have : (δ * p) ^ 2 = 2 * c * p := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        field_simp
      nlinarith
    rw [show (empiricalMiscount h S : ℝ) = n * q by dsimp only [q]; field_simp]
    nlinarith
  calc Measure.pi (fun _ : Fin n => D)
          {S | (empiricalMiscount h S : ℝ) / n + c +
              Real.sqrt (c ^ 2 + 2 * ((empiricalMiscount h S : ℝ) / n) * c) < p}
      ≤ Measure.pi (fun _ : Fin n => D)
          ((fun S i => f (S i)) ⁻¹' {b : Fin n → Bool |
            ∑ i, score i (b i) ≤ (1 - δ) * (n * p)}) := measure_mono hsub
    _ = ((Cslib.Probability.PMF.pi fun _ : Fin n => qPmf).toMeasure)
          {b : Fin n → Bool | ∑ i, score i (b i) ≤ (1 - δ) * (n * p)} := by
        rw [← Measure.map_apply hfm (Set.toFinite _).measurableSet, hmap]
    _ = (Cslib.Probability.PMF.pi fun _ : Fin n => qPmf).toOuterMeasure
          {b : Fin n → Bool | ∑ i, score i (b i) ≤ (1 - δ) * (n * p)} :=
        PMF.toMeasure_apply_eq_toOuterMeasure _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(n * c))) := by
        have hne := Cslib.Probability.PMF.toOuterMeasure_ne_top
          (Cslib.Probability.PMF.pi fun _ : Fin n => qPmf)
          {b : Fin n → Bool | ∑ i, score i (b i) ≤ (1 - δ) * (n * p)}
        rw [ENNReal.le_ofReal_iff_toReal_le hne (Real.exp_pos _).le]
        have hch := Cslib.Probability.PMF.pi_sum_le_one_sub_mul
          (fun _ : Fin n => qPmf) score hscore (μ := n * p) (δ := δ) hmean.ge hδ0
        have hrate : δ ^ 2 * (n * p) / 2 = n * c := by
          rw [Real.sq_sqrt (by positivity)]
          field_simp
        rwa [hrate] at hch

end SingleHypothesis

/-! ### Generic hold-out slicing on `Measure.pi` -/

section Holdout

variable [MeasurableSpace α] [MeasurableSpace β] [DecidableEq β]

/-- Index-wise `g S (S i).1 ≠ (S i).2` count outside `J` is measurable in `S` when `g` has a
jointly measurable misclassification set. -/
private theorem measurable_heldOutMiscount {m : ℕ} (J : Finset (Fin m))
    {g : LabeledSample α β m → α → β}
    (hgm : MeasurableSet {q : (LabeledSample α β m × α) × β | Function.uncurry g q.1 ≠ q.2}) :
    Measurable fun S : LabeledSample α β m => (heldOutMiscount J (g S) S : ℝ) := by
  have heq : (fun S : LabeledSample α β m => (heldOutMiscount J (g S) S : ℝ)) =
      fun S => ∑ i ∈ Jᶜ, if g S (S i).1 ≠ (S i).2 then (1 : ℝ) else 0 := by
    simp only [heldOutMiscount, ← Finset.sum_boole]
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => ?_
  have hset : MeasurableSet {S : LabeledSample α β m | g S (S i).1 ≠ (S i).2} :=
    hgm.preimage (f := fun S : LabeledSample α β m => ((S, (S i).1), (S i).2)) (by fun_prop)
  exact Measurable.ite hset measurable_const measurable_const

omit [DecidableEq β] in
private theorem measurable_error_toReal (D : Measure (α × β)) [IsProbabilityMeasure D] {m : ℕ}
    {g : LabeledSample α β m → α → β}
    (hgm : MeasurableSet {q : (LabeledSample α β m × α) × β | Function.uncurry g q.1 ≠ q.2}) :
    Measurable fun S : LabeledSample α β m => (error D (g S)).toReal := by
  have hs : MeasurableSet {q : LabeledSample α β m × (α × β) | g q.1 q.2.1 ≠ q.2.2} :=
    hgm.preimage (f := fun q : LabeledSample α β m × (α × β) => ((q.1, q.2.1), q.2.2))
      (by fun_prop)
  exact (measurable_measure_prodMk_left hs).ennreal_toReal

/-- Generic conditional hold-out inequality: if `g` depends only on the coordinates in `J` and an
event `P(q, p)` of `(heldOutError, error.toReal)` has probability at most `bound` for every fixed
hypothesis `h` with measurable misclassification set on `Fin (m - J.card)` i.i.d. examples, then
`Measure.pi` of `{S | P (heldOutError J (g S) S) (error D (g S)).toReal}` is at most `bound`. -/
private theorem measure_pi_holdout_of_pred (D : Measure (α × β)) [IsProbabilityMeasure D]
    {m : ℕ} (J : Finset (Fin m)) {g : LabeledSample α β m → α → β}
    (hg : DependsOn g (J : Set (Fin m)))
    (hgm : MeasurableSet {q : (LabeledSample α β m × α) × β | Function.uncurry g q.1 ≠ q.2})
    (P : ℝ → ℝ → Prop)
    (hT : MeasurableSet {S : LabeledSample α β m |
      P (heldOutError J (g S) S) (error D (g S)).toReal})
    (bound : ℝ≥0∞)
    (hsingle : ∀ h : α → β, MeasurableSet {p : α × β | h p.1 ≠ p.2} →
      Measure.pi (fun _ : Fin (m - J.card) => D)
        {v | P ((empiricalMiscount h v : ℝ) / ((m - J.card : ℕ) : ℝ)) (error D h).toReal} ≤
          bound) :
    Measure.pi (fun _ : Fin m => D)
        {S | P (heldOutError J (g S) S) (error D (g S)).toReal} ≤ bound := by
  classical
  set T := {S : LabeledSample α β m | P (heldOutError J (g S) S) (error D (g S)).toReal}
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => α × β) (· ∈ J)
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin m => D) (· ∈ J)
  rw [← he.symm.measure_preimage_equiv T, Measure.prod_apply (e.symm.measurable hT)]
  have hcard : Fintype.card {i : Fin m // i ∉ J} = m - J.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have hcard_compl : Jᶜ.card = m - J.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  let eqv : Fin (m - J.card) ≃ {i : Fin m // i ∉ J} :=
    (Fintype.equivFinOfCardEq hcard).symm
  have hslice (S : LabeledSample α β m) : MeasurableSet {p : α × β | g S p.1 ≠ p.2} :=
    hgm.preimage (f := fun p : α × β => ((S, p.1), p.2)) (by fun_prop)
  have hbound (u : (i : {i // i ∈ J}) → α × β) :
      Measure.pi (fun _ : {i // i ∉ J} => D) (Prod.mk u ⁻¹' (e.symm ⁻¹' T)) ≤ bound := by
    rcases (Prod.mk u ⁻¹' (e.symm ⁻¹' T)).eq_empty_or_nonempty with h0 | ⟨v₀, _⟩
    · rw [h0, measure_empty]; exact zero_le
    set h := g (e.symm (u, v₀))
    have hconst (v : (i : {i // i ∉ J}) → α × β) : g (e.symm (u, v)) = h :=
      hg fun i hi => by
        simp only [e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, Finset.mem_coe.1 hi,
          dite_true]
    have hcount_eq (v : (i : {i // i ∉ J}) → α × β) :
        heldOutMiscount J h (e.symm (u, v)) =
          empiricalMiscount h (fun j : Fin (m - J.card) => v (eqv j)) := by
      refine Finset.card_bij
        (fun i hi => eqv.symm ⟨i, Finset.mem_compl.1 (Finset.mem_filter.1 hi).1⟩) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and] at hi ⊢
        simpa only [Equiv.apply_symm_apply, e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,
          hi.1, dite_false] using hi.2
      · intro i₁ hi₁ i₂ hi₂ h12
        have := congrArg (Subtype.val ∘ eqv) h12
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        refine ⟨(eqv j).1, Finset.mem_filter.2 ⟨Finset.mem_compl.2 (eqv j).2, ?_⟩, ?_⟩
        · simpa only [e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, (eqv j).2,
            dite_false, Subtype.coe_eta] using hj
        · exact eqv.symm_apply_apply j
    let reidx : ((i : {i // i ∉ J}) → α × β) ≃ᵐ LabeledSample α β (m - J.card) :=
      MeasurableEquiv.piCongrLeft (fun _ => α × β) eqv.symm
    have hmp : MeasurePreserving reidx
        (Measure.pi fun _ : {i // i ∉ J} => D)
        (Measure.pi fun _ : Fin (m - J.card) => D) :=
      measurePreserving_piCongrLeft (fun _ : Fin (m - J.card) => D) eqv.symm
    have hreidx_apply (v : (i : {i // i ∉ J}) → α × β) (j : Fin (m - J.card)) :
        reidx v j = v (eqv j) := by
      simp only [reidx, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
        Equiv.symm_symm, cast_eq]
    have hpre : Prod.mk u ⁻¹' (e.symm ⁻¹' T) ⊆
        reidx ⁻¹' {w : LabeledSample α β (m - J.card) |
          P ((empiricalMiscount h w : ℝ) / ((m - J.card : ℕ) : ℝ)) (error D h).toReal} := by
      intro v hv
      change P (heldOutError J (g (e.symm (u, v))) (e.symm (u, v)))
        (error D (g (e.symm (u, v)))).toReal at hv
      rw [hconst v, heldOutError, hcard_compl, hcount_eq v] at hv
      have hfn : (fun j => v (eqv j)) = reidx v := funext fun j => (hreidx_apply v j).symm
      simpa only [mem_preimage, mem_ofPred_eq, hfn] using hv
    calc Measure.pi (fun _ : {i // i ∉ J} => D) (Prod.mk u ⁻¹' (e.symm ⁻¹' T))
        ≤ Measure.pi (fun _ : {i // i ∉ J} => D)
            (reidx ⁻¹' {w | P ((empiricalMiscount h w : ℝ) / ((m - J.card : ℕ) : ℝ))
              (error D h).toReal}) := measure_mono hpre
      _ = Measure.pi (fun _ : Fin (m - J.card) => D)
            {w | P ((empiricalMiscount h w : ℝ) / ((m - J.card : ℕ) : ℝ))
              (error D h).toReal} := hmp.measure_preimage_equiv _
      _ ≤ bound := hsingle h (hslice _)
  refine (lintegral_mono hbound).trans_eq ?_
  rw [lintegral_const, measure_univ, mul_one]

/-- Shared union bound over all index lists `Fin j → Fin m` (`j ≤ k`, count `≤ (m + 1) ^ k`). -/
private theorem measure_pi_union_compression_le (D : Measure (α × β))
    {k m : ℕ} (κ : GeneralCompressionScheme α β k) (P : ℝ → ℝ → Prop) (bound : ℝ≥0∞)
    (hstep : ∀ (ι : Σ j : Fin (k + 1), Fin j → Fin m),
      let g : LabeledSample α β m → α → β := fun S => κ.reconstruct (List.ofFn (S ∘ ι.2))
      let J : Finset (Fin m) := Finset.univ.image ι.2
      Measure.pi (fun _ : Fin m => D)
        {S | P (heldOutError J (g S) S) (error D (g S)).toReal} ≤ bound) :
    Measure.pi (fun _ : Fin m => D)
        {S | P (heldOutError (κ.keptSet S) (κ.learner S) S)
          (error D (κ.learner S)).toReal} ≤
      ((m + 1) ^ k : ℕ) * bound := by
  classical
  set μ := Measure.pi (fun _ : Fin m => D)
  let g (ι : Σ j : Fin (k + 1), Fin j → Fin m) (S : LabeledSample α β m) : α → β :=
    κ.reconstruct (List.ofFn (S ∘ ι.2))
  let J (ι : Σ j : Fin (k + 1), Fin j → Fin m) : Finset (Fin m) := Finset.univ.image ι.2
  let B (ι : Σ j : Fin (k + 1), Fin j → Fin m) : Set (LabeledSample α β m) :=
    {S | P (heldOutError (J ι) (g ι S) S) (error D (g ι S)).toReal}
  have hsub : {S : LabeledSample α β m |
        P (heldOutError (κ.keptSet S) (κ.learner S) S) (error D (κ.learner S)).toReal} ⊆
      ⋃ ι, B ι := by
    intro S hS
    let j : Fin (k + 1) := ⟨(κ.compress S).length, Nat.lt_succ_of_le (κ.length_compress_le S)⟩
    let r : Fin j → Fin m := fun t => (κ.compress S)[t.1]
    refine Set.mem_iUnion.2 ⟨⟨j, r⟩, ?_⟩
    have hlist : List.ofFn (S ∘ r) = (κ.compress S).map S :=
      List.ext_getElem (by simp [j]) fun t _ _ => by simp [r]
    have hset_eq : J ⟨j, r⟩ = κ.keptSet S := by
      ext a
      simp only [J, GeneralCompressionScheme.keptSet, Finset.mem_image, Finset.mem_univ, true_and,
        List.mem_toFinset, List.mem_iff_getElem]
      constructor
      · rintro ⟨t, rfl⟩; exact ⟨t.1, t.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩
    change P (heldOutError (J ⟨j, r⟩) (g ⟨j, r⟩ S) S) (error D (g ⟨j, r⟩ S)).toReal
    have hg_eq : g ⟨j, r⟩ S = κ.learner S := by
      simp only [g, GeneralCompressionScheme.learner, hlist]
    rw [hset_eq, hg_eq]
    exact hS
  have hcard : Fintype.card (Σ j : Fin (k + 1), Fin j → Fin m) ≤ (m + 1) ^ k := by
    simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun j => m ^ j)]
    exact Cslib.sum_range_pow_le_add_one_pow m k
  calc μ {S | P (heldOutError (κ.keptSet S) (κ.learner S) S) (error D (κ.learner S)).toReal}
      ≤ μ (⋃ ι, B ι) := measure_mono hsub
    _ ≤ ∑ ι, μ (B ι) := measure_iUnion_fintype_le μ B
    _ ≤ ∑ _ι : Σ j : Fin (k + 1), Fin j → Fin m, bound := Finset.sum_le_sum fun ι _ => hstep ι
    _ = Fintype.card (Σ j : Fin (k + 1), Fin j → Fin m) * bound := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((m + 1) ^ k : ℕ) * bound := by gcongr

private theorem card_image_le_k {k m : ℕ} (ι : Σ j : Fin (k + 1), Fin j → Fin m) :
    (Finset.univ.image ι.2).card ≤ k :=
  (Finset.card_image_le).trans (by
    rw [Finset.card_univ, Fintype.card_fin]
    exact Nat.lt_succ_iff.1 ι.1.2)

omit [MeasurableSpace α] [MeasurableSpace β] [DecidableEq β] in
private theorem dependsOn_ofFn {m j : ℕ} (ρ : List (α × β) → α → β) (r : Fin j → Fin m) :
    DependsOn (fun S : LabeledSample α β m => ρ (List.ofFn (S ∘ r)))
      ((Finset.univ.image r : Finset (Fin m)) : Set (Fin m)) :=
  fun _ _ h => congrArg (fun l => ρ (List.ofFn l)) <|
    funext fun t => h _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ t)))

omit [DecidableEq β] in
private theorem measurableSet_uncurry_ofFn {m j : ℕ} {ρ : List (α × β) → α → β}
    (hρ : MeasurableReconstruction ρ) (r : Fin j → Fin m) :
    MeasurableSet {q : (LabeledSample α β m × α) × β |
      Function.uncurry (fun S : LabeledSample α β m => ρ (List.ofFn (S ∘ r))) q.1 ≠ q.2} := by
  have hm : Measurable fun q : (LabeledSample α β m × α) × β =>
      ((fun t => q.1.1 (r t), q.1.2), q.2) := by fun_prop
  exact (hρ j).preimage hm

end Holdout

namespace GeneralCompressionScheme

variable [MeasurableSpace α] [MeasurableSpace β] [DecidableEq β] {k : ℕ}

/-! ### Agnostic Hoeffding compression bound -/

/-- **Two-sided Hoeffding tail for agnostic sample compression schemes**
[LittlestoneWarmuth1986; FloydWarmuth1995] (locators unverified). For any distribution `D` on
`α × β` (no realizability assumption) and any `ε ≥ 0`, on `m` i.i.d. examples the empirical error
on the held-out complement differs from `error D (κ.learner S)` by at least `ε` with probability at
most `(m + 1) ^ k * 2 exp (-2 (m - k) ε²)`. -/
theorem measure_pi_abs_sub_heldOutError_le (κ : GeneralCompressionScheme α β k)
    (hκ : MeasurableReconstruction κ.reconstruct) (D : Measure (α × β)) [IsProbabilityMeasure D]
    (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => D)
        {S | ε ≤ |heldOutError (κ.keptSet S) (κ.learner S) S -
            (error D (κ.learner S)).toReal|} ≤
      ((m + 1) ^ k : ℕ) * ENNReal.ofReal (2 * Real.exp (-2 * (m - k : ℕ) * ε ^ 2)) := by
  let P : ℝ → ℝ → Prop := fun q p => ε ≤ |q - p|
  refine measure_pi_union_compression_le D κ P _ fun ι => ?_
  have hgm := measurableSet_uncurry_ofFn hκ ι.2
  have hdep := dependsOn_ofFn κ.reconstruct ι.2
  have hJk : (Finset.univ.image ι.2).card ≤ k := card_image_le_k ι
  refine measure_pi_holdout_of_pred D (Finset.univ.image ι.2) hdep hgm P ?_ _ fun h hh => ?_
  · have hq := (measurable_heldOutMiscount (Finset.univ.image ι.2) hgm).div_const
      ((Finset.univ.image ι.2)ᶜ.card : ℝ)
    have hp := measurable_error_toReal D hgm
    exact measurableSet_le measurable_const (continuous_abs.measurable.comp (hq.sub hp))
  · refine (measure_pi_le_abs_empiricalMiscount_div_sub_error D hh
      (m - (Finset.univ.image ι.2).card) hε).trans ?_
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) two_pos.le)
    have := (Nat.cast_le (α := ℝ)).2 (Nat.sub_le_sub_left hJk m)
    nlinarith [sq_nonneg ε]

private theorem pow_add_one_mul_exp_neg_le (m k : ℕ) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    (((m + 1) ^ k : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (a * Real.exp (-(k * Real.log (m + 1) + Real.log (a / δ)))) ≤
      ENNReal.ofReal δ := by
  have hcast : (((m + 1) ^ k : ℕ) : ℝ≥0∞) = ENNReal.ofReal (((m : ℝ) + 1) ^ k) := by
    rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_nat_mul,
    Real.exp_log (by positivity : (0 : ℝ) < (m : ℝ) + 1), Real.exp_log (div_pos ha hδ)]
  have hmp : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private theorem complexity_num_nonneg (m k : ℕ) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) :
    0 ≤ k * Real.log ((m : ℝ) + 1) + Real.log (a / δ) := by
  have hlogm : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlogδ : 0 ≤ Real.log (a / δ) := Real.log_nonneg ((one_le_div hδ).2 hδa)
  positivity

/-- **`δ`-parameterized two-sided Hoeffding bound for agnostic sample compression**: for `k < m`
and `0 < δ`, with probability at least `1 - δ` over `S ~ D ^ m`, the held-out empirical error and
true error of `κ.learner S` differ by less than `√((k log (m + 1) + log (2 / δ)) / (2 (m - k)))`. -/
theorem measure_pi_hoeffding_gt_le (κ : GeneralCompressionScheme α β k)
    (hκ : MeasurableReconstruction κ.reconstruct) (D : Measure (α × β)) [IsProbabilityMeasure D]
    {m : ℕ} (hkm : k < m) {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D)
        {S | Real.sqrt ((k * Real.log (m + 1) + Real.log (2 / δ)) / (2 * (m - k : ℕ))) ≤
          |heldOutError (κ.keptSet S) (κ.learner S) S - (error D (κ.learner S)).toReal|} ≤
      ENNReal.ofReal δ := by
  rcases le_or_gt 2 δ with hδ2 | hδ2
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 (by linarith))
  have hmk : (0 : ℝ) < (m - k : ℕ) := Nat.cast_pos.2 (by omega)
  have hnum := complexity_num_nonneg m k hδ hδ2.le
  set ε := Real.sqrt ((k * Real.log (m + 1) + Real.log (2 / δ)) / (2 * (m - k : ℕ)))
  refine (κ.measure_pi_abs_sub_heldOutError_le hκ D m (Real.sqrt_nonneg _)).trans ?_
  have hexp : -2 * ((m - k : ℕ) : ℝ) * ε ^ 2 = -(k * Real.log (m + 1) + Real.log (2 / δ)) := by
    rw [Real.sq_sqrt (div_nonneg hnum (by positivity))]
    field_simp
  rw [hexp]
  exact pow_add_one_mul_exp_neg_le m k two_pos hδ

/-! ### Agnostic multiplicative-Chernoff / Bernstein fast-rate bound -/

/-- **Raw Bernstein/Chernoff tail for agnostic sample compression**: for `k < m` and `c ≥ 0`,
`error D (κ.learner S) > q + c + √(c² + 2 q c)` (where `q = heldOutError (κ.keptSet S)
(κ.learner S) S`) with probability at most `(m + 1) ^ k * exp (-(m - k) * c)`. -/
theorem measure_pi_bernstein_tail_le (κ : GeneralCompressionScheme α β k)
    (hκ : MeasurableReconstruction κ.reconstruct) (D : Measure (α × β)) [IsProbabilityMeasure D]
    {m : ℕ} (hkm : k < m) {c : ℝ} (hc : 0 ≤ c) :
    Measure.pi (fun _ : Fin m => D)
        {S | heldOutError (κ.keptSet S) (κ.learner S) S + c +
            Real.sqrt (c ^ 2 + 2 * heldOutError (κ.keptSet S) (κ.learner S) S * c) <
          (error D (κ.learner S)).toReal} ≤
      ((m + 1) ^ k : ℕ) * ENNReal.ofReal (Real.exp (-((m - k : ℕ) * c))) := by
  let P : ℝ → ℝ → Prop := fun q p => q + c + Real.sqrt (c ^ 2 + 2 * q * c) < p
  refine measure_pi_union_compression_le D κ P _ fun ι => ?_
  have hgm := measurableSet_uncurry_ofFn hκ ι.2
  have hdep := dependsOn_ofFn κ.reconstruct ι.2
  have hJk : (Finset.univ.image ι.2).card ≤ k := card_image_le_k ι
  have hpos : 0 < m - (Finset.univ.image ι.2).card := by omega
  refine measure_pi_holdout_of_pred D (Finset.univ.image ι.2) hdep hgm P ?_ _ fun h hh => ?_
  · have hq := (measurable_heldOutMiscount (Finset.univ.image ι.2) hgm).div_const
      ((Finset.univ.image ι.2)ᶜ.card : ℝ)
    have hp := measurable_error_toReal D hgm
    exact measurableSet_lt
      ((hq.add measurable_const).add
        ((measurable_const.add ((measurable_const.mul hq).mul measurable_const)).sqrt)) hp
  · refine (measure_pi_bernstein_single_le D hh hpos hc).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := (Nat.cast_le (α := ℝ)).2 (Nat.sub_le_sub_left hJk m)
    nlinarith

/-- **Sharp quadratic agnostic sample compression bound** [ShalevShwartzBenDavid2014, Theorem 30.2]
(locator unverified; tighter constants). For `k < m`, `0 < δ`, and
`c = (k log (m + 1) + log (1 / δ)) / (m - k)`, with probability at least `1 - δ` over `S ~ D ^ m`,
`(error D (κ.learner S)).toReal ≤ q + c + √(c² + 2 q c)`, where `q` is the held-out error on
`(κ.keptSet S)ᶜ`. -/
theorem measure_pi_bernstein_gt_le (κ : GeneralCompressionScheme α β k)
    (hκ : MeasurableReconstruction κ.reconstruct) (D : Measure (α × β)) [IsProbabilityMeasure D]
    {m : ℕ} (hkm : k < m) {δ : ℝ} (hδ : 0 < δ) :
    let c := (k * Real.log (m + 1) + Real.log (1 / δ)) / (m - k : ℕ)
    Measure.pi (fun _ : Fin m => D)
        {S | heldOutError (κ.keptSet S) (κ.learner S) S + c +
            Real.sqrt (c ^ 2 + 2 * heldOutError (κ.keptSet S) (κ.learner S) S * c) <
          (error D (κ.learner S)).toReal} ≤
      ENNReal.ofReal δ := by
  intro c
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 hδ1)
  have hmk : (0 : ℝ) < (m - k : ℕ) := Nat.cast_pos.2 (by omega)
  have hc : 0 ≤ c := div_nonneg (complexity_num_nonneg m k hδ hδ1.le) hmk.le
  refine (κ.measure_pi_bernstein_tail_le hκ D hkm hc).trans ?_
  have hmul : ((m - k : ℕ) : ℝ) * c = k * Real.log (m + 1) + Real.log (1 / δ) := by
    dsimp only [c]; field_simp
  rw [hmul, ← one_mul (Real.exp _)]
  exact pow_add_one_mul_exp_neg_le m k one_pos hδ

/-- **Relaxed additive fast-rate bound for agnostic sample compression**
[ShalevShwartzBenDavid2014, Theorem 30.2] (locator unverified): for `k < m`, `0 < δ`, and
`c = (k log (m + 1) + log (1 / δ)) / (m - k)`,
`(error D (κ.learner S)).toReal ≤ q + √(2 q c) + 2 c` with probability at least `1 - δ`.
The coefficients `(√2, 2)` improve on the textbook Bernstein constants `(2, 4)` (or `(√4, 4)`
with `m / 2`). -/
theorem measure_pi_fastRate_gt_le (κ : GeneralCompressionScheme α β k)
    (hκ : MeasurableReconstruction κ.reconstruct) (D : Measure (α × β)) [IsProbabilityMeasure D]
    {m : ℕ} (hkm : k < m) {δ : ℝ} (hδ : 0 < δ) :
    let c := (k * Real.log (m + 1) + Real.log (1 / δ)) / (m - k : ℕ)
    Measure.pi (fun _ : Fin m => D)
        {S | heldOutError (κ.keptSet S) (κ.learner S) S +
            Real.sqrt (2 * heldOutError (κ.keptSet S) (κ.learner S) S * c) + 2 * c <
          (error D (κ.learner S)).toReal} ≤
      ENNReal.ofReal δ := by
  intro c
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 hδ1)
  have hc : 0 ≤ c :=
    div_nonneg (complexity_num_nonneg m k hδ hδ1.le) (Nat.cast_nonneg _)
  refine (measure_mono fun S hS => ?_).trans (κ.measure_pi_bernstein_gt_le hκ D hkm hδ)
  have hS' : heldOutError (κ.keptSet S) (κ.learner S) S +
      Real.sqrt (2 * heldOutError (κ.keptSet S) (κ.learner S) S * c) + 2 * c <
      (error D (κ.learner S)).toReal := hS
  have hq : 0 ≤ heldOutError (κ.keptSet S) (κ.learner S) S := heldOutError_nonneg _ _ _
  have hsqrt := sqrt_sq_add_two_mul_le hq hc
  change heldOutError (κ.keptSet S) (κ.learner S) S + c +
      Real.sqrt (c ^ 2 + 2 * heldOutError (κ.keptSet S) (κ.learner S) S * c) <
    (error D (κ.learner S)).toReal
  linarith [hS', hsqrt]

omit [DecidableEq β] in
/-- **Zero held-out error corollary** [ShalevShwartzBenDavid2014, Corollary 30.3] (locator
unverified): the event where `κ.learner S` labels every held-out example correctly yet has true
error above `2 * (k log (m + 1) + log (1 / δ)) / (m - k)` has probability at most `δ`. -/
theorem measure_pi_zero_heldOut_gt_le (κ : GeneralCompressionScheme α β k)
    (hκ : MeasurableReconstruction κ.reconstruct) (D : Measure (α × β)) [IsProbabilityMeasure D]
    {m : ℕ} (hkm : k < m) {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D)
        {S | (∀ i ∉ κ.keptSet S, κ.learner S (S i).1 = (S i).2) ∧
          2 * (k * Real.log (m + 1) + Real.log (1 / δ)) / (m - k : ℕ) <
            (error D (κ.learner S)).toReal} ≤
      ENNReal.ofReal δ := by
  classical
  refine (measure_mono fun S hS => ?_).trans
    (κ.measure_pi_fastRate_gt_le hκ D hkm hδ)
  have hzero : ∀ i ∉ κ.keptSet S, κ.learner S (S i).1 = (S i).2 := hS.1
  have hgt : 2 * (k * Real.log (m + 1) + Real.log (1 / δ)) / (m - k : ℕ) <
      (error D (κ.learner S)).toReal := hS.2
  have hJk : (κ.keptSet S).card < m := (κ.card_keptSet_le S).trans_lt hkm
  have hq0 : heldOutError (κ.keptSet S) (κ.learner S) S = 0 :=
    (heldOutError_eq_zero_iff hJk _ _).2 hzero
  change heldOutError (κ.keptSet S) (κ.learner S) S +
      Real.sqrt (2 * heldOutError (κ.keptSet S) (κ.learner S) S *
        ((k * Real.log (m + 1) + Real.log (1 / δ)) / (m - k : ℕ))) +
      2 * ((k * Real.log (m + 1) + Real.log (1 / δ)) / (m - k : ℕ)) <
    (error D (κ.learner S)).toReal
  simpa only [hq0, mul_zero, zero_mul, zero_div, Real.sqrt_zero, zero_add,
    mul_div_assoc'] using hgt

end GeneralCompressionScheme

end Cslib.MachineLearning.PACLearning
