/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.MachineLearning.Replicable.Basic
public import CslibFrontier.MachineLearning.Replicable.Rounding
public import CslibFrontier.Languages.Probabilistic.Basic
import CslibFrontier.Probability.Azuma
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.ToReal

/-!
# Replicable bounded-mean and coin bias estimation

This module provides an end-to-end replicable estimation client based on Hoeffding concentration
and periodic grid rounding (`roundGridProg`) [ImpagliazzoLeiPitassiSorrell2022]:

* **Bounded mean estimation (`replicableMeanProg`)**: given any domain `X` and bounded observable
  `f : X → ℝ` taking values in `[a, b]`, empirical averaging combined with `roundGridProg w N`
  yields a `ProbComp`-backed `Program` that is both strongly `ρ`-replicable over all distributions
  `D : PMF X` and `(ε, β)`-accurate for estimating `𝔼_{x ~ D}[f x]`.
* **Coin bias estimation (`replicableBiasProg`)**: specializing to `X = Bool` and
  `coinBias D = (D true).toReal`, empirical head frequency plus `roundGridProg` gives an explicit
  strongly `ρ`-replicable and `(ε, β)`-accurate coin bias estimator with concrete sample-complexity
  guarantees.

## Main definitions

* `Cslib.MachineLearning.Replicable.empiricalMean`,
  `Cslib.MachineLearning.Replicable.distExpectation`: sample average and population expectation.
* `Cslib.MachineLearning.Replicable.replicableMeanProg`: `ProbComp` replicable mean-estimation
  program.
* `Cslib.MachineLearning.Replicable.coinBias`,
  `Cslib.MachineLearning.Replicable.empiricalBias`,
  `Cslib.MachineLearning.Replicable.replicableBiasProg`: replicable coin bias-estimation program.

## Main results

* `Cslib.MachineLearning.Replicable.boundedMean_concentrates`: Hoeffding concentration of
  `empiricalMean` around `distExpectation`.
* `Cslib.MachineLearning.Replicable.estimates_replicableMeanProg`,
  `Cslib.MachineLearning.Replicable.isReplicable_replicableMeanProg`,
  `Cslib.MachineLearning.Replicable.exists_replicableMeanProg`: strong `ρ`-replicability and
  `(ε, β)`-accuracy for bounded-mean estimation.
* `Cslib.MachineLearning.Replicable.estimates_replicableBiasProg`,
  `Cslib.MachineLearning.Replicable.isReplicable_replicableBiasProg`,
  `Cslib.MachineLearning.Replicable.exists_replicableBiasProg`: concrete quantitative guarantees
  and parameter synthesis for replicable coin bias estimation.

## References

* [Impagliazzo, Lei, Pitassi, Sorrell (STOC 2022)][ImpagliazzoLeiPitassiSorrell2022],
  *Reproducibility in Learning* (paper PDF not directly inspected in this formalization;
  `ProbComp` bias-estimation programs and Hoeffding/grid-rounding proofs are formalized directly).
-/

public section

namespace Cslib.MachineLearning.Replicable

section BoundedMean

variable {X : Type}

/-- Sample average of `f : X → ℝ` over `S : Fin m → X`. -/
@[expose] noncomputable def empiricalMean {X : Type*} (f : X → ℝ) {m : ℕ} (S : Fin m → X) : ℝ :=
  (∑ j : Fin m, f (S j)) / m

/-- Population expectation `∑' x, (D x).toReal * f x` on a domain `X`. -/
@[expose] noncomputable def distExpectation {X : Type*} (D : PMF X) (f : X → ℝ) : ℝ :=
  ∑' x : X, (D x).toReal * f x

/-- `ProbComp`-backed ideal real-arithmetic program for replicable bounded-mean estimation via
periodic grid rounding of `empiricalMean f` (interpreted semantically via `Program.toAlgorithm`). -/
@[expose] noncomputable def replicableMeanProg (f : X → ℝ) (w : ℝ) (N m : ℕ) [NeZero N] :
    Program X (Fin N) ℝ m :=
  roundGridProg w N (empiricalMean f)

/-- Hoeffding concentration of the empirical mean of an observable `f : X → [a, b]` under
`m ≥ 1` i.i.d. draws from `D`, using effective width `M = max (b - a) 1`. -/
theorem boundedMean_concentrates {X : Type*} (D : PMF X) (f : X → ℝ) {a b : ℝ}
    (hf : ∀ x ∈ D.support, f x ∈ Set.Icc a b) (m : ℕ) [NeZero m] {δ : ℝ} (hδ : 0 ≤ δ) :
    ((Probability.PMF.iid D m).toOuterMeasure
      {S : Fin m → X | δ < |empiricalMean f S - distExpectation D f|}).toReal ≤
      2 * Real.exp (-2 * (m : ℝ) * δ ^ 2 / (max (b - a) 1) ^ 2) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  let bound : ℝ := max (b - a) 1
  have hiid : Probability.PMF.iid D m = Probability.PMF.seqProcess (fun _ _ => D) m := by
    ext S
    rw [Probability.PMF.iid_apply, Probability.PMF.seqProcess_apply]
  have hsumm : Summable fun x : X => (D x).toReal * f x :=
    Probability.PMF.summable_toReal_mul_of_abs_le D f (C := max |a| |b|) fun x hx =>
      abs_le_max_abs_abs (hf x hx).1 (hf x hx).2
  let Xproc : ∀ k : ℕ, (Fin k → X) → ℝ := fun k S => ∑ j : Fin k, (f (S j) - distExpectation D f)
  have hsnoc (k : ℕ) (S : Fin k → X) (x : X) :
      Xproc (k + 1) (Fin.snoc S x) = Xproc k S + (f x - distExpectation D f) := by
    simp only [Xproc, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  have hazuma := Probability.PMF.seqProcess_abs_sub_ge_le (fun _ _ => D) Xproc (fun _ => bound) m
    (fun k _ S _ => by
      have heq (x : X) : (D x).toReal * Xproc (k + 1) (Fin.snoc S x) =
          (D x).toReal * (Xproc k S - distExpectation D f) + (D x).toReal * f x := by
        rw [hsnoc]
        ring
      simp_rw [heq]
      rw [((Probability.PMF.summable_toReal D).mul_right _).tsum_add hsumm, tsum_mul_right,
        Probability.PMF.tsum_toReal D, one_mul]
      unfold distExpectation
      ring)
    (fun k _ S _ =>
      ⟨Xproc k S + (a - distExpectation D f), Xproc k S + (b - distExpectation D f),
        by dsimp only [bound]; linarith [le_max_left (b - a) 1], fun x hx => by
          obtain ⟨hlo, hhi⟩ := hf x hx
          rw [hsnoc]
          exact ⟨by linarith, by linarith⟩⟩)
    (mul_nonneg hm.le hδ)
  have hsub : {S : Fin m → X | δ < |empiricalMean f S - distExpectation D f|} ⊆
      {S : Fin m → X | (m : ℝ) * δ ≤ |Xproc m S - Xproc 0 Fin.elim0|} := by
    intro S hS
    simp only [Set.mem_ofPred_eq, empiricalMean, Xproc, Fin.sum_univ_zero, sub_zero] at hS ⊢
    have hdiff : (∑ j : Fin m, (f (S j) - distExpectation D f)) =
        (m : ℝ) * ((∑ j : Fin m, f (S j)) / m - distExpectation D f) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [hm.ne']
    rw [hdiff, abs_mul, abs_of_pos hm]
    exact (mul_lt_mul_of_pos_left hS hm).le
  rw [hiid]
  refine (Probability.PMF.toOuterMeasure_toReal_mono _ hsub).trans (hazuma.trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, bound]
  congr 1
  field_simp [hm.ne']

/-- Strong `(w / 2 + δ, 2 * exp (-2 * m * δ^2 / (max (b - a) 1)^2))`-estimation accuracy of
`replicableMeanProg`. -/
theorem estimates_replicableMeanProg (f : X → ℝ) {a b : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) {w δ : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) (N m : ℕ)
    [NeZero N] [NeZero m] :
    Estimates (replicableMeanProg f w N m).toAlgorithm (fun D => distExpectation D f)
      (w / 2 + δ) (2 * Real.exp (-2 * (m : ℝ) * δ ^ 2 / (max (b - a) 1) ^ 2)) :=
  isAccurateFor_roundGridProg_of_concentrates hw N (empiricalMean f) Set.univ
    (fun D => distExpectation D f) fun D _ =>
      boundedMean_concentrates D f (fun x _ => hf x) m hδ

/-- Strong `ρ`-replicability of `replicableMeanProg` for any bounded observable `f : X → [a, b]`. -/
theorem isReplicable_replicableMeanProg (f : X → ℝ) {a b : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) {w δ : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) (N m : ℕ)
    [NeZero N] [NeZero m] :
    IsReplicable (replicableMeanProg f w N m).toAlgorithm
      (2 * δ / w + 1 / N + 2 * (2 * Real.exp (-2 * (m : ℝ) * δ ^ 2 / (max (b - a) 1) ^ 2))) :=
  isReplicableFor_roundGridProg_of_concentrates hw N (empiricalMean f) Set.univ
    (fun D => distExpectation D f) hδ (by positivity) fun D _ =>
      boundedMean_concentrates D f (fun x _ => hf x) m hδ

/-- **Parameter synthesis for replicable bounded-mean estimation**: for any domain `X`, bounded
`f : X → [a, b]`, and target `(ε, ρ, β)` with `ε, ρ, β > 0`, there exist `w > 0` and `N, m ≥ 1`
making `(replicableMeanProg f w N m).toAlgorithm` strongly `ρ`-replicable and strongly
`(ε, β)`-accurate. -/
theorem exists_replicableMeanProg (f : X → ℝ) {a b ε ρ β : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) (hε : 0 < ε) (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ (w : ℝ) (N m : ℕ) (_ : NeZero N) (_ : NeZero m), 0 < w ∧
      IsReplicable (replicableMeanProg f w N m).toAlgorithm ρ ∧
      Estimates (replicableMeanProg f w N m).toAlgorithm (fun D => distExpectation D f) ε β := by
  let δ : ℝ := min (ε / 2) (ρ / 8 * ε)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨N, hN_gt⟩ := exists_nat_gt (4 / ρ)
  have hNR : (0 : ℝ) < N := (by positivity : (0 : ℝ) < 4 / ρ).trans hN_gt
  have hN_inst : NeZero N := ⟨by exact_mod_cast hNR.ne'⟩
  have hN_bound : (1 : ℝ) / N ≤ ρ / 4 := by
    rw [div_le_div_iff₀ hNR (by norm_num : (0 : ℝ) < 4), one_mul]
    linarith [(div_lt_iff₀ hρ).mp hN_gt]
  let width : ℝ := max (b - a) 1
  have hwidth : 0 < width := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let errTarget : ℝ := min (ρ / 4) β
  have herrTarget : 0 < errTarget := lt_min (by positivity) hβ
  let t : ℝ := Real.log (2 / errTarget) * width ^ 2 / (2 * δ ^ 2)
  obtain ⟨m, hm_gt⟩ := exists_nat_gt (max t 0)
  have hm_inst : NeZero m := ⟨by exact_mod_cast ((le_max_right t 0).trans_lt hm_gt).ne'⟩
  have hm_bound : 2 * Real.exp (-2 * (m : ℝ) * δ ^ 2 / width ^ 2) ≤ errTarget := by
    have hmt : t < m := (le_max_left t 0).trans_lt hm_gt
    have harg : Real.log (2 / errTarget) < 2 * (m : ℝ) * δ ^ 2 / width ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]
      linarith [(div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * δ ^ 2)).1 hmt]
    have := Real.exp_le_exp.2 (show -2 * (m : ℝ) * δ ^ 2 / width ^ 2 ≤ Real.log (errTarget / 2) by
      rw [neg_mul, neg_mul, neg_div, ← inv_div 2 errTarget, Real.log_inv, neg_le_neg_iff]
      exact harg.le)
    rw [Real.exp_log (by positivity)] at this
    linarith
  refine ⟨ε, N, m, hN_inst, hm_inst, hε, ?_, ?_⟩
  · refine (isReplicable_replicableMeanProg f hf hε hδ.le N m).mono ?_
    have hle : δ ≤ ρ / 8 * ε := min_le_right _ _
    have h1 : 2 * δ / ε ≤ ρ / 4 := by rw [div_le_iff₀ hε]; linarith
    have h2 : 2 * Real.exp (-2 * (m : ℝ) * δ ^ 2 / (max (b - a) 1) ^ 2) ≤ ρ / 4 :=
      hm_bound.trans (min_le_left _ _)
    linarith
  · exact (estimates_replicableMeanProg f hf hε hδ.le N m).mono
      (by have : δ ≤ ε / 2 := min_le_left _ _; linarith)
      (hm_bound.trans (min_le_right _ _))

end BoundedMean

section CoinBias

/-- True bias `Pr_{x ~ D}[x = true]` of a Bernoulli distribution `D : PMF Bool`. -/
@[expose] noncomputable def coinBias (D : PMF Bool) : ℝ :=
  (D true).toReal

/-- Empirical bias (fraction of `true` samples) of `S : Fin m → Bool`. -/
@[expose] noncomputable def empiricalBias {m : ℕ} (S : Fin m → Bool) : ℝ :=
  ((Finset.univ.filter fun j : Fin m => S j = true).card : ℝ) / m

/-- `ProbComp`-backed ideal real-arithmetic program for replicable coin bias estimation via
periodic grid rounding of `empiricalBias` (interpreted semantically via `Program.toAlgorithm`). -/
@[expose] noncomputable def replicableBiasProg (w : ℝ) (N m : ℕ) [NeZero N] :
    Program Bool (Fin N) ℝ m :=
  roundGridProg w N empiricalBias

private theorem empiricalBias_eq_empiricalMean {m : ℕ} (S : Fin m → Bool) :
    empiricalBias S = empiricalMean (fun b => if b then (1 : ℝ) else 0) S := by
  simp only [empiricalBias, empiricalMean, Finset.card_filter, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  cases S j <;> simp

private theorem coinBias_eq_distExpectation (D : PMF Bool) :
    coinBias D = distExpectation D (fun b => if b then (1 : ℝ) else 0) := by
  simp [coinBias, distExpectation, tsum_fintype]

private theorem replicableBiasProg_toAlgorithm_eq (w : ℝ) (N m : ℕ) [NeZero N] :
    (replicableBiasProg w N m).toAlgorithm =
      (replicableMeanProg (fun b : Bool => if b then (1 : ℝ) else 0) w N m).toAlgorithm := by
  simp only [Program.toAlgorithm, replicableBiasProg, replicableMeanProg, roundGridProg]
  congr 2
  ext S i
  simp [empiricalBias_eq_empiricalMean]

/-- Strong `(w / 2 + δ, 2 * exp (-2 * m * δ^2))`-estimation accuracy of `replicableBiasProg`
for estimating `coinBias D` across all Bernoulli distributions `D : PMF Bool`. -/
theorem estimates_replicableBiasProg {w δ : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) (N m : ℕ)
    [NeZero N] [NeZero m] :
    Estimates (replicableBiasProg w N m).toAlgorithm coinBias
      (w / 2 + δ) (2 * Real.exp (-2 * (m : ℝ) * δ ^ 2)) := by
  have hf : ∀ b : Bool, (if b then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := fun b => by
    cases b <;> simp
  have hest := estimates_replicableMeanProg (fun b : Bool => if b then (1 : ℝ) else 0) hf hw hδ
    N m
  rw [show max ((1 : ℝ) - 0) 1 = 1 by norm_num, one_pow, div_one] at hest
  intro D hD
  dsimp only
  rw [replicableBiasProg_toAlgorithm_eq, coinBias_eq_distExpectation]
  exact hest D hD

/-- Strong `ρ`-replicability of `replicableBiasProg` across all distributions `D : PMF Bool`. -/
theorem isReplicable_replicableBiasProg {w δ : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) (N m : ℕ)
    [NeZero N] [NeZero m] :
    IsReplicable (replicableBiasProg w N m).toAlgorithm
      (2 * δ / w + 1 / N + 2 * (2 * Real.exp (-2 * (m : ℝ) * δ ^ 2))) := by
  have hf : ∀ b : Bool, (if b then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := fun b => by
    cases b <;> simp
  have hrep := isReplicable_replicableMeanProg (fun b : Bool => if b then (1 : ℝ) else 0) hf hw hδ
    N m
  rw [show max ((1 : ℝ) - 0) 1 = 1 by norm_num, one_pow, div_one] at hrep
  intro D hD
  rw [replicableBiasProg_toAlgorithm_eq]
  exact hrep D hD

/-- **Replicable coin bias-estimation theorem** [ImpagliazzoLeiPitassiSorrell2022]: for any
`ε > 0`, `ρ > 0`, and `β > 0`, there exist `w > 0` and `N, m ≥ 1` such that
`(replicableBiasProg w N m).toAlgorithm` is strongly `ρ`-replicable and strongly
`(ε, β)`-accurate for estimating `coinBias D`. -/
theorem exists_replicableBiasProg {ε ρ β : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ (w : ℝ) (N m : ℕ) (_ : NeZero N) (_ : NeZero m), 0 < w ∧
      IsReplicable (replicableBiasProg w N m).toAlgorithm ρ ∧
      Estimates (replicableBiasProg w N m).toAlgorithm coinBias ε β := by
  have hf : ∀ b : Bool, (if b then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := fun b => by
    cases b <;> simp
  obtain ⟨w, N, m, hN, hm, hw, hrep, hest⟩ :=
    exists_replicableMeanProg (fun b : Bool => if b then (1 : ℝ) else 0) hf hε hρ hβ
  refine ⟨w, N, m, hN, hm, hw, fun D hD => ?_, fun D hD => ?_⟩
  · rw [replicableBiasProg_toAlgorithm_eq]
    exact hrep D hD
  · dsimp only
    rw [replicableBiasProg_toAlgorithm_eq, coinBias_eq_distExpectation]
    exact hest D hD

end CoinBias

end Cslib.MachineLearning.Replicable
