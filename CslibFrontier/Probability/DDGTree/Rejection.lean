/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Foundations.Data.Fin.Decode
public import CslibFrontier.Init
public import CslibFrontier.Probability.DDGTree
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
public import CslibFrontier.Probability.UniformNat
import CslibFrontier.Probability.Option
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.StatisticalDistance.ClosedForm
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Exact fair-bit block-rejection sampling and capped trials

A block-rejection sampler (`Cslib.Probability.BlockRejectionSpec`) reads fair bits in independent
blocks of length `width` and applies a single-block decoder `attempt : List Bool → Option α`. On
`some a` the sampler accepts and halts with `a`; on `none` it rejects the block and repeats on the
remaining bits.

Running at most `trials` blocks gives the capped law `BlockRejectionSpec.runTrials` (realized by
`decodeTrials` on `trials * width` fair bits), whose failure probability is `rejectProb ^ trials`
and whose fallback completion `runCapped` lies within statistical distance
`(rejectProb ^ trials).toReal` of the target distribution. Reading arbitrarily many blocks defines a
computable discrete distribution generating tree `BlockRejectionSpec.toDDGTree` satisfying
`toDDGTree.run n = runTrials (n / width)` for every bit budget `n`, generating the target law
whenever `0 < width` and `acceptProb ≠ 0`, and reading `width / acceptProb` fair bits in
expectation (`expectedFlips_toDDGTree`).

Instantiating `BlockRejectionSpec` with binary decoding yields:
* `uniformFinRejectionSpec` and `uniformFinTree` for `Fin n` (`[NeZero n]`), generating
  `PMF.uniformOfFintype (Fin n)` with expected flips at most `2 * Nat.clog 2 n` (attaining `k` at
  powers of two `2 ^ k`) and `t`-trial failure probability at most `(1 / 2) ^ t`;
* `dyadicFinRejectionSpec` using `UniformNat.dyadicSize n` (`Nat.log 2 n + 1` bits per trial),
  giving `t`-trial failure probability at most `(1 / 2) ^ t` for all `n ≥ 1`;
* `subsetDyadicSpec` for exact uniform sampling on a nonempty subset `S : Finset α` inside an
  indexed range `Fin m → α`.

## Main definitions

* `Cslib.Probability.BlockRejectionSpec`: block width and single-block acceptance decoder.
* `Cslib.Probability.BlockRejectionSpec.decodeTrials`, `runTrials`, `runCapped`: capped `t`-trial
  decoder, optional law, and fallback completion.
* `Cslib.Probability.BlockRejectionSpec.toDDGTree`: exact unbounded `DDGTree` of a block sampler.
* `Cslib.Probability.finCutoffSpec`, `uniformFinRejectionSpec`, `uniformFinTree`,
  `dyadicFinRejectionSpec`, `subsetDyadicSpec`: exact bounded-integer and subset fair-bit rejection
  samplers.

## Main results

* `Cslib.Probability.BlockRejectionSpec.acceptProb_eq_tsum_some`,
  `Cslib.Probability.BlockRejectionSpec.runTrials_none`,
  `Cslib.Probability.BlockRejectionSpec.runTrials_some_of_singleLaw`: exact single-trial and
  `t`-trial laws.
* `Cslib.Probability.BlockRejectionSpec.dist_runCapped_le`,
  `Cslib.Probability.BlockRejectionSpec.closeTo_runCapped`: statistical distance of the capped
  fallback sampler from the target law (with and without `[Fintype α]`).
* `Cslib.Probability.BlockRejectionSpec.run_toDDGTree`,
  `Cslib.Probability.BlockRejectionSpec.toDDGTree_generates`,
  `Cslib.Probability.BlockRejectionSpec.expectedFlips_toDDGTree`: exact `DDGTree` generation and
  closed-form expected fair-bit cost `width / acceptProb`.
* `Cslib.Probability.uniformFinTree_generates`,
  `Cslib.Probability.expectedFlips_uniformFinTree_two_pow`,
  `Cslib.Probability.expectedFlips_uniformFinTree_le`,
  `Cslib.Probability.runTrials_dyadicFinRejectionSpec_none_le`: bounded-integer exactness, expected
  flip bounds, and exponential trial-failure decay.
* `Cslib.Probability.subsetDyadicSpec_generates`,
  `Cslib.Probability.expectedFlips_subsetDyadicSpec`: exact subset generation and expected flips.

## References

* [D. E. Knuth, A. C. Yao, *The complexity of nonuniform random number generation*][KnuthYao1976].
-/

public section

open scoped ENNReal Cslib.Probability.PMF
open Filter Topology

namespace Cslib.Probability

/-- Specification of a block-rejection fair-bit sampler: each trial reads `width` independent fair
bits and applies `attempt`; `some a` accepts `a`, and `none` rejects the block. -/
structure BlockRejectionSpec (α : Type*) where
  /-- Number of fair bits read per rejection trial. -/
  width : ℕ
  /-- Single-block decoder returning `some a` on acceptance and `none` on rejection. -/
  attempt : List Bool → Option α

namespace BlockRejectionSpec

variable {α : Type*}

/-- Law of a single `width`-bit rejection trial. -/
@[expose] noncomputable def singleLaw (spec : BlockRejectionSpec α) : PMF (Option α) :=
  (BitString.uniformList spec.width).map spec.attempt

/-- Rejection probability of a single `width`-bit trial. -/
@[expose] noncomputable def rejectProb (spec : BlockRejectionSpec α) : ℝ≥0∞ :=
  spec.singleLaw none

/-- Acceptance probability `1 - rejectProb` of a single `width`-bit trial. -/
@[expose] noncomputable def acceptProb (spec : BlockRejectionSpec α) : ℝ≥0∞ :=
  1 - spec.rejectProb

theorem rejectProb_le_one (spec : BlockRejectionSpec α) : spec.rejectProb ≤ 1 :=
  PMF.coe_le_one _ _

/-- The rejection probability is finite, as a `finiteness` rule. -/
@[aesop (rule_sets := [finiteness]) safe apply]
theorem rejectProb_ne_top (spec : BlockRejectionSpec α) : spec.rejectProb ≠ ⊤ :=
  PMF.apply_ne_top _ _

theorem acceptProb_add_rejectProb (spec : BlockRejectionSpec α) :
    spec.acceptProb + spec.rejectProb = 1 :=
  tsub_add_cancel_of_le spec.rejectProb_le_one

theorem one_sub_rejectProb (spec : BlockRejectionSpec α) :
    1 - spec.rejectProb = spec.acceptProb :=
  rfl

theorem rejectProb_lt_one_iff (spec : BlockRejectionSpec α) :
    spec.rejectProb < 1 ↔ spec.acceptProb ≠ 0 := by
  rw [acceptProb, ne_eq, tsub_eq_zero_iff_le, not_le]

/-- Acceptance probability of a single block equals `∑' a, spec.singleLaw (some a)`. -/
theorem acceptProb_eq_tsum_some (spec : BlockRejectionSpec α) :
    spec.acceptProb = ∑' a, spec.singleLaw (some a) := by
  have h := spec.singleLaw.tsum_coe
  rw [tsum_option_eq, add_comm] at h
  exact (ENNReal.eq_sub_of_add_eq spec.rejectProb_ne_top h).symm

/-- Decode at most `trials` consecutive `width`-bit blocks from `bits`, returning the first
accepted value or `none`. -/
@[expose] def decodeTrials (spec : BlockRejectionSpec α) : ℕ → List Bool → Option α
  | 0, _ => none
  | t + 1, bits =>
    match spec.attempt (bits.take spec.width) with
    | some a => some a
    | none => spec.decodeTrials t (bits.drop spec.width)

@[simp]
theorem decodeTrials_zero (spec : BlockRejectionSpec α) (bits : List Bool) :
    spec.decodeTrials 0 bits = none :=
  rfl

theorem decodeTrials_succ (spec : BlockRejectionSpec α) (t : ℕ) (bits : List Bool) :
    spec.decodeTrials (t + 1) bits =
      match spec.attempt (bits.take spec.width) with
      | some a => some a
      | none => spec.decodeTrials t (bits.drop spec.width) :=
  rfl

theorem decodeTrials_append_of_some {spec : BlockRejectionSpec α} {t : ℕ} {w : List Bool} {a : α}
    (hw : t * spec.width ≤ w.length) (h : spec.decodeTrials t w = some a) (v : List Bool) :
    spec.decodeTrials t (w ++ v) = some a := by
  induction t generalizing w with
  | zero => simp at h
  | succ t ih =>
    rw [Nat.succ_mul] at hw
    have hw1 : spec.width ≤ w.length := by omega
    rw [decodeTrials_succ, List.take_append_of_le_length hw1, List.drop_append_of_le_length hw1]
    rw [decodeTrials_succ] at h
    cases hatt : spec.attempt (w.take spec.width) <;> rw [hatt] at h
    · exact ih (by rw [List.length_drop]; omega) h
    · exact h

theorem decodeTrials_mono_of_some {spec : BlockRejectionSpec α} {t t' : ℕ} {w : List Bool} {a : α}
    (htt : t ≤ t') (h : spec.decodeTrials t w = some a) :
    spec.decodeTrials t' w = some a := by
  induction t generalizing t' w with
  | zero => simp at h
  | succ t ih =>
    obtain ⟨k, rfl⟩ : ∃ k, t' = k + 1 := ⟨t' - 1, by omega⟩
    rw [decodeTrials_succ] at h ⊢
    cases hatt : spec.attempt (w.take spec.width) <;> rw [hatt] at h
    · exact ih (by omega) h
    · exact h

theorem decodeTrials_take (spec : BlockRejectionSpec α) (t : ℕ) (w : List Bool) :
    spec.decodeTrials t (w.take (t * spec.width)) = spec.decodeTrials t w := by
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    have hle : spec.width ≤ (t + 1) * spec.width := by rw [Nat.succ_mul]; omega
    rw [decodeTrials_succ, decodeTrials_succ, List.take_take, Nat.min_eq_left hle,
      List.drop_take, Nat.succ_mul, Nat.add_sub_cancel]
    cases spec.attempt (w.take spec.width) with
    | some a => rfl
    | none => exact ih (w.drop spec.width)

/-- Post-composing a single-block decoder with `Option.map f` commutes with `decodeTrials`. -/
theorem decodeTrials_map {β : Type*} (spec : BlockRejectionSpec α) (f : α → β)
    (spec' : BlockRejectionSpec β) (hw : spec'.width = spec.width)
    (ha : ∀ bits, spec'.attempt bits = (spec.attempt bits).map f) :
    ∀ (t : ℕ) (bits : List Bool),
      spec'.decodeTrials t bits = (spec.decodeTrials t bits).map f
  | 0, _ => rfl
  | t + 1, bits => by
    rw [decodeTrials_succ, decodeTrials_succ, hw, ha]
    cases spec.attempt (bits.take spec.width) with
    | none => exact decodeTrials_map spec f spec' hw ha t (bits.drop spec.width)
    | some a => rfl

/-- Distribution of running at most `trials` independent `width`-bit blocks. -/
@[expose] noncomputable def runTrials (spec : BlockRejectionSpec α) (trials : ℕ) :
    PMF (Option α) :=
  (BitString.uniformList (trials * spec.width)).map (spec.decodeTrials trials)

@[simp]
theorem runTrials_zero (spec : BlockRejectionSpec α) :
    spec.runTrials 0 = PMF.pure none := by
  simp [runTrials, decodeTrials]

theorem runTrials_succ (spec : BlockRejectionSpec α) (t : ℕ) :
    spec.runTrials (t + 1) =
      spec.singleLaw.bind fun o =>
        match o with
        | some a => PMF.pure (some a)
        | none => spec.runTrials t := by
  unfold runTrials singleLaw
  rw [show (t + 1) * spec.width = spec.width + t * spec.width by rw [Nat.succ_mul, Nat.add_comm]]
  refine (BitString.uniformList_bind_split spec.width (t * spec.width)
    (fun front rest => PMF.pure (match spec.attempt front with
      | some a => some a
      | none => spec.decodeTrials t rest))).trans ?_
  rw [PMF.bind_map]
  congr 1
  funext front
  dsimp only [Function.comp_apply]
  cases spec.attempt front <;> simp [PMF.bind_const, PMF.map, Function.comp_def]

/-- Failure probability after `t` trials is `rejectProb ^ t`. -/
theorem runTrials_none (spec : BlockRejectionSpec α) (t : ℕ) :
    spec.runTrials t none = spec.rejectProb ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [runTrials_succ, PMF.bind_apply, tsum_option_eq,
      tsum_eq_zero_iff.mpr fun a => by simp, add_zero, ih, pow_succ']
    rfl

/-- Accepted outcome mass after `t` trials. -/
theorem runTrials_some (spec : BlockRejectionSpec α) (t : ℕ) (a : α) :
    spec.runTrials t (some a) =
      spec.singleLaw (some a) * ∑ j ∈ Finset.range t, spec.rejectProb ^ j := by
  induction t with
  | zero => simp
  | succ t ih =>
    classical
    rw [runTrials_succ, PMF.bind_apply, tsum_option_eq, ih, geom_sum_succ]
    have hsome : ∑' b : α, spec.singleLaw (some b) *
        (PMF.pure (some b) : PMF (Option α)) (some a) = spec.singleLaw (some a) :=
      (tsum_eq_single a fun b hb => by simp [hb.symm]).trans (by simp)
    rw [hsome]
    change spec.rejectProb * (spec.singleLaw (some a) * ∑ j ∈ Finset.range t, spec.rejectProb ^ j) +
      spec.singleLaw (some a) = _
    ring

private theorem mul_geom_sum_eq_one_sub_pow {r : ℝ≥0∞} (hr : r ≤ 1) (t : ℕ) :
    (1 - r) * ∑ j ∈ Finset.range t, r ^ j = 1 - r ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hpow : r ^ t ≤ 1 := pow_le_one₀ zero_le hr
    rw [Finset.sum_range_succ, mul_add, ih, ENNReal.sub_mul fun _ _ =>
      ne_top_of_le_ne_top ENNReal.one_ne_top hpow, one_mul, ← pow_succ']
    exact tsub_add_tsub_cancel hpow (pow_le_pow_of_le_one zero_le hr t.le_succ)

/-- When a single trial outputs `some a` with probability `acceptProb * target a`, `t` trials
output `some a` with probability `(1 - rejectProb ^ t) * target a`. -/
theorem runTrials_some_of_singleLaw {spec : BlockRejectionSpec α} {target : PMF α}
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a) (t : ℕ) (a : α) :
    spec.runTrials t (some a) = (1 - spec.rejectProb ^ t) * target a := by
  rw [runTrials_some, h a, mul_right_comm, acceptProb,
    mul_geom_sum_eq_one_sub_pow spec.rejectProb_le_one t]

/-- Capped `t`-trial sampler substituting `fallback` if all `t` blocks reject. -/
@[expose] noncomputable def runCapped (spec : BlockRejectionSpec α) (fallback : α) (t : ℕ) :
    PMF α :=
  (spec.runTrials t).map fun o => o.getD fallback

theorem runCapped_apply [DecidableEq α] {spec : BlockRejectionSpec α} {target : PMF α}
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a)
    (fallback : α) (t : ℕ) (a : α) :
    spec.runCapped fallback t a =
      (1 - spec.rejectProb ^ t) * target a +
        if a = fallback then spec.rejectProb ^ t else 0 := by
  classical
  rw [runCapped, PMF.map_apply, tsum_option_eq]
  simp only [Option.getD_none, Option.getD_some, runTrials_none]
  rw [tsum_eq_single a fun b hb => by simp [hb.symm]]
  simp only [↓reduceIte, runTrials_some_of_singleLaw h t a, add_comm]

/-- Statistical distance between the capped fallback sampler and the target distribution is
`(rejectProb ^ t).toReal * (1 - (target fallback).toReal)`, hence at most
`(rejectProb ^ t).toReal`. -/
theorem dist_runCapped_eq [Fintype α] {spec : BlockRejectionSpec α} {target : PMF α}
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a)
    (fallback : α) (t : ℕ) :
    dist (spec.runCapped fallback t) target =
      (spec.rejectProb ^ t).toReal * (1 - (target fallback).toReal) := by
  classical
  set r := spec.rejectProb ^ t with hr
  -- `ennreal_to_real` splits `(1 - r).toReal` with `hr1`.
  have hr1 : r ≤ 1 := pow_le_one₀ zero_le spec.rejectProb_le_one
  have hval (a : α) : (spec.runCapped fallback t a).toReal =
      (1 - r.toReal) * (target a).toReal + if a = fallback then r.toReal else 0 := by
    rw [runCapped_apply h fallback t a, ← hr]
    split_ifs <;> ennreal_to_real
  -- Completing the sampler scales each deviation from the target by the failure mass.
  have hsub (a : α) : (spec.runCapped fallback t a).toReal - (target a).toReal =
      r.toReal * (((PMF.pure fallback) a).toReal - (target a).toReal) := by
    rw [hval, PMF.pure_apply]
    split_ifs <;> simp only [ENNReal.toReal_one, ENNReal.toReal_zero] <;> ring
  calc
    _ = r.toReal * dist (PMF.pure fallback) target := by
      rw [PMF.dist_eq, PMF.dist_eq]
      simp only [hsub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, ← Finset.mul_sum]
      ring
    _ = _ := by rw [PMF.dist_pure_left]

theorem dist_runCapped_le [Fintype α] {spec : BlockRejectionSpec α} {target : PMF α}
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a)
    (fallback : α) (t : ℕ) :
    dist (spec.runCapped fallback t) target ≤ (spec.rejectProb ^ t).toReal := by
  rw [dist_runCapped_eq h fallback t]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (sub_le_self _ ENNReal.toReal_nonneg)

/-- Without any `Fintype` assumption, `spec.runCapped fallback t` lies within `CloseTo` statistical
distance `spec.rejectProb ^ t` of `target`. -/
theorem closeTo_runCapped {α : Type} {spec : BlockRejectionSpec α} {target : PMF α}
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a)
    (fallback : α) (t : ℕ) :
    CloseTo (spec.runCapped fallback t) target (spec.rejectProb ^ t) := by
  classical
  refine CloseTo.of_one_sub_mul_le fun a => ?_
  rw [← spec.runTrials_some_of_singleLaw h t a, runCapped, PMF.map_apply]
  exact le_trans (by simp) (le_tsum _ (some a))

/-! ### Unbounded `DDGTree` realization -/

/-- Exact discrete distribution generating tree executing `spec` on consecutive `width`-bit
blocks. -/
@[expose] def toDDGTree (spec : BlockRejectionSpec α) : DDGTree α where
  output w := spec.decodeTrials (w.length / spec.width) w
  output_append_singleton w a b h := by
    have hw : (w.length / spec.width) * spec.width ≤ w.length :=
      Nat.div_mul_le_self w.length spec.width
    have happ := decodeTrials_append_of_some hw h [b]
    have hle : w.length / spec.width ≤ (w ++ [b]).length / spec.width := by gcongr; simp
    exact decodeTrials_mono_of_some hle happ

/-- Running `toDDGTree` on `n` fair bits has the exact law of `n / width` rejection trials. -/
theorem run_toDDGTree (spec : BlockRejectionSpec α) (n : ℕ) :
    spec.toDDGTree.run n = spec.runTrials (n / spec.width) := by
  unfold DDGTree.run runTrials
  rw [← BitString.uniformList_take (Nat.div_mul_le_self n spec.width), PMF.map_comp]
  apply PMF.map_congr_on_support
  intro w hw
  dsimp only [toDDGTree, Function.comp_apply]
  rw [BitString.length_of_mem_support_uniformList hw, decodeTrials_take]

/-- If `0 < width`, `acceptProb ≠ 0`, and accepted trials follow `target`, `toDDGTree` generates
`target` exactly. -/
theorem toDDGTree_generates {spec : BlockRejectionSpec α} {target : PMF α}
    (hw : 0 < spec.width) (hacc : spec.acceptProb ≠ 0)
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a) :
    spec.toDDGTree.Generates target := by
  intro a
  apply le_antisymm
  · refine iSup_le fun n => ?_
    rw [run_toDDGTree, runTrials_some_of_singleLaw h]
    exact mul_le_of_le_one_left' tsub_le_self
  · have hr_lt : spec.rejectProb < 1 := spec.rejectProb_lt_one_iff.mpr hacc
    have hpow : Tendsto (fun t : ℕ => spec.rejectProb ^ t) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr_lt
    have hsub : Tendsto (fun t : ℕ => (1 - spec.rejectProb ^ t) * target a) atTop
        (𝓝 ((1 - 0) * target a)) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr (PMF.apply_ne_top target a))
      exact ENNReal.Tendsto.sub tendsto_const_nhds hpow (Or.inr ENNReal.zero_ne_top)
    rw [tsub_zero, one_mul] at hsub
    refine le_of_tendsto' hsub fun t => ?_
    have := spec.toDDGTree.run_le_outputProb (t * spec.width) a
    rwa [run_toDDGTree, Nat.mul_div_cancel t hw, runTrials_some_of_singleLaw h] at this

/-- Closed-form expected fair-bit cost of `toDDGTree`: `(width : ℝ≥0∞) / acceptProb` whenever
`0 < width` (including `⊤` when `acceptProb = 0`). -/
theorem expectedFlips_toDDGTree (spec : BlockRejectionSpec α) (hw : 0 < spec.width) :
    spec.toDDGTree.expectedFlips = (spec.width : ℝ≥0∞) / spec.acceptProb := by
  unfold DDGTree.expectedFlips
  simp_rw [run_toDDGTree, runTrials_none]
  have : NeZero spec.width := ⟨hw.ne'⟩
  rw [← (Nat.divModEquiv spec.width).symm.tsum_eq]
  have hdiv (p : ℕ × Fin spec.width) : (Nat.divModEquiv spec.width).symm p / spec.width = p.1 := by
    rw [Nat.divModEquiv_symm_apply, Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt p.2.isLt,
      Nat.add_zero]
  simp_rw [hdiv]
  rw [tsum_prod']
  simp_rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← one_sub_rejectProb, div_eq_mul_inv]

/-- When `0 < width` and `1 / 2 ≤ acceptProb`, `toDDGTree` reads at most `2 * width` fair bits in
expectation. -/
theorem expectedFlips_toDDGTree_le_two_mul {spec : BlockRejectionSpec α}
    (hw : 0 < spec.width) (hacc : (1 / 2 : ℝ≥0∞) ≤ spec.acceptProb) :
    spec.toDDGTree.expectedFlips ≤ 2 * (spec.width : ℝ≥0∞) := by
  rw [expectedFlips_toDDGTree spec hw, div_eq_mul_inv]
  exact (mul_le_mul_right ((ENNReal.inv_le_inv.mpr hacc).trans_eq (by rw [one_div, inv_inv]))
    _).trans_eq (mul_comm _ _)

private theorem runTrials_none_le_of_one_half_le {spec : BlockRejectionSpec α}
    (hacc : (1 / 2 : ℝ≥0∞) ≤ spec.acceptProb) (t : ℕ) :
    spec.runTrials t none ≤ (1 / 2 : ℝ≥0∞) ^ t := by
  rw [spec.runTrials_none]
  refine pow_le_pow_left' ?_ t
  calc
    spec.rejectProb = 1 - spec.acceptProb :=
      (ENNReal.sub_sub_cancel ENNReal.one_ne_top spec.rejectProb_le_one).symm
    _ ≤ 1 - 1 / 2 := tsub_le_tsub_left hacc 1
    _ = 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]

end BlockRejectionSpec

private theorem div_div_natCast {w c d : ℕ} (hc : c ≠ 0) :
    (w : ℝ≥0∞) / ((c : ℝ≥0∞) / (d : ℝ≥0∞)) = (w : ℝ≥0∞) * (d : ℝ≥0∞) / c := by
  rw [← ENNReal.div_mul _ (Or.inl (Nat.cast_ne_zero.mpr hc)) (Or.inr (ENNReal.natCast_ne_top _)),
    div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]

/-! ### Bounded integers (`Fin n`) -/

/-- Block-rejection specification for `Fin n` reading `k` bits per trial and keeping binary values
strictly below `n`. -/
@[expose] def finCutoffSpec (n k : ℕ) : BlockRejectionSpec (Fin n) where
  width := k
  attempt w := Fin.ofNat? n (BitString.binaryValue w)

/-- Exact block-rejection specification for `Fin n` reading `Nat.clog 2 n` bits per trial. -/
@[expose] def uniformFinRejectionSpec (n : ℕ) : BlockRejectionSpec (Fin n) :=
  finCutoffSpec n (Nat.clog 2 n)

/-- Dyadic bounded-integer rejection specification reading `Nat.log 2 n + 1` bits per trial
(`2 ^ width = dyadicSize n`), matching `UniformNat.dyadicSize`. -/
@[expose] def dyadicFinRejectionSpec (n : ℕ) : BlockRejectionSpec (Fin n) :=
  finCutoffSpec n (Nat.log 2 n + 1)

private theorem singleLaw_finCutoffSpec_some {n k : ℕ} (hnk : n ≤ 2 ^ k) (i : Fin n) :
    (finCutoffSpec n k).singleLaw (some i) = ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := by
  let f : ℕ → Option (Fin n) := Fin.ofNat? n
  change ((BitString.uniformList k).map (f ∘ BitString.binaryValue)) (some i) = _
  rw [← PMF.map_comp, BitString.uniformList_binaryValue, PMF.map_comp, PMF.map_apply,
    tsum_fintype, Finset.sum_eq_single ⟨i.val, i.isLt.trans_le hnk⟩]
  · simp [f, i.isLt, PMF.uniformOfFintype_apply]
  · intro j _ hj
    refine ite_eq_right fun heq => hj (Fin.ext ?_)
    simp only [Function.comp_apply, f, Fin.ofNat?] at heq
    split_ifs at heq
    exact (congrArg Fin.val (Option.some.inj heq)).symm
  · simp

private theorem acceptProb_finCutoffSpec {n k : ℕ} (hnk : n ≤ 2 ^ k) :
    (finCutoffSpec n k).acceptProb = (n : ℝ≥0∞) / ((2 ^ k : ℕ) : ℝ≥0∞) := by
  rw [BlockRejectionSpec.acceptProb_eq_tsum_some, tsum_fintype]
  simp_rw [singleLaw_finCutoffSpec_some hnk]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]

private theorem one_half_le_acceptProb_finCutoffSpec {n k : ℕ} (hnk : n ≤ 2 ^ k)
    (hpow : 2 ^ k ≤ 2 * n) :
    (1 / 2 : ℝ≥0∞) ≤ (finCutoffSpec n k).acceptProb := by
  rw [acceptProb_finCutoffSpec hnk,
    ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _))]
  calc
    (1 / 2 : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0∞) * ((2 * n : ℕ) : ℝ≥0∞) := by gcongr
    _ = (n : ℝ≥0∞) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc, one_div,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

private theorem singleLaw_finCutoffSpec_eq_mul {n k : ℕ} [NeZero n] (hnk : n ≤ 2 ^ k) (i : Fin n) :
    (finCutoffSpec n k).singleLaw (some i) =
      (finCutoffSpec n k).acceptProb * PMF.uniformOfFintype (Fin n) i := by
  rw [acceptProb_finCutoffSpec hnk, PMF.uniformOfFintype_apply, Fintype.card_fin,
    div_eq_mul_inv, mul_right_comm,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top n),
    one_mul]
  exact singleLaw_finCutoffSpec_some hnk i

theorem acceptProb_uniformFinRejectionSpec (n : ℕ) :
    (uniformFinRejectionSpec n).acceptProb = (n : ℝ≥0∞) / ((2 ^ Nat.clog 2 n : ℕ) : ℝ≥0∞) :=
  acceptProb_finCutoffSpec (Nat.le_pow_clog Nat.one_lt_two n)

theorem singleLaw_uniformFinRejectionSpec_some (n : ℕ) [NeZero n] (i : Fin n) :
    (uniformFinRejectionSpec n).singleLaw (some i) =
      (uniformFinRejectionSpec n).acceptProb * PMF.uniformOfFintype (Fin n) i :=
  singleLaw_finCutoffSpec_eq_mul (Nat.le_pow_clog Nat.one_lt_two n) i

theorem one_half_le_acceptProb_uniformFinRejectionSpec (n : ℕ) [NeZero n] :
    (1 / 2 : ℝ≥0∞) ≤ (uniformFinRejectionSpec n).acceptProb := by
  refine one_half_le_acceptProb_finCutoffSpec (Nat.le_pow_clog Nat.one_lt_two n) ?_
  by_cases hn1 : n ≤ 1
  · obtain rfl : n = 1 := by have := NeZero.pos n; omega
    simp
  · have hclog : Nat.clog 2 n ≤ Nat.log 2 (n - 1) + 1 := by
      rw [Nat.clog_le_iff_le_pow Nat.one_lt_two]
      have := Nat.lt_pow_succ_log_self Nat.one_lt_two (n - 1)
      omega
    have hle1 : 2 ^ Nat.clog 2 n ≤ 2 ^ Nat.log 2 (n - 1) * 2 :=
      pow_succ 2 (Nat.log 2 (n - 1)) ▸ Nat.pow_le_pow_right (by decide) hclog
    have := Nat.pow_log_le_self 2 (x := n - 1) (by omega)
    omega

/-- After `t` trials of `uniformFinRejectionSpec n` (`n ≥ 1`), rejection probability is at most
`(1 / 2) ^ t`. -/
theorem runTrials_uniformFinRejectionSpec_none_le (n : ℕ) [NeZero n] (t : ℕ) :
    (uniformFinRejectionSpec n).runTrials t none ≤ (1 / 2 : ℝ≥0∞) ^ t :=
  BlockRejectionSpec.runTrials_none_le_of_one_half_le
    (one_half_le_acceptProb_uniformFinRejectionSpec n) t

/-- Root-leaf `DDGTree` outputting `0 : Fin n` without flipping any fair bits. -/
@[expose] def constZeroFinTree (n : ℕ) [NeZero n] : DDGTree (Fin n) where
  output _ := some ⟨0, NeZero.pos n⟩
  output_append_singleton _ _ _ h := h

private theorem expectedFlips_constZeroFinTree (n : ℕ) [NeZero n] :
    (constZeroFinTree n).expectedFlips = 0 := by
  simp [DDGTree.expectedFlips, DDGTree.run_eq_pure_of_output_nil (T := constZeroFinTree n) rfl]

/-- Exact `DDGTree` generating the uniform distribution on `Fin n`: `0` flips at `n = 1` and
`Nat.clog 2 n`-bit block rejection for `n ≥ 2`. -/
@[expose] def uniformFinTree (n : ℕ) [NeZero n] : DDGTree (Fin n) :=
  if n = 1 then constZeroFinTree n else (uniformFinRejectionSpec n).toDDGTree

theorem uniformFinTree_generates (n : ℕ) [NeZero n] :
    (uniformFinTree n).Generates (PMF.uniformOfFintype (Fin n)) := by
  unfold uniformFinTree
  split_ifs with hn1
  · subst hn1
    intro i
    obtain rfl : i = ⟨0, NeZero.pos 1⟩ := Subsingleton.elim _ _
    simp [DDGTree.outputProb, DDGTree.run_eq_pure_of_output_nil (T := constZeroFinTree 1) rfl,
      PMF.uniformOfFintype_apply]
  · exact BlockRejectionSpec.toDDGTree_generates
      (Nat.clog_pos Nat.one_lt_two (by have := NeZero.pos n; omega))
      (ne_of_gt (lt_of_lt_of_le (by norm_num) (one_half_le_acceptProb_uniformFinRejectionSpec n)))
      (singleLaw_uniformFinRejectionSpec_some n)

theorem expectedFlips_uniformFinTree_of_two_le {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (uniformFinTree n).expectedFlips =
      (Nat.clog 2 n : ℝ≥0∞) * ((2 ^ Nat.clog 2 n : ℕ) : ℝ≥0∞) / n := by
  unfold uniformFinTree
  rw [ite_eq_right (by omega), BlockRejectionSpec.expectedFlips_toDDGTree _
      (Nat.clog_pos Nat.one_lt_two (by omega : 1 < n)),
    acceptProb_uniformFinRejectionSpec]
  exact div_div_natCast (by omega)

/-- At any power of two `2 ^ k`, `uniformFinTree (2 ^ k)` reads `k` fair bits in expectation,
attaining the Knuth–Yao entropy lower bound. -/
theorem expectedFlips_uniformFinTree_two_pow (k : ℕ) :
    (uniformFinTree (2 ^ k)).expectedFlips = k := by
  cases k with
  | zero =>
    unfold uniformFinTree
    rw [ite_eq_left (by simp : 2 ^ 0 = 1), Nat.cast_zero]
    exact expectedFlips_constZeroFinTree _
  | succ k =>
    rw [expectedFlips_uniformFinTree_of_two_le (Nat.le_self_pow k.succ_ne_zero 2),
      Nat.clog_pow _ _ Nat.one_lt_two,
      ENNReal.mul_div_cancel_right (by positivity) (ENNReal.natCast_ne_top _)]

/-- For every `n ≥ 1`, `uniformFinTree n` reads at most `2 * Nat.clog 2 n` fair bits in
expectation. -/
theorem expectedFlips_uniformFinTree_le (n : ℕ) [NeZero n] :
    (uniformFinTree n).expectedFlips ≤ 2 * (Nat.clog 2 n : ℝ≥0∞) := by
  unfold uniformFinTree
  split_ifs with hn1
  · simp [expectedFlips_constZeroFinTree]
  · exact BlockRejectionSpec.expectedFlips_toDDGTree_le_two_mul
      (Nat.clog_pos Nat.one_lt_two (by have := NeZero.pos n; omega))
      (one_half_le_acceptProb_uniformFinRejectionSpec n)

theorem singleLaw_dyadicFinRejectionSpec_some (n : ℕ) [NeZero n] (i : Fin n) :
    (dyadicFinRejectionSpec n).singleLaw (some i) =
      (dyadicFinRejectionSpec n).acceptProb * PMF.uniformOfFintype (Fin n) i :=
  singleLaw_finCutoffSpec_eq_mul (lt_dyadicSize n).le i

theorem dyadicFinRejectionSpec_generates (n : ℕ) [NeZero n] :
    (dyadicFinRejectionSpec n).toDDGTree.Generates (PMF.uniformOfFintype (Fin n)) := by
  have hacc : (dyadicFinRejectionSpec n).acceptProb ≠ 0 := by
    rw [dyadicFinRejectionSpec, acceptProb_finCutoffSpec (lt_dyadicSize n).le]
    exact ENNReal.div_ne_zero.mpr ⟨Nat.cast_ne_zero.mpr (NeZero.ne n), ENNReal.natCast_ne_top _⟩
  exact BlockRejectionSpec.toDDGTree_generates (Nat.succ_pos (Nat.log 2 n)) hacc
    (singleLaw_dyadicFinRejectionSpec_some n)

theorem runTrials_dyadicFinRejectionSpec_none_le (n : ℕ) [NeZero n] (t : ℕ) :
    (dyadicFinRejectionSpec n).runTrials t none ≤ (1 / 2 : ℝ≥0∞) ^ t := by
  refine BlockRejectionSpec.runTrials_none_le_of_one_half_le
    (one_half_le_acceptProb_finCutoffSpec (lt_dyadicSize n).le ?_) t
  have h1 := Nat.pow_log_le_self 2 (NeZero.ne n)
  rw [pow_succ]
  omega

/-! ### Subset rejection sampling -/

/-- Exact dyadic block-rejection sampler for a subset `S : Finset α` inside an indexed range
`enum : Fin m → α`. -/
@[expose] def subsetDyadicSpec {α : Type*} [DecidableEq α] (m : ℕ) (enum : Fin m → α)
    (S : Finset α) : BlockRejectionSpec α where
  width := Nat.log 2 m + 1
  attempt w :=
    if h : BitString.binaryValue w < m then
      let a := enum ⟨BitString.binaryValue w, h⟩
      if a ∈ S then some a else none
    else none

private theorem singleLaw_subsetDyadicSpec_some {α : Type*} [DecidableEq α] {m : ℕ}
    {enum : Fin m → α} (hinj : Function.Injective enum) {S : Finset α}
    (hcov : ∀ a ∈ S, ∃ i : Fin m, enum i = a) (a : α) :
    (subsetDyadicSpec m enum S).singleLaw (some a) =
      if a ∈ S then ((dyadicSize m : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  have hmk : m ≤ 2 ^ (Nat.log 2 m + 1) := (lt_dyadicSize m).le
  let g : ℕ → Option α := fun v =>
    if h : v < m then (if enum ⟨v, h⟩ ∈ S then some (enum ⟨v, h⟩) else none) else none
  change ((BitString.uniformList (Nat.log 2 m + 1)).map (g ∘ BitString.binaryValue)) (some a) = _
  rw [← PMF.map_comp, BitString.uniformList_binaryValue, PMF.map_comp, PMF.map_apply,
    tsum_fintype]
  split_ifs with haS
  · obtain ⟨i, rfl⟩ := hcov a haS
    rw [Finset.sum_eq_single ⟨i.val, i.isLt.trans_le hmk⟩]
    · simp [g, i.isLt, haS, PMF.uniformOfFintype_apply, dyadicSize]
    · intro j _ hj
      refine ite_eq_right fun heq => hj (Fin.ext ?_)
      simp only [Function.comp_apply, g] at heq
      split_ifs at heq with hlt hmS
      exact (congrArg Fin.val (hinj (Option.some.inj heq))).symm
    · simp
  · refine Finset.sum_eq_zero fun j _ => ite_eq_right fun heq => ?_
    simp only [Function.comp_apply, g] at heq
    split_ifs at heq with hlt hmS
    exact haS (Option.some.inj heq ▸ hmS)

theorem acceptProb_subsetDyadicSpec {α : Type*} [DecidableEq α] {m : ℕ} {enum : Fin m → α}
    (hinj : Function.Injective enum) {S : Finset α}
    (hcov : ∀ a ∈ S, ∃ i : Fin m, enum i = a) :
    (subsetDyadicSpec m enum S).acceptProb =
      (S.card : ℝ≥0∞) / ((dyadicSize m : ℕ) : ℝ≥0∞) := by
  rw [BlockRejectionSpec.acceptProb_eq_tsum_some]
  simp_rw [singleLaw_subsetDyadicSpec_some hinj hcov]
  rw [tsum_eq_sum (s := S) fun a ha => by simp [ha], Finset.sum_ite_mem, Finset.inter_self,
    Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem subsetDyadicSpec_generates {α : Type*} [DecidableEq α] {m : ℕ} {enum : Fin m → α}
    (hinj : Function.Injective enum) {S : Finset α} (hS : S.Nonempty)
    (hcov : ∀ a ∈ S, ∃ i : Fin m, enum i = a) :
    (subsetDyadicSpec m enum S).toDDGTree.Generates (PMF.uniformOfFinset S hS) := by
  have hacc_eq := acceptProb_subsetDyadicSpec hinj hcov
  have hacc : (subsetDyadicSpec m enum S).acceptProb ≠ 0 := by
    rw [hacc_eq]
    exact ENNReal.div_ne_zero.mpr
      ⟨Nat.cast_ne_zero.mpr hS.card_ne_zero, ENNReal.natCast_ne_top _⟩
  refine BlockRejectionSpec.toDDGTree_generates (Nat.succ_pos (Nat.log 2 m)) hacc fun a => ?_
  rw [singleLaw_subsetDyadicSpec_some hinj hcov a, hacc_eq, PMF.uniformOfFinset_apply]
  split_ifs with haS
  · rw [div_eq_mul_inv, mul_right_comm,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hS.card_ne_zero) (ENNReal.natCast_ne_top _),
      one_mul]
  · rw [mul_zero]

theorem expectedFlips_subsetDyadicSpec {α : Type*} [DecidableEq α] {m : ℕ} {enum : Fin m → α}
    (hinj : Function.Injective enum) {S : Finset α} (hS : S.Nonempty)
    (hcov : ∀ a ∈ S, ∃ i : Fin m, enum i = a) :
    (subsetDyadicSpec m enum S).toDDGTree.expectedFlips =
      ((Nat.log 2 m + 1 : ℕ) : ℝ≥0∞) * ((dyadicSize m : ℕ) : ℝ≥0∞) / S.card := by
  rw [BlockRejectionSpec.expectedFlips_toDDGTree _ (Nat.succ_pos (Nat.log 2 m)),
    acceptProb_subsetDyadicSpec hinj hcov]
  exact div_div_natCast hS.card_ne_zero

end Cslib.Probability
