/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Crypto.Computational.Lattice.GIVP
public import CslibFrontier.Crypto.Computational.Lattice.MR07Shorten
public import CslibFrontier.Crypto.Computational.SIS.Basic
public import CslibFrontier.Crypto.Computational.SIS.Ell2
public import CslibFrontier.Crypto.Computational.SIS.MR07Core
public import CslibFrontier.Crypto.Computational.SIS.MR07Reduction.IncGDD
public import CslibFrontier.Crypto.Computational.SIS.MR07Reduction.Shorten
public import CslibFrontier.Foundations.Data.Matrix.RowTable
public import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter

import CslibFrontier.Algorithms.LatticeReduction.Potential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Probability.PMF.Event
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Log

/-!
# Strict-PPT `GIVP` Reduction from `ℓ₂`-SIS (Micciancio–Regev Finite-Parameter Step)

This module assembles the full finite-parameter strict probabilistic polynomial-time (`IsPPTOn`)
basis-shortening reduction from worst-case `GIVP^{η_ε}_{8 β √n}` on full-rank integer lattice
bases to average-case `ℓ₂`-SIS, providing the finite-parameter reduction step toward
`[MicciancioRegev2007]` Theorem 5.9, Lemma 5.10, and Corollary 5.13 (see tracking issue #6861 for
the asymptotic worst-case hardness endpoints).

Re-exports `CslibFrontier.Crypto.Computational.SIS.MR07Reduction.Shorten` and
`CslibFrontier.Crypto.Computational.SIS.MR07Reduction.IncGDD`.

## Main definitions

* `Cslib.Crypto.SIS.MR07.GIVPInput`, `GIVPInput.enc`: structured input `(secParam, basisB)` and
  framing encoding for worst-case lattice basis solvers.
* `Cslib.Crypto.SIS.MR07.mr07ErrBits`, `mr07Prec`, `mr07MaxTrials`, `mr07AmpTrials`, `mr07Eps`:
  explicit unary/real error-budget schedules parameterized by `(n, m, β, κ, c, R)`.
* `Cslib.Crypto.SIS.MR07.mr07GIVPShortenStep`, `Cslib.Crypto.SIS.MR07.mr07GIVPReduction`:
  guarded strict-PPT basis-shortening loop (`OracleComp.iterate`) composing
  `ratOrthoTargetIntTable`, `mr07IncGDDReduction`, and `guardedUpdateIntTable`.

## Main results

* `Cslib.Crypto.SIS.MR07.computableInPolyTime_mr07GIVPSchedules`: polynomial-time computability of
  all five unary parameter schedules from `GIVPInput.enc`.
* `Cslib.Crypto.SIS.MR07.mr07_hprec_ok`, `mr07_singleCall_eta_le`, `mr07_singleCall_succProb_ge`,
  `mr07_amp_round_failure_le`, `mr07_total_succProb_ge`: closed quantitative error-budget and
  amplification inequalities.
* `Cslib.Crypto.SIS.MR07.isPPTOn_mr07GIVPReduction`: unconditional strict-PPT certificate via
  `IsPPTOn.iterateWith_spec` with the disjunctive malformed-input and bounded-column-norm invariant.
* `Cslib.Crypto.SIS.MR07.mr07GIVPReduction_succProb_ge`, `mr07GIVPReduction_succProb_ge_half`:
  finite-parameter `GIVP` success probability lower bound `≥ 1 - (1 / 4) * 2 ^ (-κ) ≥ 1 / 2`
  (step toward `[MicciancioRegev2007]` Lemma 5.10 and Corollary 5.13).
-/

public section

namespace Cslib.Crypto.SIS.MR07

open Cslib Cslib.Crypto Cslib.Crypto.SIS Cslib.LinearAlgebra Cslib.Probability Cslib.ProbComp
open Turing.MultiTapeTM ComputableInPolyTime ProbabilityTheory ZLattice
open scoped IntTable IncGDDInput BigOperators ENNReal NNReal RealInnerProductSpace _root_.Matrix

attribute [local irreducible] encRat encIntBin encNat IntTable.enc IncGDDInput.enc

/-! ### 1. `GIVPInput` & Explicit Error-Budget Schedules -/

/-- Input to the strict-PPT `GIVP` reduction (finite step toward `[MicciancioRegev2007]`
Lemma 5.10 and Corollary 5.13): unary security parameter `secParam` and row-major full-rank
integer lattice basis `basisB`. -/
structure GIVPInput where
  /-- Security parameter (encoded in unary). -/
  secParam : ℕ
  /-- Row-major integer basis matrix whose columns generate `intLattice B`. -/
  basisB : IntTable
  deriving DecidableEq, Repr

namespace GIVPInput

/-- Framing encoding of `GIVPInput`. -/
enc_structure enc : GIVPInput where
  secParam : encUnary,
  basisB : IntTable.enc

end GIVPInput

attribute [local irreducible] GIVPInput.enc
open scoped GIVPInput

/-- Unary error-bit parameter `L_err = ⌈log₂(48 m² n β (κ + 1)^c + 1)⌉ + 2` used for both
`tail` and `extraBits`. -/
def mr07ErrBits (n m β κ c : ℕ) : ℕ :=
  Nat.clog 2 (48 * m ^ 2 * n * β * (κ + 1) ^ c + 1) + 2

/-- Unary dyadic acceptance-coin precision `prec` passed to `sampleGridGaussian`. -/
def mr07Prec (n m β κ c : ℕ) : ℕ :=
  let tail := mr07ErrBits n m β κ c
  Nat.clog 2 (48 * m ^ 2 * n * β * (κ + 1) ^ c * (8 * tail + 24) + 1) + 4

/-- Unary rejection-trial cap `maxTrials = 16 * (2 * tail + 6) * tail` for `sampleGridGaussian`. -/
def mr07MaxTrials (n m β κ c : ℕ) : ℕ :=
  let tail := mr07ErrBits n m β κ c
  16 * (2 * tail + 6) * tail

/-- Unary amplification trial count `T_amp` per shortening round. -/
def mr07AmpTrials (m β κ c R : ℕ) : ℕ :=
  12 * (2 * β * m) * (κ + 1) ^ c * (κ + Nat.clog 2 (R + 1) + 2)

/-- Target smoothing-parameter accuracy `ε = 1 / (400 β m² (κ + 1)^c)` for `mr07GIVPReduction`. -/
noncomputable def mr07Eps (m β κ c : ℕ) : ℝ :=
  1 / (400 * (β : ℝ) * (m : ℝ) ^ 2 * ((κ + 1 : ℝ) ^ c))

/-- `mr07Eps m β κ c` is strictly positive whenever `1 ≤ m` and `1 ≤ β`. -/
theorem mr07Eps_pos {m β : ℕ} (κ c : ℕ) (hm : 1 ≤ m) (hβ : 1 ≤ β) :
    0 < mr07Eps m β κ c := by
  unfold mr07Eps
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hβR : (0 : ℝ) < β := Nat.cast_pos.mpr hβ
  positivity

/-- Polynomial-time computability of all five unary schedules (`R`, `L_err`, `prec`, `maxTrials`,
`T_amp`) from `GIVPInput.enc` under `MR07ParamPolyTime P`. -/
theorem computableInPolyTime_mr07GIVPSchedules {P : SISParams} (hP : MR07ParamPolyTime P) (c : ℕ) :
    let R := fun inp : GIVPInput =>
      MR07Shorten.shortenRoundBound (P.n inp.secParam) (intTableMaxColSqNorm inp.basisB)
    let Lerr := fun inp : GIVPInput =>
      mr07ErrBits (P.n inp.secParam) (P.m inp.secParam) (P.β inp.secParam) inp.secParam c
    let prec := fun inp : GIVPInput =>
      mr07Prec (P.n inp.secParam) (P.m inp.secParam) (P.β inp.secParam) inp.secParam c
    let maxTrials := fun inp : GIVPInput =>
      mr07MaxTrials (P.n inp.secParam) (P.m inp.secParam) (P.β inp.secParam) inp.secParam c
    let Tamp := fun inp : GIVPInput =>
      mr07AmpTrials (P.m inp.secParam) (P.β inp.secParam) inp.secParam c (R inp)
    ComputableInPolyTime R GIVPInput.enc encUnary ∧
    ComputableInPolyTime Lerr GIVPInput.enc encUnary ∧
    ComputableInPolyTime prec GIVPInput.enc encUnary ∧
    ComputableInPolyTime maxTrials GIVPInput.enc encUnary ∧
    ComputableInPolyTime Tamp GIVPInput.enc encUnary := by
  have cU : ∀ k : ℕ, ComputableInPolyTime (fun _ : GIVPInput => k) GIVPInput.enc encUnary :=
    fun k => ComputableInPolyTime.const k
  have hκ : ComputableInPolyTime GIVPInput.secParam GIVPInput.enc encUnary := by fun_prop
  have hB : ComputableInPolyTime GIVPInput.basisB GIVPInput.enc IntTable.enc := by fun_prop
  have hn : ComputableInPolyTime (fun inp : GIVPInput => P.n inp.secParam) GIVPInput.enc encUnary :=
    hP.hn.comp hκ
  have hm : ComputableInPolyTime (fun inp : GIVPInput => P.m inp.secParam) GIVPInput.enc encUnary :=
    hP.hm.comp hκ
  have hβ : ComputableInPolyTime (fun inp : GIVPInput => P.β inp.secParam) GIVPInput.enc encUnary :=
    hP.hβ.comp hκ
  have hM : ComputableInPolyTime (fun inp : GIVPInput => intTableMaxColSqNorm inp.basisB)
      GIVPInput.enc encNat := computableInPolyTime_intTableMaxColSqNorm.comp hB
  have hR : ComputableInPolyTime
      (fun inp : GIVPInput =>
        MR07Shorten.shortenRoundBound (P.n inp.secParam) (intTableMaxColSqNorm inp.basisB))
      GIVPInput.enc encUnary :=
    computableInPolyTime_shortenRoundBound.comp (hn.prod hM)
  have hκc : ComputableInPolyTime (fun inp : GIVPInput => (inp.secParam + 1) ^ c)
      GIVPInput.enc encUnary := by
    induction c with
    | zero =>
      exact (show (fun inp : GIVPInput => (inp.secParam + 1) ^ 0) = fun _ => 1 from
        funext fun _ => pow_zero _).symm ▸ cU 1
    | succ c ih =>
      have hstep : ComputableInPolyTime
          (fun inp : GIVPInput => (inp.secParam + 1) ^ c * (inp.secParam + 1))
          GIVPInput.enc encUnary :=
        unary_mul.comp (ih.prod (unary_add.comp (hκ.prod (cU 1))))
      exact (show (fun inp : GIVPInput => (inp.secParam + 1) ^ (c + 1)) = _ from
        funext fun inp => pow_succ _ _).symm ▸ hstep
  have hbase : ComputableInPolyTime
      (fun inp : GIVPInput =>
        48 * (P.m inp.secParam) ^ 2 * P.n inp.secParam * P.β inp.secParam *
          (inp.secParam + 1) ^ c)
      GIVPInput.enc encUnary := by
    have hm2 : ComputableInPolyTime (fun inp : GIVPInput => (P.m inp.secParam) ^ 2)
        GIVPInput.enc encUnary := by
      have h := unary_mul.comp (hm.prod hm)
      rwa [show ((fun p : ℕ × ℕ => p.1 * p.2) ∘ fun inp : GIVPInput =>
          (P.m inp.secParam, P.m inp.secParam)) = (fun inp => (P.m inp.secParam) ^ 2) from
        funext fun inp => by dsimp only [Function.comp_apply]; ring] at h
    have h1 := unary_mul.comp ((cU 48).prod hm2)
    have h2 := unary_mul.comp (h1.prod hn)
    have h3 := unary_mul.comp (h2.prod hβ)
    exact unary_mul.comp (h3.prod hκc)
  have hclog_unary : ∀ {f : GIVPInput → ℕ}, ComputableInPolyTime f GIVPInput.enc encUnary →
      ComputableInPolyTime (fun inp => Nat.clog 2 (f inp)) GIVPInput.enc encUnary := fun hf =>
    binary_clog_two.comp (unary_to_binary.comp hf)
  have hLerr : ComputableInPolyTime
      (fun inp : GIVPInput =>
        mr07ErrBits (P.n inp.secParam) (P.m inp.secParam) (P.β inp.secParam) inp.secParam c)
      GIVPInput.enc encUnary := by
    unfold mr07ErrBits
    exact unary_add.comp ((hclog_unary (unary_add.comp (hbase.prod (cU 1)))).prod (cU 2))
  have hprec : ComputableInPolyTime
      (fun inp : GIVPInput =>
        mr07Prec (P.n inp.secParam) (P.m inp.secParam) (P.β inp.secParam) inp.secParam c)
      GIVPInput.enc encUnary := by
    unfold mr07Prec
    have h824 := unary_add.comp ((unary_mul.comp ((cU 8).prod hLerr)).prod (cU 24))
    have hprod := unary_mul.comp (hbase.prod h824)
    exact unary_add.comp ((hclog_unary (unary_add.comp (hprod.prod (cU 1)))).prod (cU 4))
  have hmaxTrials : ComputableInPolyTime
      (fun inp : GIVPInput =>
        mr07MaxTrials (P.n inp.secParam) (P.m inp.secParam) (P.β inp.secParam) inp.secParam c)
      GIVPInput.enc encUnary := by
    unfold mr07MaxTrials
    have h26 := unary_add.comp ((unary_mul.comp ((cU 2).prod hLerr)).prod (cU 6))
    exact unary_mul.comp ((unary_mul.comp ((cU 16).prod h26)).prod hLerr)
  have hTamp : ComputableInPolyTime
      (fun inp : GIVPInput =>
        mr07AmpTrials (P.m inp.secParam) (P.β inp.secParam) inp.secParam c
          (MR07Shorten.shortenRoundBound (P.n inp.secParam) (intTableMaxColSqNorm inp.basisB)))
      GIVPInput.enc encUnary := by
    unfold mr07AmpTrials
    have hclogR := hclog_unary (unary_add.comp (hR.prod (cU 1)))
    have htail := unary_add.comp ((unary_add.comp (hκ.prod hclogR)).prod (cU 2))
    have h2βm := unary_mul.comp ((unary_mul.comp ((cU 2).prod hβ)).prod hm)
    exact unary_mul.comp
      ((unary_mul.comp ((unary_mul.comp ((cU 12).prod h2βm)).prod hκc)).prod htail)
  exact ⟨hR, hLerr, hprec, hmaxTrials, hTamp⟩

/-! ### 2. Closed Quantitative Error-Budget & Amplification Bounds -/

private theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 :=
  le_trans (by norm_num) Real.exp_one_gt_d9.le

private theorem exp_neg_nat_le_inv_two_pow (k : ℕ) :
    Real.exp (-(k : ℝ)) ≤ 1 / (2 : ℝ) ^ k := by
  rw [Real.exp_neg, ← one_div]
  refine one_div_le_one_div_of_le (by positivity) ?_
  calc (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := pow_le_pow_left₀ (by norm_num) two_le_exp_one k
    _ = Real.exp (k : ℝ) := by rw [← Real.exp_nat_mul, mul_one]

/-- Exact dyadic-precision side condition `8 * (2 * tail + 6) ≤ 2 ^ prec` for
`closeTo_eval_singleIncGDDCall_idealIncGDDStep`. -/
theorem mr07_hprec_ok {n m β : ℕ} (κ c : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hβ : 1 ≤ β) :
    8 * (2 * mr07ErrBits n m β κ c + 6) ≤ 2 ^ mr07Prec n m β κ c := by
  set t := mr07ErrBits n m β κ c
  have h1 : 1 ≤ 48 * m ^ 2 * n * β * (κ + 1) ^ c := Nat.succ_le_of_lt (by positivity)
  have hclog : 48 * m ^ 2 * n * β * (κ + 1) ^ c * (8 * t + 24) + 1 ≤
      2 ^ Nat.clog 2 (48 * m ^ 2 * n * β * (κ + 1) ^ c * (8 * t + 24) + 1) :=
    Nat.le_pow_clog (by decide : 1 < 2) _
  have hprec_eq : 2 ^ mr07Prec n m β κ c =
      16 * 2 ^ Nat.clog 2 (48 * m ^ 2 * n * β * (κ + 1) ^ c * (8 * t + 24) + 1) := by
    unfold mr07Prec
    rw [pow_add]
    ring
  rw [hprec_eq]
  have hmul : 8 * t + 24 ≤ 48 * m ^ 2 * n * β * (κ + 1) ^ c * (8 * t + 24) :=
    Nat.le_mul_of_pos_left _ h1
  omega

/-- Complete 5-term `CloseTo` error bound for one `singleIncGDDCall`:
`mr07SingleCallErr ≤ 6 / (96 K) = 1 / (16 K) ≤ 1 / (12 K)` where `K = 2 β m (κ + 1)^c`. -/
theorem mr07_singleCall_eta_le {n m β : ℕ} (κ c : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hβ : 1 ≤ β) :
    let L := mr07ErrBits n m β κ c
    let prec := mr07Prec n m β κ c
    let maxTrials := mr07MaxTrials n m β κ c
    let ε := mr07Eps m β κ c
    let K : ℝ := 2 * (β : ℝ) * (m : ℝ) * ((κ + 1 : ℝ) ^ c)
    mr07SingleCallErr n m L prec maxTrials L ε ≤ 1 / (12 * K) := by
  intro L prec maxTrials ε K
  unfold mr07SingleCallErr
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hβR : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hκc : (1 : ℝ) ≤ ((κ + 1 : ℝ) ^ c) := one_le_pow₀ (by linarith)
  have hKpos : 0 < K := by dsimp only [K]; positivity
  have hL_ge2 : 2 ≤ L := by dsimp only [L, mr07ErrBits]; omega
  have hLR_ge2 : (2 : ℝ) ≤ L := by exact_mod_cast hL_ge2
  have h2L_ge : 96 * (m : ℝ) * (n : ℝ) * K ≤ (2 : ℝ) ^ L := by
    have hclog : 48 * m ^ 2 * n * β * (κ + 1) ^ c + 1 ≤
        2 ^ Nat.clog 2 (48 * m ^ 2 * n * β * (κ + 1) ^ c + 1) :=
      Nat.le_pow_clog (by decide : 1 < 2) _
    have hclogR : 48 * (m : ℝ) ^ 2 * (n : ℝ) * (β : ℝ) * ((κ + 1 : ℝ) ^ c) + 1 ≤
        (2 : ℝ) ^ Nat.clog 2 (48 * m ^ 2 * n * β * (κ + 1) ^ c + 1) := by exact_mod_cast hclog
    have hpow : (2 : ℝ) ^ L =
        4 * (2 : ℝ) ^ Nat.clog 2 (48 * m ^ 2 * n * β * (κ + 1) ^ c + 1) := by
      dsimp only [L, mr07ErrBits]; rw [pow_add]; ring
    rw [hpow]
    have hident : 96 * (m : ℝ) * (n : ℝ) * K =
        4 * (48 * (m : ℝ) ^ 2 * (n : ℝ) * (β : ℝ) * ((κ + 1 : ℝ) ^ c)) := by
      dsimp only [K]; ring
    linarith
  have hmn_div_2L : (m : ℝ) * (n : ℝ) / (2 : ℝ) ^ L ≤ 1 / (96 * K) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have ht1 : 2 * (2 : ℝ) ^ (-(L : ℤ)) ≤ 2 / (96 * K) := by
    rw [zpow_neg, zpow_natCast]
    have h1 : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by nlinarith
    have h2 : (1 : ℝ) / (2 : ℝ) ^ L ≤ 1 / (96 * K) :=
      (div_le_div_of_nonneg_right h1 (by positivity)).trans hmn_div_2L
    have h3 : 2 * ((2 : ℝ) ^ L)⁻¹ = 2 * ((1 : ℝ) / (2 : ℝ) ^ L) := by ring
    have h4 : 2 * (1 / (96 * K)) = 2 / (96 * K) := by ring
    linarith
  have ht2 : (m : ℝ) * ((n : ℝ) / (2 : ℝ) ^ L) ≤ 1 / (96 * K) := by
    simpa only [mul_div_assoc'] using hmn_div_2L
  have ht3 :
      (m : ℝ) * (n : ℝ) * (1 - 1 / (16 * (2 * (L : ℝ) + 6))) ^ maxTrials ≤ 1 / (96 * K) := by
    set d : ℝ := 16 * (2 * (L : ℝ) + 6)
    have hd_pos : 0 < d := by positivity
    have h1 : 1 - 1 / d ≤ Real.exp (-(1 / d)) := by
      have := Real.add_one_le_exp (-(1 / d)); linarith
    have hbase0 : 0 ≤ 1 - 1 / d := by
      have : (1 : ℝ) ≤ d := by dsimp only [d]; linarith
      have : 1 / d ≤ 1 := div_le_one_of_le₀ this hd_pos.le
      linarith
    have hpow : (1 - 1 / d) ^ maxTrials ≤ Real.exp (-(L : ℝ)) := by
      calc (1 - 1 / d) ^ maxTrials
          ≤ (Real.exp (-(1 / d))) ^ maxTrials := pow_le_pow_left₀ hbase0 h1 maxTrials
        _ = Real.exp ((maxTrials : ℝ) * (-(1 / d))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(L : ℝ)) := by
            congr 1; dsimp only [maxTrials, mr07MaxTrials, d, L]
            push_cast; field_simp
    calc (m : ℝ) * (n : ℝ) * (1 - 1 / d) ^ maxTrials
        ≤ (m : ℝ) * (n : ℝ) * (1 / (2 : ℝ) ^ L) :=
          mul_le_mul_of_nonneg_left (hpow.trans (exp_neg_nat_le_inv_two_pow L)) (by positivity)
      _ = (m : ℝ) * (n : ℝ) / (2 : ℝ) ^ L := by ring
      _ ≤ 1 / (96 * K) := hmn_div_2L
  have ht4 : (m : ℝ) * (n : ℝ) * ((8 * (L : ℝ) + 24) / (2 : ℝ) ^ prec) ≤ 1 / (96 * K) := by
    set argN : ℕ := 48 * m ^ 2 * n * β * (κ + 1) ^ c * (8 * L + 24) + 1
    have hclogR : (argN : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 argN := by
      exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) argN
    have hpow : (2 : ℝ) ^ prec = 16 * (2 : ℝ) ^ Nat.clog 2 argN := by
      dsimp only [prec, mr07Prec, argN]; rw [pow_add]; ring
    have harg_eq : (argN : ℝ) = 24 * (m : ℝ) * (n : ℝ) * K * (8 * (L : ℝ) + 24) + 1 := by
      dsimp only [argN, K]; push_cast; ring
    have h2prec_pos : (0 : ℝ) < (2 : ℝ) ^ prec := pow_pos (by norm_num) prec
    have h96K_pos : (0 : ℝ) < 96 * K := mul_pos (by norm_num) hKpos
    have h2prec_ge : 96 * (m : ℝ) * (n : ℝ) * K * (8 * (L : ℝ) + 24) ≤ (2 : ℝ) ^ prec := by
      have hprod_nn : 0 ≤ (m : ℝ) * (n : ℝ) * K * (8 * (L : ℝ) + 24) :=
        mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)) hKpos.le)
          (by linarith only [hLR_ge2])
      linarith only [hclogR, hpow, harg_eq, hprod_nn]
    have hdiv : (m : ℝ) * (n : ℝ) * ((8 * (L : ℝ) + 24) / (2 : ℝ) ^ prec) =
        ((m : ℝ) * (n : ℝ) * (8 * (L : ℝ) + 24)) / (2 : ℝ) ^ prec := by ring
    rw [hdiv, div_le_div_iff₀ h2prec_pos h96K_pos]
    have hrew : (m : ℝ) * (n : ℝ) * (8 * (L : ℝ) + 24) * (96 * K) =
        96 * (m : ℝ) * (n : ℝ) * K * (8 * (L : ℝ) + 24) := by ring
    linarith only [h2prec_ge, hrew]
  have ht5 : (m : ℝ) * (n : ℝ) *
      ((1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (L : ℝ) ^ 2))) ≤ 1 / (96 * K) := by
    have hε_le : ε ≤ 1 / 400 := by
      dsimp only [ε, mr07Eps]
      refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
      have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hmR
      have h1 : (1 : ℝ) ≤ (β : ℝ) * (m : ℝ) ^ 2 * ((κ + 1 : ℝ) ^ c) :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hβR hm2) hκc
      linarith only [h1]
    have hfrac : (1 + ε) / (1 - ε) ≤ 3 / 2 := by
      rw [div_le_iff₀ (by linarith only [hε_le])]; linarith only [hε_le]
    have hexp_le : Real.exp (-Real.pi * (L : ℝ) ^ 2) ≤ (1 / 3 : ℝ) * (1 / (2 : ℝ) ^ L) := by
      have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hsq : 2 * (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith only [hLR_ge2]
      have harg : -Real.pi * (L : ℝ) ^ 2 ≤ -((L : ℝ) + 2) := by
        nlinarith only [hpi3, hLR_ge2, hsq]
      have h1 : Real.exp (-Real.pi * (L : ℝ) ^ 2) ≤ Real.exp (-((L : ℝ) + 2)) :=
        Real.exp_le_exp.mpr harg
      have hsplit : Real.exp (-((L : ℝ) + 2)) = Real.exp (-2 : ℝ) * Real.exp (-(L : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      have he2 : Real.exp (-2 : ℝ) ≤ 1 / 3 := by
        rw [Real.exp_neg, one_div]
        refine inv_anti₀ (by norm_num) ?_
        linarith [Real.add_one_le_exp (2 : ℝ)]
      calc Real.exp (-Real.pi * (L : ℝ) ^ 2)
          ≤ Real.exp (-2 : ℝ) * Real.exp (-(L : ℝ)) := by rw [← hsplit]; exact h1
        _ ≤ (1 / 3 : ℝ) * (1 / (2 : ℝ) ^ L) :=
            mul_le_mul he2 (exp_neg_nat_le_inv_two_pow L) (Real.exp_pos _).le (by norm_num)
    have hinner :
        (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (L : ℝ) ^ 2)) ≤ 1 / (2 : ℝ) ^ L := by
      calc (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (L : ℝ) ^ 2))
          ≤ (3 / 2 : ℝ) * (2 * ((1 / 3 : ℝ) * (1 / (2 : ℝ) ^ L))) :=
            mul_le_mul hfrac (mul_le_mul_of_nonneg_left hexp_le (by norm_num))
              (by positivity) (by norm_num)
        _ = 1 / (2 : ℝ) ^ L := by ring
    calc (m : ℝ) * (n : ℝ) * ((1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (L : ℝ) ^ 2)))
        ≤ (m : ℝ) * (n : ℝ) * (1 / (2 : ℝ) ^ L) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = (m : ℝ) * (n : ℝ) / (2 : ℝ) ^ L := by ring
      _ ≤ 1 / (96 * K) := hmn_div_2L
  have hsum : 6 / (96 * K) ≤ 1 / (12 * K) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hKpos) (mul_pos (by norm_num) hKpos)]
    linarith only [hKpos]
  have hdist :
      (m : ℝ) * ((n : ℝ) *
        ((1 - 1 / (16 * (2 * (L : ℝ) + 6))) ^ maxTrials
          + (8 * (L : ℝ) + 24) / (2 : ℝ) ^ prec
          + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (L : ℝ) ^ 2)))) =
      (m : ℝ) * (n : ℝ) * (1 - 1 / (16 * (2 * (L : ℝ) + 6))) ^ maxTrials +
        (m : ℝ) * (n : ℝ) * ((8 * (L : ℝ) + 24) / (2 : ℝ) ^ prec) +
        (m : ℝ) * (n : ℝ) * ((1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (L : ℝ) ^ 2))) := by
    ring
  have h6 : 2 / (96 * K) + 1 / (96 * K) + 1 / (96 * K) + 1 / (96 * K) + 1 / (96 * K) =
      6 / (96 * K) := by ring
  linarith only [ht1, ht2, ht3, ht4, ht5, hsum, hdist, h6]

/-- Single-call success probability lower bound: when `1 / (κ + 1)^c ≤ adv` and
`η ≤ 1 / (12 K)`, `mr07Eps` satisfies the `MR07Core` threshold and the single-call success
probability is at least `1 / (12 * (2 * β * m) * (κ + 1)^c)`. -/
theorem mr07_singleCall_succProb_ge {m β : ℕ} (κ c : ℕ)
    (hm : 1 ≤ m) (hβ : 1 ≤ β) {adv η : ℝ}
    (hadv : 1 / ((κ + 1 : ℝ) ^ c) ≤ adv)
    (hη : η ≤ 1 / (12 * (2 * (β : ℝ) * (m : ℝ) * ((κ + 1 : ℝ) ^ c)))) :
    let ε := mr07Eps m β κ c
    ε ≤ 1 / (400 * max 1 (Real.sqrt m)) ∧
    1 / (12 * (2 * (β : ℝ) * (m : ℝ)) * ((κ + 1 : ℝ) ^ c)) ≤
      (1 / 3 : ℝ) * (adv / (2 * (β : ℝ) * (m : ℝ)) - (m : ℝ) * ε / (2 * (1 - ε))) - η := by
  intro ε
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hβR : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hκc : (1 : ℝ) ≤ ((κ + 1 : ℝ) ^ c) := one_le_pow₀ (by linarith)
  set K : ℝ := 2 * (β : ℝ) * (m : ℝ) * ((κ + 1 : ℝ) ^ c)
  have hKpos : 0 < K := by dsimp only [K]; positivity
  have hsqrt_le_m : Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
    calc Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = (m : ℝ) := Real.sqrt_sq (by linarith)
  have hmax_le : max (1 : ℝ) (Real.sqrt m) ≤ (β : ℝ) * (m : ℝ) ^ 2 * ((κ + 1 : ℝ) ^ c) := by
    have hbm1 : (1 : ℝ) ≤ (β : ℝ) * (m : ℝ) ^ 2 := by nlinarith only [hβR, hmR]
    have h1 : (1 : ℝ) ≤ (β : ℝ) * (m : ℝ) ^ 2 * ((κ + 1 : ℝ) ^ c) := by nlinarith only [hbm1, hκc]
    have h2 : (m : ℝ) ≤ (β : ℝ) * (m : ℝ) ^ 2 * ((κ + 1 : ℝ) ^ c) := by
      have hbm : (m : ℝ) ≤ (β : ℝ) * (m : ℝ) ^ 2 := by nlinarith only [hβR, hmR]
      nlinarith only [hbm, hκc]
    exact max_le h1 (hsqrt_le_m.trans h2)
  constructor
  · dsimp only [ε, mr07Eps]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  · have hε_le_half : ε ≤ 1 / 2 := by
      dsimp only [ε, mr07Eps]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hbm : (1 : ℝ) ≤ (β : ℝ) * (m : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hmeps_le : (m : ℝ) * ε / (2 * (1 - ε)) ≤ 1 / (200 * K) := by
      have h1 : (m : ℝ) * ε / (2 * (1 - ε)) ≤ (m : ℝ) * ε := by
        rw [div_le_iff₀ (by linarith)]
        have : 0 ≤ (m : ℝ) * ε := by dsimp only [ε, mr07Eps]; positivity
        nlinarith
      have h2 : (m : ℝ) * ε = 1 / (200 * K) := by
        dsimp only [ε, mr07Eps, K]
        have hmne : (m : ℝ) ≠ 0 := by linarith
        have hβne : (β : ℝ) ≠ 0 := by linarith
        have hκne : ((κ + 1 : ℝ) ^ c) ≠ 0 := by positivity
        field_simp [hmne, hβne, hκne]
        ring
      linarith
    have hadv_div : 1 / K ≤ adv / (2 * (β : ℝ) * (m : ℝ)) := by
      have heq : 1 / K = (1 / ((κ + 1 : ℝ) ^ c)) / (2 * (β : ℝ) * (m : ℝ)) := by
        dsimp only [K]
        have hmne : (m : ℝ) ≠ 0 := by linarith
        have hβne : (β : ℝ) ≠ 0 := by linarith
        have hκne : ((κ + 1 : ℝ) ^ c) ≠ 0 := by positivity
        field_simp [hmne, hβne, hκne]
      rw [heq]
      exact div_le_div_of_nonneg_right hadv (by positivity)
    have hcomb : 1 / (12 * K) ≤ (1 / 3 : ℝ) * (1 / K - 1 / (200 * K)) - 1 / (12 * K) := by
      field_simp [hKpos.ne']
      norm_num
    have h12K_eq : 1 / (12 * (2 * (β : ℝ) * (m : ℝ)) * ((κ + 1 : ℝ) ^ c)) = 1 / (12 * K) := by
      dsimp only [K]; ring_nf
    rw [h12K_eq]
    linarith [hadv_div, hmeps_le, hη, hcomb]

/-- Per-round failure bound after `mr07AmpTrials m β κ c R` independent trials. -/
theorem mr07_amp_round_failure_le {m β : ℕ} (κ c R : ℕ)
    (hm : 1 ≤ m) (hβ : 1 ≤ β) {p : ℝ}
    (hp_ge : 1 / (12 * (2 * (β : ℝ) * (m : ℝ)) * ((κ + 1 : ℝ) ^ c)) ≤ p) (hp_le1 : p ≤ 1) :
    (1 - p) ^ (mr07AmpTrials m β κ c R) ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) / ((R : ℝ) + 1) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hβR : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  set P : ℝ := 12 * (2 * (β : ℝ) * (m : ℝ)) * ((κ + 1 : ℝ) ^ c)
  have hPpos : 0 < P := by dsimp only [P]; positivity
  set E : ℕ := κ + Nat.clog 2 (R + 1) + 2
  have hT_eq : (mr07AmpTrials m β κ c R : ℝ) = P * (E : ℝ) := by
    dsimp only [mr07AmpTrials, P, E]; push_cast; ring
  have h1p_le : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  have hpow : (1 - p) ^ mr07AmpTrials m β κ c R ≤ Real.exp (-(E : ℝ)) := by
    calc (1 - p) ^ mr07AmpTrials m β κ c R
        ≤ (Real.exp (-p)) ^ mr07AmpTrials m β κ c R :=
          pow_le_pow_left₀ (by linarith) h1p_le _
      _ = Real.exp ((mr07AmpTrials m β κ c R : ℝ) * (-p)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (-(E : ℝ)) := by
          apply Real.exp_le_exp.mpr
          rw [hT_eq]
          have hPp : 1 ≤ P * p := (div_le_iff₀' hPpos).mp (by simpa [one_div] using hp_ge)
          have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg E
          nlinarith
  have hinv : Real.exp (-(E : ℝ)) ≤ 1 / (2 : ℝ) ^ E := exp_neg_nat_le_inv_two_pow E
  have hclog : ((R : ℝ) + 1) ≤ (2 : ℝ) ^ Nat.clog 2 (R + 1) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (R + 1)
  have h2E : (2 : ℝ) ^ E = 4 * (2 : ℝ) ^ κ * (2 : ℝ) ^ Nat.clog 2 (R + 1) := by
    dsimp only [E]; rw [pow_add, pow_add]; ring
  have hfinal : 1 / (2 : ℝ) ^ E ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) / ((R : ℝ) + 1) := by
    rw [h2E, zpow_neg, zpow_natCast]
    have h1 : 4 * (2 : ℝ) ^ κ * ((R : ℝ) + 1) ≤ 4 * (2 : ℝ) ^ κ * (2 : ℝ) ^ Nat.clog 2 (R + 1) :=
      mul_le_mul_of_nonneg_left hclog (by positivity)
    have h2 : 1 / (4 * (2 : ℝ) ^ κ * (2 : ℝ) ^ Nat.clog 2 (R + 1)) ≤
        1 / (4 * (2 : ℝ) ^ κ * ((R : ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) h1
    have heq : 1 / (4 * (2 : ℝ) ^ κ * ((R : ℝ) + 1)) =
        (1 / 4 : ℝ) * ((2 : ℝ) ^ κ)⁻¹ / ((R : ℝ) + 1) := by
      have h2k : (2 : ℝ) ^ κ ≠ 0 := by positivity
      have hR1 : (R : ℝ) + 1 ≠ 0 := by positivity
      field_simp [h2k, hR1]
    linarith
  exact hpow.trans (hinv.trans hfinal)

/-- Union bound over `R` shortening rounds yields total success probability
`≥ 1 - (1 / 4) * 2 ^ (-κ) ≥ 1 / 2` for every `κ : ℕ`. -/
theorem mr07_total_succProb_ge (κ R : ℕ) {roundFail : ℝ}
    (hfail : roundFail ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) / ((R : ℝ) + 1)) :
    (1 / 2 : ℝ) ≤ 1 - (R : ℝ) * roundFail ∧
    1 - (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) ≤ 1 - (R : ℝ) * roundFail := by
  have hR_le : (R : ℝ) / ((R : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hprod : (R : ℝ) * roundFail ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) := by
    calc (R : ℝ) * roundFail
        ≤ (R : ℝ) * ((1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) / ((R : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hfail (Nat.cast_nonneg R)
      _ = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) * ((R : ℝ) / ((R : ℝ) + 1)) := by ring
      _ ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) * 1 :=
          mul_le_mul_of_nonneg_left hR_le (by positivity)
      _ = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) := mul_one _
  have h2inv : (2 : ℝ) ^ (-(κ : ℤ)) ≤ 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  constructor <;> linarith

/-! ### 3. Guarded Strict-PPT Shortening Reduction (`mr07GIVPReduction`) -/

/-- One guarded basis-shortening round of `mr07GIVPReduction`: computes the rational orthogonal
target `ratOrthoTargetIntTable T`, calls `mr07IncGDDReduction`, and applies
`guardedUpdateIntTable`. -/
noncomputable def mr07GIVPShortenStep (P : SISParams) (c : ℕ) (F : P.Solver)
    (inp : GIVPInput) (T : IntTable) : ProbComp IntTable := do
  let κ := inp.secParam
  let n := P.n κ
  let m := P.m κ
  let β := P.β κ
  let R := MR07Shorten.shortenRoundBound n (intTableMaxColSqNorm inp.basisB)
  let L := mr07ErrBits n m β κ c
  let prec := mr07Prec n m β κ c
  let maxTrials := mr07MaxTrials n m β κ c
  let trials := mr07AmpTrials m β κ c R
  let iStar := intTableMaxSqNormIdx T
  let t := ratOrthoTargetIntTable T
  let rSq : ℚ := ((intTableColSqNorm T iStar : ℕ) : ℚ) / 64
  let u ← mr07IncGDDReduction P F
    ⟨κ, inp.basisB, T, t, rSq, trials, L, prec, maxTrials, L⟩
  pure (guardedUpdateIntTable n T iStar u)

/-- Guarded strict-PPT basis-shortening reduction solving `GIVP` via `OracleComp.iterate`
(finite-parameter reduction step toward `[MicciancioRegev2007]` Lemma 5.10 and Corollary 5.13). -/
noncomputable def mr07GIVPReduction (P : SISParams) (c : ℕ) (F : P.Solver) (inp : GIVPInput) :
    ProbComp IntTable :=
  let R := MR07Shorten.shortenRoundBound (P.n inp.secParam) (intTableMaxColSqNorm inp.basisB)
  OracleComp.iterate R (mr07GIVPShortenStep P c F inp) inp.basisB

private theorem isPPTOn_mr07GIVPShortenStep {P : SISParams} (hP : MR07ParamPolyTime P) (c : ℕ)
    {F : P.Solver} (hF : F.IsPPT) :
    IsPPTOn (encPair GIVPInput.enc IntTable.enc) IntTable.enc
      (fun p => mr07GIVPShortenStep P c F p.1 p.2) := by
  obtain ⟨_, hLerr, hprec, hmaxTrials, hTamp⟩ := computableInPolyTime_mr07GIVPSchedules hP c
  let encP := encPair GIVPInput.enc IntTable.enc
  have hp1 := fst GIVPInput.enc IntTable.enc
  have hp2 := snd GIVPInput.enc IntTable.enc
  have hκ : ComputableInPolyTime (fun p : GIVPInput × IntTable => p.1.secParam) encP encUnary :=
    (by fun_prop : ComputableInPolyTime GIVPInput.secParam GIVPInput.enc encUnary).comp hp1
  have hB : ComputableInPolyTime (fun p : GIVPInput × IntTable => p.1.basisB) encP IntTable.enc :=
    (by fun_prop : ComputableInPolyTime GIVPInput.basisB GIVPInput.enc IntTable.enc).comp hp1
  have hiStar : ComputableInPolyTime (fun p : GIVPInput × IntTable => intTableMaxSqNormIdx p.2)
      encP encUnary :=
    computableInPolyTime_intTableMaxSqNormIdx.comp hp2
  have ht : ComputableInPolyTime (fun p : GIVPInput × IntTable => ratOrthoTargetIntTable p.2)
      encP (encList encRat) :=
    computableInPolyTime_ratOrthoTargetIntTable.comp hp2
  have hrSq : ComputableInPolyTime
      (fun p : GIVPInput × IntTable =>
        ((intTableColSqNorm p.2 (intTableMaxSqNormIdx p.2) : ℕ) : ℚ) / 64)
      encP encRat := by
    have hsqN : ComputableInPolyTime
        (fun p : GIVPInput × IntTable => intTableColSqNorm p.2 (intTableMaxSqNormIdx p.2))
        encP encNat :=
      computableInPolyTime_intTableColSqNorm.comp (hp2.prod hiStar)
    have hsqQ : ComputableInPolyTime
        (fun p : GIVPInput × IntTable =>
          ((intTableColSqNorm p.2 (intTableMaxSqNormIdx p.2) : ℕ) : ℚ))
        encP encRat := by
      have h := rat_intCast.comp (intBin_natCast.comp hsqN)
      rwa [show ((Int.cast : ℤ → ℚ) ∘ ((Nat.cast : ℕ → ℤ) ∘
          fun p : GIVPInput × IntTable => intTableColSqNorm p.2 (intTableMaxSqNormIdx p.2))) =
          (fun p : GIVPInput × IntTable =>
            ((intTableColSqNorm p.2 (intTableMaxSqNormIdx p.2) : ℕ) : ℚ)) from
        funext fun _ => by simp] at h
    exact rat_div' hsqQ (const 64)
  have hincInp : ComputableInPolyTime
      (fun p : GIVPInput × IntTable =>
        IncGDDInput.mk p.1.secParam p.1.basisB p.2 (ratOrthoTargetIntTable p.2)
          (((intTableColSqNorm p.2 (intTableMaxSqNormIdx p.2) : ℕ) : ℚ) / 64)
          (mr07AmpTrials (P.m p.1.secParam) (P.β p.1.secParam) p.1.secParam c
            (MR07Shorten.shortenRoundBound (P.n p.1.secParam) (intTableMaxColSqNorm p.1.basisB)))
          (mr07ErrBits (P.n p.1.secParam) (P.m p.1.secParam) (P.β p.1.secParam) p.1.secParam c)
          (mr07Prec (P.n p.1.secParam) (P.m p.1.secParam) (P.β p.1.secParam) p.1.secParam c)
          (mr07MaxTrials (P.n p.1.secParam) (P.m p.1.secParam) (P.β p.1.secParam) p.1.secParam c)
          (mr07ErrBits (P.n p.1.secParam) (P.m p.1.secParam) (P.β p.1.secParam) p.1.secParam c))
      encP IncGDDInput.enc :=
    IncGDDInput.enc_mk_polyTime hκ hB hp2 ht hrSq
      (hTamp.comp hp1) (hLerr.comp hp1) (hprec.comp hp1) (hmaxTrials.comp hp1) (hLerr.comp hp1)
  have hcall := (isPPTOn_mr07IncGDDReduction hP hF).preprocess hincInp
  have hupd : ComputableInPolyTime
      (fun q : (GIVPInput × IntTable) × List ℤ =>
        guardedUpdateIntTable (P.n q.1.1.secParam) q.1.2 (intTableMaxSqNormIdx q.1.2) q.2)
      (encPair encP (encList encIntBin)) IntTable.enc := by
    have hq1 := fst encP (encList encIntBin)
    have hq2 := snd encP (encList encIntBin)
    have hn' := (hP.hn.comp hκ).comp hq1
    have hT' := hp2.comp hq1
    have hi' := hiStar.comp hq1
    exact computableInPolyTime_guardedUpdateIntTable.comp ((hn'.prod hT').prod (hi'.prod hq2))
  refine (hcall.keep_input.map hupd).congr fun p => ?_
  simp only [mr07GIVPShortenStep, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]

/-- Unconditional strict-PPT certificate for `mr07GIVPReduction` via `IsPPTOn.iterateWith_spec`,
handling all inputs (including malformed `inp.basisB`) with the cubic encoding-length bound
`14 * ((GIVPInput.enc inp).length + 1) ^ 3`. -/
theorem isPPTOn_mr07GIVPReduction {P : SISParams} (hP : MR07ParamPolyTime P) (c : ℕ)
    {F : P.Solver} (hF : F.IsPPT) :
    IsPPTOn GIVPInput.enc IntTable.enc (mr07GIVPReduction P c F) := by
  obtain ⟨hR, _, _, _, _⟩ := computableInPolyTime_mr07GIVPSchedules hP c
  let roundsFn : GIVPInput → ℕ := fun inp =>
    MR07Shorten.shortenRoundBound (P.n inp.secParam) (intTableMaxColSqNorm inp.basisB)
  let inv : GIVPInput → ℕ → IntTable → Prop := fun inp _ T =>
    T = inp.basisB ∨
      (T.numRows = P.n inp.secParam ∧ T.numCols = P.n inp.secParam ∧ T.WellFormed ∧
       inp.basisB.numRows = P.n inp.secParam ∧ inp.basisB.numCols = P.n inp.secParam ∧
       inp.basisB.WellFormed ∧
       ∀ j < P.n inp.secParam, intTableColSqNorm T j ≤ intTableMaxColSqNorm inp.basisB)
  let sizeBound : GIVPInput → ℕ := fun inp => 14 * ((GIVPInput.enc inp).length + 1) ^ 3
  have hpoly : PolyBounded (fun a => (GIVPInput.enc a).length) sizeBound :=
    PolyBounded.of_forall_le 14 3 fun _ => le_rfl
  have hB_le :
      ∀ inp : GIVPInput, (IntTable.enc inp.basisB).length ≤ (GIVPInput.enc inp).length := by
    intro inp
    rw [GIVPInput.enc_apply, length_encPair]
    dsimp only; omega
  have hstep_inv : ∀ (inp : GIVPInput) (T : IntTable),
      ∀ T' ∈ (ProbComp.eval (mr07GIVPShortenStep P c F inp T)).support,
        (¬ (T.numRows = P.n inp.secParam ∧ T.numCols = P.n inp.secParam ∧ T.WellFormed) →
          T' = T) ∧
        (T.numRows = P.n inp.secParam ∧ T.numCols = P.n inp.secParam ∧ T.WellFormed →
          T'.numRows = P.n inp.secParam ∧ T'.numCols = P.n inp.secParam ∧ T'.WellFormed ∧
          ∀ j < P.n inp.secParam, intTableColSqNorm T' j ≤ intTableMaxColSqNorm T) := by
    intro inp T T' hT'
    unfold mr07GIVPShortenStep at hT'
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hT'
    obtain ⟨u, _, rfl⟩ := hT'
    exact guardedUpdateIntTable_invariants (P.n inp.secParam) T (intTableMaxSqNormIdx T) u
  refine (IsPPTOn.iterateWith_spec (input := GIVPInput.enc) (stateEncoding := IntTable.enc)
    (count := roundsFn) (initial := GIVPInput.basisB) (step := mr07GIVPShortenStep P c F)
    (invariant := inv) (size := sizeBound)
    (hcount := hR) (hinitial := by fun_prop) (hstep := isPPTOn_mr07GIVPShortenStep hP c hF)
    (hbase := fun _ => Or.inl rfl)
    (hpreserve := ?_) (hsize := hpoly) (hbound := ?_)).1
  · intro inp i T _ hT T' hT'
    obtain ⟨hbad, hgood⟩ := hstep_inv inp T T' hT'
    rcases hT with rfl | ⟨hTr, hTc, hTwf, hBr, hBc, hBwf, hnorm⟩
    · by_cases hwfB : inp.basisB.numRows = P.n inp.secParam ∧
          inp.basisB.numCols = P.n inp.secParam ∧ inp.basisB.WellFormed
      · obtain ⟨hTr', hTc', hTwf', hnorm'⟩ := hgood hwfB
        exact Or.inr ⟨hTr', hTc', hTwf', hwfB.1, hwfB.2.1, hwfB.2.2, hnorm'⟩
      · exact Or.inl (hbad hwfB)
    · obtain ⟨hTr', hTc', hTwf', hnorm'⟩ := hgood ⟨hTr, hTc, hTwf⟩
      refine Or.inr ⟨hTr', hTc', hTwf', hBr, hBc, hBwf, fun j hj => ?_⟩
      have hmax_le : intTableMaxColSqNorm T ≤ intTableMaxColSqNorm inp.basisB :=
        intTableMaxColSqNorm_le T fun k hk => hnorm k (hTc ▸ hk)
      exact (hnorm' j hj).trans hmax_le
  · intro inp i T _ hT
    rcases hT with rfl | ⟨hTr, hTc, hTwf, hBr, hBc, _, hnorm⟩
    · have h1 := hB_le inp
      dsimp only [sizeBound]
      have hpos : 1 ≤ ((GIVPInput.enc inp).length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have hle : (GIVPInput.enc inp).length ≤ ((GIVPInput.enc inp).length + 1) ^ 3 := by nlinarith
      omega
    · have h1 := length_intTableEnc_le_of_colSqNorm_le hBr hBc hTr hTc hTwf hnorm
      have h2 := hB_le inp
      dsimp only [sizeBound]
      exact h1.trans (Nat.mul_le_mul_left 14 (Nat.pow_le_pow_left (Nat.add_le_add_right h2 1) 3))

/-! ### 4. Quantitative `GIVP` Success Probability Theorem (`mr07GIVPReduction_succProb_ge`) -/

private lemma mr07GIVPShortenStep_drop_failure_le
    (P : SISParams) (c : ℕ) (F : P.Solver) (κ : ℕ)
    (hn : 1 ≤ P.n κ) (hm : 1 ≤ P.m κ) (hβ : 1 ≤ P.β κ)
    (hq : 8 * (P.n κ : ℝ) * Real.sqrt (P.m κ) * (P.β κ : ℝ) ≤ (P.q κ : ℝ))
    (hadv : 1 / ((κ + 1 : ℝ) ^ c) ≤ (sisEll2Advantage (P.q κ) (P.β κ : ℝ) (F κ) : ℝ))
    (B : Matrix (Fin (P.n κ)) (Fin (P.n κ)) ℤ) (hB : B.det ≠ 0)
    (T : IntTable) (hr : T.numRows = P.n κ) (hc : T.numCols = P.n κ) (hwf : T.WellFormed)
    (hli : LinearIndependent ℝ
      (intColCast B (Matrix.of fun i j : Fin (P.n κ) => T.entry i.val j.val) hB))
    (hmem : ∀ j, intColCast B (Matrix.of fun i j : Fin (P.n κ) => T.entry i.val j.val) hB j ∈
      intLattice B)
    (hnotGIVP : ¬ GIVP.IsSolution
      (fun L => ZLattice.smoothingParameter L (mr07Eps (P.m κ) (P.β κ) κ c))
      (8 * ((P.β κ : ℝ) * Real.sqrt (P.n κ))) (intLattice B)
      (intColCast B (Matrix.of fun i j : Fin (P.n κ) => T.entry i.val j.val) hB)) :
    let n := P.n κ
    let R := MR07Shorten.shortenRoundBound n (intTableMaxColSqNorm (RowTable.ofMatrix B))
    let pSingle : ℝ := 1 / (12 * (2 * (P.β κ : ℝ) * (P.m κ : ℝ)) * ((κ + 1 : ℝ) ^ c))
    let entryMat : IntTable → Matrix (Fin n) (Fin n) ℤ :=
      fun U => Matrix.of fun i j => U.entry i.val j.val
    ((ProbComp.eval (mr07GIVPShortenStep P c F ⟨κ, RowTable.ofMatrix B⟩ T)).toOuterMeasure
      {T' | ¬ (MR07Shorten.sqNormProd (intColCast B (entryMat T') hB) ≤
        (13 / 16 : ℝ) ^ 2 * MR07Shorten.sqNormProd (intColCast B (entryMat T) hB))}).toReal ≤
      (1 - pSingle) ^ mr07AmpTrials (P.m κ) (P.β κ) κ c R := by
  intro n R pSingle entryMat
  have : IsZLattice ℝ (intLattice B) := isZLattice_intLattice hB
  obtain ⟨mDim, hmDim⟩ : ∃ mDim : ℕ, n = mDim + 1 := ⟨n - 1, by omega⟩
  set B₀ : IntTable := RowTable.ofMatrix B
  set ε : ℝ := mr07Eps (P.m κ) (P.β κ) κ c
  have hε_pos : 0 < ε := mr07Eps_pos κ c hm hβ
  have hTeq : T = RowTable.ofMatrix (entryMat T) := intTable_eq_ofMatrix_of_wellFormed T hr hc hwf
  have hdetT : (entryMat T).det ≠ 0 := by
    rw [← linearIndependent_intCol_iff_det_ne_zero]
    let eCast : Fin (Module.finrank ℤ (intLattice B)) ≃ Fin n := finCongr (finrank_intLattice hB)
    exact (linearIndependent_equiv eCast).mp hli
  have hsubT : intLattice (entryMat T) ≤ intLattice B := by
    rw [intLattice, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj := hmem (Fin.cast (finrank_intLattice hB).symm j)
    simpa [intColCast] using hj
  have hval := (MR07Shorten.isSolution_givp_or_isValidInstance_incGDD
    (fun L => ZLattice.smoothingParameter L ε)
    ((P.β κ : ℝ) * Real.sqrt n) (intLattice B)
    (intColCast B (entryMat T) hB) hli hmem).resolve_left hnotGIVP
  have hnorm_T_pos : 0 < ‖intColCast B (entryMat T) hB‖ :=
    lt_of_lt_of_le
      (norm_pos_iff.mpr (hli.ne_zero (Fin.cast (finrank_intLattice hB).symm ⟨0, hn⟩)))
      (norm_le_pi_norm _ _)
  have hr_m : T.numRows = mDim + 1 := hr.trans hmDim
  have hc_m : T.numCols = mDim + 1 := hc.trans hmDim
  have hli_m : LinearIndependent ℝ
      (intCol (Matrix.of fun i j : Fin (mDim + 1) => T.entry i.val j.val)) := by
    rw [linearIndependent_intCol_iff_det_ne_zero]
    let eM : Fin (mDim + 1) ≃ Fin n := finCongr hmDim.symm
    have hsub : (Matrix.of fun i j : Fin (mDim + 1) => T.entry i.val j.val) =
        (entryMat T).submatrix eM eM := by ext i j; rfl
    rw [hsub, Matrix.det_submatrix_equiv_self]
    exact hdetT
  obtain ⟨hiStar_eq_m, hmax_m, horth_m, hlo_m, hhi_m⟩ :=
    ratOrthoTargetIntTable_spec T hr_m hc_m hli_m
  have hiStar_lt : intTableMaxSqNormIdx T < n := by
    have hlt := intTableMaxSqNormIdx_lt T (by omega)
    omega
  let iStar : Fin n := ⟨intTableMaxSqNormIdx T, hiStar_lt⟩
  let iCast : Fin (Module.finrank ℤ (intLattice B)) := Fin.cast (finrank_intLattice hB).symm iStar
  let tE := ratListToEuclidean n (ratOrthoTargetIntTable T)
  have heq_norm : ∀ j : Fin (mDim + 1),
      ‖intCol (Matrix.of fun i k : Fin (mDim + 1) => T.entry i.val k.val) j‖ =
      ‖intCol (entryMat T) (Fin.cast hmDim.symm j)‖ := fun j => by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    exact Fintype.sum_equiv (finCongr hmDim.symm) _ _ fun i => by simp [intCol, entryMat]
  have hpi_eq : ‖intCol (Matrix.of fun i k : Fin (mDim + 1) => T.entry i.val k.val)‖ =
      ‖intCol (entryMat T)‖ := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j; rw [heq_norm j]; exact norm_le_pi_norm _ _
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j
      have hj := heq_norm (Fin.cast hmDim j)
      have hj_eq : Fin.cast hmDim.symm (Fin.cast hmDim j) = j := by ext; rfl
      rw [hj_eq] at hj
      rw [← hj]; exact norm_le_pi_norm _ _
  have hpi_eq' : ‖intCol (Matrix.of fun i k : Fin (mDim + 1) => T.entry i.val k.val)‖ =
      ‖intColCast B (entryMat T) hB‖ := hpi_eq.trans (norm_intColCast B (entryMat T) hB).symm
  have hnorm_iStar : ‖intColCast B (entryMat T) hB iCast‖ = ‖intColCast B (entryMat T) hB‖ := by
    rw [norm_intColCast]
    change ‖intCol (entryMat T) iStar‖ = ‖intCol (entryMat T)‖
    have hi_cast : iStar =
        Fin.cast hmDim.symm (MR07Shorten.maxSqNormIndex fun j i => (T.entry i.val j.val : ℚ)) := by
      ext; exact hiStar_eq_m
    rw [hi_cast, ← heq_norm, hmax_m, hpi_eq]
  have ht_norm_eq : ‖tE‖ = ‖ratListToEuclidean (mDim + 1) (ratOrthoTargetIntTable T)‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    exact Fintype.sum_equiv (finCongr hmDim) _ _ fun i => by simp [tE, ratListToEuclidean]
  have ht_lo : (1 / 2 : ℝ) * ‖intColCast B (entryMat T) hB‖ ≤ ‖tE‖ := by
    rw [ht_norm_eq, ← hpi_eq']; exact hlo_m.le
  have ht_hi : ‖tE‖ ≤ (9 / 16 : ℝ) * ‖intColCast B (entryMat T) hB‖ := by
    rw [ht_norm_eq, ← hpi_eq']; exact hhi_m
  have ht_orth : ∀ j, j ≠ iCast → ⟪tE, intColCast B (entryMat T) hB j⟫ = 0 := by
    intro j hj
    let jM : Fin (mDim + 1) := Fin.cast hmDim (Fin.cast (finrank_intLattice hB) j)
    have hjM_ne : jM ≠ MR07Shorten.maxSqNormIndex fun j i => (T.entry i.val j.val : ℚ) := by
      intro heq; apply hj; ext
      have h1 : jM.val =
          (MR07Shorten.maxSqNormIndex fun j i => (T.entry i.val j.val : ℚ)).val :=
        congrArg Fin.val heq
      simpa [jM, iCast, iStar, hiStar_eq_m] using h1
    have hinner_eq : ⟪tE, intColCast B (entryMat T) hB j⟫ =
        ⟪MR07Shorten.toEuclidean
          (fun k : Fin (mDim + 1) => (ratOrthoTargetIntTable T).getD k.val 0),
          intCol (Matrix.of fun i k : Fin (mDim + 1) => T.entry i.val k.val) jM⟫ := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
      exact Fintype.sum_equiv (finCongr hmDim) _ _ fun i => by
        simp [tE, ratListToEuclidean, MR07Shorten.toEuclidean, intColCast, intCol, entryMat, jM]
    rw [hinner_eq]
    exact horth_m jM hjM_ne
  set rSq : ℚ := ((intTableColSqNorm T iStar.val : ℕ) : ℚ) / 64
  have hr_eq : Real.sqrt (rSq : ℝ) = ‖intColCast B (entryMat T) hB‖ / 8 := by
    have hsq : (rSq : ℝ) = (‖intColCast B (entryMat T) hB‖ / 8) ^ 2 := by
      dsimp only [rSq]
      push_cast
      rw [intTableColSqNorm_cast_eq_norm_sq T hr iStar]
      have h1 : ‖intCol (entryMat T) iStar‖ = ‖intColCast B (entryMat T) hB‖ := by
        simpa [intColCast, iCast] using hnorm_iStar
      rw [h1]; ring
    rw [hsq, Real.sqrt_sq (by positivity)]
  have hrSq_pos : 0 < rSq := by
    have hpos : (0 : ℝ) < (rSq : ℝ) := by
      have h2 : 0 < Real.sqrt (rSq : ℝ) := by rw [hr_eq]; positivity
      exact Real.sqrt_pos.mp h2
    exact_mod_cast hpos
  have hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule
      (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B))
      (2 / (2 * Real.sqrt (rSq : ℝ) / ((P.β κ : ℝ) * Real.sqrt n))) 0 - 1 ≤ ε := by
    have hval_r : ((P.β κ : ℝ) * Real.sqrt n) * ZLattice.smoothingParameter (intLattice B) ε <
        Real.sqrt (rSq : ℝ) := by
      rw [hr_eq]; exact hval.radius_gt
    have hdenom_pos : (0 : ℝ) < (P.β κ : ℝ) * Real.sqrt n := by
      have : (0 : ℝ) < P.β κ := Nat.cast_pos.mpr hβ
      have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      positivity
    set sHalf : ℝ := Real.sqrt (rSq : ℝ) / ((P.β κ : ℝ) * Real.sqrt n)
    have hsHalf_pos : 0 < sHalf :=
      div_pos (Real.sqrt_pos.mpr (by exact_mod_cast hrSq_pos)) hdenom_pos
    have hsmoothing_le : ZLattice.smoothingParameter (intLattice B) ε ≤ sHalf :=
      ((lt_div_iff₀' hdenom_pos).mpr hval_r).le
    have hdual1 := (ZLattice.smoothingParameter_le_iff (intLattice B) hsHalf_pos hε_pos).mp
      hsmoothing_le
    have hwidth : 2 / (2 * Real.sqrt (rSq : ℝ) / ((P.β κ : ℝ) * Real.sqrt n)) = 1 / sHalf := by
      dsimp only [sHalf]
      field_simp [hdenom_pos.ne']
    rwa [hwidth]
  have hL_ge1 : 1 ≤ mr07ErrBits n (P.m κ) (P.β κ) κ c := by unfold mr07ErrBits; omega
  have hprec_ok := mr07_hprec_ok (n := n) (m := P.m κ) (β := P.β κ) κ c hn hm hβ
  have heta_le := mr07_singleCall_eta_le (n := n) (m := P.m κ) (β := P.β κ) κ c hn hm hβ
  obtain ⟨hε_le, hpSingle_le⟩ :=
    mr07_singleCall_succProb_ge (m := P.m κ) (β := P.β κ) κ c hm hβ hadv heta_le
  set L := mr07ErrBits n (P.m κ) (P.β κ) κ c
  set prec := mr07Prec n (P.m κ) (P.β κ) κ c
  set maxTrials := mr07MaxTrials n (P.m κ) (P.β κ) κ c
  set trials := mr07AmpTrials (P.m κ) (P.β κ) κ c R
  let incInp : IncGDDInput :=
    ⟨κ, B₀, T, ratOrthoTargetIntTable T, rSq, trials, L, prec, maxTrials, L⟩
  have hinc := mr07IncGDDReduction_succProb_ge P F incInp
    hn hm hβ hrSq_pos hL_ge1 hprec_ok B (entryMat T) hB hdetT hsubT rfl hTeq
    (by norm_num : (0 : ℝ) < 8) hε_pos.le hε_le hq hdual hpSingle_le
  have hmeas_le :
      (ProbComp.eval (mr07GIVPShortenStep P c F ⟨κ, B₀⟩ T)).toOuterMeasure
        {T' | ¬ (MR07Shorten.sqNormProd (intColCast B (entryMat T') hB) ≤
          (13 / 16 : ℝ) ^ 2 * MR07Shorten.sqNormProd (intColCast B (entryMat T) hB))} ≤
      (ProbComp.eval (mr07IncGDDReduction P F incInp)).toOuterMeasure
        {u | ¬ (u.length = n ∧ IncGDD.IsSolution 8 (intLattice B) (intColCast B (entryMat T) hB)
          tE (Real.sqrt (rSq : ℝ)) (listToEuclidean n u))} := by
    have hstep_map :
        ProbComp.eval (mr07GIVPShortenStep P c F ⟨κ, B₀⟩ T) =
        (ProbComp.eval (mr07IncGDDReduction P F incInp)).map
          (guardedUpdateIntTable n T iStar.val) := by
      simp only [mr07GIVPShortenStep, ProbComp.eval_bind, ProbComp.eval_pure]
      rfl
    rw [hstep_map, PMF.toOuterMeasure_map_apply]
    refine (ProbComp.eval _).toOuterMeasure.mono fun u hu hgood => hu ?_
    obtain ⟨hu_len, hu_sol⟩ := hgood
    have hcol_eq := guardedUpdateIntTable_eq_shortenGuardedStep B hB T hr hc hwf iStar u hu_len
      hu_sol.mem
    change MR07Shorten.sqNormProd
      (intColCast B (entryMat (guardedUpdateIntTable n T iStar.val u)) hB) ≤ _
    rw [hcol_eq]
    rw [hr_eq] at hu_sol
    exact (MR07Shorten.shortenGuardedStep_of_incGDD hli hnorm_iStar ht_orth ht_lo ht_hi hu_sol).2
  exact (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _) hmeas_le).trans hinc

/-- Quantitative `GIVP` success probability lower bound (finite-parameter step toward
`[MicciancioRegev2007]` Lemma 5.10 and Corollary 5.13, §5.3, pp. 24–25): at any `κ` where
`64 * (P.n κ)^2 * P.m κ * (P.β κ)^2 ≤ (P.q κ)^2` and `1 / (κ + 1)^c ≤ sisEll2Advantage`, for every
full-rank `P.n κ × P.n κ` integer lattice basis `B`, `mr07GIVPReduction P c F ⟨κ, ofMatrix B⟩`
outputs a `GIVP^{η_ε}_{8 β √n}` solution on `intLattice B` with probability
`≥ 1 - (1 / 4) * 2 ^ (-κ)` at `ε := mr07Eps (P.m κ) (P.β κ) κ c`. -/
theorem mr07GIVPReduction_succProb_ge
    (P : SISParams) (c : ℕ) (F : P.Solver) (κ : ℕ)
    (hn : 1 ≤ P.n κ) (hm : 1 ≤ P.m κ) (hβ : 1 ≤ P.β κ)
    (hq : 64 * (P.n κ) ^ 2 * P.m κ * (P.β κ) ^ 2 ≤ (P.q κ) ^ 2)
    (hadv : 1 / ((κ + 1 : ℝ) ^ c) ≤ (sisEll2Advantage (P.q κ) (P.β κ : ℝ) (F κ) : ℝ))
    (B : Matrix (Fin (P.n κ)) (Fin (P.n κ)) ℤ) (hB : B.det ≠ 0) :
    let n := P.n κ
    let ε := mr07Eps (P.m κ) (P.β κ) κ c
    let φ : Submodule ℤ (EuclideanSpace ℝ (Fin n)) → ℝ :=
      fun L => ZLattice.smoothingParameter L ε
    1 - (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) ≤
      ((ProbComp.eval (mr07GIVPReduction P c F ⟨κ, RowTable.ofMatrix B⟩)).toOuterMeasure
        {T | ∃ S : Matrix (Fin n) (Fin n) ℤ, T = RowTable.ofMatrix S ∧
          GIVP.IsSolution φ (8 * (P.β κ : ℝ) * Real.sqrt n) (intLattice B)
            (intColCast B S hB)}).toReal := by
  intro n ε φ
  have : IsZLattice ℝ (intLattice B) := isZLattice_intLattice hB
  set B₀ : IntTable := RowTable.ofMatrix B
  set R : ℕ := MR07Shorten.shortenRoundBound n (intTableMaxColSqNorm B₀)
  set step := mr07GIVPShortenStep P c F ⟨κ, B₀⟩
  have hqR : 8 * (n : ℝ) * Real.sqrt (P.m κ) * (P.β κ : ℝ) ≤ (P.q κ : ℝ) := by
    have hsq : (8 * (n : ℝ) * Real.sqrt (P.m κ) * (P.β κ : ℝ)) ^ 2 ≤ ((P.q κ : ℝ)) ^ 2 := by
      have hcast : 64 * (n : ℝ) ^ 2 * (P.m κ : ℝ) * (P.β κ : ℝ) ^ 2 ≤ (P.q κ : ℝ) ^ 2 := by
        exact_mod_cast hq
      calc (8 * (n : ℝ) * Real.sqrt (P.m κ) * (P.β κ : ℝ)) ^ 2
          = 64 * (n : ℝ) ^ 2 * (Real.sqrt (P.m κ)) ^ 2 * (P.β κ : ℝ) ^ 2 := by ring
        _ = 64 * (n : ℝ) ^ 2 * (P.m κ : ℝ) * (P.β κ : ℝ) ^ 2 := by
            rw [Real.sq_sqrt (Nat.cast_nonneg _)]
        _ ≤ (P.q κ : ℝ) ^ 2 := hcast
    exact (sq_le_sq₀ (by positivity) (Nat.cast_nonneg _)).mp hsq
  let entryMat : IntTable → Matrix (Fin n) (Fin n) ℤ :=
    fun T => Matrix.of fun i j => T.entry i.val j.val
  let GoodState : IntTable → Prop := fun T =>
    T.numRows = n ∧ T.numCols = n ∧ T.WellFormed ∧
    LinearIndependent ℝ (intColCast B (entryMat T) hB) ∧
    (∀ j, intColCast B (entryMat T) hB j ∈ intLattice B)
  let Solved : IntTable → Prop := fun T =>
    ∃ S : Matrix (Fin n) (Fin n) ℤ, T = RowTable.ofMatrix S ∧
      GIVP.IsSolution φ (8 * (P.β κ : ℝ) * Real.sqrt n) (intLattice B) (intColCast B S hB)
  let potential : IntTable → ℝ := fun T =>
    MR07Shorten.sqNormProd (intColCast B (entryMat T) hB)
  let ρ : ℝ := (13 / 16 : ℝ) ^ 2
  have hρ0 : 0 ≤ ρ := by positivity
  set pSingle : ℝ := 1 / (12 * (2 * (P.β κ : ℝ) * (P.m κ : ℝ)) * ((κ + 1 : ℝ) ^ c))
  set trials : ℕ := mr07AmpTrials (P.m κ) (P.β κ) κ c R
  let roundErr : ℝ := (1 - pSingle) ^ trials
  have hp_le1 : pSingle ≤ 1 := by
    dsimp only [pSingle]
    rw [div_le_one (by
      have hmR : (0 : ℝ) < P.m κ := Nat.cast_pos.mpr hm
      have hβR : (0 : ℝ) < P.β κ := Nat.cast_pos.mpr hβ
      positivity)]
    have hm1 : (1 : ℝ) ≤ P.m κ := by exact_mod_cast hm
    have hβ1 : (1 : ℝ) ≤ P.β κ := by exact_mod_cast hβ
    have hκc : (1 : ℝ) ≤ ((κ + 1 : ℝ) ^ c) := one_le_pow₀ (by linarith)
    nlinarith [one_le_mul_of_one_le_of_one_le hβ1 hm1]
  have herr0 : 0 ≤ roundErr := pow_nonneg (by linarith) trials
  have hB₀_mat : entryMat B₀ = B := by
    ext i j; exact RowTable.entry_ofMatrix_of_lt B i.isLt j.isLt
  have hGood₀ : GoodState B₀ := by
    refine ⟨rfl, rfl, RowTable.wellFormed_ofMatrix B, ?_, ?_⟩
    · rw [hB₀_mat]
      let e : Fin (Module.finrank ℤ (intLattice B)) ≃ Fin n := finCongr (finrank_intLattice hB)
      exact (linearIndependent_equiv e).mpr ((linearIndependent_intCol_iff_det_ne_zero B).mpr hB)
    · intro j
      rw [hB₀_mat]
      exact Submodule.subset_span ⟨Fin.cast (finrank_intLattice hB) j, rfl⟩
  have hGood_props : ∀ T, GoodState T →
      T = RowTable.ofMatrix (entryMat T) ∧ (entryMat T).det ≠ 0 ∧
      intLattice (entryMat T) ≤ intLattice B := by
    intro T ⟨hr, hc, hwf, hli, hmem⟩
    have hTeq := intTable_eq_ofMatrix_of_wellFormed T hr hc hwf
    let e : Fin (Module.finrank ℤ (intLattice B)) ≃ Fin n := finCongr (finrank_intLattice hB)
    have hli_col : LinearIndependent ℝ (intCol (entryMat T)) := (linearIndependent_equiv e).mp hli
    have hdet : (entryMat T).det ≠ 0 := (linearIndependent_intCol_iff_det_ne_zero _).mp hli_col
    have hsub : intLattice (entryMat T) ≤ intLattice B := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      simpa [intColCast] using hmem (Fin.cast (finrank_intLattice hB).symm j)
    exact ⟨hTeq, hdet, hsub⟩
  have hstep_support : ∀ T, GoodState T → ∀ T' ∈ (ProbComp.eval (step T)).support,
      ∃ (u : List ℤ) (iStar : Fin n),
        T' = guardedUpdateIntTable n T iStar.val u ∧
        u.length = n ∧ listToEuclidean n u ∈ intLattice B ∧
        intColCast B (entryMat T') hB =
          MR07Shorten.shortenGuardedStep (intLattice B) (intColCast B (entryMat T) hB)
            (Fin.cast (finrank_intLattice hB).symm iStar) (listToEuclidean n u) := by
    intro T hGood T' hT'
    obtain ⟨hTeq, hdetT, hsubT⟩ := hGood_props T hGood
    obtain ⟨hr, hc, hwf, _, _⟩ := hGood
    unfold step mr07GIVPShortenStep at hT'
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hT'
    obtain ⟨u, hu, rfl⟩ := hT'
    obtain ⟨hu_len, hu_mem⟩ :=
      mem_support_mr07IncGDDReduction_mem_intLattice P F _ B (entryMat T) hB hdetT hsubT rfl hTeq hu
    let iStar : Fin n :=
      ⟨intTableMaxSqNormIdx T, by have hlt := intTableMaxSqNormIdx_lt T (by omega); omega⟩
    exact ⟨u, iStar, rfl, hu_len, hu_mem,
      guardedUpdateIntTable_eq_shortenGuardedStep B hB T hr hc hwf iStar u hu_len hu_mem⟩
  have hGood_pres : ∀ T, GoodState T →
      ∀ T' ∈ (ProbComp.eval (step T)).support, GoodState T' := by
    intro T hGood T' hT'
    obtain ⟨u, iStar, rfl, _, _, hcol_eq⟩ := hstep_support T hGood T' hT'
    obtain ⟨hr, hc, hwf, hli, hmem⟩ := hGood
    have hwf' := (guardedUpdateIntTable_invariants n T iStar.val u).2 ⟨hr, hc, hwf⟩
    have hinv := MR07Shorten.shortenGuardedStep_invariants hli hmem
      (Fin.cast (finrank_intLattice hB).symm iStar) (listToEuclidean n u)
    exact ⟨hwf'.1, hwf'.2.1, hwf'.2.2.1, hcol_eq ▸ hinv.1, hcol_eq ▸ hinv.2.1⟩
  have hSolved_pres : ∀ T, GoodState T → Solved T →
      ∀ T' ∈ (ProbComp.eval (step T)).support, Solved T' := by
    intro T hGood hSol T' hT'
    obtain ⟨u, iStar, rfl, _, _, hcol_eq⟩ := hstep_support T hGood T' hT'
    obtain ⟨hr, hc, hwf, hli, hmem⟩ := hGood
    obtain ⟨S, hTS, hGIVP⟩ := hSol
    have hS_eq : S = entryMat T := by
      ext i j; rw [hTS]; exact (RowTable.entry_ofMatrix_of_lt S i.isLt j.isLt).symm
    subst hS_eq
    have hwf' := (guardedUpdateIntTable_invariants n T iStar.val u).2 ⟨hr, hc, hwf⟩
    have hinv := MR07Shorten.shortenGuardedStep_invariants hli hmem
      (Fin.cast (finrank_intLattice hB).symm iStar) (listToEuclidean n u)
    refine ⟨entryMat (guardedUpdateIntTable n T iStar.val u),
      intTable_eq_ofMatrix_of_wellFormed _ hwf'.1 hwf'.2.1 hwf'.2.2.1, ?_⟩
    rw [hcol_eq]
    refine ⟨hinv.1, hinv.2.1, fun j => ?_⟩
    have hpi_T : ‖intColCast B (entryMat T) hB‖ ≤
        8 * (P.β κ : ℝ) * Real.sqrt n * φ (intLattice B) := by
      have hφ0 : 0 ≤ φ (intLattice B) := ZLattice.smoothingParameter_nonneg (intLattice B) ε
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      exact hGIVP.norm_le
    exact (norm_le_pi_norm _ j).trans (hinv.2.2.trans hpi_T)
  have hDrop : ∀ T, GoodState T → ¬ Solved T →
      ((ProbComp.eval (step T)).toOuterMeasure
        {T' | ¬ (potential T' ≤ ρ * potential T)}).toReal ≤ roundErr := by
    intro T hGood hnotSol
    obtain ⟨hTeq, _, _⟩ := hGood_props T hGood
    obtain ⟨hr, hc, hwf, hli, hmem⟩ := hGood
    have hnotGIVP : ¬ GIVP.IsSolution φ (8 * ((P.β κ : ℝ) * Real.sqrt n)) (intLattice B)
        (intColCast B (entryMat T) hB) := by
      intro hsol
      apply hnotSol
      exact ⟨entryMat T, hTeq, by simpa only [mul_assoc] using hsol⟩
    exact mr07GIVPShortenStep_drop_failure_le P c F κ hn hm hβ hqR hadv B hB
      T hr hc hwf hli hmem hnotGIVP
  have hPot_lb : ∀ T, GoodState T → 1 ≤ potential T := by
    intro T ⟨_, _, _, hli, hmem⟩
    refine MR07Shorten.one_le_sqNormProd hli fun i j => ?_
    exact Cslib.Algorithms.LatticeReduction.exists_int_inner_of_mem_span (fun a b => by
      simp only [intCol, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
      exact ⟨∑ k : Fin n, B k b * B k a, by push_cast; rfl⟩) (hmem i) (hmem j)
  have hPot_end : ρ ^ R * potential B₀ < 1 := by
    set M := intTableMaxColSqNorm B₀
    have hB_le : ∀ j : Fin (Module.finrank ℤ (intLattice B)),
        ‖intColCast B (entryMat B₀) hB j‖ ^ 2 ≤ (M : ℝ) := fun j => by
      let k : Fin n := Fin.cast (finrank_intLattice hB) j
      have h1 : ‖intColCast B (entryMat B₀) hB j‖ ^ 2 = ((intTableColSqNorm B₀ k.val : ℕ) : ℝ) := by
        change ‖intCol (Matrix.of fun i l => B₀.entry i.val l.val) k‖ ^ 2 = _
        exact (intTableColSqNorm_cast_eq_norm_sq B₀ rfl k).symm
      rw [h1]
      exact_mod_cast intTableColSqNorm_le_max B₀ k.isLt
    have hpot_le : potential B₀ ≤ (M : ℝ) ^ n := by
      have h1 := MR07Shorten.sqNormProd_le_pow hB_le
      simpa only [finrank_intLattice hB] using h1
    have hlt1 : ρ ^ R * (M : ℝ) ^ n < 1 := by
      have hM_lt : (M : ℝ) < (2 : ℝ) ^ (Nat.log 2 M + 1) := by
        exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) M
      have hbase : ρ ^ 2 < 1 / 2 := by dsimp only [ρ]; norm_num
      have hstep1 : (ρ ^ 2) ^ (Nat.log 2 M + 1) ≤ (1 / 2 : ℝ) ^ (Nat.log 2 M + 1) :=
        pow_le_pow_left₀ (by positivity) hbase.le _
      have hone : (ρ ^ 2) ^ (Nat.log 2 M + 1) * (M : ℝ) < 1 := by
        calc (ρ ^ 2) ^ (Nat.log 2 M + 1) * (M : ℝ)
            ≤ (1 / 2 : ℝ) ^ (Nat.log 2 M + 1) * (M : ℝ) :=
              mul_le_mul_of_nonneg_right hstep1 (Nat.cast_nonneg M)
          _ < (1 / 2 : ℝ) ^ (Nat.log 2 M + 1) * (2 : ℝ) ^ (Nat.log 2 M + 1) :=
              mul_lt_mul_of_pos_left hM_lt (by positivity)
          _ = 1 := by rw [← mul_pow]; norm_num
      have hrew : ρ ^ R * (M : ℝ) ^ n = ((ρ ^ 2) ^ (Nat.log 2 M + 1) * (M : ℝ)) ^ n := by
        have hR : R = 2 * (Nat.log 2 M + 1) * n := by
          change 2 * n * (Nat.log 2 M + 1) = _; ring
        rw [hR, mul_pow, pow_mul, pow_mul]
      rw [hrew]
      exact pow_lt_one₀ (by positivity) hone (by omega)
    exact (mul_le_mul_of_nonneg_left hpot_le (by positivity)).trans_lt hlt1
  let inv : ℕ → IntTable → Prop := fun i T =>
    GoodState T ∧ (Solved T ∨ potential T ≤ ρ ^ i * potential B₀)
  have hinit : inv 0 B₀ := ⟨hGood₀, Or.inr (by simp)⟩
  have hstep_err : ∀ i < R, ∀ T, inv i T →
      ((ProbComp.eval (step T)).toOuterMeasure {T' | ¬ inv (i + 1) T'}).toReal ≤ roundErr := by
    intro i _ T ⟨hGoodT, hdisj⟩
    by_cases hSol : Solved T
    · have hzero : (ProbComp.eval (step T)).toOuterMeasure {T' | ¬ inv (i + 1) T'} = 0 := by
        rw [PMF.toOuterMeasure_apply]
        refine tsum_eq_zero_iff.mpr fun T' => ?_
        by_cases hmem : T' ∈ (ProbComp.eval (step T)).support
        · have hnot : T' ∉ ({T' | ¬ inv (i + 1) T'} : Set IntTable) :=
            fun h => h ⟨hGood_pres T hGoodT T' hmem, Or.inl (hSolved_pres T hGoodT hSol T' hmem)⟩
          rw [Set.indicator_of_notMem hnot]
        · have h0 : ProbComp.eval (step T) T' = 0 := by simpa [PMF.mem_support_iff] using hmem
          simp [h0]
      rw [hzero, ENNReal.toReal_zero]; exact herr0
    · have hpotT : potential T ≤ ρ ^ i * potential B₀ := hdisj.resolve_left hSol
      have hmeas : (ProbComp.eval (step T)).toOuterMeasure {T' | ¬ inv (i + 1) T'} ≤
          (ProbComp.eval (step T)).toOuterMeasure {T' | ¬ (potential T' ≤ ρ * potential T)} := by
        rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
        refine tsum_le_tsum fun T' => ?_
        by_cases hmem : T' ∈ (ProbComp.eval (step T)).support
        · by_cases h1 : T' ∈ ({T' | ¬ inv (i + 1) T'} : Set IntTable)
          · have h2 : T' ∈ ({T' | ¬ (potential T' ≤ ρ * potential T)} : Set IntTable) := by
              intro hle; apply h1
              refine ⟨hGood_pres T hGoodT T' hmem, Or.inr ?_⟩
              calc potential T' ≤ ρ * potential T := hle
                _ ≤ ρ * (ρ ^ i * potential B₀) := mul_le_mul_of_nonneg_left hpotT hρ0
                _ = ρ ^ (i + 1) * potential B₀ := by rw [pow_succ']; ring
            rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
          · rw [Set.indicator_of_notMem h1]; exact zero_le
        · have h0 : ProbComp.eval (step T) T' = 0 := by simpa [PMF.mem_support_iff] using hmem
          simp [Set.indicator_apply, h0]
      exact (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _) hmeas).trans
        (hDrop T hGoodT hSol)
  have hloop := ProbComp.iterate_failure_toReal_le_mul R step B₀ inv hinit herr0 hstep_err
  have hsub : {T | ¬ Solved T} ⊆ {T | ¬ inv R T} := fun T hnotSol ⟨hGoodT, hdisj⟩ => by
    linarith [hPot_lb T hGoodT, hdisj.resolve_left hnotSol, hPot_end]
  have hfail_le :
      ((ProbComp.eval (OracleComp.iterate R step B₀)).toOuterMeasure {T | ¬ Solved T}).toReal ≤
        (R : ℝ) * roundErr :=
    (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
      ((ProbComp.eval (OracleComp.iterate R step B₀)).toOuterMeasure.mono hsub)).trans hloop
  have htoR :
      ((ProbComp.eval (OracleComp.iterate R step B₀)).toOuterMeasure {T | Solved T}).toReal +
      ((ProbComp.eval (OracleComp.iterate R step B₀)).toOuterMeasure {T | ¬ Solved T}).toReal = 1 :=
    Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl
      (ProbComp.eval (OracleComp.iterate R step B₀)) {T | Solved T}
  have hround_le : roundErr ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) / ((R : ℝ) + 1) :=
    mr07_amp_round_failure_le κ c R hm hβ le_rfl hp_le1
  have htot := (mr07_total_succProb_ge κ R hround_le).2
  change 1 - (1 / 4 : ℝ) * (2 : ℝ) ^ (-(κ : ℤ)) ≤
    ((ProbComp.eval (OracleComp.iterate R step B₀)).toOuterMeasure {T | Solved T}).toReal
  linarith

/-- Corollary of `mr07GIVPReduction_succProb_ge`: `mr07GIVPReduction` succeeds with probability at
least `1 / 2` for every security parameter `κ : ℕ` satisfying the finite parameter hypotheses. -/
theorem mr07GIVPReduction_succProb_ge_half
    (P : SISParams) (c : ℕ) (F : P.Solver) (κ : ℕ)
    (hn : 1 ≤ P.n κ) (hm : 1 ≤ P.m κ) (hβ : 1 ≤ P.β κ)
    (hq : 64 * (P.n κ) ^ 2 * P.m κ * (P.β κ) ^ 2 ≤ (P.q κ) ^ 2)
    (hadv : 1 / ((κ + 1 : ℝ) ^ c) ≤ (sisEll2Advantage (P.q κ) (P.β κ : ℝ) (F κ) : ℝ))
    (B : Matrix (Fin (P.n κ)) (Fin (P.n κ)) ℤ) (hB : B.det ≠ 0) :
    let n := P.n κ
    let ε := mr07Eps (P.m κ) (P.β κ) κ c
    let φ : Submodule ℤ (EuclideanSpace ℝ (Fin n)) → ℝ :=
      fun L => ZLattice.smoothingParameter L ε
    (1 / 2 : ℝ) ≤
      ((ProbComp.eval (mr07GIVPReduction P c F ⟨κ, RowTable.ofMatrix B⟩)).toOuterMeasure
        {T | ∃ S : Matrix (Fin n) (Fin n) ℤ, T = RowTable.ofMatrix S ∧
          GIVP.IsSolution φ (8 * (P.β κ : ℝ) * Real.sqrt n) (intLattice B)
            (intColCast B S hB)}).toReal := by
  have h1 := mr07GIVPReduction_succProb_ge P c F κ hn hm hβ hq hadv B hB
  have h2inv : (2 : ℝ) ^ (-(κ : ℤ)) ≤ 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  linarith

end Cslib.Crypto.SIS.MR07
