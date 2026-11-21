/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Rational.Runtime.Determinant
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Foundations.Analysis.Lattice.Dual
public import CslibFrontier.Foundations.Probability.Gaussian.Discrete
public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.RejectionSampling
import CslibFrontier.Computability.Probabilistic.Traverse
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.CloseTo.UniformNat
import CslibFrontier.Foundations.Probability.Gaussian.OffCenterTail
import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
import CslibFrontier.Probability.DDGTree.Rejection
import CslibFrontier.Probability.Option
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.StatisticalDistance.Product
import CslibFrontier.Probability.StatisticalDistance.TotalVariation
import CslibFrontier.Probability.UniformNat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Strict-PPT 1-D discrete Gaussian, grid Gaussian, and lattice quotient samplers

This module constructs three strict probabilistic polynomial-time (`IsPPTOn`) sampling primitives
for lattice reductions, together with explicit finite-parameter statistical-distance (`CloseTo`)
certificates:

1. `sampleZ`: a capped-trial strict-PPT 1-D discrete Gaussian sampler over `ℤ` that uses
   Machin's formula for `π` and range-reduced fixed-point evaluation of `exp(-π (x - c)² / s²)`
   to certify `IsPPTOn` directly against `Turing.MultiTapeTM.ComputableInPolyTime`, with total
   variation distance bounded under a 1-D dual-mass premise `ρ_{1/s}(ℤ* \ {0}) ≤ ε ≤ 1/2`.
2. `sampleGridGaussian`: an `n`-coordinate product of `sampleZ` calls at scaled width `q · s`
   and centers `q · tᵢ`, followed by exact rational linear solving (`ratSolve`) and Babai/grid
   floor reduction `gridReduceInt`.
3. `sampleQuotientModS`: an HNF-free strict-PPT quotient sampler for `L(B) ∩ P(S)` that computes
   the index `D = |det S| / |det B|` via staged Bird determinants (`detRows`), draws `n`
   approximately uniform residues modulo `D` via `sampleModNat`, and reduces modulo `S` using
   exact `ratSolve` (`quotientReduceInt`).

## Main definitions

* `Cslib.Probability.SampleZInput`, `Cslib.Probability.SampleZInput.enc`: input record and
  framing encoding for `sampleZ`.
* `Cslib.Probability.sampleZ`: strict-PPT capped-trial 1-D discrete Gaussian sampler.
* `Cslib.Probability.intLatticeReal`, `Cslib.Probability.discreteGaussianInt`: the canonical
  1-D integer lattice `ℤ ⊂ ℝ` and its discrete Gaussian `PMF ℤ`.
* `Cslib.Probability.GridSampleInput`, `Cslib.Probability.GridSampleInput.enc`,
  `Cslib.Probability.gridReduceInt`, `Cslib.Probability.sampleGridGaussian`: grid Gaussian
  sampler and exact integer reduction map.
* `Cslib.Probability.QuotientSampleInput`, `Cslib.Probability.QuotientSampleInput.enc`,
  `Cslib.Probability.quotientIndex`, `Cslib.Probability.quotientReduceInt`,
  `Cslib.Probability.sampleQuotientModS`: HNF-free quotient sampler and reduction map.

## Main results

* `Cslib.Probability.isPPTOn_sampleZ`: strict-PPT certificate for `sampleZ`.
* `Cslib.Probability.closeTo_eval_sampleZ_discreteGaussian`: explicit `CloseTo` bound between
  `sampleZ` and `discreteGaussianInt` decomposing into timeout, fixed-point approximation, and
  off-center 1-D Gaussian tail terms.
* `Cslib.Probability.isPPTOn_sampleGridGaussian`,
  `Cslib.Probability.closeTo_eval_sampleGridGaussian_pi`: strict-PPT and `CloseTo` certificates
  for `sampleGridGaussian` against `PMF.piFin` pushed forward by `gridReduceInt`.
* `Cslib.Probability.isPPTOn_sampleQuotientModS`,
  `Cslib.Probability.closeTo_eval_sampleQuotientModS_pi`: strict-PPT and `CloseTo` certificates
  for `sampleQuotientModS` against `PMF.piFin` of `PMF.uniformOfFintype (ZMod D)` pushed forward
  by `quotientReduceInt`.

## References

* [GentryPeikertVaikuntanathan2008], Section 4.1, Lemma 4.3 (p. 15) and Lemma 4.2 (p. 14) of the
  August 25, 2008 full version: 1-D discrete Gaussian sampling over `ℤ` via rejection sampling
  on `[c - s · t, c + s · t]`. The present module implements the capped-trial strict-PPT variant
  (explicit `maxTrials` cap and finite dyadic precision `prec`, with an explicit timeout term
  rather than expected-time rejection) and uses the dual-mass premise `ρ_{1/s}(ℤ* \ {0}) ≤ ε`.
* [MicciancioRegev2007], Section 2.2 (p. 8) and Lemma 5.7 (p. 20) of the December 27, 2005
  author's copy: grid Gaussian reduction and uniform coset sampling in `L(B) ∩ P(S)`.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Exact rational floor in polynomial time -/

/-- Exact rational floor computed from numerator and denominator using unsigned division. -/
private def ratFloor (q : ℚ) : ℤ :=
  if q.num < 0 then
    -(((q.num.natAbs + q.den - 1) / q.den : ℕ) : ℤ)
  else
    ((q.num.toNat / q.den : ℕ) : ℤ)

private theorem ratFloor_eq_intFloor (q : ℚ) : ratFloor q = Int.floor q := by
  symm
  rw [Int.floor_eq_iff]
  have hq_eq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  have hd : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.den_pos
  have hd_pos : 0 < q.den := q.den_pos
  unfold ratFloor
  split_ifs with hneg
  · set m : ℕ := (q.num.natAbs + q.den - 1) / q.den
    have hnum_eq : q.num = -(q.num.natAbs : ℤ) := by
      have := Int.ofNat_natAbs_of_nonpos hneg.le
      omega
    have hlo : q.num.natAbs ≤ m * q.den := by
      have hdiv := Nat.div_add_mod (q.num.natAbs + q.den - 1) q.den
      have hmod := Nat.mod_lt (q.num.natAbs + q.den - 1) hd_pos
      have hm_eq : q.den * m + (q.num.natAbs + q.den - 1) % q.den = q.num.natAbs + q.den - 1 := hdiv
      rw [mul_comm] at hm_eq
      omega
    have hpos : 0 < q.num.natAbs := Int.natAbs_pos.mpr hneg.ne
    have hm_pos : 1 ≤ m := (Nat.le_div_iff_mul_le hd_pos).mpr (by omega)
    have hhi : (m - 1) * q.den < q.num.natAbs := by
      have hmul := Nat.div_mul_le_self (q.num.natAbs + q.den - 1) q.den
      change m * q.den ≤ q.num.natAbs + q.den - 1 at hmul
      have hsub : (m - 1) * q.den + q.den = m * q.den := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel hm_pos]
      omega
    have hlo' : (q.num.natAbs : ℚ) ≤ (m : ℚ) * (q.den : ℚ) := by exact_mod_cast hlo
    have hhi' : ((m : ℚ) - 1) * (q.den : ℚ) < (q.num.natAbs : ℚ) := by
      have hcast : (((m - 1) * q.den : ℕ) : ℚ) = ((m : ℚ) - 1) * (q.den : ℚ) := by
        rw [Nat.cast_mul, Nat.cast_sub hm_pos, Nat.cast_one]
      rw [← hcast]
      exact_mod_cast hhi
    rw [hq_eq, hnum_eq, Int.cast_neg, Int.cast_natCast, Int.cast_neg, Int.cast_natCast]
    constructor
    · rw [le_div_iff₀ hd]
      linarith
    · rw [div_lt_iff₀ hd]
      linarith
  · push Not at hneg
    set m : ℕ := q.num.toNat / q.den
    have hnum_eq : q.num = (q.num.toNat : ℤ) := (Int.toNat_of_nonneg hneg).symm
    have hlo : m * q.den ≤ q.num.toNat := Nat.div_mul_le_self q.num.toNat q.den
    have hhi : q.num.toNat < (m + 1) * q.den := by
      have h := Nat.lt_mul_div_succ q.num.toNat hd_pos
      rwa [mul_comm] at h
    have hlo' : (m : ℚ) * (q.den : ℚ) ≤ (q.num.toNat : ℚ) := by exact_mod_cast hlo
    have hhi' : (q.num.toNat : ℚ) < ((m : ℚ) + 1) * (q.den : ℚ) := by exact_mod_cast hhi
    rw [hq_eq, hnum_eq, Int.cast_natCast, Int.cast_natCast]
    constructor
    · rw [le_div_iff₀ hd]
      exact hlo'
    · rw [div_lt_iff₀ hd]
      exact hhi'

private theorem ratFloor_eq_ratFloor (q : ℚ) : ratFloor q = q.floor := by
  rw [ratFloor_eq_intFloor]
  rfl

private theorem computableInPolyTime_ratFloor : ComputableInPolyTime ratFloor encRat encIntBin := by
  unfold ratFloor
  have hnum : ComputableInPolyTime Rat.num encRat encIntBin := rat_num
  have hden : ComputableInPolyTime Rat.den encRat encNat := rat_den
  have hcond : ComputableInPolyTime (fun q : ℚ => decide (q.num < 0)) encRat encBool :=
    intBin_lt' hnum (const 0)
  have hneg : ComputableInPolyTime
      (fun q : ℚ => -(((q.num.natAbs + q.den - 1) / q.den : ℕ) : ℤ)) encRat encIntBin :=
    intBin_neg.comp (intBin_natCast.comp
      (binary_div' (binary_sub' (binary_add' (intBin_natAbs.comp hnum) hden) (const 1)) hden))
  have hnonneg : ComputableInPolyTime
      (fun q : ℚ => ((q.num.toNat / q.den : ℕ) : ℤ)) encRat encIntBin :=
    intBin_natCast.comp (binary_div' (intBin_toNat.comp hnum) hden)
  exact ite_decide hcond hneg hnonneg

/-! ### 2. Machin's formula and pure-`ℕ` fixed-point `π` approximation -/

private theorem machin_pi_div_four :
    4 * Real.arctan (1 / 5) - Real.arctan (1 / 239) = Real.pi / 4 := by
  have h1 : Real.arctan (1 / 5) + Real.arctan (1 / 5) = Real.arctan (5 / 12) := by
    rw [Real.arctan_add (by norm_num)]
    congr 1; norm_num
  have h2 : Real.arctan (5 / 12) + Real.arctan (5 / 12) = Real.arctan (120 / 119) := by
    rw [Real.arctan_add (by norm_num)]
    congr 1; norm_num
  have h3 : Real.arctan (120 / 119) + Real.arctan (-(1 / 239)) = Real.arctan 1 := by
    rw [Real.arctan_add (by norm_num)]
    congr 1; norm_num
  rw [Real.arctan_neg, Real.arctan_one] at h3
  linarith

private theorem arctan_alternating_remainder {x : ℝ} (hx0 : 0 ≤ x) (N : ℕ) :
    |Real.arctan x - ∑ k ∈ Finset.range (2 * N),
        ((-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1 : ℝ))| ≤
      x ^ (4 * N + 1) / (4 * N + 1 : ℝ) := by
  let g : ℝ → ℝ := fun t =>
    Real.arctan t - ∑ k ∈ Finset.range (2 * N), ((-1 : ℝ) ^ k * t ^ (2 * k + 1) / (2 * k + 1 : ℝ))
  have hderiv (t : ℝ) : HasDerivAt g (t ^ (4 * N) / (1 + t ^ 2)) t := by
    have hsum : HasDerivAt
        (fun y : ℝ => ∑ k ∈ Finset.range (2 * N),
          ((-1 : ℝ) ^ k * y ^ (2 * k + 1) / (2 * k + 1 : ℝ)))
        (∑ k ∈ Finset.range (2 * N), (-t ^ 2) ^ k) t := by
      have hterm (k : ℕ) :
          HasDerivAt (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (2 * k + 1) / (2 * k + 1 : ℝ))
            ((-t ^ 2) ^ k) t := by
        have hp := ((hasDerivAt_pow (2 * k + 1) t).const_mul ((-1 : ℝ) ^ k)).div_const
          (2 * k + 1 : ℝ)
        convert hp using 1
        have hnz : (2 * k + 1 : ℝ) ≠ 0 := by positivity
        have heq : (2 * k + 1 : ℕ) - 1 = 2 * k := by omega
        rw [heq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        rw [mul_comm ((-1 : ℝ) ^ k), mul_assoc, mul_div_cancel_left₀ _ hnz,
          pow_mul, ← mul_pow, mul_neg_one]
      exact HasDerivAt.fun_sum fun k _ => hterm k
    have hdiff := (Real.hasDerivAt_arctan t).sub hsum
    convert hdiff using 1
    have hden : 1 + t ^ 2 ≠ 0 := by positivity
    have hgeom : (∑ k ∈ Finset.range (2 * N), (-t ^ 2) ^ k) * (1 + t ^ 2) =
        1 - (-t ^ 2) ^ (2 * N) := by
      have h := geom_sum_mul (-t ^ 2) (2 * N)
      have hsub : (-t ^ 2 : ℝ) - 1 = -(1 + t ^ 2) := by ring
      rw [hsub] at h
      linarith
    have heven : (-t ^ 2) ^ (2 * N) = t ^ (4 * N) := by
      rw [pow_mul, neg_sq, ← pow_mul, ← pow_mul]
      congr 1; ring
    rw [heven] at hgeom
    field_simp
    linarith
  have hg0 : g 0 = 0 := by
    simp [g]
  have ht4_nn (t : ℝ) : 0 ≤ t ^ (4 * N) := by
    rw [show 4 * N = 2 * (2 * N) by ring, pow_mul]
    positivity
  have hlo : 0 ≤ g x := by
    have hmono : MonotoneOn g (Set.Icc 0 x) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
        (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
        (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt)
        fun t _ => ?_
      rw [(hderiv t).deriv]
      exact div_nonneg (ht4_nn t) (by positivity)
    simpa [hg0] using hmono (Set.left_mem_Icc.mpr hx0) (Set.right_mem_Icc.mpr hx0) hx0
  have hhi : g x ≤ x ^ (4 * N + 1) / (4 * N + 1 : ℝ) := by
    let h : ℝ → ℝ := fun t => t ^ (4 * N + 1) / (4 * N + 1 : ℝ) - g t
    have hhderiv (t : ℝ) : HasDerivAt h (t ^ (4 * N) - t ^ (4 * N) / (1 + t ^ 2)) t := by
      have hp : HasDerivAt (fun y : ℝ => y ^ (4 * N + 1) / (4 * N + 1 : ℝ)) (t ^ (4 * N)) t := by
        have h1 := (hasDerivAt_pow (4 * N + 1) t).div_const (4 * N + 1 : ℝ)
        convert h1 using 1
        have hnz : (4 * N + 1 : ℝ) ≠ 0 := by positivity
        have heq : (4 * N + 1 : ℕ) - 1 = 4 * N := by omega
        rw [heq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        exact (mul_div_cancel_left₀ _ hnz).symm
      exact hp.sub (hderiv t)
    have hmono : MonotoneOn h (Set.Icc 0 x) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
        (fun t _ => (hhderiv t).continuousAt.continuousWithinAt)
        (fun t _ => (hhderiv t).differentiableAt.differentiableWithinAt)
        fun t _ => ?_
      rw [(hhderiv t).deriv]
      have h1 : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
      have hdiv : t ^ (4 * N) / (1 + t ^ 2) ≤ t ^ (4 * N) :=
        div_le_self (ht4_nn t) h1
      linarith
    have hh0 : h 0 = 0 := by simp [h, hg0]
    have := hmono (Set.left_mem_Icc.mpr hx0) (Set.right_mem_Icc.mpr hx0) hx0
    dsimp only [h] at this
    linarith [hh0]
  rw [abs_of_nonneg hlo]
  exact hhi

/-! ### 3. Pure-`ℕ` alternating `arctan (1 / d)` fixed-point loop -/

/-- One step of fixed-point `arctan(1/d)` series at scale `S`: state is `(k, (powTerm, acc))`. -/
private def arctanStep (dSq : ℕ) (st : ℕ × (ℕ × ℕ)) : ℕ × (ℕ × ℕ) :=
  let k := st.1
  let powTerm := st.2.1
  let acc := st.2.2
  let term := powTerm / (2 * k + 1)
  let acc' := if k % 2 = 0 then acc + term else acc - term
  (k + 1, (powTerm / dSq, acc'))

/-- Fixed-point approximation to `2 ^ M * arctan (1 / d)` using `2 * L` terms. -/
private def arctanInvApprox (d M L : ℕ) : ℕ :=
  ((arctanStep (d * d))^[2 * L] (0, (2 ^ M / d, 0))).2.2

private theorem arctanStep_fst (dSq : ℕ) (st : ℕ × (ℕ × ℕ)) (i : ℕ) :
    ((arctanStep dSq)^[i] st).1 = st.1 + i := by
  induction i generalizing st with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [arctanStep]; omega

private theorem arctanStep_powTerm (d M : ℕ) (i : ℕ) :
    ((arctanStep (d * d))^[i] (0, (2 ^ M / d, 0))).2.1 ≤ 2 ^ M := by
  induction i with
  | zero => exact Nat.div_le_self _ _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (Nat.div_le_self _ _).trans ih

private theorem arctanStep_inv (d M : ℕ) (i : ℕ) :
    let st := (arctanStep (d * d))^[i] (0, (2 ^ M / d, 0))
    let term := st.2.1 / (2 * st.1 + 1)
    st.2.1 ≤ 2 ^ M ∧
      (if i % 2 = 0 then st.2.2 + term ≤ 2 ^ M else term ≤ st.2.2 ∧ st.2.2 ≤ 2 ^ M) := by
  induction i with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.zero_mod, ↓reduceIte, zero_add]
    exact ⟨Nat.div_le_self _ _, (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)⟩
  | succ i ih =>
    set st := (arctanStep (d * d))^[i] (0, (2 ^ M / d, 0)) with hst_def
    have hfst : st.1 = i := by simpa [hst_def] using arctanStep_fst (d * d) (0, (2 ^ M / d, 0)) i
    have hpow_le : st.2.1 ≤ 2 ^ M := ih.1
    have hterm_le : (st.2.1 / (d * d)) / (2 * (i + 1) + 1) ≤ st.2.1 / (2 * i + 1) := by
      exact (Nat.div_le_div_right (Nat.div_le_self _ _)).trans
        (Nat.div_le_div_left (by omega) (by omega))
    rw [Function.iterate_succ_apply']
    dsimp only [arctanStep]
    rw [← hst_def, hfst]
    refine ⟨(Nat.div_le_self _ _).trans hpow_le, ?_⟩
    by_cases hev : i % 2 = 0
    · have hodd : (i + 1) % 2 ≠ 0 := by omega
      have hih : st.2.2 + st.2.1 / (2 * i + 1) ≤ 2 ^ M := by
        have h2 := ih.2
        simp only [hev, ↓reduceIte, hfst] at h2
        exact h2
      simp only [hev, hodd, ↓reduceIte]
      exact ⟨hterm_le.trans (Nat.le_add_left _ _), hih⟩
    · have hev' : (i + 1) % 2 = 0 := by omega
      have hih : st.2.1 / (2 * i + 1) ≤ st.2.2 ∧ st.2.2 ≤ 2 ^ M := by
        have h2 := ih.2
        simp only [hev, ↓reduceIte, hfst] at h2
        exact h2
      simp only [hev, hev', ↓reduceIte]
      omega

private theorem arctanStep_powTerm_error (d M : ℕ) (hd : 5 ≤ d) (i : ℕ) :
    let p := ((arctanStep (d * d))^[i] (0, (2 ^ M / d, 0))).2.1
    (p : ℝ) ≤ (2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1) ∧
      (2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1) - (p : ℝ) ≤ 2 := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by positivity
  have hd2 : (25 : ℝ) ≤ (d : ℝ) ^ 2 := by
    have : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  induction i with
  | zero =>
    simp only [Function.iterate_zero, id_eq, mul_zero, zero_add, pow_one]
    have hlo : ((2 ^ M / d : ℕ) : ℝ) ≤ (2 : ℝ) ^ M / (d : ℝ) := by
      rw [le_div_iff₀ hdpos]
      exact_mod_cast Nat.div_mul_le_self (2 ^ M) d
    have hhi : (2 : ℝ) ^ M / (d : ℝ) < ((2 ^ M / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hdpos]
      have h := Nat.lt_mul_div_succ (2 ^ M) (by omega : 0 < d)
      have h' : (2 : ℝ) ^ M < (d : ℝ) * (((2 ^ M / d : ℕ) : ℝ) + 1) := by exact_mod_cast h
      linarith
    exact ⟨hlo, by linarith⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    dsimp only [arctanStep]
    set p := ((arctanStep (d * d))^[i] (0, (2 ^ M / d, 0))).2.1
    have hdiv_le : ((p / (d * d) : ℕ) : ℝ) ≤ (p : ℝ) / (d : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h := Nat.div_mul_le_self p (d * d)
      have h' : ((p / (d * d) : ℕ) : ℝ) * ((d * d : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h
      simpa [sq, Nat.cast_mul] using h'
    have hdiv_lt : (p : ℝ) / (d : ℝ) ^ 2 < ((p / (d * d) : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (by positivity)]
      have h := Nat.lt_mul_div_succ p (by positivity : 0 < d * d)
      have h' : (p : ℝ) < ((d * d : ℕ) : ℝ) * (((p / (d * d) : ℕ) : ℝ) + 1) := by exact_mod_cast h
      have : ((d * d : ℕ) : ℝ) = (d : ℝ) ^ 2 := by push_cast; ring
      rw [this] at h'
      linarith
    have hpow : (2 : ℝ) ^ M / (d : ℝ) ^ (2 * (i + 1) + 1) =
        ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1)) / (d : ℝ) ^ 2 := by
      rw [div_div, ← pow_add, show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by omega]
    rw [hpow]
    refine ⟨hdiv_le.trans (div_le_div_of_nonneg_right ih.1 (by positivity)), ?_⟩
    have hstep :
        ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1) - (p : ℝ)) / (d : ℝ) ^ 2 ≤ 2 / 25 := by
      calc
        ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1) - (p : ℝ)) / (d : ℝ) ^ 2 ≤
            2 / (d : ℝ) ^ 2 := div_le_div_of_nonneg_right ih.2 (by positivity)
        _ ≤ 2 / 25 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd2
    have hsplit :
        ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1)) / (d : ℝ) ^ 2 - ((p / (d * d) : ℕ) : ℝ) =
          ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1) - (p : ℝ)) / (d : ℝ) ^ 2 +
            ((p : ℝ) / (d : ℝ) ^ 2 - ((p / (d * d) : ℕ) : ℝ)) := by ring
    linarith

private theorem arctanInvApprox_series_error (d M L : ℕ) (hd : 5 ≤ d) :
    |((arctanInvApprox d M L : ℝ)) -
        (2 : ℝ) ^ M * ∑ k ∈ Finset.range (2 * L),
          ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))| ≤
      6 * (L : ℝ) := by
  have hgen : ∀ n : ℕ,
      |(((arctanStep (d * d))^[n] (0, (2 ^ M / d, 0))).2.2 : ℝ) -
          (2 : ℝ) ^ M * ∑ k ∈ Finset.range n,
            ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))| ≤
        3 * (n : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      set st := (arctanStep (d * d))^[n] (0, (2 ^ M / d, 0))
      have hfst : st.1 = n := by simpa [st] using arctanStep_fst (d * d) (0, (2 ^ M / d, 0)) n
      have hinv := arctanStep_inv d M n
      have hp := arctanStep_powTerm_error d M hd n
      set term : ℕ := st.2.1 / (2 * n + 1)
      have hterm_err :
          |(term : ℝ) - (2 : ℝ) ^ M * ((1 / (d : ℝ)) ^ (2 * n + 1) / (2 * n + 1 : ℝ))| ≤ 3 := by
        have hden : (0 : ℝ) < (2 * n + 1 : ℝ) := by positivity
        have hdiv_le : (term : ℝ) ≤ (st.2.1 : ℝ) / (2 * n + 1 : ℝ) := by
          rw [le_div_iff₀ hden]
          have h := Nat.div_mul_le_self st.2.1 (2 * n + 1)
          exact_mod_cast h
        have hdiv_lt : (st.2.1 : ℝ) / (2 * n + 1 : ℝ) < (term : ℝ) + 1 := by
          rw [div_lt_iff₀ hden]
          have h := Nat.lt_mul_div_succ st.2.1 (by omega : 0 < 2 * n + 1)
          have h' : (st.2.1 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) * ((term : ℝ) + 1) := by exact_mod_cast h
          push_cast at h'
          linarith
        have hrew : (2 : ℝ) ^ M * ((1 / (d : ℝ)) ^ (2 * n + 1) / (2 * n + 1 : ℝ)) =
            ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * n + 1)) / (2 * n + 1 : ℝ) := by
          rw [one_div_pow, mul_div_assoc', mul_one_div]
        rw [hrew]
        have h1 : ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * n + 1)) / (2 * n + 1 : ℝ) -
            (st.2.1 : ℝ) / (2 * n + 1 : ℝ) ≤ 2 := by
          rw [← sub_div]
          exact (div_le_self (by linarith [hp.1])
            (by linarith [Nat.cast_nonneg (α := ℝ) n])).trans hp.2
        have h2 : (st.2.1 : ℝ) / (2 * n + 1 : ℝ) ≤
            ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * n + 1)) / (2 * n + 1 : ℝ) :=
          div_le_div_of_nonneg_right hp.1 hden.le
        rw [abs_le]
        constructor <;> linarith
      rw [Function.iterate_succ_apply', Finset.sum_range_succ, mul_add]
      dsimp only [arctanStep]
      rw [hfst]
      by_cases hev : n % 2 = 0
      · have hsign : (-1 : ℝ) ^ n = 1 := Even.neg_one_pow (Nat.even_iff.mpr hev)
        simp only [hev, ↓reduceIte, Nat.cast_add, Nat.cast_one, hsign, one_mul]
        have hsplit :
            ((st.2.2 : ℝ) + (term : ℝ)) -
                ((2 : ℝ) ^ M * ∑ k ∈ Finset.range n,
                    ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ)) +
                  (2 : ℝ) ^ M * ((1 / (d : ℝ)) ^ (2 * n + 1) / (2 * n + 1 : ℝ))) =
              ((st.2.2 : ℝ) - (2 : ℝ) ^ M * ∑ k ∈ Finset.range n,
                  ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))) +
                ((term : ℝ) - (2 : ℝ) ^ M * ((1 / (d : ℝ)) ^ (2 * n + 1) / (2 * n + 1 : ℝ))) := by
          ring
        rw [hsplit]
        calc
          _ ≤ _ := abs_add_le _ _
          _ ≤ 3 * (n : ℝ) + 3 := add_le_add ih hterm_err
          _ = 3 * ((n : ℝ) + 1) := by ring
      · have hsign : (-1 : ℝ) ^ n = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
        have hle : term ≤ st.2.2 := by
          have h2 := hinv.2
          simp only [hev, ↓reduceIte] at h2
          simpa only [st, term, hfst] using h2.1
        simp only [hev, ↓reduceIte, hsign, neg_one_mul, neg_div]
        change |((st.2.2 - term : ℕ) : ℝ) - _| ≤ _
        rw [Nat.cast_sub hle]
        have hsplit :
            ((st.2.2 : ℝ) - (term : ℝ)) -
                ((2 : ℝ) ^ M * ∑ k ∈ Finset.range n,
                    ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ)) +
                  (2 : ℝ) ^ M * -((1 / (d : ℝ)) ^ (2 * n + 1) / (2 * n + 1 : ℝ))) =
              ((st.2.2 : ℝ) - (2 : ℝ) ^ M * ∑ k ∈ Finset.range n,
                  ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))) -
                ((term : ℝ) - (2 : ℝ) ^ M * ((1 / (d : ℝ)) ^ (2 * n + 1) / (2 * n + 1 : ℝ))) := by
          ring
        rw [hsplit]
        calc
          _ ≤ _ := abs_sub _ _
          _ ≤ 3 * (n : ℝ) + 3 := add_le_add ih hterm_err
          _ = 3 * ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simpa only [arctanInvApprox, Nat.cast_mul, Nat.cast_ofNat,
    show (3 : ℝ) * (2 * (L : ℝ)) = 6 * (L : ℝ) by ring]
    using hgen (2 * L)

/-- Rounding-to-nearest error of `(raw + 2 ^ (g - 1)) / 2 ^ g` against `raw / 2 ^ g`. -/
private theorem abs_div_two_pow_round_sub_le (raw g : ℕ) (hg : 1 ≤ g) :
    |(((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) - (raw : ℝ) / (2 : ℝ) ^ g| ≤ 1 / 2 := by
  have h2g_pos : (0 : ℝ) < (2 : ℝ) ^ g := by positivity
  have hhalf : ((2 ^ (g - 1) : ℕ) : ℝ) / (2 : ℝ) ^ g = 1 / 2 := by
    have hmul : (2 : ℕ) ^ g = 2 * 2 ^ (g - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hg, pow_succ']
    have hmul' : (2 : ℝ) ^ g = 2 * ((2 ^ (g - 1) : ℕ) : ℝ) := by exact_mod_cast hmul
    rw [hmul']
    have hnz : ((2 ^ (g - 1) : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hlo : (((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) ≤
      ((raw + 2 ^ (g - 1) : ℕ) : ℝ) / (2 : ℝ) ^ g := by
    rw [le_div_iff₀ h2g_pos]
    exact_mod_cast Nat.div_mul_le_self (raw + 2 ^ (g - 1)) (2 ^ g)
  have hhi : ((raw + 2 ^ (g - 1) : ℕ) : ℝ) / (2 : ℝ) ^ g <
      (((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ h2g_pos]
    have h := Nat.lt_mul_div_succ (raw + 2 ^ (g - 1)) (by positivity : 0 < 2 ^ g)
    have h' : ((raw + 2 ^ (g - 1) : ℕ) : ℝ) <
        (2 : ℝ) ^ g * ((((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) + 1) := by exact_mod_cast h
    linarith
  rw [Nat.cast_add, add_div, hhalf] at hlo hhi
  rw [abs_le]
  constructor <;> linarith

/-- Guard bits for `piApprox qBits` ensuring total Machin rounding and truncation error
is strictly below `2 ^ (-qBits)`. -/
private def piGuard (qBits : ℕ) : ℕ := Nat.clog 2 (qBits + 8) + 10

/-- Pure-`ℕ` fixed-point Machin approximation to `2 ^ qBits * π` with round-to-nearest downshift. -/
private def piApprox (qBits : ℕ) : ℕ :=
  let g := piGuard qBits
  let M := qBits + g
  let L := qBits + 4
  let raw := 16 * arctanInvApprox 5 M L - 4 * arctanInvApprox 239 M L
  (raw + 2 ^ (g - 1)) / 2 ^ g

private theorem abs_piApprox_div_sub_pi_le (qBits : ℕ) :
    |(piApprox qBits : ℝ) / (2 : ℝ) ^ qBits - Real.pi| ≤ (2 : ℝ) ^ (-(qBits : ℤ)) := by
  set g := piGuard qBits
  set M := qBits + g
  set L := qBits + 4
  have hg10 : 10 ≤ g := by dsimp only [g, piGuard]; omega
  have h2g : (1024 : ℝ) * ((qBits : ℝ) + 8) ≤ (2 : ℝ) ^ g := by
    have hclog : qBits + 8 ≤ 2 ^ Nat.clog 2 (qBits + 8) := Nat.le_pow_clog (by omega) _
    have hpow : (2 : ℕ) ^ g = 2 ^ Nat.clog 2 (qBits + 8) * 1024 := by
      dsimp only [g, piGuard]
      rw [pow_add]
      norm_num
    have hmul : 1024 * (qBits + 8) ≤ 2 ^ g := by rw [hpow]; omega
    exact_mod_cast hmul
  have h2M : (2 : ℝ) ^ M = (2 : ℝ) ^ qBits * (2 : ℝ) ^ g := by
    dsimp only [M]; rw [pow_add]
  have hterm_full (d : ℕ) (hd : 5 ≤ d) :
      |(arctanInvApprox d M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / (d : ℝ))| ≤
        6 * (L : ℝ) / (2 : ℝ) ^ M + (1 / (d : ℝ)) ^ (4 * L + 1) / (4 * L + 1 : ℝ) := by
    have herr := arctanInvApprox_series_error d M L hd
    have htail := arctan_alternating_remainder (x := 1 / (d : ℝ)) (by positivity) L
    have h1 : |(arctanInvApprox d M L : ℝ) / (2 : ℝ) ^ M -
        ∑ k ∈ Finset.range (2 * L),
          ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))| ≤
        6 * (L : ℝ) / (2 : ℝ) ^ M := by
      rw [← mul_div_cancel_left₀ (∑ k ∈ Finset.range (2 * L), _)
          (by positivity : (2 : ℝ) ^ M ≠ 0),
        ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)]
      exact div_le_div_of_nonneg_right herr (by positivity)
    calc
      |(arctanInvApprox d M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / (d : ℝ))| ≤
          |(arctanInvApprox d M L : ℝ) / (2 : ℝ) ^ M -
              ∑ k ∈ Finset.range (2 * L),
                ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))| +
            |Real.arctan (1 / (d : ℝ)) -
              ∑ k ∈ Finset.range (2 * L),
                ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))| := by
        rw [abs_sub_comm (Real.arctan _)]
        exact abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 htail
  have h5_full : |(arctanInvApprox 5 M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / 5)| ≤
      6 * (L : ℝ) / (2 : ℝ) ^ M + (1 / 5 : ℝ) ^ (4 * L + 1) / (4 * L + 1 : ℝ) := by
    simpa using hterm_full 5 (by omega)
  have h239_full : |(arctanInvApprox 239 M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / 239)| ≤
      6 * (L : ℝ) / (2 : ℝ) ^ M + (1 / 239 : ℝ) ^ (4 * L + 1) / (4 * L + 1 : ℝ) := by
    simpa using hterm_full 239 (by omega)
  have h5_pow : (1 / 5 : ℝ) ^ (4 * L + 1) ≤ (1 / 625 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
    have hpow1 : (1 / 5 : ℝ) ^ (4 * L + 1) ≤ (1 / 5 : ℝ) ^ (qBits + 4) := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      dsimp only [L]; omega
    have hpow2 : (1 / 5 : ℝ) ^ (qBits + 4) = (1 / 625 : ℝ) * (1 / 5 : ℝ) ^ qBits := by
      rw [pow_add]; norm_num; ring
    have hpow3 : (1 / 5 : ℝ) ^ qBits ≤ (1 / 2 : ℝ) ^ qBits :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    linarith [mul_le_mul_of_nonneg_left hpow3 (by norm_num : (0 : ℝ) ≤ 1 / 625)]
  have h239_pow : (1 / 239 : ℝ) ^ (4 * L + 1) ≤ (1 / 5 : ℝ) ^ (4 * L + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hround_small : 120 * (L : ℝ) / (2 : ℝ) ^ M ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) := by
    rw [h2M, zpow_neg, zpow_natCast, ← one_div, div_mul_eq_div_div, mul_one_div]
    have h1 : 120 * (L : ℝ) / (2 : ℝ) ^ g ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have hL : (L : ℝ) = (qBits : ℝ) + 4 := by dsimp only [L]; push_cast; ring
      linarith
    have h2 : 120 * (L : ℝ) / (2 : ℝ) ^ qBits / (2 : ℝ) ^ g =
        (120 * (L : ℝ) / (2 : ℝ) ^ g) / (2 : ℝ) ^ qBits := by ring
    rw [h2]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have hraw_real :
      |(16 * (arctanInvApprox 5 M L : ℝ) - 4 * (arctanInvApprox 239 M L : ℝ)) / (2 : ℝ) ^ M -
          Real.pi| ≤
        (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) := by
    have hpi : Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
      linarith [machin_pi_div_four]
    rw [hpi, sub_div, mul_div_assoc, mul_div_assoc]
    have hsplit :
        (16 * ((arctanInvApprox 5 M L : ℝ) / (2 : ℝ) ^ M) -
            4 * ((arctanInvApprox 239 M L : ℝ) / (2 : ℝ) ^ M)) -
          (16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239)) =
        16 * ((arctanInvApprox 5 M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / 5)) -
          4 * ((arctanInvApprox 239 M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / 239)) := by ring
    rw [hsplit]
    have htri := abs_sub (16 * ((arctanInvApprox 5 M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / 5)))
      (4 * ((arctanInvApprox 239 M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / 239)))
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16),
      abs_of_pos (by norm_num : (0 : ℝ) < 4)] at htri
    have hden1 : (1 : ℝ) ≤ (4 * L + 1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) L]
    have htail5 : (1 / 5 : ℝ) ^ (4 * L + 1) / (4 * L + 1 : ℝ) ≤
        (1 / 625 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) :=
      (div_le_self (by positivity) hden1).trans h5_pow
    have htail239 : (1 / 239 : ℝ) ^ (4 * L + 1) / (4 * L + 1 : ℝ) ≤
        (1 / 625 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) :=
      (div_le_self (by positivity) hden1).trans (h239_pow.trans h5_pow)
    have hcomb :
        16 * (6 * (L : ℝ) / (2 : ℝ) ^ M) + 4 * (6 * (L : ℝ) / (2 : ℝ) ^ M) =
          120 * (L : ℝ) / (2 : ℝ) ^ M := by ring
    have hzpos : (0 : ℝ) < (2 : ℝ) ^ (-(qBits : ℤ)) := by positivity
    linarith
  have hge : 4 * arctanInvApprox 239 M L ≤ 16 * arctanInvApprox 5 M L := by
    have hlow := (abs_le.mp hraw_real).1
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hz1 : (2 : ℝ) ^ (-(qBits : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hpos : (0 : ℝ) < (16 * (arctanInvApprox 5 M L : ℝ) -
        4 * (arctanInvApprox 239 M L : ℝ)) / (2 : ℝ) ^ M := by linarith
    have hnum : (0 : ℝ) < 16 * (arctanInvApprox 5 M L : ℝ) - 4 * (arctanInvApprox 239 M L : ℝ) :=
      (div_pos_iff_of_pos_right (by positivity)).mp hpos
    have hle : (4 * arctanInvApprox 239 M L : ℝ) ≤ (16 * arctanInvApprox 5 M L : ℝ) := by linarith
    exact_mod_cast hle
  set raw : ℕ := 16 * arctanInvApprox 5 M L - 4 * arctanInvApprox 239 M L
  have hraw_cast : (raw : ℝ) =
      16 * (arctanInvApprox 5 M L : ℝ) - 4 * (arctanInvApprox 239 M L : ℝ) := by
    dsimp only [raw]
    rw [Nat.cast_sub hge, Nat.cast_mul, Nat.cast_mul]
    norm_num
  have hshift : |((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) - (raw : ℝ) / (2 : ℝ) ^ g| ≤ 1 / 2 :=
    abs_div_two_pow_round_sub_le raw g (by omega)
  have hpi_eq : piApprox qBits = (raw + 2 ^ (g - 1)) / 2 ^ g := rfl
  rw [hpi_eq]
  have hshift_scaled :
      |(((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) / (2 : ℝ) ^ qBits - (raw : ℝ) / (2 : ℝ) ^ M| ≤
        (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) := by
    rw [h2M, div_mul_eq_div_div, div_right_comm (raw : ℝ), ← sub_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ qBits),
      zpow_neg, zpow_natCast, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hshift (by positivity)
  rw [← hraw_cast] at hraw_real
  calc
    |(((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) / (2 : ℝ) ^ qBits - Real.pi| ≤
        |(((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) / (2 : ℝ) ^ qBits - (raw : ℝ) / (2 : ℝ) ^ M| +
          |(raw : ℝ) / (2 : ℝ) ^ M - Real.pi| := abs_sub_le _ _ _
    _ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) + (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) :=
      add_le_add hshift_scaled hraw_real
    _ = (2 : ℝ) ^ (-(qBits : ℤ)) := by ring

private theorem computableInPolyTime_arctanInvApprox (d : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => arctanInvApprox d p.1 p.2)
      (encPair encUnary encUnary) encNat := by
  have hcount : ComputableInPolyTime (fun p : ℕ × ℕ => 2 * p.2)
      (encPair encUnary encUnary) encUnary :=
    unary_mul' (const 2) (snd encUnary encUnary)
  have hinit : ComputableInPolyTime (fun p : ℕ × ℕ => (0, (2 ^ p.1 / d, 0)))
      (encPair encUnary encUnary) (encPair encNat (encPair encNat encNat)) :=
    (const 0).prod
      ((binary_div' (binary_two_pow.comp (fst encUnary encUnary)) (const d)).prod (const 0))
  have hstep : ComputableInPolyTime (arctanStep (d * d))
      (encPair encNat (encPair encNat encNat)) (encPair encNat (encPair encNat encNat)) := by
    unfold arctanStep
    have hk := fst encNat (encPair encNat encNat)
    have hpow := (snd encNat (encPair encNat encNat)).fst'
    have hacc := (snd encNat (encPair encNat encNat)).snd'
    have hterm := binary_div' hpow (binary_add' (binary_mul' (const 2) hk) (const 1))
    have hcond : ComputableInPolyTime (fun st : ℕ × (ℕ × ℕ) => decide (st.1 % 2 = 0))
        (encPair encNat (encPair encNat encNat)) encBool :=
      decide_eq' (binary_mod' hk (const 2)) (const 0)
    have hacc' := ite_decide hcond (binary_add' hacc hterm) (binary_sub' hacc hterm)
    exact (binary_add' hk (const 1)).prod ((binary_div' hpow (const (d * d))).prod hacc')
  have hiter := iterate hcount hinit hstep
    (bound := fun p => 12 * (encPair encUnary encUnary p).length + 20)
    (((PolyBounded.const 12).mul .self).add (.const 20))
    (fun p i hi => by
      have hinv := arctanStep_inv d p.1 i
      have hfst : ((arctanStep (d * d))^[i] (0, (2 ^ p.1 / d, 0))).1 = i := by
        simpa using arctanStep_fst (d * d) (0, (2 ^ p.1 / d, 0)) i
      have hpow_lt : ((arctanStep (d * d))^[i] (0, (2 ^ p.1 / d, 0))).2.1 < 2 ^ (p.1 + 1) :=
        lt_of_le_of_lt hinv.1 (Nat.pow_lt_pow_right (by omega) (by omega))
      have hacc_lt : ((arctanStep (d * d))^[i] (0, (2 ^ p.1 / d, 0))).2.2 < 2 ^ (p.1 + 1) := by
        have hle : ((arctanStep (d * d))^[i] (0, (2 ^ p.1 / d, 0))).2.2 ≤ 2 ^ p.1 := by
          by_cases h : i % 2 = 0
          · have h2 := hinv.2
            simp only [h, ↓reduceIte] at h2
            exact le_trans (Nat.le_add_right _ _) h2
          · have h2 := hinv.2
            simp only [h, ↓reduceIte] at h2
            exact h2.2
        exact lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by omega) (by omega))
      have hi_lt : i < 2 ^ (2 * p.2) := lt_of_le_of_lt hi Nat.lt_two_pow_self
      have hl1 : (encNat i).length ≤ 2 * p.2 := length_encNat_le_of_lt_two_pow hi_lt
      have hl2 : (encNat ((arctanStep (d * d))^[i] (0, (2 ^ p.1 / d, 0))).2.1).length ≤ p.1 + 1 :=
        length_encNat_le_of_lt_two_pow hpow_lt
      have hl3 : (encNat ((arctanStep (d * d))^[i] (0, (2 ^ p.1 / d, 0))).2.2).length ≤ p.1 + 1 :=
        length_encNat_le_of_lt_two_pow hacc_lt
      simp only [length_encPair, encUnary_apply, List.length_replicate, hfst] at hl1 hl2 hl3 ⊢
      omega)
  exact hiter.snd'.snd'

private theorem computableInPolyTime_piGuard : ComputableInPolyTime piGuard encUnary encUnary := by
  unfold piGuard
  exact unary_add' (binary_clog_two.comp (unary_to_binary.comp (unary_add' id' (const 8))))
    (const 10)

private theorem computableInPolyTime_piApprox : ComputableInPolyTime piApprox encUnary encNat := by
  unfold piApprox
  have hg := computableInPolyTime_piGuard
  have hM : ComputableInPolyTime (fun q => q + piGuard q) encUnary encUnary :=
    unary_add' id' hg
  have hL : ComputableInPolyTime (fun q => q + 4) encUnary encUnary :=
    unary_add' id' (const 4)
  have ha5 := (computableInPolyTime_arctanInvApprox 5).comp (hM.prod hL)
  have ha239 := (computableInPolyTime_arctanInvApprox 239).comp (hM.prod hL)
  have hraw := binary_sub' (binary_mul' (const 16) ha5) (binary_mul' (const 4) ha239)
  have hhalf := binary_two_pow.comp (unary_sub' hg (const 1))
  have hden := binary_two_pow.comp hg
  exact binary_div' (binary_add' hraw hhalf) hden

/-! ### 4. Alternating `exp(-z)` Taylor bound and pure-`ℕ` fixed-point `exp(-z)` -/

private theorem exp_neg_alternating_bound :
    ∀ N : ℕ, ∀ {z : ℝ}, 0 ≤ z →
      (Even N → ∑ k ∈ Finset.range N, (-z) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (-z)) ∧
      (Odd N → Real.exp (-z) ≤ ∑ k ∈ Finset.range N, (-z) ^ k / (Nat.factorial k : ℝ)) := by
  intro N
  induction N with
  | zero =>
    intro z _
    refine ⟨fun _ => by simp [(Real.exp_pos _).le], fun h => by simp at h⟩
  | succ N ih =>
    intro z hz
    let f : ℝ → ℝ := fun t =>
      Real.exp (-t) - ∑ k ∈ Finset.range (N + 1), (-t) ^ k / (Nat.factorial k : ℝ)
    have hf0 : f 0 = 0 := by
      simp [f, Finset.sum_range_succ']
    have hderiv (t : ℝ) :
        HasDerivAt f
          (-(Real.exp (-t) - ∑ k ∈ Finset.range N, (-t) ^ k / (Nat.factorial k : ℝ))) t := by
      have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-t)) t := by
        simpa using ((hasDerivAt_id' t).neg).exp
      have hsum : HasDerivAt
          (fun y : ℝ => ∑ k ∈ Finset.range (N + 1), (-y) ^ k / (Nat.factorial k : ℝ))
          (-(∑ k ∈ Finset.range N, (-t) ^ k / (Nat.factorial k : ℝ))) t := by
        have hrew : (fun y : ℝ => ∑ k ∈ Finset.range (N + 1), (-y) ^ k / (Nat.factorial k : ℝ)) =
            fun y : ℝ => (1 : ℝ) +
              ∑ k ∈ Finset.range N, (-y) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
          funext y
          rw [Finset.sum_range_succ']
          simp [add_comm]
        rw [hrew]
        have hterm (k : ℕ) :
            HasDerivAt (fun y : ℝ => (-y) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ))
              (-((-t) ^ k / (Nat.factorial k : ℝ))) t := by
          have hp := (((hasDerivAt_id' t).neg).pow (k + 1)).div_const (Nat.factorial (k + 1) : ℝ)
          convert hp using 1
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
          have hnz : (k + 1 : ℝ) ≠ 0 := by positivity
          dsimp only [Pi.neg_apply]
          field_simp
        simpa only [Finset.sum_neg_distrib] using
          (HasDerivAt.fun_sum fun k _ => hterm k).const_add (1 : ℝ)
      convert hexp.sub hsum using 1
      ring
    constructor
    · intro hev
      have hodd : Odd N := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hev)
      have hmono : MonotoneOn f (Set.Icc 0 z) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc 0 z)
          (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
          (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt)
          fun t ht => ?_
        rw [(hderiv t).deriv]
        have hht : 0 ≤ t := (interior_subset ht).1
        linarith [(ih hht).2 hodd]
      have hmz := hmono (Set.left_mem_Icc.mpr hz) (Set.right_mem_Icc.mpr hz) hz
      dsimp only [f] at hf0 hmz
      linarith
    · intro hodd
      have hev : Even N := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hodd)
      have hanti : AntitoneOn f (Set.Icc 0 z) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc 0 z)
          (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
          (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt)
          fun t ht => ?_
        rw [(hderiv t).deriv]
        have hht : 0 ≤ t := (interior_subset ht).1
        linarith [(ih hht).1 hev]
      have hmz := hanti (Set.left_mem_Icc.mpr hz) (Set.right_mem_Icc.mpr hz) hz
      dsimp only [f] at hf0 hmz
      linarith

private theorem abs_exp_neg_sub_sum_le {z : ℝ} (hz : 0 ≤ z) (M : ℕ) :
    |Real.exp (-z) - ∑ k ∈ Finset.range (2 * M), (-z) ^ k / (Nat.factorial k : ℝ)| ≤
      z ^ (2 * M) / (Nat.factorial (2 * M) : ℝ) := by
  have hlo := (exp_neg_alternating_bound (2 * M) hz).1 (even_two_mul M)
  have hhi := (exp_neg_alternating_bound (2 * M + 1) hz).2 ⟨M, rfl⟩
  rw [Finset.sum_range_succ, Even.neg_pow (even_two_mul M)] at hhi
  rw [abs_le]
  constructor <;> linarith

/-- One step of fixed-point `exp(-z)` series at scale `S`: `par = (S, zFp)`,
state `(j, (term, acc))`. -/
private def expNegStep (par : ℕ × ℕ) (st : ℕ × (ℕ × ℕ)) : ℕ × (ℕ × ℕ) :=
  let S := par.1
  let zFp := par.2
  let j := st.1
  let term := st.2.1
  let acc := st.2.2
  let acc' := if j % 2 = 0 then acc + term else acc - term
  let term' := (term * zFp) / ((j + 1) * S)
  (j + 1, (term', acc'))

/-- Fixed-point approximation to `2 ^ qBits * exp(-zFp / 2 ^ qBits)`
using `2 * (qBits + 2)` terms. -/
private def expNegSeries (qBits zFp : ℕ) : ℕ :=
  let S := 2 ^ qBits
  let zC := min zFp S
  ((expNegStep (S, zC))^[2 * (qBits + 2)] (0, (S, 0))).2.2

/-- Fixed-point `K`-fold powering `(P_r * base) / 2 ^ qBits` starting from `2 ^ qBits`. -/
private def expNegPow (qBits zFp K : ℕ) : ℕ :=
  let S := 2 ^ qBits
  let b := expNegSeries qBits zFp
  (fun p => (p * b) / S)^[K] S

private theorem expNegStep_fst (par : ℕ × ℕ) (st : ℕ × (ℕ × ℕ)) (i : ℕ) :
    ((expNegStep par)^[i] st).1 = st.1 + i := by
  induction i generalizing st with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [expNegStep]; omega

private theorem expNegStep_inv (S zC : ℕ) (hz : zC ≤ S) (i : ℕ) :
    let st := (expNegStep (S, zC))^[i] (0, (S, 0))
    st.2.1 ≤ S ∧ (if i % 2 = 0 then st.2.2 + st.2.1 ≤ S else st.2.1 ≤ st.2.2 ∧ st.2.2 ≤ S) := by
  induction i with
  | zero => simp
  | succ i ih =>
    set st := (expNegStep (S, zC))^[i] (0, (S, 0)) with hst_def
    have hfst : st.1 = i := by simpa [hst_def] using expNegStep_fst (S, zC) (0, (S, 0)) i
    have hterm_le : (st.2.1 * zC) / ((i + 1) * S) ≤ st.2.1 := by
      rcases Nat.eq_zero_or_pos S with rfl | hS
      · simp
      · refine (Nat.div_le_iff_le_mul_add_pred (by positivity)).mpr ?_
        have h1 : st.2.1 * zC ≤ st.2.1 * S := Nat.mul_le_mul_left _ hz
        have h2 : st.2.1 * S ≤ st.2.1 * ((i + 1) * S) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left S (by omega))
        have h3 : st.2.1 * ((i + 1) * S) = ((i + 1) * S) * st.2.1 := mul_comm _ _
        omega
    rw [Function.iterate_succ_apply']
    dsimp only [expNegStep]
    rw [← hst_def, hfst]
    refine ⟨hterm_le.trans ih.1, ?_⟩
    by_cases hev : i % 2 = 0
    · have hodd : (i + 1) % 2 ≠ 0 := by omega
      have hih : st.2.2 + st.2.1 ≤ S := by
        have h2 := ih.2; simp only [hev, ↓reduceIte] at h2; exact h2
      simp only [hev, hodd, ↓reduceIte]
      exact ⟨hterm_le.trans (Nat.le_add_left _ _), hih⟩
    · have hev' : (i + 1) % 2 = 0 := by omega
      have hih : st.2.1 ≤ st.2.2 ∧ st.2.2 ≤ S := by
        have h2 := ih.2; simp only [hev, ↓reduceIte] at h2; exact h2
      simp only [hev, hev', ↓reduceIte]
      omega

private theorem expNegSeries_le (qBits zFp : ℕ) : expNegSeries qBits zFp ≤ 2 ^ qBits := by
  have hinv := expNegStep_inv (2 ^ qBits) (min zFp (2 ^ qBits)) (min_le_right _ _) (2 * (qBits + 2))
  have hev : (2 * (qBits + 2)) % 2 = 0 := by omega
  simp only [hev, ↓reduceIte] at hinv
  change ((expNegStep (2 ^ qBits, min zFp (2 ^ qBits)))^[2 * (qBits + 2)]
    (0, (2 ^ qBits, 0))).2.2 ≤ _
  omega

private theorem expNegPow_step_le (S b : ℕ) (hb : b ≤ S) (p : ℕ) (hp : p ≤ S) :
    (p * b) / S ≤ S := by
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · simp
  · refine (Nat.div_le_iff_le_mul_add_pred hS).mpr ?_
    have h1 : p * b ≤ S * S := Nat.mul_le_mul hp hb
    omega

private theorem expNegPow_le (qBits zFp K : ℕ) : expNegPow qBits zFp K ≤ 2 ^ qBits := by
  unfold expNegPow
  have hb := expNegSeries_le qBits zFp
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Function.iterate_succ_apply']
    exact expNegPow_step_le _ _ hb _ ih

private theorem computableInPolyTime_expNegSeries :
    ComputableInPolyTime (fun p : ℕ × ℕ => expNegSeries p.1 p.2)
      (encPair encUnary encNat) encNat := by
  have hS : ComputableInPolyTime (fun p : ℕ × ℕ => 2 ^ p.1)
      (encPair encUnary encNat) encNat :=
    binary_two_pow.comp (fst encUnary encNat)
  have hzC : ComputableInPolyTime (fun p : ℕ × ℕ => min p.2 (2 ^ p.1))
      (encPair encUnary encNat) encNat :=
    binary_min' (snd encUnary encNat) hS
  have hpar := hS.prod hzC
  have hcount : ComputableInPolyTime (fun p : ℕ × ℕ => 2 * (p.1 + 2))
      (encPair encUnary encNat) encUnary :=
    unary_mul' (const 2) (unary_add' (fst encUnary encNat) (const 2))
  have hinit : ComputableInPolyTime (fun p : ℕ × ℕ => (0, (2 ^ p.1, 0)))
      (encPair encUnary encNat) (encPair encNat (encPair encNat encNat)) :=
    (const 0).prod (hS.prod (const 0))
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => expNegStep q.1 q.2)
      (encPair (encPair encNat encNat) (encPair encNat (encPair encNat encNat)))
      (encPair encNat (encPair encNat encNat)) := by
    unfold expNegStep
    have hpar_q := fst (encPair encNat encNat) (encPair encNat (encPair encNat encNat))
    have hst_q := snd (encPair encNat encNat) (encPair encNat (encPair encNat encNat))
    have hSq := hpar_q.fst'
    have hzq := hpar_q.snd'
    have hj := hst_q.fst'
    have hterm := hst_q.snd'.fst'
    have hacc := hst_q.snd'.snd'
    have hcond : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => decide (q.2.1 % 2 = 0))
        (encPair (encPair encNat encNat) (encPair encNat (encPair encNat encNat))) encBool :=
      decide_eq' (binary_mod' hj (const 2)) (const 0)
    have hacc' := ite_decide hcond (binary_add' hacc hterm) (binary_sub' hacc hterm)
    have hterm' := binary_div' (binary_mul' hterm hzq)
      (binary_mul' (binary_add' hj (const 1)) hSq)
    exact (binary_add' hj (const 1)).prod (hterm'.prod hacc')
  have hiter := iterateWith hpar hcount hinit hstep
    (bound := fun p => 12 * (encPair encUnary encNat p).length + 30)
    (((PolyBounded.const 12).mul .self).add (.const 30))
    (fun p i hi => by
      have hinv := expNegStep_inv (2 ^ p.1) (min p.2 (2 ^ p.1)) (min_le_right _ _) i
      have hfst : ((expNegStep (2 ^ p.1, min p.2 (2 ^ p.1)))^[i] (0, (2 ^ p.1, 0))).1 = i := by
        simpa using expNegStep_fst (2 ^ p.1, min p.2 (2 ^ p.1)) (0, (2 ^ p.1, 0)) i
      have ht_lt : ((expNegStep (2 ^ p.1, min p.2 (2 ^ p.1)))^[i] (0, (2 ^ p.1, 0))).2.1 <
          2 ^ (p.1 + 1) :=
        lt_of_le_of_lt hinv.1 (Nat.pow_lt_pow_right (by omega) (by omega))
      have ha_lt : ((expNegStep (2 ^ p.1, min p.2 (2 ^ p.1)))^[i] (0, (2 ^ p.1, 0))).2.2 <
          2 ^ (p.1 + 1) := by
        have hle :
            ((expNegStep (2 ^ p.1, min p.2 (2 ^ p.1)))^[i] (0, (2 ^ p.1, 0))).2.2 ≤
              2 ^ p.1 := by
          by_cases h : i % 2 = 0
          · simp only [h, ↓reduceIte] at hinv; omega
          · simp only [h, ↓reduceIte] at hinv; exact hinv.2.2
        exact lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by omega) (by omega))
      have hi_lt : i < 2 ^ (2 * (p.1 + 2)) := lt_of_le_of_lt hi Nat.lt_two_pow_self
      have hl1 : (encNat i).length ≤ 2 * (p.1 + 2) := length_encNat_le_of_lt_two_pow hi_lt
      have hl2 : (encNat ((expNegStep (2 ^ p.1, min p.2 (2 ^ p.1)))^[i]
          (0, (2 ^ p.1, 0))).2.1).length ≤
          p.1 + 1 := length_encNat_le_of_lt_two_pow ht_lt
      have hl3 : (encNat ((expNegStep (2 ^ p.1, min p.2 (2 ^ p.1)))^[i]
          (0, (2 ^ p.1, 0))).2.2).length ≤
          p.1 + 1 := length_encNat_le_of_lt_two_pow ha_lt
      simp only [length_encPair, encUnary_apply, List.length_replicate, hfst] at hl1 hl2 hl3 ⊢
      omega)
  exact hiter.snd'.snd'

private theorem computableInPolyTime_expNegPow :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => expNegPow p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encNat) encUnary) encNat := by
  have hS : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => 2 ^ p.1.1)
      (encPair (encPair encUnary encNat) encUnary) encNat :=
    binary_two_pow.comp (fst (encPair encUnary encNat) encUnary).fst'
  have hb : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => expNegSeries p.1.1 p.1.2)
      (encPair (encPair encUnary encNat) encUnary) encNat :=
    computableInPolyTime_expNegSeries.comp (fst (encPair encUnary encNat) encUnary)
  have hpar := hS.prod hb
  have hcount : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.2)
      (encPair (encPair encUnary encNat) encUnary) encUnary :=
    snd (encPair encUnary encNat) encUnary
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × ℕ => (q.2 * q.1.2) / q.1.1)
      (encPair (encPair encNat encNat) encNat) encNat := by
    have hpar_q := fst (encPair encNat encNat) encNat
    have hp_q := snd (encPair encNat encNat) encNat
    exact binary_div' (binary_mul' hp_q hpar_q.snd') hpar_q.fst'
  exact iterateWith (step := fun (par : ℕ × ℕ) (x : ℕ) => (x * par.2) / par.1) hpar hcount hS hstep
    (bound := fun p => (encPair (encPair encUnary encNat) encUnary p).length + 2)
    (PolyBounded.add .self (.const 2))
    (fun p i _ => by
      have hle : (fun x => (x * expNegSeries p.1.1 p.1.2) / 2 ^ p.1.1)^[i] (2 ^ p.1.1) ≤
          2 ^ p.1.1 :=
        expNegPow_le p.1.1 p.1.2 i
      have hlt : (fun x => (x * expNegSeries p.1.1 p.1.2) / 2 ^ p.1.1)^[i] (2 ^ p.1.1) <
          2 ^ (p.1.1 + 1) :=
        lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by omega) (by omega))
      have hl := length_encNat_le_of_lt_two_pow hlt
      simp only [length_encPair, encUnary_apply, List.length_replicate] at hl ⊢
      omega)

private theorem two_pow_le_factorial_succ (n : ℕ) : 2 ^ n ≤ Nat.factorial (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Nat.factorial_succ]
    have h2 : 2 ≤ n + 2 := by omega
    exact Nat.mul_le_mul h2 ih

private theorem abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a]
    exact this hb ha (le_of_not_ge hab)
  have hge : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr hge), abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
  have h1 : Real.exp (-a) - Real.exp (-b) = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2; ring
  have h2 : 1 - Real.exp (-(b - a)) ≤ b - a := by
    linarith [Real.add_one_le_exp (-(b - a))]
  have h3 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [h1]
  have hnn : 0 ≤ 1 - Real.exp (-(b - a)) := by
    have : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  exact (mul_le_of_le_one_left hnn h3).trans h2

private theorem expNegStep_term_error (qBits zFp : ℕ) (hz : zFp ≤ 2 ^ qBits) (j : ℕ) :
    let S : ℕ := 2 ^ qBits
    let z : ℝ := (zFp : ℝ) / (S : ℝ)
    let term := ((expNegStep (S, zFp))^[j] (0, (S, 0))).2.1
    (term : ℝ) ≤ (S : ℝ) * z ^ j / (Nat.factorial j : ℝ) ∧
      (S : ℝ) * z ^ j / (Nat.factorial j : ℝ) - (term : ℝ) ≤ if j = 0 then 0 else 2 := by
  set S : ℕ := 2 ^ qBits
  set z : ℝ := (zFp : ℝ) / (S : ℝ)
  have hSpos : (0 : ℝ) < (S : ℝ) := by positivity
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z ≤ 1 := (div_le_one hSpos).mpr (by exact_mod_cast hz)
  induction j with
  | zero =>
    simp [S]
  | succ j ih =>
    dsimp only
    rw [Function.iterate_succ_apply']
    dsimp only [expNegStep]
    set st := (expNegStep (S, zFp))^[j] (0, (S, 0))
    have hfst : st.1 = j := by simpa [st] using expNegStep_fst (S, zFp) (0, (S, 0)) j
    rw [hfst]
    set term := st.2.1
    set den : ℕ := (j + 1) * S
    have hden_pos : 0 < den := by positivity
    have hden_r : (0 : ℝ) < (den : ℝ) := by positivity
    have hdiv_le : (((term * zFp) / den : ℕ) : ℝ) ≤ (term : ℝ) * z / (j + 1 : ℝ) := by
      have h1 : (((term * zFp) / den : ℕ) : ℝ) ≤ ((term * zFp : ℕ) : ℝ) / (den : ℝ) := by
        rw [le_div_iff₀ hden_r]
        exact_mod_cast Nat.div_mul_le_self (term * zFp) den
      have h2 : ((term * zFp : ℕ) : ℝ) / (den : ℝ) = (term : ℝ) * z / (j + 1 : ℝ) := by
        dsimp only [den, z]
        push_cast
        have hS0 : (S : ℝ) ≠ 0 := hSpos.ne'
        have hj0 : (j : ℝ) + 1 ≠ 0 := by positivity
        field_simp
      rwa [h2] at h1
    have hdiv_lt : (term : ℝ) * z / (j + 1 : ℝ) < (((term * zFp) / den : ℕ) : ℝ) + 1 := by
      have h1 : ((term * zFp : ℕ) : ℝ) / (den : ℝ) < (((term * zFp) / den : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hden_r]
        have h := Nat.lt_mul_div_succ (term * zFp) hden_pos
        have h' : ((term * zFp : ℕ) : ℝ) < (den : ℝ) * ((((term * zFp) / den : ℕ) : ℝ) + 1) := by
          exact_mod_cast h
        linarith
      have h2 : ((term * zFp : ℕ) : ℝ) / (den : ℝ) = (term : ℝ) * z / (j + 1 : ℝ) := by
        dsimp only [den, z]
        push_cast
        have hS0 : (S : ℝ) ≠ 0 := hSpos.ne'
        have hj0 : (j : ℝ) + 1 ≠ 0 := by positivity
        field_simp
      rwa [h2] at h1
    have hpow_step : (S : ℝ) * z ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) =
        ((S : ℝ) * z ^ j / (Nat.factorial j : ℝ)) * z / (j + 1 : ℝ) := by
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hf0 : (Nat.factorial j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      have hj0 : (j : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    have hupper : (((term * zFp) / den : ℕ) : ℝ) ≤
        (S : ℝ) * z ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) := by
      rw [hpow_step]
      exact hdiv_le.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right ih.1 hz0) (by positivity))
    refine ⟨hupper, ?_⟩
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have hsplit :
        (S : ℝ) * z ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) - (((term * zFp) / den : ℕ) : ℝ) =
          ((S : ℝ) * z ^ j / (Nat.factorial j : ℝ) - (term : ℝ)) * (z / (j + 1 : ℝ)) +
            ((term : ℝ) * z / (j + 1 : ℝ) - (((term * zFp) / den : ℕ) : ℝ)) := by
      rw [hpow_step]; ring
    have herr_mul : ((S : ℝ) * z ^ j / (Nat.factorial j : ℝ) - (term : ℝ)) *
        (z / (j + 1 : ℝ)) ≤ 1 := by
      cases j with
      | zero =>
        have hih0 : (S : ℝ) * z ^ 0 / (Nat.factorial 0 : ℝ) - (term : ℝ) ≤ 0 := by
          have h := ih.2
          simp only [↓reduceIte] at h
          exact h
        have hnn : 0 ≤ (S : ℝ) * z ^ 0 / (Nat.factorial 0 : ℝ) - (term : ℝ) := by linarith [ih.1]
        have heq0 : (S : ℝ) * z ^ 0 / (Nat.factorial 0 : ℝ) - (term : ℝ) = 0 := by linarith
        rw [heq0, zero_mul]; norm_num
      | succ k =>
        have hih2 : (S : ℝ) * z ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) - (term : ℝ) ≤ 2 := by
          have h := ih.2
          simp only [Nat.succ_ne_zero, ↓reduceIte] at h
          exact h
        have hzdiv : z / ((k + 1 : ℕ) + 1 : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have hk : (2 : ℝ) ≤ ((k + 1 : ℕ) + 1 : ℝ) := by push_cast; linarith
          nlinarith
        have hnn : 0 ≤ (S : ℝ) * z ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) - (term : ℝ) := by
          linarith [ih.1]
        calc
          ((S : ℝ) * z ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) - (term : ℝ)) *
                (z / ((k + 1 : ℕ) + 1 : ℝ)) ≤
              2 * (1 / 2) := mul_le_mul hih2 hzdiv (by positivity) (by norm_num)
          _ = 1 := by norm_num
    linarith

private theorem abs_expNegSeries_div_sub_exp_le (qBits zFp : ℕ) (hz : zFp ≤ 2 ^ qBits) :
    |(expNegSeries qBits zFp : ℝ) / (2 : ℝ) ^ qBits -
        Real.exp (-((zFp : ℝ) / (2 : ℝ) ^ qBits))| ≤
      (4 * ((qBits : ℝ) + 2) + 1) / (2 : ℝ) ^ qBits := by
  set S : ℕ := 2 ^ qBits
  set z : ℝ := (zFp : ℝ) / (S : ℝ)
  have hSpos : (0 : ℝ) < (S : ℝ) := by positivity
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z ≤ 1 := (div_le_one hSpos).mpr (by exact_mod_cast hz)
  have hgen : ∀ n : ℕ,
      |(((expNegStep (S, zFp))^[n] (0, (S, 0))).2.2 : ℝ) -
          (S : ℝ) * ∑ k ∈ Finset.range n, (-z) ^ k / (Nat.factorial k : ℝ)| ≤
        2 * (n : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      set st := (expNegStep (S, zFp))^[n] (0, (S, 0))
      have hfst : st.1 = n := by simpa [st] using expNegStep_fst (S, zFp) (0, (S, 0)) n
      have hinv := expNegStep_inv S zFp hz n
      have ht := expNegStep_term_error qBits zFp hz n
      have ht_err : |(st.2.1 : ℝ) - (S : ℝ) * (z ^ n / (Nat.factorial n : ℝ))| ≤ 2 := by
        have h2 : (S : ℝ) * z ^ n / (Nat.factorial n : ℝ) - (st.2.1 : ℝ) ≤ 2 := by
          have := ht.2
          split_ifs at this <;> linarith
        rw [← mul_div_assoc, abs_le]
        constructor <;> linarith [ht.1]
      rw [Function.iterate_succ_apply', Finset.sum_range_succ, mul_add]
      dsimp only [expNegStep]
      rw [hfst]
      by_cases hev : n % 2 = 0
      · have hsign : (-z) ^ n = z ^ n := Even.neg_pow (Nat.even_iff.mpr hev) z
        simp only [hev, ↓reduceIte, Nat.cast_add, Nat.cast_one, hsign]
        have hsplit :
            ((st.2.2 : ℝ) + (st.2.1 : ℝ)) -
                ((S : ℝ) * ∑ k ∈ Finset.range n, (-z) ^ k / (Nat.factorial k : ℝ) +
                  (S : ℝ) * (z ^ n / (Nat.factorial n : ℝ))) =
              ((st.2.2 : ℝ) - (S : ℝ) * ∑ k ∈ Finset.range n, (-z) ^ k / (Nat.factorial k : ℝ)) +
                ((st.2.1 : ℝ) - (S : ℝ) * (z ^ n / (Nat.factorial n : ℝ))) := by ring
        rw [hsplit]
        calc
          _ ≤ _ := abs_add_le _ _
          _ ≤ 2 * (n : ℝ) + 2 := add_le_add ih ht_err
          _ = 2 * ((n : ℝ) + 1) := by ring
      · have hsign : (-z) ^ n = -(z ^ n) := Odd.neg_pow (Nat.odd_iff.mpr (by omega)) z
        have hle : st.2.1 ≤ st.2.2 := by
          have h2 := hinv.2
          simp only [hev, ↓reduceIte] at h2
          exact h2.1
        simp only [hev, ↓reduceIte, hsign, neg_div]
        change |((st.2.2 - st.2.1 : ℕ) : ℝ) - _| ≤ _
        rw [Nat.cast_sub hle]
        have hsplit :
            ((st.2.2 : ℝ) - (st.2.1 : ℝ)) -
                ((S : ℝ) * ∑ k ∈ Finset.range n, (-z) ^ k / (Nat.factorial k : ℝ) +
                  (S : ℝ) * -(z ^ n / (Nat.factorial n : ℝ))) =
              ((st.2.2 : ℝ) - (S : ℝ) * ∑ k ∈ Finset.range n, (-z) ^ k / (Nat.factorial k : ℝ)) -
                ((st.2.1 : ℝ) - (S : ℝ) * (z ^ n / (Nat.factorial n : ℝ))) := by ring
        rw [hsplit]
        calc
          _ ≤ _ := abs_sub _ _
          _ ≤ 2 * (n : ℝ) + 2 := add_le_add ih ht_err
          _ = 2 * ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  have hsum_err :
      |(expNegSeries qBits zFp : ℝ) / (S : ℝ) -
          ∑ k ∈ Finset.range (2 * (qBits + 2)), (-z) ^ k / (Nat.factorial k : ℝ)| ≤
        4 * ((qBits : ℝ) + 2) / (S : ℝ) := by
    have hg := hgen (2 * (qBits + 2))
    have hEq : expNegSeries qBits zFp =
        ((expNegStep (S, zFp))^[2 * (qBits + 2)] (0, (S, 0))).2.2 := by
      dsimp only [expNegSeries]
      rw [min_eq_left hz]
    rw [hEq, ← mul_div_cancel_left₀ (∑ k ∈ Finset.range (2 * (qBits + 2)), _) hSpos.ne',
      ← sub_div, abs_div, abs_of_pos hSpos]
    refine div_le_div_of_nonneg_right ?_ hSpos.le
    calc
      _ ≤ 2 * ((2 * (qBits + 2) : ℕ) : ℝ) := hg
      _ = 4 * ((qBits : ℝ) + 2) := by push_cast; ring
  have htail :
      |Real.exp (-z) - ∑ k ∈ Finset.range (2 * (qBits + 2)), (-z) ^ k / (Nat.factorial k : ℝ)| ≤
        1 / (S : ℝ) := by
    have h1 := abs_exp_neg_sub_sum_le hz0 (qBits + 2)
    have hpow1 : z ^ (2 * (qBits + 2)) ≤ 1 := pow_le_one₀ hz0 hz1
    have hfac : (2 : ℕ) ^ qBits ≤ Nat.factorial (2 * (qBits + 2)) := by
      calc
        2 ^ qBits ≤ 2 ^ (2 * (qBits + 2) - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ Nat.factorial ((2 * (qBits + 2) - 1) + 1) := two_pow_le_factorial_succ _
        _ = Nat.factorial (2 * (qBits + 2)) := by
          have : 2 * (qBits + 2) - 1 + 1 = 2 * (qBits + 2) := by omega
          rw [this]
    have hfac' : (S : ℝ) ≤ (Nat.factorial (2 * (qBits + 2)) : ℝ) := by exact_mod_cast hfac
    have h2 : z ^ (2 * (qBits + 2)) / (Nat.factorial (2 * (qBits + 2)) : ℝ) ≤ 1 / (S : ℝ) := by
      calc
        z ^ (2 * (qBits + 2)) / (Nat.factorial (2 * (qBits + 2)) : ℝ) ≤
            1 / (Nat.factorial (2 * (qBits + 2)) : ℝ) :=
          div_le_div_of_nonneg_right hpow1 (by positivity)
        _ ≤ 1 / (S : ℝ) := one_div_le_one_div_of_le hSpos hfac'
    exact h1.trans h2
  have htri :
      |(expNegSeries qBits zFp : ℝ) / (S : ℝ) - Real.exp (-z)| ≤
        |(expNegSeries qBits zFp : ℝ) / (S : ℝ) -
            ∑ k ∈ Finset.range (2 * (qBits + 2)), (-z) ^ k / (Nat.factorial k : ℝ)| +
          |Real.exp (-z) -
            ∑ k ∈ Finset.range (2 * (qBits + 2)), (-z) ^ k / (Nat.factorial k : ℝ)| := by
    rw [abs_sub_comm (Real.exp (-z))]
    exact abs_sub_le _ _ _
  have hadd := htri.trans (add_le_add hsum_err htail)
  rw [← add_div] at hadd
  have hS_cast : (S : ℝ) = (2 : ℝ) ^ qBits := by dsimp only [S]; push_cast; rfl
  simpa only [z, hS_cast] using hadd

private theorem abs_expNegPow_div_sub_exp_le (qBits zFp K : ℕ) (hz : zFp ≤ 2 ^ qBits)
    {zReal : ℝ} (hzReal : 0 ≤ zReal)
    (hzErr : |zReal - (zFp : ℝ) / (2 : ℝ) ^ qBits| ≤ 2 / (2 : ℝ) ^ qBits) :
    |(expNegPow qBits zFp K : ℝ) / (2 : ℝ) ^ qBits - Real.exp (-(K : ℝ) * zReal)| ≤
      (K : ℝ) * (4 * ((qBits : ℝ) + 2) + 4) / (2 : ℝ) ^ qBits := by
  set S : ℕ := 2 ^ qBits
  set b : ℕ := expNegSeries qBits zFp
  have hS_cast : (S : ℝ) = (2 : ℝ) ^ qBits := by dsimp only [S]; push_cast; rfl
  have hSpos : (0 : ℝ) < (S : ℝ) := by positivity
  have hb_le : (b : ℝ) ≤ (S : ℝ) := by exact_mod_cast expNegSeries_le qBits zFp
  have hb_err : |(b : ℝ) / (S : ℝ) - Real.exp (-zReal)| ≤
      (4 * ((qBits : ℝ) + 2) + 3) / (S : ℝ) := by
    have h1 : |(b : ℝ) / (S : ℝ) - Real.exp (-((zFp : ℝ) / (S : ℝ)))| ≤
        (4 * ((qBits : ℝ) + 2) + 1) / (S : ℝ) := by
      simpa only [b, hS_cast] using abs_expNegSeries_div_sub_exp_le qBits zFp hz
    have h2 : |Real.exp (-((zFp : ℝ) / (S : ℝ))) - Real.exp (-zReal)| ≤ 2 / (S : ℝ) := by
      rw [abs_sub_comm]
      exact (abs_exp_neg_sub_exp_neg_le hzReal (by positivity)).trans
        (by simpa only [hS_cast] using hzErr)
    calc
      |(b : ℝ) / (S : ℝ) - Real.exp (-zReal)| ≤
          |(b : ℝ) / (S : ℝ) - Real.exp (-((zFp : ℝ) / (S : ℝ)))| +
            |Real.exp (-((zFp : ℝ) / (S : ℝ))) - Real.exp (-zReal)| := abs_sub_le _ _ _
      _ ≤ (4 * ((qBits : ℝ) + 2) + 1) / (S : ℝ) + 2 / (S : ℝ) := add_le_add h1 h2
      _ = (4 * ((qBits : ℝ) + 2) + 3) / (S : ℝ) := by ring
  rw [← hS_cast]
  induction K with
  | zero =>
    rw [expNegPow, Function.iterate_zero, id_eq]
    rw [hS_cast]
    simp
  | succ K ih =>
    unfold expNegPow at ih ⊢
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    set p : ℕ := (fun x => (x * b) / S)^[K] S
    have hp_le : (p : ℝ) ≤ (S : ℝ) := by exact_mod_cast expNegPow_le qBits zFp K
    have hdiv_err :
        |(((p * b) / S : ℕ) : ℝ) / (S : ℝ) - ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ))| ≤
        1 / (S : ℝ) := by
      have hlo : (((p * b) / S : ℕ) : ℝ) ≤ ((p * b : ℕ) : ℝ) / (S : ℝ) := by
        rw [le_div_iff₀ hSpos]
        exact_mod_cast Nat.div_mul_le_self (p * b) S
      have hhi : ((p * b : ℕ) : ℝ) / (S : ℝ) < (((p * b) / S : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hSpos]
        have h := Nat.lt_mul_div_succ (p * b) (by positivity : 0 < S)
        have h' : ((p * b : ℕ) : ℝ) < (S : ℝ) * ((((p * b) / S : ℕ) : ℝ) + 1) := by exact_mod_cast h
        linarith
      have h1 : |(((p * b) / S : ℕ) : ℝ) - ((p * b : ℕ) : ℝ) / (S : ℝ)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have hrew : ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ)) =
          (((p * b : ℕ) : ℝ) / (S : ℝ)) / (S : ℝ) := by
        push_cast; ring
      rw [hrew, ← sub_div, abs_div, abs_of_pos hSpos]
      exact div_le_div_of_nonneg_right h1 hSpos.le
    have hexp_step : Real.exp (-((K + 1 : ℕ) : ℝ) * zReal) =
        Real.exp (-(K : ℝ) * zReal) * Real.exp (-zReal) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have hsplit :
        (((p * b) / S : ℕ) : ℝ) / (S : ℝ) - Real.exp (-((K + 1 : ℕ) : ℝ) * zReal) =
          ((((p * b) / S : ℕ) : ℝ) / (S : ℝ) - ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ))) +
          ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ) - Real.exp (-zReal)) +
          ((p : ℝ) / (S : ℝ) - Real.exp (-(K : ℝ) * zReal)) * Real.exp (-zReal) := by
      rw [hexp_step]; ring
    change |(((p * b) / S : ℕ) : ℝ) / (S : ℝ) - Real.exp (-((K + 1 : ℕ) : ℝ) * zReal)| ≤ _
    rw [hsplit]
    have ht1 := abs_add_le
      ((((p * b) / S : ℕ) : ℝ) / (S : ℝ) - ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ)) +
        ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ) - Real.exp (-zReal)))
      (((p : ℝ) / (S : ℝ) - Real.exp (-(K : ℝ) * zReal)) * Real.exp (-zReal))
    have ht2 := abs_add_le
      ((((p * b) / S : ℕ) : ℝ) / (S : ℝ) - ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ)))
      (((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ) - Real.exp (-zReal)))
    have hp1 : (p : ℝ) / (S : ℝ) ≤ 1 := (div_le_one hSpos).mpr hp_le
    have hexp1 : Real.exp (-zReal) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hm1 : |((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ) - Real.exp (-zReal))| ≤
        (4 * ((qBits : ℝ) + 2) + 3) / (S : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact (mul_le_of_le_one_left (abs_nonneg _) hp1).trans hb_err
    have hm2 : |((p : ℝ) / (S : ℝ) - Real.exp (-(K : ℝ) * zReal)) * Real.exp (-zReal)| ≤
        (K : ℝ) * (4 * ((qBits : ℝ) + 2) + 4) / (S : ℝ) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_of_le_one_right (abs_nonneg _) hexp1).trans ih
    calc
      _ ≤ 1 / (S : ℝ) + (4 * ((qBits : ℝ) + 2) + 3) / (S : ℝ) +
          (K : ℝ) * (4 * ((qBits : ℝ) + 2) + 4) / (S : ℝ) := by linarith
      _ = ((K + 1 : ℕ) : ℝ) * (4 * ((qBits : ℝ) + 2) + 4) / (S : ℝ) := by push_cast; ring


/-! ### 5. `SampleZInput`, radius, weight numerator, and `sampleZ` -/

open scoped ENNReal RealInnerProductSpace Cslib.Probability.PMF
open Module Cslib.Probability Cslib.ProbComp ProbabilityTheory

/-- Input specification for the 1-D discrete Gaussian sampler `sampleZ`. -/
structure SampleZInput where
  /-- Rational squared Gaussian width `s² > 0`. -/
  sSq : ℚ
  /-- Rational center `c`. -/
  center : ℚ
  /-- Unary tail-cutoff multiplier `t`. -/
  tail : ℕ
  /-- Unary dyadic acceptance-coin precision `prec`. -/
  prec : ℕ
  /-- Unary rejection-trial cap `maxTrials`. -/
  maxTrials : ℕ
  deriving DecidableEq, Repr

namespace SampleZInput

/-- Framing encoding of `SampleZInput`: binary rationals `sSq` and `center`, unary `tail`,
`prec`, and `maxTrials`. -/
enc_structure enc : SampleZInput where
  sSq : encRat, center : encRat, tail : encUnary, prec : encUnary, maxTrials : encUnary

end SampleZInput

open scoped SampleZInput

/-- Integer search radius `R = ⌊√(t² · ⌊s²⌋)⌋ + 2` (using floor of `t² · s²`). -/
private def sampleZRadius (inp : SampleZInput) : ℕ :=
  Nat.sqrt ((inp.tail ^ 2 * inp.sSq.num.natAbs) / inp.sSq.den) + 2

private theorem sampleZRadius_ge_two (inp : SampleZInput) : 2 ≤ sampleZRadius inp := by
  unfold sampleZRadius; omega

private theorem computableInPolyTime_sampleZRadius :
    ComputableInPolyTime sampleZRadius SampleZInput.enc encNat := by
  unfold sampleZRadius
  have hsSq : ComputableInPolyTime SampleZInput.sSq SampleZInput.enc encRat := by fun_prop
  have htail : ComputableInPolyTime SampleZInput.tail SampleZInput.enc encUnary := by fun_prop
  have htailBin : ComputableInPolyTime SampleZInput.tail SampleZInput.enc encNat :=
    unary_to_binary.comp htail
  have htailSq : ComputableInPolyTime (fun inp : SampleZInput => inp.tail ^ 2)
      SampleZInput.enc encNat := by
    have : (fun inp : SampleZInput => inp.tail ^ 2) = fun inp => inp.tail * inp.tail := by
      funext inp; rw [sq]
    rw [this]
    exact binary_mul' htailBin htailBin
  have hnum : ComputableInPolyTime (fun inp : SampleZInput => inp.sSq.num.natAbs)
      SampleZInput.enc encNat := intBin_natAbs.comp (rat_num.comp hsSq)
  have hden : ComputableInPolyTime (fun inp : SampleZInput => inp.sSq.den)
      SampleZInput.enc encNat := rat_den.comp hsSq
  exact binary_add' (binary_sqrt' (binary_div' (binary_mul' htailSq hnum) hden)) (const 2)

private theorem rat_eq_natAbs_div_den {q : ℚ} (hq : 0 ≤ q) :
    (q : ℝ) = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
  have hnum : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  conv_lhs => rw [Rat.cast_def, ← hnum, Int.cast_natCast]

private theorem lt_sampleZRadius_sub_one (inp : SampleZInput) (hsSq : 0 < inp.sSq) :
    (inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ) < (sampleZRadius inp : ℝ) - 1 := by
  set m : ℕ := (inp.tail ^ 2 * inp.sSq.num.natAbs) / inp.sSq.den
  have hden_pos : 0 < inp.sSq.den := inp.sSq.den_pos
  have hden_r : (0 : ℝ) < (inp.sSq.den : ℝ) := by exact_mod_cast hden_pos
  have hq : (inp.sSq : ℝ) = (inp.sSq.num.natAbs : ℝ) / (inp.sSq.den : ℝ) :=
    rat_eq_natAbs_div_den hsSq.le
  have hsq_lt :
      ((inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ)) ^ 2 < ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by
    have h1 : ((inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ)) ^ 2 =
        ((inp.tail ^ 2 * inp.sSq.num.natAbs : ℕ) : ℝ) / (inp.sSq.den : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by exact_mod_cast hsSq.le), hq]
      push_cast; ring
    have h2 : ((inp.tail ^ 2 * inp.sSq.num.natAbs : ℕ) : ℝ) / (inp.sSq.den : ℝ) < (m : ℝ) + 1 := by
      rw [div_lt_iff₀ hden_r]
      have h := Nat.lt_mul_div_succ (inp.tail ^ 2 * inp.sSq.num.natAbs) hden_pos
      have h' : ((inp.tail ^ 2 * inp.sSq.num.natAbs : ℕ) : ℝ) <
          (inp.sSq.den : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast h
      linarith
    have h3 : m + 1 ≤ (Nat.sqrt m + 1) ^ 2 := by
      rw [sq]
      exact Nat.succ_le_of_lt (Nat.lt_succ_sqrt m)
    have h3' : (m : ℝ) + 1 ≤ ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h3
    linarith
  have hlt : (inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ) < ((Nat.sqrt m + 1 : ℕ) : ℝ) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) inp.tail) (Real.sqrt_nonneg (inp.sSq : ℝ)),
      Nat.cast_nonneg (α := ℝ) (Nat.sqrt m + 1)]
  have hR : (sampleZRadius inp : ℝ) - 1 = ((Nat.sqrt m + 1 : ℕ) : ℝ) := by
    unfold sampleZRadius; push_cast; ring
  linarith

private theorem sampleZRadius_le (inp : SampleZInput) (hsSq : 0 < inp.sSq) :
    (sampleZRadius inp : ℝ) ≤ (inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ) + 2 := by
  set m : ℕ := (inp.tail ^ 2 * inp.sSq.num.natAbs) / inp.sSq.den
  have hden_r : (0 : ℝ) < (inp.sSq.den : ℝ) := by exact_mod_cast inp.sSq.den_pos
  have hq : (inp.sSq : ℝ) = (inp.sSq.num.natAbs : ℝ) / (inp.sSq.den : ℝ) :=
    rat_eq_natAbs_div_den hsSq.le
  have hsq_le : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ ((inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ)) ^ 2 := by
    have h1 : (Nat.sqrt m : ℕ) ^ 2 ≤ m := by rw [sq]; exact Nat.sqrt_le m
    have h2 : (m : ℝ) ≤ ((inp.tail ^ 2 * inp.sSq.num.natAbs : ℕ) : ℝ) / (inp.sSq.den : ℝ) := by
      rw [le_div_iff₀ hden_r]
      exact_mod_cast Nat.div_mul_le_self (inp.tail ^ 2 * inp.sSq.num.natAbs) inp.sSq.den
    have h3 : ((inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ)) ^ 2 =
        ((inp.tail ^ 2 * inp.sSq.num.natAbs : ℕ) : ℝ) / (inp.sSq.den : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by exact_mod_cast hsSq.le), hq]
      push_cast; ring
    have h1' : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast h1
    linarith
  have hle : (Nat.sqrt m : ℝ) ≤ (inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) inp.tail) (Real.sqrt_nonneg (inp.sSq : ℝ)),
      Nat.cast_nonneg (α := ℝ) (Nat.sqrt m)]
  unfold sampleZRadius
  push_cast
  linarith

private theorem two_mul_sampleZRadius_add_one_le (inp : SampleZInput) (hsSq : 0 < inp.sSq)
    (hs1 : 1 ≤ Real.sqrt (inp.sSq : ℝ)) :
    ((2 * sampleZRadius inp + 1 : ℕ) : ℝ) ≤
      (2 * (inp.tail : ℝ) + 6) * Real.sqrt (inp.sSq : ℝ) := by
  have hR := sampleZRadius_le inp hsSq
  push_cast
  nlinarith

/-- Extra internal fixed-point guard bits for `sampleZWeightNum`. -/
private def sampleZShift (tail prec : ℕ) : ℕ :=
  3 * Nat.clog 2 (tail + 3) + Nat.clog 2 (prec + 16) + 12

private theorem nat_clog_two_le_self (n : ℕ) : Nat.clog 2 n ≤ n := by
  exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)

private theorem sampleZShift_bound (tail prec : ℕ) :
    2 * (4 * (tail + 3) ^ 2) * (4 * (prec + sampleZShift tail prec + 2) + 4) ≤
      2 ^ sampleZShift tail prec := by
  set cT := Nat.clog 2 (tail + 3)
  set cP := Nat.clog 2 (prec + 16)
  set A := 2 ^ cT
  set B := 2 ^ cP
  have hA_ge : tail + 3 ≤ A := Nat.le_pow_clog (by omega) _
  have hB_ge : prec + 16 ≤ B := Nat.le_pow_clog (by omega) _
  have hcT : cT ≤ A := (nat_clog_two_le_self (tail + 3)).trans hA_ge
  have hcP : cP ≤ B := (nat_clog_two_le_self (prec + 16)).trans hB_ge
  have h2s : 2 ^ sampleZShift tail prec = 4096 * A ^ 3 * B := by
    unfold sampleZShift
    change 2 ^ (3 * cT + cP + 12) = 4096 * A ^ 3 * B
    rw [pow_add, pow_add, pow_mul]
    have hpow3 : (2 ^ 3) ^ cT = A ^ 3 := by
      dsimp only [A]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hpow3]
    norm_num
    ring
  have hK : 4 * (tail + 3) ^ 2 ≤ 4 * A ^ 2 := by nlinarith
  have hfac : 4 * (prec + sampleZShift tail prec + 2) + 4 ≤ 23 * A * B := by
    have hsh : sampleZShift tail prec = 3 * cT + cP + 12 := rfl
    nlinarith
  have hprod : 2 * (4 * (tail + 3) ^ 2) * (4 * (prec + sampleZShift tail prec + 2) + 4) ≤
      2 * (4 * A ^ 2) * (23 * A * B) := by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hK) hfac
  have h184 : 2 * (4 * A ^ 2) * (23 * A * B) = 184 * A ^ 3 * B := by ring
  rw [h2s]
  calc
    2 * (4 * (tail + 3) ^ 2) * (4 * (prec + sampleZShift tail prec + 2) + 4) ≤
        184 * A ^ 3 * B := h184 ▸ hprod
    _ ≤ 4096 * A ^ 3 * B :=
        Nat.mul_le_mul_right B (Nat.mul_le_mul_right (A ^ 3) (by omega))

private theorem computableInPolyTime_sampleZShift :
    ComputableInPolyTime (fun p : ℕ × ℕ => sampleZShift p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  unfold sampleZShift
  have hT := binary_clog_two.comp
    (unary_to_binary.comp (unary_add' (fst encUnary encUnary) (const 3)))
  have hP := binary_clog_two.comp
    (unary_to_binary.comp (unary_add' (snd encUnary encUnary) (const 16)))
  exact unary_add' (unary_add' (unary_mul' (const 3) hT) hP) (const 12)


/-- Squared normalized rational distance `(x - c)² / s²`. -/
private def sampleZRatArg (inp : SampleZInput) (x : ℤ) : ℚ :=
  ((x : ℚ) - inp.center) ^ 2 / inp.sSq

private theorem computableInPolyTime_sampleZRatArg :
    ComputableInPolyTime (fun p : SampleZInput × ℤ => sampleZRatArg p.1 p.2)
      (encPair SampleZInput.enc encIntBin) encRat := by
  let encIn := encPair SampleZInput.enc encIntBin
  have hcenter : ComputableInPolyTime (fun p : SampleZInput × ℤ => p.1.center)
      encIn encRat := by fun_prop
  have hsSq : ComputableInPolyTime (fun p : SampleZInput × ℤ => p.1.sSq)
      encIn encRat := by fun_prop
  have hdiff : ComputableInPolyTime (fun p : SampleZInput × ℤ => (p.2 : ℚ) - p.1.center)
      encIn encRat :=
    rat_sub' (rat_intCast.comp (snd SampleZInput.enc encIntBin)) hcenter
  have hsq : ComputableInPolyTime (fun p : SampleZInput × ℤ => ((p.2 : ℚ) - p.1.center) ^ 2)
      encIn encRat := by
    have : (fun p : SampleZInput × ℤ => ((p.2 : ℚ) - p.1.center) ^ 2) =
        fun p => ((p.2 : ℚ) - p.1.center) * ((p.2 : ℚ) - p.1.center) := by funext p; rw [sq]
    rw [this]
    exact rat_mul' hdiff hdiff
  exact rat_div' hsq hsSq

/-- Fixed-point scaled exponent `zFp = ⌊piApprox qBits * r / K⌋` for `sampleZWeightNum`. -/
private def sampleZZFp (inp : SampleZInput) (x : ℤ) : ℕ :=
  let qBits := inp.prec + sampleZShift inp.tail inp.prec
  let K := 4 * (inp.tail + 3) ^ 2
  let r := sampleZRatArg inp x
  (piApprox qBits * r.num.natAbs) / (r.den * K)

private theorem computableInPolyTime_sampleZK :
    ComputableInPolyTime (fun inp : SampleZInput => 4 * (inp.tail + 3) ^ 2)
      SampleZInput.enc encUnary := by
  have htail : ComputableInPolyTime SampleZInput.tail SampleZInput.enc encUnary := by fun_prop
  have htp3 : ComputableInPolyTime (fun inp : SampleZInput => inp.tail + 3)
      SampleZInput.enc encUnary := unary_add' htail (const 3)
  have hsq : ComputableInPolyTime (fun inp : SampleZInput => (inp.tail + 3) ^ 2)
      SampleZInput.enc encUnary := by
    have : (fun inp : SampleZInput => (inp.tail + 3) ^ 2) =
        fun inp => (inp.tail + 3) * (inp.tail + 3) := by funext inp; rw [sq]
    rw [this]
    exact unary_mul' htp3 htp3
  exact unary_mul' (const 4) hsq

private theorem computableInPolyTime_sampleZShiftOfInput :
    ComputableInPolyTime (fun inp : SampleZInput => sampleZShift inp.tail inp.prec)
      SampleZInput.enc encUnary := by
  have htail : ComputableInPolyTime SampleZInput.tail SampleZInput.enc encUnary := by fun_prop
  have hprec : ComputableInPolyTime SampleZInput.prec SampleZInput.enc encUnary := by fun_prop
  exact (htail.prod hprec).trans computableInPolyTime_sampleZShift

private theorem computableInPolyTime_sampleZQBits :
    ComputableInPolyTime (fun inp : SampleZInput => inp.prec + sampleZShift inp.tail inp.prec)
      SampleZInput.enc encUnary := by
  have hprec : ComputableInPolyTime SampleZInput.prec SampleZInput.enc encUnary := by fun_prop
  exact unary_add' hprec computableInPolyTime_sampleZShiftOfInput

private theorem computableInPolyTime_sampleZZFp :
    ComputableInPolyTime (fun p : SampleZInput × ℤ => sampleZZFp p.1 p.2)
      (encPair SampleZInput.enc encIntBin) encNat := by
  have hfst := fst SampleZInput.enc encIntBin
  have hpi := computableInPolyTime_piApprox.comp (computableInPolyTime_sampleZQBits.comp hfst)
  have hr := computableInPolyTime_sampleZRatArg
  have hK := unary_to_binary.comp (computableInPolyTime_sampleZK.comp hfst)
  exact binary_div' (binary_mul' hpi (intBin_natAbs.comp (rat_num.comp hr)))
    (binary_mul' (rat_den.comp hr) hK)

/-- Numerator `w ≤ 2 ^ inp.prec` approximating `2 ^ inp.prec * exp(-π (x - c)² / s²)` in
polynomial time. Returns `0` if `inp.sSq ≤ 0`. -/
private def sampleZWeightNum (inp : SampleZInput) (x : ℤ) : ℕ :=
  if inp.sSq ≤ 0 then 0
  else
    let shift := sampleZShift inp.tail inp.prec
    let qBits := inp.prec + shift
    let K := 4 * (inp.tail + 3) ^ 2
    let raw := expNegPow qBits (sampleZZFp inp x) K
    min (2 ^ inp.prec) ((raw + 2 ^ (shift - 1)) / 2 ^ shift)

private theorem sampleZWeightNum_le (inp : SampleZInput) (x : ℤ) :
    sampleZWeightNum inp x ≤ 2 ^ inp.prec := by
  unfold sampleZWeightNum
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.min_le_left _ _

private theorem computableInPolyTime_sampleZWeightNum :
    ComputableInPolyTime (fun p : SampleZInput × ℤ => sampleZWeightNum p.1 p.2)
      (encPair SampleZInput.enc encIntBin) encNat := by
  let encIn := encPair SampleZInput.enc encIntBin
  have hfst : ComputableInPolyTime (fun p : SampleZInput × ℤ => p.1)
      encIn SampleZInput.enc := fst SampleZInput.enc encIntBin
  have hsSq : ComputableInPolyTime (fun p : SampleZInput × ℤ => p.1.sSq)
      encIn encRat := by fun_prop
  have hprec : ComputableInPolyTime (fun p : SampleZInput × ℤ => p.1.prec)
      encIn encUnary := by fun_prop
  have hcond : ComputableInPolyTime (fun p : SampleZInput × ℤ => decide (p.1.sSq ≤ 0))
      encIn encBool := rat_le' hsSq (const (0 : ℚ))
  have hshift := computableInPolyTime_sampleZShiftOfInput.comp hfst
  have hqBits := computableInPolyTime_sampleZQBits.comp hfst
  have hK := computableInPolyTime_sampleZK.comp hfst
  have hraw :=
    ((hqBits.prod computableInPolyTime_sampleZZFp).prod hK).trans computableInPolyTime_expNegPow
  have hhalf := binary_two_pow.comp (unary_sub' hshift (const 1))
  have hden := binary_two_pow.comp hshift
  have hcap := binary_two_pow.comp hprec
  have hmain := ite_decide hcond (const 0)
    (binary_min' hcap (binary_div' (binary_add' hraw hhalf) hden))
  have heq :
      (fun p : SampleZInput × ℤ => sampleZWeightNum p.1 p.2) =
      (fun p : SampleZInput × ℤ =>
        if p.1.sSq ≤ 0 then 0
        else min (2 ^ p.1.prec)
          ((expNegPow (p.1.prec + sampleZShift p.1.tail p.1.prec) (sampleZZFp p.1 p.2)
              (4 * (p.1.tail + 3) ^ 2) + 2 ^ (sampleZShift p.1.tail p.1.prec - 1)) /
            2 ^ sampleZShift p.1.tail p.1.prec)) := rfl
  rw [heq]
  exact hmain

/-- Map a finite index `i : Fin (2 * R + 1)` to `cFloor - R + i : ℤ`. -/
private def finToInt (cFloor : ℤ) (R : ℕ) (i : Fin (2 * R + 1)) : ℤ :=
  cFloor - (R : ℤ) + (i.val : ℤ)

private theorem finToInt_injective (cFloor : ℤ) (R : ℕ) :
    Function.Injective (finToInt cFloor R) := by
  intro i j h
  unfold finToInt at h
  ext
  omega

private theorem abs_sampleZWeightNum_div_sub_gaussianWeight_le
    (inp : SampleZInput) (hsSq : 0 < inp.sSq) (hs1 : 1 ≤ Real.sqrt (inp.sSq : ℝ))
    (i : Fin (2 * sampleZRadius inp + 1)) :
    let x := finToInt (ratFloor inp.center) (sampleZRadius inp) i
    |(sampleZWeightNum inp x : ℝ) / (2 : ℝ) ^ inp.prec -
        gaussianWeight (Real.sqrt (inp.sSq : ℝ)) ((x : ℝ) - (inp.center : ℝ))| ≤
      (2 : ℝ) ^ (-(inp.prec : ℤ)) := by
  intro x
  set s : ℝ := Real.sqrt (inp.sSq : ℝ)
  let R : ℕ := sampleZRadius inp
  set shift : ℕ := sampleZShift inp.tail inp.prec
  set qBits : ℕ := inp.prec + shift
  set K : ℕ := 4 * (inp.tail + 3) ^ 2
  set piFp : ℕ := piApprox qBits
  set r : ℚ := sampleZRatArg inp x
  set zFp : ℕ := sampleZZFp inp x
  set raw : ℕ := expNegPow qBits zFp K
  have hshift12 : 12 ≤ shift := by dsimp only [shift, sampleZShift]; omega
  have hqBits12 : 12 ≤ qBits := by omega
  have hKpos : 0 < K := by dsimp only [K]; positivity
  have hsSq_r : (0 : ℝ) < (inp.sSq : ℝ) := by exact_mod_cast hsSq
  have hs_sq : s ^ 2 = (inp.sSq : ℝ) := Real.sq_sqrt hsSq_r.le
  have hr_nonneg : (0 : ℚ) ≤ r := div_nonneg (sq_nonneg _) hsSq.le
  have hr_cast : (r : ℝ) = ((x : ℝ) - (inp.center : ℝ)) ^ 2 / s ^ 2 := by
    dsimp only [r, sampleZRatArg]; rw [hs_sq]; push_cast; rfl
  have hr_nat : (r : ℝ) = (r.num.natAbs : ℝ) / (r.den : ℝ) := rat_eq_natAbs_div_den hr_nonneg
  have hfloor : (ratFloor inp.center : ℝ) ≤ (inp.center : ℝ) ∧
      (inp.center : ℝ) < (ratFloor inp.center : ℝ) + 1 := by
    rw [ratFloor_eq_intFloor]
    have h1 : ((Int.floor inp.center : ℤ) : ℚ) ≤ inp.center := Int.floor_le inp.center
    have h2 : inp.center < ((Int.floor inp.center : ℤ) : ℚ) + 1 := Int.lt_floor_add_one inp.center
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hx_dist : |(x : ℝ) - (inp.center : ℝ)| ≤ ((inp.tail : ℝ) + 3) * s := by
    have hR := sampleZRadius_le inp hsSq
    have hx_eq : (x : ℝ) = (ratFloor inp.center : ℝ) - (R : ℝ) + (i.val : ℝ) := by
      dsimp only [x, finToInt, R]; push_cast; rfl
    have hi_le : (i.val : ℝ) ≤ 2 * (R : ℝ) := by
      have : i.val ≤ 2 * R := by omega
      exact_mod_cast this
    have hi_ge : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> nlinarith
  have hr_div_K : (r : ℝ) / (K : ℝ) ≤ 1 / 4 := by
    rw [hr_cast]
    have hsq : ((x : ℝ) - (inp.center : ℝ)) ^ 2 ≤ (((inp.tail : ℝ) + 3) * s) ^ 2 := by
      rw [← sq_abs ((x : ℝ) - (inp.center : ℝ))]
      exact pow_le_pow_left₀ (abs_nonneg _) hx_dist 2
    have hdiv : ((x : ℝ) - (inp.center : ℝ)) ^ 2 / s ^ 2 ≤ ((inp.tail : ℝ) + 3) ^ 2 := by
      rw [div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < s))]
      nlinarith
    have hK_r : (K : ℝ) = 4 * ((inp.tail : ℝ) + 3) ^ 2 := by dsimp only [K]; push_cast; ring
    rw [hK_r, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set zReal : ℝ := Real.pi * (r : ℝ) / (K : ℝ)
  have hzReal0 : 0 ≤ zReal := by
    dsimp only [zReal]
    have : 0 ≤ (r : ℝ) := by exact_mod_cast hr_nonneg
    positivity
  have hpiErr : |(piFp : ℝ) / (2 : ℝ) ^ qBits - Real.pi| ≤ 1 / (2 : ℝ) ^ qBits := by
    have h := abs_piApprox_div_sub_pi_le qBits
    rw [zpow_neg, zpow_natCast, ← one_div] at h
    exact h
  have hdenK_pos : (0 : ℝ) < ((r.den * K : ℕ) : ℝ) := by
    have : 0 < r.den * K := Nat.mul_pos r.den_pos hKpos
    exact_mod_cast this
  have hzFp_le_exact : (zFp : ℝ) / (2 : ℝ) ^ qBits ≤
      ((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) := by
    have h1 : (zFp : ℝ) ≤ ((piFp * r.num.natAbs : ℕ) : ℝ) / ((r.den * K : ℕ) : ℝ) := by
      rw [le_div_iff₀ hdenK_pos]
      exact_mod_cast Nat.div_mul_le_self (piFp * r.num.natAbs) (r.den * K)
    have h2 : ((piFp * r.num.natAbs : ℕ) : ℝ) / ((r.den * K : ℕ) : ℝ) / (2 : ℝ) ^ qBits =
        ((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) := by
      rw [hr_nat]; push_cast; ring
    rw [← h2]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have hzFp_gt_exact :
      ((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) - 1 / (2 : ℝ) ^ qBits <
        (zFp : ℝ) / (2 : ℝ) ^ qBits := by
    have h1 : ((piFp * r.num.natAbs : ℕ) : ℝ) / ((r.den * K : ℕ) : ℝ) < (zFp : ℝ) + 1 := by
      rw [div_lt_iff₀ hdenK_pos]
      have h := Nat.lt_mul_div_succ (piFp * r.num.natAbs) (Nat.mul_pos r.den_pos hKpos)
      have h' : ((piFp * r.num.natAbs : ℕ) : ℝ) <
          ((r.den * K : ℕ) : ℝ) * ((zFp : ℝ) + 1) := by exact_mod_cast h
      linarith
    have h2 : ((piFp * r.num.natAbs : ℕ) : ℝ) / ((r.den * K : ℕ) : ℝ) / (2 : ℝ) ^ qBits =
        ((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) := by
      rw [hr_nat]; push_cast; ring
    have h3 := div_lt_div_of_pos_right h1 (by positivity : (0 : ℝ) < (2 : ℝ) ^ qBits)
    rw [h2, add_div] at h3
    linarith
  have hzErr : |zReal - (zFp : ℝ) / (2 : ℝ) ^ qBits| ≤ 2 / (2 : ℝ) ^ qBits := by
    have hrK0 : 0 ≤ (r : ℝ) / (K : ℝ) := by
      have : 0 ≤ (r : ℝ) := by exact_mod_cast hr_nonneg
      positivity
    have h1 : |((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) - zReal| ≤
        (1 / 4) / (2 : ℝ) ^ qBits := by
      have hrew : ((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) - zReal =
          ((piFp : ℝ) / (2 : ℝ) ^ qBits - Real.pi) * ((r : ℝ) / (K : ℝ)) := by
        dsimp only [zReal]; ring
      rw [hrew, abs_mul, abs_of_nonneg hrK0]
      calc
        |(piFp : ℝ) / (2 : ℝ) ^ qBits - Real.pi| * ((r : ℝ) / (K : ℝ)) ≤
            (1 / (2 : ℝ) ^ qBits) * (1 / 4) := mul_le_mul hpiErr hr_div_K hrK0 (by positivity)
        _ = (1 / 4) / (2 : ℝ) ^ qBits := by ring
    have h2 : |((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) - (zFp : ℝ) / (2 : ℝ) ^ qBits| ≤
        1 / (2 : ℝ) ^ qBits := by
      rw [abs_le]; constructor <;> linarith
    have htri : |zReal - (zFp : ℝ) / (2 : ℝ) ^ qBits| ≤
        |((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) - zReal| +
          |((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) - (zFp : ℝ) / (2 : ℝ) ^ qBits| := by
      rw [abs_sub_comm (((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ))) zReal]
      exact abs_sub_le _ _ _
    have hpos : (0 : ℝ) < (2 : ℝ) ^ qBits := by positivity
    have hcomb : (1 / 4) / (2 : ℝ) ^ qBits + 1 / (2 : ℝ) ^ qBits ≤ 2 / (2 : ℝ) ^ qBits := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) hpos.le
    linarith
  have hzFp_le : zFp ≤ 2 ^ qBits := by
    have hpi4 : Real.pi < 3.15 := by linarith [Real.pi_lt_d4]
    have h2q : (4096 : ℝ) ≤ (2 : ℝ) ^ qBits := by
      have : 2 ^ 12 ≤ 2 ^ qBits := Nat.pow_le_pow_right (by omega) hqBits12
      exact_mod_cast this
    have hzReal_lt : zReal ≤ 3.15 / 4 := by
      have : zReal = Real.pi * ((r : ℝ) / (K : ℝ)) := by dsimp only [zReal]; ring
      rw [this]
      have hrK0 : 0 ≤ (r : ℝ) / (K : ℝ) := by
        have : 0 ≤ (r : ℝ) := by exact_mod_cast hr_nonneg
        positivity
      calc
        Real.pi * ((r : ℝ) / (K : ℝ)) ≤ 3.15 * (1 / 4) :=
          mul_le_mul hpi4.le hr_div_K hrK0 (by norm_num)
        _ = 3.15 / 4 := by ring
    have hzFp_lt : (zFp : ℝ) / (2 : ℝ) ^ qBits ≤ 1 := by
      have hsub := (abs_le.mp hzErr).1
      have h2div : 2 / (2 : ℝ) ^ qBits ≤ 2 / 4096 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2q
      linarith
    have hle_r : (zFp : ℝ) ≤ ((2 ^ qBits : ℕ) : ℝ) := by
      push_cast
      exact (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ qBits)).mp hzFp_lt
    exact_mod_cast hle_r
  have hexp_err := abs_expNegPow_div_sub_exp_le qBits zFp K hzFp_le hzReal0 hzErr
  have hKz : -(K : ℝ) * zReal = -Real.pi * ‖(x : ℝ) - (inp.center : ℝ)‖ ^ 2 / s ^ 2 := by
    dsimp only [zReal]
    rw [hr_cast, Real.norm_eq_abs, sq_abs]
    have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
    field_simp
  have hraw_err : |(raw : ℝ) / (2 : ℝ) ^ qBits -
      gaussianWeight s ((x : ℝ) - (inp.center : ℝ))| ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ inp.prec := by
    have hbound : (K : ℝ) * (4 * ((qBits : ℝ) + 2) + 4) / (2 : ℝ) ^ qBits ≤
        (1 / 2 : ℝ) / (2 : ℝ) ^ inp.prec := by
      have hb_nat : 2 * (K * (4 * (qBits + 2) + 4)) ≤ 2 ^ shift := by
        simpa only [K, qBits, shift, Nat.mul_assoc] using sampleZShift_bound inp.tail inp.prec
      have hb_r : 2 * ((K : ℝ) * (4 * ((qBits : ℝ) + 2) + 4)) ≤ (2 : ℝ) ^ shift := by
        exact_mod_cast hb_nat
      have h2q : (2 : ℝ) ^ qBits = (2 : ℝ) ^ inp.prec * (2 : ℝ) ^ shift := by
        dsimp only [qBits]; rw [pow_add]
      have h2p : (0 : ℝ) < (2 : ℝ) ^ inp.prec := by positivity
      have hmul := mul_le_mul_of_nonneg_left hb_r h2p.le
      rw [h2q, div_le_div_iff₀ (by positivity) h2p]
      linarith
    have hgw : gaussianWeight s ((x : ℝ) - (inp.center : ℝ)) = Real.exp (-(K : ℝ) * zReal) := by
      unfold gaussianWeight; rw [hKz]
    rw [hgw]
    exact hexp_err.trans hbound
  have hraw_le : raw ≤ 2 ^ qBits := expNegPow_le qBits zFp K
  have hround_le : (raw + 2 ^ (shift - 1)) / 2 ^ shift ≤ 2 ^ inp.prec := by
    have h1 : raw + 2 ^ (shift - 1) < (2 ^ inp.prec + 1) * 2 ^ shift := by
      have h2q : 2 ^ qBits = 2 ^ inp.prec * 2 ^ shift := by dsimp only [qBits]; rw [pow_add]
      have hhalf : 2 ^ (shift - 1) < 2 ^ shift := Nat.pow_lt_pow_right (by omega) (by omega)
      rw [Nat.add_mul, one_mul]
      omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by positivity)).mpr h1)
  have hw_eq : sampleZWeightNum inp x = (raw + 2 ^ (shift - 1)) / 2 ^ shift := by
    unfold sampleZWeightNum
    rw [ite_eq_right (not_le.mpr hsSq)]
    exact Nat.min_eq_right hround_le
  have hshift_err : |(((raw + 2 ^ (shift - 1)) / 2 ^ shift : ℕ) : ℝ) -
      (raw : ℝ) / (2 : ℝ) ^ shift| ≤ 1 / 2 :=
    abs_div_two_pow_round_sub_le raw shift (by omega)
  have hshift_scaled :
      |(((raw + 2 ^ (shift - 1)) / 2 ^ shift : ℕ) : ℝ) / (2 : ℝ) ^ inp.prec -
          (raw : ℝ) / (2 : ℝ) ^ qBits| ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ inp.prec := by
    have h2q : (2 : ℝ) ^ qBits = (2 : ℝ) ^ inp.prec * (2 : ℝ) ^ shift := by
      dsimp only [qBits]; rw [pow_add]
    rw [h2q, ← div_div, div_right_comm (raw : ℝ), ← sub_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ inp.prec)]
    exact div_le_div_of_nonneg_right hshift_err (by positivity)
  rw [hw_eq, zpow_neg, zpow_natCast, ← one_div]
  calc
    |(((raw + 2 ^ (shift - 1)) / 2 ^ shift : ℕ) : ℝ) / (2 : ℝ) ^ inp.prec -
        gaussianWeight s ((x : ℝ) - (inp.center : ℝ))| ≤
      |(((raw + 2 ^ (shift - 1)) / 2 ^ shift : ℕ) : ℝ) / (2 : ℝ) ^ inp.prec -
          (raw : ℝ) / (2 : ℝ) ^ qBits| +
        |(raw : ℝ) / (2 : ℝ) ^ qBits - gaussianWeight s ((x : ℝ) - (inp.center : ℝ))| :=
      abs_sub_le _ _ _
    _ ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ inp.prec + (1 / 2 : ℝ) / (2 : ℝ) ^ inp.prec :=
      add_le_add hshift_scaled hraw_err
    _ = 1 / (2 : ℝ) ^ inp.prec := by ring


/-- Non-dependent single-block rejection specification for `sampleZ` outputting `Option ℤ`. -/
private def sampleZIntSpec (inp : SampleZInput) : BlockRejectionSpec ℤ where
  width := Nat.clog 2 (2 * sampleZRadius inp + 1) + inp.prec
  attempt bits :=
    let R := sampleZRadius inp
    let k := Nat.clog 2 (2 * R + 1)
    let idx := Cslib.BitString.binaryValue (bits.take k)
    let coin := Cslib.BitString.binaryValue (bits.drop k)
    if idx < 2 * R + 1 then
      let x : ℤ := ratFloor inp.center - (R : ℤ) + (idx : ℤ)
      if coin < sampleZWeightNum inp x then some x else none
    else none

/-- Strict-PPT capped-trial 1-D discrete Gaussian sampler ([GentryPeikertVaikuntanathan2008],
§4.1, Lemma 4.3, p. 15). -/
noncomputable def sampleZ (inp : SampleZInput) : ProbComp ℤ :=
  sampleBlockCapped (sampleZIntSpec inp) (ratFloor inp.center) inp.maxTrials

private theorem computableInPolyTime_sampleZBitWidth :
    ComputableInPolyTime (fun inp : SampleZInput => Nat.clog 2 (2 * sampleZRadius inp + 1))
      SampleZInput.enc encUnary :=
  binary_clog_two.comp (binary_add' (binary_mul' (const 2) computableInPolyTime_sampleZRadius)
    (const 1))

private theorem computableInPolyTime_sampleZAttempt :
    ComputableInPolyTime
      (fun p : SampleZInput × List Bool => (sampleZIntSpec p.1).attempt p.2)
      (encPair SampleZInput.enc encBits) (encOption encIntBin) := by
  let encIn := encPair SampleZInput.enc encBits
  have hfst : ComputableInPolyTime (fun p : SampleZInput × List Bool => p.1)
      encIn SampleZInput.enc := fst SampleZInput.enc encBits
  have hsnd : ComputableInPolyTime (fun p : SampleZInput × List Bool => p.2)
      encIn encBits := snd SampleZInput.enc encBits
  have hcenter : ComputableInPolyTime SampleZInput.center SampleZInput.enc encRat := by fun_prop
  have hfallback : ComputableInPolyTime (fun inp : SampleZInput => ratFloor inp.center)
      SampleZInput.enc encIntBin := computableInPolyTime_ratFloor.comp hcenter
  have hR := computableInPolyTime_sampleZRadius
  have h2R1 : ComputableInPolyTime (fun inp : SampleZInput => 2 * sampleZRadius inp + 1)
      SampleZInput.enc encNat :=
    binary_add' (binary_mul' (const 2) hR) (const 1)
  have hk := computableInPolyTime_sampleZBitWidth
  have htake := bitsTakeWithInput hsnd (hk.comp hfst)
  have hdrop := bitsDropWithInput hsnd (hk.comp hfst)
  have hidx := bitsBinaryValue.comp htake
  have hcoin := bitsBinaryValue.comp hdrop
  have hlt1 := binary_lt' hidx (h2R1.comp hfst)
  have hx := intBin_add'
    (intBin_sub' (hfallback.comp hfst) (intBin_natCast.comp (hR.comp hfst)))
    (intBin_natCast.comp hidx)
  have hw := (hfst.prod hx).trans computableInPolyTime_sampleZWeightNum
  have hlt2 := binary_lt' hcoin hw
  have hinner := ite_decide hlt2 ((optionSome encIntBin).comp hx) (const none)
  have houter := ite_decide hlt1 hinner (const none)
  exact houter

/-- Strict-PPT certificate for the 1-D discrete Gaussian sampler `sampleZ`. -/
theorem isPPTOn_sampleZ : IsPPTOn SampleZInput.enc encIntBin sampleZ := by
  have htrials : ComputableInPolyTime SampleZInput.maxTrials SampleZInput.enc encUnary := by
    fun_prop
  have hprec : ComputableInPolyTime SampleZInput.prec SampleZInput.enc encUnary := by fun_prop
  have hcenter : ComputableInPolyTime SampleZInput.center SampleZInput.enc encRat := by fun_prop
  have hwidth : ComputableInPolyTime (fun inp : SampleZInput => (sampleZIntSpec inp).width)
      SampleZInput.enc encUnary := unary_add' computableInPolyTime_sampleZBitWidth hprec
  have hfallback : ComputableInPolyTime (fun inp : SampleZInput => ratFloor inp.center)
      SampleZInput.enc encIntBin := computableInPolyTime_ratFloor.comp hcenter
  exact isPPTOn_sampleBlockCapped htrials hwidth computableInPolyTime_sampleZAttempt hfallback

/-! ### 6. Distribution analysis of `sampleZ` via `CloseTo` -/

/-- The standard 1-D integer lattice `ℤ ⊂ ℝ`. -/
noncomputable abbrev intLatticeReal : Submodule ℤ ℝ :=
  Submodule.span ℤ (Set.range (Basis.singleton Unit ℝ))

private theorem mem_intLatticeReal_iff (x : ℝ) : x ∈ intLatticeReal ↔ ∃ n : ℤ, (n : ℝ) = x := by
  have hspan : Set.range (Basis.singleton Unit ℝ) = {(1 : ℝ)} := by
    ext y
    simp
  rw [intLatticeReal, hspan, Submodule.mem_span_singleton]
  simp only [zsmul_eq_mul, mul_one]

/-- Additive equivalence identifying `ℤ` with `intLatticeReal ⊂ ℝ`. -/
private noncomputable def intLatticeEquiv : ℤ ≃+ intLatticeReal where
  toFun n := ⟨(n : ℝ), (mem_intLatticeReal_iff _).mpr ⟨n, rfl⟩⟩
  invFun z := Int.floor (z : ℝ)
  left_inv n := Int.floor_intCast n
  right_inv z := by
    obtain ⟨n, hn⟩ := (mem_intLatticeReal_iff (z : ℝ)).mp z.property
    ext
    dsimp only
    rw [← hn, Int.floor_intCast]
  map_add' m n := by ext; push_cast; rfl

/-- Canonical discrete Gaussian on `ℤ` induced by `ZLattice.discreteGaussian` on `ℤ ⊂ ℝ`. -/
noncomputable def discreteGaussianInt (s : ℝ) (hs : 0 < s) (c : ℝ) : PMF ℤ :=
  (ZLattice.discreteGaussian intLatticeReal s hs c).map intLatticeEquiv.symm

/-- Pointwise evaluation formula for `discreteGaussianInt`. -/
theorem discreteGaussianInt_apply (s : ℝ) (hs : 0 < s) (c : ℝ) (x : ℤ) :
    discreteGaussianInt s hs c x =
      ENNReal.ofReal (gaussianWeight s ((x : ℝ) - c)) /
        ENNReal.ofReal (ZLattice.gaussianMass intLatticeReal s c) := by
  classical
  unfold discreteGaussianInt
  rw [PMF.map_apply, tsum_eq_single (intLatticeEquiv x)]
  · simp only [AddEquiv.symm_apply_apply, ↓reduceIte, ZLattice.discreteGaussian_apply]
    rfl
  · intro z hz
    have hne : x ≠ intLatticeEquiv.symm z := by
      intro heq
      apply hz
      have := congrArg intLatticeEquiv heq
      simpa using this.symm
    simp [hne]

private def sampleZFinSpec (inp : SampleZInput) :
    BlockRejectionSpec (Fin (2 * sampleZRadius inp + 1)) where
  width := Nat.clog 2 (2 * sampleZRadius inp + 1) + inp.prec
  attempt bits :=
    let R := sampleZRadius inp
    let k := Nat.clog 2 (2 * R + 1)
    let idx := Cslib.BitString.binaryValue (bits.take k)
    let coin := Cslib.BitString.binaryValue (bits.drop k)
    if h : idx < 2 * R + 1 then
      let i : Fin (2 * R + 1) := ⟨idx, h⟩
      if coin < sampleZWeightNum inp (finToInt (ratFloor inp.center) R i) then some i else none
    else none

private theorem decodeTrials_map {α β : Type*} (spec : BlockRejectionSpec α) (f : α → β)
    (spec' : BlockRejectionSpec β) (hw : spec'.width = spec.width)
    (ha : ∀ bits, spec'.attempt bits = (spec.attempt bits).map f) :
    ∀ (t : ℕ) (bits : List Bool),
      spec'.decodeTrials t bits = (spec.decodeTrials t bits).map f
  | 0, _ => rfl
  | t + 1, bits => by
    rw [BlockRejectionSpec.decodeTrials_succ, BlockRejectionSpec.decodeTrials_succ, hw, ha]
    cases spec.attempt (bits.take spec.width) with
    | none => exact decodeTrials_map spec f spec' hw ha t (bits.drop spec.width)
    | some a => rfl

private theorem eval_sampleZ_eq_map_runCapped (inp : SampleZInput) :
    ProbComp.eval (sampleZ inp) =
      ((sampleZFinSpec inp).runCapped ⟨sampleZRadius inp, by omega⟩ inp.maxTrials).map
        (finToInt (ratFloor inp.center) (sampleZRadius inp)) := by
  have hdec := decodeTrials_map (sampleZFinSpec inp)
    (finToInt (ratFloor inp.center) (sampleZRadius inp)) (sampleZIntSpec inp) rfl (fun bits => by
      dsimp only [sampleZIntSpec, sampleZFinSpec, finToInt]
      by_cases h1 : Cslib.BitString.binaryValue
          (bits.take (Nat.clog 2 (2 * sampleZRadius inp + 1))) < 2 * sampleZRadius inp + 1
      · simp only [h1, ↓reduceIte, ↓reduceDIte]
        by_cases h2 : Cslib.BitString.binaryValue
            (bits.drop (Nat.clog 2 (2 * sampleZRadius inp + 1))) <
            sampleZWeightNum inp (ratFloor inp.center - (sampleZRadius inp : ℤ) +
              (Cslib.BitString.binaryValue
                (bits.take (Nat.clog 2 (2 * sampleZRadius inp + 1))) : ℤ))
        · simp only [h2, ↓reduceIte, Option.map_some]; rfl
        · simp only [h2, ↓reduceIte, Option.map_none]
      · simp only [h1, ↓reduceIte, ↓reduceDIte, Option.map_none])
  rw [sampleZ, eval_sampleBlockCapped, BlockRejectionSpec.runCapped,
    BlockRejectionSpec.runCapped, BlockRejectionSpec.runTrials, BlockRejectionSpec.runTrials]
  rw [PMF.map_comp, PMF.map_comp, PMF.map_comp]
  have hw : (sampleZIntSpec inp).width = (sampleZFinSpec inp).width := rfl
  rw [hw]
  congr 1
  funext bits
  simp only [Function.comp_apply, hdec]
  cases (sampleZFinSpec inp).decodeTrials inp.maxTrials bits with
  | none =>
    simp only [Option.map_none, Option.getD_none, finToInt]
    omega
  | some i =>
    simp only [Option.map_some, Option.getD_some]

private theorem sampleZFinSpec_singleLaw_some (inp : SampleZInput)
    (i : Fin (2 * sampleZRadius inp + 1)) :
    let R := sampleZRadius inp
    let k := Nat.clog 2 (2 * R + 1)
    (sampleZFinSpec inp).singleLaw (some i) =
      (sampleZWeightNum inp (finToInt (ratFloor inp.center) R i) : ℝ≥0∞) /
        ((2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞) ^ inp.prec) := by
  intro R k
  classical
  have hi_lt : i.val < 2 ^ k := lt_of_lt_of_le i.isLt (Nat.le_pow_clog (by omega) _)
  let iK : Fin (2 ^ k) := ⟨i.val, hi_lt⟩
  let w : ℕ := sampleZWeightNum inp (finToInt (ratFloor inp.center) R i)
  have hw_le : w ≤ 2 ^ inp.prec := sampleZWeightNum_le inp _
  have hlaw : (sampleZFinSpec inp).singleLaw =
      (PMF.uniformOfFintype (Fin (2 ^ k))).bind fun idx =>
        (PMF.uniformOfFintype (Fin (2 ^ inp.prec))).map fun coin =>
          if h : idx.val < 2 * R + 1 then
            let j : Fin (2 * R + 1) := ⟨idx.val, h⟩
            if coin.val < sampleZWeightNum inp (finToInt (ratFloor inp.center) R j) then some j
            else none
          else none := by
    unfold BlockRejectionSpec.singleLaw
    have hsplit : (sampleZFinSpec inp).width = k + inp.prec := rfl
    rw [hsplit]
    have h1 := Cslib.BitString.uniformList_bind_split k inp.prec
      (fun b1 b2 => PMF.pure (
        let idx := Cslib.BitString.binaryValue b1
        let coin := Cslib.BitString.binaryValue b2
        if h : idx < 2 * R + 1 then
          let j : Fin (2 * R + 1) := ⟨idx, h⟩
          if coin < sampleZWeightNum inp (finToInt (ratFloor inp.center) R j) then some j else none
        else none))
    change (Cslib.BitString.uniformList (k + inp.prec)).map _ = _
    rw [PMF.map]
    change (Cslib.BitString.uniformList (k + inp.prec)).bind
      (fun tape => PMF.pure (
        let idx := Cslib.BitString.binaryValue (tape.take k)
        let coin := Cslib.BitString.binaryValue (tape.drop k)
        if h : idx < 2 * R + 1 then
          let j : Fin (2 * R + 1) := ⟨idx, h⟩
          if coin < sampleZWeightNum inp (finToInt (ratFloor inp.center) R j) then some j else none
        else none)) = _
    rw [h1]
    have hmap1 : ∀ (f : ℕ → PMF (Option (Fin (2 * R + 1)))),
        (Cslib.BitString.uniformList k).bind (fun b => f (Cslib.BitString.binaryValue b)) =
          (PMF.uniformOfFintype (Fin (2 ^ k))).bind (fun idx => f idx.val) := by
      intro f
      change (Cslib.BitString.uniformList k).bind (f ∘ Cslib.BitString.binaryValue) =
        (PMF.uniformOfFintype (Fin (2 ^ k))).bind (f ∘ Fin.val)
      rw [← PMF.bind_map, Cslib.BitString.uniformList_binaryValue, PMF.bind_map]
    have hmap2 : ∀ (g : ℕ → Option (Fin (2 * R + 1))),
        (Cslib.BitString.uniformList inp.prec).bind
          (fun b => PMF.pure (g (Cslib.BitString.binaryValue b))) =
          (PMF.uniformOfFintype (Fin (2 ^ inp.prec))).map (fun coin => g coin.val) := by
      intro g
      change (Cslib.BitString.uniformList inp.prec).map (g ∘ Cslib.BitString.binaryValue) =
        (PMF.uniformOfFintype (Fin (2 ^ inp.prec))).map (g ∘ Fin.val)
      rw [← PMF.map_comp, Cslib.BitString.uniformList_binaryValue, PMF.map_comp]
    dsimp only
    rw [hmap1 (fun idx => (Cslib.BitString.uniformList inp.prec).bind fun b2 => PMF.pure
      (if h : idx < 2 * R + 1 then
        if Cslib.BitString.binaryValue b2 <
            sampleZWeightNum inp (finToInt (ratFloor inp.center) R ⟨idx, h⟩)
        then some ⟨idx, h⟩ else none else none))]
    congr 1; funext idx
    exact hmap2 (fun coin =>
      if h : idx.val < 2 * R + 1 then
        if coin < sampleZWeightNum inp (finToInt (ratFloor inp.center) R ⟨idx.val, h⟩)
        then some ⟨idx.val, h⟩ else none else none)
  rw [hlaw, PMF.bind_apply, tsum_eq_single iK]
  · simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
      PMF.map_apply]
    have hiK : iK.val < 2 * R + 1 := i.isLt
    simp only [hiK, ↓reduceDIte]
    have hcoin : (∑' coin : Fin (2 ^ inp.prec),
        if some i = (if coin.val < w then some i else none) then
          ((2 : ℝ≥0∞) ^ inp.prec)⁻¹
        else 0) = (w : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ inp.prec)⁻¹ := by
      rw [tsum_fintype]
      have hite : ∀ coin : Fin (2 ^ inp.prec),
          (if some i = (if coin.val < w then some i else none) then ((2 : ℝ≥0∞) ^ inp.prec)⁻¹
            else 0) = if coin.val < w then ((2 : ℝ≥0∞) ^ inp.prec)⁻¹ else 0 := by
        intro coin
        by_cases hcw : coin.val < w <;> simp [hcw]
      simp_rw [hite, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        Fin.card_filter_val_lt, Nat.min_eq_right hw_le]
    have hrew : (⟨iK.val, hiK⟩ : Fin (2 * R + 1)) = i := Fin.ext rfl
    rw [hrew]
    change ((2 : ℝ≥0∞) ^ k)⁻¹ * (∑' coin : Fin (2 ^ inp.prec),
      if some i = (if coin.val < w then some i else none) then ((2 : ℝ≥0∞) ^ inp.prec)⁻¹ else 0) = _
    rw [hcoin, div_eq_mul_inv, ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp))]
    ring
  · intro idx hne
    have hzero : ((PMF.uniformOfFintype (Fin (2 ^ inp.prec))).map fun coin =>
        if h : idx.val < 2 * R + 1 then
          let j : Fin (2 * R + 1) := ⟨idx.val, h⟩
          if coin.val < sampleZWeightNum inp (finToInt (ratFloor inp.center) R j) then some j
          else none
        else none) (some i) = 0 := by
      rw [PMF.map_apply]
      refine tsum_eq_zero_iff.mpr fun coin => ?_
      by_cases hlt : idx.val < 2 * R + 1
      · simp only [hlt, ↓reduceDIte]
        by_cases hc : coin.val <
            sampleZWeightNum inp (finToInt (ratFloor inp.center) R ⟨idx.val, hlt⟩)
        · simp only [hc, ↓reduceIte, Option.some.injEq, Fin.ext_iff]
          have hne_val : i.val ≠ idx.val := fun h => hne (Fin.ext h.symm)
          simp [hne_val]
        · simp [hc]
      · simp [hlt]
    rw [hzero, mul_zero]

/-- Elementary `dist` bound between two finite normalized PMFs from unnormalized weights. -/
private theorem dist_normalize_fin_le {n : ℕ} {u v : Fin n → ℝ}
    (hu : ∀ i, 0 ≤ u i)
    (hU : 0 < ∑ i, u i) (hV : 0 < ∑ i, v i)
    (pu pv : PMF (Fin n))
    (hpu : ∀ i, (pu i).toReal = u i / ∑ j, u j)
    (hpv : ∀ i, (pv i).toReal = v i / ∑ j, v j) :
    dist pu pv ≤ (∑ i, |u i - v i|) / ∑ i, v i := by
  set U := ∑ i, u i
  set V := ∑ i, v i
  rw [PMF.dist_eq]
  have hterm (i : Fin n) :
      |(pu i).toReal - (pv i).toReal| ≤ |u i - v i| / V + (u i / U) * (|V - U| / V) := by
    rw [hpu i, hpv i]
    have hsplit : u i / U - v i / V = (u i - v i) / V + (u i / U) * ((V - U) / V) := by
      have hU0 : U ≠ 0 := hU.ne'
      have hV0 : V ≠ 0 := hV.ne'
      field_simp; ring
    rw [hsplit]
    calc
      |(u i - v i) / V + (u i / U) * ((V - U) / V)| ≤
          |(u i - v i) / V| + |(u i / U) * ((V - U) / V)| := abs_add_le _ _
      _ = |u i - v i| / V + (u i / U) * (|V - U| / V) := by
          rw [abs_div, abs_mul, abs_div, abs_div, abs_of_pos hV, abs_of_nonneg (hu i),
            abs_of_pos hU]
  have hsum_le : ∑ i, |(pu i).toReal - (pv i).toReal| ≤
      (∑ i, |u i - v i|) / V + |V - U| / V := by
    calc
      ∑ i, |(pu i).toReal - (pv i).toReal| ≤
          ∑ i, (|u i - v i| / V + (u i / U) * (|V - U| / V)) := Finset.sum_le_sum fun i _ => hterm i
      _ = (∑ i, |u i - v i|) / V + ((∑ i, u i) / U) * (|V - U| / V) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, ← Finset.sum_div]
      _ = (∑ i, |u i - v i|) / V + |V - U| / V := by
          rw [div_self hU.ne', one_mul]
  have hVU : |V - U| ≤ ∑ i, |u i - v i| := by
    rw [abs_sub_comm]
    calc
      |U - V| = |∑ i, (u i - v i)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, |u i - v i| := Finset.abs_sum_le_sum_abs _ _
  have hdiv : |V - U| / V ≤ (∑ i, |u i - v i|) / V := div_le_div_of_nonneg_right hVU hV.le
  linarith

/-- Truncating any `PMF α` to a subset `S` incurs `CloseTo` error at most `μ.toOuterMeasure Sᶜ`. -/
private theorem closeTo_map_restrict_of_finset {α : Type} (μ : PMF α) (S : Finset α)
    (hS : μ.toOuterMeasure (S : Set α) ≠ 0)
    (μS : PMF S)
    (hμS : ∀ x : S, μS x = μ x.val / μ.toOuterMeasure (S : Set α)) :
    CloseTo (μS.map Subtype.val) μ (μ.toOuterMeasure (S : Set α)ᶜ) := by
  classical
  refine CloseTo.symm fun E => ?_
  set p := μ.toOuterMeasure (S : Set α)
  have hp1 : p ≤ 1 := PMF.toOuterMeasure_le_one μ _
  have hcompl : μ.toOuterMeasure E ≤
      μ.toOuterMeasure (E ∩ (S : Set α)) + μ.toOuterMeasure (S : Set α)ᶜ := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
    refine tsum_le_tsum fun x => ?_
    by_cases hxS : x ∈ (S : Set α)
    · by_cases hxE : x ∈ E
      · simp [hxE, hxS]
      · simp [hxE, hxS]
    · by_cases hxE : x ∈ E
      · simp [hxE, hxS]
      · simp [hxE, hxS]
  have hle_map : μ.toOuterMeasure (E ∩ (S : Set α)) ≤ (μS.map Subtype.val).toOuterMeasure E := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ E ∩ (S : Set α)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx.1]
      rw [PMF.map_apply, tsum_eq_single ⟨x, hx.2⟩]
      · simp only [↓reduceIte, hμS]
        exact ENNReal.le_div_iff_mul_le (Or.inl hS) (Or.inl (PMF.toOuterMeasure_ne_top μ _)) |>.mpr
          (mul_le_of_le_one_right zero_le hp1)
      · intro y hy
        have hne : x ≠ y.val := fun h => hy (Subtype.ext h.symm)
        simp [hne]
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  exact hcompl.trans (add_le_add hle_map le_rfl)

/-- Explicit `CloseTo` bound for `sampleZ` against `discreteGaussianInt` under the 1-D dual-mass
premise `ρ_{1/s}(ℤ* \ {0}) ≤ ε ≤ 1 / 2` ([GentryPeikertVaikuntanathan2008], §4.1, Lemma 4.3,
p. 15, capped-trial strict-PPT variant). -/
theorem closeTo_eval_sampleZ_discreteGaussian
    (inp : SampleZInput) (hsSq : 0 < inp.sSq) (hs1 : 1 ≤ Real.sqrt (inp.sSq : ℝ))
    (ht : 1 ≤ inp.tail) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hdual : ZLattice.gaussianMass
      (LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal)
      (1 / Real.sqrt (inp.sSq : ℝ)) 0 - 1 ≤ ε)
    (hprec : 8 * (2 * inp.tail + 6) ≤ 2 ^ inp.prec) :
    CloseTo (ProbComp.eval (sampleZ inp))
      (discreteGaussianInt (Real.sqrt (inp.sSq : ℝ)) (by positivity) (inp.center : ℝ))
      (ENNReal.ofReal
        ((1 - 1 / (16 * (2 * inp.tail + 6 : ℝ))) ^ inp.maxTrials
          + (8 * inp.tail + 24 : ℝ) / (2 : ℝ) ^ inp.prec
          + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2)))) := by
  set s : ℝ := Real.sqrt (inp.sSq : ℝ)
  have hs : 0 < s := by positivity
  set c : ℝ := (inp.center : ℝ)
  set cF : ℤ := ratFloor inp.center
  set R : ℕ := sampleZRadius inp
  set k : ℕ := Nat.clog 2 (2 * R + 1)
  set μ : PMF ℤ := discreteGaussianInt s hs c
  set tailErr : ℝ := (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2))
  have htail := ZLattice.discreteGaussian_real_abs_sub_ge_le_of_dual_mass_le intLatticeReal
    s hs c (Nat.cast_nonneg inp.tail) ε (by linarith) hdual
  have htailErr0 : 0 ≤ tailErr := by
    dsimp only [tailErr]
    have : 0 < 1 - ε := by linarith
    positivity
  -- 1. Support finset `S = image (finToInt cF R) univ` contains `{x | |x - c| < t * s}`.
  let S : Finset ℤ := Finset.univ.image (finToInt cF R)
  have hfloor : (cF : ℝ) ≤ c ∧ c < (cF : ℝ) + 1 := by
    dsimp only [cF, c]
    rw [ratFloor_eq_intFloor]
    exact ⟨by exact_mod_cast Int.floor_le inp.center,
      by exact_mod_cast Int.lt_floor_add_one inp.center⟩
  have hnotS_tail : ∀ x : ℤ, x ∉ (S : Set ℤ) → (inp.tail : ℝ) * s ≤ |(x : ℝ) - c| := by
    intro x hx
    by_contra hlt
    push Not at hlt
    have hR := lt_sampleZRadius_sub_one inp hsSq
    have hlow : cF - (R : ℤ) ≤ x := by
      have h1 : ((cF - (R : ℤ) - 1 : ℤ) : ℝ) < (x : ℝ) := by
        push_cast; linarith [(abs_lt.mp hlt).1]
      have h2 : cF - (R : ℤ) - 1 < x := by exact_mod_cast h1
      omega
    have hhigh : x ≤ cF + (R : ℤ) := by
      have h1 : (x : ℝ) < ((cF + (R : ℤ) + 1 : ℤ) : ℝ) := by
        push_cast; linarith [(abs_lt.mp hlt).2]
      have h2 : x < cF + (R : ℤ) + 1 := by exact_mod_cast h1
      omega
    have hmem : x ∈ S := by
      refine Finset.mem_image.mpr
        ⟨⟨(x - (cF - (R : ℤ))).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp only [finToInt]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    exact hx hmem
  have hcompl_le : μ.toOuterMeasure (S : Set ℤ)ᶜ ≤ ENNReal.ofReal tailErr := by
    have hpre : intLatticeEquiv.symm ⁻¹' (S : Set ℤ)ᶜ ⊆
        {z : intLatticeReal | (inp.tail : ℝ) * s ≤ |(z : ℝ) - c|} := by
      intro z hz
      have hnot : intLatticeEquiv.symm z ∉ (S : Set ℤ) := hz
      have hval := hnotS_tail (intLatticeEquiv.symm z) hnot
      have hcast : ((intLatticeEquiv.symm z : ℤ) : ℝ) = (z : ℝ) := by
        have := intLatticeEquiv.apply_symm_apply z
        exact congrArg Subtype.val this
      rwa [hcast] at hval
    have hmap : μ.toOuterMeasure (S : Set ℤ)ᶜ =
        (ZLattice.discreteGaussian intLatticeReal s hs c).toOuterMeasure
          (intLatticeEquiv.symm ⁻¹' (S : Set ℤ)ᶜ) := by
      unfold μ discreteGaussianInt
      exact PMF.toOuterMeasure_map_apply _ _ _
    rw [hmap]
    exact ((ZLattice.discreteGaussian intLatticeReal s hs c).toOuterMeasure.mono hpre).trans htail
  -- 2. Total mass `gaussianMass intLatticeReal s c ≥ s / 2` and truncated mass `V ≥ s / 4`.
  have hcov :
      ZLattice.covolume intLatticeReal (MeasureTheory.volume : MeasureTheory.Measure ℝ) = 1 := by
    have hF := ZSpan.isAddFundamentalDomain (Basis.singleton Unit ℝ)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)
    rw [ZLattice.covolume_eq_measure_fundamentalDomain intLatticeReal MeasureTheory.volume hF]
    have hdom : ZSpan.fundamentalDomain (Basis.singleton Unit ℝ) = Set.Ico (0 : ℝ) 1 := by
      ext x
      simp [ZSpan.fundamentalDomain]
    rw [hdom, MeasureTheory.measureReal_def, Real.volume_Ico]
    simp
  have hmass_ge : s / 2 ≤ ZLattice.gaussianMass intLatticeReal s c := by
    have hIcc := (ZLattice.gaussianMass_mem_Icc_of_dual_mass_le intLatticeReal s hs ε hdual c).1
    rw [Module.finrank_self, pow_one, hcov, div_one] at hIcc
    nlinarith
  have htailErr_le_half : tailErr ≤ 1 / 2 := by
    dsimp only [tailErr]
    have ht1 : (1 : ℝ) ≤ (inp.tail : ℝ) := by exact_mod_cast ht
    have hpi : Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2) ≤ 1 / 16 := by
      have h1 : -Real.pi * (inp.tail : ℝ) ^ 2 ≤ -3 := by nlinarith [Real.pi_gt_three]
      have h2 : Real.exp (-3) ≤ 1 / 16 := by
        have hlog : 4 * Real.log 2 < 3 := by linarith [Real.log_two_lt_d9]
        have hlt : Real.exp (-3) < Real.exp (-4 * Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
        have hval : Real.exp (-4 * Real.log 2) = 1 / 16 := by
          rw [show (-4 : ℝ) * Real.log 2 = -((4 : ℕ) * Real.log 2) by norm_num, Real.exp_neg,
            Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          norm_num
        linarith
      exact (Real.exp_le_exp.mpr h1).trans h2
    have hrat : (1 + ε) / (1 - ε) ≤ 3 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hrat0 : 0 ≤ (1 + ε) / (1 - ε) := by
      have : 0 < 1 - ε := by linarith
      positivity
    calc
      (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2)) ≤
          3 * (2 * (1 / 16)) := mul_le_mul hrat (by linarith) (by positivity) (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  -- Unnormalized weights `v i = ρ_s(x_i - c)` and `u i = w_i / 2^prec`
  let v : Fin (2 * R + 1) → ℝ := fun i => gaussianWeight s ((finToInt cF R i : ℝ) - c)
  let u : Fin (2 * R + 1) → ℝ := fun i =>
    (sampleZWeightNum inp (finToInt cF R i) : ℝ) / (2 : ℝ) ^ inp.prec
  set V : ℝ := ∑ i, v i
  set U : ℝ := ∑ i, u i
  have hS_mass_eq : μ.toOuterMeasure (S : Set ℤ) =
      ENNReal.ofReal V / ENNReal.ofReal (ZLattice.gaussianMass intLatticeReal s c) := by
    rw [PMF.toOuterMeasure_apply,
      tsum_eq_sum (s := S) (fun x hx => Set.indicator_of_notMem hx μ)]
    have hsum1 : ∑ x ∈ S, (S : Set ℤ).indicator μ x = ∑ x ∈ S, μ x :=
      Finset.sum_congr rfl fun x hx => Set.indicator_of_mem hx μ
    rw [hsum1, Finset.sum_image (fun a _ b _ h => finToInt_injective cF R h)]
    simp_rw [μ, discreteGaussianInt_apply]
    rw [← ENNReal.sum_div, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => (gaussianWeight_pos _ _).le)]
  have hS_ge_half : (1 / 2 : ℝ) ≤ (μ.toOuterMeasure (S : Set ℤ)).toReal := by
    have hadd := PMF.toOuterMeasure_add_compl_ennreal μ (S : Set ℤ)
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcompl_le
    rw [ENNReal.toReal_ofReal htailErr0] at h1
    have h2 :
        (μ.toOuterMeasure (S : Set ℤ)).toReal + (μ.toOuterMeasure (S : Set ℤ)ᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add (PMF.toOuterMeasure_ne_top μ _) (PMF.toOuterMeasure_ne_top μ _),
        hadd, ENNReal.toReal_one]
    linarith
  have hV_ge : s / 4 ≤ V := by
    have hm_pos := ZLattice.gaussianMass_pos intLatticeReal s hs c
    have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ => (gaussianWeight_pos _ _).le
    have htoReal :
        (μ.toOuterMeasure (S : Set ℤ)).toReal = V / ZLattice.gaussianMass intLatticeReal s c := by
      rw [hS_mass_eq, ENNReal.toReal_div, ENNReal.toReal_ofReal hV0,
        ENNReal.toReal_ofReal hm_pos.le]
    rw [htoReal, le_div_iff₀ hm_pos] at hS_ge_half
    nlinarith
  have hV_pos : 0 < V := by linarith
  have hS_ne_zero : μ.toOuterMeasure (S : Set ℤ) ≠ 0 := by
    rw [hS_mass_eq]
    exact (ENNReal.div_pos (ENNReal.ofReal_pos.mpr hV_pos).ne' ENNReal.ofReal_ne_top).ne'
  -- Bound `∑ |u i - v i|` and `U ≥ s / 8`
  have hdiff_i (i : Fin (2 * R + 1)) : |u i - v i| ≤ 1 / (2 : ℝ) ^ inp.prec := by
    have h := abs_sampleZWeightNum_div_sub_gaussianWeight_le inp hsSq hs1 i
    rw [zpow_neg, zpow_natCast, ← one_div] at h
    exact h
  have hsum_diff : ∑ i, |u i - v i| ≤ (2 * (inp.tail : ℝ) + 6) * s / (2 : ℝ) ^ inp.prec := by
    calc
      ∑ i : Fin (2 * R + 1), |u i - v i| ≤
          ∑ _i : Fin (2 * R + 1), (1 / (2 : ℝ) ^ inp.prec) :=
        Finset.sum_le_sum fun i _ => hdiff_i i
      _ = ((2 * R + 1 : ℕ) : ℝ) / (2 : ℝ) ^ inp.prec := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      _ ≤ (2 * (inp.tail : ℝ) + 6) * s / (2 : ℝ) ^ inp.prec :=
          div_le_div_of_nonneg_right (two_mul_sampleZRadius_add_one_le inp hsSq hs1) (by positivity)
  have hU_ge : s / 8 ≤ U := by
    have hprec_r : 8 * (2 * (inp.tail : ℝ) + 6) ≤ (2 : ℝ) ^ inp.prec := by exact_mod_cast hprec
    have hdiff_le : (2 * (inp.tail : ℝ) + 6) * s / (2 : ℝ) ^ inp.prec ≤ s / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hsub : V - U ≤ ∑ i, |u i - v i| := by
      calc
        V - U = ∑ i, (v i - u i) := (Finset.sum_sub_distrib _ _).symm
        _ ≤ ∑ i, |u i - v i| := Finset.sum_le_sum fun i _ => by
            rw [abs_sub_comm]; exact le_abs_self _
    linarith
  have hU_pos : 0 < U := by linarith
  let pApprox : PMF (Fin (2 * R + 1)) :=
    PMF.ofFintype (fun i => ENNReal.ofReal (u i) / ENNReal.ofReal U) (by
      rw [← ENNReal.sum_div,
        ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by dsimp only [u]; positivity),
        ENNReal.div_self (ENNReal.ofReal_pos.mpr hU_pos).ne' ENNReal.ofReal_ne_top])
  let pTrunc : PMF (Fin (2 * R + 1)) :=
    PMF.ofFintype (fun i => ENNReal.ofReal (v i) / ENNReal.ofReal V) (by
      rw [← ENNReal.sum_div,
        ← ENNReal.ofReal_sum_of_nonneg (fun i _ => (gaussianWeight_pos _ _).le),
        ENNReal.div_self (ENNReal.ofReal_pos.mpr hV_pos).ne' ENNReal.ofReal_ne_top])
  -- 3. Step 1 (Timeout): `runCapped` vs `pApprox`
  have haccept_eq : (sampleZFinSpec inp).acceptProb = ENNReal.ofReal (U / (2 : ℝ) ^ k) := by
    have hsum_some : (∑' i : Fin (2 * R + 1), (sampleZFinSpec inp).singleLaw (some i)) =
        ENNReal.ofReal (U / (2 : ℝ) ^ k) := by
      rw [tsum_fintype]
      simp_rw [sampleZFinSpec_singleLaw_some]
      rw [← ENNReal.sum_div]
      have hnum_eq : (∑ i : Fin (2 * R + 1),
            (sampleZWeightNum inp (finToInt cF R i) : ℝ≥0∞)) =
          ENNReal.ofReal (U * (2 : ℝ) ^ inp.prec) := by
        rw [Finset.sum_mul]
        have hterm (i : Fin (2 * R + 1)) : u i * (2 : ℝ) ^ inp.prec =
            (sampleZWeightNum inp (finToInt cF R i) : ℝ) := by
          dsimp only [u]; field_simp
        simp_rw [hterm]
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Nat.cast_nonneg _)]
        exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_natCast _).symm
      rw [hnum_eq, ENNReal.ofReal_div_of_pos (by positivity)]
      have hden : (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞) ^ inp.prec =
          ENNReal.ofReal ((2 : ℝ) ^ k) * ENNReal.ofReal ((2 : ℝ) ^ inp.prec) := by
        simp [ENNReal.ofReal_pow]
      rw [hden, ENNReal.ofReal_mul hU_pos.le,
        ENNReal.mul_div_mul_right _ _ (ENNReal.ofReal_pos.mpr (by positivity)).ne'
          ENNReal.ofReal_ne_top]
    have htsum := (sampleZFinSpec inp).singleLaw.tsum_coe
    rw [tsum_option_eq] at htsum
    have hrej : (sampleZFinSpec inp).rejectProb = (sampleZFinSpec inp).singleLaw none := rfl
    rw [← hrej, hsum_some] at htsum
    rw [BlockRejectionSpec.acceptProb]
    exact ENNReal.sub_eq_of_eq_add_rev (PMF.apply_ne_top _ _) htsum.symm
  have hsingle_factor (i : Fin (2 * R + 1)) :
      (sampleZFinSpec inp).singleLaw (some i) = (sampleZFinSpec inp).acceptProb * pApprox i := by
    rw [sampleZFinSpec_singleLaw_some, haccept_eq]
    change _ = ENNReal.ofReal (U / (2 : ℝ) ^ k) * (ENNReal.ofReal (u i) / ENNReal.ofReal U)
    have hU0 : ENNReal.ofReal U ≠ 0 := (ENNReal.ofReal_pos.mpr hU_pos).ne'
    have h2k : ENNReal.ofReal ((2 : ℝ) ^ k) = (2 : ℝ≥0∞) ^ k := by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    have hnum : ENNReal.ofReal (u i) =
        (sampleZWeightNum inp (finToInt cF R i) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ inp.prec := by
      dsimp only [u]
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    rw [ENNReal.ofReal_div_of_pos (by positivity), h2k, hnum]
    have hcancel :
        ENNReal.ofReal U / (2 : ℝ≥0∞) ^ k *
          (((sampleZWeightNum inp (finToInt cF R i) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ inp.prec) /
            ENNReal.ofReal U) =
        ((sampleZWeightNum inp (finToInt cF R i) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ inp.prec) /
          (2 : ℝ≥0∞) ^ k := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (ENNReal.ofReal U), mul_assoc,
        ← mul_assoc (ENNReal.ofReal U), mul_comm (ENNReal.ofReal U),
        mul_assoc (_ / _), ENNReal.mul_inv_cancel hU0 ENNReal.ofReal_ne_top,
        mul_one, mul_comm, ← div_eq_mul_inv]
    rw [hcancel, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
      ← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)),
      mul_comm ((2 : ℝ≥0∞) ^ inp.prec)]
  have h2k_lt : (2 : ℝ) ^ k < 2 * (2 * (inp.tail : ℝ) + 6) * s := by
    have hR1 : 1 < 2 * R + 1 := by have := sampleZRadius_ge_two inp; omega
    have hclog_lt : 2 ^ k < 2 * (2 * R + 1) := by
      have h1 : k = (k - 1) + 1 := by
        have : 0 < k := Nat.clog_pos (by omega) hR1
        omega
      have h2 : 2 ^ (k - 1) < 2 * R + 1 := Nat.pow_pred_clog_lt_self (by omega) hR1
      rw [h1, pow_succ]
      omega
    have hclog_r : (2 : ℝ) ^ k < 2 * ((2 * R + 1 : ℕ) : ℝ) := by exact_mod_cast hclog_lt
    have h2R := two_mul_sampleZRadius_add_one_le inp hsSq hs1
    linarith
  have haccept_ge : 1 / (16 * (2 * (inp.tail : ℝ) + 6)) ≤ U / (2 : ℝ) ^ k := by
    have h1 :
        1 / (16 * (2 * (inp.tail : ℝ) + 6)) = (s / 8) / (2 * (2 * (inp.tail : ℝ) + 6) * s) := by
      have hs0 : s ≠ 0 := hs.ne'
      have ht0 : 2 * (inp.tail : ℝ) + 6 ≠ 0 := by positivity
      field_simp; ring
    rw [h1]
    exact div_le_div₀ (by positivity) hU_ge (by positivity) h2k_lt.le
  have hrej_le : ((sampleZFinSpec inp).rejectProb ^ inp.maxTrials).toReal ≤
      (1 - 1 / (16 * (2 * (inp.tail : ℝ) + 6))) ^ inp.maxTrials := by
    have hacc_le1 : U / (2 : ℝ) ^ k ≤ 1 := by
      have : (sampleZFinSpec inp).acceptProb ≤ 1 := tsub_le_self
      rw [haccept_eq] at this
      exact (ENNReal.ofReal_le_one).mp this
    have hrej_eq : (sampleZFinSpec inp).rejectProb = ENNReal.ofReal (1 - U / (2 : ℝ) ^ k) := by
      have hadd := (sampleZFinSpec inp).acceptProb_add_rejectProb
      rw [haccept_eq] at hadd
      have hsub := ENNReal.sub_eq_of_eq_add_rev ENNReal.ofReal_ne_top hadd.symm
      rw [← hsub, ← ENNReal.ofReal_one, ENNReal.ofReal_sub _ (by positivity)]
    rw [hrej_eq, ← ENNReal.ofReal_pow (by linarith), ENNReal.toReal_ofReal (by positivity)]
    exact pow_le_pow_left₀ (by linarith) (by linarith) inp.maxTrials
  have hstep1 : CloseTo ((sampleZFinSpec inp).runCapped ⟨R, by omega⟩ inp.maxTrials) pApprox
      (ENNReal.ofReal ((1 - 1 / (16 * (2 * (inp.tail : ℝ) + 6))) ^ inp.maxTrials)) :=
    closeTo_of_dist_le_ofReal
      ((BlockRejectionSpec.dist_runCapped_le hsingle_factor ⟨R, by omega⟩ inp.maxTrials).trans
        hrej_le)
  -- 4. Step 2 (Approximation): `pApprox` vs `pTrunc`
  have hstep2 : CloseTo pApprox pTrunc
      (ENNReal.ofReal ((8 * (inp.tail : ℝ) + 24) / (2 : ℝ) ^ inp.prec)) := by
    apply closeTo_of_dist_le_ofReal
    have hd := dist_normalize_fin_le
      (u := u) (v := v) (fun i => by dsimp only [u]; positivity)
      hU_pos hV_pos pApprox pTrunc
      (fun i => by
        change (ENNReal.ofReal (u i) / ENNReal.ofReal U).toReal = u i / U
        rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by dsimp only [u]; positivity),
          ENNReal.toReal_ofReal hU_pos.le])
      (fun i => by
        change (ENNReal.ofReal (v i) / ENNReal.ofReal V).toReal = v i / V
        rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (gaussianWeight_pos _ _).le,
          ENNReal.toReal_ofReal hV_pos.le])
    refine hd.trans ?_
    calc
      (∑ i, |u i - v i|) / V ≤
          ((2 * (inp.tail : ℝ) + 6) * s / (2 : ℝ) ^ inp.prec) / (s / 4) :=
        div_le_div₀ (by positivity) hsum_diff (by positivity) hV_ge
      _ = (8 * (inp.tail : ℝ) + 24) / (2 : ℝ) ^ inp.prec := by
        have hs0 : s ≠ 0 := hs.ne'
        field_simp; ring
  -- 5. Step 3 (Truncation): `pTrunc.map (finToInt cF R)` vs `μ`
  have hstep3 : CloseTo (pTrunc.map (finToInt cF R)) μ (ENNReal.ofReal tailErr) := by
    let e : Fin (2 * R + 1) ≃ S :=
      Equiv.ofBijective (fun i => ⟨finToInt cF R i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
        ⟨fun a b h => finToInt_injective cF R (congrArg Subtype.val h),
         fun ⟨x, hx⟩ => by
           obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
           exact ⟨i, Subtype.ext hi⟩⟩
    have hmap_eq : pTrunc.map (finToInt cF R) = (pTrunc.map e).map Subtype.val := by
      rw [PMF.map_comp]; rfl
    rw [hmap_eq]
    refine (closeTo_map_restrict_of_finset μ S hS_ne_zero (pTrunc.map e) fun y => ?_).mono hcompl_le
    rw [PMF.map_apply, tsum_eq_single (e.symm y)]
    · simp only [Equiv.apply_symm_apply, ↓reduceIte]
      change ENNReal.ofReal (v (e.symm y)) / ENNReal.ofReal V =
        μ y.val / μ.toOuterMeasure (S : Set ℤ)
      rw [hS_mass_eq]
      have hy : finToInt cF R (e.symm y) = y.val := congrArg Subtype.val (e.apply_symm_apply y)
      have hv_eq : v (e.symm y) = gaussianWeight s ((y.val : ℝ) - c) := by
        dsimp only [v]; rw [hy]
      rw [hv_eq, discreteGaussianInt_apply]
      have hm0 := (ENNReal.ofReal_pos.mpr (ZLattice.gaussianMass_pos intLatticeReal s hs c)).ne'
      symm
      rw [← ENNReal.mul_div_mul_right _ _ hm0 ENNReal.ofReal_ne_top,
        ENNReal.div_mul_cancel hm0 ENNReal.ofReal_ne_top,
        ENNReal.div_mul_cancel hm0 ENNReal.ofReal_ne_top]
    · intro i hi
      have hne : y ≠ e i := fun h => hi (by rw [h, Equiv.symm_apply_apply])
      simp [hne]
  -- Combine all 3 steps via `CloseTo.map` and `CloseTo.trans`
  rw [eval_sampleZ_eq_map_runCapped]
  have h12 := (hstep1.trans hstep2).map (finToInt cF R)
  have h123 := h12.trans hstep3
  have ht1 : 0 ≤ (1 - 1 / (16 * (2 * (inp.tail : ℝ) + 6))) ^ inp.maxTrials := by
    have : (1 : ℝ) / (16 * (2 * (inp.tail : ℝ) + 6)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) inp.tail]
    exact pow_nonneg (by linarith) _
  have ht2 : 0 ≤ (8 * (inp.tail : ℝ) + 24) / (2 : ℝ) ^ inp.prec := by positivity
  rwa [← ENNReal.ofReal_add ht1 ht2, ← ENNReal.ofReal_add (add_nonneg ht1 ht2) htailErr0] at h123


/-! ### 7. `List.mapM` bridge to `PMF.piFin` -/

private theorem eval_mapM_range {β : Type} :
    ∀ (k : ℕ) (f : ℕ → ProbComp β),
      ProbComp.eval ((List.range k).mapM f) =
        (PMF.piFin fun i : Fin k => ProbComp.eval (f i.val)).map List.ofFn
  | 0, _ => by simp [PMF.piFin]
  | k + 1, f => by
    rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.piFin, PMF.map_bind, PMF.map_comp,
      Function.comp_def]
    congr 1
    funext first
    have ih := eval_mapM_range k (fun n => f (n + 1))
    have hbind : (ProbComp.eval ((List.range k).mapM fun n => f (n + 1))).bind
        (fun tail => PMF.pure (first :: tail)) =
        (ProbComp.eval ((List.range k).mapM fun n => f (n + 1))).map (first :: ·) := rfl
    rw [hbind, ih, PMF.map_comp]
    congr 1
    funext rest
    simp [List.ofFn_succ]

/-! ### 8. Grid Gaussian sampler (`sampleGridGaussian`) & Quotient sampler (`sampleQuotientModS`) -/

open Cslib.LinearAlgebra
open scoped IntTable RatTable LinearSystemInput LinearSolveResult

/-- Convert an `IntTable` to a `RatTable` by casting each entry to `ℚ`. -/
private def intTableToRatTable (B : IntTable) : RatTable :=
  ⟨B.numRows, B.numCols, B.rows.map fun row => row.map (Int.cast : ℤ → ℚ)⟩

private theorem computableInPolyTime_intTableToRatTable :
    ComputableInPolyTime intTableToRatTable IntTable.enc RatTable.enc := by
  have hcast : ComputableInPolyTime (fun p : List ℤ × ℤ => (p.2 : ℚ))
      (encPair (encList encIntBin) encIntBin) encRat :=
    (snd (encList encIntBin) encIntBin).trans rat_intCast
  have hrow : ComputableInPolyTime (fun row : List ℤ => row.map (Int.cast : ℤ → ℚ))
      (encList encIntBin) (encList encRat) :=
    mapWithInput (f := fun _ (z : ℤ) => (z : ℚ)) (id' (encIn := encList encIntBin)) hcast
  have hBrows : ComputableInPolyTime IntTable.rows IntTable.enc (encList (encList encIntBin)) := by
    fun_prop
  have hrows : ComputableInPolyTime
      (fun B : IntTable => B.rows.map fun row => row.map (Int.cast : ℤ → ℚ))
      IntTable.enc (encList (encList encRat)) := by
    have hstep : ComputableInPolyTime (fun p : IntTable × List ℤ => p.2.map (Int.cast : ℤ → ℚ))
        (encPair IntTable.enc (encList encIntBin)) (encList encRat) :=
      (snd IntTable.enc (encList encIntBin)).trans hrow
    exact mapWithInput (f := fun _ (row : List ℤ) => row.map (Int.cast : ℤ → ℚ)) hBrows hstep
  have heq : intTableToRatTable = fun B =>
      RatTable.mk B.numRows B.numCols (B.rows.map fun row => row.map (Int.cast : ℤ → ℚ)) := rfl
  rw [heq]
  fun_prop

/-- Exact integer matrix-vector multiplication `B *ᵥ v` on list representations. -/
private def intTableMulVec (B : IntTable) (v : List ℤ) : List ℤ :=
  (List.range B.numRows).map fun r =>
    ((List.range B.numCols).map fun c => B.entry r c * v.getD c 0).sum

private theorem computableInPolyTime_intTableMulVec :
    ComputableInPolyTime (fun p : IntTable × List ℤ => intTableMulVec p.1 p.2)
      (encPair IntTable.enc (encList encIntBin)) (encList encIntBin) := by
  let encIn := encPair IntTable.enc (encList encIntBin)
  have hrows : ComputableInPolyTime (fun p : IntTable × List ℤ => List.range p.1.numRows)
      encIn (encList encUnary) := by
    have hnr : ComputableInPolyTime (fun p : IntTable × List ℤ => p.1.numRows)
        encIn encUnary := by fun_prop
    exact unary_range' hnr
  have hrowStep : ComputableInPolyTime
      (fun q : (IntTable × List ℤ) × ℕ =>
        ((List.range q.1.1.numCols).map fun c => q.1.1.entry q.2 c * q.1.2.getD c 0).sum)
      (encPair encIn encUnary) encIntBin := by
    let encQ := encPair encIn encUnary
    have hcols : ComputableInPolyTime (fun q : (IntTable × List ℤ) × ℕ => List.range q.1.1.numCols)
        encQ (encList encUnary) := by
      have hnc : ComputableInPolyTime (fun q : (IntTable × List ℤ) × ℕ => q.1.1.numCols)
          encQ encUnary := by fun_prop
      exact unary_range' hnc
    have hterm : ComputableInPolyTime
        (fun t : ((IntTable × List ℤ) × ℕ) × ℕ =>
          Cslib.rowEntry t.1.1.1.rows t.1.2 t.2 * t.1.1.2.getD t.2 0)
        (encPair encQ encUnary) encIntBin := by
      have hrowL : ComputableInPolyTime
          (fun t : ((IntTable × List ℤ) × ℕ) × ℕ => t.1.1.1.rows.getD t.1.2 [])
          (encPair encQ encUnary) (encList encIntBin) := by
        have hr : ComputableInPolyTime
            (fun t : ((IntTable × List ℤ) × ℕ) × ℕ => t.1.1.1.rows)
            (encPair encQ encUnary) (encList (encList encIntBin)) := by fun_prop
        have hi : ComputableInPolyTime
            (fun t : ((IntTable × List ℤ) × ℕ) × ℕ => t.1.2)
            (encPair encQ encUnary) encUnary := by fun_prop
        exact listGetDWithInput hr hi []
      have hentry : ComputableInPolyTime
          (fun t : ((IntTable × List ℤ) × ℕ) × ℕ => (t.1.1.1.rows.getD t.1.2 []).getD t.2 0)
          (encPair encQ encUnary) encIntBin :=
        listGetDWithInput hrowL (snd encQ encUnary) 0
      have hv : ComputableInPolyTime
          (fun t : ((IntTable × List ℤ) × ℕ) × ℕ => t.1.1.2.getD t.2 0)
          (encPair encQ encUnary) encIntBin := by
        have hvl : ComputableInPolyTime
            (fun t : ((IntTable × List ℤ) × ℕ) × ℕ => t.1.1.2)
            (encPair encQ encUnary) (encList encIntBin) := by fun_prop
        exact listGetDWithInput hvl (snd encQ encUnary) 0
      exact intBin_mul' hentry hv
    have hlist :=
      mapWithInput (f := fun q c => Cslib.rowEntry q.1.1.rows q.2 c * q.1.2.getD c 0) hcols hterm
    have heq :
        (fun q : (IntTable × List ℤ) × ℕ =>
          ((List.range q.1.1.numCols).map fun c => q.1.1.entry q.2 c * q.1.2.getD c 0).sum) =
        fun q =>
          ((List.range q.1.1.numCols).map fun c =>
            Cslib.rowEntry q.1.1.rows q.2 c * q.1.2.getD c 0).sum := rfl
    rw [heq]
    exact hlist.trans intBin_sum
  exact mapWithInput hrows hrowStep

/-- Shared polynomial-time helper: solve `mat *ᵥ ξ = rhs`, take componentwise `ratFloor`, and
multiply back by `mat`. -/
private def solveFloorMul (dim : ℕ) (mat : IntTable) (rhs : List ℚ) : List ℤ :=
  let sol := (ratSolve ⟨intTableToRatTable mat, rhs⟩).solution.getD (List.replicate dim 0)
  intTableMulVec mat ((List.range dim).map fun i => ratFloor (sol.getD i 0))

private theorem computableInPolyTime_solveFloorMul {α : Type} {encIn : α ↪ List Bool}
    {dim : α → ℕ} {mat : α → IntTable} {rhs : α → List ℚ}
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hmat : ComputableInPolyTime mat encIn IntTable.enc)
    (hrhs : ComputableInPolyTime rhs encIn (encList encRat)) :
    ComputableInPolyTime (fun a => solveFloorMul (dim a) (mat a) (rhs a))
      encIn (encList encIntBin) := by
  have hmatRat : ComputableInPolyTime (fun a => intTableToRatTable (mat a))
      encIn RatTable.enc := computableInPolyTime_intTableToRatTable.comp hmat
  have hsys : ComputableInPolyTime
      (fun a => LinearSystemInput.mk (intTableToRatTable (mat a)) (rhs a))
      encIn LinearSystemInput.enc := by fun_prop
  have hres := ratSolve_computableInPolyTime.comp hsys
  have hopt : ComputableInPolyTime
      (fun a => (ratSolve ⟨intTableToRatTable (mat a), rhs a⟩).solution)
      encIn (encOption (encList encRat)) := by fun_prop
  have hdef : ComputableInPolyTime (fun a => List.replicate (dim a) (0 : ℚ))
      encIn (encList encRat) := by fun_prop
  have hsol := optionGetDWithInput hopt hdef
  have hrng := unary_range' hdim
  have hk : ComputableInPolyTime
      (fun a => (List.range (dim a)).map fun i =>
        ratFloor (((ratSolve ⟨intTableToRatTable (mat a), rhs a⟩).solution.getD
          (List.replicate (dim a) 0)).getD i 0))
      encIn (encList encIntBin) := by
    refine mapWithInput hrng ?_
    exact computableInPolyTime_ratFloor.comp
      (listGetDWithInput (hsol.comp (fst encIn encUnary)) (snd encIn encUnary) 0)
  have hres := (hmat.prod hk).trans computableInPolyTime_intTableMulVec
  have heq :
      (fun a => solveFloorMul (dim a) (mat a) (rhs a)) =
      fun a => intTableMulVec (mat a)
        ((List.range (dim a)).map fun i =>
          ratFloor (((ratSolve ⟨intTableToRatTable (mat a), rhs a⟩).solution.getD
            (List.replicate (dim a) 0)).getD i 0)) := rfl
  rw [heq]
  exact hres

private theorem computableInPolyTime_gridRhs {α : Type} {encIn : α ↪ List Bool}
    {dim : α → ℕ} {q : α → ℤ} {r' : α → List ℤ}
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hq : ComputableInPolyTime q encIn encIntBin)
    (hr' : ComputableInPolyTime r' encIn (encList encIntBin)) :
    ComputableInPolyTime
      (fun a => (List.range (dim a)).map fun i => Rat.divInt (-((r' a).getD i 0)) (q a))
      encIn (encList encRat) := by
  have hrng := unary_range' hdim
  have hneg := (listGetDWithInput ((fst encIn encUnary).trans hr') (snd encIn encUnary) 0).trans
    intBin_neg
  have hqp := (fst encIn encUnary).trans hq
  exact mapWithInput (f := fun a i => Rat.divInt (-((r' a).getD i 0)) (q a)) hrng
    (rat_divInt' hneg hqp)

private theorem computableInPolyTime_gridPost {α : Type} {encIn : α ↪ List Bool}
    {dim : α → ℕ} {q : α → ℤ} {r' bk : α → List ℤ}
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hq : ComputableInPolyTime q encIn encIntBin)
    (hr' : ComputableInPolyTime r' encIn (encList encIntBin))
    (hbk : ComputableInPolyTime bk encIn (encList encIntBin)) :
    ComputableInPolyTime
      (fun a =>
        ((List.range (dim a)).map fun i => -((r' a).getD i 0) - q a * (bk a).getD i 0,
         (List.range (dim a)).map fun i => -((bk a).getD i 0)))
      encIn (encPair (encList encIntBin) (encList encIntBin)) := by
  have hrng := unary_range' hdim
  have hneg := (listGetDWithInput ((fst encIn encUnary).trans hr') (snd encIn encUnary) 0).trans
    intBin_neg
  have hqp := (fst encIn encUnary).trans hq
  have hbki := listGetDWithInput ((fst encIn encUnary).trans hbk) (snd encIn encUnary) 0
  have hu := mapWithInput
    (f := fun a i => -((r' a).getD i 0) - q a * (bk a).getD i 0)
    hrng (intBin_sub' hneg (intBin_mul' hqp hbki))
  have hy := mapWithInput (f := fun a i => -((bk a).getD i 0)) hrng (hbki.trans intBin_neg)
  exact hu.prod hy

private theorem computableInPolyTime_vecIntToRat {α : Type} {encIn : α ↪ List Bool}
    {dim : α → ℕ} {v : α → List ℤ}
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hv : ComputableInPolyTime v encIn (encList encIntBin)) :
    ComputableInPolyTime
      (fun a => (List.range (dim a)).map fun i => ((v a).getD i 0 : ℚ))
      encIn (encList encRat) := by
  have hvi := listGetDWithInput ((fst encIn encUnary).trans hv) (snd encIn encUnary) 0
  exact mapWithInput (f := fun a i => ((v a).getD i 0 : ℚ)) (unary_range' hdim)
    (hvi.trans rat_intCast)

private theorem computableInPolyTime_vecSub {α : Type} {encIn : α ↪ List Bool}
    {dim : α → ℕ} {u v : α → List ℤ}
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hu : ComputableInPolyTime u encIn (encList encIntBin))
    (hv : ComputableInPolyTime v encIn (encList encIntBin)) :
    ComputableInPolyTime
      (fun a => (List.range (dim a)).map fun i => (u a).getD i 0 - (v a).getD i 0)
      encIn (encList encIntBin) := by
  have hui := listGetDWithInput ((fst encIn encUnary).trans hu) (snd encIn encUnary) 0
  have hvi := listGetDWithInput ((fst encIn encUnary).trans hv) (snd encIn encUnary) 0
  exact mapWithInput (f := fun a i => (u a).getD i 0 - (v a).getD i 0) (unary_range' hdim)
    (intBin_sub' hui hvi)

/-- Input specification for the discrete-grid Gaussian sampler `sampleGridGaussian`
([MicciancioRegev2007], Lemma 5.7, p. 20). -/
structure GridSampleInput where
  /-- Ambient lattice dimension `n`. -/
  dim : ℕ
  /-- Integer grid modulus `q > 0`. -/
  modulus : ℕ
  /-- Basis matrix `B` of the lattice `L(B)` (columns are basis vectors). -/
  basis : IntTable
  /-- Rational squared Gaussian width `s² > 0`. -/
  sSq : ℚ
  /-- Target center `t ∈ ℚ^n`. -/
  target : List ℚ
  /-- Unary tail-cutoff multiplier `t_tail` passed to `sampleZ`. -/
  tail : ℕ
  /-- Unary dyadic acceptance-coin precision `prec` passed to `sampleZ`. -/
  prec : ℕ
  /-- Unary rejection-trial cap `maxTrials` passed to `sampleZ`. -/
  maxTrials : ℕ
  deriving DecidableEq, Repr

namespace GridSampleInput

/-- Framing encoding of `GridSampleInput`. -/
enc_structure enc : GridSampleInput where
  dim : encUnary, modulus : encUnary, basis : IntTable.enc, sSq : encRat,
  target : (encList encRat), tail : encUnary, prec : encUnary, maxTrials : encUnary

end GridSampleInput

open scoped GridSampleInput

/-- Exact integer grid reduction: given `r' ∈ ℤ^dim`, solves `B *ᵥ ξ = -r' / q`, sets
`k = ⌊ξ⌋`, `bk = B *ᵥ k`, and returns `(u, y) = (-r' - q • bk, -bk)`. -/
@[expose] def gridReduceInt (dim q : ℕ) (B : IntTable) (r' : List ℤ) : List ℤ × List ℤ :=
  let rhs : List ℚ := (List.range dim).map fun i => Rat.divInt (-(r'.getD i 0)) (q : ℤ)
  let Brat : RatTable :=
    ⟨B.numRows, B.numCols, B.rows.map fun row => row.map (Int.cast : ℤ → ℚ)⟩
  let sol : List ℚ := (ratSolve ⟨Brat, rhs⟩).solution.getD (List.replicate dim 0)
  let k : List ℤ := (List.range dim).map fun i => (sol.getD i 0).floor
  let bk : List ℤ := (List.range B.numRows).map fun r =>
    ((List.range B.numCols).map fun c => B.entry r c * k.getD c 0).sum
  ((List.range dim).map fun i => -(r'.getD i 0) - (q : ℤ) * bk.getD i 0,
   (List.range dim).map fun i => -(bk.getD i 0))

private def gridReduceRhs (dim q : ℕ) (r' : List ℤ) : List ℚ :=
  (List.range dim).map fun i => Rat.divInt (-(r'.getD i 0)) (q : ℤ)

private theorem gridReduceInt_eq_solveFloorMul (dim q : ℕ) (B : IntTable) (r' : List ℤ) :
    gridReduceInt dim q B r' =
      let bk := solveFloorMul dim B (gridReduceRhs dim q r')
      ((List.range dim).map fun i => -(r'.getD i 0) - (q : ℤ) * bk.getD i 0,
       (List.range dim).map fun i => -(bk.getD i 0)) := by
  simp only [gridReduceInt, solveFloorMul, gridReduceRhs, intTableToRatTable, intTableMulVec,
    ratFloor_eq_ratFloor]

/-- Coordinate `i` 1-D input for `sampleGridGaussian`. -/
private def gridCoordInput (inp : GridSampleInput) (i : ℕ) : SampleZInput :=
  ⟨((inp.modulus : ℚ) ^ 2) * inp.sSq, (inp.modulus : ℚ) * inp.target.getD i 0,
    inp.tail, inp.prec, inp.maxTrials⟩

/-- Strict-PPT discrete-grid Gaussian sampler (`r' ~ D_{ℤ^dim, q*s, q*t}` followed by exact
`gridReduceInt`). -/
noncomputable def sampleGridGaussian (inp : GridSampleInput) : ProbComp (List ℤ × List ℤ) := do
  let r' ← (List.range inp.dim).mapM fun i => sampleZ (gridCoordInput inp i)
  pure (gridReduceInt inp.dim inp.modulus inp.basis r')

private theorem computableInPolyTime_gridReduceInt :
    ComputableInPolyTime
      (fun p : GridSampleInput × List ℤ => gridReduceInt p.1.dim p.1.modulus p.1.basis p.2)
      (encPair GridSampleInput.enc (encList encIntBin))
      (encPair (encList encIntBin) (encList encIntBin)) := by
  let encIn := encPair GridSampleInput.enc (encList encIntBin)
  have hdim : ComputableInPolyTime (fun p : GridSampleInput × List ℤ => p.1.dim)
      encIn encUnary := by fun_prop
  have hmod : ComputableInPolyTime (fun p : GridSampleInput × List ℤ => p.1.modulus)
      encIn encUnary := by fun_prop
  have hB : ComputableInPolyTime (fun p : GridSampleInput × List ℤ => p.1.basis)
      encIn IntTable.enc := by fun_prop
  have hr' : ComputableInPolyTime (fun p : GridSampleInput × List ℤ => p.2)
      encIn (encList encIntBin) := snd GridSampleInput.enc (encList encIntBin)
  have hq : ComputableInPolyTime (fun p : GridSampleInput × List ℤ => (p.1.modulus : ℤ))
      encIn encIntBin := (hmod.trans unary_to_binary).trans intBin_natCast
  have hrhs := computableInPolyTime_gridRhs hdim hq hr'
  have hbk := computableInPolyTime_solveFloorMul hdim hB hrhs
  have hmain := computableInPolyTime_gridPost hdim hq hr' hbk
  have heq :
      (fun p : GridSampleInput × List ℤ => gridReduceInt p.1.dim p.1.modulus p.1.basis p.2) =
      fun p =>
        ((List.range p.1.dim).map fun i =>
            -(p.2.getD i 0) - (p.1.modulus : ℤ) *
              (solveFloorMul p.1.dim p.1.basis
                ((List.range p.1.dim).map fun j =>
                  Rat.divInt (-(p.2.getD j 0)) (p.1.modulus : ℤ))).getD i 0,
         (List.range p.1.dim).map fun i =>
            -((solveFloorMul p.1.dim p.1.basis
                ((List.range p.1.dim).map fun j =>
                  Rat.divInt (-(p.2.getD j 0)) (p.1.modulus : ℤ))).getD i 0)) :=
    funext fun p => gridReduceInt_eq_solveFloorMul _ _ _ _
  rw [heq]
  exact hmain

/-- Strict-PPT certificate for `sampleGridGaussian`. -/
theorem isPPTOn_sampleGridGaussian :
    IsPPTOn GridSampleInput.enc (encPair (encList encIntBin) (encList encIntBin))
      sampleGridGaussian := by
  have hcoord : ComputableInPolyTime (fun p : GridSampleInput × ℕ => gridCoordInput p.1 p.2)
      (encPair GridSampleInput.enc encUnary) SampleZInput.enc := by
    let encP := encPair GridSampleInput.enc encUnary
    have hmod : ComputableInPolyTime (fun p : GridSampleInput × ℕ => p.1.modulus)
        encP encUnary := by fun_prop
    have hsSq : ComputableInPolyTime (fun p : GridSampleInput × ℕ => p.1.sSq)
        encP encRat := by fun_prop
    have htargetList : ComputableInPolyTime (fun p : GridSampleInput × ℕ => p.1.target)
        encP (encList encRat) := by fun_prop
    have hqRat : ComputableInPolyTime (fun p : GridSampleInput × ℕ => (p.1.modulus : ℚ))
        encP encRat :=
      rat_intCast.comp (intBin_natCast.comp (unary_to_binary.comp hmod))
    have hqSq : ComputableInPolyTime (fun p : GridSampleInput × ℕ => (p.1.modulus : ℚ) ^ 2)
        encP encRat := by
      have : (fun p : GridSampleInput × ℕ => (p.1.modulus : ℚ) ^ 2) =
          fun p => (p.1.modulus : ℚ) * (p.1.modulus : ℚ) := by funext p; rw [sq]
      rw [this]
      exact rat_mul' hqRat hqRat
    have hsSq' : ComputableInPolyTime
        (fun p : GridSampleInput × ℕ => (p.1.modulus : ℚ) ^ 2 * p.1.sSq) encP encRat :=
      rat_mul' hqSq hsSq
    have htarget : ComputableInPolyTime
        (fun p : GridSampleInput × ℕ => (p.1.modulus : ℚ) * p.1.target.getD p.2 0) encP encRat :=
      rat_mul' hqRat (listGetDWithInput htargetList (snd GridSampleInput.enc encUnary) 0)
    have htail : ComputableInPolyTime (fun p : GridSampleInput × ℕ => p.1.tail) encP encUnary := by
      fun_prop
    have hprec : ComputableInPolyTime (fun p : GridSampleInput × ℕ => p.1.prec) encP encUnary := by
      fun_prop
    have hmax : ComputableInPolyTime (fun p : GridSampleInput × ℕ => p.1.maxTrials)
        encP encUnary := by fun_prop
    exact SampleZInput.enc_mk_polyTime hsSq' htarget htail hprec hmax
  have hdim : ComputableInPolyTime GridSampleInput.dim GridSampleInput.enc encUnary := by fun_prop
  have htrav : IsPPTOn GridSampleInput.enc (encList encIntBin)
      (fun inp => (List.range inp.dim).mapM fun i => sampleZ (gridCoordInput inp i)) :=
    IsPPTOn.mapMWith (isPPTOn_sampleZ.preprocess hcoord) (unary_range' hdim)
  have hres := htrav.map_with
    (f := fun inp r' => gridReduceInt inp.dim inp.modulus inp.basis r')
    computableInPolyTime_gridReduceInt
  refine hres.congr fun inp => ?_
  simp only [sampleGridGaussian, bind_pure_comp]

/-- `CloseTo` bound for `sampleGridGaussian` against `PMF.piFin` of 1-D discrete Gaussians at
width `q * √sSq` and centers `q * t_i`, pushed forward by `gridReduceInt`. -/
theorem closeTo_eval_sampleGridGaussian_pi
    (inp : GridSampleInput) (hsSq : 0 < inp.sSq) (hq : 0 < inp.modulus)
    (hqs1 : 1 ≤ (inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ)) (ht : 1 ≤ inp.tail)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hdual : ZLattice.gaussianMass
      (LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal)
      (1 / ((inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ))) 0 - 1 ≤ ε)
    (hprec : 8 * (2 * inp.tail + 6) ≤ 2 ^ inp.prec) :
    CloseTo (ProbComp.eval (sampleGridGaussian inp))
      ((PMF.piFin fun i : Fin inp.dim =>
          discreteGaussianInt ((inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ))
            (by positivity) ((inp.modulus : ℝ) * (inp.target.getD i.val 0 : ℝ))).map
        fun r => gridReduceInt inp.dim inp.modulus inp.basis (List.ofFn r))
      (ENNReal.ofReal ((inp.dim : ℝ) *
        ((1 - 1 / (16 * (2 * inp.tail + 6 : ℝ))) ^ inp.maxTrials
          + (8 * inp.tail + 24 : ℝ) / (2 : ℝ) ^ inp.prec
          + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2))))) := by
  set s := Real.sqrt (inp.sSq : ℝ)
  set qs := (inp.modulus : ℝ) * s
  have hqs_pos : 0 < qs := by positivity
  set Δ := (1 - 1 / (16 * (2 * (inp.tail : ℝ) + 6))) ^ inp.maxTrials
      + (8 * (inp.tail : ℝ) + 24) / (2 : ℝ) ^ inp.prec
      + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2))
  have hcoord (i : Fin inp.dim) :
      CloseTo (ProbComp.eval (sampleZ (gridCoordInput inp i.val)))
        (discreteGaussianInt qs hqs_pos
          ((inp.modulus : ℝ) * (inp.target.getD i.val 0 : ℝ)))
        (ENNReal.ofReal Δ) := by
    have hq_pos_q : (0 : ℚ) < (inp.modulus : ℚ) := by exact_mod_cast hq
    have hsSq' : 0 < (gridCoordInput inp i.val).sSq := by
      dsimp only [gridCoordInput]
      exact mul_pos (sq_pos_of_pos hq_pos_q) hsSq
    have hsqrt_eq : Real.sqrt (((gridCoordInput inp i.val).sSq : ℚ) : ℝ) = qs := by
      dsimp only [gridCoordInput, qs, s]
      push_cast
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
    have hcenter_eq : ((gridCoordInput inp i.val).center : ℝ) =
        (inp.modulus : ℝ) * (inp.target.getD i.val 0 : ℝ) := by
      dsimp only [gridCoordInput]; push_cast; rfl
    have h := closeTo_eval_sampleZ_discreteGaussian (gridCoordInput inp i.val) hsSq'
      (by rwa [hsqrt_eq]) ht hε0 hε (by rwa [hsqrt_eq]) hprec
    have hdgInt_eq :
        discreteGaussianInt (Real.sqrt (((gridCoordInput inp i.val).sSq : ℚ) : ℝ))
          (by positivity) ((gridCoordInput inp i.val).center : ℝ) =
        discreteGaussianInt qs hqs_pos
          ((inp.modulus : ℝ) * (inp.target.getD i.val 0 : ℝ)) := by
      congr 1
    rw [hdgInt_eq] at h
    exact h
  have hpi := CloseTo.piFin hcoord
  have hmul_eq : (inp.dim : ℝ≥0∞) * ENNReal.ofReal Δ = ENNReal.ofReal ((inp.dim : ℝ) * Δ) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hmul_eq] at hpi
  have heval : ProbComp.eval (sampleGridGaussian inp) =
      (PMF.piFin fun i : Fin inp.dim =>
        ProbComp.eval (sampleZ (gridCoordInput inp i.val))).map
        fun r => gridReduceInt inp.dim inp.modulus inp.basis (List.ofFn r) := by
    unfold sampleGridGaussian
    rw [bind_pure_comp, ProbComp.eval_map, eval_mapM_range, PMF.map_comp]
    rfl
  rw [heval]
  exact hpi.map _

/-- Input specification for the HNF-free quotient sampler `sampleQuotientModS`. -/
structure QuotientSampleInput where
  /-- Ambient lattice dimension `n`. -/
  dim : ℕ
  /-- Basis matrix `B` of the outer lattice `L(B)`. -/
  basis : IntTable
  /-- Basis matrix `S` of the sublattice `L(S) ⊆ L(B)`. -/
  sublattice : IntTable
  /-- Extra random bits per coordinate above `Nat.clog 2 D`. -/
  extraBits : ℕ
  deriving DecidableEq, Repr

namespace QuotientSampleInput

/-- Framing encoding of `QuotientSampleInput`. -/
enc_structure enc : QuotientSampleInput where
  dim : encUnary, basis : IntTable.enc, sublattice : IntTable.enc, extraBits : encUnary

end QuotientSampleInput

open scoped QuotientSampleInput

/-- Integer quotient index `D = |det S| / |det B|` computed via staged Bird determinants. -/
@[expose] def quotientIndex (B S : IntTable) : ℕ :=
  (Cslib.Circuits.Rational.detRows S.rows).natAbs /
    (Cslib.Circuits.Rational.detRows B.rows).natAbs

private theorem computableInPolyTime_quotientIndex :
    ComputableInPolyTime (fun p : IntTable × IntTable => quotientIndex p.1 p.2)
      (encPair IntTable.enc IntTable.enc) encNat := by
  unfold quotientIndex
  have hSrows : ComputableInPolyTime (fun p : IntTable × IntTable => p.2.rows)
      (encPair IntTable.enc IntTable.enc) Cslib.encIntTable := by
    change ComputableInPolyTime (fun p : IntTable × IntTable => p.2.rows)
      (encPair IntTable.enc IntTable.enc) (encList (encList encIntBin))
    fun_prop
  have hBrows : ComputableInPolyTime (fun p : IntTable × IntTable => p.1.rows)
      (encPair IntTable.enc IntTable.enc) Cslib.encIntTable := by
    change ComputableInPolyTime (fun p : IntTable × IntTable => p.1.rows)
      (encPair IntTable.enc IntTable.enc) (encList (encList encIntBin))
    fun_prop
  have hS := intBin_natAbs.comp (Cslib.Circuits.Rational.detRows_polytime.comp hSrows)
  have hB := intBin_natAbs.comp (Cslib.Circuits.Rational.detRows_polytime.comp hBrows)
  exact binary_div' hS hB

/-- Exact integer quotient representative reduction: given `x ∈ ℕ^dim`, computes `v₀ = B *ᵥ x`,
solves `S *ᵥ ξ = v₀`, sets `k = ⌊ξ⌋`, and returns `v₀ - S *ᵥ k`. -/
@[expose] def quotientReduceInt (dim : ℕ) (B S : IntTable) (x : List ℕ) : List ℤ :=
  let v0 : List ℤ := (List.range B.numRows).map fun r =>
    ((List.range B.numCols).map fun c => B.entry r c * (x.getD c 0 : ℤ)).sum
  let rhs : List ℚ := (List.range dim).map fun i => (v0.getD i 0 : ℚ)
  let Srat : RatTable :=
    ⟨S.numRows, S.numCols, S.rows.map fun row => row.map (Int.cast : ℤ → ℚ)⟩
  let sol : List ℚ := (ratSolve ⟨Srat, rhs⟩).solution.getD (List.replicate dim 0)
  let k : List ℤ := (List.range dim).map fun i => (sol.getD i 0).floor
  let sk : List ℤ := (List.range S.numRows).map fun r =>
    ((List.range S.numCols).map fun c => S.entry r c * k.getD c 0).sum
  (List.range dim).map fun i => v0.getD i 0 - sk.getD i 0

private def quotientReduceV0 (B : IntTable) (x : List ℕ) : List ℤ :=
  intTableMulVec B (x.map (Nat.cast : ℕ → ℤ))

private def quotientReduceRhs (dim : ℕ) (B : IntTable) (x : List ℕ) : List ℚ :=
  let v0 := quotientReduceV0 B x
  (List.range dim).map fun i => (v0.getD i 0 : ℚ)

private theorem quotientReduceInt_eq_solveFloorMul (dim : ℕ) (B S : IntTable) (x : List ℕ) :
    quotientReduceInt dim B S x =
      let v0 := quotientReduceV0 B x
      let sk := solveFloorMul dim S (quotientReduceRhs dim B x)
      (List.range dim).map fun i => v0.getD i 0 - sk.getD i 0 := by
  have hv0 :
      ((List.range B.numRows).map fun r =>
        ((List.range B.numCols).map fun c => B.entry r c * (x.getD c 0 : ℤ)).sum) =
      quotientReduceV0 B x := by
    simp only [quotientReduceV0, intTableMulVec]
    congr 1
    funext r
    congr 1
    congr 1
    funext c
    by_cases hc : c < x.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hc,
        Option.map_some, Option.getD_some]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_none (Nat.not_lt.mp hc), Option.map_none, Option.getD_none, Nat.cast_zero]
  simp only [quotientReduceInt, hv0, solveFloorMul, quotientReduceRhs, intTableToRatTable,
    intTableMulVec, ratFloor_eq_ratFloor]

/-- HNF-free strict-PPT quotient sampler for `L(B) ∩ P(S)`. Returns `0` if `D = 0`. -/
noncomputable def sampleQuotientModS (inp : QuotientSampleInput) : ProbComp (List ℤ) :=
  let D := quotientIndex inp.basis inp.sublattice
  let width := if D = 0 then 0 else Nat.clog 2 D + inp.extraBits
  do
    let coords ← (List.range inp.dim).mapM fun _ => sampleModNat width D
    pure (if D = 0 then List.replicate inp.dim 0
      else quotientReduceInt inp.dim inp.basis inp.sublattice coords)

private theorem computableInPolyTime_quotientReduceInt :
    ComputableInPolyTime
      (fun p : QuotientSampleInput × List ℕ =>
        quotientReduceInt p.1.dim p.1.basis p.1.sublattice p.2)
      (encPair QuotientSampleInput.enc (encList encNat)) (encList encIntBin) := by
  let encIn := encPair QuotientSampleInput.enc (encList encNat)
  have hdim : ComputableInPolyTime (fun p : QuotientSampleInput × List ℕ => p.1.dim)
      encIn encUnary := by fun_prop
  have hB : ComputableInPolyTime (fun p : QuotientSampleInput × List ℕ => p.1.basis)
      encIn IntTable.enc := by fun_prop
  have hS : ComputableInPolyTime (fun p : QuotientSampleInput × List ℕ => p.1.sublattice)
      encIn IntTable.enc := by fun_prop
  have hxInt : ComputableInPolyTime
      (fun p : QuotientSampleInput × List ℕ => p.2.map (Nat.cast : ℕ → ℤ))
      encIn (encList encIntBin) := by
    have hcast : ComputableInPolyTime (fun q : (QuotientSampleInput × List ℕ) × ℕ => (q.2 : ℤ))
        (encPair encIn encNat) encIntBin := (snd encIn encNat).trans intBin_natCast
    exact mapWithInput (f := fun _ (n : ℕ) => (n : ℤ))
      (snd QuotientSampleInput.enc (encList encNat)) hcast
  have hv0 := (hB.prod hxInt).trans computableInPolyTime_intTableMulVec
  have hrhs := computableInPolyTime_vecIntToRat hdim hv0
  have hsk := computableInPolyTime_solveFloorMul hdim hS hrhs
  have hmain := computableInPolyTime_vecSub hdim hv0 hsk
  have heq :
      (fun p : QuotientSampleInput × List ℕ =>
        quotientReduceInt p.1.dim p.1.basis p.1.sublattice p.2) =
      fun p =>
        let v0 := intTableMulVec p.1.basis (p.2.map (Nat.cast : ℕ → ℤ))
        let sk := solveFloorMul p.1.dim p.1.sublattice
          ((List.range p.1.dim).map fun j => (v0.getD j 0 : ℚ))
        (List.range p.1.dim).map fun i => v0.getD i 0 - sk.getD i 0 :=
    funext fun p => quotientReduceInt_eq_solveFloorMul _ _ _ _
  rw [heq]
  exact hmain

/-- Strict-PPT certificate for `sampleQuotientModS`. -/
theorem isPPTOn_sampleQuotientModS :
    IsPPTOn QuotientSampleInput.enc (encList encIntBin) sampleQuotientModS := by
  have hB : ComputableInPolyTime QuotientSampleInput.basis
      QuotientSampleInput.enc IntTable.enc := by fun_prop
  have hS : ComputableInPolyTime QuotientSampleInput.sublattice
      QuotientSampleInput.enc IntTable.enc := by fun_prop
  have hextra : ComputableInPolyTime QuotientSampleInput.extraBits
      QuotientSampleInput.enc encUnary := by fun_prop
  have hdim : ComputableInPolyTime QuotientSampleInput.dim
      QuotientSampleInput.enc encUnary := by fun_prop
  have hD : ComputableInPolyTime
      (fun inp : QuotientSampleInput => quotientIndex inp.basis inp.sublattice)
      QuotientSampleInput.enc encNat :=
    computableInPolyTime_quotientIndex.comp (hB.prod hS)
  have hD0 : ComputableInPolyTime
      (fun inp : QuotientSampleInput => decide (quotientIndex inp.basis inp.sublattice = 0))
      QuotientSampleInput.enc encBool :=
    decide_eq' hD (const 0)
  have hwidth : ComputableInPolyTime
      (fun inp : QuotientSampleInput =>
        if quotientIndex inp.basis inp.sublattice = 0 then 0
        else Nat.clog 2 (quotientIndex inp.basis inp.sublattice) + inp.extraBits)
      QuotientSampleInput.enc encUnary :=
    ite_decide hD0 (const 0) (unary_add' (binary_clog_two.comp hD) hextra)
  have hcoord : IsPPTOn (encPair QuotientSampleInput.enc encUnary) encNat
      (fun p : QuotientSampleInput × ℕ =>
        sampleModNat
          (if quotientIndex p.1.basis p.1.sublattice = 0 then 0
            else Nat.clog 2 (quotientIndex p.1.basis p.1.sublattice) + p.1.extraBits)
          (quotientIndex p.1.basis p.1.sublattice)) :=
    isPPTOn_sampleModNat (hwidth.comp (fst QuotientSampleInput.enc encUnary))
      (hD.comp (fst QuotientSampleInput.enc encUnary))
  have htrav : IsPPTOn QuotientSampleInput.enc (encList encNat)
      (fun inp => (List.range inp.dim).mapM fun _ =>
        sampleModNat
          (if quotientIndex inp.basis inp.sublattice = 0 then 0
            else Nat.clog 2 (quotientIndex inp.basis inp.sublattice) + inp.extraBits)
          (quotientIndex inp.basis inp.sublattice)) :=
    IsPPTOn.mapMWith hcoord (unary_range' hdim)
  have hrep : ComputableInPolyTime
      (fun p : QuotientSampleInput × List ℕ => List.replicate p.1.dim (0 : ℤ))
      (encPair QuotientSampleInput.enc (encList encNat)) (encList encIntBin) := by fun_prop
  have hpost : ComputableInPolyTime
      (fun p : QuotientSampleInput × List ℕ =>
        if quotientIndex p.1.basis p.1.sublattice = 0 then List.replicate p.1.dim (0 : ℤ)
        else quotientReduceInt p.1.dim p.1.basis p.1.sublattice p.2)
      (encPair QuotientSampleInput.enc (encList encNat)) (encList encIntBin) :=
    ite_decide (hD0.comp (fst QuotientSampleInput.enc (encList encNat)))
      hrep computableInPolyTime_quotientReduceInt
  have hres := htrav.map_with
    (f := fun inp coords =>
      if quotientIndex inp.basis inp.sublattice = 0 then List.replicate inp.dim (0 : ℤ)
      else quotientReduceInt inp.dim inp.basis inp.sublattice coords)
    hpost
  refine hres.congr fun inp => ?_
  simp only [sampleQuotientModS, bind_pure_comp]

/-- `CloseTo` bound for `sampleQuotientModS` against `PMF.piFin` of `uniformOfFintype (ZMod D)`
pushed forward by `quotientReduceInt`. -/
theorem closeTo_eval_sampleQuotientModS_pi (inp : QuotientSampleInput)
    (hDpos : 0 < quotientIndex inp.basis inp.sublattice) :
    let D := quotientIndex inp.basis inp.sublattice
    letI : NeZero D := ⟨hDpos.ne'⟩
    CloseTo (ProbComp.eval (sampleQuotientModS inp))
      ((PMF.piFin fun _ : Fin inp.dim => PMF.uniformOfFintype (ZMod D)).map
        fun z => quotientReduceInt inp.dim inp.basis inp.sublattice
          (List.ofFn fun i => (z i).val))
      ((inp.dim : ℝ≥0∞) / 2 ^ inp.extraBits) := by
  dsimp only
  set D := quotientIndex inp.basis inp.sublattice
  have : NeZero D := ⟨hDpos.ne'⟩
  have hDne : D ≠ 0 := hDpos.ne'
  set width := Nat.clog 2 D + inp.extraBits
  have hcoord : CloseTo
      ((ProbComp.eval (sampleModNat width D)).map (Nat.cast : ℕ → ZMod D))
      (PMF.uniformOfFintype (ZMod D))
      (1 / 2 ^ inp.extraBits) := by
    refine (closeTo_uniform_sampleModNat width D).symm.mono ?_
    have hDle : (D : ℝ≥0∞) ≤ 2 ^ Nat.clog 2 D := by
      exact_mod_cast Nat.le_pow_clog (by omega) D
    rw [show (2 : ℝ≥0∞) ^ width = 2 ^ Nat.clog 2 D * 2 ^ inp.extraBits by
      dsimp only [width]; rw [pow_add]]
    calc
      (D : ℝ≥0∞) / (2 ^ Nat.clog 2 D * 2 ^ inp.extraBits) ≤
          (2 ^ Nat.clog 2 D) / (2 ^ Nat.clog 2 D * 2 ^ inp.extraBits) :=
        ENNReal.div_le_div_right hDle _
      _ = 1 / 2 ^ inp.extraBits := by
        conv_lhs => arg 1; rw [← mul_one ((2 : ℝ≥0∞) ^ Nat.clog 2 D)]
        rw [ENNReal.mul_div_mul_left 1 (2 ^ inp.extraBits) (by positivity) (by simp)]
  have hpi : CloseTo
      (PMF.piFin fun _ : Fin inp.dim =>
        (ProbComp.eval (sampleModNat width D)).map (Nat.cast : ℕ → ZMod D))
      (PMF.piFin fun _ : Fin inp.dim => PMF.uniformOfFintype (ZMod D))
      ((inp.dim : ℝ≥0∞) / 2 ^ inp.extraBits) := by
    have h := CloseTo.piFin (fun _ : Fin inp.dim => hcoord)
    rwa [mul_one_div] at h
  have heval : ProbComp.eval (sampleQuotientModS inp) =
      (PMF.piFin fun _ : Fin inp.dim =>
        (ProbComp.eval (sampleModNat width D)).map (Nat.cast : ℕ → ZMod D)).map
        fun z => quotientReduceInt inp.dim inp.basis inp.sublattice
          (List.ofFn fun i => (z i).val) := by
    rw [PMF.piFin_map (p := fun _ : Fin inp.dim => ProbComp.eval (sampleModNat width D))
      (g := fun _ => (Nat.cast : ℕ → ZMod D)), PMF.map_comp]
    have hprog : sampleQuotientModS inp =
        (do
          let coords ← (List.range inp.dim).mapM fun _ => sampleModNat width D
          pure (quotientReduceInt inp.dim inp.basis inp.sublattice coords)) := by
      unfold sampleQuotientModS
      dsimp only
      change (do
        let coords ← (List.range inp.dim).mapM fun _ =>
          sampleModNat (if D = 0 then 0 else Nat.clog 2 D + inp.extraBits) D
        pure (if D = 0 then List.replicate inp.dim 0
          else quotientReduceInt inp.dim inp.basis inp.sublattice coords)) = _
      simp only [hDne, ↓reduceIte]
      rfl
    rw [hprog, bind_pure_comp, ProbComp.eval_map, eval_mapM_range, PMF.map_comp]
    apply PMF.map_congr_on_support
    intro r hr
    simp only [Function.comp_apply]
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_ofFn]
    have hri : r ⟨i, by simpa using hi⟩ ∈ (ProbComp.eval (sampleModNat width D)).support :=
      (PMF.mem_support_piFin_iff _ _).mp hr ⟨i, by simpa using hi⟩
    have hlt : r ⟨i, by simpa using hi⟩ < D := by
      unfold sampleModNat at hri
      rw [ProbComp.eval_map] at hri
      obtain ⟨n, _, hn⟩ := (PMF.mem_support_map_iff _ _ _).mp hri
      rw [← hn]
      exact Nat.mod_lt n hDpos
    exact (ZMod.val_natCast_of_lt hlt).symm
  rw [heval]
  exact hpi.map _

end Cslib.Probability
