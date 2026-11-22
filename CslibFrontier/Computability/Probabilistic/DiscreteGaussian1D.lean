/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Foundations.Analysis.Lattice.Dual
public import CslibFrontier.Foundations.Probability.Gaussian.Int
public import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter
public import CslibFrontier.Probability.StatisticalDistance.CloseTo

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.PolyTime.FixedPointExp
import CslibFrontier.Computability.Probabilistic.RejectionSampling
import CslibFrontier.Foundations.Data.Nat.Clog
import CslibFrontier.Foundations.Probability.Gaussian.OffCenterTail
import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
import CslibFrontier.Probability.DDGTree.Rejection
import CslibFrontier.Probability.Option
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.StatisticalDistance.TotalVariation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Strict-PPT 1-D discrete Gaussian sampler (`sampleZ`)

This module constructs the finite-parameter strict probabilistic polynomial-time (`IsPPTOn`) 1-D
discrete Gaussian sampler `Cslib.Probability.sampleZ` together with explicit statistical-distance
(`CloseTo`) and support-radius certificates, without matrix or determinant dependencies.

On input `inp : SampleZInput` with rational squared width `sSq = s² > 0` and rational center `c`,
each trial draws a uniform integer proposal from the padded interval `[⌊c⌋ - R, ⌊c⌋ + R]` about
`⌊c⌋` (with `R = ⌊√⌊t² · s²⌋⌋ + 2`), containing the paper's window `ℤ ∩ [c - s · t, c + s · t]`,
and accepts via a `prec`-bit dyadic coin computed by the deterministic fixed-point Machin-`π` and
range-reduced `exp(-z)` primitives in `CslibFrontier.Computability.PolyTime.FixedPointExp`.
Repeating for at most `maxTrials` blocks with timeout fallback `⌊c⌋` realizes the capped-trial
variant of [GentryPeikertVaikuntanathan2008], §4.1, Lemmas 4.2–4.3 (pp. 14–15). The asymptotic
`ω(log n)` endpoint is not formalized here (tracked in
[#6861](https://github.com/cslib-community/cslib-frontier/issues/6861) and
[#1213](https://github.com/cslib-community/cslib-frontier/issues/1213)).

## Main definitions

* `Cslib.Probability.SampleZInput`, `Cslib.Probability.SampleZInput.enc`: input parameters and
  framing multi-tape Turing machine encoding for `sampleZ`.
* `Cslib.Probability.sampleZ`: finite-parameter strict-PPT 1-D discrete Gaussian sampler.

## Main results

* `Cslib.Probability.isPPTOn_sampleZ`: unconditional strict-PPT certificate for `sampleZ`.
* `Cslib.Probability.closeTo_eval_sampleZ_discreteGaussian`,
  `Cslib.Probability.closeTo_eval_sampleZ_discreteGaussian_of_smoothingParameter_le`:
  finite-parameter `CloseTo` certificates against `ZLattice.discreteGaussianInt` in dual-mass and
  smoothing-parameter forms.
* `Cslib.Probability.mem_support_sampleZ_abs_sub_le`: real distance support bound
  `|(z : ℝ) - inp.center| ≤ inp.tail * √(inp.sSq) + 3` for `0 < inp.sSq`.

## References

* [C. Gentry, C. Peikert, and V. Vaikuntanathan, *Trapdoors for Hard Lattices and New
  Cryptographic Constructions*][GentryPeikertVaikuntanathan2008], §4.1, Lemmas 4.2–4.3 (full
  version of August 25, 2008, pp. 14–15).
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM ComputableInPolyTime Cslib.FixedPointExp
open Module Cslib.ProbComp ProbabilityTheory ZLattice
open scoped ENNReal RealInnerProductSpace Cslib.Probability.PMF

/-! ### 1. `SampleZInput`, search radius, weight numerator, and `sampleZ` -/

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

private theorem sampleZRadius_target_sq (inp : SampleZInput) (hsSq : 0 < inp.sSq) :
    ((inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ)) ^ 2 =
      ((inp.tail ^ 2 * inp.sSq.num.natAbs : ℕ) : ℝ) / (inp.sSq.den : ℝ) := by
  rw [mul_pow, Real.sq_sqrt (by exact_mod_cast hsSq.le), rat_eq_natAbs_div_den hsSq.le]
  push_cast; ring

private theorem lt_sampleZRadius_sub_one (inp : SampleZInput) (hsSq : 0 < inp.sSq) :
    (inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ) < (sampleZRadius inp : ℝ) - 1 := by
  set m : ℕ := (inp.tail ^ 2 * inp.sSq.num.natAbs) / inp.sSq.den
  have hden_pos : 0 < inp.sSq.den := inp.sSq.den_pos
  have hden_r : (0 : ℝ) < (inp.sSq.den : ℝ) := by exact_mod_cast hden_pos
  have hsq_lt :
      ((inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ)) ^ 2 < ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by
    have h1 := sampleZRadius_target_sq inp hsSq
    have h2 : ((inp.tail ^ 2 * inp.sSq.num.natAbs : ℕ) : ℝ) / (inp.sSq.den : ℝ) < (m : ℝ) + 1 := by
      rw [div_lt_iff₀ hden_r]
      have h := Nat.lt_mul_div_succ (inp.tail ^ 2 * inp.sSq.num.natAbs) hden_pos
      have h' : ((inp.tail ^ 2 * inp.sSq.num.natAbs : ℕ) : ℝ) <
          (inp.sSq.den : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast h
      linarith only [h']
    have h3 : m + 1 ≤ (Nat.sqrt m + 1) ^ 2 := by
      rw [sq]
      exact Nat.succ_le_of_lt (Nat.lt_succ_sqrt m)
    have h3' : (m : ℝ) + 1 ≤ ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h3
    linarith only [h1, h2, h3']
  have hlt : (inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ) < ((Nat.sqrt m + 1 : ℕ) : ℝ) :=
    lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg _) hsq_lt
  have hR : (sampleZRadius inp : ℝ) - 1 = ((Nat.sqrt m + 1 : ℕ) : ℝ) := by
    unfold sampleZRadius; push_cast; ring
  linarith only [hlt, hR]

private theorem sampleZRadius_le (inp : SampleZInput) (hsSq : 0 < inp.sSq) :
    (sampleZRadius inp : ℝ) ≤ (inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ) + 2 := by
  set m : ℕ := (inp.tail ^ 2 * inp.sSq.num.natAbs) / inp.sSq.den
  have hden_r : (0 : ℝ) < (inp.sSq.den : ℝ) := by exact_mod_cast inp.sSq.den_pos
  have hsq_le : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ ((inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ)) ^ 2 := by
    have h1 : (Nat.sqrt m : ℕ) ^ 2 ≤ m := by rw [sq]; exact Nat.sqrt_le m
    have h2 : (m : ℝ) ≤ ((inp.tail ^ 2 * inp.sSq.num.natAbs : ℕ) : ℝ) / (inp.sSq.den : ℝ) := by
      rw [le_div_iff₀ hden_r]
      exact_mod_cast Nat.div_mul_le_self (inp.tail ^ 2 * inp.sSq.num.natAbs) inp.sSq.den
    have h3 := sampleZRadius_target_sq inp hsSq
    have h1' : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast h1
    linarith only [h1', h2, h3]
  have hle : (Nat.sqrt m : ℝ) ≤ (inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ) :=
    le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq_le
  unfold sampleZRadius
  push_cast
  linarith only [hle]

private theorem two_mul_sampleZRadius_add_one_le (inp : SampleZInput) (hsSq : 0 < inp.sSq)
    (hs1 : 1 ≤ Real.sqrt (inp.sSq : ℝ)) :
    ((2 * sampleZRadius inp + 1 : ℕ) : ℝ) ≤
      (2 * (inp.tail : ℝ) + 6) * Real.sqrt (inp.sSq : ℝ) := by
  have hR := sampleZRadius_le inp hsSq
  rw [add_mul]
  push_cast
  linarith only [hR, hs1]

/-- Extra internal fixed-point guard bits for `sampleZWeightNum`. -/
private def sampleZShift (tail prec : ℕ) : ℕ :=
  3 * Nat.clog 2 (tail + 3) + Nat.clog 2 (prec + 16) + 12

private theorem sampleZShift_bound (tail prec : ℕ) :
    2 * (4 * (tail + 3) ^ 2) * (4 * (prec + sampleZShift tail prec + 2) + 4) ≤
      2 ^ sampleZShift tail prec := by
  have hA_ge : tail + 3 ≤ 2 ^ Nat.clog 2 (tail + 3) := Nat.le_pow_clog Nat.one_lt_two _
  have hB_ge : prec + 16 ≤ 2 ^ Nat.clog 2 (prec + 16) := Nat.le_pow_clog Nat.one_lt_two _
  have hcT : Nat.clog 2 (tail + 3) ≤ 2 ^ Nat.clog 2 (tail + 3) :=
    (Nat.clog_le_self 2 (tail + 3)).trans hA_ge
  have hcP : Nat.clog 2 (prec + 16) ≤ 2 ^ Nat.clog 2 (prec + 16) :=
    (Nat.clog_le_self 2 (prec + 16)).trans hB_ge
  unfold sampleZShift
  generalize Nat.clog 2 (tail + 3) = cT at hA_ge hcT ⊢
  generalize Nat.clog 2 (prec + 16) = cP at hB_ge hcP ⊢
  rw [pow_add, pow_add, mul_comm 3, pow_mul]
  generalize 2 ^ cT = A at hA_ge hcT ⊢
  generalize 2 ^ cP = B at hB_ge hcP ⊢
  have hK : 4 * (tail + 3) ^ 2 ≤ 4 * A ^ 2 :=
    Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hA_ge 2)
  have hfac : 4 * (prec + (cT * 3 + cP + 12) + 2) + 4 ≤ 23 * (A * B) := by
    have hAB1 := Nat.mul_le_mul hcT (show 16 ≤ B by omega)
    have hAB2 := Nat.mul_le_mul (show 3 ≤ A by omega) hB_ge
    have hAB3 := Nat.mul_le_mul (show 3 ≤ A by omega) hcP
    omega
  calc
    2 * (4 * (tail + 3) ^ 2) * (4 * (prec + (cT * 3 + cP + 12) + 2) + 4) ≤
        2 * (4 * A ^ 2) * (23 * (A * B)) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hK) hfac
    _ = 184 * (A ^ 3 * B) := by ring
    _ ≤ 2 ^ 12 * (A ^ 3 * B) := Nat.mul_le_mul_right _ (by decide)
    _ = A ^ 3 * B * 2 ^ 12 := by ring

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

private theorem finToInt_abs_sub_le (inp : SampleZInput) (hsSq : 0 < inp.sSq)
    (i : Fin (2 * sampleZRadius inp + 1)) :
    |(finToInt inp.center.floor (sampleZRadius inp) i : ℝ) - (inp.center : ℝ)| ≤
      (inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ) + 3 := by
  have hR := sampleZRadius_le inp hsSq
  have hfl1 : ((inp.center.floor : ℤ) : ℝ) ≤ (inp.center : ℝ) := by
    exact_mod_cast (Int.floor_le inp.center : ((inp.center.floor : ℤ) : ℚ) ≤ inp.center)
  have hfl2 : (inp.center : ℝ) < ((inp.center.floor : ℤ) : ℝ) + 1 := by
    exact_mod_cast
      (Int.lt_floor_add_one inp.center : inp.center < ((inp.center.floor : ℤ) : ℚ) + 1)
  have hx_eq : (finToInt inp.center.floor (sampleZRadius inp) i : ℝ) =
      (inp.center.floor : ℝ) - (sampleZRadius inp : ℝ) + (i.val : ℝ) := by
    dsimp only [finToInt]; push_cast; rfl
  have hi_le : (i.val : ℝ) ≤ 2 * (sampleZRadius inp : ℝ) := by
    have : i.val ≤ 2 * sampleZRadius inp := by omega
    exact_mod_cast this
  have hi_ge : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
  rw [hx_eq, abs_le]
  constructor <;> linarith only [hR, hfl1, hfl2, hi_le, hi_ge]

private theorem abs_sampleZWeightNum_div_sub_gaussianWeight_le
    (inp : SampleZInput) (hsSq : 0 < inp.sSq) (hs1 : 1 ≤ Real.sqrt (inp.sSq : ℝ))
    (i : Fin (2 * sampleZRadius inp + 1)) :
    let x := finToInt (inp.center.floor) (sampleZRadius inp) i
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
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ qBits := by positivity
  have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ inp.prec := by positivity
  have hKpos : 0 < K := by dsimp only [K]; positivity
  have hsSq_r : (0 : ℝ) < (inp.sSq : ℝ) := by exact_mod_cast hsSq
  have hs_sq : s ^ 2 = (inp.sSq : ℝ) := Real.sq_sqrt hsSq_r.le
  have hr_nonneg : (0 : ℚ) ≤ r := div_nonneg (sq_nonneg _) hsSq.le
  have hr_cast : (r : ℝ) = ((x : ℝ) - (inp.center : ℝ)) ^ 2 / s ^ 2 := by
    dsimp only [r, sampleZRatArg]; rw [hs_sq]; push_cast; rfl
  have hr_nat : (r : ℝ) = (r.num.natAbs : ℝ) / (r.den : ℝ) := rat_eq_natAbs_div_den hr_nonneg
  have hx_dist : |(x : ℝ) - (inp.center : ℝ)| ≤ ((inp.tail : ℝ) + 3) * s := by
    have h1 := finToInt_abs_sub_le inp hsSq i
    dsimp only [x, s] at h1 ⊢
    rw [add_mul]
    linarith only [h1, hs1]
  have hr_div_K : (r : ℝ) / (K : ℝ) ≤ 1 / 4 := by
    rw [hr_cast]
    have hsq : ((x : ℝ) - (inp.center : ℝ)) ^ 2 ≤ (((inp.tail : ℝ) + 3) * s) ^ 2 := by
      rw [← sq_abs ((x : ℝ) - (inp.center : ℝ))]
      exact pow_le_pow_left₀ (abs_nonneg _) hx_dist 2
    have hdiv : ((x : ℝ) - (inp.center : ℝ)) ^ 2 / s ^ 2 ≤ ((inp.tail : ℝ) + 3) ^ 2 := by
      rw [div_le_iff₀ (sq_pos_of_pos (by linarith only [hs1] : 0 < s)), ← mul_pow]
      exact hsq
    have hK_r : (K : ℝ) = 4 * ((inp.tail : ℝ) + 3) ^ 2 := by dsimp only [K]; push_cast; ring
    rw [hK_r, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hdiv]
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
    exact div_le_div_of_nonneg_right h1 h2q_pos.le
  have hzFp_gt_exact :
      ((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) - 1 / (2 : ℝ) ^ qBits <
        (zFp : ℝ) / (2 : ℝ) ^ qBits := by
    have h1 : ((piFp * r.num.natAbs : ℕ) : ℝ) / ((r.den * K : ℕ) : ℝ) < (zFp : ℝ) + 1 := by
      rw [div_lt_iff₀ hdenK_pos]
      have h := Nat.lt_mul_div_succ (piFp * r.num.natAbs) (Nat.mul_pos r.den_pos hKpos)
      have h' : ((piFp * r.num.natAbs : ℕ) : ℝ) <
          ((r.den * K : ℕ) : ℝ) * ((zFp : ℝ) + 1) := by exact_mod_cast h
      linarith only [h']
    have h2 : ((piFp * r.num.natAbs : ℕ) : ℝ) / ((r.den * K : ℕ) : ℝ) / (2 : ℝ) ^ qBits =
        ((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) := by
      rw [hr_nat]; push_cast; ring
    have h3 := div_lt_div_of_pos_right h1 h2q_pos
    rw [h2, add_div] at h3
    linarith only [h3]
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
      rw [abs_le]; constructor <;> linarith only [hzFp_le_exact, hzFp_gt_exact]
    have htri : |zReal - (zFp : ℝ) / (2 : ℝ) ^ qBits| ≤
        |((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) - zReal| +
          |((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ)) - (zFp : ℝ) / (2 : ℝ) ^ qBits| := by
      rw [abs_sub_comm (((piFp : ℝ) / (2 : ℝ) ^ qBits) * ((r : ℝ) / (K : ℝ))) zReal]
      exact abs_sub_le _ _ _
    have hcomb : (1 / 4) / (2 : ℝ) ^ qBits + 1 / (2 : ℝ) ^ qBits ≤ 2 / (2 : ℝ) ^ qBits := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) h2q_pos.le
    linarith only [htri, h1, h2, hcomb]
  have hzFp_le : zFp ≤ 2 ^ qBits := by
    have hpi4 : Real.pi < 3.15 := Real.pi_lt_d4.trans (by norm_num)
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
      linarith only [hsub, hzReal_lt, h2div]
    have hle_r : (zFp : ℝ) ≤ ((2 ^ qBits : ℕ) : ℝ) := by
      push_cast
      exact (div_le_one h2q_pos).mp hzFp_lt
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
      have hmul := mul_le_mul_of_nonneg_left hb_r h2p_pos.le
      rw [div_le_div_iff₀ h2q_pos h2p_pos, h2q]
      linarith only [hmul]
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
    rw [h2q, ← div_div, div_right_comm (raw : ℝ), ← sub_div, abs_div, abs_of_pos h2p_pos]
    exact div_le_div_of_nonneg_right hshift_err h2p_pos.le
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
      let x : ℤ := inp.center.floor - (R : ℤ) + (idx : ℤ)
      if coin < sampleZWeightNum inp x then some x else none
    else none

/-- Finite-parameter strict-PPT capped-trial 1-D discrete Gaussian sampler after
[GentryPeikertVaikuntanathan2008], §4.1, Lemma 4.3 (p. 15). Proposals are drawn uniformly from the
padded integer interval `[⌊c⌋ - R, ⌊c⌋ + R]` about `⌊c⌋` (with `R = ⌊√⌊t² · s²⌋⌋ + 2`), which
contains the paper's window `ℤ ∩ [c - s · t, c + s · t]`; the asymptotic `ω(log n)` endpoint is not
formalized here (tracked in [#6861](https://github.com/cslib-community/cslib-frontier/issues/6861)
and [#1213](https://github.com/cslib-community/cslib-frontier/issues/1213)). -/
noncomputable def sampleZ (inp : SampleZInput) : ProbComp ℤ :=
  sampleBlockCapped (sampleZIntSpec inp) (inp.center.floor) inp.maxTrials

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
  have hfallback : ComputableInPolyTime (fun inp : SampleZInput => inp.center.floor)
      SampleZInput.enc encIntBin := rat_floor.comp hcenter
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
  have hfallback : ComputableInPolyTime (fun inp : SampleZInput => inp.center.floor)
      SampleZInput.enc encIntBin := rat_floor.comp hcenter
  exact isPPTOn_sampleBlockCapped htrials hwidth computableInPolyTime_sampleZAttempt hfallback


/-! ### 2. Distribution analysis of `sampleZ` via `CloseTo` -/

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
      if coin < sampleZWeightNum inp (finToInt (inp.center.floor) R i) then some i else none
    else none


private theorem eval_sampleZ_eq_map_runCapped (inp : SampleZInput) :
    ProbComp.eval (sampleZ inp) =
      ((sampleZFinSpec inp).runCapped ⟨sampleZRadius inp, by omega⟩ inp.maxTrials).map
        (finToInt (inp.center.floor) (sampleZRadius inp)) := by
  have hdec := BlockRejectionSpec.decodeTrials_map (sampleZFinSpec inp)
    (finToInt (inp.center.floor) (sampleZRadius inp)) (sampleZIntSpec inp) rfl (fun bits => by
      dsimp only [sampleZIntSpec, sampleZFinSpec, finToInt]
      by_cases h1 : Cslib.BitString.binaryValue
          (bits.take (Nat.clog 2 (2 * sampleZRadius inp + 1))) < 2 * sampleZRadius inp + 1
      · simp only [h1, ↓reduceIte, ↓reduceDIte]
        by_cases h2 : Cslib.BitString.binaryValue
            (bits.drop (Nat.clog 2 (2 * sampleZRadius inp + 1))) <
            sampleZWeightNum inp (inp.center.floor - (sampleZRadius inp : ℤ) +
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
      (sampleZWeightNum inp (finToInt (inp.center.floor) R i) : ℝ≥0∞) /
        ((2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞) ^ inp.prec) := by
  intro R k
  classical
  have hi_lt : i.val < 2 ^ k := lt_of_lt_of_le i.isLt (Nat.le_pow_clog (by omega) _)
  let iK : Fin (2 ^ k) := ⟨i.val, hi_lt⟩
  let w : ℕ := sampleZWeightNum inp (finToInt (inp.center.floor) R i)
  have hw_le : w ≤ 2 ^ inp.prec := sampleZWeightNum_le inp _
  have hlaw : (sampleZFinSpec inp).singleLaw =
      (PMF.uniformOfFintype (Fin (2 ^ k))).bind fun idx =>
        (PMF.uniformOfFintype (Fin (2 ^ inp.prec))).map fun coin =>
          if h : idx.val < 2 * R + 1 then
            let j : Fin (2 * R + 1) := ⟨idx.val, h⟩
            if coin.val < sampleZWeightNum inp (finToInt (inp.center.floor) R j) then some j
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
          if coin < sampleZWeightNum inp (finToInt (inp.center.floor) R j) then some j else none
        else none))
    change (Cslib.BitString.uniformList (k + inp.prec)).map _ = _
    rw [PMF.map]
    change (Cslib.BitString.uniformList (k + inp.prec)).bind
      (fun tape => PMF.pure (
        let idx := Cslib.BitString.binaryValue (tape.take k)
        let coin := Cslib.BitString.binaryValue (tape.drop k)
        if h : idx < 2 * R + 1 then
          let j : Fin (2 * R + 1) := ⟨idx, h⟩
          if coin < sampleZWeightNum inp (finToInt (inp.center.floor) R j) then some j else none
        else none)) = _
    rw [h1]
    have hmap_bin {α : Type} (m : ℕ) (f : ℕ → PMF α) :
        (Cslib.BitString.uniformList m).bind (fun b => f (Cslib.BitString.binaryValue b)) =
          (PMF.uniformOfFintype (Fin (2 ^ m))).bind (fun idx => f idx.val) := by
      change (Cslib.BitString.uniformList m).bind (f ∘ Cslib.BitString.binaryValue) =
        (PMF.uniformOfFintype (Fin (2 ^ m))).bind (f ∘ Fin.val)
      rw [← PMF.bind_map, Cslib.BitString.uniformList_binaryValue, PMF.bind_map]
    dsimp only
    rw [hmap_bin (α := Option (Fin (2 * R + 1))) k (fun idx =>
      (Cslib.BitString.uniformList inp.prec).bind fun b2 => PMF.pure
        (if h : idx < 2 * R + 1 then
          let j : Fin (2 * R + 1) := ⟨idx, h⟩
          if Cslib.BitString.binaryValue b2 <
              sampleZWeightNum inp (finToInt (inp.center.floor) R j)
          then some j else none else none))]
    congr 1; funext idx
    simpa only [PMF.map, Function.comp_def] using
      hmap_bin (α := Option (Fin (2 * R + 1))) inp.prec (fun coin => PMF.pure (
        if h : idx.val < 2 * R + 1 then
          let j : Fin (2 * R + 1) := ⟨idx.val, h⟩
          if coin < sampleZWeightNum inp (finToInt (inp.center.floor) R j)
          then some j else none else none))
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
          if coin.val < sampleZWeightNum inp (finToInt (inp.center.floor) R j) then some j
          else none
        else none) (some i) = 0 := by
      rw [PMF.map_apply]
      refine tsum_eq_zero_iff.mpr fun coin => ?_
      by_cases hlt : idx.val < 2 * R + 1
      · simp only [hlt, ↓reduceDIte]
        by_cases hc : coin.val <
            sampleZWeightNum inp (finToInt (inp.center.floor) R ⟨idx.val, hlt⟩)
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
  linarith only [hsum_le, hdiv]

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

/-- Finite-parameter strict-PPT `CloseTo` step for `sampleZ` against `discreteGaussianInt` under
the 1-D dual-mass premise `ρ_{1/s}(ℤ* \ {0}) ≤ ε ≤ 1 / 2`, after
[GentryPeikertVaikuntanathan2008], §4.1, Lemmas 4.2–4.3 (pp. 14–15); the asymptotic `ω(log n)`
endpoint is not formalized here (tracked in
[#6861](https://github.com/cslib-community/cslib-frontier/issues/6861) and
[#1213](https://github.com/cslib-community/cslib-frontier/issues/1213)). -/
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
  set cF : ℤ := inp.center.floor
  set R : ℕ := sampleZRadius inp
  set k : ℕ := Nat.clog 2 (2 * R + 1)
  set μ : PMF ℤ := discreteGaussianInt s hs c
  set tailErr : ℝ := (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2))
  have htail := ZLattice.discreteGaussian_real_abs_sub_ge_le_of_dual_mass_le intLatticeReal
    s hs c (Nat.cast_nonneg inp.tail) ε (by linarith only [hε]) hdual
  have htailErr0 : 0 ≤ tailErr := by
    dsimp only [tailErr]
    have : 0 < 1 - ε := by linarith only [hε]
    positivity
  -- 1. Support finset `S = image (finToInt cF R) univ` contains `{x | |x - c| < t * s}`.
  let S : Finset ℤ := Finset.univ.image (finToInt cF R)
  have hfloor : (cF : ℝ) ≤ c ∧ c < (cF : ℝ) + 1 := by
    dsimp only [cF, c]
    exact ⟨by exact_mod_cast Int.floor_le inp.center,
      by exact_mod_cast Int.lt_floor_add_one inp.center⟩
  have hnotS_tail : ∀ x : ℤ, x ∉ (S : Set ℤ) → (inp.tail : ℝ) * s ≤ |(x : ℝ) - c| := by
    intro x hx
    by_contra hlt
    push Not at hlt
    have hR := lt_sampleZRadius_sub_one inp hsSq
    have hlow : cF - (R : ℤ) ≤ x := by
      have h1 : ((cF - (R : ℤ) - 1 : ℤ) : ℝ) < (x : ℝ) := by
        push_cast; linarith only [hfloor.1, hR, (abs_lt.mp hlt).1]
      have h2 : cF - (R : ℤ) - 1 < x := by exact_mod_cast h1
      omega
    have hhigh : x ≤ cF + (R : ℤ) := by
      have h1 : (x : ℝ) < ((cF + (R : ℤ) + 1 : ℤ) : ℝ) := by
        push_cast; linarith only [hfloor.2, hR, (abs_lt.mp hlt).2]
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
    have hpre : ZLattice.intLatticeRealEquiv.symm ⁻¹' (S : Set ℤ)ᶜ ⊆
        {z : intLatticeReal | (inp.tail : ℝ) * s ≤ |(z : ℝ) - c|} := by
      intro z hz
      have hnot : ZLattice.intLatticeRealEquiv.symm z ∉ (S : Set ℤ) := hz
      have hval := hnotS_tail (ZLattice.intLatticeRealEquiv.symm z) hnot
      have hcast : ((ZLattice.intLatticeRealEquiv.symm z : ℤ) : ℝ) = (z : ℝ) :=
        ZLattice.coe_intLatticeRealEquiv_symm z
      rwa [hcast] at hval
    have hmap : μ.toOuterMeasure (S : Set ℤ)ᶜ =
        (ZLattice.discreteGaussian intLatticeReal s hs c).toOuterMeasure
          (ZLattice.intLatticeRealEquiv.symm ⁻¹' (S : Set ℤ)ᶜ) := by
      dsimp only [μ]
      rw [ZLattice.discreteGaussianInt_eq_map]
      exact PMF.toOuterMeasure_map_apply _ _ _
    rw [hmap]
    exact ((ZLattice.discreteGaussian intLatticeReal s hs c).toOuterMeasure.mono hpre).trans htail
  -- 2. Total mass `gaussianMass intLatticeReal s c ≥ s / 2` and truncated mass `V ≥ s / 4`.
  have hcov := ZLattice.covolume_intLatticeReal
  have hmass_ge : s / 2 ≤ ZLattice.gaussianMass intLatticeReal s c := by
    have hIcc := (ZLattice.gaussianMass_mem_Icc_of_dual_mass_le intLatticeReal s hs ε hdual c).1
    rw [Module.finrank_self, pow_one, hcov, div_one] at hIcc
    linarith only [hIcc, mul_le_mul_of_nonneg_right hε hs.le]
  have htailErr_le_half : tailErr ≤ 1 / 2 := by
    dsimp only [tailErr]
    have ht1 : (1 : ℝ) ≤ (inp.tail : ℝ) := by exact_mod_cast ht
    have hpi : Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2) ≤ 1 / 16 := by
      have h1 : -Real.pi * (inp.tail : ℝ) ^ 2 ≤ -3 := by
        linarith only [mul_le_mul Real.pi_gt_three.le (one_le_pow₀ ht1 (n := 2))
          zero_le_one Real.pi_pos.le]
      have hlog : 4 * Real.log 2 < 3 := by linarith only [Real.log_two_lt_d9]
      have hval : Real.exp (-4 * Real.log 2) = 1 / 16 := by
        rw [show (-4 : ℝ) * Real.log 2 = -((4 : ℕ) * Real.log 2) by ring, Real.exp_neg,
          Real.exp_nat_mul, Real.exp_log two_pos]
        norm_num
      exact (Real.exp_le_exp.mpr h1).trans
        ((Real.exp_lt_exp.mpr (by linarith only [hlog])).le.trans hval.le)
    have hrat : (1 + ε) / (1 - ε) ≤ 3 :=
      (div_le_iff₀ (by linarith only [hε])).mpr (by linarith only [hε])
    calc
      (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2)) ≤ 3 * (2 * (1 / 16)) :=
        mul_le_mul hrat (by linarith only [hpi]) (by positivity) (by norm_num)
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
    linarith only [h1, h2, htailErr_le_half]
  have hV_ge : s / 4 ≤ V := by
    have hm_pos := ZLattice.gaussianMass_pos intLatticeReal s hs c
    have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ => (gaussianWeight_pos _ _).le
    have htoReal :
        (μ.toOuterMeasure (S : Set ℤ)).toReal = V / ZLattice.gaussianMass intLatticeReal s c := by
      rw [hS_mass_eq, ENNReal.toReal_div, ENNReal.toReal_ofReal hV0,
        ENNReal.toReal_ofReal hm_pos.le]
    rw [htoReal, le_div_iff₀ hm_pos] at hS_ge_half
    linarith only [hS_ge_half, hmass_ge]
  have hV_pos : 0 < V := by linarith only [hs, hV_ge]
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
      linarith only [mul_le_mul_of_nonneg_right hprec_r hs.le]
    have hsub : V - U ≤ ∑ i, |u i - v i| := by
      calc
        V - U = ∑ i, (v i - u i) := (Finset.sum_sub_distrib _ _).symm
        _ ≤ ∑ i, |u i - v i| := Finset.sum_le_sum fun i _ => by
            rw [abs_sub_comm]; exact le_abs_self _
    linarith only [hV_ge, hsub, hsum_diff, hdiff_le]
  have hU_pos : 0 < U := by linarith only [hs, hU_ge]
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
      have hk_pos : 0 < k := Nat.clog_pos Nat.one_lt_two hR1
      have h2 : 2 ^ k.pred < 2 * R + 1 := Nat.pow_pred_clog_lt_self Nat.one_lt_two hR1
      rw [← Nat.succ_pred_eq_of_pos hk_pos, pow_succ]
      omega
    have hclog_r : (2 : ℝ) ^ k < 2 * ((2 * R + 1 : ℕ) : ℝ) := by exact_mod_cast hclog_lt
    linarith only [hclog_r, two_mul_sampleZRadius_add_one_le inp hsSq hs1]
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
    rw [hrej_eq, ← ENNReal.ofReal_pow (by linarith only [hacc_le1]),
      ENNReal.toReal_ofReal (by positivity)]
    exact pow_le_pow_left₀ (by linarith only [hacc_le1]) (by linarith only [haccept_ge]) _
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
    have hle1 : (1 : ℝ) / (16 * (2 * (inp.tail : ℝ) + 6)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith only [Nat.cast_nonneg (α := ℝ) inp.tail])
    exact pow_nonneg (by linarith only [hle1]) _
  have ht2 : 0 ≤ (8 * (inp.tail : ℝ) + 24) / (2 : ℝ) ^ inp.prec := by positivity
  rwa [← ENNReal.ofReal_add ht1 ht2, ← ENNReal.ofReal_add (add_nonneg ht1 ht2) htailErr0] at h123

/-- Smoothing-parameter (`η_ε(ℤ) ≤ √sSq`) form of the finite-parameter strict-PPT `CloseTo` step
`closeTo_eval_sampleZ_discreteGaussian`, after [GentryPeikertVaikuntanathan2008], §4.1,
Lemmas 4.2–4.3 (pp. 14–15); the asymptotic `ω(log n)` endpoint is not formalized here (tracked in
[#6861](https://github.com/cslib-community/cslib-frontier/issues/6861) and
[#1213](https://github.com/cslib-community/cslib-frontier/issues/1213)). -/
theorem closeTo_eval_sampleZ_discreteGaussian_of_smoothingParameter_le
    (inp : SampleZInput) (hsSq : 0 < inp.sSq) (hs1 : 1 ≤ Real.sqrt (inp.sSq : ℝ))
    (ht : 1 ≤ inp.tail) {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1 / 2)
    (hη : ZLattice.smoothingParameter intLatticeReal ε ≤ Real.sqrt (inp.sSq : ℝ))
    (hprec : 8 * (2 * inp.tail + 6) ≤ 2 ^ inp.prec) :
    CloseTo (ProbComp.eval (sampleZ inp))
      (discreteGaussianInt (Real.sqrt (inp.sSq : ℝ)) (by positivity) (inp.center : ℝ))
      (ENNReal.ofReal
        ((1 - 1 / (16 * (2 * inp.tail + 6 : ℝ))) ^ inp.maxTrials
          + (8 * inp.tail + 24 : ℝ) / (2 : ℝ) ^ inp.prec
          + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2)))) :=
  closeTo_eval_sampleZ_discreteGaussian inp hsSq hs1 ht hε.le hε_le
    ((ZLattice.smoothingParameter_le_iff intLatticeReal (by positivity) hε).mp hη) hprec

/-- Every point in the support of `sampleZ inp` lies within `(inp.tail : ℝ) * √(inp.sSq) + 3` of
`inp.center` for `0 < inp.sSq` (including the timeout fallback `inp.center.floor`). -/
theorem mem_support_sampleZ_abs_sub_le (inp : SampleZInput) (hsSq : 0 < inp.sSq) {z : ℤ}
    (hz : z ∈ (ProbComp.eval (sampleZ inp)).support) :
    |(z : ℝ) - (inp.center : ℝ)| ≤ (inp.tail : ℝ) * Real.sqrt (inp.sSq : ℝ) + 3 := by
  rw [eval_sampleZ_eq_map_runCapped] at hz
  obtain ⟨i, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  exact finToInt_abs_sub_le inp hsSq i

end Cslib.Probability
