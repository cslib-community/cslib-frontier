/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.StableInfluence
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.Linarith

/-!
# The Odd BLR test and Håstad's test

The **Odd BLR test** queries a Boolean function `f` at independent uniformly random strings `x`
and `y` and at `z = x + y + (b, …, b)` for a uniformly random bit `b`, and accepts when
`f(x) + f(y) + f(z) = b` (`BitString.oddBlrAcceptance`). **Håstad's test** with noise rate `δ`
first flips each bit of `z` independently with probability `δ / 2`
(`BitString.hastadAcceptance`). Reading `f` as signs `F`, the test accepts with probability
`1/2 + 1/2 ∑_{|S| odd} (1 - δ) ^ |S| F̂(S)³` (`BitString.hastadAcceptance_eq_sum`)
[O'Donnell, (7.4)][ODonnell2014], and at `δ = 0` this is the Odd BLR test
[O'Donnell, Proposition 7.46][ODonnell2014]. With `b` fixed to `false` the Odd BLR test
corresponds to the Blum–Luby–Rubinfeld test (`BitString.blrAcceptance`), which every parity passes
with probability one, the constant `false` and parities on many coordinates included. The noise
rate is a real parameter, so the tests are stated through their acceptance probabilities rather
than as `PCP.LocalTest`s, whose random strings are uniform.

The same noisy 3-bit linear test, run on folded Long Code tables across a Label Cover projection,
is `Cslib.PCP.Hastad` in `CslibFrontier.Computability.PCP.Approximation.Hastad`, with its own
Fourier expansion `PCP.Hastad.linearCorr_eq_sum` [Håstad][Hastad2001]. That two-table setting is
Håstad's NP-hardness proof; this module is the single-function dictator test of O'Donnell's
Section 7.4, and a `Foundations` module cannot import it.

These tests use only 3-variable linear equations over `F₂` as predicates. A parity on an odd
number `k` of coordinates is accepted with probability `1/2 + 1/2 (1 - δ) ^ k`, and one on an
even number with probability `1/2` (`BitString.hastadAcceptance_parityOn`), so dictators are
accepted with probability `1 - δ / 2` (`BitString.hastadAcceptance_dictator`). Conversely, for
`0 ≤ ε ≤ δ ≤ 1`, if every `(1 - ε)`-stable influence of `F` is at most `ε`, so that `f` has no
`(ε, ε)`-notable coordinates, the test accepts with probability at most `1/2 + 1/2 √ε`
(`BitString.hastadAcceptance_le_of_stableInfluence_le`), and for `0 ≤ δ ≤ 2` it accepts with
probability at most one (`BitString.hastadAcceptance_le_one`). With `λ(ε) = 1/2 √ε` for `ε ≤ δ`
and `λ(ε) = 1/2` otherwise, these are the clauses of a `(1/2, 1 - δ / 2)`-Dictator-vs.-No-Notables
test, and at noise rate `2 δ` this is Håstad's `(1/2, 1 - δ)` test
[O'Donnell, Theorem 7.42][ODonnell2014]. This file does not formalize Dictator-vs.-No-Notables
tests in general [O'Donnell, Definition 7.37][ODonnell2014].

The book's bound `1/2 + 1/2 max_{|S| odd} F̂(S)` for the Odd BLR test needs the maximum to be
nonnegative (`BitString.oddBlrAcceptance_le_of_fourierCoeff_le`).

## Main definitions

* `Cslib.BitString.oddBlrAcceptance`: the acceptance probability of the Odd BLR test.
* `Cslib.BitString.hastadAcceptance`: the acceptance probability of Håstad's test.

## Main results

* `Cslib.BitString.hastadAcceptance_eq_sum`: the Fourier formula (7.4).
* `Cslib.BitString.oddBlrAcceptance_eq_sum`,
  `Cslib.BitString.oddBlrAcceptance_le_of_fourierCoeff_le`: Proposition 7.46.
* `Cslib.BitString.hastadAcceptance_parityOn`: the acceptance probability of parities.
* `Cslib.BitString.hastadAcceptance_dictator`,
  `Cslib.BitString.hastadAcceptance_le_of_stableInfluence_le`,
  `Cslib.BitString.hastadAcceptance_le_one`: Theorem 7.42.

## References

* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The acceptance probability of **Håstad's test** with noise rate `δ` on `f`: over independent
uniformly random strings `x` and `y`, a uniformly random bit `b`, and a string `z'` that flips each
bit of `z = x + y + (b, …, b)` independently with probability `δ / 2`, the probability that
`f(x) + f(y) + f(z') = b`. It is a probability for `0 ≤ δ ≤ 2`. -/
noncomputable def hastadAcceptance (δ : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  𝔼 x, 𝔼 y, 𝔼 b : Bool,
    noiseOp (1 - δ) (fun z => if (f x ^^ f y ^^ f z) = b then 1 else 0) (x + y + fun _ => b)

/-- The defining formula of `hastadAcceptance`. -/
theorem hastadAcceptance_def (δ : ℝ) (f : (ι → Bool) → Bool) :
    hastadAcceptance δ f = 𝔼 x, 𝔼 y, 𝔼 b : Bool,
      noiseOp (1 - δ) (fun z => if (f x ^^ f y ^^ f z) = b then 1 else 0) (x + y + fun _ => b) := by
  rw [hastadAcceptance]

/-- The acceptance probability of the **Odd BLR test** on `f`: over independent uniformly random
strings `x` and `y` and a uniformly random bit `b`, the probability that
`f(x) + f(y) + f(x + y + (b, …, b)) = b`. -/
noncomputable def oddBlrAcceptance (f : (ι → Bool) → Bool) : ℝ :=
  𝔼 x, 𝔼 y, 𝔼 b : Bool, if (f x ^^ f y ^^ f (x + y + fun _ => b)) = b then 1 else 0

/-- The defining formula of `oddBlrAcceptance`. -/
theorem oddBlrAcceptance_def (f : (ι → Bool) → Bool) :
    oddBlrAcceptance f =
      𝔼 x, 𝔼 y, 𝔼 b : Bool, if (f x ^^ f y ^^ f (x + y + fun _ => b)) = b then 1 else 0 := by
  rw [oddBlrAcceptance]

/-- Håstad's test without noise is the Odd BLR test. -/
theorem hastadAcceptance_zero (f : (ι → Bool) → Bool) :
    hastadAcceptance 0 f = oddBlrAcceptance f := by
  simp only [oddBlrAcceptance, hastadAcceptance, sub_zero, noiseOp_one]

omit [Fintype ι] [DecidableEq ι] in
/-- The character of `S` at the constant string `(b, …, b)` is the sign of `b` to the power `|S|`,
so its correlation with the sign of a uniformly random `b` detects whether `|S|` is odd. -/
private theorem expect_signVal_mul_chi_const (S : Finset ι) :
    𝔼 b : Bool, signVal b * chi ℝ S (fun _ => b) = if Odd #S then 1 else 0 := by
  simp only [chi_eq_prod_signVal, prod_const, ← pow_succ', Fintype.expect_bool, signVal_false,
    signVal_true, one_pow]
  rcases Nat.even_or_odd #S with h | h
  · rw [h.add_one.neg_one_pow, ite_eq_right (Nat.not_odd_iff_even.2 h)]
    norm_num
  · rw [h.add_one.neg_one_pow, ite_eq_left h]
    norm_num

/-- **The acceptance probability of Håstad's test** [O'Donnell, (7.4)][ODonnell2014]: reading `f`
as signs, the test accepts with probability `1/2 + 1/2 ∑_{|S| odd} (1 - δ) ^ |S| F̂(S)³`. -/
theorem hastadAcceptance_eq_sum (δ : ℝ) (f : (ι → Bool) → Bool) :
    hastadAcceptance δ f = 1 / 2 + 1 / 2 *
      ∑ S with Odd #S, (1 - δ) ^ #S * fourierCoeff (fun x => signVal (f x)) S ^ 3 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hind (a c b d : Bool) : (if (a ^^ c ^^ d) = b then (1 : ℝ) else 0) =
      1 / 2 + 1 / 2 * (signVal a * signVal c * signVal b) * signVal d := by
    cases a <;> cases c <;> cases b <;> cases d <;> norm_num
  have hterm (x y : ι → Bool) (b : Bool) :
      F x * F y * signVal b * noiseOp (1 - δ) F (x + y + fun _ => b) =
        ∑ S, (1 - δ) ^ #S * fourierCoeff F S * (F x * chi ℝ S x) * (F y * chi ℝ S y) *
          (signVal b * chi ℝ S fun _ => b) := by
    rw [noiseOp_eq_sum, mul_sum]
    refine sum_congr rfl fun S _ => ?_
    rw [chi_add, chi_add]
    ring
  calc hastadAcceptance δ f
      = 1 / 2 + 1 / 2 * 𝔼 x, 𝔼 y, 𝔼 b : Bool,
          F x * F y * signVal b * noiseOp (1 - δ) F (x + y + fun _ => b) := by
        simp only [hastadAcceptance, hind, noiseOp_add, noiseOp_const, noiseOp_const_mul,
          expect_add_distrib, ← mul_expect, Fintype.expect_const, mul_assoc]
        rfl
    _ = 1 / 2 + 1 / 2 * ∑ S, (1 - δ) ^ #S * fourierCoeff F S * fourierCoeff F S *
          fourierCoeff F S * (if Odd #S then 1 else 0) := by
        simp only [hterm, expect_sum_comm, ← mul_expect, ← expect_mul,
          expect_signVal_mul_chi_const]
        rfl
    _ = _ := by
        rw [sum_filter]
        congr 2
        refine sum_congr rfl fun S _ => ?_
        split_ifs <;> ring

/-- **The acceptance probability of the Odd BLR test** [O'Donnell, Proposition 7.46][ODonnell2014]:
reading `f` as signs, the test accepts with probability `1/2 + 1/2 ∑_{|S| odd} F̂(S)³`. -/
theorem oddBlrAcceptance_eq_sum (f : (ι → Bool) → Bool) :
    oddBlrAcceptance f = 1 / 2 + 1 / 2 *
      ∑ S with Odd #S, fourierCoeff (fun x => signVal (f x)) S ^ 3 := by
  simp only [← hastadAcceptance_zero, hastadAcceptance_eq_sum, sub_zero, one_pow, one_mul]

/-- **The Odd BLR test accepts with probability at most `1/2 + 1/2 M`** for any nonnegative bound
`M` on the odd Fourier coefficients [O'Donnell, Proposition 7.46][ODonnell2014]. The book states
this for `M = max_{|S| odd} F̂(S)`, which needs `M ≥ 0`: for the NAND of two bits both odd
coefficients are `-1/2`, and the test accepts with probability `3/8`. -/
theorem oddBlrAcceptance_le_of_fourierCoeff_le {f : (ι → Bool) → Bool} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ S : Finset ι, Odd #S → fourierCoeff (fun x => signVal (f x)) S ≤ M) :
    oddBlrAcceptance f ≤ 1 / 2 + 1 / 2 * M := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hsum :
      ∑ S with Odd #S, fourierCoeff F S ^ 3 ≤ M * ∑ S with Odd #S, fourierCoeff F S ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun S hS => ?_
    rw [pow_succ, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM S (mem_filter.1 hS).2) (sq_nonneg _)
  have hW := mul_le_of_le_one_right hM0
    (sum_fourierCoeff_sq_signVal_le_one f {S | Odd #S})
  rw [oddBlrAcceptance_eq_sum]
  linarith

/-- **Håstad's test on parities**: a parity on `S` is accepted with probability
`1/2 + 1/2 (1 - δ) ^ |S|` if `|S|` is odd, and `1/2` if `|S|` is even. -/
theorem hastadAcceptance_parityOn (δ : ℝ) (S : Finset ι) :
    hastadAcceptance δ (parityOn S) =
      if Odd #S then 1 / 2 + 1 / 2 * (1 - δ) ^ #S else 1 / 2 := by
  rw [hastadAcceptance_eq_sum]
  split_ifs with h <;> simp [fourierCoeff_signVal_parityOn, h]

/-- **Completeness of Håstad's test** [O'Donnell, Theorem 7.42][ODonnell2014]: dictators are
accepted with probability `1 - δ / 2`. -/
theorem hastadAcceptance_dictator (δ : ℝ) (i : ι) :
    hastadAcceptance δ (fun x : ι → Bool => x i) = 1 - δ / 2 := by
  rw [← funext (parityOn_singleton i), hastadAcceptance_parityOn, card_singleton,
    ite_eq_left odd_one]
  ring

/-- **Soundness of Håstad's test** [O'Donnell, Theorem 7.42 and (7.6)][ODonnell2014]: for
`0 ≤ ε ≤ δ ≤ 1`, if every `(1 - ε)`-stable influence of `f`, read as signs, is at most `ε`, so that
`f` has no `(ε, ε)`-notable coordinates, then the test accepts with probability at most
`1/2 + 1/2 √ε`. Every odd `S` contains some coordinate `i`, so
`((1 - δ) ^ |S| F̂(S))² ≤ (1 - ε) ^ (|S| - 1) F̂(S)²` is at most `Infᵢ^{(1 - ε)}[F] ≤ ε`, and the
odd weight of `F` is at most one. -/
theorem hastadAcceptance_le_of_stableInfluence_le {δ ε : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hδ : δ ≤ 1) {f : (ι → Bool) → Bool}
    (h : ∀ i, stableInfluence (1 - ε) i (fun x => signVal (f x)) ≤ ε) :
    hastadAcceptance δ f ≤ 1 / 2 + 1 / 2 * √ε := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hterm (S : Finset ι) (hS : S ∈ ({S | Odd #S} : Finset (Finset ι))) :
      (1 - δ) ^ #S * fourierCoeff F S ^ 3 ≤ √ε * fourierCoeff F S ^ 2 := by
    have hodd := (mem_filter.1 hS).2
    obtain ⟨i, hi⟩ := card_pos.1 hodd.pos
    have hsq : ((1 - δ) ^ #S * fourierCoeff F S) ^ 2 ≤ ε := calc
      _ = (1 - δ) ^ (2 * #S) * fourierCoeff F S ^ 2 := by ring
      _ ≤ (1 - ε) ^ (#S - 1) * fourierCoeff F S ^ 2 := by
        gcongr ?_ * _
        calc (1 - δ) ^ (2 * #S) ≤ (1 - δ) ^ (#S - 1) :=
              pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
          _ ≤ (1 - ε) ^ (#S - 1) := by gcongr
      _ ≤ stableInfluence (1 - ε) i F :=
        pow_mul_fourierCoeff_sq_le_stableInfluence (by linarith) hi F
      _ ≤ ε := h i
    calc (1 - δ) ^ #S * fourierCoeff F S ^ 3
        = (1 - δ) ^ #S * fourierCoeff F S * fourierCoeff F S ^ 2 := by ring
      _ ≤ √ε * fourierCoeff F S ^ 2 := by
        gcongr
        exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  have hsum := sum_le_sum hterm
  rw [← mul_sum] at hsum
  have hW := mul_le_of_le_one_right (Real.sqrt_nonneg ε)
    (sum_fourierCoeff_sq_signVal_le_one f {S | Odd #S})
  rw [hastadAcceptance_eq_sum]
  linarith

/-- **Håstad's test accepts with probability at most one** for `0 ≤ δ ≤ 2`, where the noise is a
probability distribution. This gives the soundness clause of Theorem 7.42 with `λ(ε) = 1/2` for
`ε > δ` [O'Donnell, Theorem 7.42][ODonnell2014]. -/
theorem hastadAcceptance_le_one {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 2) (f : (ι → Bool) → Bool) :
    hastadAcceptance δ f ≤ 1 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hterm (S : Finset ι) (_ : S ∈ ({S | Odd #S} : Finset (Finset ι))) :
      (1 - δ) ^ #S * fourierCoeff F S ^ 3 ≤ fourierCoeff F S ^ 2 := by
    have h1 : (1 - δ) ^ #S * fourierCoeff F S ≤ 1 := calc
      _ ≤ |1 - δ| ^ #S * |fourierCoeff F S| := by rw [← abs_pow, ← abs_mul]; exact le_abs_self _
      _ ≤ 1 := (mul_le_mul (pow_le_one₀ (abs_nonneg _) (abs_le.2 ⟨by linarith, by linarith⟩))
        (abs_fourierCoeff_signVal_le_one f S) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    calc (1 - δ) ^ #S * fourierCoeff F S ^ 3
        = (1 - δ) ^ #S * fourierCoeff F S * fourierCoeff F S ^ 2 := by ring
      _ ≤ fourierCoeff F S ^ 2 := mul_le_of_le_one_left (sq_nonneg _) h1
  have hsum := sum_le_sum hterm
  have hW := sum_fourierCoeff_sq_signVal_le_one f {S | Odd #S}
  rw [hastadAcceptance_eq_sum]
  linarith

end Cslib.BitString
