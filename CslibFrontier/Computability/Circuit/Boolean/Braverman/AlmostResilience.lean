/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Braverman.Resilience
public import CslibFrontier.Computability.Circuit.Boolean.Tribes
public import CslibFrontier.Probability.SmallBias.AlmostIndependent
import CslibFrontier.Probability.PMF

/-!
# Resilient functions and `AC⁰` circuits under almost `k`-wise independence

Using Fourier smoothing (`Cslib.BitString.exists_isKWiseIndependent_dist_le_of_isKWiseSmallBias`),
this module extends Braverman's theorem and the bounded-independence resilience transfer of
`CslibFrontier.Computability.Circuit.Boolean.Braverman.Resilience`
[Chattopadhyay–Zuckerman, Theorem 4.1][ChattopadhyayZuckerman2019] from exact `t`-wise
independence to `t`-wise `γ`-biased and almost `t`-wise independent distributions, resolving the
gap noted in the docstring of `Braverman.Resilience`.

If `D` is `t`-wise `γ`-biased on `n` bits (or every `t`-marginal is within statistical distance
`γ` of uniform), smoothing produces an exact `t`-wise independent distribution `D'` within
statistical distance `n ^ t * γ` (respectively `2 * n ^ t * γ`), transferring both the bias bound
and coalition influence of monotone `AC⁰` circuits (with concrete instances for
`Cslib.BitString.tribes`). Note that Chattopadhyay and Zuckerman use the tighter Alon–Goldreich–
Mansour smoothing / Tal's Braverman exponent, which are not claimed here; these bounds use
Fourier smoothing together with the closed-form independence bound of `Braverman.Fooling`.

## Main results

* `Cslib.Circuits.Boolean.Braverman.fools_bitVal_of_isKWiseSmallBias`: `t`-wise `γ`-biased
  distributions fool constant-depth circuits up to `2 ^ (-p) + n ^ t * γ`.
* `Cslib.Circuits.Boolean.Braverman.abs_sum_bitVal_sub_half_le_of_isKWiseSmallBias`: bias bound
  under `t`-wise `γ`-bias.
* `Cslib.Circuits.Boolean.Braverman.coalitionInfluence_le_of_isKWiseSmallBias`,
  `Cslib.Circuits.Boolean.Braverman.coalitionInfluence_le_of_dist_map_restrict_le`: coalition
  influence of monotone `AC⁰` circuits under almost `t`-wise independence.
* `Cslib.Circuits.Boolean.Braverman.coalitionInfluence_tribes_le_of_isKWiseSmallBias`,
  `Cslib.Circuits.Boolean.Braverman.abs_sum_bitVal_tribes_sub_half_le_of_isKWiseSmallBias`:
  almost `t`-wise independent Tribes bounds.

## References

* [E. Chattopadhyay, D. Zuckerman, *Explicit two-source extractors and resilient
  functions*][ChattopadhyayZuckerman2019]
* [M. Braverman, *Polylogarithmic independence fools `AC⁰` circuits*][Braverman2010]
* [N. Alon, O. Goldreich, J. Håstad, R. Peralta, *Simple constructions of almost `k`-wise
  independent random variables*][AlonGoldreichHastadPeralta1992]
-/

public section

namespace Cslib.Circuits.Boolean.Braverman

open Finset BitString Probability Cslib.Probability.PMF
open scoped BigOperators

variable {n : ℕ}

private theorem bitVal_nonneg (b : Bool) : 0 ≤ bitVal ℝ b := by
  cases b <;> norm_num

private theorem bitVal_le_one (b : Bool) : bitVal ℝ b ≤ 1 := by
  cases b <;> norm_num

/-- **Almost `t`-wise independence fools `AC⁰`**: a `t`-wise `γ`-biased distribution with
`t ≥ (64 * p) ^ ((2 * d + 3) * (d + 7) + 1)` fools a circuit of size at most `2 ^ p`, fan-in less
than `2 ^ p`, and depth at most `d` with error `2 ^ (-p) + n ^ t * γ`. -/
theorem fools_bitVal_of_isKWiseSmallBias {D : PMF (BitString n)} {d p t : ℕ} {γ : ℝ}
    (hp : 1 ≤ p) (C : Circuit Unbounded.signature n 1)
    (hfan : C.FanInAtMost (2 ^ p - 1)) (hsize : C.size ≤ 2 ^ p) (hd : C.depth ≤ d)
    (ht : (64 * p) ^ ((2 * d + 3) * (d + 7) + 1) ≤ t)
    (hγ : 0 ≤ γ) (hD : IsKWiseSmallBias t γ D) :
    Fools D (1 / 2 ^ p + (n : ℝ) ^ t * γ)
      fun x => bitVal ℝ (C.eval Unbounded.interpretation x 0) := by
  obtain ⟨D', hD'_ind, hdist⟩ := exists_isKWiseIndependent_dist_le_of_isKWiseSmallBias hγ hD
  rw [Fintype.card_fin] at hdist
  have hfools := fools_of_isKWiseIndependent hp C hfan hsize hd ht hD'_ind
  unfold Fools at hfools ⊢
  have hdiff := abs_sum_mul_sub_le_dist D D'
    (fun x => bitVal ℝ (C.eval Unbounded.interpretation x 0))
    (fun _ => bitVal_nonneg _) (fun _ => bitVal_le_one _)
  have htri := abs_sub_le
    (∑ x, (D x).toReal * bitVal ℝ (C.eval Unbounded.interpretation x 0))
    (∑ x, (D' x).toReal * bitVal ℝ (C.eval Unbounded.interpretation x 0))
    (𝔼 x, bitVal ℝ (C.eval Unbounded.interpretation x 0))
  linarith

/-- **Bias under almost `t`-wise independence**
[Chattopadhyay–Zuckerman, Theorem 4.1][ChattopadhyayZuckerman2019]: extension of
`abs_sum_bitVal_sub_half_le_of_isKWiseIndependent` to `t`-wise `γ`-biased distributions via
Fourier smoothing. -/
theorem abs_sum_bitVal_sub_half_le_of_isKWiseSmallBias {D : PMF (BitString n)} {d p t : ℕ}
    {ε₁ γ : ℝ} (hp : 1 ≤ p) (C : Circuit Unbounded.signature n 1)
    (hfan : C.FanInAtMost (2 ^ p - 1)) (hsize : C.size ≤ 2 ^ p) (hd : C.depth ≤ d)
    (hbias : |𝔼 x, bitVal ℝ (C.eval Unbounded.interpretation x 0) - 1 / 2| ≤ ε₁)
    (ht : (64 * p) ^ ((2 * d + 3) * (d + 7) + 1) ≤ t)
    (hγ : 0 ≤ γ) (hD : IsKWiseSmallBias t γ D) :
    |∑ x, (D x).toReal * bitVal ℝ (C.eval Unbounded.interpretation x 0) - 1 / 2| ≤
      ε₁ + 1 / 2 ^ p + (n : ℝ) ^ t * γ := by
  have hf := fools_bitVal_of_isKWiseSmallBias hp C hfan hsize hd ht hγ hD
  unfold Fools at hf
  have htri := abs_sub_le
    (∑ x, (D x).toReal * bitVal ℝ (C.eval Unbounded.interpretation x 0))
    (𝔼 x, bitVal ℝ (C.eval Unbounded.interpretation x 0)) (1 / 2)
  linarith

/-- **Coalition influence under `t`-wise `γ`-bias**
[Chattopadhyay–Zuckerman, Theorem 4.1][ChattopadhyayZuckerman2019]: extends
`coalitionInfluence_le_of_independence_le` from exact `t`-wise independence to `t`-wise `γ`-biased
distributions via Fourier smoothing. -/
theorem coalitionInfluence_le_of_isKWiseSmallBias {D : PMF (BitString n)} {d p t : ℕ} {ε₂ γ : ℝ}
    (hp : 2 ≤ p) (C : Circuit Unbounded.signature n 1)
    (hmono : Monotone fun x => C.eval Unbounded.interpretation x 0)
    (hfan : C.FanInAtMost (2 ^ p - 1)) (hsize : 2 * C.size + 6 ≤ 2 ^ p) (hd : C.depth ≤ d)
    (Q : Finset (Fin n))
    (hQ : coalitionInfluence (PMF.uniformOfFintype (BitString n)) Q
      (fun x => C.eval Unbounded.interpretation x 0) ≤ ε₂)
    (ht : (64 * p) ^ ((2 * d + 9) * (d + 10) + 1) ≤ t)
    (hγ : 0 ≤ γ) (hD : IsKWiseSmallBias t γ D) :
    coalitionInfluence D Q (fun x => C.eval Unbounded.interpretation x 0) ≤
      ε₂ + 1 / 2 ^ p + (n : ℝ) ^ t * γ := by
  obtain ⟨D', hD'_ind, hdist⟩ := exists_isKWiseIndependent_dist_le_of_isKWiseSmallBias hγ hD
  rw [Fintype.card_fin] at hdist
  have he : (2 * (d + 3) + 3) * (d + 3 + 7) + 1 = (2 * d + 9) * (d + 10) + 1 := by ring
  have hi := independence_le (by omega : 1 ≤ p) (d + 3)
  rw [he] at hi
  have hD' := coalitionInfluence_le_of_independence_le hp C hmono hfan hsize hd Q hQ
    (hi.trans ht) hD'_ind
  have hshift := abs_sum_mul_sub_le_dist D D'
    (fun x => if IsUndetermined Q (fun y => C.eval Unbounded.interpretation y 0) x then 1 else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => by split_ifs <;> norm_num)
  change |coalitionInfluence D Q _ - coalitionInfluence D' Q _| ≤ dist D D' at hshift
  linarith [(abs_le.mp hshift).2]

/-- **Coalition influence under almost `t`-wise independence (marginal form)**: if every
`t`-subset marginal of `D` is within statistical distance `γ` of uniform, then coalition influence
moves by at most `2 ^ (-p) + 2 * n ^ t * γ`. -/
theorem coalitionInfluence_le_of_dist_map_restrict_le {D : PMF (BitString n)} {d p t : ℕ}
    {ε₂ γ : ℝ} (hp : 2 ≤ p) (C : Circuit Unbounded.signature n 1)
    (hmono : Monotone fun x => C.eval Unbounded.interpretation x 0)
    (hfan : C.FanInAtMost (2 ^ p - 1)) (hsize : 2 * C.size + 6 ≤ 2 ^ p) (hd : C.depth ≤ d)
    (Q : Finset (Fin n))
    (hQ : coalitionInfluence (PMF.uniformOfFintype (BitString n)) Q
      (fun x => C.eval Unbounded.interpretation x 0) ≤ ε₂)
    (ht : (64 * p) ^ ((2 * d + 9) * (d + 10) + 1) ≤ t)
    (hD : ∀ T : Finset (Fin n), #T ≤ t →
      dist (D.map T.restrict) (PMF.uniformOfFintype (T → Bool)) ≤ γ) :
    coalitionInfluence D Q (fun x => C.eval Unbounded.interpretation x 0) ≤
      ε₂ + 1 / 2 ^ p + 2 * (n : ℝ) ^ t * γ := by
  have hγ : 0 ≤ γ := dist_nonneg.trans (hD ∅ (Nat.zero_le t))
  have h := coalitionInfluence_le_of_isKWiseSmallBias hp C hmono hfan hsize hd Q hQ ht
    (mul_nonneg zero_le_two hγ) (isKWiseSmallBias_of_dist_map_restrict_le hD)
  exact h.trans_eq (by ring)

/-- **Tribes coalition influence under `t`-wise `γ`-bias**: extension of
`isKWiseResilient_tribes` to almost `t`-wise independent distributions. -/
theorem coalitionInfluence_tribes_le_of_isKWiseSmallBias {w s p q t : ℕ}
    {D : PMF (BitString (s * w))} {γ : ℝ} (hp : 2 ≤ p) (hs : 2 * s + 8 ≤ 2 ^ p)
    (hw : w < 2 ^ p) (ht : (64 * p) ^ 157 ≤ t) (Q : Finset (Fin (s * w))) (hQ : #Q = q)
    (hγ : 0 ≤ γ) (hD : IsKWiseSmallBias t γ D) :
    coalitionInfluence D Q (tribes w s) ≤ 2 ^ q / 2 ^ w + 1 / 2 ^ p + (s * w : ℝ) ^ t * γ := by
  obtain ⟨D', hD'_ind, hdist⟩ := exists_isKWiseIndependent_dist_le_of_isKWiseSmallBias hγ hD
  rw [Fintype.card_fin] at hdist
  have hD' := isKWiseResilient_tribes hp hs hw ht Q hQ D' hD'_ind
  have hshift := abs_sum_mul_sub_le_dist D D'
    (fun x => if IsUndetermined Q (tribes w s) x then 1 else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => by split_ifs <;> norm_num)
  change |coalitionInfluence D Q (tribes w s) - coalitionInfluence D' Q (tribes w s)| ≤
    dist D D' at hshift
  have hcast : ((s * w : ℕ) : ℝ) ^ t * γ = (s * w : ℝ) ^ t * γ := by push_cast; rfl
  rw [hcast] at hdist
  linarith [(abs_le.mp hshift).2]

/-- **Tribes bias under `t`-wise `γ`-bias**: extension of `abs_sum_bitVal_tribes_sub_half_le`
to almost `t`-wise independent distributions. -/
theorem abs_sum_bitVal_tribes_sub_half_le_of_isKWiseSmallBias {w s p t : ℕ}
    {D : PMF (BitString (s * w))} {γ : ℝ} (hp : 1 ≤ p) (hs : s < 2 ^ p) (hw : w < 2 ^ p)
    (h₁ : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ s) (h₂ : (1 - (2⁻¹ : ℝ) ^ w) ^ (s + 1) < 1 / 2)
    (ht : (64 * p) ^ 64 ≤ t) (hγ : 0 ≤ γ) (hD : IsKWiseSmallBias t γ D) :
    |∑ x, (D x).toReal * bitVal ℝ (tribes w s x) - 1 / 2| ≤
      2⁻¹ ^ w + 1 / 2 ^ p + (s * w : ℝ) ^ t * γ := by
  obtain ⟨D', hD'_ind, hdist⟩ := exists_isKWiseIndependent_dist_le_of_isKWiseSmallBias hγ hD
  rw [Fintype.card_fin] at hdist
  have hD' := abs_sum_bitVal_tribes_sub_half_le hp hs hw h₁ h₂ ht hD'_ind
  have hshift := abs_sum_mul_sub_le_dist D D' (fun x => bitVal ℝ (tribes w s x))
    (fun _ => bitVal_nonneg _) (fun _ => bitVal_le_one _)
  have htri := abs_sub_le
    (∑ x, (D x).toReal * bitVal ℝ (tribes w s x))
    (∑ x, (D' x).toReal * bitVal ℝ (tribes w s x)) (1 / 2)
  have hcast : ((s * w : ℕ) : ℝ) ^ t * γ = (s * w : ℝ) ^ t * γ := by push_cast; rfl
  rw [hcast] at hdist
  linarith

end Cslib.Circuits.Boolean.Braverman
