/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.AverageCase.Ensemble
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Counting
import CslibFrontier.Computability.Complexity.Classes.Counting.OracleSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Probability.BitString
import CslibFrontier.Tactic.PolyTime

/-!
# Samplable ensembles that are not computable unless `#P` is easy

A function `f` in `#P` on words, `f x = #{w ∈ {0,1}^{p(|x|)} : V(x, w)}` for a polynomial-time
verifier `V`, gives a polynomial-time samplable ensemble: on length `m + 1`, draw `x` uniformly
from `{0,1}^m` and `w` uniformly from `{0,1}^{p(m)}`, and output `x` followed by the bit `V(x, w)`.
The word `x ++ [true]` then has probability `f x / 2^{m + p(m)}`, and it immediately follows
`x ++ [false]` among the words of length `m + 1`, so this probability is the difference of two
values of the cumulative distribution. If the ensemble were polynomial-time computable, `f` would
be computable in polynomial time.

Ensembles, polynomial-time computability (`Cslib.Complexity.Ensemble.PComp`, an exact rational
cumulative distribution) and polynomial-time samplability (`Cslib.Complexity.Ensemble.PSamp`, an
exact strict-PPT sampler given the length in unary) are those of
`CslibFrontier.Computability.Complexity.Classes.AverageCase.Ensemble`. Functions in `#P` are
`Cslib.Complexity.SharpP encBits`, functions on words with binary output, and the class `P^#P` is
`Cslib.Complexity.PWithSharpPOracle`.

## Main results

* `Cslib.Complexity.Ensemble.exists_pSamp_not_pComp_of_not_SharpP_subset`: if some function in
  `#P` is not computable in polynomial time, some polynomial-time samplable ensemble is not
  polynomial-time computable [Goldreich, Exercise 10.26][Goldreich2007DraftR5].
* `Cslib.Complexity.Ensemble.exists_pSamp_not_pComp_of_P_ne_PWithSharpPOracle`: the same
  conclusion from `P ≠ P^#P` [Arora and Barak, Chapter 15, Exercise 4][AroraBarak07], stated for
  ensembles rather than for the single distributions on `{0,1}*` of the source.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, Chapters 9–10 (April 2007
  draft)][Goldreich2007DraftR5]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (2007 web
  draft)][AroraBarak07]
* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
-/

public section

namespace Cslib.Complexity

open scoped ENNReal
open Turing.MultiTapeTM

namespace Ensemble

/-- The cumulative distribution at `x ++ [true]` is the one at its predecessor `x ++ [false]`
plus the probability of `x ++ [true]`. -/
private theorem cdf_append_true (D : Ensemble) (x : List Bool) :
    D.cdf (x ++ [true]) = D.cdf (x ++ [false]) + D.dist (x.length + 1) (x ++ [true]) := by
  have hval (b : Bool) :
      BitString.binaryValue (x ++ [b]) = 2 * BitString.binaryValue x + b.toNat := by
    rw [BitString.binaryValue_append]
    cases b <;> simp [BitString.binaryValue, mul_comm]
  have hpred : BitString.predWord (x ++ [true]) = x ++ [false] :=
    BitString.binaryValue_injective_of_length_eq (by simp [BitString.length_predWord])
      (by rw [BitString.binaryValue_predWord, hval, hval]; simp)
  rw [cdf_eq_cdfLo_add, cdfLo_eq_cdf_predWord _ (by rw [hval]; simp), hpred, List.length_append,
    List.length_singleton]

/-- From `a / b = c / d + k / N` in `ℝ≥0∞`, with positive denominators, `k` is recovered by
natural-number arithmetic. -/
private theorem eq_div_of_div_eq_div_add_div {a b c d k N : ℕ} (hb : b ≠ 0) (hd : d ≠ 0)
    (hN : N ≠ 0) (h : (a : ℝ≥0∞) / b = c / d + k / N) :
    k = (N * a * d - N * c * b) / (b * d) := by
  have hreal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hd))
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hN))] at hreal
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hreal
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  field_simp at hreal
  have hnat : N * a * d = N * c * b + k * (b * d) := by
    exact_mod_cast (show ((N * a * d : ℕ) : ℝ) = ((N * c * b + k * (b * d) : ℕ) : ℝ) by
      push_cast; linear_combination hreal)
  rw [hnat, Nat.add_sub_cancel_left,
    Nat.mul_div_cancel _ (Nat.mul_pos (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hd))]

variable (V : List Bool × List Bool → Bool) (p : Polynomial ℕ)

/-- The number of seed bits that the counting sampler uses on length `n`. -/
private def seedLength (n : ℕ) : ℕ :=
  n - 1 + p.eval (n - 1)

/-- The word that the counting sampler outputs on length `n` from the seed `r`: the first
`n - 1` seed bits `x`, followed by the verdict of `V` on `x` and the remaining seed bits. -/
private def countingWord (n : ℕ) (r : List Bool) : List Bool :=
  (r.take (n - 1) ++ [V (r.take (n - 1), r.drop (n - 1))]).take n

/-- The counting sampler: on length `n`, run `countingWord` on `seedLength n` fair bits. -/
private noncomputable def countingSampler (n : ℕ) : ProbComp (List Bool) :=
  (fun r => countingWord V n r) <$> BitString.sampleList (seedLength p n)

private theorem length_countingWord {n : ℕ} {r : List Bool} (hr : n - 1 ≤ r.length) :
    (countingWord V n r).length = n := by
  simp only [countingWord, List.length_take, List.length_append, List.length_singleton]
  omega

/-- The ensemble sampled by `countingSampler`. -/
private noncomputable def countingEnsemble : Ensemble where
  dist n := ProbComp.eval (countingSampler V p n)
  length_eq n x hx := by
    simp only [countingSampler, ProbComp.eval_map, BitString.eval_sampleList,
      PMF.support_map, Set.mem_image] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    refine length_countingWord V ?_
    rw [BitString.length_of_mem_support_uniformList hr, seedLength]
    omega

private theorem computableInPolyTime_countingWord
    (hV : ComputableInPolyTime V (encPair encBits encBits) encBool) :
    ComputableInPolyTime (fun q : ℕ × List Bool => countingWord V q.1 q.2)
      (encPair encUnary encBits) encBits := by
  unfold countingWord; fun_prop

/-- The counting ensemble of a polynomial-time verifier is polynomial-time samplable. -/
private theorem pSamp_countingEnsemble
    (hV : ComputableInPolyTime V (encPair encBits encBits) encBool) :
    (countingEnsemble V p).PSamp := by
  refine ⟨countingSampler V p, ?_, fun _ => rfl⟩
  unfold countingSampler
  exact Probability.IsPPTOn.of_seeded (f := fun q : ℕ × List Bool => countingWord V q.1 q.2)
    (by unfold seedLength; fun_prop) (computableInPolyTime_countingWord V hV)

/-- The word `x ++ [true]` has probability `#{w ∈ {0,1}^{p(|x|)} : V(x, w)} / 2^{|x| + p(|x|)}`
under the counting ensemble. -/
private theorem countingEnsemble_dist_append_true (x : List Bool) :
    (countingEnsemble V p).dist (x.length + 1) (x ++ [true]) =
      (acceptCount V x (p.eval x.length) : ℝ≥0∞) / 2 ^ (x.length + p.eval x.length) := by
  classical
  change ProbComp.eval (countingSampler V p (x.length + 1)) (x ++ [true]) = _
  rw [countingSampler, show seedLength p (x.length + 1) = x.length + p.eval x.length by
      simp [seedLength], ProbComp.eval_map, BitString.eval_sampleList,
    BitString.uniformList_map_apply]
  congr 2
  have hiff (r : Fin (x.length + p.eval x.length) → Bool) :
      countingWord V (x.length + 1) (List.ofFn r) = x ++ [true] ↔
        (List.ofFn r).take x.length = x ∧ V (x, (List.ofFn r).drop x.length) = true := by
    simp only [countingWord, Nat.add_sub_cancel]
    rw [List.take_of_length_le (by simp)]
    refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at h2
    rw [h1] at h2
    exact ⟨h1, h2⟩
  simp only [hiff, BitString.card_filter_ofFn_add x.length (p.eval x.length)
    (fun u w => u = x ∧ V (x, w) = true)]
  rw [Finset.sum_eq_single x.get]
  · simp [List.ofFn_get, acceptCount]
  · intro u _ hu
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro w - ⟨h, -⟩
    exact hu (List.ofFn_injective (h.trans (List.ofFn_get x).symm))
  · simp

/-- The count read off a cumulative distribution given as `num / den`: `2^{|x| + p(|x|)}` times
the difference of its values at `x ++ [true]` and at `x ++ [false]`, in natural-number
arithmetic. -/
private def recoveredCount (num den : List Bool → ℕ) (x : List Bool) : ℕ :=
  (2 ^ (x.length + p.eval x.length) * num (x ++ [true]) * den (x ++ [false]) -
      2 ^ (x.length + p.eval x.length) * num (x ++ [false]) * den (x ++ [true])) /
    (den (x ++ [true]) * den (x ++ [false]))

private theorem computableInPolyTime_recoveredCount {num den : List Bool → ℕ}
    (hnum : ComputableInPolyTime num encBits encNat)
    (hden : ComputableInPolyTime den encBits encNat) :
    ComputableInPolyTime (recoveredCount p num den) encBits encNat := by
  have hpow : ComputableInPolyTime (fun x : List Bool => 2 ^ (x.length + p.eval x.length))
      encBits encNat :=
    ComputableInPolyTime.binary_two_pow.comp
      (ComputableInPolyTime.unary_add' .length_bits
        ((ComputableInPolyTime.unary_eval p).comp .length_bits))
  have hmul {f g : List Bool → ℕ} (hf : ComputableInPolyTime f encBits encNat)
      (hg : ComputableInPolyTime g encBits encNat) :
      ComputableInPolyTime (fun x => f x * g x) encBits encNat :=
    ComputableInPolyTime.binary_mul.comp (hf.prod hg)
  have hat {g : List Bool → ℕ} (hg : ComputableInPolyTime g encBits encNat) (b : Bool) :
      ComputableInPolyTime (fun x => g (x ++ [b])) encBits encNat :=
    hg.comp (by fun_prop)
  exact ComputableInPolyTime.binary_div'
    (ComputableInPolyTime.binary_sub' (hmul (hmul hpow (hat hnum true)) (hat hden false))
      (hmul (hmul hpow (hat hnum false)) (hat hden true)))
    (hmul (hat hden true) (hat hden false))

/-- If the cumulative distribution of the counting ensemble is `num / den`, the count of `x` is
`recoveredCount p num den x`. -/
private theorem acceptCount_eq_recoveredCount {num den : List Bool → ℕ}
    (hden0 : ∀ x, den x ≠ 0)
    (hcdf : ∀ x, (countingEnsemble V p).cdf x = (num x : ℝ≥0∞) / den x) (x : List Bool) :
    acceptCount V x (p.eval x.length) = recoveredCount p num den x := by
  refine eq_div_of_div_eq_div_add_div (hden0 _) (hden0 _) (by positivity) ?_
  rw [← hcdf, ← hcdf, cdf_append_true, countingEnsemble_dist_append_true]
  push_cast; rfl

/-- **A computable counting ensemble makes the count easy**: if the counting ensemble of `V` and
`p` is polynomial-time computable, the count `x ↦ #{w ∈ {0,1}^{p(|x|)} : V(x, w)}` is computable
in polynomial time with binary output. -/
private theorem computableInPolyTime_acceptCount_of_pComp (h : (countingEnsemble V p).PComp) :
    ComputableInPolyTime (fun x => acceptCount V x (p.eval x.length)) encBits encNat := by
  obtain ⟨num, den, hnum, hden, hden0, hcdf⟩ := h
  rw [funext (acceptCount_eq_recoveredCount V p hden0 hcdf)]
  exact computableInPolyTime_recoveredCount p hnum hden

/-- **Goldreich, Exercise 10.26**: if some function in `#P` is not computable in polynomial time,
then some polynomial-time samplable ensemble is not polynomial-time computable
[Goldreich, Exercise 10.26][Goldreich2007DraftR5].

`#P` is `SharpP encBits`, the functions on words counting the accepted certificates of exact
polynomial length of a polynomial-time verifier; polynomial-time computability is with binary
output. The ensemble is supported on words of length exactly `n` at index `n`; it is sampled by a
strict-PPT program given `n` in unary (`Ensemble.PSamp`). Its cumulative distribution is not the
ratio of two polynomial-time functions (`Ensemble.PComp`), so in particular it is not given by a
polynomial-time binary fraction. -/
theorem exists_pSamp_not_pComp_of_not_SharpP_subset
    (h : ¬ SharpP encBits ⊆ {f | ComputableInPolyTime f encBits encNat}) :
    ∃ D : Ensemble, D.PSamp ∧ ¬ D.PComp := by
  obtain ⟨f, ⟨p, V, hV, hf⟩, hnot⟩ := Set.not_subset.mp h
  refine ⟨countingEnsemble V p, pSamp_countingEnsemble V p hV, fun hc => hnot ?_⟩
  rw [Set.mem_ofPred_eq, funext hf]
  exact computableInPolyTime_acceptCount_of_pComp V p hc

/-- **Arora–Barak, Chapter 15, Exercise 4**, for ensembles: if `P ≠ P^#P`, then some
polynomial-time samplable ensemble is not polynomial-time computable
[Arora and Barak, Chapter 15, Exercise 4][AroraBarak07].

The source states the exercise for single distributions on `{0,1}*` (Definition 15.12 and §15.1.1
of the draft); here, as in `Cslib.Complexity.Ensemble`, distributions are ensembles indexed by the
input length [Bogdanov and Trevisan, §2.1][BogdanovTrevisan2006]. The hypothesis is for any
instance encoding `enc`; `P^#P` is `PWithSharpPOracle`. If every function in `#P` on words were
computable in polynomial time, `P^#P` would collapse to `P`
(`Cslib.Complexity.PWithSharpPOracle_subset_P_of_SharpP_subset`), so the claim follows from
`Cslib.Complexity.Ensemble.exists_pSamp_not_pComp_of_not_SharpP_subset`. -/
theorem exists_pSamp_not_pComp_of_P_ne_PWithSharpPOracle {α : Type} {enc : α ↪ List Bool}
    (h : P enc ≠ PWithSharpPOracle enc) :
    ∃ D : Ensemble, D.PSamp ∧ ¬ D.PComp :=
  exists_pSamp_not_pComp_of_not_SharpP_subset fun hsub =>
    h (P_subset_PWithSharpPOracle.antisymm (PWithSharpPOracle_subset_P_of_SharpP_subset hsub))

end Ensemble

end Cslib.Complexity
