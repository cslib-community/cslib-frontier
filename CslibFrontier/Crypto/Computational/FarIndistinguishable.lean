/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GoldreichLevin.HardCore
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Tactic.PPT

/-!
# Statistically far yet computationally indistinguishable ensembles

Computational indistinguishability is strictly weaker than statistical closeness. Pseudorandom
generators and hard-core predicates both give polynomial-time constructible ensembles that no
efficient test tells apart although they are statistically far apart
[Goldreich2007DraftR4], Section 8.2.3.2 and Exercises 8.7 and 8.8.

* A word function `g` on `n`-bit seeds takes at most `2 ^ n` values, so its output on a uniform seed
  is at statistical distance at least `1 - 2 ^ n / 2 ^ m` from a uniform `m`-bit word
  (`Cslib.Crypto.one_sub_div_le_of_closeTo_generatorEnsemble`). For a generator with stretch
  `ℓ(n) > n` this is at least `1 / 2`.
* If `f` is one-to-one on `n`-bit words, the word `f(x) b(x)` for a uniform `x` determines the
  bit `b(x)`. Replacing that bit by a fair coin therefore moves the distribution by exactly `1 / 2`
  in statistical distance, for every predicate `b`
  (`Cslib.Crypto.closeTo_generatorEnsemble_hardCoreIdeal_iff`).

Polynomial-time constructibility follows [Goldreich2007DraftR4], Section 8.2.3.3: one
probabilistic polynomial-time sampler `S` with `S(1ⁿ)` distributed as the `n`-th member. It is
stated as in `Cslib.Crypto.ComputationallyIndistinguishable.replicate_bind`, by samplers
`ℕ → ProbComp (List Bool)` that are `IsPPTOn encUnary encBits`. Statistical distance is
`Cslib.Probability.CloseTo`: `CloseTo μ ν ε` says the variation distance is at most `ε`. The
headlines prove distance at least `1 / 2` at every `n`. The draft's "statistically far apart"
(Exercise 8.9: distance greater than `1 / p(n)` for a positive polynomial `p` and all large `n`)
follows with `p = 3`.

## Main results

* `Cslib.Crypto.one_sub_div_le_of_closeTo_generatorEnsemble`: the support-size lower bound.
* `Cslib.Crypto.PseudorandomGenerator.exists_far_indistinguishable`: [Goldreich2007DraftR4],
  Exercise 8.7.
* `Cslib.Crypto.closeTo_generatorEnsemble_hardCoreIdeal_iff`: distance exactly `1 / 2` for
  one-to-one `f`.
* `Cslib.Crypto.OneWay.exists_far_indistinguishable_of_injective`: [Goldreich2007DraftR4],
  Exercise 8.8, through the Goldreich–Levin hard core (`GoldreichLevin.padded_hardCore`) of the
  padded function `(x, r) ↦ (f(x), r)`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  r4][Goldreich2007DraftR4], Section 8.2.3 and Exercises 8.7–8.8 (PDF pp. 60–61 and 107,
  printed pp. 324–325 and 371).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM Cslib.Probability
open scoped ENNReal

/-! ### Support size bounds the distance from uniform -/

/-- **A word function of `n`-bit seeds is far from uniform on `m` bits**: its output on a uniform
seed takes at most `2 ^ n` values, so its statistical distance from a uniform `m`-bit word is at
least `1 - 2 ^ n / 2 ^ m`. This is the guideline of [Goldreich2007DraftR4], Exercise 8.7. -/
theorem one_sub_div_le_of_closeTo_generatorEnsemble (generator : List Bool → List Bool)
    (n m : ℕ) {ε : ℝ≥0∞}
    (h : CloseTo (generatorEnsemble generator n) (BitString.uniformList m) ε) :
    1 - 2 ^ n / 2 ^ m ≤ ε := by
  classical
  let image : Finset (List Bool) := Finset.univ.image fun r : Fin n → Bool =>
    generator (List.ofFn r)
  have hreal : (generatorEnsemble generator n).toOuterMeasure image = 1 := by
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro word hword
    rw [generatorEnsemble, BitString.uniformList, PMF.map_comp, PMF.mem_support_map_iff] at hword
    obtain ⟨r, -, rfl⟩ := hword
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ r))
  have hcard : (image.card : ℝ≥0∞) ≤ 2 ^ n := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin n → Bool)))
      (f := fun r => generator (List.ofFn r))
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
    exact_mod_cast h
  have hideal : (BitString.uniformList m).toOuterMeasure image ≤ 2 ^ n / 2 ^ m := by
    refine (BitString.toOuterMeasure_uniformList_finset_le m image).trans ?_
    rw [← mul_div_assoc, mul_one]
    exact ENNReal.div_le_div_right hcard _
  have hclose := h image
  rw [hreal] at hclose
  calc 1 - 2 ^ n / 2 ^ m ≤ 1 - (BitString.uniformList m).toOuterMeasure image :=
        tsub_le_tsub_left hideal 1
    _ ≤ ε := tsub_le_iff_left.2 hclose

/-- The constructible form of a generator ensemble: sample a seed, then evaluate. -/
private theorem eval_map_sampleList (generator : List Bool → List Bool) (n : ℕ) :
    ProbComp.eval (generator <$> BitString.sampleList n) = generatorEnsemble generator n := by
  simp [generatorEnsemble]

/-- **Pseudorandom generators give far yet indistinguishable ensembles**
([Goldreich2007DraftR4], Exercise 8.7): the generator's output on a uniform seed and a uniform word
of the output length have polynomial-time samplers and are computationally indistinguishable, yet
their statistical distance is at least `1 - 2 ^ (n - ℓ(n)) ≥ 1 / 2` at every seed length `n`. -/
theorem PseudorandomGenerator.exists_far_indistinguishable
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ∃ X Y : ℕ → ProbComp (List Bool), IsPPTOn encUnary encBits X ∧ IsPPTOn encUnary encBits Y ∧
      ComputationallyIndistinguishable (fun n => ProbComp.eval (X n))
        (fun n => ProbComp.eval (Y n)) ∧
      ∀ n ε, CloseTo (ProbComp.eval (X n)) (ProbComp.eval (Y n)) ε → 1 / 2 ≤ ε := by
  have hg := h.polyTime
  have hl := h.polyTime_length
  refine ⟨fun n => generator <$> BitString.sampleList n,
    fun n => BitString.sampleList (length n), by ppt, by ppt, ?_, fun n ε hε => ?_⟩
  · simpa only [eval_map_sampleList, BitString.eval_sampleList] using h.indistinguishable
  · simp only [eval_map_sampleList, BitString.eval_sampleList] at hε
    refine le_trans ?_ (one_sub_div_le_of_closeTo_generatorEnsemble generator n (length n) hε)
    have hpow : (2 : ℝ≥0∞) ^ (n + 1) ≤ 2 ^ length n :=
      pow_le_pow_right₀ one_le_two (h.stretch n)
    have hhalf : (2 : ℝ≥0∞) ^ n / 2 ^ length n ≤ 1 / 2 := by
      rw [ENNReal.div_le_iff (by positivity) (by simp), one_div, pow_succ] at *
      calc (2 : ℝ≥0∞) ^ n = 2⁻¹ * (2 ^ n * 2) := by
            rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
              mul_one]
        _ ≤ 2⁻¹ * 2 ^ length n := by gcongr
    calc (1 : ℝ≥0∞) / 2 = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
      _ ≤ 1 - 2 ^ n / 2 ^ length n := tsub_le_tsub_left hhalf 1

/-! ### Hiding one bit of a one-to-one image -/

/-- The ideal hybrid of a hard-core predicate as a mixture over the seed. -/
private theorem hardCoreIdeal_eq_bind (f : List Bool → List Bool) (n : ℕ) :
    hardCoreIdeal f n = (BitString.uniformList n).bind
      (fun seed => (PMF.uniformOfFintype Bool).map (fun bit => f seed ++ [bit])) :=
  rfl

/-- Replacing the appended bit by a fair coin at least halves the probability of every word, so
the two laws are within statistical distance `1 / 2`, for every `f` and predicate. -/
private theorem closeTo_generatorEnsemble_hardCoreIdeal (f : List Bool → List Bool)
    (predicate : List Bool → Bool) (n : ℕ) :
    CloseTo (generatorEnsemble (fun seed => f seed ++ [predicate seed]) n) (hardCoreIdeal f n)
      (1 / 2) := by
  have hhalf : ENNReal.ofReal (1 - 1 / 2) = 2⁻¹ := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos two_pos]
    simp
  have hpoint (word : List Bool) :
      ENNReal.ofReal (1 - 1 / 2) * generatorEnsemble (fun seed => f seed ++ [predicate seed]) n word
        ≤ hardCoreIdeal f n word := by
    rw [hhalf, generatorEnsemble, ← PMF.bind_pure_comp, hardCoreIdeal_eq_bind, PMF.bind_apply,
      PMF.bind_apply, ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun seed => ?_
    rw [mul_left_comm]
    gcongr
    simp only [Function.comp_apply, PMF.pure_apply]
    split_ifs with hword
    · rw [mul_one, PMF.map_apply]
      refine le_trans ?_ (le_tsum _ (predicate seed))
      simp [hword]
    · simp
  have h := (CloseTo.of_le_apply (by norm_num) hpoint).symm
  rwa [show ENNReal.ofReal (1 / 2) = 1 / 2 by
    rw [one_div, ENNReal.ofReal_inv_of_pos two_pos]; simp] at h

/-- **Hiding the bit of a one-to-one image moves the law by exactly `1 / 2`**: if `f` is
one-to-one on `n`-bit words, then `f(x) b(x)` and `f(x) σ`, for a uniform `n`-bit `x` and an
independent fair bit `σ`, are at statistical distance exactly `1 / 2`, for every predicate `b`
([Goldreich2007DraftR4], Exercise 8.8). The word `f(x) b(x)` determines `b(x)`, so the event that
the last bit is the predicate of the preimage has probability `1` and `1 / 2`. -/
theorem closeTo_generatorEnsemble_hardCoreIdeal_iff {f : List Bool → List Bool}
    (predicate : List Bool → Bool) {n : ℕ} (hf : Set.InjOn f {seed | seed.length = n})
    {ε : ℝ≥0∞} :
    CloseTo (generatorEnsemble (fun seed => f seed ++ [predicate seed]) n) (hardCoreIdeal f n) ε ↔
      1 / 2 ≤ ε := by
  refine ⟨fun h => ?_, (closeTo_generatorEnsemble_hardCoreIdeal f predicate n).mono⟩
  let event : Set (List Bool) :=
    {word | ∃ seed, seed.length = n ∧ word = f seed ++ [predicate seed]}
  have hreal : (generatorEnsemble (fun seed => f seed ++ [predicate seed]) n).toOuterMeasure event
      = 1 := by
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro word hword
    rw [generatorEnsemble, PMF.mem_support_map_iff] at hword
    obtain ⟨seed, hseed, rfl⟩ := hword
    exact ⟨seed, BitString.length_of_mem_support_uniformList hseed, rfl⟩
  have hideal : (hardCoreIdeal f n).toOuterMeasure event ≤ 2⁻¹ := by
    rw [hardCoreIdeal_eq_bind, PMF.toOuterMeasure_bind_apply]
    calc ∑' seed, BitString.uniformList n seed *
          ((PMF.uniformOfFintype Bool).map (fun bit => f seed ++ [bit])).toOuterMeasure event
        ≤ ∑' seed, BitString.uniformList n seed * 2⁻¹ := by
          refine tsum_le_tsum fun seed => ?_
          by_cases hseed : seed ∈ (BitString.uniformList n).support
          · gcongr
            rw [PMF.toOuterMeasure_map_apply]
            calc (PMF.uniformOfFintype Bool).toOuterMeasure ((fun bit => f seed ++ [bit]) ⁻¹' event)
                ≤ (PMF.uniformOfFintype Bool).toOuterMeasure {predicate seed} := by
                  refine (PMF.uniformOfFintype Bool).toOuterMeasure.mono fun bit hbit => ?_
                  obtain ⟨other, hother, heq⟩ := hbit
                  obtain ⟨himage, hbit⟩ := List.append_inj' heq rfl
                  have := hf (BitString.length_of_mem_support_uniformList hseed) hother himage
                  subst this
                  simpa using hbit
              _ = 2⁻¹ := by simp
          · rw [(PMF.apply_eq_zero_iff _ _).2 hseed]
            simp
      _ = 2⁻¹ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hclose := h event
  rw [hreal] at hclose
  calc (1 : ℝ≥0∞) / 2 = 1 - 2⁻¹ := by rw [one_div, ENNReal.one_sub_inv_two]
    _ ≤ ε := tsub_le_iff_left.2 (hclose.trans (add_le_add_left hideal ε))

/-- The padded function `(x, r) ↦ (f(x), r)` of a one-to-one `f` is one-to-one on each length. -/
private theorem injOn_paddedFunction {f : List Bool → List Bool} (hf : Function.Injective f)
    (n : ℕ) : Set.InjOn (GoldreichLevin.paddedFunction f) {seed | seed.length = n} := by
  intro seed hseed other hother heq
  simp only [Set.mem_ofPred_eq] at hseed hother
  simp only [GoldreichLevin.paddedFunction, hseed, hother] at heq
  obtain ⟨himage, hrest⟩ := List.append_inj' heq (by simp [hseed, hother])
  rw [← List.take_append_drop (n / 2) seed, ← List.take_append_drop (n / 2) other, hf himage,
    hrest]

/-- **One-to-one one-way functions give far yet indistinguishable ensembles**
([Goldreich2007DraftR4], Exercise 8.8): for a one-to-one one-way `f`, the padded function
`g(x, r) = (f(x), r)` is one-to-one with the Goldreich–Levin hard core `b(x, r) = ⟨x, r⟩`
([Goldreich2007DraftR4], Theorem 7.7; `GoldreichLevin.padded_hardCore`). The ensembles
`g(Uₙ) b(Uₙ)` and `g(Uₙ) U₁` have polynomial-time samplers and are computationally
indistinguishable, yet at statistical distance exactly `1 / 2` at every `n`. -/
theorem OneWay.exists_far_indistinguishable_of_injective {f : List Bool → List Bool}
    (hf : OneWay f) (hinj : Function.Injective f) :
    ∃ X Y : ℕ → ProbComp (List Bool), IsPPTOn encUnary encBits X ∧ IsPPTOn encUnary encBits Y ∧
      ComputationallyIndistinguishable (fun n => ProbComp.eval (X n))
        (fun n => ProbComp.eval (Y n)) ∧
      ∀ n ε, CloseTo (ProbComp.eval (X n)) (ProbComp.eval (Y n)) ε ↔ 1 / 2 ≤ ε := by
  have hg := GoldreichLevin.polyTime_paddedFunction hf.polyTime
  have hb := GoldreichLevin.polyTime_paddedPredicate
  have hideal (n : ℕ) : ProbComp.eval (do
      let seed ← BitString.sampleList n
      let bit ← ProbComp.uniform Bool
      return GoldreichLevin.paddedFunction f seed ++ [bit]) =
        hardCoreIdeal (GoldreichLevin.paddedFunction f) n := by
    simp [hardCoreIdeal_eq_bind, PMF.map, Function.comp_def]
  refine ⟨fun n => (fun seed => GoldreichLevin.paddedFunction f seed ++
      [GoldreichLevin.paddedPredicate seed]) <$> BitString.sampleList n,
    fun n => do
      let seed ← BitString.sampleList n
      let bit ← ProbComp.uniform Bool
      return GoldreichLevin.paddedFunction f seed ++ [bit], by ppt, by ppt, ?_, fun n ε => ?_⟩
  · simpa only [eval_map_sampleList, hideal] using
      (GoldreichLevin.padded_hardCore hf).indistinguishable
  · simp only [eval_map_sampleList, hideal]
    exact closeTo_generatorEnsemble_hardCoreIdeal_iff _ (injOn_paddedFunction hinj n)

end Cslib.Crypto
