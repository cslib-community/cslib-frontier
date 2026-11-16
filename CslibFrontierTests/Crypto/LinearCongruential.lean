/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.PRG.LinearCongruential
import Cslib.Crypto.Primitives.PRG.Asymptotic
import Cslib.Probability.PMF
import Mathlib.Tactic.NormNum

/-!
# Tests for linear congruential generator distinguisher and seed search
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.LinearCongruential

open Cslib.Crypto.PRG Cslib.Crypto.PRG.LinearCongruential Turing.MultiTapeTM
open scoped NNReal

/-- A small generator with multiplier coprime to the modulus: `q = 16`, `a = 5`, `b = 3`,
`w = 4`. -/
def small : LinearCongruential := ⟨16, 5, 3, 4⟩

instance : NeZero small.q := ⟨by decide⟩
instance : NeZero java8.q := ⟨by decide⟩

/-! ### Values -/

example : small.next 7 = 6 := by decide
example : small.prev 6 = 7 := by
  unfold prev BinaryGcd.modInv
  decide

example : ∀ s < 16, small.prev (small.next s) = s := fun _ hs => small.prev_next (by decide) hs

example : small.test 1 6 = true ∧ small.test 2 6 = false := by
  unfold test prev BinaryGcd.modInv
  decide

/-- Known output on state `25214903917` under `java8`: one iteration gives `205749139540596`,
whose top 26 bits are `49054417`. -/
example : java8.next 25214903917 = 205749139540596 ∧
    java8.next 25214903917 / java8.w = 49054417 := by decide

/-! ### The advantage of the test -/

example : small.generator.advantage (fun y => PMF.pure (small.test y.1 y.2)) = 3 / 4 := by
  rw [advantage_generator_test small (by decide)]
  norm_num [small]

example : java8.generator.advantage (fun y => PMF.pure (java8.test y.1 y.2)) = 1 - 1 / 2 ^ 26 := by
  rw [advantage_generator_test java8 (by decide)]
  norm_num [java8]

/-- `G_lcg` is not secure against a class of tests that contains the test. -/
example (P : LinearCongruential) [NeZero P.q] (ha : P.a.Coprime P.q)
    {Admissible : Adversary (Fin ((P.q - 1) / P.w + 1) × Fin P.q) → Prop} {ε : ℝ≥0}
    (hA : Admissible fun y => PMF.pure (P.test y.1 y.2))
    (hε : (ε : ℝ) < 1 - 1 / (((P.q - 1) / P.w + 1 : ℕ) : ℝ)) :
    ¬ P.generator.Secure Admissible ε := fun h => by
  have := h _ hA
  rw [advantage_generator_test P ha] at this
  linarith

/-- Any family of linear congruential generators with `0 < w n < q n` and `a n` coprime to `q n`
is insecure against any adversary family class admitting the book's test. -/
example (P : ℕ → LinearCongruential) [∀ n, NeZero (P n).q] (ha : ∀ n, (P n).a.Coprime (P n).q)
    (hw : ∀ n, 0 < (P n).w) (hwq : ∀ n, (P n).w < (P n).q)
    {Admissible : (∀ n, Adversary (Fin (((P n).q - 1) / (P n).w + 1) × Fin (P n).q)) → Prop}
    (hA : Admissible fun n y => PMF.pure ((P n).test y.1 y.2)) :
    ¬ Family.Secure (fun n => (P n).generator) Admissible := by
  have hfun : (fun n => (P n).generator.rangeAdversary) =
      fun n y => PMF.pure ((P n).test y.1 y.2) :=
    funext fun n => funext fun y => congrArg PMF.pure ((P n).rangeTest_generator (ha n) y)
  refine Family.not_secure_of_two_mul_card_le _ (hfun ▸ hA)
    (Filter.Eventually.of_forall fun n => ?_)
  have := Nat.div_pos (Nat.le_sub_one_of_lt (hwq n)) (hw n)
  simp only [Fintype.card_prod, Fintype.card_fin]
  nlinarith

/-- The advantage is at least `1 / 2` when `0 < w < q`. -/
example (P : LinearCongruential) [NeZero P.q] (ha : P.a.Coprime P.q) (hw : 0 < P.w)
    (hwq : P.w < P.q) :
    1 / 2 ≤ P.generator.advantage (fun y => PMF.pure (P.test y.1 y.2)) := by
  rw [advantage_generator_test P ha]
  have h : 2 ≤ (P.q - 1) / P.w + 1 := by
    have := Nat.div_pos (Nat.le_sub_one_of_lt hwq) hw
    lia
  have h' : (2 : ℝ) ≤ (((P.q - 1) / P.w + 1 : ℕ) : ℝ) := by exact_mod_cast h
  have : 1 / (((P.q - 1) / P.w + 1 : ℕ) : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h'
  linarith

/-- The advantage is `0` when `w = 0` or `q ≤ w`: then `R` has one element. -/
example (P : LinearCongruential) [NeZero P.q] (ha : P.a.Coprime P.q) (h : P.w = 0 ∨ P.q ≤ P.w) :
    P.generator.advantage (fun y => PMF.pure (P.test y.1 y.2)) = 0 := by
  rw [advantage_generator_test P ha]
  have h' : (P.q - 1) / P.w = 0 := by
    rcases h with h | h
    · simp [h]
    · exact Nat.div_eq_of_lt (by have := NeZero.pos P.q; lia)
  simp [h']

/-! ### Difference from the book: `w = q` -/

/-- `w = q`, which the book's "`w ≤ q`" allows: `R` has one element. -/
def flat : LinearCongruential := ⟨4, 1, 0, 4⟩

instance : NeZero flat.q := ⟨by decide⟩

/-- With `w = q` the test has advantage `0`. -/
example : flat.generator.advantage (fun y => PMF.pure (flat.test y.1 y.2)) = 0 := by
  rw [advantage_generator_test flat (by decide)]
  norm_num [flat]

/-- With `w = q` no test has any advantage: this `G_lcg` is a bijection, so it is not insecure. -/
example (A : Adversary (Fin ((flat.q - 1) / flat.w + 1) × Fin flat.q)) :
    flat.generator.advantage A = 0 := by
  have hb : Function.Bijective flat.generator := by decide
  have hu : flat.generator.outputDist = Cslib.Probability.PMF.uniformOfFintype _ :=
    Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.ofBijective _ hb)
  exact le_antisymm (flat.generator.secure_zero_of_outputDist_eq hu (fun _ => True) A trivial)
    (flat.generator.advantage_nonneg A)

/-! ### Probe: `a` coprime to `q` -/

/-- `a = 2` is not coprime to `q = 4`. -/
def even : LinearCongruential := ⟨4, 2, 0, 1⟩

instance : NeZero even.q := ⟨by decide⟩

/-- Without coprimality no function recovers the state: the states `0` and `2` have the same
successor. -/
example : ¬ ∃ f : ℕ → ℕ, ∀ s < 4, f (even.next s) = s := fun ⟨f, h⟩ => by
  have h₀ := h 0 (by decide)
  have h₂ := h 2 (by decide)
  rw [show even.next 2 = even.next 0 by decide, h₀] at h₂
  exact absurd h₂ (by decide)

/-- Without coprimality the advantage formula itself fails: on `even`, `test` has advantage `0`
rather than `1 - 1 / |R| = 3 / 4`. -/
example : even.generator.advantage (fun y => PMF.pure (even.test y.1 y.2)) = 0 ∧
    even.generator.advantage (fun y => PMF.pure (even.test y.1 y.2)) ≠
      1 - 1 / (((even.q - 1) / even.w + 1 : ℕ) : ℝ) := by
  have hc₁ : (Finset.univ.filter fun s : Fin even.q =>
      true = even.test (even.generator s).1 (even.generator s).2).card = 1 := by
    unfold generator test prev BinaryGcd.modInv
    decide
  have hc₂ : (Finset.univ.filter fun y : Fin ((even.q - 1) / even.w + 1) × Fin even.q =>
      true = even.test y.1 y.2).card = 4 := by
    unfold test prev BinaryGcd.modInv
    decide
  have hreal :
      (even.generator.realExperiment (fun y => PMF.pure (even.test y.1 y.2)) true).toReal =
        1 / 4 := by
    simp only [Generator.realExperiment, Generator.outputDist, PMF.bind_map, Function.comp_def,
      PMF.bind_apply, PMF.pure_apply, Cslib.Probability.PMF.uniformOfFintype_apply, tsum_fintype,
      mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.sum_const, hc₁, one_nsmul,
      Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    norm_num [even]
  have hideal :
      (Generator.idealExperiment
          (fun y : Fin ((even.q - 1) / even.w + 1) × Fin even.q =>
            PMF.pure (even.test y.1 y.2)) true).toReal = 1 / 4 := by
    simp only [Generator.idealExperiment, PMF.bind_apply, PMF.pure_apply,
      Cslib.Probability.PMF.uniformOfFintype_apply, tsum_fintype,
      mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.sum_const, hc₂,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    norm_num [even]
  have hadv : even.generator.advantage (fun y => PMF.pure (even.test y.1 y.2)) = 0 := by
    simp [Generator.advantage, hreal, hideal]
  refine ⟨hadv, ?_⟩
  rw [hadv]
  norm_num [even]

/-! ### The search -/

/-- The search for a Java 8 seed tries `2 ^ 22 = 4194304` candidates, "about four million". -/
example : java8.w = 4194304 ∧ java8.q / java8.w = 2 ^ 26 := by decide

/-- On the small generator the search finds every seed. Here two outputs do not determine the seed
(`0` and `3` share them), so `seedSearch_eq` does not apply: its hypothesis is sufficient, not
necessary, and the third output is what separates the candidates. -/
example : ∀ s < 16, small.seedSearch (s / small.w) (small.next s / small.w)
    (small.next (small.next s) / small.w) = s := by decide

example : small.next 0 / small.w = small.next 3 / small.w ∧ (0 : ℕ) / small.w = 3 / small.w := by
  decide

/-- **Prediction** ([BonehShoup2023], p. 71): from the first three outputs of the Java 8 generator,
every later output. -/
example {s : ℕ} (hs : s < java8.q) (n : ℕ) :
    java8.next^[n] (java8.seedSearch (s / java8.w) (java8.next s / java8.w)
      (java8.next (java8.next s) / java8.w)) / java8.w = java8.next^[n] s / java8.w := by
  rw [seedSearch_java8 hs]

/-! ### Probe: the hypotheses of `seedSearch_eq` -/

/-- A counter: `a = 1`, `b = 1`, with `q = 16` and `w = 4`. It meets every condition the book
puts on the parameters. -/
def counter : LinearCongruential := ⟨16, 1, 1, 4⟩

/-- The seeds `0` and `1` of the counter have the same first three outputs, and the search returns
`1` on the outputs of `0`: without `hshort` the search need not find the seed. -/
example : counter.seedSearch (0 / counter.w) (counter.next 0 / counter.w)
    (counter.next (counter.next 0) / counter.w) = 1 := by decide

/-- `hshort` fails for the counter at `d = d' = 1`. -/
example : ¬ ∀ d d' : ℤ, |d| < counter.w → |d'| < counter.w →
    (counter.q : ℤ) ∣ counter.a * d - d' → d = 0 := fun h => by
  have := h 1 1 (by decide) (by decide) (by decide)
  lia

/-- `w = 0`: `hshort` holds, and the search does not find the seed `1`. -/
def zeroDivisor : LinearCongruential := ⟨2, 1, 0, 0⟩

example : (∀ d d' : ℤ, |d| < zeroDivisor.w → |d'| < zeroDivisor.w →
    (zeroDivisor.q : ℤ) ∣ zeroDivisor.a * d - d' → d = 0) ∧
    zeroDivisor.seedSearch (1 / zeroDivisor.w) (zeroDivisor.next 1 / zeroDivisor.w)
      (zeroDivisor.next (zeroDivisor.next 1) / zeroDivisor.w) ≠ 1 := by
  refine ⟨fun d d' hd => ?_, by decide⟩
  have : |d| < 0 := hd
  exact absurd this (not_lt.mpr (abs_nonneg d))

/-! ### Efficiency certificates at concrete encodings -/

/-- The test, on the parameters and a challenge `(r, s')`, all in binary. -/
example : ComputableInPolyTime (fun x : LinearCongruential × ℕ × ℕ => x.1.test x.2.1 x.2.2)
    (encPair encLinearCongruential (encPair encNat encNat)) encBool :=
  computableInPolyTime_test (by fun_prop) (by fun_prop) (by fun_prop)

/-- An input of the search: the divisor in unary, the other parameters and the three observed
outputs in binary. -/
structure SearchInput where
  /-- The divisor `w`, in unary: the search tries `w` candidates. -/
  w : ℕ
  /-- The modulus. -/
  q : ℕ
  /-- The multiplier. -/
  a : ℕ
  /-- The increment. -/
  b : ℕ
  /-- The first observed output. -/
  r₁ : ℕ
  /-- The second observed output. -/
  r₂ : ℕ
  /-- The third observed output. -/
  r₃ : ℕ

/-- The encoding of a search input: `w` in unary, then `q`, `a`, `b`, `r₁`, `r₂`, `r₃` in
binary. -/
private enc_structure encSearchInput : SearchInput where
  w : encUnary, q : encNat, a : encNat, b : encNat, r₁ : encNat, r₂ : encNat, r₃ : encNat

/-- The search runs in time polynomial in `w` and in the binary length of the rest. -/
example : ComputableInPolyTime
    (fun x : SearchInput => (⟨x.q, x.a, x.b, x.w⟩ : LinearCongruential).seedSearch x.r₁ x.r₂ x.r₃)
    encSearchInput encNat :=
  computableInPolyTime_seedSearch (P := fun x : SearchInput => ⟨x.q, x.a, x.b, x.w⟩)
    (encLinearCongruential_mk_polyTime (by fun_prop) (by fun_prop) (by fun_prop)
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop)))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

end CslibFrontierTests.Crypto.LinearCongruential
