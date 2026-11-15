/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.StatisticalIndistinguishability
import CslibFrontier.Crypto.Computational.Pseudoentropy.SeedExtraction
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Probability.StatisticalDistance.UniformMod

/-!
# Statistical indistinguishability: client tests

Finite-type and unbounded-test instances, separating constant ensembles, and a client converting
`SeedRealization.remainingSeed_word_extraction` into `StatisticallyIndistinguishable`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.StatisticalIndistinguishability

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal Cslib.Probability.PMF

/-- Negligibility used by the instances below. -/
theorem negligible_three_div_two_pow : Negligible fun n => (3 : ℝ≥0) / 2 ^ n := by
  have h := (negligible_geometric (ratio := 2⁻¹) (by norm_num)).const_mul 3
  simpa only [div_eq_mul_inv, inv_pow] using h

/-- Definition 3.6 holds for a pair of distinct ensembles on a finite type: a uniform value below
`2 ^ n` read in `ZMod 3`, and the uniform law on `ZMod 3` (Example 3.2 with `dist`). -/
theorem statisticallyIndistinguishable_natCast_zmod_three :
    StatisticallyIndistinguishable
      (fun n => (PMF.uniformOfFintype (Fin (2 ^ n))).map fun x => (x.val : ZMod 3))
      (fun _ => PMF.uniformOfFintype (ZMod 3)) :=
  .of_dist_le negligible_three_div_two_pow fun n => by
    simpa using PMF.dist_map_natCast_uniformOfFintype_le_div (2 ^ n) 3

/-- Definition 3.6 as printed: the statistical distance of that pair is negligible. -/
example : Negligible fun n => nndist
    ((PMF.uniformOfFintype (Fin (2 ^ n))).map fun x => (x.val : ZMod 3))
    (PMF.uniformOfFintype (ZMod 3)) :=
  statisticallyIndistinguishable_iff_negligible_nndist.mp
    statisticallyIndistinguishable_natCast_zmod_three

/-- Theorem 3.11 for that pair: every family of tests has negligible advantage. -/
example (test : ℕ → ZMod 3 → Game) : Negligible fun n => Game.advantage
    (((PMF.uniformOfFintype (Fin (2 ^ n))).map fun x => (x.val : ZMod 3)).bind (test n))
    ((PMF.uniformOfFintype (ZMod 3)).bind (test n)) :=
  statisticallyIndistinguishable_natCast_zmod_three.indistinguishable test trivial

/-- Corollary 3.12 for that pair, written in binary. -/
example : ComputationallyIndistinguishable
    (fun n => ((PMF.uniformOfFintype (Fin (2 ^ n))).map fun x => (x.val : ZMod 3)).map
      fun r => encNat r.val)
    (fun _ => (PMF.uniformOfFintype (ZMod 3)).map fun r => encNat r.val) :=
  (statisticallyIndistinguishable_natCast_zmod_three.map
    fun _ r => encNat r.val).computationallyIndistinguishable

/-- Definition 3.6 fails for two constant ensembles that differ. -/
theorem not_statisticallyIndistinguishable_pure :
    ¬ StatisticallyIndistinguishable (fun _ : ℕ => PMF.pure false)
      (fun _ : ℕ => PMF.pure true) := by
  rintro ⟨ε, hε, h⟩
  refine not_negligible_const one_ne_zero (negligible_of_le hε fun n => ?_)
  have hn := h n {false}
  simpa using hn

/-- So, by the equivalence with unbounded tests, some family of tests tells them apart. -/
example : ¬ Game.Indistinguishable
    (fun (test : ℕ → Bool → Game) n => (PMF.pure false).bind (test n))
    (fun test n => (PMF.pure true).bind (test n)) (fun _ => True) :=
  fun h => not_statisticallyIndistinguishable_pure
    (statisticallyIndistinguishable_iff_indistinguishable.mpr h)

/-- A client on `main`. Holenstein's remaining-seed extraction
(`SeedRealization.remainingSeed_word_extraction`) is stated against every family of tests of the
joint output, so it says that the real and ideal outputs are statistically indistinguishable. -/
example {pair : Pseudoentropy.SamplablePair} (saved : pair.SeedRealization)
    (inverseSlack outputBits : ℕ → ℕ) {Key : ℕ → Type} [∀ n, Finite (Key n)]
    (key : ∀ n, ProbComp (Key n))
    (hash : ∀ n, Key n → List (List Bool) → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (key n))
      (fun key (values : Fin (saved.sampleCount inverseSlack n) →
        BitString (saved.length n)) => hash n key ((List.ofFn values).map List.ofFn)))
    (hbudget : ∀ᶠ n in Filter.atTop, outputBits n = 0 ∨
      outputBits n + 2 * (saved.sampleSlack inverseSlack n : ℝ) ≤
        saved.sampleCount inverseSlack n *
          (saved.length n - PMF.entropy ((pair.joint n).map Prod.fst) -
            PMF.conditionalEntropy (pair.joint n))) :
    StatisticallyIndistinguishable
      (fun n => ProbComp.eval (Pseudoentropy.extractLabelsReal (saved.sampleWithSeed n)
        (saved.sampleCount inverseSlack n) (key n) (hash n)))
      (fun n => Pseudoentropy.extractLabelsIdeal (Output := BitString (outputBits n))
        (pair.sample n) (saved.sampleCount inverseSlack n) (key n)) :=
  statisticallyIndistinguishable_iff_indistinguishable.2
    (saved.remainingSeed_word_extraction inverseSlack outputBits key hash hhash hbudget)

end CslibFrontierTests.Crypto.StatisticalIndistinguishability
