/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Crypto.Primitives.PRG.Defs
public import Mathlib.Data.Finset.Density
public import Mathlib.Basic.Real.Basic
public import Cslib.Foundations.Data.BitString
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Expect

/-!
# Deterministic tests of generators

The experiments of Attack Game 3.1 [BonehShoup2023] against a deterministic test are densities:
a test accepts the output of a generator on a uniform seed with probability the density of the
seeds whose output it accepts (`Cslib.Crypto.PRG.Generator.toReal_realExperiment_pure`), and a
uniform string with the density of the strings it accepts
(`Cslib.Crypto.PRG.Generator.toReal_idealExperiment_pure`). On bit strings the advantage is the
difference of the two counts, scaled by the numbers of seeds and strings
(`Cslib.Crypto.PRG.Generator.advantage_pure_eq`).

## Main results

* `Cslib.Crypto.PRG.Generator.toReal_realExperiment_pure`,
  `Cslib.Crypto.PRG.Generator.toReal_idealExperiment_pure`: the experiments of a deterministic
  test are densities.
* `Cslib.Crypto.PRG.Generator.toReal_realExperiment_sub_toReal_idealExperiment_not`: a test that
  accepts no output of the generator gives its negation the advantage of its density.
* `Cslib.Crypto.PRG.Generator.advantage_pure_eq`: the advantage of a deterministic test on bit
  strings as a difference of counts.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 3.1
-/

public section

namespace Cslib.Crypto.PRG

open Cslib.Probability.PMF Finset

section Deterministic

variable {Seed Output : Type*}

/-- A deterministic test accepts the output of a generator on a uniform seed with probability the
density of the seeds on which it accepts. -/
theorem Generator.toReal_realExperiment_pure [Fintype Seed] [Nonempty Seed]
    (G : Generator Seed Output) (test : Output → Bool) :
    (G.realExperiment (fun y => PMF.pure (test y)) true).toReal = dens {z | test (G z) = true} := by
  rw [Generator.realExperiment, Generator.outputDist, PMF.bind_map,
    ← toReal_uniformOfFintype_map_apply_true, ← PMF.bind_pure_comp]
  rfl

/-- A deterministic test accepts a uniform string with probability the density of the strings it
accepts. -/
theorem Generator.toReal_idealExperiment_pure [Fintype Output] [Nonempty Output]
    (test : Output → Bool) :
    (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal =
      dens {y | test y = true} := by
  rw [Generator.idealExperiment, ← toReal_uniformOfFintype_map_apply_true, ← PMF.bind_pure_comp]
  rfl

/-- **Dense tests that avoid a generator.** If a deterministic test accepts no output of `G`, its
negation accepts outputs of `G` with probability exceeding that of uniform strings by exactly the
density of the strings the test accepts. -/
theorem Generator.toReal_realExperiment_sub_toReal_idealExperiment_not [Fintype Seed]
    [Nonempty Seed] [Fintype Output] [Nonempty Output] (G : Generator Seed Output)
    {test : Output → Bool} (havoid : ∀ z, test (G z) = false) :
    (G.realExperiment (fun y => PMF.pure (!test y)) true).toReal -
        (Generator.idealExperiment (fun y => PMF.pure (!test y)) true).toReal =
      dens {y | test y = true} := by
  rw [Generator.toReal_realExperiment_pure, Generator.toReal_idealExperiment_pure]
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
  have hreal : ({z | test (G z) = false} : Finset Seed) = univ :=
    filter_true_of_mem fun z _ => havoid z
  have hsplit := dens_filter_add_dens_filter_not_eq_dens (s := (univ : Finset Output))
    fun y => test y = true
  simp only [Bool.not_eq_true, dens_univ] at hsplit
  rw [hreal, dens_univ, NNRat.cast_one]
  have hcast : (dens {y : Output | test y = true} : ℝ) + dens {y : Output | test y = false} = 1 :=
    mod_cast hsplit
  linarith

end Deterministic

/-- The advantage of a deterministic test is the difference of the fractions of seeds and of
strings it accepts. -/
theorem Generator.advantage_pure_eq {k L : ℕ} (Gk : Generator (BitString k) (BitString L))
    (test : BitString L → Bool) :
    Gk.advantage (fun y => PMF.pure (test y)) =
      |(#{z | test (Gk z) = true} : ℝ) / 2 ^ k - #{y | test y = true} / 2 ^ L| := by
  rw [Generator.advantage, Generator.toReal_realExperiment_pure,
    Generator.toReal_idealExperiment_pure, nnratCast_dens, nnratCast_dens]
  simp [BitString]

end Cslib.Crypto.PRG
