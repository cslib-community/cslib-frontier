/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import Cslib.Crypto.Primitives.PRG.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Crypto.Computational.FuzzyExtractor.Basic
import CslibFrontier.Crypto.Computational.OneWay.CondEPPRG
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.BitString
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime
import CslibFrontierTests.Crypto.Computational.FuzzyExtractorTest

set_option linter.privateModule false

/-!
# Non-vacuity witnesses for PRG, condEP-PRG, and computational fuzzy-extractor assumptions

Ordinary `module` test suite supplying positive and negative non-vacuity checks for:

1. **`PRG.Generator.Secure`** (`Cslib.Crypto.Primitives.PRG.Defs`):
   * Positive check: `idBoolPRG : PRG.Generator Bool Bool` satisfies `Secure Admissible 0` for every
     admissible predicate `Admissible`.
   * Negative check: the expanding constant generator `constFalsePRG : PRG.Generator Unit Bool`
     satisfies `IsExpanding` yet has advantage `1 / 2` against `fun b => PMF.pure (!b)`, refuting
     `Secure Admissible ε` whenever `Admissible` admits that test and `ε < 1 / 2`.
2. **`CondEPPRG`** (`OneWay/CondEPPRG.lean`):
   * `zeroPadLog2 z := List.replicate (Nat.log 2 z.length) false ++ z` is deterministic polytime
     and satisfies the exact stretch length `n + 1 * Nat.log 2 n`, yet fails `CondEPPRG zeroPadLog2
     (fun _ => 1 / 4) 1 α` for every `α : ℕ` because its leading bit is `false` for all `n ≥ 2`.
3. **`FuzzyExtractor.ComputationallySecureFor` and `FuzzyExtractor.ComputationallySecure`**
   (`FuzzyExtractor/Basic.lean`):
   * Positive checks: `uniformKeyExtractor : FuzzyExtractor Bool Bool Unit` achieves `0` advantage
     against arbitrary distinguisher families and every source in `Set.univ`.
   * Negative checks: reuses `revealingFuzzyExtractor`, `eqBitDistinguisher`, and
     `securityAdvantage_revealingFuzzyExtractor` from
     `CslibFrontierTests.Crypto.Computational.FuzzyExtractorTest` to refute both
     `ComputationallySecureFor` (for `ε < 1 / 2`) and `ComputationallySecure`.
-/

namespace CslibFrontierTests.Crypto.PRGAndFuzzyExtractorNonvacuity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PRG Turing.MultiTapeTM
open CslibFrontierTests.Crypto.Computational.FuzzyExtractorTest
open scoped NNReal

/-! ### 1. `Cslib.Crypto.PRG.Generator.Secure` -/

/-- The identity generator on `Bool` (positive witness for `PRG.Generator.Secure`). -/
private def idBoolPRG : PRG.Generator Bool Bool :=
  ⟨id⟩

/-- Constant-false expanding generator `Unit → Bool` (negative witness for `Secure`). -/
private def constFalsePRG : PRG.Generator Unit Bool :=
  ⟨fun _ => false⟩

/-- `constFalsePRG` strictly expands its seed space (`1 < 2`). -/
theorem isExpanding_constFalsePRG : constFalsePRG.IsExpanding := by
  unfold PRG.Generator.IsExpanding
  decide

/-- The identity generator `idBoolPRG` has `0` advantage against every test and therefore satisfies
`PRG.Generator.Secure Admissible 0` for every `Admissible`. -/
theorem prgGeneratorSecure_idBool (Admissible : PRG.Adversary Bool → Prop) :
    idBoolPRG.Secure Admissible 0 := by
  intro adv _
  have hout : idBoolPRG.outputDist = Probability.PMF.uniformOfFintype Bool := by
    simp only [PRG.Generator.outputDist, idBoolPRG, PRG.Generator.coe_mk, PMF.map_id]
  simp only [PRG.Generator.advantage, PRG.Generator.realExperiment, hout,
    PRG.Generator.idealExperiment, sub_self, abs_zero, NNReal.coe_zero, le_refl]

/-- The test `fun b => PMF.pure (!b)` achieves advantage `1 / 2` against `constFalsePRG`. -/
theorem advantage_constFalsePRG_not :
    constFalsePRG.advantage (fun b => PMF.pure (!b)) = 1 / 2 := by
  have hreal : (constFalsePRG.realExperiment (fun b => PMF.pure (!b)) true).toReal = 1 := by
    simp [PRG.Generator.realExperiment, PRG.Generator.outputDist, constFalsePRG]
  have hideal : (PRG.Generator.idealExperiment (fun b => PMF.pure (!b)) true).toReal = 1 / 2 := by
    have hp : (PRG.Generator.idealExperiment (fun b => PMF.pure (!b)) true) = (2 : ENNReal)⁻¹ := by
      simp [PRG.Generator.idealExperiment]
    rw [hp, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    norm_num
  rw [PRG.Generator.advantage, hreal, hideal]
  norm_num

/-- For every distinguisher class admitting `fun b => PMF.pure (!b)` and every `ε < 1 / 2`, the
expanding generator `constFalsePRG` fails `PRG.Generator.Secure Admissible ε`. -/
theorem not_prgGeneratorSecure_constFalse (Admissible : PRG.Adversary Bool → Prop)
    (hadm : Admissible (fun b => PMF.pure (!b))) {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 2) :
    ¬ constFalsePRG.Secure Admissible ε := by
  intro hsec
  have hle := hsec _ hadm
  rw [advantage_constFalsePRG_not] at hle
  linarith

/-! ### 2. `CondEPPRG` -/

/-- Candidate `(·, 1)`-stretching map that prepends `⌊log₂ |z|⌋` zero bits to `z`. -/
private def zeroPadLog2 (z : List Bool) : List Bool :=
  List.replicate (Nat.log 2 z.length) false ++ z

theorem computableInPolyTime_zeroPadLog2 :
    ComputableInPolyTime zeroPadLog2 encBits encBits := by
  have hz : ComputableInPolyTime (fun z : List Bool => z) encBits encBits := by fun_prop
  have hpad : ComputableInPolyTime (fun z : List Bool => List.replicate (Nat.log 2 z.length) false)
      encBits encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp
      (ComputableInPolyTime.unary_log_two.comp hz.length_bits_comp)
  exact ComputableInPolyTime.bitsAppend hpad hz

theorem length_zeroPadLog2 (z : List Bool) :
    (zeroPadLog2 z).length = z.length + 1 * Nat.log 2 z.length := by
  simp only [zeroPadLog2, List.length_append, List.length_replicate, one_mul, Nat.add_comm]

/-- Uniform strict PPT distinguisher returning `true` iff the first output bit is `false`. -/
private def headZeroDist : Distinguisher :=
  fun _ y => pure !(y.headD true)

private theorem headZeroDist_isPPT : IsPPT encBool headZeroDist := by
  have hy : ComputableInPolyTime (fun p : ℕ × List Bool => p.2)
      (encPair encUnary encBits) encBits := by fun_prop
  have hhead : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.headD true)
      (encPair encUnary encBits) encBool :=
    (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) true).comp hy
  exact (ComputableInPolyTime.bool_not.comp hhead).isPPTOn.isPPT

private theorem ideal_headZeroDist_eq_half {n m : ℕ} (hm : 1 ≤ m) :
    (BitString.uniformList m).bind (fun y => ProbComp.eval (headZeroDist n y)) true =
      (2 : ENNReal)⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [BitString.uniformList_succ, PMF.bind_bind]
  have hbit (b : Bool) :
      ((BitString.uniformList k).map (List.cons b)).bind
        (fun y => ProbComp.eval (headZeroDist n y)) = PMF.pure (!b) := by
    simp only [PMF.map, Function.comp_def, headZeroDist, ProbComp.eval_pure, PMF.bind_bind,
      PMF.pure_bind, List.headD_cons, PMF.bind_const]
  rw [PMF.bind_apply, tsum_bool]
  simp [hbit, Probability.PMF.uniformOfFintype_apply]

/-- `zeroPadLog2` satisfies both the polytime and exact `n + ⌊log₂ n⌋` length conditions of
`CondEPPRG`, yet fails `CondEPPRG zeroPadLog2 (fun _ => 1 / 4) 1 α` for every entropy-loss
parameter `α`. -/
theorem not_condEPPRG_zeroPadLog2 (α : ℕ) :
    ¬ CondEPPRG zeroPadLog2 (fun _ => (1 : ℝ) / 4) 1 α := by
  rintro ⟨_, _, E, hE, hdist, _⟩
  have hev := hdist headZeroDist headZeroDist_isPPT
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  let n := max N 2
  have hnN : N ≤ n := le_max_left _ _
  have hn2 : 2 ≤ n := le_max_right _ _
  have hlog : 1 ≤ Nat.log 2 n :=
    (show 1 ≤ Nat.log 2 2 by decide).trans (Nat.log_mono_right hn2)
  have hreal_dist :
      ((((PMF.uniformOfFinset (E n) (hE n)).map List.ofFn).map zeroPadLog2).bind
        fun y => ProbComp.eval (headZeroDist n y)) = PMF.pure true := by
    have hpt :
        (fun x : BitString n => ProbComp.eval (headZeroDist n (zeroPadLog2 (List.ofFn x)))) =
          fun _ => PMF.pure true := by
      funext x
      have hlogx : 1 ≤ Nat.log 2 (List.ofFn x).length := by
        simpa only [List.length_ofFn] using hlog
      obtain ⟨k, hk⟩ : ∃ k, Nat.log 2 (List.ofFn x).length = k + 1 :=
        ⟨Nat.log 2 (List.ofFn x).length - 1, by omega⟩
      simp only [headZeroDist, zeroPadLog2, hk, List.replicate_succ, List.cons_append,
        List.headD_cons, Bool.not_false, ProbComp.eval_pure]
    rw [PMF.map_comp, PMF.map, PMF.bind_bind]
    simp only [Function.comp_def, PMF.pure_bind, hpt, PMF.bind_const]
  have hideal_true :
      ((BitString.uniformList (n + 1 * Nat.log 2 n)).bind
        fun y => ProbComp.eval (headZeroDist n y)) true = (2 : ENNReal)⁻¹ :=
    ideal_headZeroDist_eq_half (by omega)
  have hadv :
      (Game.advantage
        ((((PMF.uniformOfFinset (E n) (hE n)).map List.ofFn).map zeroPadLog2).bind
          fun y => ProbComp.eval (headZeroDist n y))
        ((BitString.uniformList (n + 1 * Nat.log 2 n)).bind
          fun y => ProbComp.eval (headZeroDist n y)) : ℝ) = 1 / 2 := by
    have h1 : Game.succProbability (PMF.pure true) = 1 := by
      simp [Game.succProbability]
    have h2 :
        Game.succProbability ((BitString.uniformList (n + 1 * Nat.log 2 n)).bind
          fun y => ProbComp.eval (headZeroDist n y)) = (1 : ℝ≥0) / 2 := by
      rw [Game.succProbability, hideal_true, ENNReal.toNNReal_inv, ENNReal.toNNReal_ofNat, one_div]
    rw [hreal_dist, Game.coe_advantage, h1, h2]
    norm_num
  have hle := hN n hnN
  rw [hadv] at hle
  norm_num at hle

/-! ### 3. `FuzzyExtractor.ComputationallySecureFor` and `ComputationallySecure` -/

/-- Trivial source-ignoring fuzzy extractor that outputs a uniformly random `Bool` key directly,
establishing positive satisfiability of both `ComputationallySecureFor` and
`ComputationallySecure` for any source family and distinguisher class. -/
private noncomputable def uniformKeyExtractor : FuzzyExtractor Bool Bool Unit where
  gen _ := (·, ()) <$> ProbComp.uniform Bool
  rep _ _ := pure false

private theorem realDistribution_eq_ideal_uniformKeyExtractor (W : PMF Bool) :
    uniformKeyExtractor.realDistribution W = uniformKeyExtractor.idealDistribution W := by
  simp only [FuzzyExtractor.realDistribution, FuzzyExtractor.idealDistribution,
    uniformKeyExtractor, ProbComp.eval_map, ProbComp.eval_uniform, PMF.map, Function.comp_def,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_const]

/-- `uniformKeyExtractor` achieves `ComputationallySecureFor` with `0` error over `Set.univ`
against any distinguisher class `Admissible`. -/
theorem computationallySecureFor_uniformKeyExtractor
    (Admissible : (Bool → Unit → Experiment) → Prop) :
    uniformKeyExtractor.ComputationallySecureFor Set.univ Admissible 0 :=
  FuzzyExtractor.computationallySecureFor_zero_of_realDistribution_eq
    (fun W _ => realDistribution_eq_ideal_uniformKeyExtractor W) Admissible

/-- `uniformKeyExtractor` achieves asymptotic `ComputationallySecure` over `Set.univ` against any
distinguisher-family class `Admissible`. -/
theorem computationallySecure_uniformKeyExtractor
    (Admissible : ((κ : ℕ) → Bool → Unit → Experiment) → Prop) :
    FuzzyExtractor.ComputationallySecure (fun _ => uniformKeyExtractor) Set.univ Admissible := by
  intro source _ D _
  have heq (κ : ℕ) :
      uniformKeyExtractor.securityAdvantage (source κ) (D κ) = 0 :=
    FuzzyExtractor.securityAdvantage_eq_zero_of_realDistribution_eq
      (realDistribution_eq_ideal_uniformKeyExtractor (source κ)) (D κ)
  simpa only [FuzzyExtractor.securityAdvantage, heq] using negligible_zero

/-- Reuses `revealingFuzzyExtractor` and `securityAdvantage_revealingFuzzyExtractor` from
`FuzzyExtractorTest` to refute `FuzzyExtractor.ComputationallySecureFor` whenever
`Admissible` admits `eqBitDistinguisher` and `ε < 1 / 2`. -/
theorem not_computationallySecureFor_revealingFuzzyExtractor
    (Admissible : (Bool → Bool → Experiment) → Prop)
    (hadm : Admissible eqBitDistinguisher) {ε : ℝ≥0} (hε : ε < (1 : ℝ≥0) / 2) :
    ¬ revealingFuzzyExtractor.ComputationallySecureFor {PMF.uniformOfFintype Bool}
        Admissible ε := by
  intro hsec
  have hle := hsec (PMF.uniformOfFintype Bool) rfl eqBitDistinguisher hadm
  rw [securityAdvantage_revealingFuzzyExtractor] at hle
  exact (not_le_of_gt hε) hle

/-- Refutes asymptotic `FuzzyExtractor.ComputationallySecure` for `revealingFuzzyExtractor` against
any class `Admissible` admitting the constant `eqBitDistinguisher` family. -/
theorem not_computationallySecure_revealingFuzzyExtractor
    (Admissible : ((κ : ℕ) → Bool → Bool → Experiment) → Prop)
    (hadm : Admissible (fun _ => eqBitDistinguisher)) :
    ¬ FuzzyExtractor.ComputationallySecure
        (fun _ => revealingFuzzyExtractor) {fun _ => PMF.uniformOfFintype Bool} Admissible := by
  intro hsec
  have hneg := hsec _ rfl (fun _ => eqBitDistinguisher) hadm
  simp only [securityAdvantage_revealingFuzzyExtractor] at hneg
  exact not_negligible_const (by norm_num) hneg

end CslibFrontierTests.Crypto.PRGAndFuzzyExtractorNonvacuity
