/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Languages.Probabilistic.Simulation.CloseTo
import CslibFrontier.Probability.StatisticalDistance.ClosedForm
import CslibFrontier.Probability.StatisticalDistance.TotalVariation

/-!
# Lipschitz oracle programs

A program `program : ProbOracleComp spec α` is `K`-Lipschitz at an oracle `oracle`
(`ProbOracleComp.LipschitzAt K oracle program`) when replacing `oracle` by any oracle whose reply
to every query is within statistical distance `ε` moves the output law of `program` by at most
`K * ε`. Private samples are uniform and each external query is answered by an independent draw
from the oracle's reply law (`OracleComp.evalWith`).

This is the stability condition under which stochastic oracle debate is correct
[BrownCohenIrvingPiliouras2024, Definition 6.1], stated for every reply and output type. On `Bool`
replies and a `Bool` output it is the source's condition (`lipschitzAt_bool_iff`): the probability
of outputting `true` moves by at most `K` times the largest difference, over queries, of the
probabilities of replying `true`.

A program making at most `n` external queries is `n`-Lipschitz at every oracle
(`LipschitzAt.of_isQueryBounded`), by replacing replies one query at a time. The constant can be
much smaller than the number of queries: a program that queries many times but returns only its
first reply is `1`-Lipschitz.

## Main definitions

* `Cslib.ProbOracleComp.LipschitzAt`: `K`-Lipschitz at an oracle.

## Main results

* `Cslib.ProbOracleComp.LipschitzAt.of_isQueryBounded`: `n` external queries give constant `n`.
* `Cslib.ProbOracleComp.LipschitzAt.bind`: constants add under sequencing.
* `Cslib.ProbOracleComp.lipschitzAt_bool_iff`: agreement with
  [BrownCohenIrvingPiliouras2024, Definition 6.1] on `Bool` replies and output.

## References

* [J. Brown-Cohen, G. Irving, G. Piliouras, *Scalable AI safety via doubly-efficient debate*,
  Section 6][BrownCohenIrvingPiliouras2024]
-/

public section

namespace Cslib.ProbOracleComp

open OracleComp (sumHandler)
open Probability
open scoped ENNReal NNReal

variable {Query α β : Type} {spec : Query → Type}

/-- `program` is `K`-Lipschitz at the oracle `oracle`: against any oracle `oracle'` whose reply
law at every query is within statistical distance `ε` of `oracle`'s, the output law of `program`
is within `K * ε` of its output law against `oracle`.

The condition is relative to the one oracle `oracle`, as in
[BrownCohenIrvingPiliouras2024, Definition 6.1], and quantifies over the tolerance `ε` in place of
the supremum distance between oracles. The source writes a strict inequality, which no machine
satisfies (take `oracle' = oracle`); the bound here is non-strict, as in the Lean formalization
accompanying the source (google-deepmind/debate, `Oracle.lipschitz`). The source takes `K > 0`;
`K = 0` is admitted here and says that the output law does not depend on the oracle. -/
@[expose] def LipschitzAt (K : ℝ≥0) (oracle : (q : Query) → PMF (spec q))
    (program : ProbOracleComp spec α) : Prop :=
  ∀ (oracle' : (q : Query) → PMF (spec q)) (ε : ℝ≥0∞),
    (∀ q, CloseTo (oracle q) (oracle' q) ε) →
      CloseTo (OracleComp.evalWith (sumHandler ProbComp.unifOracle oracle) program)
        (OracleComp.evalWith (sumHandler ProbComp.unifOracle oracle') program) ((K : ℝ≥0∞) * ε)

namespace LipschitzAt

variable {K K₁ K₂ : ℝ≥0} {oracle : (q : Query) → PMF (spec q)}

/-- A larger constant is still a Lipschitz constant. -/
theorem mono {program : ProbOracleComp spec α} (h : LipschitzAt K₁ oracle program)
    (hK : K₁ ≤ K₂) : LipschitzAt K₂ oracle program :=
  fun oracle' ε hε => (h oracle' ε hε).mono (by gcongr)

/-- **Query-bounded programs.** A program making at most `n` external queries on every path is
`n`-Lipschitz at every oracle: replacing the replies one query at a time moves the output law by
at most `ε` per query, and private samples are answered identically on both sides. -/
theorem of_isQueryBounded {program : ProbOracleComp spec α} {n : ℕ}
    (h : program.IsQueryBounded n) (oracle : (q : Query) → PMF (spec q)) :
    LipschitzAt (n : ℝ≥0) oracle program := by
  intro oracle' ε hε
  have key := OracleComp.closeTo_run_interpret_simulation_readOnly (State := Unit)
    (State' := Unit) (Sum.elim (fun _ => 0) (fun _ => 1))
    (fun q s => (fun a => (a, s)) <$> sumHandler ProbComp.unifOracle oracle q)
    (fun _ => sumHandler ProbComp.unifOracle oracle') PMF.pure ε ?_ program h ()
  · rw [OracleComp.run_interpret_stateless] at key
    simp only [PMF.monad_map_eq_map, PMF.map_comp, PMF.pure_bind] at key
    rw [show (Prod.fst ∘ fun a : α => (a, ())) = id from rfl, PMF.map_id] at key
    rwa [OracleComp.evalWith_eq_interpret, OracleComp.evalWith_eq_interpret, ENNReal.coe_natCast]
  · rintro (n | q) s
    · simp only [PMF.monad_map_eq_map, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
      exact (CloseTo.refl _).mono zero_le
    · simp only [PMF.monad_map_eq_map, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
        Sum.elim_inr, Nat.cast_one, one_mul]
      exact (hε q).bind_left _

/-- **Sequencing.** If `program` is `K₁`-Lipschitz at `oracle` and every continuation is
`K₂`-Lipschitz there, the sequenced program is `(K₁ + K₂)`-Lipschitz at `oracle`. -/
theorem bind {program : ProbOracleComp spec α} {next : α → ProbOracleComp spec β}
    (h : LipschitzAt K₁ oracle program) (hnext : ∀ a, LipschitzAt K₂ oracle (next a)) :
    LipschitzAt (K₁ + K₂) oracle (program >>= next) := by
  intro oracle' ε hε
  simp only [OracleComp.evalWith_bind]
  exact ((h oracle' ε hε).bind fun a _ => hnext a oracle' ε hε).mono
    (by rw [ENNReal.coe_add, add_mul])

/-- Deterministic postprocessing keeps the constant. -/
theorem map (f : α → β) {program : ProbOracleComp spec α} (h : LipschitzAt K oracle program) :
    LipschitzAt K oracle (f <$> program) := by
  intro oracle' ε hε
  simpa only [OracleComp.evalWith_map] using (h oracle' ε hε).map f

end LipschitzAt

/-- **Agreement with the source on `Bool`.** For `Bool` replies, a `Bool` output and a finite
constant `K`, being `K`-Lipschitz at `oracle` is [BrownCohenIrvingPiliouras2024, Definition 6.1]:
against every other oracle, the probability of outputting `true` moves by at most `K` times the
largest difference, over queries, of the probabilities of replying `true`. -/
theorem lipschitzAt_bool_iff {oracle : Query → PMF Bool}
    {program : ProbOracleComp (fun _ : Query => Bool) Bool} {K : ℝ≥0} :
    LipschitzAt K oracle program ↔ ∀ oracle' : Query → PMF Bool,
      |(OracleComp.evalWith (sumHandler ProbComp.unifOracle oracle) program true).toReal -
          (OracleComp.evalWith (sumHandler ProbComp.unifOracle oracle') program true).toReal| ≤
        K * ⨆ q, |(oracle q true).toReal - (oracle' q true).toReal| := by
  have hsup (oracle' : Query → PMF Bool) :
      ∃ s : ℝ≥0, (s : ℝ) = ⨆ q, |(oracle q true).toReal - (oracle' q true).toReal| :=
    ⟨⟨_, Real.iSup_nonneg fun _ => abs_nonneg _⟩, rfl⟩
  constructor
  · intro h oracle'
    obtain ⟨s, hs⟩ := hsup oracle'
    have hbdd : BddAbove (Set.range fun q => |(oracle q true).toReal - (oracle' q true).toReal|) :=
      ⟨1, by rintro _ ⟨q, rfl⟩; exact (PMF.dist_bool _ _).symm.trans_le (PMF.dist_le_one _ _)⟩
    have hK := h oracle' s fun q => closeTo_coe_iff_dist_le.2 <|
      (PMF.dist_bool _ _).trans_le ((le_ciSup hbdd q).trans_eq hs.symm)
    rwa [← ENNReal.coe_mul, closeTo_coe_iff_dist_le, PMF.dist_bool, NNReal.coe_mul, hs] at hK
  · intro h oracle' ε hε
    obtain ⟨s, hs⟩ := hsup oracle'
    have hsε : (s : ℝ≥0∞) ≤ ε := by
      induction ε with
      | top => exact le_top
      | coe e =>
        rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, hs]
        exact Real.iSup_le (fun q => (PMF.dist_bool _ _).symm.trans_le
          (closeTo_coe_iff_dist_le.1 (hε q))) e.coe_nonneg
    refine CloseTo.mono ?_ (mul_le_mul_right hsε K)
    rw [← ENNReal.coe_mul, closeTo_coe_iff_dist_le, PMF.dist_bool, NNReal.coe_mul, hs]
    exact h oracle'

end Cslib.ProbOracleComp
