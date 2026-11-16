/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRP.Finite
import CslibFrontier.Languages.Probabilistic.Oracle.CoinFixing

/-!
# Bidirectional switching against the forgetful sampler

A `PRP.StrongAdversary D` queries a permutation of a finite type `D` in both directions. This
module bounds how well such an adversary, with private coins and at most `Q` queries, tells a
uniformly random permutation from `RandomPermutation.forgetfulAnswer`, the lazy sampler that keeps
the pairs `(x, y)` it has answered, answers `.forward x` or `.inverse y` from a recorded pair when
there is one, and otherwise with a fresh uniform point of `D`, which may repeat a recorded one. The
forgetful sampler is neither a random function nor a random permutation; it is the object that
`RandomPermutation.abs_sub_uniformPerm_forgetful_le` compares a uniform permutation with, for
deterministic adversaries. The adversary's coins are fixed with
`ProbOracleComp.coinLaw_bind_runWith_fixCoins`, which reduces the bound to that deterministic one.

The bound is information-theoretic: nothing is claimed about running time.

## Main results

* `PRP.advantage_strongIdealExperiment_forgetful_le`: an adversary making at most `Q` queries has
  advantage at most `Q.choose 2 / |D|` between `PRP.strongIdealExperiment` and its run against the
  forgetful sampler.
-/

public section

namespace Cslib.Crypto.PRP

open Probability RandomPermutation

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The law of `strongIdealExperiment`: a uniform permutation `π`, then the adversary interpreted
at the `PMF` level against `π` in both directions. -/
theorem eval_strongIdealExperiment (A : StrongAdversary D) :
    ProbComp.eval (strongIdealExperiment A) =
      (PMF.uniformOfFintype (Equiv.Perm D)).bind fun π =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle fun q => PMF.pure (evalPerm π q)) A := by
  simp only [strongIdealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_run, ProbComp.eval_pure]

variable [Nonempty D]

/-- **Bidirectional switching bound for adversaries with private coins**: an adversary making at
most `Q` queries tells a uniform permutation of `D`, queried in both directions, from the
forgetful lazy sampler with advantage at most `Q.choose 2 / |D|`. -/
theorem advantage_strongIdealExperiment_forgetful_le {A : StrongAdversary D} {Q : ℕ}
    (hQ : A.IsQueryBounded Q) :
    (Game.advantage (ProbComp.eval (strongIdealExperiment A))
      ((ProbOracleComp.runWith forgetfulAnswer A []).map Prod.fst) : ℝ) ≤
      Q.choose 2 / Fintype.card D := by
  rw [eval_strongIdealExperiment,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind (PMF.uniformOfFintype (Equiv.Perm D))
      (fun π q => evalPerm π q) A,
    ← ProbOracleComp.coinLaw_bind_runWith_fixCoins, PMF.map_bind]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  rw [Game.coe_advantage, div_eq_mul_inv]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    Probability.PMF.monad_bind_eq_bind, PMF.bind_pure, OracleComp.runWith_eq_run_interpret] using
      abs_sub_uniformPerm_forgetful_le (ProbOracleComp.isQueryBounded_fixCoins hQ ω) PMF.pure true

end Cslib.Crypto.PRP
