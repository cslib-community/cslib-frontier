/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Crypto.Primitives.PRG.Defs
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.Vector
import CslibFrontier.Crypto.Primitives.PRG.Game
import CslibFrontier.Probability.PMF.Uniform

/-!
# Pseudorandom generator from a pseudorandom function

Evaluating a keyed function `F : Key → D → R` at `ℓ` distinct domain points `x : Fin ℓ ↪ D`
yields a deterministic generator `PRF.toPRG F x : PRG.Generator Key (Fin ℓ → R)` sending a key `k`
to `fun i => F k (x i)` ([BonehShoup2023], §4.4.4, Theorem 4.8, p. 138).

Given a randomized PRG distinguisher `A : (Fin ℓ → R) → ProbComp Bool`, `PRF.prgReduction x A`
queries `x 0, ..., x (ℓ - 1)` through the PRF oracle (`PRF.queryPoints x`), passes the collected
tuple to `A`, and outputs whatever `A` outputs. It makes `ℓ` external queries
(`PRF.isQueryBounded_prgReduction`) and achieves the exact same advantage
(`PRF.advantage_toPRG_eq`):
`(toPRG F x).advantage (fun y => ProbComp.eval (A y)) = (PRF.advantage F (prgReduction x A) : ℝ)`.
Here `A` ranges over `ProbComp`-valued tests rather than arbitrary `Cslib.Crypto.PRG.Adversary`
(`(Fin ℓ → R) → PMF Bool`) because general `PMF` values with arbitrary real weights cannot be
simulated inside a finitely-branching `ProbComp` adversary.

This finite-type identity is a step toward Theorem 4.8, not the cited result: in the theorem the
reduction is an elementary wrapper around `A` and the conclusion is that the generator is a secure
PRG, while nothing here certifies `prgReduction` as efficient. In
`CslibFrontier.Crypto.Computational.PseudorandomFunction.ToPRG`, the theorem's security conclusion
is `Cslib.Crypto.indistinguishable_prgFromPRF`. The exact identity
`Cslib.Crypto.advantage_prgFromPRF_eq` explains the reduction: it equates the two advantages for
the oracle-PPT word reduction `Cslib.Crypto.prgFromPRFReduction`, which runs `prgReduction`.
`Cslib.Crypto.PseudorandomFunctionOver.toPRG` concludes `PseudorandomGenerator` and so also needs
strict stretch, `n < ℓ n * outLen n`. For example, one output block as wide as the seed gives
indistinguishable outputs but no stretch.

## Main definitions

* `Cslib.Crypto.PRF.toPRG`: generator obtained by evaluating `F` at `x : Fin ℓ ↪ D`.
* `Cslib.Crypto.PRF.queryPoints`: adaptive oracle program collecting replies at
  `x 0, ..., x (ℓ - 1)`.
* `Cslib.Crypto.PRF.prgReduction`: PRF adversary running a `ProbComp` distinguisher on those
  replies.

## Main results

* `Cslib.Crypto.PRF.isQueryBounded_prgReduction`: the reduction makes at most `ℓ` oracle queries.
* `Cslib.Crypto.PRF.eval_realExperiment_prgReduction`: real PRF experiment agrees with the PRG
  real experiment.
* `Cslib.Crypto.PRF.eval_idealExperiment_prgReduction`: ideal PRF experiment agrees with the PRG
  ideal experiment.
* `Cslib.Crypto.PRF.isExpanding_toPRG`: `PRF.toPRG F x` is expanding when `|Key| < |R| ^ ℓ`.

## Step toward Theorem 4.8

* `Cslib.Crypto.PRF.advantage_toPRG_eq`: exact PRG-to-PRF advantage identity on finite types.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  §4.4.4 (Theorem 4.8, p. 138).
-/

public section

namespace Cslib.Crypto.PRF

open Probability

section Definitions

variable {Key D R : Type} {ℓ : ℕ}

/-- Pseudorandom generator constructed from a keyed function `F : Key → D → R` by evaluating at
`ℓ` distinct domain elements `x 0, ..., x (ℓ - 1)` ([BonehShoup2023], §4.4.4, p. 138). -/
@[expose] def toPRG (F : Key → D → R) (x : Fin ℓ ↪ D) : PRG.Generator Key (Fin ℓ → R) where
  toFun key i := F key (x i)

@[simp] theorem toPRG_apply (F : Key → D → R) (x : Fin ℓ ↪ D) (key : Key) (i : Fin ℓ) :
    toPRG F x key i = F key (x i) := rfl

/-- Query the PRF oracle at `x 0, ..., x (ℓ - 1)` in order and return the reply tuple. -/
@[expose] def queryPoints (x : Fin ℓ ↪ D) : ProbOracleComp (fun _ : D => R) (Fin ℓ → R) :=
  OracleComp.pi fun i => ProbOracleComp.query (x i)

/-- Reduction turning a `ProbComp`-valued PRG distinguisher `A` on `Fin ℓ → R` into an `ℓ`-query
PRF adversary that queries `x 0, ..., x (ℓ - 1)` and forwards the tuple to `A`. -/
@[expose] def prgReduction (x : Fin ℓ ↪ D) (A : (Fin ℓ → R) → ProbComp Bool) :
    Adversary D R :=
  ((do
    let y ← queryPoints x
    ProbOracleComp.sample (A y)) : ProbOracleComp (fun _ : D => R) Bool)

end Definitions

section Proofs

variable {Key D R : Type} {ℓ : ℕ}

/-- Evaluating `queryPoints x` against a deterministic function `f : D → R` returns `f ∘ x`. -/
theorem run_queryPoints {ℓ : ℕ} (x : Fin ℓ ↪ D) (f : D → R) :
    ProbOracleComp.run (queryPoints (R := R) x) (fun d => pure (f d)) =
      pure (fun i => f (x i)) :=
  ProbOracleComp.run_pi_query (fun i => x i) f

/-- `queryPoints x` makes at most `ℓ` queries on every execution path. -/
theorem isQueryBounded_queryPoints {ℓ : ℕ} (x : Fin ℓ ↪ D) :
    (queryPoints (R := R) x).IsQueryBounded ℓ :=
  ProbOracleComp.isQueryBounded_pi_query (fun i => x i)

/-- The PRF reduction `prgReduction x A` makes at most `ℓ` oracle queries regardless of private
coins and oracle replies. -/
theorem isQueryBounded_prgReduction (x : Fin ℓ ↪ D) (A : (Fin ℓ → R) → ProbComp Bool) :
    (prgReduction x A).IsQueryBounded ℓ := by
  simpa only [prgReduction, add_zero] using
    (isQueryBounded_queryPoints x).bind fun y => ProbOracleComp.IsQueryBounded.sample (A y)

/-- Against `F`, the PRF real experiment of `prgReduction x A` has the same distribution as the PRG
real experiment of `toPRG F x` on `A`. -/
theorem eval_realExperiment_prgReduction [Fintype Key] [Nonempty Key]
    (F : Key → D → R) (x : Fin ℓ ↪ D) (A : (Fin ℓ → R) → ProbComp Bool) :
    ProbComp.eval (realExperiment F (prgReduction x A)) =
      (toPRG F x).realExperiment (fun y => ProbComp.eval (A y)) := by
  simp only [realExperiment, prgReduction, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.run_bind, run_queryPoints, pure_bind, ProbOracleComp.run_sample,
    PRG.Generator.realExperiment, PRG.Generator.outputDist, PMF.bind_map]
  rfl

/-- In the ideal PRF experiment, querying `x : Fin ℓ ↪ D` yields a uniformly random `Fin ℓ → R`
tuple, matching the PRG ideal experiment on `A`. -/
theorem eval_idealExperiment_prgReduction [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R]
    (x : Fin ℓ ↪ D) (A : (Fin ℓ → R) → ProbComp Bool) :
    ProbComp.eval (idealExperiment (prgReduction x A)) =
      PRG.Generator.idealExperiment (fun y => ProbComp.eval (A y)) := by
  simp only [idealExperiment, prgReduction, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.run_bind, run_queryPoints, pure_bind, ProbOracleComp.run_sample,
    PRG.Generator.idealExperiment]
  rw [← PMF.uniformOfFintype_pi_map_comp_embedding x, PMF.bind_map]
  rfl

/-- Finite-type advantage identity, a step toward [BonehShoup2023], Theorem 4.8 (p. 138), not the
cited result: for any `ProbComp`-valued distinguisher `A` on `Fin ℓ → R`, its PRG distinguishing
advantage against `toPRG F x` equals the PRF distinguishing advantage of the `ℓ`-query reduction
`prgReduction x A` against `F`. Nothing here certifies `prgReduction` as efficient. The theorem's
security conclusion, with an oracle-PPT reduction, is `Cslib.Crypto.indistinguishable_prgFromPRF`;
its exact identity is `Cslib.Crypto.advantage_prgFromPRF_eq`. -/
theorem advantage_toPRG_eq [Fintype Key] [Nonempty Key] [Fintype D] [DecidableEq D]
    [Fintype R] [Nonempty R]
    (F : Key → D → R) (x : Fin ℓ ↪ D) (A : (Fin ℓ → R) → ProbComp Bool) :
    (toPRG F x).advantage (fun y => ProbComp.eval (A y)) =
      (advantage F (prgReduction x A) : ℝ) := by
  rw [PRG.Generator.advantage_eq_game, advantage,
    eval_realExperiment_prgReduction, eval_idealExperiment_prgReduction]

/-- `toPRG F x` is length-expanding (`|Key| < |Fin ℓ → R|`) whenever `|Key| < |R| ^ ℓ`. -/
theorem isExpanding_toPRG [Fintype Key] [Fintype R]
    (F : Key → D → R) (x : Fin ℓ ↪ D) (hcard : Fintype.card Key < Fintype.card R ^ ℓ) :
    (toPRG F x).IsExpanding := by
  simpa only [PRG.Generator.IsExpanding, Fintype.card_fun, Fintype.card_fin] using hcard

end Proofs

end Cslib.Crypto.PRF
