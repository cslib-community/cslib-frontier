/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Game.Inversion
public import CslibFrontier.Probability.Distributional.Search

/-!
# Inversion and prediction as distributional search

The existing inversion and prediction experiments are instances of partially observed
distributional search. In both cases the hidden state is the sampled input, and the observation
is its image. Inversion accepts any preimage of that image; prediction accepts the designated
bit of the sampled input. The equality theorems below identify the complete Boolean laws with
`inversionExperiment` and `predictionExperiment`, so their existing probability bounds apply.

These constructions specify search problems, without imposing a new security or computation
model. A `DistributionalSearchProblem.HasSolver` instance supplies an evaluator and admissibility
predicate; the existing cryptographic game notions can instead quantify over adversaries.

## Main definitions

* `Cslib.Crypto.inversionSearchProblem`: return any preimage of the observed image.
* `Cslib.Crypto.predictionSearchProblem`: predict a hidden bit from the observed image.

## Main results

* `Cslib.Crypto.experiment_inversionSearchProblem`: the search and inversion experiments agree.
* `Cslib.Crypto.experiment_predictionSearchProblem`: the search and prediction experiments agree.
-/

public section

namespace Cslib.Crypto

open Probability

variable {α : Type} {β : Type*}

/-- Inversion as distributional search: the solver sees `f x` and may return any of its preimages.
Recovering the particular sampled input is not required. -/
@[expose] def inversionSearchProblem (sample : PMF α) (f : α → β) :
    DistributionalSearchProblem α β α where
  distribution := sample
  observe := f
  accepts := fun x answer => f answer = f x

/-- Predicting a hidden bit as distributional search: the solver sees `f x` and must return `h x`.
The input `x` remains available to the success test only. -/
@[expose] def predictionSearchProblem (sample : PMF α) (f : α → β) (h : α → Bool) :
    DistributionalSearchProblem α β Bool where
  distribution := sample
  observe := f
  accepts := fun x answer => answer = h x

/-- With lawful Boolean equality, mathematical inversion success is exactly the existing
inversion experiment's success test, including for noninjective functions. -/
@[simp] theorem experiment_inversionSearchProblem [BEq β] [LawfulBEq β]
    (sample : PMF α) (f : α → β) (inverter : β → PMF α) :
    (inversionSearchProblem sample f).experiment inverter =
      inversionExperiment sample f inverter := by
  classical
  rw [DistributionalSearchProblem.experiment, inversionExperiment_eq_bind_map]
  apply congrArg (PMF.bind sample)
  funext x
  apply congrArg (fun score : α → Bool => (inverter (f x)).map score)
  funext answer
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, beq_iff_eq]
  rfl

/-- Distributional search reproduces the existing hidden-bit prediction experiment. -/
@[simp] theorem experiment_predictionSearchProblem
    (sample : PMF α) (f : α → β) (h : α → Bool) (predictor : β → PMF Bool) :
    (predictionSearchProblem sample f h).experiment predictor =
      predictionExperiment sample f h predictor := by
  classical
  rw [DistributionalSearchProblem.experiment]
  simp only [predictionExperiment, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map, Function.comp_def]
  apply congrArg (PMF.bind sample)
  funext x
  apply congrArg (PMF.bind (predictor (f x)))
  funext answer
  apply congrArg PMF.pure
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, beq_iff_eq]
  rfl

end Cslib.Crypto
