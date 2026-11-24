/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF

/-!
# Distribution distinguishing problems

A `DistinguishingProblem` consists of two discrete laws on the observations supplied to a test.
Its experiment draws from the null law for `false` and the alternative law for `true`, then
runs a randomized Boolean test. The hypothesis bit selects the law; it is not given to the test.

The definition does not choose an encoding, an algorithm class or a resource bound. In
particular, specifying a law does not assert that it has an efficient sampler. A family may use
a different observation type at every parameter. The shared Boolean-game predicates in
`Crypto/Game` can then restrict tests by any model of computation.

`map` and `bind` apply the same deterministic or randomized transformation to both laws. Their
experiment equations express exactly the composition used by distributional reductions;
efficiency and approximation bounds are separate obligations of a concrete reduction.
-/

public section

namespace Cslib.Probability

/-- Two observation laws to be distinguished, independent of a computational model. -/
structure DistinguishingProblem (Input : Type*) where
  /-- The observation law under the null hypothesis. -/
  nullDist : PMF Input
  /-- The observation law under the alternative hypothesis. -/
  alternativeDist : PMF Input

namespace DistinguishingProblem

variable {Input Output : Type*}

/-- Draw from the selected law and run the test, revealing only the sampled observation. -/
@[expose] noncomputable def experiment (P : DistinguishingProblem Input)
    (hypothesis : Bool) (test : Input → PMF Bool) : PMF Bool :=
  (if hypothesis then P.alternativeDist else P.nullDist).bind test

/-- Under the null hypothesis the test receives a sample from `nullDist`. -/
@[simp] theorem experiment_false (P : DistinguishingProblem Input) (test : Input → PMF Bool) :
    P.experiment false test = P.nullDist.bind test := rfl

/-- Under the alternative hypothesis the test receives a sample from `alternativeDist`. -/
@[simp] theorem experiment_true (P : DistinguishingProblem Input) (test : Input → PMF Bool) :
    P.experiment true test = P.alternativeDist.bind test := rfl

/-- A deterministic test pushes the selected input law forward to its Boolean answer. -/
theorem experiment_pure (P : DistinguishingProblem Input) (hypothesis : Bool)
    (test : Input → Bool) :
    P.experiment hypothesis (fun input => PMF.pure (test input)) =
      (if hypothesis then P.alternativeDist else P.nullDist).map test := rfl

/-- A test that ignores its observation has the same answer law under either hypothesis. -/
@[simp] theorem experiment_const (P : DistinguishingProblem Input) (hypothesis : Bool)
    (answer : PMF Bool) : P.experiment hypothesis (fun _ => answer) = answer :=
  PMF.bind_const _ _

/-- Apply one deterministic observation map under both hypotheses. -/
@[expose] noncomputable def map (P : DistinguishingProblem Input) (f : Input → Output) :
    DistinguishingProblem Output where
  nullDist := P.nullDist.map f
  alternativeDist := P.alternativeDist.map f

/-- Apply one randomized observation kernel under both hypotheses. -/
@[expose] noncomputable def bind (P : DistinguishingProblem Input) (kernel : Input → PMF Output) :
    DistinguishingProblem Output where
  nullDist := P.nullDist.bind kernel
  alternativeDist := P.alternativeDist.bind kernel

/-- Testing deterministically transformed observations precomposes the test with the map. -/
theorem experiment_map (P : DistinguishingProblem Input) (f : Input → Output)
    (hypothesis : Bool) (test : Output → PMF Bool) :
    (P.map f).experiment hypothesis test =
      P.experiment hypothesis (fun input => test (f input)) := by
  cases hypothesis <;>
    simp only [experiment_false, experiment_true, map, PMF.bind_map, Function.comp_def]

/-- Testing randomly transformed observations composes the kernel with the test. -/
theorem experiment_bind (P : DistinguishingProblem Input) (kernel : Input → PMF Output)
    (hypothesis : Bool) (test : Output → PMF Bool) :
    (P.bind kernel).experiment hypothesis test =
      P.experiment hypothesis (fun input => (kernel input).bind test) := by
  cases hypothesis <;> simp only [experiment_false, experiment_true, bind, PMF.bind_bind]

/-- Postprocessing the test's answer postprocesses the experiment's answer. -/
theorem experiment_map_answer (P : DistinguishingProblem Input) (hypothesis : Bool)
    (test : Input → PMF Bool) (f : Bool → Bool) :
    P.experiment hypothesis (fun input => (test input).map f) =
      (P.experiment hypothesis test).map f := by
  simp only [experiment, PMF.map_bind]

end DistinguishingProblem

end Cslib.Probability
