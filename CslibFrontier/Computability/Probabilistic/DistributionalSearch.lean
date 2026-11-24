/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Probability.Distributional.Search

/-!
# Certified programs for distributional search

A semantic search problem may have parameter-dependent observation and answer types, while a
uniform machine processes one fixed encoded input type and returns one fixed encoded output type.
`HasSolver.of_computableInPolyTime` connects these presentations. It uses the existing
deterministic-to-PPT realization theorem to certify the actual program `fun x => pure (f x)`.

The input presentation and output interpretation are part of the represented-program model,
whose evaluator and `IsPPTOn` predicate remain explicit in the conclusion. They are not operations
granted to the program, and this theorem does not assert that arbitrary transformations preserve
an independently specified computational model. A concrete client supplies its intended input
and output representations and proves the success bound for those representations.

One certificate applies to every represented input. The parameter may determine the semantic
types and the public data presented to the program, but does not select a different program or
a different machine certificate.
-/

public section

namespace Cslib.Probability.DistributionalSearchProblem

open Turing.MultiTapeTM
open scoped ENNReal

/-- A certified deterministic function supplies a uniform strict PPT solver in the explicitly
represented-program model. The representation maps specify the meaning of machine inputs and
outputs; they are not assumed to be free preprocessing or postprocessing in another model. -/
theorem HasSolver.of_computableInPolyTime
    {State Input Output : ℕ → Type*} {EncodedInput EncodedOutput : Type}
    (P : ∀ n, DistributionalSearchProblem (State n) (Input n) (Output n))
    (present : ∀ n, Input n → EncodedInput) (interpret : ∀ n, EncodedOutput → Output n)
    {encInput : EncodedInput ↪ List Bool} {encOutput : EncodedOutput ↪ List Bool}
    {f : EncodedInput → EncodedOutput} (hf : ComputableInPolyTime f encInput encOutput)
    {ε : ℕ → ℝ≥0∞}
    (hfailure : ∀ n, (P n).experiment
      (fun input => PMF.pure (interpret n (f (present n input)))) false ≤ ε n) :
    HasSolver P
      (fun (program : EncodedInput → ProbComp EncodedOutput) n input =>
        (ProbComp.eval (program (present n input))).map (interpret n))
      (IsPPTOn encInput encOutput) ε := by
  refine ⟨fun input => pure (f input), hf.isPPTOn, fun n => ?_⟩
  simpa only [ProbComp.eval_pure, PMF.pure_map] using hfailure n

end Cslib.Probability.DistributionalSearchProblem
