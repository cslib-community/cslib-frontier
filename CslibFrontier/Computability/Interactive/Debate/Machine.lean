/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Debate

/-!
# Machines with an external stochastic oracle

`Debate.lean` treats a randomized computation as a step law indexed by the whole transcript
prefix. The source of the debate protocol starts from a machine with access to an external
stochastic oracle [BrownCohenIrvingPiliouras2024, Section 3]. This module gives that machine in
the form the protocol uses: at each transcript prefix the next bit is a deterministic function of
the prefix, a fair internal coin, or the reply to a query computed from the prefix.

`Machine.run M n` runs `n` steps as an oracle program over the external interface, so that
[BrownCohenIrvingPiliouras2024, Definition 6.1] for `M` is
`ProbOracleComp.LipschitzAt K O (M.run n)`. `Machine.stepLaw M O` is the step law of `M` against
the oracle `O`, and the two descriptions have the same output law
(`Machine.evalWith_output_stepLaw`).

The transcript is the list of bits written so far, most recent first, and the step may read all
of it; relevant coordinates, tapes and encodings are not modelled.

For machines whose every step queries an encoding of the whole transcript so far
(`prefixMachine`), Definition 6.1 suffices for the soundness step of `Debate.lean`: a perturbation
of the step law is then a perturbation of the external oracle
(`lipschitzAt_stepLaw_of_lipschitzAt_run`, `soundness_of_lipschitzAt_run_prefixMachine`).

## Main definitions

* `Cslib.Interactive.Debate.Step`, `Cslib.Interactive.Debate.Machine`: the three kinds of step,
  and a machine.
* `Cslib.Interactive.Debate.Machine.run`: the machine against an external oracle.
* `Cslib.Interactive.Debate.Machine.stepLaw`: its step law against an oracle.
* `Cslib.Interactive.Debate.prefixMachine`: the machine that queries an encoding of the whole
  transcript at every step.

## Main results

* `Cslib.Interactive.Debate.Machine.evalWith_output_stepLaw`: the output of the step law has the
  law of the machine's run.
* `Cslib.Interactive.Debate.lipschitzAt_stepLaw_of_lipschitzAt_run`: for a machine that queries
  an injective encoding of the whole transcript at every step, Definition 6.1 gives the
  step-law hypothesis.
* `Cslib.Interactive.Debate.soundness_of_lipschitzAt_run_prefixMachine`: the soundness step of
  `Debate.lean` for such machines, under Definition 6.1.

## References

* [J. Brown-Cohen, G. Irving, G. Piliouras, *Scalable AI safety via doubly-efficient debate*,
  Sections 3 and 6][BrownCohenIrvingPiliouras2024]
-/

public section

namespace Cslib.Interactive.Debate

open OracleComp (sumHandler)
open ProbOracleComp (LipschitzAt)
open scoped NNReal

/-- One step of a machine with an external oracle whose replies are bits. -/
inductive Step (Query : Type) where
  /-- Write a bit determined by the transcript so far. -/
  | det (bit : Bool)
  /-- Write a fair internal coin. -/
  | coin
  /-- Write the reply of the external oracle to a query. -/
  | ask (query : Query)

/-- A machine with an external oracle on `Query`: the kind of its next step, as a function of the
bits written so far, most recent first. -/
structure Machine (Query : Type) where
  /-- The next step after the given transcript. -/
  step : List Bool → Step Query

namespace Machine

variable {Query : Type}

/-- The program for the next bit after the transcript `bits`. -/
@[expose] noncomputable def next (M : Machine Query) (bits : List Bool) :
    ProbOracleComp (fun _ : Query => Bool) Bool :=
  match M.step bits with
  | .det bit => pure bit
  | .coin => ProbOracleComp.sample (ProbComp.uniform Bool)
  | .ask query => ProbOracleComp.query query

/-- The transcript of the first `n` steps, most recent bit first. -/
@[expose] noncomputable def transcript (M : Machine Query) :
    ℕ → ProbOracleComp (fun _ : Query => Bool) (List Bool)
  | 0 => pure []
  | n + 1 => do
    let bits ← M.transcript n
    let bit ← M.next bits
    pure (bit :: bits)

/-- The output of `n` steps of the machine against an external oracle: the last bit of its
transcript (`false` when `n = 0`). -/
@[expose] noncomputable def run (M : Machine Query) (n : ℕ) :
    ProbOracleComp (fun _ : Query => Bool) Bool :=
  (fun bits => bits.headD false) <$> M.transcript n

/-- The step law of the machine against the oracle `O`: a point mass at a deterministic step, a
fair coin at a coin step, and the reply law of `O` at a query step. -/
@[expose] noncomputable def stepLaw (M : Machine Query) (O : Query → PMF Bool) :
    List Bool → PMF Bool := fun bits =>
  match M.step bits with
  | .det bit => PMF.pure bit
  | .coin => Probability.PMF.uniformOfFintype Bool
  | .ask query => O query

/-- The next bit of the machine against `O` has the law given by its step law. -/
theorem evalWith_next (M : Machine Query) (O : Query → PMF Bool) (bits : List Bool) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle O) (M.next bits) = M.stepLaw O bits := by
  unfold next stepLaw
  cases M.step bits with
  | det bit => rfl
  | coin =>
    change OracleComp.evalWith _ (ProbOracleComp.sample (ProbComp.uniform Bool)) = _
    rw [OracleComp.evalWith_eq_interpret, ProbOracleComp.interpret_sample,
      ← OracleComp.evalWith_eq_interpret]
    exact ProbComp.eval_uniform Bool
  | ask query => exact OracleComp.evalWith_query _ _

/-- The transcript of the step law of a machine has the law of the machine's transcript. -/
theorem evalWith_transcript_stepLaw (M : Machine Query) (O : Query → PMF Bool) :
    ∀ n, OracleComp.evalWith (sumHandler ProbComp.unifOracle (M.stepLaw O)) (Debate.transcript n) =
      OracleComp.evalWith (sumHandler ProbComp.unifOracle O) (M.transcript n)
  | 0 => rfl
  | n + 1 => by
    have hquery (bits : List Bool) :
        OracleComp.evalWith (sumHandler ProbComp.unifOracle (M.stepLaw O))
          (ProbOracleComp.query (spec := StepSpec) bits) = M.stepLaw O bits :=
      OracleComp.evalWith_query _ _
    simp only [Debate.transcript, Machine.transcript, OracleComp.evalWith_bind,
      OracleComp.evalWith_pure, hquery, evalWith_next, evalWith_transcript_stepLaw M O n]

/-- The output of the step law of a machine has the law of the machine's run: the prefix-indexed
description of `Debate.lean` and the run against the external oracle agree. -/
theorem evalWith_output_stepLaw (M : Machine Query) (O : Query → PMF Bool) (n : ℕ) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle (M.stepLaw O)) (output n) =
      OracleComp.evalWith (sumHandler ProbComp.unifOracle O) (M.run n) := by
  rw [output, run, OracleComp.evalWith_map, OracleComp.evalWith_map,
    evalWith_transcript_stepLaw]

end Machine

/-! ### Machines that query the whole transcript -/

variable {Query : Type}

/-- The machine whose every step asks the external oracle at an encoding of the whole
transcript so far. With `Query = List Bool` and `enc = id` it asks the transcript itself. -/
@[expose] def prefixMachine (enc : List Bool → Query) : Machine Query where
  step bits := .ask (enc bits)

/-- The step law of a machine that queries an encoding of the whole transcript is the oracle at
that encoding. -/
theorem stepLaw_prefixMachine (enc : List Bool → Query) (O : Query → PMF Bool)
    (bits : List Bool) : (prefixMachine enc).stepLaw O bits = O (enc bits) :=
  rfl

/-- With the identity encoding the step law is the oracle. -/
theorem stepLaw_prefixMachine_id (O : List Bool → PMF Bool) :
    (prefixMachine (id : List Bool → List Bool)).stepLaw O = O :=
  rfl

private theorem transcript_prefixMachine_id :
    ∀ n, (prefixMachine (id : List Bool → List Bool)).transcript n = transcript n
  | 0 => rfl
  | n + 1 => by
    have hnext (bits : List Bool) :
        (prefixMachine (id : List Bool → List Bool)).next bits =
          ProbOracleComp.query (spec := StepSpec) bits := rfl
    simp only [Machine.transcript, transcript, hnext, transcript_prefixMachine_id n]

/-- With the identity encoding the machine's run is the output program of `Debate.lean`. -/
theorem run_prefixMachine_id (n : ℕ) :
    (prefixMachine (id : List Bool → List Bool)).run n = output n := by
  rw [Machine.run, output, transcript_prefixMachine_id]

/-- **Definition 6.1 gives the step-law hypothesis** for machines whose every step queries an
injective encoding of the whole transcript so far: every step law near the machine's is the
step law of the machine against a nearby oracle, so being Lipschitz in the external oracle
([BrownCohenIrvingPiliouras2024, Definition 6.1]) is being Lipschitz in the whole step law. -/
theorem lipschitzAt_stepLaw_of_lipschitzAt_run {enc : List Bool → Query}
    (henc : Function.Injective enc) {K : ℝ≥0} {O : Query → PMF Bool} {n : ℕ}
    (h : LipschitzAt K O ((prefixMachine enc).run n)) :
    LipschitzAt K ((prefixMachine enc).stepLaw O) (output n) := by
  classical
  intro law' ε hε
  -- The oracle that answers the encoding of a transcript as `law'` answers the transcript.
  let O' : Query → PMF Bool := fun query =>
    if hq : ∃ bits, enc bits = query then law' (Classical.choose hq) else O query
  have hO' (query : Query) : Probability.CloseTo (O query) (O' query) ε := by
    by_cases hq : ∃ bits, enc bits = query
    · have hclose := hε (Classical.choose hq)
      rw [stepLaw_prefixMachine, Classical.choose_spec hq] at hclose
      simpa only [O', hq, ↓reduceDIte] using hclose
    · simpa only [O', hq, ↓reduceDIte] using (Probability.CloseTo.refl (O query)).mono zero_le
  have hstep : (prefixMachine enc).stepLaw O' = law' := by
    funext bits
    have hq : ∃ bits', enc bits' = enc bits := ⟨bits, rfl⟩
    rw [stepLaw_prefixMachine]
    simp only [O', hq, ↓reduceDIte]
    rw [henc (Classical.choose_spec hq)]
  have hrun := h O' ε hO'
  rwa [← Machine.evalWith_output_stepLaw, ← Machine.evalWith_output_stepLaw, hstep] at hrun

/-- **Soundness under Definition 6.1 for machines that query the whole transcript.** A step
toward [BrownCohenIrvingPiliouras2024, Theorem 6.2], not that theorem: for machines whose every
step queries an injective encoding of the whole transcript so far, Definition 6.1 suffices for
the soundness step `soundness_of_lipschitzAt_stepLaw`. If the output of such a machine of
`T + 1` steps is `K`-Lipschitz at the external oracle and is `true` with probability at most
`1 / 3`, then against the honest challenger every proposer makes the verifier accept with
probability at most `2 / 5`.

The protocol is `Debate.run`: claims and coins lie on a grid, and the interpreter draws the bit
of each round from the claim and the two coins. Nothing is claimed about running time or query
counts, and the constants are `Params.default`. -/
theorem soundness_of_lipschitzAt_run_prefixMachine {enc : List Bool → Query}
    (henc : Function.Injective enc) {K : ℝ≥0} (hK : 0 < K) (T : ℕ) {O : Query → PMF Bool}
    (hL : LipschitzAt K O ((prefixMachine enc).run (T + 1)))
    (hno : OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
      ((prefixMachine enc).run (T + 1)) true ≤ 1 / 3)
    (A : Proposer (Params.default K T).grid) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle ((prefixMachine enc).stepLaw O))
      (run (Params.default K T) A (honestChallenger (Params.default K T))) true ≤ 2 / 5 :=
  soundness_of_lipschitzAt_stepLaw hK T (lipschitzAt_stepLaw_of_lipschitzAt_run henc hL)
    (by rwa [Machine.evalWith_output_stepLaw]) A

end Cslib.Interactive.Debate
