/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic

/-!
# Cook reductions between promise problems

A Cook reduction uses one deterministic polynomial-time oracle program that solves the source
promise problem against every language solving the target. Answers outside the target promise,
including malformed query words, are arbitrary. The strict machine certificate bounds the whole
interaction, including the number and length of adaptive queries.

Goldreich's draft, Exercise 2.35 (December 2006 `r1.pdf`, PDF p. 138 / printed p. 113), asserts
that a promise problem Cook-reducible to one solvable in polynomial time is itself solvable in
polynomial time [Goldreich][Goldreich2006DraftR1]. Here `PromiseP` uses total polynomial-time
solvers: the source's possibly nonhalting off-promise solver is first clocked, as its guideline
allows. For typed oracle instances we require a total polynomial-time decoder of their encoding;
ordinary bit strings use `Decoder.bits`.

The completion argument is shared by deterministic promise reductions and the randomized
verifier in `ValiantVazirani/Collapse` through
`PolyTimeOracleProgram.exists_computableInPolyTime_of_mem_PromiseP`.

## Main definitions

* `Cslib.Complexity.PromiseProblem.PolyTimeTuringReducible`: Cook reductions of promise problems.

## Main results

* `Cslib.Complexity.exists_mem_P_solvedBy_of_mem_PromiseP`: an efficient oracle completion.
* `Cslib.Complexity.PolyTimeOracleProgram.exists_computableInPolyTime_of_mem_PromiseP`:
  eliminate an efficient promise oracle from any function specification.
* `Cslib.Complexity.PromiseProblem.PolyTimeTuringReducible.mem_PromiseP`: Exercise 2.35.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type}

open Classical in
/-- A promise problem in `PromiseP` is solved by an oracle language in `P`, under an encoding
with a total decoder: accept the words whose decoded instance the solver accepts. -/
theorem exists_mem_P_solvedBy_of_mem_PromiseP {Q : PromiseProblem β} {encQ : β ↪ List Bool}
    (D : Decoder encQ) (hQ : Q ∈ PromiseP encQ) :
    ∃ A ∈ P encBits, Q.SolvedBy fun b => decide (encQ b ∈ A) := by
  obtain ⟨f, hf, hsolve⟩ := mem_PromiseP_iff.1 hQ
  refine ⟨{w | f (D.decode w) = true}, ⟨_, hf.comp D.computableInPolyTime,
    fun _ => Iff.rfl⟩, ?_⟩
  simpa [D.decode_enc] using hsolve

open Classical in
/-- Eliminate a promise oracle in `PromiseP` from a polynomial-time oracle program, preserving
its specification. Choose one efficient completion, then answer its queries with its decider. -/
theorem PolyTimeOracleProgram.exists_computableInPolyTime_of_mem_PromiseP
    {Q : PromiseProblem γ} {encQ : γ ↪ List Bool}
    {input : α ↪ List Bool} {output : β ↪ List Bool} {Spec : (α → β) → Prop}
    (h : PolyTimeOracleProgram input output
      (fun A => Q.SolvedBy fun b => decide (encQ b ∈ A)) Spec)
    (D : Decoder encQ) (hQ : Q ∈ PromiseP encQ) :
    ∃ f, ComputableInPolyTime f input output ∧ Spec f := by
  obtain ⟨A, hA, hsolve⟩ := exists_mem_P_solvedBy_of_mem_PromiseP D hQ
  obtain ⟨f, hf, hSpec⟩ := h.exists_computableInPolyTimeWithOracle hsolve
  exact ⟨f, hf.computableInPolyTime hA, hSpec⟩

namespace PromiseProblem

open Classical in
/-- A Cook reduction of promise problems: one strict polynomial-time oracle program solves `X`
against every language solving `Y`. Off-promise answers are unrestricted. -/
@[expose] def PolyTimeTuringReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (X : PromiseProblem α) (Y : PromiseProblem β) : Prop :=
  PolyTimeOracleProgram encA encBool
    (fun A => Y.SolvedBy fun b => decide (encB b ∈ A)) X.SolvedBy

/-- **Goldreich's draft Exercise 2.35** (`r1.pdf`, PDF p. 138 / printed p. 113): a promise
problem Cook-reducible to a polynomial-time-solvable promise problem is polynomial-time solvable.
The typed oracle encoding has a total polynomial-time decoder; for words use `Decoder.bits`. -/
theorem PolyTimeTuringReducible.mem_PromiseP {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (h : PolyTimeTuringReducible encA encB X Y) (D : Decoder encB)
    (hY : Y ∈ PromiseP encB) : X ∈ PromiseP encA :=
  mem_PromiseP_iff.2 (h.exists_computableInPolyTime_of_mem_PromiseP D hY)

end PromiseProblem

end Cslib.Complexity
