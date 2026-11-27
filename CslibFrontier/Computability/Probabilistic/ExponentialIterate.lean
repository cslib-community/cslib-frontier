/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Internal.Oracle.BinaryIteration
public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Probability.PMF.Bool
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Binary-counter exponential iteration on fair-coin multitape machines

`Cslib.Probability.IsPPTOn.iterate_spec` clocks bounded adaptive loops in polynomial time when the
iteration count is computed in unary (`encUnary`). Exponential-time randomized algorithms such as
Schöning's `k`-SAT walk instead repeat a polynomial-time step an exponential number of times while
reusing polynomial workspace across restarts.

When the iteration count `count : α → ℕ` is computable in polynomial time in **binary** (`encNat`),
`(encNat (count a)).length` is polynomial in `(input a).length` even when `count a` itself is
exponential. Pairing a binary countdown counter with a polynomially bounded state and running clean
phases inside `Turing.MultiTapePTM.repeatUntilBlank` produces one finite-control `MultiTapePTM`
whose runs:

* halt on every branch within `C * ((count a + 1) * ((input a).length + 1) ^ E)` steps,
* realize `(ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).map stateEncoding`,
* visit at most `C * ((input a).length + 1) ^ E` work-tape cells (`toNTM.RunsInSpace`), independent
  of `count a`.

## Main definitions

* `Cslib.Probability.repeatAnyStep`: one OR-accumulating trial step (`if acc then pure true else
  trial`).

## Main results

* `Cslib.Probability.eval_iterate_repeatAnyStep_false_toReal`: `r` independent trials fail with
  probability `(1 - p) ^ r`.
* `Cslib.Probability.IsPPTOn.exists_multiTapePTM_iterate_binary`: closed binary-counter iteration
  with `(count a + 1) * poly(|input a|)` halting time and polynomial workspace.
* `Cslib.Probability.IsPPTOn.exists_multiTapePTM_iterateWith_binary`: captured-input variant.
* `Cslib.Probability.IsPPTOn.exists_multiTapePTM_repeatAnyBool_binary`: repeating a strict PPT
  Boolean trial an exponential binary-computable number of times in polynomial workspace.
-/

public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
  _root_.Turing.MultiTapePTM

/-! ### Exponential independent Boolean trial repetition -/

/-- One OR-accumulating trial step: keep `true` once reached, otherwise run `trial`. -/
def repeatAnyStep (trial : ProbComp Bool) (acc : Bool) : ProbComp Bool :=
  if acc then pure true else trial

/-- `r` independent trials fail (`false`) with probability `(1 - p) ^ r`, where
`p = (ProbComp.eval trial true).toReal`. -/
theorem eval_iterate_repeatAnyStep_false_toReal (trial : ProbComp Bool) (r : ℕ) :
    (ProbComp.eval (OracleComp.iterate r (repeatAnyStep trial) false) false).toReal =
      (1 - (ProbComp.eval trial true).toReal) ^ r := by
  induction r with
  | zero =>
    simp only [OracleComp.iterate_zero, ProbComp.eval_pure, PMF.pure_apply_self, ENNReal.toReal_one,
      pow_zero]
  | succ r ih =>
    rw [OracleComp.iterate_succ, ProbComp.eval_bind]
    have hfalse_step : ProbComp.eval (repeatAnyStep trial false) = ProbComp.eval trial := rfl
    have htrue_step : ProbComp.eval (repeatAnyStep trial true) = PMF.pure true := rfl
    have hbind : (ProbComp.eval (OracleComp.iterate r (repeatAnyStep trial) false)).bind
        (fun b => ProbComp.eval (repeatAnyStep trial b)) false =
        ProbComp.eval (OracleComp.iterate r (repeatAnyStep trial) false) false *
          ProbComp.eval trial false := by
      rw [PMF.bind_apply, tsum_fintype]
      simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
        Finset.sum_insert, Finset.sum_singleton, htrue_step, hfalse_step, PMF.pure_apply,
        Bool.false_eq_true, ↓reduceIte, mul_zero, zero_add]
    rw [hbind, ENNReal.toReal_mul, ih, PMF.toReal_false_eq_one_sub (ProbComp.eval trial), pow_succ]

/-- When `trial` has zero probability of returning `true`, `r` repetitions return `false` with
probability `1` (exact distribution `PMF.pure false`). -/
theorem eval_iterate_repeatAnyStep_eq_pure_false (trial : ProbComp Bool) (r : ℕ)
    (hzero : ProbComp.eval trial true = 0) :
    ProbComp.eval (OracleComp.iterate r (repeatAnyStep trial) false) = PMF.pure false := by
  have hpure : ProbComp.eval trial = PMF.pure false := by
    ext b
    cases b with
    | false =>
      have hsum := PMF.tsum_coe (ProbComp.eval trial)
      rw [tsum_fintype] at hsum
      simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
        Finset.sum_insert, Finset.sum_singleton, hzero, zero_add] at hsum
      simp only [PMF.pure_apply_self, hsum]
    | true => simp only [hzero, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte]
  induction r with
  | zero => simp only [OracleComp.iterate_zero, ProbComp.eval_pure]
  | succ r ih =>
    rw [OracleComp.iterate_succ, ProbComp.eval_bind, ih, PMF.pure_bind]
    exact hpure

/-- **Repeating a strict PPT Boolean trial an exponential binary-computable number of times.** Given
`htrial : IsPPTOn input encBool trialProg` and `hcount : ComputableInPolyTime trials input encNat`,
one finite-control fair-coin `MultiTapePTM` halts on every branch within
`C * ((trials a + 1) * ((input a).length + 1) ^ E)` steps, runs in polynomial workspace
`C * ((input a).length + 1) ^ E`, never outputs `[true]` when `trialProg a` has zero probability of
`true`, and outputs `[true]` with probability `1 - (1 - p) ^ (trials a)` where
`p = (ProbComp.eval (trialProg a) true).toReal`. -/
theorem IsPPTOn.exists_multiTapePTM_repeatAnyBool_binary {α : Type} {input : α ↪ List Bool}
    {trialProg : α → ProbComp Bool} {trials : α → ℕ}
    (htrial : IsPPTOn input encBool trialProg)
    (hcount : ComputableInPolyTime trials input encNat) :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (C E : ℕ),
      ∀ a,
        let T := C * ((trials a + 1) * ((input a).length + 1) ^ E)
        let S := C * ((input a).length + 1) ^ E
        let μ := ProbComp.eval (OracleComp.iterate (trials a) (repeatAnyStep (trialProg a)) false)
        (∀ final ∈ (ProbComp.eval
            (machine.runClosedConfigFrom T (machine.initialConfig (input a)))).support,
            final.tapes.state = none) ∧
          ProbComp.eval (machine.runClosed T (input a)) = μ.map encBool ∧
          machine.toNTM.RunsInSpace (input a) S := by
  have hstep : IsPPTOn (encPair input encBool) encBool
      (fun pair : α × Bool => repeatAnyStep (trialProg pair.1) pair.2) := by
    refine IsPPTOn.cond (ComputableInPolyTime.snd input encBool)
      (ComputableInPolyTime.const true).isPPTOn ?_
    exact htrial.preprocess (ComputableInPolyTime.fst input encBool)
  obtain ⟨⟨K, Control, hfin, machine, C, E, hM⟩, -⟩ :=
    IsPPTOn.exists_multiTapePTM_iterateWith_binary
      (initial := fun _ : α => false)
      (count := trials)
      (step := fun a b => repeatAnyStep (trialProg a) b)
      hcount (.const false) hstep
      (fun _ _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
      (size := fun _ => 1) (.const 1)
      (fun _ _ b _ _ => by cases b <;> exact le_rfl)
  exact ⟨K, Control, hfin, machine, C, E, hM⟩

end Cslib.Probability
