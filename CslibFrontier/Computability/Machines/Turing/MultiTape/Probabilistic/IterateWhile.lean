/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelIterateWhile
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.IterateWhileLayout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop.ExpectedTime
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Iterating a probabilistic oracle machine while its result is non-empty

`tm.iterateWhile mark` applies the tidy probabilistic oracle machine `tm` to its input, then to
the result, and so on, until `tm` produces the empty word, and then outputs the last word before
the empty one. The machine keeps the current word on one work tape and the next word on another.
A round copies the next word to the current tape and computes the new next word from it with `tm`.
Rounds are repeated by `Turing.MultiTapePTM.repeatUntilBlank` until the next word is empty.
The tape layout is shared with the deterministic construction through
`Turing.MultiTapeTM.IterateWhile`.

Each round makes exactly the oracle calls of `tm` on the current word, with the external oracle
state left by the previous round. The final round's program returns the empty word, and the loop
then halts; no further round is executed.

## Main definitions

* `Turing.MultiTapePTM.iterateWhileRound`: one round of the iteration.
* `Turing.MultiTapePTM.iterateWhile`: the iterating machine.

## Main results

* `Turing.MultiTapePTM.ComputesTidily.iterateWhile`: if `tm` tidily computes `step w` from every
  word `w` reached in the first `r` rounds and the empty word in round `r`, then
  `tm.iterateWhile mark` tidily computes `OracleComp.iterate r step`, preserving the joint law of
  the result and the external oracle state.
* `Turing.MultiTapePTM.RunsInSpace.iterateWhile`: the same supplied closed machine uses
  workspace independent of the number of rounds, with an explicit terminal-round certificate.
* `Turing.MultiTapePTM.tsum_toOuterMeasure_compl_iterateWhile_le`: a Las Vegas iteration, whose
  rounds stop at a random round and continue with probability at most `q`, halts with an answer
  with probability tending to one, within expected time `O(D / (1 - q))` for rounds of `D` steps.

## References

Adapts `Combinators/IterateWhile` (vendored crei:crei/tidy-universal @7f7c0696), by Christian
Reitwiessner, and cslib's `Plumbing/RepeatUntilBlank` to probabilistic oracle machines.
-/

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeTM

variable {k : ℕ} {State Operation : Type} {x : List Bool} [DecidableEq Operation]

namespace IterateWhile

open Turing.MultiTapeTM.IterateWhile

/-- The words on the current and next tapes determine the tapes. -/
theorem words_injective : Function.Injective (fun p : List Bool × List Bool =>
    words (k := k) p.1 p.2) := by
  rintro ⟨vc, vn⟩ ⟨vc', vn'⟩ h
  exact Prod.ext (by simpa only [words_cur] using congrFun h (curTape k))
    (by simpa only [words_next] using congrFun h (nextTape k))

/-! ### The deterministic phases -/

/-- The states of `Turing.MultiTapePTM.IterateWhile.prepareRound`. -/
public abbrev PrepareState : Type :=
  (Unit ⊕ RewindWorkState) ⊕
    (MarkWorkState ⊕ ((Unit ⊕ RewindState) ⊕ RewindWorkState) ⊕ MarkWorkState) ⊕
      (Unit ⊕ RewindWorkState)

/-- The states of `Turing.MultiTapePTM.IterateWhile.finish`. -/
public abbrev FinishState : Type :=
  (MarkWorkState ⊕ (Unit ⊕ RewindState) ⊕ MarkWorkState) ⊕ (Unit ⊕ RewindWorkState)

/-- The states of `Turing.MultiTapePTM.iterateWhileRound`. -/
public abbrev RoundState (State : Type) : Type :=
  PrepareState ⊕ (MarkWorkState ⊕ (State ⊕ RewindWorkState) ⊕ MarkWorkState)

/-- The states of `Turing.MultiTapePTM.iterateWhile`. -/
public abbrev MachineState (State : Type) : Type :=
  ((Unit ⊕ RewindState) ⊕ RewindWorkState) ⊕
    ((RoundState State ⊕ Unit) ⊕ FinishState)

variable (k) in
/-- Prepare a round: clear the current tape, copy the next word to it and clear the next tape,
using `mark` to flag the left end of words. -/
noncomputable def prepareRound (mark : Bool) : MultiTapeTM (k + 1 + 2) Bool PrepareState :=
  Turing.MultiTapeTM.IterateWhile.prepareRound (k := k) mark

variable (k) in
/-- Finish the iteration: output the current word and clear its tape. -/
noncomputable def finish (mark : Bool) : MultiTapeTM (k + 1 + 2) Bool FinishState :=
  (emitWord (emitEmb k) mark).seq
    ((MultiTapeTM.clearWork Bool).extendTapes (tapeEmb (curTape k)))

/-- Preparing a round moves the next word `v` to the current tape, replacing `vp`. -/
theorem transformsTapes_prepareRound (mark : Bool) (vp v : List Bool) :
    TransformsTapes (prepareRound k mark) (fun _ ws => ws = words vp v)
      (fun _ _ ws' e => ws' = words v [] ∧ e = [])
      (3 * vp.length + 6 * v.length + 16) (vp.length + 5 * v.length + 3 * (k + 1 + 2) + 17) :=
  Turing.MultiTapeTM.IterateWhile.transformsTapes_prepareRound mark vp v

/-- Finishing outputs the current word `v` and leaves every tape blank. -/
theorem transformsTapes_finish (mark : Bool) (v : List Bool) :
    TransformsTapes (finish k mark) (fun _ ws => ws = words v [])
      (fun _ _ ws' e => ws' = (fun _ => []) ∧ e = v)
      (5 * v.length + 11) (3 * v.length + 2 * (k + 1 + 2) + 11) := by
  have hemit := (transformsTapes_emitWord (emitEmb k) mark v).imp
    (P' := fun _ ws => ws = words v []) (Q' := fun _ _ ws' e => ws' = words v [] ∧ e = v)
    (fun _ _ h => by subst h; simp) (fun _ _ _ _ h ⟨h', he⟩ => ⟨h'.trans h, he⟩) le_rfl le_rfl
  have hclear := (transformsTapes_clearWork_tapeEmb (curTape k) v).imp
    (P' := fun _ ws => ws = words v []) (Q' := fun _ _ ws' e => ws' = (fun _ => []) ∧ e = [])
    (fun _ _ h => by rw [h, words_cur])
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, update_words_cur, words_nil_nil], he⟩) le_rfl le_rfl
  exact (hemit.seq_eq hclear).imp (fun _ _ h => h)
    (fun _ _ _ _ _ ⟨h', he⟩ => ⟨h', by simp [he]⟩) (by omega) (by omega)

end IterateWhile

open IterateWhile

/-! ### The machine -/

/-- One round: move the next word to the current tape, then apply `tm` from the current tape to
the next tape, using `mark` to flag the left end of words. -/
public noncomputable def iterateWhileRound (tm : MultiTapePTM k Bool State Operation)
    (mark : Bool) :
    MultiTapePTM (k + 1 + 2) Bool (RoundState State) Operation :=
  (ofDeterministic (prepareRound k mark)).seq (tm.onWords mark)

/-- `tm`, applied repeatedly while its result is non-empty, using `mark` to flag the left end of
words: load the input to the next tape, repeat rounds until the next tape is empty, then output
the current word and clear its tape. -/
public noncomputable def iterateWhile (tm : MultiTapePTM k Bool State Operation) (mark : Bool) :
    MultiTapePTM (k + 1 + 2) Bool (MachineState State) Operation :=
  (ofDeterministic (loadWord Bool (nextTape k))).seq
    ((repeatUntilBlank (nextTape k) (tm.iterateWhileRound mark)).seq
      (ofDeterministic (finish k mark)))

/-- A round moves `v` to the current tape and replaces it on the next tape by the result of
`tm` on `v`, making exactly the oracle calls of `tm`. -/
theorem RunsWords.iterateWhileRound {tm : MultiTapePTM k Bool State Operation} (mark : Bool)
    {vp v : List Bool} {t l : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : tm.ComputesTidily v t program)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w' : List Bool) (s' : OracleState),
      (w', s') ∈ (ProbOracleComp.runWith oracle program
          s).support → w'.length ≤ l) (out₀ : List Bool) :
    (tm.iterateWhileRound mark).RunsWords x (words vp v) out₀
      (3 * vp.length + 6 * v.length + 16 + (t + l + 6)) program (fun v' => words v v')
      (fun _ => []) := by
  have h₁ := RunsWords.of_transformsTapes (Operation := Operation) (x := x) (out₀ := out₀)
    (Turing.MultiTapePTM.IterateWhile.transformsTapes_prepareRound (k := k) mark vp v)
    rfl (ws' := words v []) (emitted := []) (fun _ _ hQ => hQ)
  exact h₁.seq_pure_left (words_nil_next v ▸ h.onWords_of_le mark hl (out₀ ++ []))

namespace IterateWhile

private def liftedStep
    (step : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool))
    (p : List Bool × List Bool) :
    ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool × List Bool) :=
  (fun v' => (p.2, v')) <$> step p.2

private def liftedLast (p : List Bool × List Bool) :
    ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool × List Bool) :=
  pure (p.2, [])

private def liftedInvariant (invariant : ℕ → List Bool → Prop) (L n : ℕ)
    (p : List Bool × List Bool) : Prop := invariant n p.2 ∧ p.1.length ≤ L

omit [DecidableEq Operation] in
private theorem lifted_preserve {r L : ℕ}
    {step : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (invariant : ℕ → List Bool → Prop)
    (hpreserve : ∀ n < r, ∀ w, invariant n w →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (s s' : OracleState) (w' : List Bool),
        (w', s') ∈ (ProbOracleComp.runWith oracle (step w) s).support →
          invariant (n + 1) w' ∧ w' ≠ [])
    (hlength : ∀ n ≤ r, ∀ w, invariant n w → w.length ≤ L) :
    ∀ n < r, ∀ p, liftedInvariant invariant L n p →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (p' : List Bool × List Bool),
        (p', st') ∈ (ProbOracleComp.runWith oracle (liftedStep step p) st).support →
          liftedInvariant invariant L (n + 1) p' ∧ p'.2 ≠ [] := by
  intro n hn p hp _ oracle st st' p' hp'
  simp only [liftedStep, ProbOracleComp.runWith_map, PMF.mem_support_map_iff] at hp'
  obtain ⟨⟨w', st''⟩, hw', ⟨⟩⟩ := hp'
  obtain ⟨hinv, hne⟩ := hpreserve n hn p.2 hp.1 _ oracle st st'' w' hw'
  exact ⟨⟨hinv, hlength n hn.le p.2 hp.1⟩, hne⟩

omit [DecidableEq Operation] in
private theorem lifted_final_support {r L : ℕ} {w₀ : List Bool}
    {step : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (invariant : ℕ → List Bool → Prop) (hbase : invariant 0 w₀)
    (hpreserve : ∀ n < r, ∀ w, invariant n w →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (s s' : OracleState) (w' : List Bool),
        (w', s') ∈ (ProbOracleComp.runWith oracle (step w) s).support →
          invariant (n + 1) w' ∧ w' ≠ [])
    (hlength : ∀ n ≤ r, ∀ w, invariant n w → w.length ≤ L) :
    ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState) (p : List Bool × List Bool),
      (p, s') ∈ (ProbOracleComp.runWith oracle
        (OracleComp.iterate r (liftedStep step) ([], w₀) >>= liftedLast) s).support →
        p.2 = [] ∧ p.1.length ≤ L := by
  intro _ oracle s s' p hp
  rw [ProbOracleComp.runWith_bind] at hp
  obtain ⟨⟨mid, s₁⟩, hmid, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
  simp only [liftedLast, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hp
  obtain ⟨rfl, -⟩ := hp
  have hmidInv := OracleComp.iterate_invariant (liftedInvariant invariant L)
    (⟨hbase, Nat.zero_le L⟩ : liftedInvariant invariant L 0 ([], w₀))
    (fun n p hn hp p' hp' => by
      obtain ⟨_, oracle', st, st', hp'⟩ := ProbOracleComp.mem_support_iff_exists.mp hp'
      rw [← ProbOracleComp.runWith_eq_run_interpret] at hp'
      exact (lifted_preserve invariant hpreserve hlength n hn p hp _ oracle' st st' p' hp').1)
    mid (ProbOracleComp.mem_support_of_mem oracle hmid)
  exact ⟨rfl, hlength r le_rfl mid.2 hmidInv.1⟩

private theorem runsWords_liftedRound {tm : MultiTapePTM k Bool State Operation} (mark : Bool)
    {p : List Bool × List Bool} {t L : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : tm.ComputesTidily p.2 t program)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w' : List Bool) (s' : OracleState),
      (w', s') ∈ (ProbOracleComp.runWith oracle program s).support → w'.length ≤ L)
    (hp : p.1.length ≤ L) (hv : p.2.length ≤ L) (out : List Bool) :
    (tm.iterateWhileRound mark).RunsWords x (words p.1 p.2) out (t + 10 * L + 22)
      ((fun v' => (p.2, v')) <$> program) (fun q => words q.1 q.2) (fun _ => []) :=
  ((RunsWords.iterateWhileRound (x := x) mark (vp := p.1) h hl out).of_map
    (fun v' => (p.2, v')) (fun q => words q.1 q.2) (fun _ => [])).mono (by omega)

private theorem runsWords_liftedLast {tm : MultiTapePTM k Bool State Operation} (mark : Bool)
    {p : List Bool × List Bool} {t L : ℕ}
    (h : tm.ComputesTidily p.2 t (pure []))
    (hp : p.1.length ≤ L) (hv : p.2.length ≤ L) (out : List Bool) :
    (tm.iterateWhileRound mark).RunsWords x (words p.1 p.2) out (t + 10 * L + 22)
      (liftedLast p) (fun q => words q.1 q.2) (fun _ => []) := by
  simpa only [map_pure, liftedLast] using runsWords_liftedRound (x := x) mark h
    (fun _ _ _ w' _ hw' => by
      simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hw'
      simp [hw'.1]) hp hv out

omit [DecidableEq Operation] in
private theorem liftedLast_stops (p : List Bool × List Bool)
    (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (st st' : OracleState) (p' : List Bool × List Bool)
    (hp' : (p', st') ∈ (ProbOracleComp.runWith oracle (liftedLast p) st).support) :
    words (k := k) p'.1 p'.2 (nextTape k) = [] := by
  simp only [liftedLast, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hp'
  rw [hp'.1]
  exact words_next _ _

end IterateWhile

/-- If `tm` tidily computes `step w` within `t` steps from every word `w` reached after `n < r`
rounds, and the empty word from every word reached after `r` rounds, all these words having length
at most `L`, then `tm.iterateWhile mark` tidily computes `OracleComp.iterate r step`. Each round
makes exactly the oracle calls of `tm` on its word, with the external oracle state left by the
previous round, and no round follows the one producing the empty word. -/
public theorem ComputesTidily.iterateWhile {tm : MultiTapePTM k Bool State Operation} (mark : Bool)
    {r t L : ℕ} {w₀ : List Bool}
    {step : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (invariant : ℕ → List Bool → Prop) (hbase : invariant 0 w₀)
    (hround : ∀ n < r, ∀ w, invariant n w → tm.ComputesTidily w t (step w))
    (hpreserve : ∀ n < r, ∀ w, invariant n w →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (s s' : OracleState) (w' : List Bool),
        (w', s') ∈ (ProbOracleComp.runWith oracle (step w)
            s).support → invariant (n + 1) w' ∧ w' ≠ [])
    (hlast : ∀ w, invariant r w → tm.ComputesTidily w t (pure []))
    (hlength : ∀ n ≤ r, ∀ w, invariant n w → w.length ≤ L) :
    (tm.iterateWhile mark).ComputesTidily w₀ ((r + 1) * (t + 10 * L + 23) + 8 * L + 17)
      (OracleComp.iterate r step w₀) := by
  have hloop (out : List Bool) := RunsWords.repeatUntilBlank (nextTape k)
    (body := tm.iterateWhileRound mark) (x := w₀) (out₀ := out) (words_injective (k := k))
    (step := liftedStep step) (last := liftedLast) (t := t + 10 * L + 22)
    (rounds := r) (s₀ := ([], w₀)) (liftedInvariant invariant L) ⟨hbase, by simp⟩
    (fun n hn p hp => runsWords_liftedRound mark (hround n hn p.2 hp.1)
      (fun _ oracle st w' st' hw' =>
        hlength (n + 1) hn w' (hpreserve n hn p.2 hp.1 _ oracle st st' w' hw').1)
      hp.2 (hlength n hn.le p.2 hp.1) out)
    (fun p hp => runsWords_liftedLast mark (hlast p.2 hp.1)
      hp.2 (hlength r le_rfl p.2 hp.1) out)
    (by simpa only [words_next] using lifted_preserve invariant hpreserve hlength)
    (fun p _ => liftedLast_stops (k := k) p)
  have hinner (out : List Bool) := (hloop out).seq_pure_right
    (second := ofDeterministic (finish k mark)) (t₂ := 5 * L + 11)
    (ws₂ := fun _ _ => []) (emit₂ := fun p => p.1)
    (fun _ _ h => words_injective (congrArg Prod.fst h))
    (fun p _ oracle s s' hp => by
      obtain ⟨hnil, hlen⟩ :=
        lifted_final_support invariant hbase hpreserve hlength _ oracle s s' p hp
      exact (RunsWords.of_transformsTapes (transformsTapes_finish (k := k) mark p.1)
        (congrArg (words p.1) hnil) (ws' := fun _ => []) (emitted := p.1) (fun _ _ hQ => hQ)).mono
        (by omega))
  have hload (out : List Bool) := RunsWords.of_transformsTapes (Operation := Operation) (x := w₀)
    (out₀ := out)
    (transformsTapes_loadWord (nextTape k) w₀) ⟨rfl, rfl⟩ (ws' := words (k := k) [] w₀)
    (emitted := []) (fun _ _ h => ⟨h.1.trans (words_nil_cur w₀).symm, h.2⟩)
  intro out₀
  have hall := ((hload out₀).seq_pure_left (hinner (out₀ ++ []))).of_map Prod.fst
    (fun _ _ => []) id
  have hprogram : Prod.fst <$> (OracleComp.iterate r (liftedStep step) ([], w₀) >>= liftedLast) =
      OracleComp.iterate r step w₀ := by
    calc
      _ = Prod.snd <$> OracleComp.iterate r (liftedStep step) ([], w₀) := by
        simp only [map_bind, liftedLast, map_pure, bind_pure_comp]
      _ = _ :=
        (OracleComp.iterate_map r (liftedStep step) step Prod.snd
          (fun p => by simp only [liftedStep, Functor.map_map, id_map']) ([], w₀)).symm
  rw [hprogram] at hall
  have := hlength 0 (Nat.zero_le _) w₀ hbase
  refine hall.mono ?_
  rw [show (r + 1) * (t + 10 * L + 22 + 1) = (r + 1) * (t + 10 * L + 23) by ring]
  omega

/-- A supplied closed machine satisfying the normal and terminal round certificates uses
workspace independent of the round count. The terminal `hlast` premise has the same per-round
time bound as every normal step. -/
public theorem RunsInSpace.iterateWhile {tm : MultiTapePTM k Bool State Empty} (mark : Bool)
    {r t L : ℕ} {w₀ : List Bool}
    {step : List Bool → ProbOracleComp (fun _ : Empty × List Bool => List Bool) (List Bool)}
    (invariant : ℕ → List Bool → Prop) (hbase : invariant 0 w₀)
    (hround : ∀ n < r, ∀ w, invariant n w → tm.ComputesTidily w t (step w))
    (hpreserve : ∀ n < r, ∀ w, invariant n w →
      ∀ (OracleState : Type) (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
        (s s' : OracleState) (w' : List Bool),
        (w', s') ∈ (ProbOracleComp.runWith oracle (step w)
            s).support → invariant (n + 1) w' ∧ w' ≠ [])
    (hlast : ∀ w, invariant r w → tm.ComputesTidily w t (pure []))
    (hlength : ∀ n ≤ r, ∀ w, invariant n w → w.length ≤ L) :
    (tm.iterateWhile mark).toNTM.RunsInSpace w₀
      ((k + 1 + 2) * (2 * (t + 10 * L + 22) + 1)) := by
  have hbound := runsInSpace_toNTM_seq_repeatUntilBlank
    (first := ofDeterministic (loadWord Bool (nextTape k)))
    (body := tm.iterateWhileRound mark) (lastM := ofDeterministic (finish (k := k) mark))
    (t₁ := 3 * L + 6) (t := t + 10 * L + 22) (t₂ := 5 * L + 11) (rounds := r) (s₀ := ([], w₀))
    (ws := fun q => words q.1 q.2)
    (step := liftedStep step) (last := liftedLast)
    (hfirst := (RunsWords.of_transformsTapes (Operation := Empty) (x := w₀) (out₀ := [])
        (ws₀ := fun _ => []) (transformsTapes_loadWord (nextTape k) w₀) ⟨rfl, rfl⟩
        (ws' := words (k := k) [] w₀) (emitted := [])
        (fun _ _ h => ⟨h.1.trans (words_nil_cur w₀).symm, h.2⟩)).mono (time' := 3 * L + 6)
      (by have := hlength 0 (by omega) w₀ hbase; omega))
    (nextTape k) words_injective (liftedInvariant invariant L) ⟨hbase, Nat.zero_le L⟩
    (fun n hn p hp => runsWords_liftedRound mark (hround n hn p.2 hp.1)
      (fun _ oracle st w' st' hw' =>
        hlength (n + 1) hn w' (hpreserve n hn p.2 hp.1 _ oracle st st' w' hw').1)
      hp.2 (hlength n hn.le p.2 hp.1) [])
    (fun p hp => runsWords_liftedLast mark (hlast p.2 hp.1)
      hp.2 (hlength r le_rfl p.2 hp.1) [])
    (by simpa only [words_next] using lifted_preserve invariant hpreserve hlength)
    (fun p _ => liftedLast_stops (k := k) p)
    (fun _ oracle s s' p hp => by
      obtain ⟨hnil, hlen⟩ :=
        lifted_final_support invariant hbase hpreserve hlength _ oracle s s' p hp
      exact (RunsWords.of_transformsTapes (Operation := Empty)
        (transformsTapes_finish (k := k) mark p.1)
        (hP := congrArg (words p.1) hnil) (hQ := fun _ _ h => h)
        (ws' := fun _ => []) (emitted := p.1)).mono (time' := 5 * L + 11) (by omega))
  exact hbound.mono (Nat.mul_le_mul_left _ (by omega))

open scoped ENNReal in
open IterateWhile RepeatUntilBlank in
/-- **Las Vegas iteration.** Let the words of an iteration be *retry* words, from which `tm` draws
the next word by `step` within `t` steps, and *answer* words, from which `tm` produces the empty
word within `t` steps, all non-empty and of length at most `L`. If from a retry word the next word
is again a retry word with probability at most `q`, and otherwise an answer word, then
`tm.iterateWhile mark`, started on a retry word, halts with an answer word as output with
probability tending to one: summed over all clocks, the probability of not having done so is at
most `8 * L + 17 + D + D * (1 - q)⁻¹` for the round time `D = t + 10 * L + 23`. In particular this
bounds the expected running time. -/
public theorem tsum_toOuterMeasure_compl_iterateWhile_le {tm : MultiTapePTM k Bool State}
    (mark : Bool)
    {t L : ℕ} {q : ℝ≥0∞} {retry answer : Set (List Bool)} {step : List Bool → ProbComp (List Bool)}
    {w₀ : List Bool} (hw₀ : w₀ ∈ retry)
    (hretry : ∀ w ∈ retry, tm.ComputesTidily w t (ProbOracleComp.sample (step w)))
    (hanswer : ∀ w ∈ answer, tm.ComputesTidily w t (pure []))
    (hsupport : ∀ w ∈ retry, ∀ w' ∈ (ProbComp.eval (step w)).support, w' ∈ retry ∨ w' ∈ answer)
    (hq : ∀ w ∈ retry, (ProbComp.eval (step w)).toOuterMeasure retry ≤ q)
    (hlength : ∀ w, w ∈ retry ∨ w ∈ answer → w ≠ [] ∧ w.length ≤ L) :
    ∑' s, (ProbComp.eval ((tm.iterateWhile mark).runClosedConfigFrom s
      ((tm.iterateWhile mark).initialConfig w₀))).toOuterMeasure
        {final | final.tapes.state = none ∧ final.tapes.output ∈ answer}ᶜ ≤
      ((8 * L + 17 : ℕ) : ℝ≥0∞) +
        (((t + 10 * L + 23 : ℕ) : ℝ≥0∞) + ((t + 10 * L + 23 : ℕ) : ℝ≥0∞) * (1 - q)⁻¹) := by
  classical
  set rnd := tm.iterateWhileRound mark
  set U := MultiTapePTM.repeatUntilBlank (nextTape k) rnd
  set R := t + 10 * L + 22 with hR
  let startU (vp v : List Bool) : Config (k + 1 + 2) Bool (RoundState State ⊕ Unit) Empty w₀ :=
    runConfig { tapes := wordsCfg w₀ (some rnd.initial) (words vp v) [], channels := Empty.elim }
  let goodU : Set (Config (k + 1 + 2) Bool (RoundState State ⊕ Unit) Empty w₀) :=
    {c | c.tapes.state = none ∧ ∃ v ∈ answer, c.tapes = wordsCfg w₀ none (words v []) []}
  have hgoodU : ∀ c ∈ goodU, c.tapes.state = none := fun c hc => hc.1
  -- a round from the words `vp`, `v` takes at most `R` steps
  have hround (vp v : List Bool) (hvp : vp.length ≤ L) (hv : v ∈ retry ∨ v ∈ answer)
      {p : ProbComp (List Bool)} (hp : tm.ComputesTidily v t (ProbOracleComp.sample p))
      (hpl : ∀ w' ∈ (ProbComp.eval p).support, w'.length ≤ L) :
      rnd.RunsWords w₀ (words vp v) [] R (ProbOracleComp.sample p) (fun v' => words v v')
        (fun _ => []) := by
    refine (RunsWords.iterateWhileRound (x := w₀) mark hp (l := L) (fun _ _ s w' s' hw' => ?_)
      []).mono ?_
    · rw [ProbOracleComp.runWith_sample, PMF.mem_support_map_iff] at hw'
      exact hw'.elim fun _ ⟨hw'', h⟩ => (Prod.mk.inj h).1 ▸ hpl _ hw''
    · have := (hlength v hv).2; omega
  -- a round from an answer word ends the loop
  have hstop (vp v : List Bool) (hvp : vp.length ≤ L) (hv : v ∈ answer) (m : ℕ) :
      (ProbComp.eval (U.runClosedConfigFrom (R + (1 + m)) (startU vp v))).toOuterMeasure
        goodUᶜ = 0 := by
    refine le_antisymm (((hround vp v hvp (Or.inr hv) (p := pure []) (hanswer v hv)
      (by simp)).toOuterMeasure_compl_repeatUntilBlank_le (nextTape k) hgoodU m).trans_eq ?_)
      zero_le
    rw [ProbComp.eval_pure, PMF.pure_bind, List.nil_append,
      eval_runClosedConfigFrom_check_nil _ _ (words_next v []) m, PMF.toOuterMeasure_pure_apply,
      ite_eq_right]
    exact fun h => h ⟨rfl, v, hv, rfl⟩
  -- after `n` further rounds from a retry word, the loop is still going with probability `q ^ n`
  have hgeom (n : ℕ) : ∀ vp v, vp.length ≤ L → v ∈ retry → ∀ j,
      (ProbComp.eval (U.runClosedConfigFrom (R + 1 + (n * (R + 1) + j))
        (startU vp v))).toOuterMeasure
        goodUᶜ ≤ q ^ n := by
    induction n with
    | zero => exact fun _ _ _ _ _ => (PMF.toOuterMeasure_le_one _ _).trans_eq (pow_zero q).symm
    | succ n ih =>
      intro vp v hvp hv j
      have hvL := (hlength v (Or.inl hv)).2
      rw [show R + 1 + ((n + 1) * (R + 1) + j) = R + (1 + (R + 1 + (n * (R + 1) + j))) by ring]
      refine ((hround vp v hvp (Or.inl hv) (hretry v hv) fun w' hw' =>
        (hlength w' (hsupport v hv w' hw')).2).toOuterMeasure_compl_repeatUntilBlank_le
          (nextTape k) hgoodU _).trans ?_
      rw [PMF.toOuterMeasure_bind_apply]
      calc _ ≤ ∑' v', retry.indicator (ProbComp.eval (step v)) v' * q ^ n := by
            refine tsum_le_tsum fun v' => ?_
            by_cases hv' : v' ∈ (ProbComp.eval (step v)).support
            · have hne := (hlength v' (hsupport v hv v' hv')).1
              rw [List.nil_append, eval_runClosedConfigFrom_check_ne_nil _ _ (by rwa [words_next])]
              by_cases ha : v' ∈ answer
              · simp [add_assoc R 1, hstop v v' hvL ha, U, startU]
              · have hr : v' ∈ retry := (hsupport v hv v' hv').resolve_right ha
                rw [Set.indicator_of_mem hr]
                exact mul_le_mul_of_nonneg_left (ih v v' hvL hr j) zero_le
            · simp [(PMF.apply_eq_zero_iff _ _).mpr hv']
        _ = (ProbComp.eval (step v)).toOuterMeasure retry * q ^ n := by
            rw [PMF.toOuterMeasure_apply, ENNReal.tsum_mul_right]
        _ ≤ q * q ^ n := by gcongr; exact hq v hv
        _ = q ^ (n + 1) := (pow_succ' q n).symm
  have hU := tsum_le_of_geometric (D := R + 1) (q := q)
    (f := fun s => (ProbComp.eval (U.runClosedConfigFrom s (startU [] w₀))).toOuterMeasure goodUᶜ)
    (by omega) (fun _ => PMF.toOuterMeasure_le_one _ _) fun n j => hgeom n [] w₀ (by simp) hw₀ j
  -- the load phase writes the start word to the next tape
  set load : MultiTapePTM (k + 1 + 2) Bool _ := ofDeterministic (loadWord Bool (nextTape k))
  set fin : MultiTapePTM (k + 1 + 2) Bool FinishState := ofDeterministic (finish k mark)
  have hw₀L := (hlength w₀ (Or.inl hw₀)).2
  have hload : ProbComp.eval (load.runClosedConfigFrom (3 * L + 6) (load.initialConfig w₀)) =
      PMF.pure { tapes := wordsCfg w₀ none (words [] w₀) [], channels := Empty.elim } := by
    have hrw := (RunsWords.of_transformsTapes (Operation := Empty) (x := w₀) (out₀ := [])
      (transformsTapes_loadWord (nextTape k) w₀) ⟨rfl, rfl⟩ (ws' := words (k := k) [] w₀)
      (emitted := []) (fun _ _ h => ⟨h.1.trans (words_nil_cur w₀).symm, h.2⟩)).mono
        (time' := 3 * L + 6) (by omega)
    exact (RunsWords.eval_runClosedConfigFrom (p := pure ()) hrw _
      (Cfg.init_eq_wordsCfg _ _)).trans (by simp [ProbComp.eval_pure])
  -- the finish phase outputs an answer word left by the loop
  let good : Set (Config (k + 1 + 2) Bool (MachineState State) Empty w₀) :=
    {final | final.tapes.state = none ∧ final.tapes.output ∈ answer}
  have hfin (r : Config (k + 1 + 2) Bool (RoundState State ⊕ Unit) Empty w₀) (hr : r ∈ goodU) :
      (ProbComp.eval (fin.runClosedConfigFrom (5 * L + 11) (Sequential.start fin r))).toOuterMeasure
        (Sequential.right ⁻¹' (Sequential.right ⁻¹' good)ᶜ) = 0 := by
    obtain ⟨-, v, hv, hrt⟩ := hr
    have hrw := (RunsWords.of_transformsTapes (Operation := Empty) (x := w₀) (out₀ := [])
      (transformsTapes_finish (k := k) mark v) rfl (ws' := fun _ => []) (emitted := v)
      (fun _ _ h => h)).mono (time' := 5 * L + 11) (by have := (hlength v (Or.inr hv)).2; omega)
    rw [RunsWords.eval_runClosedConfigFrom (p := pure ()) hrw _
      (by rw [Sequential.start, hrt, withState_wordsCfg]), ProbComp.eval_pure, PMF.pure_map,
      PMF.toOuterMeasure_pure_apply, ite_eq_right]
    simpa [good, Sequential.right, Cfg.mapState, wordsCfg] using hv
  -- each clock of the whole machine, shifted by the two phases, against the loop
  have hshift (s : ℕ) :
      (ProbComp.eval ((tm.iterateWhile mark).runClosedConfigFrom ((3 * L + 6) + (5 * L + 11) + s)
        ((tm.iterateWhile mark).initialConfig w₀))).toOuterMeasure goodᶜ ≤
        (ProbComp.eval (U.runClosedConfigFrom s (startU [] w₀))).toOuterMeasure goodUᶜ := by
    rw [show 3 * L + 6 + (5 * L + 11) + s = (3 * L + 6) + (s + (5 * L + 11)) by omega]
    change (ProbComp.eval ((load.seq (U.seq fin)).runClosedConfigFrom _
      (Sequential.left (U.seq fin) (load.initialConfig w₀)))).toOuterMeasure goodᶜ ≤ _
    refine (toOuterMeasure_compl_seq_le load (U.seq fin) (good := good) (fun c hc => hc.1)
      _ _ _).trans ?_
    set r₀ : Config (k + 1 + 2) Bool ((Unit ⊕ RewindState) ⊕ RewindWorkState) Empty w₀ :=
      { tapes := wordsCfg w₀ none (words [] w₀) [], channels := Empty.elim }
    have hr₀ : r₀.tapes.state = none := rfl
    rw [hload, tsum_eq_single r₀ fun r hr => by rw [PMF.pure_apply, ite_eq_right hr, zero_mul],
      PMF.pure_apply, ite_eq_left rfl, one_mul, ite_eq_left hr₀]
    have hstart : Sequential.start (U.seq fin) r₀ = Sequential.left fin (startU [] w₀) :=
      Config.ext (by simp [r₀, Sequential.start, Sequential.left, startU, runConfig, U,
        MultiTapePTM.repeatUntilBlank, withState_wordsCfg, mapState_wordsCfg, handOver])
        (Subsingleton.elim _ _)
    rw [hstart, Set.preimage_compl]
    refine (toOuterMeasure_compl_seq_le U fin (good := Sequential.right ⁻¹' good)
      (fun c hc => by simpa [Sequential.right, Cfg.mapState] using hc.1) s (5 * L + 11) _).trans ?_
    rw [PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun r => ?_
    by_cases hr : r ∈ goodU
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hr), ite_eq_left hr.1, hfin r hr,
        mul_zero]
    · rw [Set.indicator_of_mem (Set.mem_compl hr)]
      split_ifs
      · exact mul_le_of_le_one_right' (PMF.toOuterMeasure_le_one _ _)
      · rw [mul_one]
  refine (tsum_le_add_of_shift _ (fun _ => PMF.toOuterMeasure_le_one _ _) hshift).trans ?_
  have h8 : 3 * L + 6 + (5 * L + 11) = 8 * L + 17 := by omega
  exact h8 ▸ add_le_add le_rfl hU

end Turing.MultiTapePTM
