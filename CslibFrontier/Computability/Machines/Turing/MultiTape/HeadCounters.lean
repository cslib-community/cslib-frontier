/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic

import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Counters stored in work-head positions

This is an obstruction step, not an equivalence between visited-cell and ever-nonblank space.
A permanent marker at position zero makes a work head into a natural-number counter: moving right
increments, moving left decrements, and reading the marker tests for zero. Decrement at zero is
saturated. `HeadCounter.machine` initializes one marker per tape and then never writes again.
`HeadCounter.step_cfg` proves the counter simulation, including input movement, output and halting.

The literal ever-nonblank convention in the 2007-01-08 draft of [AroraBarak09], Definition 4.1
(printed p. 76 / PDF p. 92), does not charge these counters. Its machine rules (printed pp. 16–17 /
PDF pp. 32–33) allow rewriting a blank as blank and supply permanent origin markers initially.
Here the native blank-initialized machine writes the markers in one extra step. All subsequent
head positions are nonnegative, so the construction does not rely on bidirectional tapes.

`HeadCounter.exists_unbounded_visited_fixed_support` exhibits a finite-state binary machine with
only one ever-nonblank work cell, injectively many reachable configurations, and no visited-space
bound, even on the empty input. This witness does not halt: it refutes unrestricted configuration
counting from nonblank support alone, not a class equivalence restricted to halting deciders.
The counter simulation also explains why storing a blank-excursion offset in a binary counter
requires a separate bound on that offset; a bound on nonblank support supplies none. A formal
universality or language-class separation theorem is not proved here.

## Main results

* `HeadCounter.step_cfg`: one-step simulation of zero-tested counter instructions.
* `HeadCounter.run_support`: all nonblank work cells, over all times, are fixed origins.
* `HeadCounter.exists_unbounded_visited_fixed_support`: nonblank support alone does not bound
  visited space or the number of reachable configurations.
-/

public section

namespace Turing.MultiTapeTM.HeadCounter

/-- An instruction for zero-tested head counters, with read-only input and append-only output. -/
structure Instruction (k : ℕ) (State : Type*) where
  /-- Attempted input-head movement. -/
  inputTape : SignType
  /-- Counter increments, no-ops or saturated decrements. -/
  counters : Fin k → SignType
  /-- Optional output bit. -/
  output : Option Bool
  /-- Next control state, or halt. -/
  state : Option State

variable {k : ℕ} {State : Type*}

private def movement (zero : Bool) (direction : SignType) : SignType :=
  match zero, direction with
  | true, .neg => .zero
  | _, d => d

private theorem movement_cast (n : ℕ) (d : SignType) :
    (n : ℤ) + (movement (decide (n = 0)) d).cast =
      (((n : ℤ) + d.cast).toNat : ℤ) := by
  cases n <;> cases d <;> simp [movement, SignType.cast]
  omega

/-- Compile a zero-test counter controller into a native machine. Control `none` initializes the
markers; `some q` runs the controller. The controller sees `true` exactly at a zero counter.
Only initialization writes; a decrement of a zero counter is suppressed. Finite control remains
finite, and each controller step takes one native step after initialization. -/
def machine (q₀ : State)
    (tr : State → Option Bool → (Fin k → Bool) → Instruction k State) :
    MultiTapeTM k Bool (Option State) :=
  .ofTr none fun q inp work => match q with
    | none => ⟨0, fun _ => (some (some true), 0), none, some (some q₀)⟩
    | some q =>
      let zero := fun i => (work i).isSome
      let a := tr q inp zero
      ⟨a.inputTape, fun i => (none, movement (zero i) (a.counters i)),
        a.output, a.state.map some⟩

/-- Represent counters by nonnegative head positions over tapes with one fixed marker each.
`q = none` represents a halted controller, distinct from the machine's initialization control. -/
@[expose] def cfg {input : List Bool} (q : Option State) (pos : Fin (input.length + 2))
    (counters : Fin k → ℕ) (output : List Bool) : Cfg k Bool (Option State) input :=
  ⟨q.map some, pos, fun _ => Function.update (fun _ => none) 0 (some true),
    fun i => counters i, output⟩

/-- A step of the compiled machine is precisely the zero-tested counter instruction. In particular,
its only work-tape contents are the fixed markers, even when counters grow without bound. -/
theorem step_cfg (q₀ : State)
    (tr : State → Option Bool → (Fin k → Bool) → Instruction k State)
    {input : List Bool} (q : State) (pos : Fin (input.length + 2))
    (counters : Fin k → ℕ) (output : List Bool) :
    let c := cfg (some q) pos counters output
    let a := tr q c.inputSymbol (fun i => decide (counters i = 0))
    (machine q₀ tr).step c =
      cfg a.state (moveInputPos pos a.inputTape)
        (fun i => ((counters i : ℤ) + (a.counters i).cast).toNat)
        (output ++ a.output.toList) := by
  dsimp only
  rw [step_of_state (q := some q) rfl]
  have hz : (cfg (some q) pos counters output).workTapeSymbols =
      fun i => if counters i = 0 then some true else none := by
    funext i
    simp [cfg, Cfg.workTapeSymbols, Function.update_apply]
  simp only [machine, tr_ofTr, hz]
  have hi (i : Fin k) : (if counters i = 0 then some true else none).isSome =
      decide (counters i = 0) := by
    split_ifs <;> simp_all
  simp only [hi]
  apply Cfg.ext
  · rfl
  · rfl
  · rfl
  · funext i
    exact movement_cast (counters i) _
  · rfl

/-- Initialization writes exactly the origin markers and starts every counter at zero. -/
theorem step_init (q₀ : State)
    (tr : State → Option Bool → (Fin k → Bool) → Instruction k State) (input : List Bool) :
    (machine q₀ tr).step ((machine q₀ tr).initCfg input) =
      cfg (some q₀) 1 (fun _ => 0) [] := by
  rw [step_of_state (q := none) rfl]
  simp [machine, Action.apply, MultiTapeNTM.initCfg, Cfg.init, cfg]

/-- At every time, every nonblank work cell is an origin marker. This quantifies over all times,
so bounds ever-nonblank support, rather than just the support of the final configuration. -/
theorem run_support (q₀ : State)
    (tr : State → Option Bool → (Fin k → Bool) → Instruction k State)
    (input : List Bool) (t : ℕ) (i : Fin k) (z : ℤ) :
    ((machine q₀ tr).runFrom ((machine q₀ tr).initCfg input) t).workTapes i z ≠ none → z = 0 := by
  induction t with
  | zero => simp [runFrom, MultiTapeNTM.initCfg, Cfg.init]
  | succ t ih =>
    rw [runFrom_succ]
    generalize hc : (machine q₀ tr).runFrom ((machine q₀ tr).initCfg input) t = c at *
    cases hs : c.state with
    | none => simpa [step_of_halt hs] using ih
    | some q =>
      rw [step_workTapes_of_state hs]
      cases q with
      | none =>
        simp only [machine, tr_ofTr]
        intro h
        by_cases hz : z = c.workTapePos i
        · have hpos : c.workTapePos i = 0 := by
            -- Initialization control is present only at time zero.
            have hstate : t = 0 := by
              cases t with
              | zero => rfl
              | succ t =>
                rw [runFrom_succ] at hc
                have hnever : ∀ c : Cfg k Bool (Option State) input,
                    ((machine q₀ tr).step c).state ≠ some none := by
                  intro c
                  cases hq : c.state with
                  | none => simp [hq]
                  | some q =>
                    rw [step_of_state hq]
                    cases q <;> simp [machine, Action.apply]
                exact False.elim (hnever _ (hc ▸ hs))
            subst t
            simpa [runFrom, MultiTapeNTM.initCfg, Cfg.init] using
              congrArg (fun c => c.workTapePos i) hc.symm
          exact hz.trans hpos
        · apply ih
          simpa [Function.update_of_ne hz] using h
      | some q => simpa [machine, tr_ofTr] using ih

private def increment : MultiTapeTM 1 Bool (Option Unit) :=
  machine () fun _ _ _ => ⟨0, fun _ => 1, none, some ()⟩

private theorem increment_run (input : List Bool) (t : ℕ) :
    increment.runFrom (increment.initCfg input) (t + 1) =
      cfg (some ()) 1 (fun _ => t) [] := by
  induction t with
  | zero => exact step_init _ _ input
  | succ t ih =>
    rw [runFrom_succ, ih]
    simpa [increment] using
      step_cfg () (fun _ _ _ => ⟨0, fun _ => 1, none, some ()⟩) ()
        (1 : Fin (input.length + 2)) (fun _ => t) []

/-- Obstruction step: a finite-state binary machine has one ever-nonblank cell but infinitely many
reachable configurations and no bound on visited space. The witness runs forever; this is not a
separation theorem for halting language deciders. -/
theorem exists_unbounded_visited_fixed_support :
    ∃ tm : MultiTapeTM 1 Bool (Option Unit),
      (∀ (input : List Bool) t i z,
        (tm.runFrom (tm.initCfg input) t).workTapes i z ≠ none → z = 0) ∧
      (∀ input, Function.Injective (fun t => tm.runFrom (tm.initCfg input) (t + 1))) ∧
      ∀ input s, ¬tm.RunsInSpace input s := by
  refine ⟨increment, run_support _ _, ?_, ?_⟩
  · intro input a b h
    have := congrArg (fun c => c.workTapePos 0) h
    simpa only [increment_run, cfg, Nat.cast_inj] using this
  · intro input s h
    let p := MultiTapeNTM.ComputationPath.ofDeterministic increment input (s + 2)
    have hw := MultiTapeNTM.RunPath.inWindow_of_space_le
      (p := p.toRunPath) (fun _ => rfl) (h p)
    have hz := mem_window.mp (hw p.last ⟨Fin.last _, rfl⟩ 0)
    rw [computationPath_last_eq_runFrom] at hz
    change ((increment.runFrom (increment.initCfg input) ((s + 1) + 1)).workTapePos 0).natAbs ≤ s
      at hz
    simp only [increment_run, cfg, Int.natAbs_natCast] at hz
    omega

end Turing.MultiTapeTM.HeadCounter
