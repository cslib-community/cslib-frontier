/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Memory.Basic
public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.EpsilonNA.ToNA
public import Cslib.Computability.Automata.NA.ToDA

/-!
# Finite automata as memory machines

A deterministic automaton on finite words (`Cslib.Automata.DA.FinAcc`) is a memory machine on a
register holding its state beside a `MemoryModule.stream` holding the unread input. While input
remains, the controller writes the successor state and consumes one symbol; on exhausted input
it halts. As a `MemoryComputer`, it loads a word with the start state and outputs whether the
halting state is accepting. From state `q` on word `w`, the run takes `w.length` steps and halts
with state `mtr q w` (`relatesInSteps_toMemoryComputer`), so the computer decides acceptance in
`w.length` steps (`eval_toMemoryComputer`, `outputsWithinTime_toMemoryComputer`).

A nondeterministic automaton becomes a memory machine through the subset construction
(`NA.FinAcc.toDAFinAcc`), whose register holds the set of reachable states, and an automaton with
`ε`-transitions through its `ε`-closure (`εNA.FinAcc.toNAFinAcc`) first. Both decide acceptance
(`NA.FinAcc.eval_toMemoryComputer`, `εNA.FinAcc.eval_toMemoryComputer`).

## Main definitions

* `Cslib.Automata.DA.FinAcc.toMemoryComputer`.

## Main results

* `Cslib.Automata.DA.FinAcc.relatesInSteps_toMemoryComputer`: the run on `w` reaches the state
  `mtr q w` with the input consumed, in `w.length` steps.
* `Cslib.Automata.DA.FinAcc.eval_toMemoryComputer`,
  `Cslib.Automata.DA.FinAcc.outputsWithinTime_toMemoryComputer`: the computer decides acceptance,
  in `w.length` steps.
* `Cslib.Automata.NA.FinAcc.eval_toMemoryComputer`,
  `Cslib.Automata.εNA.FinAcc.eval_toMemoryComputer`: so do the subset constructions.
-/

public section

namespace Cslib.Automata

open Cslib.Machines Relation

namespace DA.FinAcc

variable {State Symbol : Type*} (da : FinAcc State Symbol)

/-- A deterministic automaton as a memory computer on its state register and its input: it
starts in the start state on the given word, and outputs whether its halting state is
accepting. -/
@[expose] def toMemoryComputer :
    MemoryComputer (List Symbol) Prop (State × List Symbol) (State × Option Symbol)
      (State × Bool) where
  memory := (MemoryModule.register State).prod (MemoryModule.stream Symbol)
  control
    | (q, a) => a.map fun a => (da.tr q a, true)
  init w := (da.start, w)
  output
    | (q, _) => q ∈ da.accept

/-- With the input exhausted, the memory machine halts. -/
@[simp] theorem step_toMemoryComputer_nil (q : State) :
    da.toMemoryComputer.step (q, []) = none := rfl

/-- On a nonempty input, the memory machine makes one transition and consumes one symbol. -/
@[simp] theorem step_toMemoryComputer_cons (q : State) (a : Symbol) (w : List Symbol) :
    da.toMemoryComputer.step (q, a :: w) = some (da.tr q a, w) := rfl

/-- From state `q` on input `w`, the memory machine reaches state `mtr q w` with no input left,
in `w.length` steps. -/
theorem relatesInSteps_toMemoryComputer (q : State) (w : List Symbol) :
    RelatesInSteps da.toMemoryComputer.Step (q, w) (da.mtr q w, []) w.length := by
  induction w generalizing q with
  | nil => exact .refl _
  | cons a w ih => exact .head _ (da.tr q a, w) _ _ (step_toMemoryComputer_cons da q a w) (ih _)

/-- The memory computer of `da` decides, within `w.length` steps, whether `da` accepts `w`. -/
theorem outputsWithinTime_toMemoryComputer (w : List Symbol) :
    da.toMemoryComputer.OutputsWithinTime w (Acceptor.Accepts da w) w.length :=
  ⟨_, _, le_rfl, ⟨da.relatesInSteps_toMemoryComputer _ w, rfl⟩, rfl⟩

/-- The memory computer of `da` computes whether `da` accepts a word. -/
theorem eval_toMemoryComputer (w : List Symbol) :
    da.toMemoryComputer.eval w = Part.some (Acceptor.Accepts da w) :=
  Part.eq_some_iff.2 (da.toMemoryComputer.mem_eval_iff.2
    ⟨_, da.outputsWithinTime_toMemoryComputer w⟩)

end DA.FinAcc

/-- Through the subset construction, a nondeterministic automaton is a memory computer that
decides whether it accepts a word. -/
theorem NA.FinAcc.eval_toMemoryComputer {State Symbol : Type*} (na : NA.FinAcc State Symbol)
    (w : List Symbol) :
    na.toDAFinAcc.toMemoryComputer.eval w = Part.some (Acceptor.Accepts na w) := by
  rw [DA.FinAcc.eval_toMemoryComputer]
  congr 1
  exact propext (Set.ext_iff.1 NA.FinAcc.toDAFinAcc_language_eq w)

/-- Through its `ε`-closure and the subset construction, an automaton with `ε`-transitions is a
memory computer that decides whether it accepts a word. -/
theorem εNA.FinAcc.eval_toMemoryComputer {State Symbol : Type*} (a : εNA.FinAcc State Symbol)
    (w : List Symbol) :
    a.toNAFinAcc.toDAFinAcc.toMemoryComputer.eval w = Part.some (Acceptor.Accepts a w) := by
  rw [NA.FinAcc.eval_toMemoryComputer]
  congr 1
  exact propext (Set.ext_iff.1 εNA.FinAcc.toNAFinAcc_language_eq w)

end Cslib.Automata
