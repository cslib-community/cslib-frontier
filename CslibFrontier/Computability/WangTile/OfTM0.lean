/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
public import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# Finite TM0 computations as seeded quadrant tilings

A finite Post–Turing machine is folded onto a one-sided tape, pairing source positions
`-(i + 1)` and `i` at position `i`. A tile records a two-row, three-cell window of its
computation. Position tags force the finite input along the bottom row; a constant tail
completes that row. A seeded quadrant tiling exists exactly when the machine does not halt.
This does not establish undecidability of the unseeded plane domino problem.

## Main definitions

* `Cslib.WangTile.OfTM0.seededInstance`: the finite seeded palette for a machine and input.

## Main results

* `Cslib.WangTile.OfTM0.tilesQuadrant_seededInstance_iff`: seeded quadrant tilings are equivalent
  to nontermination of the given `Turing.TM0` computation.
* `Cslib.WangTile.OfTM0.primrec_seededInstance`: the palette construction for a fixed finite
  machine is primitive recursive in its input.

## References

Adapted from
[lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3/LeanWang/Robinson/Machine),
revision `64268a3`, including its folded tape simulation.
The simulation here applies to arbitrary finite `TM0` machines.
The tableau method is after [Robinson1971, §4, pp. 190–192], which proves the plane variant
with a prescribed tile used at least once. The source states Wang's origin-constrained
first-quadrant problem in §1, p. 178, and remarks on p. 192 that a similar tableau argument
proves it, crediting Wang. Here tiles are two-row, three-cell windows rather than the source's
signal tiles; `TM0` separates writes and moves, and folding preserves its two-sided tape
semantics on the one-sided simulation tape. For the undecidability reduction, the universal
machine is fixed and the bottom-row input varies, instead of varying the machine on a blank
tape as in the source's origin-constrained proof.
-/

noncomputable section

namespace Cslib.WangTile.OfTM0

private inductive Move where
  | left | right | stay
  deriving DecidableEq

private instance : Fintype Move :=
  ⟨{.left, .right, .stay}, by rintro (_ | _ | _) <;> simp⟩

private def Move.apply : Move → ℕ → ℕ
  | .left, i => i.pred
  | .right, i => i + 1
  | .stay, i => i

/-- A single update of the private one-sided simulation. -/
private structure Action (S Q : Type) where
  /-- The symbol written under the old head. -/
  write : S
  /-- The next control state. -/
  state : Q
  /-- The movement after writing. -/
  move : Move
  deriving DecidableEq, Fintype

/-- The private typed target of tape folding. -/
private structure OneMachine (S Q : Type) where
  /-- The symbol outside the finite input. -/
  blank : S
  /-- The initial control state. -/
  start : Q
  /-- The absorbing halting state. -/
  halt : Q
  /-- The finite transition table. -/
  step : Q → S → Action S Q

/-- A one-sided simulation configuration. -/
@[ext] private structure Config (S Q : Type) where
  /-- The one-sided tape indexed by distance from the fold. -/
  tape : ℕ → S
  /-- The current one-sided head position. -/
  head : ℕ
  /-- The current finite control. -/
  state : Q

section Kernel

variable {S Q : Type}

namespace OneMachine

variable [DecidableEq Q]

/-- One machine step. Halting configurations are fixed points. -/
private def nextID (M : OneMachine S Q) (c : Config S Q) : Config S Q :=
  if c.state = M.halt then
    c
  else
    let read := c.tape c.head
    let ⟨write, state', move⟩ := M.step c.state read
    { tape := fun i => if i = c.head then write else c.tape i
      head := move.apply c.head
      state := state' }

@[simp]
private theorem nextID_of_halt (M : OneMachine S Q) (c : Config S Q) (h : c.state = M.halt) :
    M.nextID c = c := by
  simp [nextID, h]

private theorem nextID_of_ne_halt {M : OneMachine S Q} {c : Config S Q} (h : c.state ≠ M.halt) :
    M.nextID c =
      let read := c.tape c.head
      let ⟨write, state', move⟩ := M.step c.state read
      { tape := fun i => if i = c.head then write else c.tape i
        head := move.apply c.head
        state := state' } := by
  simp [nextID, h]

private theorem nextID_state_of_ne_halt {M : OneMachine S Q} {c : Config S Q}
    (h : c.state ≠ M.halt) :
    (M.nextID c).state = (M.step c.state (c.tape c.head)).state := by
  rw [nextID_of_ne_halt h]

private theorem nextID_head_of_ne_halt {M : OneMachine S Q} {c : Config S Q}
    (h : c.state ≠ M.halt) :
    (M.nextID c).head = (M.step c.state (c.tape c.head)).move.apply c.head := by
  rw [nextID_of_ne_halt h]

private theorem nextID_tape_of_ne_head {M : OneMachine S Q} {c : Config S Q} {i : ℕ}
    (hi : i ≠ c.head) :
    (M.nextID c).tape i = c.tape i := by
  by_cases h : c.state = M.halt
  · simp [nextID, h]
  · rw [nextID_of_ne_halt h]
    rcases M.step c.state (c.tape c.head) with ⟨write, state', move⟩
    simp [hi]

end OneMachine

/-- A cell in a local space-time window, including the left boundary marker. -/
private inductive Cell (S Q : Type) where
  | boundary
  | plain (symbol : S)
  | head (state : Q) (symbol : S)
  deriving DecidableEq, Fintype

private instance [Fintype S] [Fintype Q] : Primcodable (Cell S Q) :=
  Primcodable.ofEquiv _ (Fintype.equivFin _)

private def Cell.Mem (M : OneMachine S Q) : Cell S Q → Prop
  | .head q _ => q ≠ M.halt
  | _ => True

private instance [DecidableEq Q] (M : OneMachine S Q) (c : Cell S Q) : Decidable (c.Mem M) :=
  match c with
  | .head q _ => inferInstanceAs (Decidable (q ≠ M.halt))
  | .boundary | .plain _ => isTrue trivial

namespace Config

/-- Read one configuration position as a row cell for the space-time diagram. -/
private def cellAt (c : Config S Q) (i : ℕ) : Cell S Q :=
  if i = c.head then
    Cell.head c.state (c.tape i)
  else
    Cell.plain (c.tape i)

@[simp]
private theorem cellAt_head (c : Config S Q) :
    c.cellAt c.head = Cell.head c.state (c.tape c.head) := by
  simp [cellAt]

private theorem cellAt_of_ne {c : Config S Q} {i : ℕ} (hi : i ≠ c.head) :
    c.cellAt i = Cell.plain (c.tape i) := by
  simp [cellAt, hi]

private theorem cellAt_ne_boundary (c : Config S Q) (i : ℕ) :
    c.cellAt i ≠ Cell.boundary := by
  by_cases hi : i = c.head
  · simp [cellAt, hi]
  · simp [cellAt, hi]

/-- The cell immediately left of a position, using a boundary marker at `0`. -/
private def cellAtLeft (c : Config S Q) : ℕ → Cell S Q
  | 0 => Cell.boundary
  | i + 1 => c.cellAt i

@[simp] private theorem cellAtLeft_zero (c : Config S Q) :
    c.cellAtLeft 0 = Cell.boundary := rfl

@[simp]
private theorem cellAtLeft_succ (c : Config S Q) (i : ℕ) :
    c.cellAtLeft (i + 1) = c.cellAt i :=
  rfl

private theorem cellAt_mem {M : OneMachine S Q} {c : Config S Q}
    (hstate : c.state ≠ M.halt) (i : ℕ) : (c.cellAt i).Mem M := by
  by_cases hi : i = c.head <;> simp [cellAt, Cell.Mem, hi, hstate]

private theorem cellAtLeft_mem {M : OneMachine S Q} {c : Config S Q}
    (hstate : c.state ≠ M.halt) (i : ℕ) : (c.cellAtLeft i).Mem M := by
  cases i with
  | zero => trivial
  | succ i => exact cellAt_mem hstate i

end Config

variable [DecidableEq Q]

private def localNextCell? (M : OneMachine S Q) (left center right : Cell S Q) :
    Option (Cell S Q) :=
  match left, center, right with
  | _, Cell.boundary, _ => none
  | _, Cell.head q a, _ =>
      if _h : q = M.halt then
        none
      else
        let ⟨write, q', move⟩ := M.step q a
        match left, move with
        | Cell.boundary, Move.left =>
            if q' = M.halt then none else some (Cell.head q' write)
        | _, Move.stay =>
            if q' = M.halt then none else some (Cell.head q' write)
        | _, _ => some (Cell.plain write)
  | Cell.head q a, Cell.plain b, _ =>
      if _h : q = M.halt then
        none
      else
        let ⟨_write, q', move⟩ := M.step q a
        match move with
        | Move.right => if q' = M.halt then none else some (Cell.head q' b)
        | Move.left | Move.stay => some (Cell.plain b)
  | _, Cell.plain b, Cell.head q a =>
      if _h : q = M.halt then
        none
      else
        let ⟨_write, q', move⟩ := M.step q a
        match move with
        | Move.left => if q' = M.halt then none else some (Cell.head q' b)
        | Move.right | Move.stay => some (Cell.plain b)
  | Cell.boundary, Cell.plain b, _ =>
      some (Cell.plain b)
  | _, Cell.plain b, _ =>
      some (Cell.plain b)

namespace OneMachine

private theorem localNextCell?_cellAt_or_halt {M : OneMachine S Q} {c : Config S Q} {pos : ℕ}
    (hstate : c.state ≠ M.halt) :
    localNextCell? M (c.cellAtLeft pos) (c.cellAt pos) (c.cellAt (pos + 1)) =
      if (M.nextID c).state = M.halt ∧ pos = (M.nextID c).head then
        none
      else
        some ((M.nextID c).cellAt pos) := by
  rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
  by_cases hcenter : pos = c.head
  · subst pos
    cases hhead : c.head with
    | zero =>
        cases move <;>
          simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
            Move.apply]
    | succ pred =>
        cases move <;>
          simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
            Move.apply]
  · by_cases hleft : c.head = pos + 1
    · cases hpos : pos with
      | zero =>
          cases move <;>
            simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
              Move.apply]
      | succ pred =>
          have hpred : pred ≠ pred + 1 + 1 := by omega
          cases move <;>
            simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
              Move.apply]
    · by_cases hright : pos = c.head + 1
      · subst pos
        cases hhead : c.head with
        | zero =>
            cases move <;>
              simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
                Move.apply]
        | succ pred =>
            have hpred : pred + 1 + 1 ≠ pred := by omega
            cases move <;>
              simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
                Move.apply]
      · cases hpos : pos with
        | zero =>
            cases hhead : c.head with
            | zero => omega
            | succ pred =>
                cases move <;>
                  (simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID,
                    localNextCell?, Move.apply]
                   try omega)
        | succ posPred =>
            cases hhead : c.head with
            | zero =>
                cases move <;>
                  simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID,
                    localNextCell?, Move.apply]
            | succ headPred =>
                have hleftCell : posPred ≠ headPred + 1 := by omega
                have hcenterCell : posPred ≠ headPred := by omega
                have hrightCell : posPred + 1 + 1 ≠ headPred + 1 := by omega
                have hnewLeft : posPred + 1 ≠ headPred := by omega
                have hnewRight : posPred + 1 ≠ headPred + 1 + 1 := by omega
                cases move <;>
                  simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID,
                    localNextCell?, Move.apply]

private theorem localNextCell?_cellAt {M : OneMachine S Q} {c : Config S Q} {pos : ℕ}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).state ≠ M.halt) :
    localNextCell? M (c.cellAtLeft pos) (c.cellAt pos) (c.cellAt (pos + 1)) =
      some ((M.nextID c).cellAt pos) := by
  rw [localNextCell?_cellAt_or_halt hstate]
  simp [OneMachine.nextID, hstate, hnextState]

private theorem localNextCell?_at_next_halt_head {M : OneMachine S Q} {c : Config S Q}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).state = M.halt) :
    localNextCell? M
        (c.cellAtLeft ((M.step c.state (c.tape c.head)).move.apply c.head))
        (c.cellAt ((M.step c.state (c.tape c.head)).move.apply c.head))
        (c.cellAt ((M.step c.state (c.tape c.head)).move.apply c.head + 1)) =
      none := by
  rw [localNextCell?_cellAt_or_halt hstate]
  simp [OneMachine.nextID, hstate, hnextState]

end OneMachine

/-- The two overlapping triples carried by a history tile. -/
private structure History (S Q : Type) where
  /-- The left cell before this transition. -/
  prevLeft : Cell S Q
  /-- The center cell before this transition. -/
  prevCenter : Cell S Q
  /-- The right cell before this transition. -/
  prevRight : Cell S Q
  /-- The left cell after this transition. -/
  nextLeft : Cell S Q
  /-- The center cell after this transition. -/
  nextCenter : Cell S Q
  /-- The right cell after this transition. -/
  nextRight : Cell S Q
  deriving DecidableEq

private def History.equivProd : History S Q ≃
    Cell S Q × Cell S Q × Cell S Q × Cell S Q × Cell S Q × Cell S Q where
  toFun t := (t.prevLeft, t.prevCenter, t.prevRight, t.nextLeft, t.nextCenter, t.nextRight)
  invFun := fun (a, b, c, d, e, f) => ⟨a, b, c, d, e, f⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance [Fintype S] [Fintype Q] : Fintype (History S Q) :=
  Fintype.ofEquiv _ History.equivProd.symm

private instance [Fintype S] [Fintype Q] : Primcodable (History S Q) :=
  Primcodable.ofEquiv _ (Fintype.equivFin _)

/-- A finite word followed by the machine's blank symbol. -/
private def tape (blank : S) (input : List S) (position : ℕ) : S :=
  input[position]?.getD blank

/-- The standard initial configuration carrying a finite input word. -/
private def initialID (M : OneMachine S Q) (input : List S) : Config S Q where
  tape := tape M.blank input
  head := 0
  state := M.start

/-- Run `M` from the finite input word rather than the empty tape. -/
private def run (M : OneMachine S Q) (input : List S) (steps : ℕ) : Config S Q :=
  Nat.iterate M.nextID steps (initialID M input)

/-- Halting of `M` on a finite input word. -/
private def Halts (M : OneMachine S Q) (input : List S) : Prop :=
  ∃ steps, (run M input steps).state = M.halt

/-- A halting computation has a first halting time and is nonhalting before
it. -/
private theorem exists_first_halting_time {M : OneMachine S Q} {input : List S}
    (halts : Halts M input) :
    ∃ steps, (run M input steps).state = M.halt ∧
      ∀ previous, previous < steps →
        (run M input previous).state ≠ M.halt := by
  let steps := Nat.find halts
  refine ⟨steps, Nat.find_spec halts, ?_⟩
  intro previous before hhalt
  exact (Nat.not_lt_of_ge (Nat.find_min' halts hhalt)) before

/-- Iterate a machine until its next step enters the absorbing halt state. -/
private def transition (M : OneMachine S Q) (config : Config S Q) : Option (Config S Q) :=
  let next := M.nextID config
  if next.state = M.halt then none else some next

private theorem transition_eq_none_iff (M : OneMachine S Q) (config : Config S Q) :
    transition M config = none ↔ (M.nextID config).state = M.halt := by
  simp [transition]

private theorem mem_transition_nextID {M : OneMachine S Q} {current next : Config S Q}
    (hnext : next ∈ transition M current) :
    next = M.nextID current := by
  by_cases hhalt : (M.nextID current).state = M.halt
  · simp [transition, hhalt] at hnext
  · have hnext' : M.nextID current = next := by
      simpa [transition, hhalt] using hnext
    exact hnext'.symm

@[simp] private theorem run_zero (M : OneMachine S Q) (input : List S) :
    run M input 0 = initialID M input :=
  rfl

@[simp] private theorem run_succ (M : OneMachine S Q) (input : List S) (steps : ℕ) :
    run M input (steps + 1) = M.nextID (run M input steps) := by
  unfold run
  rw [Function.iterate_succ_apply']

@[simp] private theorem tape_eq_blank_of_length_le
    {blank : S} {input : List S} {position : ℕ}
    (hposition : input.length ≤ position) :
    tape blank input position = blank := by
  simp [tape, List.getElem?_eq_none_iff.mpr hposition]

private theorem run_state_ne_halt_of_not_halts {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input) (steps : ℕ) :
    (run M input steps).state ≠ M.halt := by
  intro hhalt
  exact notHalts ⟨steps, hhalt⟩

private theorem run_state_eq_halt_of_le {M : OneMachine S Q} {input : List S}
    {first second : ℕ} (hle : first ≤ second)
    (hhalt : (run M input first).state = M.halt) :
    (run M input second).state = M.halt := by
  rcases Nat.exists_eq_add_of_le hle with ⟨extra, rfl⟩
  clear hle
  induction extra with
  | zero => simpa using hhalt
  | succ extra ih =>
      rw [show first + (extra + 1) = first + extra + 1 by omega, run_succ]
      rw [OneMachine.nextID_of_halt M _ ih]
      exact ih

private theorem transition_reaches_run_of_ne_halt {M : OneMachine S Q} {input : List S}
    {steps : ℕ} (hne : (run M input steps).state ≠ M.halt) :
    StateTransition.Reaches (transition M)
      (initialID M input) (run M input steps) := by
  induction steps with
  | zero => exact Relation.ReflTransGen.refl
  | succ steps ih =>
      have hprevious : (run M input steps).state ≠ M.halt := by
        intro hhalt
        exact hne (run_state_eq_halt_of_le (Nat.le_succ steps) hhalt)
      have hnextNe : (M.nextID (run M input steps)).state ≠ M.halt := by
        simpa [run_succ] using hne
      have hnext : transition M (run M input steps) =
          some (run M input (steps + 1)) := by
        rw [run_succ]
        simp [transition, hnextNe]
      exact Relation.ReflTransGen.tail (ih hprevious) hnext

private theorem reaches_transition_eq_run {M : OneMachine S Q} {input : List S}
    {config : Config S Q}
    (hreaches : StateTransition.Reaches (transition M)
      (initialID M input) config) :
    ∃ steps, config = run M input steps := by
  induction hreaches with
  | refl => exact ⟨0, rfl⟩
  | tail hreach hstep ih =>
      rcases ih with ⟨steps, rfl⟩
      have hid := mem_transition_nextID hstep
      refine ⟨steps + 1, ?_⟩
      rw [run_succ]
      exact hid

private theorem transition_eval_dom_iff_halts (M : OneMachine S Q) (input : List S) :
    (StateTransition.eval (transition M) (initialID M input)).Dom ↔
      Halts M input := by
  constructor
  · intro hdom
    rcases Part.dom_iff_mem.1 hdom with ⟨terminal, hterminal⟩
    rcases StateTransition.mem_eval.1 hterminal with ⟨hreaches, hnone⟩
    rcases reaches_transition_eq_run hreaches with ⟨steps, rfl⟩
    refine ⟨steps + 1, ?_⟩
    rw [run_succ]
    exact (transition_eq_none_iff M _).1 hnone
  · intro halts
    rcases exists_first_halting_time halts with
      ⟨steps, hhalt, before⟩
    cases steps with
    | zero =>
        have hinitial : (initialID M input).state = M.halt := by
          simpa using hhalt
        apply Part.dom_iff_mem.2
        refine ⟨initialID M input, StateTransition.mem_eval.2 ⟨?_, ?_⟩⟩
        · exact Relation.ReflTransGen.refl
        · apply (transition_eq_none_iff M _).2
          rw [OneMachine.nextID_of_halt M _ hinitial]
          exact hinitial
    | succ steps =>
        apply Part.dom_iff_mem.2
        refine ⟨run M input steps, StateTransition.mem_eval.2 ⟨?_, ?_⟩⟩
        · exact transition_reaches_run_of_ne_halt (before steps (by omega))
        · apply (transition_eq_none_iff M _).2
          simpa [run_succ] using hhalt

/-- A local history block cut from two rows of a finite-input run. -/
private def historyTile (M : OneMachine S Q) (input : List S) (time position : ℕ) :
    History S Q where
  prevLeft := (run M input time).cellAtLeft position
  prevCenter := (run M input time).cellAt position
  prevRight := (run M input time).cellAt (position + 1)
  nextLeft := (run M input (time + 1)).cellAtLeft position
  nextCenter := (run M input (time + 1)).cellAt position
  nextRight := (run M input (time + 1)).cellAt (position + 1)

private theorem historyTile_hMatches (M : OneMachine S Q) (input : List S)
    (time position : ℕ) :
    (historyTile M input time position).prevCenter =
        (historyTile M input time (position + 1)).prevLeft ∧
      (historyTile M input time position).prevRight =
        (historyTile M input time (position + 1)).prevCenter ∧
      (historyTile M input time position).nextCenter =
        (historyTile M input time (position + 1)).nextLeft ∧
      (historyTile M input time position).nextRight =
        (historyTile M input time (position + 1)).nextCenter := by
  simp [historyTile, run_succ]

private theorem historyTile_cells_mem {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input)
    (time position : ℕ) :
    (historyTile M input time position).prevLeft.Mem M ∧
      (historyTile M input time position).prevCenter.Mem M ∧
      (historyTile M input time position).prevRight.Mem M ∧
      (historyTile M input time position).nextLeft.Mem M ∧
      (historyTile M input time position).nextCenter.Mem M ∧
      (historyTile M input time position).nextRight.Mem M := by
  simp [historyTile, Config.cellAtLeft_mem, Config.cellAt_mem,
    run_state_ne_halt_of_not_halts notHalts, -run_succ]

private theorem historyTile_local_of_state_ne_halt {M : OneMachine S Q} {input : List S}
    {time : ℕ}
    (hstate : (run M input time).state ≠ M.halt)
    (hnext : (run M input (time + 1)).state ≠ M.halt)
    (position : ℕ) :
    localNextCell? M (historyTile M input time position).prevLeft
        (historyTile M input time position).prevCenter
        (historyTile M input time position).prevRight =
      some (historyTile M input time position).nextCenter := by
  let c := run M input time
  have hstate' : c.state ≠ M.halt := by simpa [c] using hstate
  have hnextState : (M.step c.state (c.tape c.head)).state ≠ M.halt := by
    rw [← OneMachine.nextID_state_of_ne_halt hstate']
    simpa [c, run_succ] using hnext
  simpa [historyTile, c, run_succ] using
    OneMachine.localNextCell?_cellAt
      (M := M) (c := c) (pos := position) hstate' hnextState

private theorem historyTile_local {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input) (time position : ℕ) :
    localNextCell? M (historyTile M input time position).prevLeft
        (historyTile M input time position).prevCenter
        (historyTile M input time position).prevRight =
      some (historyTile M input time position).nextCenter := by
  exact historyTile_local_of_state_ne_halt
    (run_state_ne_halt_of_not_halts notHalts time)
    (run_state_ne_halt_of_not_halts notHalts (time + 1)) position

private theorem historyTile_boundaryOK (M : OneMachine S Q) (input : List S)
    (time position : ℕ) :
    (historyTile M input time position).prevLeft = Cell.boundary →
      (historyTile M input time position).nextLeft = Cell.boundary := by
  cases position with
  | zero => simp [historyTile]
  | succ position =>
      intro hprev
      have hnot : (run M input time).cellAt position ≠ Cell.boundary :=
        Config.cellAt_ne_boundary (run M input time) position
      exact False.elim (hnot (by
        simpa [historyTile] using hprev))

/- The input-specific palette consists of a finite prefix followed by one
constant blank tile.  The `+ 3` margin covers both the width-three local window
and the possible one-cell head move in the first transition. -/

/-- Past this position, the time-zero local history is a constant blank tail. -/
private def tailPosition (input : List S) : ℕ :=
  input.length + 3

private theorem run_zero_cell_eq_plain_blank
    (M : OneMachine S Q) (input : List S) {position : ℕ}
    (hlength : input.length ≤ position) (hpositive : 0 < position) :
    (run M input 0).cellAt position = Cell.plain M.blank := by
  simp [run_zero, initialID, Config.cellAt, tape,
    List.getElem?_eq_none_iff.mpr hlength, Nat.ne_of_gt hpositive]

private theorem run_zero_cellLeft_eq_plain_blank
    (M : OneMachine S Q) (input : List S) {position : ℕ}
    (hlength : input.length < position) (htwo : 2 ≤ position) :
    (run M input 0).cellAtLeft position = Cell.plain M.blank := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position ≠ 0)
  simp only [Config.cellAtLeft_succ]
  exact run_zero_cell_eq_plain_blank M input (by omega) (by omega)

private theorem run_one_cell_eq_plain_blank
    (M : OneMachine S Q) (input : List S) {position : ℕ}
    (hlength : input.length ≤ position) (htwo : 2 ≤ position) :
    (run M input 1).cellAt position = Cell.plain M.blank := by
  by_cases hhalt : M.start = M.halt
  · have hinitial : (initialID M input).state = M.halt := by
      simpa [initialID] using hhalt
    rw [show 1 = 0 + 1 by omega, run_succ, run_zero,
      OneMachine.nextID_of_halt M _ hinitial]
    exact run_zero_cell_eq_plain_blank M input hlength (by omega)
  · have hstate : (initialID M input).state ≠ M.halt := by
      simpa [initialID] using hhalt
    have hhead : (M.nextID (initialID M input)).head ≤ 1 := by
      rw [OneMachine.nextID_head_of_ne_halt hstate]
      rcases hstep : M.step M.start (tape M.blank input 0) with
        ⟨write, state, move⟩
      change (M.step M.start (tape M.blank input 0)).move.apply 0 ≤ 1
      rw [hstep]
      cases move <;> simp [Move.apply]
    rw [show 1 = 0 + 1 by omega, run_succ, run_zero]
    rw [Config.cellAt_of_ne (by omega : position ≠ (M.nextID (initialID M input)).head)]
    congr 1
    rw [OneMachine.nextID_tape_of_ne_head (by simp [initialID]; omega)]
    exact tape_eq_blank_of_length_le hlength

private theorem run_one_cellLeft_eq_plain_blank
    (M : OneMachine S Q) (input : List S) {position : ℕ}
    (hlength : input.length + 1 < position) (hthree : 3 ≤ position) :
    (run M input 1).cellAtLeft position = Cell.plain M.blank := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position ≠ 0)
  simp only [Config.cellAtLeft_succ]
  exact run_one_cell_eq_plain_blank M input (by omega) (by omega)

private def blankHistoryTile (M : OneMachine S Q) : History S Q where
  prevLeft := .plain M.blank
  prevCenter := .plain M.blank
  prevRight := .plain M.blank
  nextLeft := .plain M.blank
  nextCenter := .plain M.blank
  nextRight := .plain M.blank

private theorem historyTile_zero_eq_blank_of_tailPosition_le
    (M : OneMachine S Q) (input : List S) {position : ℕ}
    (hposition : tailPosition input ≤ position) :
    historyTile M input 0 position = blankHistoryTile M := by
  have hp : input.length + 3 ≤ position := by
    simpa [tailPosition] using hposition
  unfold historyTile blankHistoryTile
  simp only [Nat.zero_add]
  rw [run_zero_cellLeft_eq_plain_blank M input (by omega) (by omega)]
  rw [run_zero_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_zero_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cellLeft_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cell_eq_plain_blank M input (by omega) (by omega)]

private theorem historyTile_zero_eq_tail_of_tailPosition_le
    (M : OneMachine S Q) (input : List S) {position : ℕ}
    (hposition : tailPosition input ≤ position) :
    historyTile M input 0 position =
      historyTile M input 0 (tailPosition input) := by
  rw [historyTile_zero_eq_blank_of_tailPosition_le M input hposition]
  rw [historyTile_zero_eq_blank_of_tailPosition_le M input (le_refl _)]

variable [Fintype S] [Fintype Q] [DecidableEq S]

private def machineHistoryTiles (M : OneMachine S Q) : List (History S Q) :=
  Finset.univ.toList.filter fun t =>
    decide (t.prevLeft.Mem M ∧ t.prevCenter.Mem M ∧ t.prevRight.Mem M ∧
      t.nextLeft.Mem M ∧ t.nextCenter.Mem M ∧ t.nextRight.Mem M ∧
      localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter ∧
      (t.prevLeft = .boundary → t.nextLeft = .boundary))

private theorem mem_machineHistoryTiles_iff (M : OneMachine S Q) (t : History S Q) :
    t ∈ machineHistoryTiles M ↔
      t.prevLeft.Mem M ∧ t.prevCenter.Mem M ∧ t.prevRight.Mem M ∧
      t.nextLeft.Mem M ∧ t.nextCenter.Mem M ∧ t.nextRight.Mem M ∧
      localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter ∧
      (t.prevLeft = .boundary → t.nextLeft = .boundary) := by
  simp only [machineHistoryTiles, List.mem_filter, Finset.mem_toList,
    Finset.mem_univ, true_and, decide_eq_true_eq]

private theorem historyTile_mem_machineHistoryTiles {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input)
    (time position : ℕ) :
    historyTile M input time position ∈ machineHistoryTiles M := by
  rcases historyTile_cells_mem notHalts time position with
    ⟨hprevLeft, hprevCenter, hprevRight, hnextLeft, hnextCenter, hnextRight⟩
  exact (mem_machineHistoryTiles_iff M _).2
    ⟨hprevLeft, hprevCenter, hprevRight, hnextLeft, hnextCenter, hnextRight,
      historyTile_local notHalts time position, historyTile_boundaryOK M input time position⟩

private theorem localNextCell?_of_mem_machineHistoryTiles {M : OneMachine S Q}
    {t : History S Q} (h : t ∈ machineHistoryTiles M) :
    localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter := by
  obtain ⟨_, _, _, _, _, _, h, _⟩ := (mem_machineHistoryTiles_iff M t).mp h
  exact h

private theorem nextLeft_boundary_of_mem_machineHistoryTiles {M : OneMachine S Q}
    {t : History S Q} (h : t ∈ machineHistoryTiles M)
    (hb : t.prevLeft = .boundary) : t.nextLeft = .boundary := by
  obtain ⟨_, _, _, _, _, _, _, h⟩ := (mem_machineHistoryTiles_iff M t).mp h
  exact h hb

private theorem prevCenter_not_halt_of_mem_machineHistoryTiles {M : OneMachine S Q}
    {t : History S Q} {a : S} (h : t ∈ machineHistoryTiles M) :
    t.prevCenter ≠ Cell.head M.halt a := by
  obtain ⟨_, hc, _⟩ := (mem_machineHistoryTiles_iff M t).mp h
  intro heq
  simp [heq, Cell.Mem] at hc

private def initialRowTag : ℕ := 0

private def normalRowTag : ℕ := 1

private theorem initialRowTag_ne_normalRowTag :
    initialRowTag ≠ normalRowTag := by
  decide

/-- Encode a tagged row triple as one Wang colour. -/
private def taggedTripleCellColor (tag : ℕ) (a b c : Cell S Q) : ℕ :=
  Encodable.encode (tag, a, b, c)

private abbrev HMatches (a b : WangTile) : Prop := a.right = b.left
private abbrev VMatches (a b : WangTile) : Prop := a.top = b.bottom

/-- Encode the position and row tags followed by the two overlapping cell pairs. -/
private def horizontalColor (positionTag rowTag : ℕ)
    (prevLeft prevRight nextLeft nextRight : Cell S Q) : ℕ :=
  Encodable.encode (positionTag, rowTag, (prevLeft, prevRight), nextLeft, nextRight)

private def toWangTile (westTag eastTag rowTag nextRowTag : ℕ)
    (tile : History S Q) : WangTile where
  top := taggedTripleCellColor nextRowTag
    tile.nextLeft tile.nextCenter tile.nextRight
  bottom := taggedTripleCellColor rowTag
    tile.prevLeft tile.prevCenter tile.prevRight
  right := horizontalColor eastTag rowTag
    tile.prevCenter tile.prevRight tile.nextCenter tile.nextRight
  left := horizontalColor westTag rowTag
    tile.prevLeft tile.prevCenter tile.nextLeft tile.nextCenter

omit [DecidableEq Q] [DecidableEq S] in
private theorem hMatches_toWangTile_iff
    (westTag eastTag westTag' eastTag' rowTag nextRowTag rowTag' nextRowTag' : ℕ)
    (left right : History S Q) :
    HMatches
        (toWangTile westTag eastTag rowTag nextRowTag left)
        (toWangTile westTag' eastTag' rowTag' nextRowTag' right) ↔
      eastTag = westTag' ∧ rowTag = rowTag' ∧
        left.prevCenter = right.prevLeft ∧
        left.prevRight = right.prevCenter ∧
        left.nextCenter = right.nextLeft ∧
        left.nextRight = right.nextCenter := by
  simp [HMatches, toWangTile, horizontalColor, and_assoc]

omit [DecidableEq Q] [DecidableEq S] in
private theorem vMatches_toWangTile_iff
    (westTag eastTag westTag' eastTag' rowTag nextRowTag rowTag' nextRowTag' : ℕ)
    (lower upper : History S Q) :
    VMatches
        (toWangTile westTag eastTag rowTag nextRowTag lower)
        (toWangTile westTag' eastTag' rowTag' nextRowTag' upper) ↔
      nextRowTag = rowTag' ∧
        lower.nextLeft = upper.prevLeft ∧
        lower.nextCenter = upper.prevCenter ∧
        lower.nextRight = upper.prevRight := by
  simp [VMatches, toWangTile, taggedTripleCellColor]

private def initialTile (M : OneMachine S Q) (input : List S) (position : ℕ) : WangTile :=
  let tail := tailPosition input
  if position < tail then
    toWangTile position (position + 1) initialRowTag normalRowTag
      (historyTile M input 0 position)
  else
    toWangTile tail tail initialRowTag normalRowTag
      (historyTile M input 0 tail)

private def initialTiles (M : OneMachine S Q) (input : List S) : List WangTile :=
  (List.range (tailPosition input + 1)).map (initialTile M input)

private def normalTiles (M : OneMachine S Q) : List WangTile :=
  (machineHistoryTiles M).map
    (toWangTile 0 0 normalRowTag normalRowTag)

private def tiles (M : OneMachine S Q) (input : List S) : List WangTile :=
  initialTiles M input ++ normalTiles M

private def seed (M : OneMachine S Q) (input : List S) : WangTile :=
  initialTile M input 0

omit [DecidableEq S] in
private theorem initialTile_mem (M : OneMachine S Q) (input : List S) (position : ℕ) :
    initialTile M input position ∈ initialTiles M input := by
  rw [initialTiles, List.mem_map]
  by_cases hposition : position < tailPosition input
  · exact ⟨position, by simp only [List.mem_range]; omega, rfl⟩
  · exact ⟨tailPosition input, by simp, by simp [initialTile, hposition]⟩

omit [DecidableEq S] in
private theorem initialTile_history (M : OneMachine S Q) (input : List S) (position : ℕ) :
    let tail := tailPosition input
    initialTile M input position =
      if position < tail then
        toWangTile position (position + 1) initialRowTag normalRowTag
          (historyTile M input 0 position)
      else
        toWangTile tail tail initialRowTag normalRowTag
          (historyTile M input 0 position) := by
  dsimp only
  rw [initialTile]
  split_ifs with hposition
  · rfl
  · congr 1
    exact (historyTile_zero_eq_tail_of_tailPosition_le M input (by omega)).symm

omit [DecidableEq S] in
private theorem initialTile_hMatches (M : OneMachine S Q) (input : List S) (position : ℕ) :
    HMatches (initialTile M input position)
      (initialTile M input (position + 1)) := by
  rw [initialTile_history, initialTile_history]
  by_cases hposition : position + 1 < tailPosition input
  · simpa [hposition, show position < tailPosition input by omega,
      hMatches_toWangTile_iff] using historyTile_hMatches M input 0 position
  · have htail : tailPosition input ≤ position + 1 := by omega
    by_cases hbefore : position < tailPosition input
    · have heq : position + 1 = tailPosition input := by omega
      simpa [hbefore, heq, hMatches_toWangTile_iff] using
        historyTile_hMatches M input 0 position
    · rw [historyTile_zero_eq_tail_of_tailPosition_le M input (by omega :
        tailPosition input ≤ position)]
      rw [historyTile_zero_eq_tail_of_tailPosition_le M input htail]
      rw [historyTile_zero_eq_blank_of_tailPosition_le M input (le_refl _)]
      simp [hbefore, hposition, hMatches_toWangTile_iff, blankHistoryTile]

/- Soundness: place the actual history tile at `(position, time)`.  Time zero
uses the tagged finite-input row, while all later rows use the fixed normal
palette.  Horizontal and vertical validity are then direct overlap facts. -/

private def runTile (M : OneMachine S Q) (input : List S) (time position : ℕ) : WangTile :=
  if time = 0 then initialTile M input position
  else toWangTile 0 0 normalRowTag normalRowTag
    (historyTile M input time position)

private theorem runTile_mem {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input)
    (time position : ℕ) :
    runTile M input time position ∈ tiles M input := by
  cases time with
  | zero => simp [runTile, tiles, initialTile_mem]
  | succ time =>
      rw [runTile, ite_eq_right (by omega)]
      simp only [tiles, List.mem_append]
      right
      rw [normalTiles, List.mem_map]
      exact ⟨historyTile M input (time + 1) position,
        historyTile_mem_machineHistoryTiles notHalts
          (time + 1) position, rfl⟩

omit [DecidableEq S] in
private theorem runTile_hMatches (M : OneMachine S Q) (input : List S)
    (time position : ℕ) :
    HMatches (runTile M input time position)
      (runTile M input time (position + 1)) := by
  cases time with
  | zero => simpa [runTile] using initialTile_hMatches M input position
  | succ time =>
      simpa [runTile, hMatches_toWangTile_iff] using
        historyTile_hMatches M input (time + 1) position

omit [DecidableEq S] in
private theorem runTile_vMatches (M : OneMachine S Q) (input : List S)
    (time position : ℕ) :
    VMatches (runTile M input time position)
      (runTile M input (time + 1) position) := by
  cases time with
  | zero =>
      rw [runTile, ite_eq_left rfl, runTile, ite_eq_right (by omega)]
      rw [initialTile_history]
      split_ifs <;> simp [vMatches_toWangTile_iff, historyTile]
  | succ time =>
      simp [runTile, vMatches_toWangTile_iff, historyTile]

private theorem tilesQuadrant_of_not_halts
    {M : OneMachine S Q} {input : List S} (notHalts : ¬ Halts M input) :
    TilesQuadrant ⟨tiles M input, seed M input⟩ := by
  refine ⟨fun x y => runTile M input y x, rfl, ?_⟩
  intro x y
  exact ⟨runTile_mem notHalts y x, runTile_hMatches M input y x,
    runTile_vMatches M input y x⟩

/- Completeness starts by classifying every palette member.  The seed fixes
position zero, horizontal tags force its unique successor repeatedly, and the
self-looping tail handles all remaining positions.  Since every legal north
edge is tagged `normal`, vertical matching excludes another initial tile above
the bottom row. -/

private theorem mem_tiles_iff (M : OneMachine S Q) (input : List S) (tile : WangTile) :
    tile ∈ tiles M input ↔
      (∃ position, position < tailPosition input ∧
        toWangTile position (position + 1) initialRowTag normalRowTag
          (historyTile M input 0 position) = tile) ∨
      tile = toWangTile (tailPosition input) (tailPosition input)
          initialRowTag normalRowTag
          (historyTile M input 0 (tailPosition input)) ∨
      ∃ history, history ∈ machineHistoryTiles M ∧
        toWangTile 0 0 normalRowTag normalRowTag history = tile := by
  have hprefix : (List.range (tailPosition input)).map (initialTile M input) =
      (List.range (tailPosition input)).map (fun p =>
        toWangTile p (p + 1) initialRowTag normalRowTag (historyTile M input 0 p)) :=
    List.map_congr_left fun p hp => by simp [initialTile, List.mem_range.mp hp]
  rw [tiles, initialTiles, List.range_succ, List.map_append, hprefix]
  simp [normalTiles, List.mem_map, initialTile]

/-- Every legal tile presents the normal-row tag on its north edge. -/
private theorem northRowTag_eq_normal_of_mem
    {M : OneMachine S Q} {input : List S} {tile : WangTile}
    (member : tile ∈ tiles M input) :
    tile.top.unpair.1 = normalRowTag := by
  rcases (mem_tiles_iff M input tile).1 member with
    ⟨position, _hposition, rfl⟩ | rfl | ⟨history, _hhistory, rfl⟩ <;>
    simp [toWangTile, taggedTripleCellColor]

private theorem next_initialTile_of_hMatches_mem
    (M : OneMachine S Q) (input : List S) (position : ℕ) {right : WangTile}
    (hmatch : HMatches (initialTile M input position) right)
    (hmem : right ∈ tiles M input) :
    right = initialTile M input (position + 1) := by
  rcases (mem_tiles_iff M input right).1 hmem with
    ⟨next, hnext, hright⟩ | hright | ⟨history, _hhistory, hright⟩
  · rw [initialTile] at hmatch ⊢
    split_ifs at hmatch with hposition
    · rw [← hright] at hmatch
      have htags := (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch
      have heq : next = position + 1 := htags.1.symm
      subst next
      rw [ite_eq_left hnext]
      exact hright.symm
    · rw [← hright] at hmatch
      have htags := (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch
      omega
  · rw [initialTile] at hmatch ⊢
    split_ifs at hmatch with hposition
    · rw [hright] at hmatch
      have htags := (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch
      have heq : position + 1 = tailPosition input := htags.1
      rw [ite_eq_right (by omega)]
      exact hright
    · rw [ite_eq_right (by omega)]
      exact hright
  · rw [initialTile] at hmatch
    split_ifs at hmatch <;> rw [← hright] at hmatch
    · exact False.elim (initialRowTag_ne_normalRowTag
        ((hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch).2.1)
    · exact False.elim (initialRowTag_ne_normalRowTag
        ((hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch).2.1)

private theorem seeded_tiling_row_zero_eq
    {M : OneMachine S Q} {input : List S}
    {plane : ℕ → ℕ → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    (seeded : plane 0 0 = seed M input) :
    ∀ position, plane position 0 = initialTile M input position := by
  intro position
  induction position with
  | zero => exact seeded
  | succ position ih =>
      apply next_initialTile_of_hMatches_mem M input position
      · simpa [ih] using (valid position 0).2.1
      · exact (valid (position + 1) 0).1

private theorem normal_of_vMatches
    (M : OneMachine S Q) (input : List S) {lower upper : WangTile}
    (lowerMem : lower ∈ tiles M input) (upperMem : upper ∈ tiles M input)
    (hmatches : VMatches lower upper) :
    ∃ history, history ∈ machineHistoryTiles M ∧
      toWangTile 0 0 normalRowTag normalRowTag history = upper := by
  have upperRowTag : upper.bottom.unpair.1 = normalRowTag := by
    rw [← hmatches]
    exact northRowTag_eq_normal_of_mem lowerMem
  rcases (mem_tiles_iff M input upper).1 upperMem with
    ⟨upperPosition, _hupperPosition, hupper⟩ | hupper |
      ⟨upperHistory, hupperHistory, hupper⟩
  · have tagEq : initialRowTag = normalRowTag := by
      simpa [← hupper, toWangTile, taggedTripleCellColor] using upperRowTag
    exact (initialRowTag_ne_normalRowTag tagEq).elim
  · have tagEq : initialRowTag = normalRowTag := by
      simpa [hupper, toWangTile, taggedTripleCellColor] using upperRowTag
    exact (initialRowTag_ne_normalRowTag tagEq).elim
  · exact ⟨upperHistory, hupperHistory, hupper⟩

private theorem positive_row_decode
    {M : OneMachine S Q} {input : List S}
    {plane : ℕ → ℕ → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    (time position : ℕ) :
    ∃ history, history ∈ machineHistoryTiles M ∧
      toWangTile 0 0 normalRowTag normalRowTag history =
        plane position (time + 1) := by
  exact normal_of_vMatches M input
    (valid position time).1 (valid position (time + 1)).1
    ((valid position time).2.2)

/-- A decoded positive row, represented by a coherent row of local history
tiles whose lower cells are the corresponding machine configuration. -/
private structure IsDecodedHistoryRow (M : OneMachine S Q) (input : List S)
    (plane : ℕ → ℕ → WangTile) (time : ℕ)
    (row : ℕ → History S Q) : Prop where
  /-- Each local history belongs to the normal palette. -/
  mem (position : ℕ) : row position ∈ machineHistoryTiles M
  /-- Each history encodes the corresponding tiling cell. -/
  encoded (position : ℕ) :
    toWangTile 0 0 normalRowTag normalRowTag (row position) =
      plane position time
  /-- The lower triples agree with the true run. -/
  prevCells (position : ℕ) :
    (row position).prevLeft = (historyTile M input time position).prevLeft ∧
      (row position).prevCenter = (historyTile M input time position).prevCenter ∧
      (row position).prevRight = (historyTile M input time position).prevRight

private def DecodedHistoryRow (M : OneMachine S Q) (input : List S)
    (plane : ℕ → ℕ → WangTile) (time : ℕ) : Prop :=
  ∃ row, IsDecodedHistoryRow M input plane time row

/- A decoded row remembers more than tile membership: its lower triples equal
the true machine configuration at that time.  Local transition validity fixes
each upper center; overlap with neighboring tiles fixes the upper left and
right cells.  Vertical matching then transfers all three cells to the lower
triple of the next row. -/

private theorem row_one_decoded
    {M : OneMachine S Q} {input : List S}
    {plane : ℕ → ℕ → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    (seeded : plane 0 0 = seed M input) :
    DecodedHistoryRow M input plane 1 := by
  choose row hrow using fun position => positive_row_decode valid 0 position
  refine ⟨row, ⟨fun position => (hrow position).1,
    fun position => (hrow position).2, ?_⟩⟩
  intro position
  have hbottom := seeded_tiling_row_zero_eq valid seeded position
  have hvertical : VMatches
      (initialTile M input position)
      (toWangTile 0 0 normalRowTag normalRowTag (row position)) := by
    simpa [hbottom, (hrow position).2] using (valid position 0).2.2
  rw [initialTile_history] at hvertical
  split_ifs at hvertical <;>
    have hcells := (vMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hvertical
  all_goals
    exact ⟨by simpa [historyTile] using hcells.2.1.symm,
      by simpa [historyTile] using hcells.2.2.1.symm,
      by simpa [historyTile] using hcells.2.2.2.symm⟩

private theorem positive_row_hMatches_cells
    {M : OneMachine S Q} {input : List S}
    {plane : ℕ → ℕ → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    {time position : ℕ} {left right : History S Q}
    (hleft : toWangTile 0 0 normalRowTag normalRowTag left =
      plane position (time + 1))
    (hright : toWangTile 0 0 normalRowTag normalRowTag right =
      plane (position + 1) (time + 1)) :
    left.prevCenter = right.prevLeft ∧
      left.prevRight = right.prevCenter ∧
      left.nextCenter = right.nextLeft ∧
      left.nextRight = right.nextCenter := by
  have hhorizontal : HMatches
      (toWangTile 0 0 normalRowTag normalRowTag left)
      (toWangTile 0 0 normalRowTag normalRowTag right) := by
    simpa [hleft, hright] using (valid position (time + 1)).2.1
  exact (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hhorizontal |>.2.2

private theorem nextCenter_eq_historyTile_nextCenter_of_prev_cells
    {M : OneMachine S Q} {input : List S} {time position : ℕ}
    {tile : History S Q}
    (tileMem : tile ∈ machineHistoryTiles M)
    (hstate : (run M input time).state ≠ M.halt)
    (hnext : (run M input (time + 1)).state ≠ M.halt)
    (hprevLeft : tile.prevLeft = (historyTile M input time position).prevLeft)
    (hprevCenter : tile.prevCenter = (historyTile M input time position).prevCenter)
    (hprevRight : tile.prevRight = (historyTile M input time position).prevRight) :
    tile.nextCenter = (historyTile M input time position).nextCenter := by
  have hlocal := localNextCell?_of_mem_machineHistoryTiles tileMem
  rw [hprevLeft, hprevCenter, hprevRight] at hlocal
  have hrun := historyTile_local_of_state_ne_halt hstate hnext position
  rw [hrun] at hlocal
  exact Option.some.inj hlocal.symm

/-- Local transition validity and horizontal matching determine all three
upper cells of a decoded history row. -/
private theorem next_cells_eq_historyTile_of_decoded_row
    {M : OneMachine S Q} {input : List S}
    {plane : ℕ → ℕ → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    {time : ℕ} {row : ℕ → History S Q}
    (decoded : IsDecodedHistoryRow M input plane (time + 1) row)
    (hstate : (run M input (time + 1)).state ≠ M.halt)
    (hnext : (run M input (time + 1 + 1)).state ≠ M.halt)
    (position : ℕ) :
    (row position).nextLeft =
        (historyTile M input (time + 1 + 1) position).prevLeft ∧
      (row position).nextCenter =
        (historyTile M input (time + 1 + 1) position).prevCenter ∧
      (row position).nextRight =
        (historyTile M input (time + 1 + 1) position).prevRight := by
  have nextCenter (p : ℕ) :
      (row p).nextCenter = (historyTile M input (time + 1) p).nextCenter :=
    nextCenter_eq_historyTile_nextCenter_of_prev_cells
      (decoded.mem p) hstate hnext
      (decoded.prevCells p).1 (decoded.prevCells p).2.1
      (decoded.prevCells p).2.2
  have nextLeft : (row position).nextLeft =
      (historyTile M input (time + 1 + 1) position).prevLeft := by
    cases position with
    | zero =>
        rw [nextLeft_boundary_of_mem_machineHistoryTiles (decoded.mem 0)
          (by simpa [historyTile] using (decoded.prevCells 0).1)]
        simp [historyTile]
    | succ predecessor =>
        have hmatches := positive_row_hMatches_cells valid
          (time := time) (position := predecessor)
          (decoded.encoded predecessor) (decoded.encoded (predecessor + 1))
        calc
          (row (Nat.succ predecessor)).nextLeft =
              (row predecessor).nextCenter := by
            simpa [Nat.succ_eq_add_one] using hmatches.2.2.1.symm
          _ = (historyTile M input (time + 1) predecessor).nextCenter :=
            nextCenter predecessor
          _ = (historyTile M input (time + 1 + 1)
              (Nat.succ predecessor)).prevLeft := by
            simp [historyTile, Nat.succ_eq_add_one]
  have hmatches := positive_row_hMatches_cells valid
    (time := time) (position := position)
    (decoded.encoded position) (decoded.encoded (position + 1))
  exact ⟨nextLeft,
    by simpa [historyTile] using nextCenter position,
    calc
      (row position).nextRight = (row (position + 1)).nextCenter :=
        hmatches.2.2.2
      _ = (historyTile M input (time + 1) (position + 1)).nextCenter :=
        nextCenter (position + 1)
      _ = (historyTile M input (time + 1 + 1) position).prevRight := by
        simp [historyTile]⟩

private theorem next_row_decoded
    {M : OneMachine S Q} {input : List S}
    {plane : ℕ → ℕ → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    {time : ℕ}
    (hrow : DecodedHistoryRow M input plane (time + 1))
    (hstate : (run M input (time + 1)).state ≠ M.halt)
    (hnext : (run M input (time + 1 + 1)).state ≠ M.halt) :
    DecodedHistoryRow M input plane (time + 1 + 1) := by
  rcases hrow with ⟨lower, decoded⟩
  choose upper hupper using fun position =>
    positive_row_decode valid (time + 1) position
  refine ⟨upper, ⟨fun position => (hupper position).1,
    fun position => (hupper position).2, ?_⟩⟩
  intro position
  have hvertical : VMatches
      (toWangTile 0 0 normalRowTag normalRowTag (lower position))
      (toWangTile 0 0 normalRowTag normalRowTag (upper position)) := by
    simpa [decoded.encoded position, (hupper position).2] using
      (valid position (time + 1)).2.2
  have cells := (vMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hvertical
  have nextCells := next_cells_eq_historyTile_of_decoded_row
    valid decoded hstate hnext position
  exact ⟨cells.2.1.symm.trans nextCells.1,
    cells.2.2.1.symm.trans nextCells.2.1,
    cells.2.2.2.symm.trans nextCells.2.2⟩

private theorem decoded_row_of_nonhalting_prefix
    {M : OneMachine S Q} {input : List S}
    {plane : ℕ → ℕ → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    (seeded : plane 0 0 = seed M input) (time : ℕ)
    (hprefix : ∀ step, 1 ≤ step → step ≤ time + 1 →
      (run M input step).state ≠ M.halt) :
    DecodedHistoryRow M input plane (time + 1) := by
  induction time with
  | zero => exact row_one_decoded valid seeded
  | succ time ih =>
      exact next_row_decoded valid
        (time := time)
        (ih fun step hstep hbound => hprefix step hstep (by omega))
        (hprefix (time + 1) (by omega) (by omega))
        (hprefix (time + 1 + 1) (by omega) (by omega))

/- At the first halting time, all preceding positive rows can be decoded.  If
halting occurs immediately, row one already contains a forbidden halt head.
Otherwise the tile at the next head position would have to realize a local
transition into `halt`, which the normal palette explicitly omits. -/

private theorem false_of_run_one_halt
    {M : OneMachine S Q} {input : List S}
    {plane : ℕ → ℕ → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    (seeded : plane 0 0 = seed M input)
    (hhalt : (run M input 1).state = M.halt) : False := by
  let position := (run M input 1).head
  rcases row_one_decoded valid seeded with ⟨row, decoded⟩
  apply prevCenter_not_halt_of_mem_machineHistoryTiles
    (a := (run M input 1).tape (run M input 1).head) (decoded.mem position)
  rw [(decoded.prevCells position).2.1]
  change (run M input 1).cellAt position =
    Cell.head M.halt ((run M input 1).tape (run M input 1).head)
  dsimp only [position]
  rw [Config.cellAt_head, hhalt]

private theorem false_of_next_halt_from_decoded_row
    {M : OneMachine S Q} {input : List S}
    {plane : ℕ → ℕ → WangTile}
    {time : ℕ}
    (hrow : DecodedHistoryRow M input plane (time + 1))
    (hstate : (run M input (time + 1)).state ≠ M.halt)
    (hnext : (run M input (time + 1 + 1)).state = M.halt) : False := by
  let configuration := run M input (time + 1)
  let position :=
    (M.step configuration.state (configuration.tape configuration.head)).move.apply
      configuration.head
  rcases hrow with ⟨row, decoded⟩
  let tile := row position
  have tileMem := decoded.mem position
  have prevCells := decoded.prevCells position
  have hstate' : configuration.state ≠ M.halt := by
    simpa [configuration] using hstate
  have hnextState :
      (M.step configuration.state (configuration.tape configuration.head)).state =
        M.halt := by
    rw [← OneMachine.nextID_state_of_ne_halt hstate']
    simpa [configuration, run_succ] using hnext
  have hlocal := localNextCell?_of_mem_machineHistoryTiles tileMem
  rw [prevCells.1, prevCells.2.1, prevCells.2.2] at hlocal
  have hnone := OneMachine.localNextCell?_at_next_halt_head
    (M := M) (c := configuration) hstate' hnextState
  have hnoneRun :
      localNextCell? M (historyTile M input (time + 1) position).prevLeft
          (historyTile M input (time + 1) position).prevCenter
          (historyTile M input (time + 1) position).prevRight = none := by
    simpa [historyTile, configuration, position] using hnone
  rw [hnoneRun] at hlocal
  cases hlocal

private theorem not_tilesQuadrant_of_halts
    {M : OneMachine S Q} {input : List S} (halts : Halts M input) :
    ¬ TilesQuadrant ⟨tiles M input, seed M input⟩ := by
  rcases exists_first_halting_time halts with ⟨step, hhalt, before⟩
  rintro ⟨plane, seeded, valid⟩
  cases step with
  | zero =>
      apply false_of_run_one_halt valid seeded
      have hinitial : (initialID M input).state = M.halt := by
        simpa [run_zero] using hhalt
      rw [show 1 = 0 + 1 by omega, run_succ, run_zero,
        OneMachine.nextID_of_halt M _ hinitial]
      exact hinitial
  | succ step =>
      cases step with
      | zero =>
          exact false_of_run_one_halt valid seeded (by simpa using hhalt)
      | succ time =>
          have hrow := decoded_row_of_nonhalting_prefix
            valid seeded time (fun k _positive bounded => before k (by omega))
          exact false_of_next_halt_from_decoded_row hrow
            (before (time + 1) (by omega)) (by simpa using hhalt)

private theorem tilesQuadrant_iff_not_halts
    {M : OneMachine S Q} {input : List S} :
    TilesQuadrant ⟨tiles M input, seed M input⟩ ↔ ¬ Halts M input := by
  constructor
  · intro tiled halts
    exact not_tilesQuadrant_of_halts halts tiled
  · exact tilesQuadrant_of_not_halts

end Kernel

namespace Folded

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

private inductive Side where
  | left
  | right
  deriving DecidableEq

private instance : Fintype Side :=
  ⟨{.left, .right}, by rintro (_ | _) <;> simp⟩

private def Side.opposite : Side → Side
  | .left => .right
  | .right => .left

private def Side.isOutward : Side → Turing.Dir → Bool
  | .left, .left | .right, .right => true
  | _, _ => false

private def Side.isInward (side : Side) (dir : Turing.Dir) : Bool :=
  !(side.isOutward dir)

private def rightAbs (position : ℕ) : Int := position

private def leftAbs (position : ℕ) : Int := -((position : Int) + 1)

private def activeAbs : Side → ℕ → Int
  | .right, head => rightAbs head
  | .left, head => leftAbs head

private def sourceOffset (side : Side) (head : ℕ) (absolute : Int) : Int :=
  absolute - activeAbs side head

private def nextSide (side : Side) (atOrigin : Bool) (dir : Turing.Dir) : Side :=
  if atOrigin && side.isInward dir then side.opposite else side

private def moveHead (side : Side) (atOrigin : Bool) (head : ℕ)
    (dir : Turing.Dir) : ℕ :=
  if atOrigin && side.isInward dir then head
  else if side.isOutward dir then head + 1
  else head.pred

/- `Config` deliberately retains the complete source TM0 configuration beside
the finite folded control data.  It is a semantic relation used to prove the
simulation, not the eventual executable machine state. -/

private structure Config (Γ Λ : Type) [Inhabited Γ] where
  /-- The full source TM0 configuration. -/
  source : Turing.TM0.Cfg Γ Λ
  /-- The active half of the folded cell. -/
  side : Side
  /-- The folded natural-number head position. -/
  head : ℕ

private def Config.afterWrite (config : Config Γ Λ) (q' : Λ) (symbol : Γ) : Config Γ Λ :=
  { source := { q := q', Tape := config.source.Tape.write symbol }
    side := config.side
    head := config.head }

private def Config.afterMove (config : Config Γ Λ) (q' : Λ) (dir : Turing.Dir) : Config Γ Λ :=
  { source := { q := q', Tape := config.source.Tape.move dir }
    side := nextSide config.side (decide (config.head = 0)) dir
    head := moveHead config.side (decide (config.head = 0)) config.head dir }

private def Config.step (M : Turing.TM0.Machine Γ Λ) (config : Config Γ Λ) : Option (Config Γ Λ) :=
  match M config.source.q config.source.Tape.head with
  | none => none
  | some (q', .write symbol) => some (config.afterWrite q' symbol)
  | some (q', .move dir) => some (config.afterMove q' dir)

private def Config.initial (input : List Γ) : Config Γ Λ where
  source := Turing.TM0.init input
  side := .right
  head := 0

private def symbolsAt (tape : Turing.Tape Γ) (side : Side)
    (head position : ℕ) : Γ × Γ :=
  (tape.nth (sourceOffset side head (leftAbs position)),
    tape.nth (sourceOffset side head (rightAbs position)))

/- Moving the source head changes the origin from which tape offsets are
measured.  The absolute source position represented at each target cell stays
fixed, so every stored symbol pair remains unchanged. -/

@[simp] private theorem sourceOffset_right_head (head : ℕ) :
    sourceOffset .right head (rightAbs head) = 0 := by
  simp [sourceOffset, activeAbs, rightAbs]

@[simp] private theorem sourceOffset_left_head (head : ℕ) :
    sourceOffset .left head (leftAbs head) = 0 := by
  simp [sourceOffset, activeAbs, leftAbs]

private theorem activeAbs_moveHead (side : Side) (head : ℕ) (dir : Turing.Dir) :
    activeAbs (nextSide side (decide (head = 0)) dir)
        (moveHead side (decide (head = 0)) head dir) =
      activeAbs side head + match dir with
      | .left => -1
      | .right => 1 := by
  cases side <;> cases dir <;> by_cases h : head = 0
  all_goals subst_vars
  all_goals simp_all [nextSide, moveHead, Side.isInward, Side.isOutward,
    Side.opposite, activeAbs, leftAbs, rightAbs]
  all_goals try omega

private theorem sourceOffset_moveHead (side : Side) (head : ℕ) (dir : Turing.Dir)
    (absolute : Int) :
    sourceOffset (nextSide side (decide (head = 0)) dir)
        (moveHead side (decide (head = 0)) head dir) absolute =
      sourceOffset side head absolute - match dir with
      | .left => -1
      | .right => 1 := by
  unfold sourceOffset
  rw [activeAbs_moveHead]
  cases dir <;> omega

private theorem symbolsAt_move (tape : Turing.Tape Γ) (side : Side)
    (head position : ℕ) (dir : Turing.Dir) :
    symbolsAt (tape.move dir)
        (nextSide side (decide (head = 0)) dir)
        (moveHead side (decide (head = 0)) head dir) position =
      symbolsAt tape side head position := by
  cases dir <;> simp [symbolsAt, sourceOffset_moveHead]

private theorem sourceOffset_left_ne_zero_of_ne_head
    (side : Side) {head position : ℕ} (h : position ≠ head) :
    sourceOffset side head (leftAbs position) ≠ 0 := by
  cases side <;> simp [sourceOffset, activeAbs, leftAbs, rightAbs] <;> omega

private theorem sourceOffset_right_ne_zero_of_ne_head
    (side : Side) {head position : ℕ} (h : position ≠ head) :
    sourceOffset side head (rightAbs position) ≠ 0 := by
  cases side <;> simp [sourceOffset, activeAbs, leftAbs, rightAbs] <;> omega

/- A write leaves every inactive target cell unchanged and replaces exactly
one component of the pair at the active cell.  These lemmas are the tape part
of the folded simulation invariant. -/

private theorem symbolsAt_write_inactive (tape : Turing.Tape Γ) (side : Side)
    {head position : ℕ} (symbol : Γ) (h : position ≠ head) :
    symbolsAt (tape.write symbol) side head position =
      symbolsAt tape side head position := by
  simp [symbolsAt, sourceOffset_left_ne_zero_of_ne_head side h,
    sourceOffset_right_ne_zero_of_ne_head side h]

private theorem sourceOffset_right_left_head_ne_zero (head : ℕ) :
    sourceOffset .right head (leftAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

private theorem sourceOffset_left_right_head_ne_zero (head : ℕ) :
    sourceOffset .left head (rightAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

private theorem symbolsAt_write_active (tape : Turing.Tape Γ) (side : Side)
    (head : ℕ) (symbol : Γ) :
    symbolsAt (tape.write symbol) side head head =
      match side with
      | .left => (symbol, (symbolsAt tape side head head).2)
      | .right => ((symbolsAt tape side head head).1, symbol) := by
  cases side with
  | left =>
      simp only [symbolsAt, sourceOffset_left_head, Turing.Tape.write_nth,
        ite_eq_left, Prod.mk.injEq, true_and]
      rw [ite_eq_right (sourceOffset_left_right_head_ne_zero head)]
  | right =>
      simp only [symbolsAt, sourceOffset_right_head, Turing.Tape.write_nth,
        ite_eq_left, Prod.mk.injEq, and_true]
      rw [ite_eq_right (sourceOffset_right_left_head_ne_zero head)]

private theorem Config.step_source {M : Turing.TM0.Machine Γ Λ} {config next : Config Γ Λ}
    (hstep : Config.step M config = some next) :
    Turing.TM0.step M config.source = some next.source := by
  unfold Config.step at hstep
  cases hm : M config.source.q config.source.Tape.head with
  | none => simp [hm] at hstep
  | some result =>
      rcases result with ⟨q', stmt⟩
      cases stmt <;> simp only [hm, Option.some.injEq] at hstep <;> cases hstep <;>
        simp [Turing.TM0.step, Config.afterWrite, Config.afterMove, hm]

end Folded

section Folding

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

open Folded (Side)

/-- A folded tape cell stores both source symbols and its boundary flag. -/
private structure TapeSymbol (Γ : Type) where
  /-- Whether this cell is at the fold between source positions −1 and 0. -/
  atOrigin : Bool
  /-- The source symbol at position −(i + 1). -/
  left : Γ
  /-- The source symbol at position i. -/
  right : Γ
  deriving DecidableEq, Fintype

private def TapeSymbol.blank : TapeSymbol Γ := ⟨false, default, default⟩

private def TapeSymbol.active : TapeSymbol Γ → Side → Γ
  | cell, .left => cell.left
  | cell, .right => cell.right

private def TapeSymbol.write (cell : TapeSymbol Γ) (side : Side) (symbol : Γ) :
    TapeSymbol Γ :=
  match side with
  | .left => { cell with left := symbol }
  | .right => { cell with right := symbol }

/-- Finite control of the folded machine. -/
private inductive Control (Λ : Type) where
  | run (side : Side) (label : Λ)
  | halt
  deriving DecidableEq, Fintype

private def physicalMove (side : Side) (atOrigin : Bool) (dir : Turing.Dir) : Move :=
  if atOrigin && side.isInward dir then .left
  else if side.isOutward dir then .right else .left

private def typedStep (M : Turing.TM0.Machine Γ Λ) :
    Control Λ → TapeSymbol Γ → Action (TapeSymbol Γ) (Control Λ)
  | .halt, cell => ⟨cell, .halt, .left⟩
  | .run side q, cell =>
      match M q (cell.active side) with
      | none => ⟨cell, .halt, .left⟩
      | some (q', .write symbol) => ⟨cell.write side symbol, .run side q', .stay⟩
      | some (q', .move dir) =>
          ⟨cell, .run (Folded.nextSide side cell.atOrigin dir) q',
            physicalMove side cell.atOrigin dir⟩

private def machine (M : Turing.TM0.Machine Γ Λ) :
    OneMachine (TapeSymbol Γ) (Control Λ) where
  blank := TapeSymbol.blank
  start := .run .right default
  halt := .halt
  step := typedStep M

private def foldedInput (source : List Γ) : List (TapeSymbol Γ) :=
  ⟨true, default, source.headI⟩ :: source.tail.map fun a => ⟨false, default, a⟩

private theorem symbolsAt_initial (source : List Γ) (position : ℕ) :
    Folded.symbolsAt
        (Folded.Config.initial (Λ := Λ) source).source.Tape .right 0 position =
      (default, source.getI position) := by
  cases position with
  | zero =>
      have hleft : Folded.sourceOffset .right 0
          (Folded.leftAbs 0) = Int.negSucc 0 := by
        simp [Folded.sourceOffset, Folded.activeAbs,
          Folded.leftAbs, Folded.rightAbs]
      have hright : Folded.sourceOffset .right 0
          (Folded.rightAbs 0) = 0 := by
        simp [Folded.sourceOffset, Folded.activeAbs,
          Folded.rightAbs]
      rw [Folded.symbolsAt, hleft, hright]
      have hget : source.headI = source.getI 0 :=
        (List.getI_zero_eq_headI (l := source)).symm
      simp [Folded.Config.initial, Turing.TM0.init,
        Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth,
        hget]
  | succ position =>
      have hleft : Folded.sourceOffset .right 0
          (Folded.leftAbs (position + 1)) =
            Int.negSucc (position + 1) := by
        simp [Folded.sourceOffset, Folded.activeAbs,
          Folded.leftAbs, Folded.rightAbs]
        omega
      have hright : Folded.sourceOffset .right 0
          (Folded.rightAbs (position + 1)) =
            Int.ofNat (position + 1) := by
        simp [Folded.sourceOffset, Folded.activeAbs,
          Folded.rightAbs]
      rw [Folded.symbolsAt, hleft, hright]
      have hget : source.tail.getI position = source.getI (position + 1) := by
        cases source <;> rfl
      simp [Folded.Config.initial, Turing.TM0.init,
        Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth,
        hget]

/-- The folded target symbol represented by a semantic TM0 configuration. -/
private def foldedSymbol (config : Folded.Config Γ Λ) (position : ℕ) : TapeSymbol Γ :=
  let symbols := Folded.symbolsAt
    config.source.Tape config.side config.head position
  ⟨decide (position = 0), symbols.1, symbols.2⟩

private def toID (config : Folded.Config Γ Λ) : Config (TapeSymbol Γ) (Control Λ) where
  tape := fun position => foldedSymbol config position
  head := config.head
  state := .run config.side config.source.q

private theorem initialID_eq_toID (M : Turing.TM0.Machine Γ Λ) (source : List Γ) :
    initialID (machine M) (foldedInput source) = toID (Folded.Config.initial (Λ := Λ) source) := by
  apply Config.ext
  · funext position
    change tape TapeSymbol.blank (foldedInput source) position =
      foldedSymbol (Folded.Config.initial (Λ := Λ) source) position
    change tape TapeSymbol.blank (foldedInput source) position =
      TapeSymbol.mk (decide (position = 0))
        (Folded.symbolsAt (Folded.Config.initial (Λ := Λ) source).source.Tape
          .right 0 position).1
        (Folded.symbolsAt (Folded.Config.initial (Λ := Λ) source).source.Tape
          .right 0 position).2
    rw [symbolsAt_initial]
    cases position with
    | zero => simp [tape, foldedInput, List.getI_zero_eq_headI]
    | succ position =>
        simp [tape, foldedInput, TapeSymbol.blank, ← List.getI_eq_getElem?_getD]
  · rfl
  · rfl

omit [Inhabited Λ] in
private theorem foldedSymbol_active_head (config : Folded.Config Γ Λ) :
    (foldedSymbol config config.head).active config.side =
      config.source.Tape.head := by
  rcases config with ⟨source, side, head⟩
  cases side <;>
    simp [foldedSymbol, TapeSymbol.active, Folded.symbolsAt]

omit [Inhabited Λ] in
private theorem foldedSymbol_afterMove (config : Folded.Config Γ Λ)
    (q' : Λ) (dir : Turing.Dir) (position : ℕ) :
    foldedSymbol (config.afterMove q' dir) position =
      foldedSymbol config position := by
  simp only [foldedSymbol, Folded.Config.afterMove]
  rw [Folded.symbolsAt_move]

omit [Inhabited Λ] in
private theorem foldedSymbol_afterWrite (config : Folded.Config Γ Λ)
    (q' : Λ) (symbol : Γ) (position : ℕ) :
    foldedSymbol (config.afterWrite q' symbol) position =
      if position = config.head then
        (foldedSymbol config position).write config.side symbol
      else foldedSymbol config position := by
  by_cases hposition : position = config.head
  · subst position
    simp only [foldedSymbol, Folded.Config.afterWrite, ite_eq_left]
    rw [Folded.symbolsAt_write_active]
    cases config.side <;> rfl
  · simp only [foldedSymbol, Folded.Config.afterWrite,
      ite_eq_right hposition]
    rw [Folded.symbolsAt_write_inactive _ _ _ hposition]

private theorem physicalMove_apply (side : Side) (head : ℕ) (dir : Turing.Dir) :
    (physicalMove side (decide (head = 0)) dir).apply head =
      Folded.moveHead side (decide (head = 0)) head dir := by
  cases side <;> cases dir <;> by_cases hhead : head = 0 <;>
    subst_vars <;>
    simp_all [physicalMove, Folded.moveHead,
      Folded.Side.isInward,
      Folded.Side.isOutward, Move.apply]

variable [DecidableEq Λ]

private theorem nextID_toID (M : Turing.TM0.Machine Γ Λ) (config : Folded.Config Γ Λ)
    {next : Folded.Config Γ Λ} (h : Folded.Config.step M config = some next) :
    (machine M).nextID (toID config) = toID next := by
  cases hm : M config.source.q config.source.Tape.head with
  | none => simp [Folded.Config.step, hm] at h
  | some action =>
      obtain ⟨q', stmt⟩ := action
      cases stmt with
      | write symbol =>
          simp only [Folded.Config.step, hm, Option.some.injEq] at h
          subst next
          apply Config.ext
          · funext p
            simp only [OneMachine.nextID, toID, machine, typedStep,
              foldedSymbol_active_head, hm, reduceCtorEq, ↓reduceIte]
            rw [foldedSymbol_afterWrite]
            split_ifs with hp <;> simp [hp]
          · simp [OneMachine.nextID, toID, machine, typedStep,
              foldedSymbol_active_head, hm, Move.apply, Folded.Config.afterWrite]
          · simp [OneMachine.nextID, toID, machine, typedStep,
              foldedSymbol_active_head, hm, Folded.Config.afterWrite]
      | move dir =>
          simp only [Folded.Config.step, hm, Option.some.injEq] at h
          subst next
          apply Config.ext
          · funext p
            by_cases hp : p = config.head <;>
              simp [OneMachine.nextID, toID, machine, typedStep,
                foldedSymbol_active_head, hm, foldedSymbol_afterMove, hp]
          · simp only [OneMachine.nextID, toID, machine, typedStep,
              foldedSymbol_active_head, hm, reduceCtorEq, ↓reduceIte]
            exact physicalMove_apply config.side config.head dir
          · simp only [OneMachine.nextID, toID, machine, typedStep,
              foldedSymbol_active_head, hm, reduceCtorEq, ↓reduceIte]
            rfl

private theorem configStep_respects_transition (M : Turing.TM0.Machine Γ Λ) :
    StateTransition.Respects (Folded.Config.step M) (transition (machine M))
      (fun c d => toID c = d) := by
  intro config target htarget
  subst target
  cases hs : Folded.Config.step M config with
  | none =>
      cases hm : M config.source.q config.source.Tape.head with
      | none => simp [transition, OneMachine.nextID, toID, machine, typedStep,
          foldedSymbol_active_head, hm]
      | some action => cases action with
        | mk q stmt => cases stmt <;> simp [Folded.Config.step, hm] at hs
  | some next =>
      refine ⟨toID next, rfl, Relation.TransGen.single ?_⟩
      unfold transition
      rw [nextID_toID M config hs]
      simp [toID, machine]

omit [DecidableEq Λ] in
private theorem configStep_respects_tm0Step (M : Turing.TM0.Machine Γ Λ) :
    StateTransition.Respects (Folded.Config.step M) (Turing.TM0.step M)
      (fun c d => c.source = d) := by
  intro config source heq
  subst source
  cases hm : M config.source.q config.source.Tape.head with
  | none => simp [Folded.Config.step, Turing.TM0.step, hm]
  | some action =>
      obtain ⟨q', stmt⟩ := action
      cases stmt <;> simp only [Folded.Config.step, hm]
      all_goals exact ⟨_, rfl, Relation.TransGen.single
        (Folded.Config.step_source (by simp [Folded.Config.step, hm]))⟩

private theorem halts_iff_tm0_eval_dom (M : Turing.TM0.Machine Γ Λ) (source : List Γ) :
    Halts (machine M) (foldedInput source) ↔ (Turing.TM0.eval M source).Dom := by
  rw [← transition_eval_dom_iff_halts, Turing.TM0.eval, Part.map_Dom]
  rw [StateTransition.tr_eval_dom (configStep_respects_transition M)
      (initialID_eq_toID M source).symm]
  exact (StateTransition.tr_eval_dom (configStep_respects_tm0Step M)
    (a₁ := Folded.Config.initial (Λ := Λ) source) rfl).symm

end Folding

section Certificates

variable {S Q : Type} [Fintype S] [Fintype Q]

private theorem primrec_toWangTile {α : Type} [Primcodable α]
    {west east : α → ℕ} {history : α → History S Q}
    (hw : Primrec west) (he : Primrec east) (hh : Primrec history) (row nextRow : ℕ) :
    Primrec (fun a => toWangTile (west a) (east a) row nextRow (history a)) := by
  apply WangTile.primrec_mk
  · exact (Primrec.dom_finite fun t : History S Q =>
      taggedTripleCellColor nextRow t.nextLeft t.nextCenter t.nextRight).comp hh
  · exact (Primrec.dom_finite fun t : History S Q =>
      taggedTripleCellColor row t.prevLeft t.prevCenter t.prevRight).comp hh
  · exact Primrec.encode.comp (hw.pair ((Primrec.dom_finite fun t : History S Q =>
      (row, (t.prevLeft, t.prevCenter), t.nextLeft, t.nextCenter)).comp hh))
  · exact Primrec.encode.comp (he.pair ((Primrec.dom_finite fun t : History S Q =>
      (row, (t.prevCenter, t.prevRight), t.nextCenter, t.nextRight)).comp hh))

variable [DecidableEq Q]

private theorem primrec_historyTile_zero [Primcodable S] (M : OneMachine S Q)
    (hstart : M.start ≠ M.halt) :
    Primrec (fun p : List S × ℕ => historyTile M p.1 0 p.2) := by
  let : Primcodable Q := Primcodable.ofEquiv _ (Fintype.equivFin _)
  have htape : Primrec (fun p : List S × ℕ => tape M.blank p.1 p.2) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const M.blank)
  have hzero : PrimrecPred (fun p : List S × ℕ => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hcell : Primrec (fun p : List S × ℕ => (initialID M p.1).cellAt p.2) :=
    (Primrec.ite hzero ((Primrec.dom_finite fun a : S => Cell.head M.start a).comp htape)
      ((Primrec.dom_finite (Cell.plain (Q := Q))).comp htape)).of_eq fun _ => rfl
  have hread := htape.comp (Primrec.pair Primrec.id (Primrec.const 0))
  have hwrite := (Primrec.dom_finite fun a : S => (M.step M.start a).write).comp hread
  have hstate := (Primrec.dom_finite fun a : S => (M.step M.start a).state).comp hread
  have hhead := (Primrec.dom_finite fun a : S => (M.step M.start a).move.apply 0).comp hread
  have hnextTape := Primrec.ite hzero (hwrite.comp Primrec.fst) htape
  have hnext : Primrec (fun p : List S × ℕ => (M.nextID (initialID M p.1)).cellAt p.2) := by
    have h := Primrec.ite (Primrec.eq.comp Primrec.snd (hhead.comp Primrec.fst))
      ((Primrec.dom_finite fun p : Q × S => Cell.head p.1 p.2).comp
        (Primrec.pair (hstate.comp Primrec.fst) hnextTape))
      ((Primrec.dom_finite (Cell.plain (Q := Q))).comp hnextTape)
    exact h.of_eq fun p => by
      simp only [OneMachine.nextID, initialID, hstart, ↓reduceIte, Config.cellAt]
      rfl
  have hleft (cfg : List S → Config S Q)
      (hc : Primrec (fun p : List S × ℕ => (cfg p.1).cellAt p.2)) :
      Primrec (fun p : List S × ℕ => (cfg p.1).cellAtLeft p.2) :=
    (Primrec.ite hzero (Primrec.const Cell.boundary)
      (hc.comp (Primrec.pair Primrec.fst (Primrec.pred.comp Primrec.snd)))).of_eq
      fun ⟨_, p⟩ => by cases p <;> rfl
  have hsucc : Primrec (fun p : List S × ℕ => (p.1, p.2 + 1)) :=
    Primrec.pair Primrec.fst (Primrec.succ.comp Primrec.snd)
  have hmk : Primrec (fun (a, b, c, d, e, f) =>
      (History.mk a b c d e f : History S Q)) := Primrec.dom_finite _
  exact (hmk.comp ((hleft (initialID M) hcell).pair (hcell.pair ((hcell.comp hsucc).pair
    ((hleft (fun input => M.nextID (initialID M input)) hnext).pair
      (hnext.pair (hnext.comp hsucc))))))).of_eq fun _ => rfl

variable [DecidableEq S]

private theorem primrec_instance [Primcodable S] (M : OneMachine S Q)
    (hstart : M.start ≠ M.halt) :
    Primrec (fun input => (SeededInstance.mk (tiles M input) (seed M input))) := by
  have htail : Primrec (fun input : List S => tailPosition input) :=
    Primrec.nat_add.comp Primrec.list_length (Primrec.const 3)
  have hhistory := primrec_historyTile_zero M hstart
  have hprefix : Primrec₂ (fun input : List S => fun p : ℕ =>
      toWangTile p (p + 1) initialRowTag normalRowTag (historyTile M input 0 p)) :=
    (primrec_toWangTile Primrec.snd (Primrec.succ.comp Primrec.snd)
      hhistory initialRowTag normalRowTag).to₂
  have hend := primrec_toWangTile htail htail
    (hhistory.comp (Primrec.pair Primrec.id htail)) initialRowTag normalRowTag
  have hinitialTile : Primrec₂ (initialTile M) :=
    (Primrec.ite (Primrec.nat_lt.comp Primrec.snd (htail.comp Primrec.fst))
      hprefix (hend.comp Primrec.fst)).to₂
  have hinitial : Primrec (initialTiles M) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp htail)) hinitialTile
  have htiles : Primrec (tiles M) :=
    Primrec.list_append.comp hinitial (Primrec.const (normalTiles M))
  have hseed : Primrec (seed M) :=
    (primrec_toWangTile (Primrec.const 0) (Primrec.const 1)
      (hhistory.comp (Primrec.pair Primrec.id (Primrec.const 0)))
        initialRowTag normalRowTag).of_eq fun input => by
      simp [seed, initialTile, tailPosition]
  exact SeededInstance.primrec₂_mk.comp htiles hseed

end Certificates

public section

variable {Γ Λ : Type} [Fintype Γ] [Fintype Λ]
  [Inhabited Γ] [Inhabited Λ] [DecidableEq Γ] [DecidableEq Λ]

/-- The finite seeded quadrant instance recording `M` on `input`. The two-sided tape is
folded at the origin, and the bottom row fixes the entire finite input and blank tail. -/
noncomputable def seededInstance (M : Turing.TM0.Machine Γ Λ) (input : List Γ) :
    SeededInstance :=
  ⟨tiles (machine M) (foldedInput input), seed (machine M) (foldedInput input)⟩

/-- A seeded quadrant can be tiled by the machine's history palette exactly when the
finite `TM0` machine does not halt on the supplied input. This is a seeded quadrant result. -/
theorem tilesQuadrant_seededInstance_iff (M : Turing.TM0.Machine Γ Λ) (input : List Γ) :
    TilesQuadrant (seededInstance M input) ↔ ¬ (Turing.TM0.eval M input).Dom := by
  unfold seededInstance
  rw [tilesQuadrant_iff_not_halts, halts_iff_tm0_eval_dom]

/-- For each fixed finite machine, constructing the seeded quadrant palette is primitive
recursive in the input word. The state and symbol enumerations are fixed constants. -/
theorem primrec_seededInstance [Primcodable Γ] (M : Turing.TM0.Machine Γ Λ) :
    Primrec (seededInstance M) := by
  let : Primcodable (TapeSymbol Γ) := Primcodable.ofEquiv _ (Fintype.equivFin _)
  have hf : Primrec (foldedInput (Γ := Γ)) :=
    Primrec.list_cons.comp
      ((Primrec.dom_finite fun a : Γ => (TapeSymbol.mk true default a)).comp Primrec.list_headI)
      (Primrec.list_map Primrec.list_tail
        ((Primrec.dom_finite fun a : Γ => TapeSymbol.mk false default a).comp Primrec.snd).to₂)
  exact ((primrec_instance (machine M) (by simp [machine])).comp hf).of_eq fun _ => rfl

end

end Cslib.WangTile.OfTM0
