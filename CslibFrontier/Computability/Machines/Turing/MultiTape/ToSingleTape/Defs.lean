/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
public import CslibFrontier.Computability.Machines.Turing.SingleTape.Sweep

/-!
# Simulating multi-tape machines on one tape: the machine

A multi-tape machine `tm : Turing.MultiTapeTM k Symbol State` with a read-only input tape, `k`
work tapes and a write-only output tape is simulated by a single-tape machine
`Turing.MultiTapeTM.toSingleTape tm` over the alphabet `Symbol ⊕ Cell k Symbol`. Plain symbols
`Sum.inl a` hold the input before the simulation and the output after it.

During the simulation, cell `z` of the single tape holds a `Cell` recording, for each of the
`k + 2` *tracks* (`Track.input`, `Track.work i` and `Track.output`), the symbol at position `z`
and whether that track's head is there. Input position `p` is cell `p - 1`, work-tape position `z`
is cell `z`, and output position `i` is cell `i`. The output's head is the cell after the last
symbol written. Cells `-1` and `|x|`, the two blank ends of the input, are flagged (`clampL`,
`clampR`) because the input head does not move past them, and cell `0` is flagged as the origin.

A simulated step has two parts:

* *collect*: sweep right over the occupied cells and record the symbol under each head;
* one *pass* per track, in the direction that track's head moves, writing the new symbol under the
  head and carrying the head mark one cell along (`passCell`). A pass that carries a mark off the
  end of the occupied cells adds a cell there.

Once the simulated machine halts, a cleanup sweep leaves only the output on the tape, in plain
symbols, with the head on its first cell. The correctness proof is in
`Machines.Turing.MultiTape.ToSingleTape.Correct`.

## Main definitions

* `Turing.MultiTapeTM.ToSingleTape.Track`, `Cell`, `Phase`, `SimState`.
* `Turing.MultiTapeTM.toSingleTape`: the simulating single-tape machine.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace ToSingleTape

variable (k : ℕ) (Symbol State : Type)

/-- The tracks of the single tape: the input, the `k` work tapes and the output. -/
inductive Track
  /-- The read-only input tape. -/
  | input
  /-- Work tape `i`. -/
  | work (i : Fin k)
  /-- The write-only output tape. -/
  | output
  deriving DecidableEq

/-- `Track k` as `Unit ⊕ Fin k ⊕ Unit`, for finiteness. -/
def Track.equivSum : Track k ≃ Unit ⊕ Fin k ⊕ Unit where
  toFun
    | .input => .inl ()
    | .work i => .inr (.inl i)
    | .output => .inr (.inr ())
  invFun
    | .inl () => .input
    | .inr (.inl i) => .work i
    | .inr (.inr ()) => .output
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with ⟨⟩ | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype (Track k) := Fintype.ofEquiv _ (Track.equivSum k).symm

/-- A cell of the single tape: for each track, its symbol and whether its head is here; and
whether this is cell `-1`, cell `|x|` or cell `0`. -/
@[ext] structure Cell where
  /-- The symbol of each track at this cell. -/
  sym : Track k → Option Symbol
  /-- Whether each track's head is at this cell. -/
  mark : Track k → Bool
  /-- Cell `-1`, left of the input: the input head does not move further left. -/
  clampL : Bool
  /-- Cell `|x|`, right of the input: the input head does not move further right. -/
  clampR : Bool
  /-- Cell `0`. -/
  origin : Bool
  deriving DecidableEq

variable {k Symbol State}

/-- `Cell` as a product, for finiteness. -/
def Cell.equivProd : Cell k Symbol ≃
    (Track k → Option Symbol) × (Track k → Bool) × Bool × Bool × Bool where
  toFun c := (c.sym, c.mark, c.clampL, c.clampR, c.origin)
  invFun
    | (s, m, l, r, o) => ⟨s, m, l, r, o⟩

instance [Fintype Symbol] : Fintype (Cell k Symbol) :=
  Fintype.ofEquiv _ Cell.equivProd.symm

instance : Inhabited (Cell k Symbol) := ⟨⟨fun _ => none, fun _ => false, false, false, false⟩⟩

/-- `Action` as a product, for finiteness. -/
def actionEquivProd : Action k Symbol State ≃
    SignType × (Fin k → Option (Option Symbol) × SignType) × Option Symbol × Option State where
  toFun a := (a.inputTape, a.workTapes, a.output, a.state)
  invFun
    | (i, w, o, s) => ⟨i, w, o, s⟩

instance instFintypeAction [Fintype Symbol] [Fintype State] :
    Fintype (Action k Symbol State) :=
  Fintype.ofEquiv _ actionEquivProd.symm

/-- What a track does in a step: the symbol to write under its head, if any, and how its head
moves. The output writes the emitted symbol and moves on; the input never writes. -/
def Track.act (a : Action k Symbol State) : Track k → Option (Option Symbol) × SignType
  | .input => (none, a.inputTape)
  | .work i => a.workTapes i
  | .output => match a.output with
    | none => (none, 0)
    | some s => (some (some s), 1)

/-- The tracks in the order their passes run. -/
def trackList (k : ℕ) : List (Track k) :=
  .input :: (List.finRange k).map .work ++ [.output]

/-- The track after `j` in `trackList k`, if any. -/
def Track.next : Track k → Option (Track k)
  | .input => if h : 0 < k then some (.work ⟨0, h⟩) else some .output
  | .work i => if h : i.val + 1 < k then some (.work ⟨i.val + 1, h⟩) else some .output
  | .output => none

/-- Whether the head of track `j` at cell `c` leaves it when moving by `move`: it moves, and it is
not the input head on the cell it does not move past. -/
def movesOn (j : Track k) (move : SignType) (c : Cell k Symbol) : Bool :=
  decide (move ≠ 0) && !(decide (j = .input) && (if move = 1 then c.clampR else c.clampL))

/-- The rewriting of a cell by the pass of track `j` performing `(write, move)`, carrying the
`pending` head mark from the previous cell. -/
def passCell (j : Track k) (write : Option (Option Symbol)) (move : SignType) (pending : Bool)
    (c : Cell k Symbol) : Bool × Cell k Symbol :=
  if pending then (false, { c with mark := Function.update c.mark j true })
  else if c.mark j then
    let c' := { c with sym := Function.update c.sym j (write.elim (c.sym j) id) }
    if movesOn j move c then (true, { c' with mark := Function.update c.mark j false })
    else (false, c')
  else (false, c)

/-- The cell added beyond the occupied ones when a pass carries the mark of track `j` there. -/
def newCell (j : Track k) : Cell k Symbol :=
  ⟨fun _ => none, fun j' => decide (j' = j), false, false, false⟩

/-- The symbols under the heads, updated by cell `c`. -/
def collectCell (reads : Track k → Option (Option Symbol)) (c : Cell k Symbol) :
    Track k → Option (Option Symbol) :=
  fun j => if c.mark j then some (c.sym j) else reads j

/-- The phases between sweeps: collecting the symbols under the heads, the pass of a track, and
the final cleanup. -/
inductive Phase (k : ℕ) (Symbol State : Type)
  /-- Collect the symbols under the heads in state `q`. -/
  | collect (q : State)
  /-- The pass of track `j` for the action `a`. -/
  | pass (a : Action k Symbol State) (j : Track k)
  /-- Leave only the output on the tape. -/
  | clean

/-- The states of the simulating machine. -/
inductive SimState (k : ℕ) (Symbol State : Type)
  /-- At cell `0` initially: step left, leaving the cell as it is. -/
  | init₀
  /-- At cell `-1`: write its cell and step right. -/
  | init₁
  /-- At an input cell (`first` for cell `0`): write its cell and step right. -/
  | init₂ (first : Bool)
  /-- Walk left to the left end, then enter `next`. -/
  | toL (next : Phase k Symbol State)
  /-- Walk right to the right end, then enter `next`. -/
  | toR (next : Phase k Symbol State)
  /-- Collect the symbols under the heads. -/
  | collect (q : State) (reads : Track k → Option (Option Symbol))
  /-- The pass of track `j` for `a`, rightwards or leftwards. -/
  | passR (a : Action k Symbol State) (j : Track k) (pending : Bool)
  | passL (a : Action k Symbol State) (j : Track k) (pending : Bool)
  /-- Convert the cells to the output, leftwards; `passed` once the origin is behind. -/
  | clean₁ (passed : Bool)
  /-- Walk right over the erased cells to the origin. -/
  | clean₂

/-- `Phase` into a sum type, for finiteness. -/
def Phase.enc : Phase k Symbol State → State ⊕ (Action k Symbol State × Track k) ⊕ Unit
  | .collect q => .inl q
  | .pass a j => .inr (.inl (a, j))
  | .clean => .inr (.inr ())

lemma Phase.enc_injective : Function.Injective (Phase.enc (k := k) (Symbol := Symbol)
    (State := State)) := by
  intro p q h
  cases p <;> cases q <;> simp_all [Phase.enc]

/-- `SimState` into a sum type, for finiteness. -/
def SimState.enc : SimState k Symbol State →
    (Unit ⊕ Unit ⊕ Bool) ⊕ (Phase k Symbol State ⊕ Phase k Symbol State) ⊕
      (State × (Track k → Option (Option Symbol))) ⊕
      ((Action k Symbol State × Track k × Bool) ⊕ (Action k Symbol State × Track k × Bool)) ⊕
      (Bool ⊕ Unit)
  | .init₀ => .inl (.inl ())
  | .init₁ => .inl (.inr (.inl ()))
  | .init₂ b => .inl (.inr (.inr b))
  | .toL p => .inr (.inl (.inl p))
  | .toR p => .inr (.inl (.inr p))
  | .collect q r => .inr (.inr (.inl (q, r)))
  | .passR a j b => .inr (.inr (.inr (.inl (.inl (a, j, b)))))
  | .passL a j b => .inr (.inr (.inr (.inl (.inr (a, j, b)))))
  | .clean₁ b => .inr (.inr (.inr (.inr (.inl b))))
  | .clean₂ => .inr (.inr (.inr (.inr (.inr ()))))

lemma SimState.enc_injective : Function.Injective (SimState.enc (k := k) (Symbol := Symbol)
    (State := State)) := by
  intro p q h
  cases p <;> cases q <;> simp_all [SimState.enc]

instance [Finite Symbol] [Finite State] : Finite (Phase k Symbol State) := by
  classical
  have := Fintype.ofFinite Symbol
  have := Fintype.ofFinite State
  exact .of_injective _ Phase.enc_injective

instance [Finite Symbol] [Finite State] : Finite (SimState k Symbol State) := by
  classical
  have := Fintype.ofFinite Symbol
  have := Fintype.ofFinite State
  have := Fintype.ofFinite (Phase k Symbol State)
  exact .of_injective _ SimState.enc_injective

/-- Whether the pass of `j` for `a` runs leftwards. -/
def passesLeft (a : Action k Symbol State) (j : Track k) : Bool := (j.act a).2 = -1

/-- The state in which to start `next`, standing on the left end of the occupied cells. -/
def fromLeft : Phase k Symbol State → SimState k Symbol State
  | .collect q => .collect q fun _ => none
  | .pass a j => if passesLeft a j then .toR (.pass a j) else .passR a j false
  | .clean => .toR .clean

/-- The state in which to start `next`, standing on the right end of the occupied cells. -/
def fromRight : Phase k Symbol State → SimState k Symbol State
  | .collect q => .toL (.collect q)
  | .pass a j => if passesLeft a j then .passL a j false else .toL (.pass a j)
  | .clean => .clean₁ false

/-- The phase after the pass of `j` for `a`: the next track's pass, then the next step or the
cleanup. -/
def afterPass (a : Action k Symbol State) (j : Track k) : Phase k Symbol State :=
  match j.next with
  | some j' => .pass a j'
  | none => match a.state with
    | some q => .collect q
    | none => .clean

/-- The output cell of a converted cell: its output symbol, as a plain symbol. -/
def convert (c : Cell k Symbol) : Option (Symbol ⊕ Cell k Symbol) := (c.sym .output).map .inl

section Machine

variable [Fintype Symbol] [Fintype State]

/-- A step of the single-tape machine, writing `w`, moving `d` and going to `q`. -/
def simStep (w : Option (Symbol ⊕ Cell k Symbol)) (d : Option _root_.Turing.Dir)
    (q : Option (SimState k Symbol State)) :
    Cslib.Turing.SingleTapeTM.Stmt (Symbol ⊕ Cell k Symbol) × Option (SimState k Symbol State) :=
  (⟨w, d⟩, q)

/-- The cell `z` of the initial simulated configuration, for `z = -1` (`left`), an input cell
holding `a`, or cell `|x|` (`a = none`, not `left`); `first` for cell `0`. -/
def initCell (left first : Bool) (a : Option Symbol) : Cell k Symbol :=
  ⟨fun j => if j = .input then a else none, fun _ => first, left, !left && a.isNone, first⟩

variable (tm : MultiTapeTM k Symbol State)

/-- The transition table of the simulating machine. -/
noncomputable def simTr :
    SimState k Symbol State → Option (Symbol ⊕ Cell k Symbol) →
      Cslib.Turing.SingleTapeTM.Stmt (Symbol ⊕ Cell k Symbol) × Option (SimState k Symbol State)
  | .init₀, a => simStep a (some .left) (some .init₁)
  | .init₁, _ => simStep (some (.inr (initCell true false none))) (some .right) (some (.init₂ true))
  | .init₂ first, some (.inl a) =>
    simStep (some (.inr (initCell false first (some a)))) (some .right) (some (.init₂ false))
  | .init₂ first, _ =>
    simStep (some (.inr (initCell false first none))) none (some (fromRight (.collect tm.q₀)))
  | .toL next, some (.inr c) => simStep (some (.inr c)) (some .left) (some (.toL next))
  | .toL next, _ => simStep none (some .right) (some (fromLeft next))
  | .toR next, some (.inr c) => simStep (some (.inr c)) (some .right) (some (.toR next))
  | .toR next, _ => simStep none (some .left) (some (fromRight next))
  | .collect q reads, some (.inr c) =>
    simStep (some (.inr c)) (some .right) (some (.collect q (collectCell reads c)))
  | .collect q reads, _ =>
    let a := tm.tr q ((reads .input).getD none) fun i => (reads (.work i)).getD none
    simStep none (some .left) (some (fromRight (.pass a .input)))
  | .passR a j pending, some (.inr c) =>
    simStep (some (.inr (passCell j (j.act a).1 (j.act a).2 pending c).2)) (some .right)
      (some (.passR a j (passCell j (j.act a).1 (j.act a).2 pending c).1))
  | .passR a j pending, _ =>
    if pending then simStep (some (.inr (newCell j))) none (some (fromRight (afterPass a j)))
    else simStep none (some .left) (some (fromRight (afterPass a j)))
  | .passL a j pending, some (.inr c) =>
    simStep (some (.inr (passCell j (j.act a).1 (j.act a).2 pending c).2)) (some .left)
      (some (.passL a j (passCell j (j.act a).1 (j.act a).2 pending c).1))
  | .passL a j pending, _ =>
    if pending then simStep (some (.inr (newCell j))) none (some (fromLeft (afterPass a j)))
    else simStep none (some .right) (some (fromLeft (afterPass a j)))
  | .clean₁ passed, some (.inr c) =>
    if passed then simStep none (some .left) (some (.clean₁ true))
    else if c.origin then simStep (some (.inr c)) (some .left) (some (.clean₁ true))
    else simStep (convert c) (some .left) (some (.clean₁ false))
  | .clean₁ _, _ => simStep none (some .right) (some .clean₂)
  | .clean₂, some (.inr c) => simStep (convert c) none none
  | .clean₂, _ => simStep none (some .right) (some .clean₂)

end Machine

end ToSingleTape

open ToSingleTape in
/-- The single-tape machine simulating `tm`. -/
noncomputable def toSingleTape {k : ℕ} {Symbol State : Type} [Fintype Symbol] [Fintype State]
    (tm : MultiTapeTM k Symbol State) :
    Cslib.Turing.SingleTapeTM (Symbol ⊕ Cell k Symbol) where
  State := SimState k Symbol State
  stateFintype := Fintype.ofFinite _
  q₀ := .init₀
  tr := simTr tm

end Turing.MultiTapeTM
