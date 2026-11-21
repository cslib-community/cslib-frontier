/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Zones
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum

/-!
# The Hennie–Stearns machine

`Turing.MultiTapeTM.hennieStearns tm` simulates a machine `tm` with `k` work tapes on two work
tapes, keeping `tm`'s input and output tapes as its own. Its alphabet is `Symbol ⊕ ACell ⊕ BCell`.

* Work tape `0` holds the `k` simulated work tapes as zoned tracks (`ZTrack`), folded at cell `0`:
  cell `0` holds the symbol under each head, and cell `n ≥ 1` holds, for each track, the zone
  cells at distance `n` on the right and on the left of its head. Zone `j` is cells
  `2 ^ (j + 1) - 1, …, 2 ^ (j + 2) - 2`; its first cell is flagged `start` and its first half
  `inner`. The zones created so far are followed by blank cells.
* Work tape `1` is scratch space: a `home` cell at `0` and then the lists of symbols a move
  gathers, or the ruler that measures a new zone.

A simulated step reads cell `0` and the input, looks up the action of `tm`, writes cell `0`, moves
the input head and emits the output symbol in one step. Then each moving track takes its move
(`ZTrack.move`). A move to side `s` scans for the first cell holding a symbol on side `s` (the
start of the level `j` of the move) and marks it, gathers the symbols of the other side up to
zone `j` with the center, gathers those of side `s`, and writes both back spread over the zones,
each in one sweep out from cell `0` and back. If no zone holds a symbol on side `s`, the next zone
is first created half full of blanks, measured with a ruler on work tape `1`.

## Main definitions

* `Turing.MultiTapeTM.HennieStearns.ACell`, `BCell`, `HState`.
* `Turing.MultiTapeTM.hennieStearns`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

variable (k : ℕ) (Symbol State : Type)

/-- A cell of work tape `0`. -/
@[ext] structure ACell where
  /-- Cell `0`. -/
  center : Bool
  /-- The first cell of a zone. -/
  start : Bool
  /-- A cell in the first half of its zone. -/
  inner : Bool
  /-- The first cell of the zone of the current move. -/
  trig : Bool
  /-- For each track, the symbol on the right (or the center symbol on cell `0`), if any. -/
  r : Fin k → Option (Option Symbol)
  /-- For each track, the symbol on the left, if any. -/
  l : Fin k → Option (Option Symbol)
  deriving DecidableEq

/-- A cell of work tape `1`. -/
@[ext] structure BCell where
  /-- An element of the list gathered from the side of the move. -/
  s : Option (Option Symbol)
  /-- An element of the list gathered from the other side. -/
  d : Option (Option Symbol)
  /-- A ruler mark. -/
  mark : Bool
  /-- The ruler mark of the first cell of the outer half. -/
  outer : Bool
  /-- The home cell. -/
  home : Bool
  deriving DecidableEq

variable {k Symbol State}

/-- `ACell` as a product, for finiteness. -/
def ACell.equivProd : ACell k Symbol ≃ Bool × Bool × Bool × Bool ×
    (Fin k → Option (Option Symbol)) × (Fin k → Option (Option Symbol)) where
  toFun c := (c.center, c.start, c.inner, c.trig, c.r, c.l)
  invFun
    | (a, b, c, d, e, f) => ⟨a, b, c, d, e, f⟩

/-- `BCell` as a product, for finiteness. -/
def BCell.equivProd : BCell Symbol ≃
    Option (Option Symbol) × Option (Option Symbol) × Bool × Bool × Bool where
  toFun c := (c.s, c.d, c.mark, c.outer, c.home)
  invFun
    | (a, b, c, d, e) => ⟨a, b, c, d, e⟩

instance [Fintype Symbol] : Fintype (ACell k Symbol) := Fintype.ofEquiv _ ACell.equivProd.symm
instance [Fintype Symbol] : Fintype (BCell Symbol) := Fintype.ofEquiv _ BCell.equivProd.symm

/-- The part of a cell for track `i` on side `s`. -/
def ACell.part (c : ACell k Symbol) (s : Side) (i : Fin k) : Option (Option Symbol) :=
  match s with
  | .R => c.r i
  | .L => c.l i

/-- The cell with the part for track `i` on side `s` replaced. -/
def ACell.setPart (c : ACell k Symbol) (s : Side) (i : Fin k) (v : Option (Option Symbol)) :
    ACell k Symbol :=
  match s with
  | .R => { c with r := Function.update c.r i v }
  | .L => { c with l := Function.update c.l i v }

/-- The empty scratch cell. -/
def BCell.empty : BCell Symbol := ⟨none, none, false, false, false⟩

/-- Whether a scratch cell holds nothing. -/
def BCell.isEmpty (b : BCell Symbol) : Bool :=
  b.s.isNone && b.d.isNone && !b.mark && !b.outer && !b.home

/-- A scratch cell as written: blank when empty. -/
def bWrite (b : BCell Symbol) : Option (Symbol ⊕ ACell k Symbol ⊕ BCell Symbol) :=
  if b.isEmpty then none else some (.inr (.inr b))

/-- What comes after walking home. -/
inductive Next
  | gatherD | gatherS | writeS | writeD | done | scan | crWalk
  deriving DecidableEq

/-- The phases of a move of one track. -/
inductive Phase
  /-- Look for the first cell with a symbol on the side of the move. -/
  | scan
  /-- Walk work tape `0` home, then work tape `1`. -/
  | back (next : Next)
  /-- Walk work tape `1` home. -/
  | backB (next : Next)
  /-- Gather the other side, with the center. -/
  | gatherD (seen : Bool)
  /-- Gather the side of the move. -/
  | gatherS (seen : Bool)
  /-- Spread the side of the move, with the center. -/
  | writeS (seen : Bool)
  /-- Spread the other side. -/
  | writeD (seen : Bool)
  /-- Lay the ruler for a new zone, walking left over the zones. -/
  | cr₁ (pend flagged : Bool)
  /-- The last ruler mark. -/
  | cr₂ (pend : Bool)
  /-- Walk to the end of the zones. -/
  | crWalk
  /-- Write the new zone along the ruler. -/
  | cr₃ (first outer : Bool)
  deriving DecidableEq

/-- The states of the Hennie–Stearns machine. -/
inductive HState (k : ℕ) (State : Type)
  /-- Write the center cell and the home cell. -/
  | init
  /-- Simulate a step of `tm` in state `q`. -/
  | apply (q : State)
  /-- The move of track `i`, in a step leading to `q` with head moves `mv`. -/
  | op (q : State) (mv : Fin k → SignType) (i : Fin k) (ph : Phase)

/-- `Next` into a sum type. -/
def Next.enc : Next → Fin 7
  | .gatherD => 0 | .gatherS => 1 | .writeS => 2 | .writeD => 3 | .done => 4 | .scan => 5
  | .crWalk => 6

lemma Next.enc_injective : Function.Injective Next.enc := by
  intro a b h; cases a <;> cases b <;> simp_all [Next.enc]

instance : Finite Next := .of_injective _ Next.enc_injective

/-- `Phase` into a tuple, for finiteness. -/
def Phase.enc : Phase → Fin 11 × Bool × Bool × Fin 7
  | .scan => (0, false, false, 0)
  | .back n => (1, false, false, n.enc)
  | .backB n => (2, false, false, n.enc)
  | .gatherD b => (3, b, false, 0)
  | .gatherS b => (4, b, false, 0)
  | .writeS b => (5, b, false, 0)
  | .writeD b => (6, b, false, 0)
  | .cr₁ a b => (7, a, b, 0)
  | .cr₂ b => (8, b, false, 0)
  | .crWalk => (9, false, false, 0)
  | .cr₃ a b => (10, a, b, 0)

lemma Phase.enc_injective : Function.Injective Phase.enc := by
  intro a b h
  cases a <;> cases b <;> simp only [Phase.enc, Prod.mk.injEq, true_and, and_true] at h <;>
    first | rfl | (congr 1; exact Next.enc_injective h) | simp_all

instance : Finite Phase := .of_injective _ Phase.enc_injective

/-- `HState` into a sum type. -/
def HState.enc : HState k State → Unit ⊕ State ⊕ (State × (Fin k → SignType) × Fin k × Phase)
  | .init => .inl ()
  | .apply q => .inr (.inl q)
  | .op q mv i ph => .inr (.inr (q, mv, i, ph))

lemma HState.enc_injective : Function.Injective (HState.enc (k := k) (State := State)) := by
  intro a b h; cases a <;> cases b <;> simp_all [HState.enc]

instance [Finite State] : Finite (HState k State) := by
  classical
  have := Fintype.ofFinite State
  have : Fintype Phase := Fintype.ofFinite _
  exact .of_injective _ HState.enc_injective

/-- The alphabet of the Hennie–Stearns machine. -/
abbrev HSym (k : ℕ) (Symbol : Type) := Symbol ⊕ ACell k Symbol ⊕ BCell Symbol

/-- Read work tape `0`: a cell, or `none` for a blank. -/
def readA : Option (HSym k Symbol) → Option (ACell k Symbol)
  | some (.inr (.inl c)) => some c
  | _ => none

/-- Read work tape `1`. -/
def readB : Option (HSym k Symbol) → BCell Symbol
  | some (.inr (.inr b)) => b
  | _ => BCell.empty

/-- Read the input tape. -/
def readIn : Option (HSym k Symbol) → Option Symbol
  | some (.inl a) => some a
  | _ => none

/-- An action on the two work tapes only. -/
def act (wA : Option (Option (HSym k Symbol))) (mA : SignType)
    (wB : Option (Option (HSym k Symbol))) (mB : SignType) (q : Option (HState k State)) :
    Action 2 (HSym k Symbol) (HState k State) :=
  ⟨0, ![(wA, mA), (wB, mB)], none, q⟩

/-- The first track at or after `i` whose head moves. -/
def nextMoving (mv : Fin k → SignType) (i : ℕ) : Option (Fin k) :=
  ((List.finRange k).filter fun j => i ≤ j.val ∧ mv j ≠ 0).head?

/-- The side of the move of track `i`. -/
def srcSide (mv : Fin k → SignType) (i : Fin k) : Side := if mv i = 1 then .R else .L

/-- The cells written by `cr₃`: a zone cell half full of blanks. -/
def newZoneCell (first inner : Bool) : ACell k Symbol :=
  ⟨false, first, inner, false, fun _ => if inner then some none else none,
    fun _ => if inner then some none else none⟩

/-- The center cell of the initial configuration. -/
def initCenter : ACell k Symbol := ⟨true, false, false, false, fun _ => some none, fun _ => none⟩

/-- The home cell. -/
def homeCell : BCell Symbol := ⟨none, none, false, false, true⟩

variable (tm : MultiTapeTM k Symbol State)

/-- The state after the move of track `i`: the next moving track, or the next step. -/
def afterOp (q : State) (mv : Fin k → SignType) (i : Fin k) : HState k State :=
  match nextMoving mv (i.val + 1) with
  | some j => .op q mv j .scan
  | none => .apply q

/-- The transitions of a move of track `i` to side `s` (`o` is the other side). -/
def opTr (q : State) (mv : Fin k → SignType) (i : Fin k) (ph : Phase)
    (a : Option (ACell k Symbol)) (b : BCell Symbol) : Action 2 (HSym k Symbol) (HState k State) :=
  let s := srcSide mv i
  let o := s.other
  let st := fun ph' => some (HState.op q mv i ph')
  let wa := fun c : ACell k Symbol => some (some (.inr (.inl c)))
  match ph, a with
  -- scan
  | .scan, some c =>
    if c.center then act none 1 none 0 (st .scan)
    else if (c.part s i).isSome then
      act (wa { c with trig := true }) (-1) none 0 (st (.back .gatherD))
    else act none 1 none 0 (st .scan)
  | .scan, none => act none (-1) none 0 (st (.cr₁ false false))
  -- walking home
  | .back nx, some c =>
    if c.center then act none 0 none 0 (st (.backB nx)) else act none (-1) none 0 (st (.back nx))
  | .back nx, none => act none (-1) none 0 (st (.back nx))
  | .backB nx, _ =>
    if b.home then
      match nx with
      | .gatherD => act none 0 none 1 (st (.gatherD false))
      | .gatherS => act none 0 none 1 (st (.gatherS false))
      | .writeS => act none 0 none 1 (st (.writeS false))
      | .writeD => act none 0 none 1 (st (.writeD false))
      | .scan => act none 0 none 1 (st .scan)
      | .crWalk => act none 0 none 1 (st .crWalk)
      | .done => act none 0 none 1 (some (afterOp q mv i))
    else act none 0 none (-1) (st (.backB nx))
  -- gathering the other side, with the center
  | .gatherD seen, some c =>
    if c.center then act none 1 (some (bWrite { b with d := c.r i })) 1 (st (.gatherD seen))
    else if seen && c.start then act none (-1) none 0 (st (.back .gatherS))
    else if (c.part o i).isSome then
      act none 1 (some (bWrite { b with d := c.part o i })) 1 (st (.gatherD (seen || c.trig)))
    else act none 1 none 0 (st (.gatherD (seen || c.trig)))
  | .gatherD _, none => act none (-1) none 0 (st (.back .gatherS))
  -- gathering the side of the move
  | .gatherS seen, some c =>
    if c.center then act none 1 none 0 (st (.gatherS seen))
    else if seen && c.start then act none (-1) none 0 (st (.back .writeS))
    else if (c.part s i).isSome then
      act none 1 (some (bWrite { b with s := c.part s i })) 1 (st (.gatherS (seen || c.trig)))
    else act none 1 none 0 (st (.gatherS (seen || c.trig)))
  | .gatherS _, none => act none (-1) none 0 (st (.back .writeS))
  -- spreading the side of the move, with the center
  | .writeS seen, some c =>
    if c.center then
      act (wa { c with r := Function.update c.r i b.s }) 1 (some (bWrite { b with s := none })) 1
        (st (.writeS seen))
    else if seen && c.start then act none (-1) none 0 (st (.back .writeD))
    else
      let seen' := seen || c.trig
      if (if seen' then b.s.isSome else c.inner) then
        act (wa (c.setPart s i b.s)) 1 (some (bWrite { b with s := none })) 1 (st (.writeS seen'))
      else act (wa (c.setPart s i none)) 1 none 0 (st (.writeS seen'))
  | .writeS _, none => act none (-1) none 0 (st (.back .writeD))
  -- spreading the other side
  | .writeD seen, some c =>
    if c.center then act none 1 none 0 (st (.writeD seen))
    else if seen && c.start then act none (-1) none 0 (st (.back .done))
    else
      let seen' := seen || c.trig
      if (if seen' then b.d.isSome else c.inner) then
        act (wa ({ c with trig := false }.setPart o i b.d)) 1 (some (bWrite { b with d := none }))
          1 (st (.writeD seen'))
      else act (wa ({ c with trig := false }.setPart o i none)) 1 none 0 (st (.writeD seen'))
  | .writeD _, none => act none (-1) none 0 (st (.back .done))
  -- creating a zone
  | .cr₁ pend flagged, some c =>
    let flagged' := flagged || pend
    let pend' := !flagged' && (c.start || c.center)
    if c.center then
      act none 0 (some (bWrite { BCell.empty with mark := true, outer := pend })) 1
        (st (.cr₂ pend'))
    else act none (-1) (some (bWrite { BCell.empty with mark := true, outer := pend })) 1
      (st (.cr₁ pend' flagged'))
  | .cr₁ pend flagged, none => act none (-1) none 0 (st (.cr₁ pend flagged))
  | .cr₂ pend, _ =>
    act none 0 (some (bWrite { BCell.empty with mark := true, outer := pend })) 1
      (st (.backB .crWalk))
  | .crWalk, some _ => act none 1 none 0 (st .crWalk)
  | .crWalk, none => act none 0 none 0 (st (.cr₃ true false))
  | .cr₃ first outer, _ =>
    if b.mark then
      let outer' := outer || b.outer
      act (wa (newZoneCell first !outer')) 1 (some none) 1 (st (.cr₃ false outer'))
    else act none (-1) none 0 (st (.back .scan))

/-- The transition table of the Hennie–Stearns machine. -/
noncomputable def hsTr (tm : MultiTapeTM k Symbol State) :
    HState k State → Option (HSym k Symbol) → (Fin 2 → Option (HSym k Symbol)) →
      Action 2 (HSym k Symbol) (HState k State)
  | .init, _, _ =>
    act (some (some (.inr (.inl initCenter)))) 0 (some (some (.inr (.inr homeCell)))) 1
      (some (.apply tm.q₀))
  | .apply q, inp, w =>
    match readA (w 0) with
    | some c =>
      let a := tm.tr q (readIn inp) fun i => (c.r i).getD none
      let c' := { c with r := fun i => match (a.workTapes i).1 with
        | none => c.r i
        | some v => some v }
      let mv := fun i => (a.workTapes i).2
      ⟨a.inputTape, ![(some (some (.inr (.inl c'))), 0), (none, 0)], a.output.map .inl,
        match a.state with
        | none => none
        | some q' => some (match nextMoving mv 0 with
          | some i => .op q' mv i .scan
          | none => .apply q')⟩
    | none => act none 0 none 0 none
  | .op q mv i ph, _, w => opTr q mv i ph (readA (w 0)) (readB (w 1))

end HennieStearns

open HennieStearns in
/-- **The Hennie–Stearns machine**: `tm` simulated on two work tapes. -/
noncomputable def hennieStearns {k : ℕ} {Symbol State : Type}
    (tm : MultiTapeTM k Symbol State) : MultiTapeTM 2 (HSym k Symbol) (HState k State) :=
  ofTr .init (hsTr tm)

end Turing.MultiTapeTM
