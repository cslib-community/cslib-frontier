/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.NamedStates
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Groups
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.GroupScript
public import CslibFrontier.Computability.Circuit.SlpStep

/-!
# The values of the dealing program and the tables of its steps

The dealing program of [AnthropicVPVNP2026] (the program `G` in the proof of Theorem J.3) guesses
the states between the blocks, the row data, the numbers of units and the outcomes of the moves of
a plan, computes from them by a straight-line program what the plan does, checks the guesses, and
writes the script of every group. Its values have names (`Name`), which an injective code turns
into paths (`Codes`). The numbers of units and the outcomes (`PlanInput`) are the inputs of the
straight-line program (`SlpTab`), whose steps compute, as digits, which units are current, cut or
given at a slot, how many units every move uses, whether the outcomes are good and the numbers of
units valid, and the group of every party. The operations on digits are steps of the interpreter
that look their results up in tries (`Codes.unaryStep`, `Codes.binaryStep`, `Codes.constStep`).

This file also has the trees of the values that the scripts of the groups read: the flags of a
row (`flagsTree`), the keys of the units of the strings between two base parties
(`Codes.writeKeysTree`, `Codes.readKeysTree`), the comparisons of the two copies of the units
from a base party to itself (`Codes.selfAgreeTree`), and the keys of the new units of a channel
(`Codes.newKeysTree`).

## Main definitions

* `Name`, `PlanName`: the names of the values of the dealing program, in general and for a plan.
* `PlanInput`: the numbers of units at the beginning and the outcomes of the moves.
* `SlpTab`, `SlpTab.conditionGate`: a straight-line program that computes what the dealing
  program needs of a plan, and its steps of the conditions.
* `Codes`: codes of the names, the digits and the row data, and the keys of the cells.
* `Codes.digitTree`, `Codes.unaryStep`, `Codes.binaryStep`, `Codes.constStep`: digits as trees,
  and the operations on them.
* `flagsTree`, `Codes.writeKeysTree`, `Codes.readKeysTree`, `Codes.selfAgreeTree`,
  `Codes.newKeysTree`: the values that the scripts read.

## Main results

* `Codes.digitTree_injective`: digits are determined by their trees.
* `Codes.exec_unaryStep`, `Codes.exec_binaryStep`, `Codes.exec_constStep`: the operations.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54). Ported from the source module `Nc.Dl.Tab` and the values of `Nc.Dl.Run`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Interpreter Interpreter.Tree Cut GroupProgram

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D nI pS mm : ℕ}

/-- The names of the values of the dealing program, for `K` blocks on the tapes `S`, `E` moves
with the channels `N` and the units `U`, and a straight-line program of `pS` steps. -/
inductive Name (K E pS : ℕ) (S N U : Type) where
  /-- The empty value, which the tables of the operations start from. -/
  | empty
  /-- The part `κ` of the input. -/
  | part (κ : Fin K)
  /-- The state `a` between the blocks. -/
  | state (a : Fin (K + 1))
  /-- The flags of the partners of the party `p` in its row on the tape `s`. -/
  | flags (s : Option S) (p : Fin (K + K))
  /-- The row data of the party `p` on the tape `s`. -/
  | rowData (s : Option S) (p : Fin (K + K))
  /-- Whether the row data of `p` on `s` are those of a staircase. -/
  | rowValid (s : Option S) (p : Fin (K + K))
  /-- The keys of the copies at `a` of the units from `a` to `b`. -/
  | writeKeys (a b : Fin (K + K))
  /-- The keys of the copies at `b` of the units from `a` to `b`. -/
  | readKeys (a b : Fin (K + K))
  /-- The comparisons of the two copies of the units from `a` to itself. -/
  | selfAgree (a : Fin (K + K))
  /-- The number of units from `a` to `b`, as a digit. -/
  | countDigit (a b : Fin (K + K))
  /-- The outcome of the channel `ν`, as a digit. -/
  | outcomeDigit (ν : N)
  /-- The keys of the copies of the new units of `ν` at its end `d`. -/
  | newKeys (ν : N) (d : Bool)
  /-- The value of step `k` of the straight-line program. -/
  | gate (k : Fin pS)
  /-- The number of units that the move `x` uses. -/
  | count (x : Fin E)
  /-- A condition: the numbers of units are valid (`none`), or the outcome of a move is good. -/
  | condition (c : Option (Fin E))
  /-- Whether the unit `u` is cut. -/
  | isCut (u : U)
  /-- The contents of the unit `u`. -/
  | content (u : U)
  deriving DecidableEq, Fintype

/-- The names of the values of the dealing program for the moves `M`, with at most `U0` units of a
string at the beginning and at most `U1` units of a channel. -/
abbrev PlanName (S : Type) (M : Moves F (K + K + A') E) (U0 U1 pS : ℕ) : Type :=
  Name K E pS S M.Channel (UnitId (K + K) U0 M.Channel U1)

/-- An argument of the functions of a plan: the numbers of units at the beginning and the outcomes
of the moves. -/
structure PlanInput (M : Moves F (K + K + A') E) (U0 U1 : ℕ) where
  /-- The number of units of the string from a base party to a base party. -/
  counts : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)
  /-- The outcome of a channel. -/
  outcomes : M.Channel → Fin U1

variable {M : Moves F (K + K + A') E}

/-- A straight-line program over the digits `Fin D`, with `nI` inputs and `pS` steps, that computes
from a `PlanInput` what the dealing program needs of the plan `P` and the groups `grp` of the
parties: the input `i` reads the number of units of a pair of base parties or the outcome of a
channel (`input i`), and dedicated steps compute, as `0`/`1`, whether a unit is current in the end,
cut between two groups, or given at a slot, compute the number of units of a move and the group of
a party, and are `1` exactly if an outcome is good or if the numbers of units are valid
(`Valid`). -/
structure SlpTab (P : Plan M U0 U1) (grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm)
    (D nI pS : ℕ) where
  /-- The coordinate that an input reads. -/
  input : Fin nI → (Fin (K + K) × Fin (K + K)) ⊕ M.Channel
  /-- The inputs, as digits. -/
  inp : Fin nI → PlanInput M U0 U1 → Fin D
  inp_val : ∀ i x, (inp i x : ℕ) =
    Sum.elim (fun ab => ((uncurry x.counts ab : Fin (U0 + 1)) : ℕ)) (fun ν => (x.outcomes ν : ℕ))
      (input i)
  /-- The function that a step computes. -/
  fn : ℕ → PlanInput M U0 U1 → Fin D
  isSlpStep : ∀ k < pS, IsSlpStep inp fn k
  /-- Whether a unit is current in the end. -/
  curGate : UnitId (K + K) U0 M.Channel U1 → Fin pS
  fn_curGate : ∀ u x, (fn (curGate u) x : ℕ) = if u ∈ P.cur x.counts x.outcomes E then 1 else 0
  /-- Whether a unit is cut: current in the end, with holders in two groups. -/
  cutGate : UnitId (K + K) U0 M.Channel U1 → Fin pS
  fn_cutGate : ∀ u x, (fn (cutGate u) x : ℕ) = if u ∈ Play.cutUnits (UnitId.holder M.channelParty)
    (grp x) (P.cur x.counts x.outcomes E) then 1 else 0
  /-- Whether a unit is given at a slot. -/
  givenGate : M.Slot → UnitId (K + K) U0 M.Channel U1 → Fin pS
  fn_givenGate : ∀ z u x, (fn (givenGate z u) x : ℕ) =
    if u ∈ P.given x.counts x.outcomes z then 1 else 0
  /-- The number of units that a move uses. -/
  countGate : Fin E → Fin pS
  fn_countGate : ∀ y x, (fn (countGate y) x : ℕ) = P.count x.counts x.outcomes y
  /-- The numbers of units that the dealing program accepts. -/
  Valid : (Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) → Prop
  /-- Whether the numbers of units are valid. -/
  validGate : Fin pS
  fn_validGate : ∀ x, (fn validGate x : ℕ) = 1 ↔ Valid x.counts
  /-- Whether the outcome of a move is good. -/
  goodGate : Fin E → Fin pS
  fn_goodGate : ∀ y x, (fn (goodGate y) x : ℕ) = 1 ↔ P.Good x.counts x.outcomes y
  /-- The group of a party. -/
  groupGate : Fin (K + K + A') → Fin pS
  fn_groupGate : ∀ a x, (fn (groupGate a) x : ℕ) = grp x a

/-- The step of a condition: the validity of the numbers of units for `none`, and whether the
outcome of the move `y` is good for `some y`. -/
@[expose] def SlpTab.conditionGate {P : Plan M U0 U1}
    {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm} (tab : SlpTab P grp D nI pS)
    (c : Option (Fin E)) : Fin pS :=
  c.elim tab.validGate tab.goodGate

/-- Injective codes, as bit lists, of the names, of the digits `Fin D` and of the row data, and
the keys of the cells and of the second copies of the units from a base party to itself. -/
structure Codes (S : Type) (M : Moves F (K + K + A') E) (U0 U1 D pS : ℕ) where
  /-- The code of a name. -/
  name : PlanName S M U0 U1 pS → List Bool
  name_injective : Injective name
  /-- The code of a digit. -/
  digit : Fin D → List Bool
  digit_injective : Injective digit
  /-- The code of row data. -/
  rowData : RowData (K + K) → List Bool
  rowData_injective : Injective rowData
  /-- The key of a cell. -/
  key : Cell M U0 U1 → List Bool
  /-- The key of the second copy of a unit from a base party to itself. -/
  dkey : Fin (K + K) × Fin U0 → List Bool

/-- The flags of the partners in a row with the data `d`, as in `baseBody`: the last partner
first. -/
@[expose] def flagsTree {A : ℕ} (d : RowData A) : Tree :=
  listT ((List.ofFn fun b => rowFlag d b).reverse.map num)

namespace Codes

variable {S : Type} (C : Codes S M U0 U1 D pS)

/-- A digit as a tree. -/
@[expose] def digitTree (d : Fin D) : Tree := ofBits (C.digit d)

theorem digitTree_injective : Injective C.digitTree := fun d d' h =>
  C.digit_injective (by simpa [digitTree] using congrArg Tree.path h)

/-- The step `dst := f d` for the digit `d` at the name `x`. -/
@[expose] noncomputable def unaryStep (x dst : PlanName S M U0 U1 pS) (f : Fin D → Tree) : DStep :=
  .op (C.name x) (C.name .empty) (C.name dst) (trieOf C.digit fun d => .cons (f d) .nil)

/-- The step `dst := f d d'` for the digits `d` at `x` and `d'` at `y`. -/
@[expose] noncomputable def binaryStep (x y dst : PlanName S M U0 U1 pS)
    (f : Fin D → Fin D → Fin D) : DStep :=
  .op (C.name x) (C.name y) (C.name dst) (trieOf C.digit fun d => trieOf C.digit fun d' =>
    C.digitTree (f d d'))

/-- The step `dst := t`. -/
@[expose] def constStep (dst : PlanName S M U0 U1 pS) (t : Tree) : DStep :=
  .op (C.name .empty) (C.name .empty) (C.name dst) (.cons (.cons t .nil) .nil)

/-- The keys of the copies at `a` of the first `n` units of the string from `a` to `b`. -/
@[expose] def writeKeysTree (a b : Fin (K + K)) (n : Fin (U0 + 1)) : Tree :=
  wordsEnc ((indicesBelow n).map fun k => C.key ⟨Fin.castAdd A' a, .init a b k⟩)

/-- The keys of the copies at `b` of the first `n` units of the string from `a` to `b`: the keys of
the second copies if `a = b`. -/
@[expose] def readKeysTree (a b : Fin (K + K)) (n : Fin (U0 + 1)) : Tree :=
  wordsEnc ((indicesBelow n).map fun k =>
    if a = b then C.dkey (b, k) else C.key ⟨Fin.castAdd A' b, .init a b k⟩)

/-- The comparisons of the two copies of the first `n` units from `a` to itself, as in
`baseInstructions`. -/
@[expose] def selfAgreeTree (a : Fin (K + K)) (n : Fin (U0 + 1)) : Tree :=
  listT ((indicesBelow n).map fun k =>
    (Instruction.agree (C.key ⟨Fin.castAdd A' a, .init a a k⟩) (C.dkey (a, k))).enc)

/-- The keys of the copies at the end `d` of the channel `ν` of its new units, for the outcome
`j`. -/
@[expose] def newKeysTree (ν : M.Channel) (d : Bool) (j : Fin U1) : Tree :=
  wordsEnc ((indicesBelow j.succ).map fun k => C.key ⟨M.channelParty ν d, .new ν k⟩)

variable {C} [DecidableEq S] {m : ℕ} {st : PlanName S M U0 U1 pS → Tree}

theorem exec_unaryStep {x dst : PlanName S M U0 U1 pS} {f : Fin D → Tree} {d : Fin D}
    (hz : st .empty = .nil) (hx : st x = C.digitTree d) :
    (C.unaryStep x dst f).exec m (extend C.name st fun _ => .nil) =
      [extend C.name (update st dst (f d)) fun _ => .nil] := by
  rw [unaryStep, exec_op C.name_injective, hz, hx, digitTree, path_ofBits,
    tget_trieOf C.digit_injective]
  rfl

theorem exec_binaryStep {x y dst : PlanName S M U0 U1 pS} {f : Fin D → Fin D → Fin D} {d d' : Fin D}
    (hx : st x = C.digitTree d) (hy : st y = C.digitTree d') :
    (C.binaryStep x y dst f).exec m (extend C.name st fun _ => .nil) =
      [extend C.name (update st dst (C.digitTree (f d d'))) fun _ => .nil] := by
  rw [binaryStep, exec_op C.name_injective, hx, hy, digitTree, digitTree, path_ofBits, path_ofBits,
    tget_trieOf C.digit_injective, tget_trieOf C.digit_injective]

theorem exec_constStep {dst : PlanName S M U0 U1 pS} {t : Tree} (hz : st .empty = .nil) :
    (C.constStep dst t).exec m (extend C.name st fun _ => .nil) =
      [extend C.name (update st dst t) fun _ => .nil] := by
  rw [constStep, exec_op C.name_injective, hz]
  rfl

end Codes

end Cslib.Circuits.Arithmetic.Separation.Dealing
