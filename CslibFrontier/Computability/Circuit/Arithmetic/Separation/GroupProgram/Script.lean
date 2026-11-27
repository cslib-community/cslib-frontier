/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Lists

/-!
# Scripts of the program GROUP

The program GROUP of the evaluator of [AnthropicVPVNP2026] reads a *script*: the number `T` of
steps of the automaton and the number `ub` of bits of a unit, both in binary, and a list of
instructions. The instructions work on a trie whose keys are bit lists and whose contents are the
units, lists of bits. An instruction is

* a block or an input part of a base party (`Instruction.block`, `Instruction.input`), with a
  `Body` that says which flags the cuts of the letters of every tape obey and at which keys the
  units of the strings to and from the partners are written;
* a comparison of the contents at two keys, or of the contents at a key with a constant
  (`Instruction.agree`, `Instruction.fixed`);
* a role of a law (`Instruction.role`), with the keys of the units at its slots and of the units
  that it writes on its channels.

This file has the syntax, its encodings as trees, and the costs of the instructions: definitions,
with `@[simp]` equations for the encodings.

## Main definitions

* `Body`, `Instruction`: the syntax.
* `wordsEnc`, `keysEnc`, `Body.enc`, `Instruction.enc`, `scriptEnc`: the encodings as trees.
* `putCost`, `Body.cost`, `Instruction.cost`: the costs.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54); this file formalizes programs
of that evaluator, not the theorem. Ported from the source module `Nc.Grp.Script` (its syntax half).
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cslib.Circuits.Arithmetic.Separation.Interpreter
  Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

/-- What a base party writes and reads. -/
structure Body where
  /-- For every tape, in a fixed order of the tapes, the flags of the partners in reverse order:
  `0` if the partner gets no letter of the tape, `1` if it gets some, anything else if it may get
  any number. -/
  flags : List (List ℕ)
  /-- For every partner, the keys of the units of the string to the partner. -/
  writeKeys : List (List (List Bool))
  /-- For every partner, the keys of the units of the string from the partner. -/
  readKeys : List (List (List Bool))

/-- The instructions of a script. -/
inductive Instruction where
  /-- A block of the automaton from the state with number `q` to the state with number `q'`. -/
  | block (q q' : ℕ) (B : Body)
  /-- An input part: the codes of its letters, in reverse order. -/
  | input (part : List (List Bool)) (B : Body)
  /-- The contents at two keys agree. -/
  | agree (k k' : List Bool)
  /-- The contents at a key are `w`. -/
  | fixed (k w : List Bool)
  /-- The role with number `j` of a list of roles of laws, for `t` units. `slots`: for every slot
  the keys of the units given, in reverse order (bits missing to `t` units are read as zeros);
  `keys`: for every channel the keys of the new units. -/
  | role (j t : ℕ) (slots keys : List (List (List Bool)))

/-- A list of bit lists as a tree. -/
@[expose] def wordsEnc (l : List (List Bool)) : Tree := listT (l.map ofBits)

/-- A list of lists of keys as a tree. -/
@[expose] def keysEnc (l : List (List (List Bool))) : Tree := listT (l.map wordsEnc)

/-- A body as a tree. -/
@[expose] def Body.enc (B : Body) : Tree :=
  .cons (listT (B.flags.map fun l => listT (l.map num))) (.cons (keysEnc B.writeKeys)
    (keysEnc B.readKeys))

/-- An instruction as a tree: its number, which for a role is `4` plus the number of the role,
and its data. -/
@[expose] def Instruction.enc : Instruction → Tree
  | block q q' B => .cons (num 0) (.cons (.cons (num q) (num q')) B.enc)
  | input part B => .cons (num 1) (.cons (wordsEnc part) B.enc)
  | agree k k' => .cons (num 2) (.cons (ofBits k) (ofBits k'))
  | fixed k w => .cons (num 3) (.cons (ofBits k) (ofBits w))
  | role j t slots keys => .cons (num (4 + j)) (.cons (num t) (.cons (keysEnc slots)
      (keysEnc keys)))

/-- The argument of GROUP: `T` and `ub` in binary (most significant bit first), and the
instructions. -/
@[expose] def scriptEnc (bT bub : List Bool) (l : List Instruction) : Tree :=
  .cons (.cons (ofBits bT) (ofBits bub)) (listT (l.map Instruction.enc))

/-- The cost of writing units of `ub` bits at the keys of lists of keys. -/
@[expose] def putCost (ub : ℕ) (kss : List (List (List Bool))) : ℕ :=
  (kss.map fun ks => (ks.map fun k => ub + k.length + 1).sum + 1).sum

/-- The cost of a body. -/
@[expose] def Body.cost (ub : ℕ) (B : Body) : ℕ :=
  (B.flags.map List.length).sum + B.writeKeys.length + putCost ub B.writeKeys +
    putCost ub B.readKeys + 1

/-- The cost of an instruction, for `T` steps of the automaton and units of `ub` bits. -/
@[expose] def Instruction.cost (T ub : ℕ) : Instruction → ℕ
  | block _ _ B => T + B.cost ub
  | input part B => part.length + B.cost ub
  | agree k k' => k.length + k'.length + ub + 1
  | fixed k w => k.length + w.length + ub + 1
  | role _ t slots keys => t * (ub + 1) + putCost ub slots + putCost ub keys + 1

@[simp] theorem hd_wordsEnc (l : List (List Bool)) : (wordsEnc l).hd = ofBits (l.headD []) := by
  cases l <;> rfl

@[simp] theorem tl_wordsEnc (l : List (List Bool)) : (wordsEnc l).tl = wordsEnc l.tail := by
  cases l <;> rfl

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
