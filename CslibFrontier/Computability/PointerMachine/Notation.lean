/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Structured

/-!
# Notation for structured pointer-machine programs

`pm[ s₁; s₂; … ]` writes a structured program (`Cslib.PointerMachine.Code`) as a sequence of
statements, one per data instruction, in the style of the pseudocode of [Tarjan1979]. Registers
and fields are named by identifiers, for instance local abbreviations of elements of `Fin n`.
Pointer and data registers are different kinds of registers that may have the same type, so the
assignment sign tells them apart: `←` assigns a pointer and `:=` assigns a datum.

The statements on pointers are:

* `r ← null`: clear pointer register `r`;
* `r ← r'`: copy a pointer register;
* `r ← base[f]`, `base[f] ← r`: load and store pointer field `f` of the record specified by
  `base`;
* `r ← new`: create a record.

The statements on data are:

* `s := s'`: copy a data register;
* `s := base[f]`, `base[f] := s`: load and store data field `f` of the record specified by
  `base`;
* `s := o s₁ s₂`: the operation `o` of the model on data registers `s₁` and `s₂`.

The tests are `r = r'` and `r ≠ r'` on pointer registers, and `p s₁ s₂` and `¬p s₁ s₂` for a
predicate `p` of the model on data registers, given by name or as a term in parentheses. The
control statements are:

* `if t then [ … ] else [ … ]`, `if t then [ … ]`: a conditional;
* `while t do [ … ]`: a loop;
* `⟪c⟫`: the structured program `c`, for instance a subroutine, or `⟪.skip⟫`.

The notation unfolds to the constructors of `Code`, so it adds nothing to the semantics. The
machine jumps when a test holds, so a conditional on a negated test exchanges its alternatives,
and a loop on a negated test is `Code.loopUntil`, the cheaper loop; `while r ≠ nil do [ … ]`
costs one test and one jump per iteration.

It is scoped: `open Cslib.PointerMachine` enables it. Only the categories `pmStmt` and `pmTest`
and the syntax abbreviation `pmBlock` are global, since Lean cannot scope them; without the open
they have no rules. Its only new tokens are `pm[` and the internal `pm_stmt%`, `pm_block%`,
`pm_branch%` and `pm_while%`, so it reserves no identifiers: `null` and `new` remain ordinary
names, except that a pointer register cannot be copied from one named `null` or `new`.

## Main definitions

* `pm[ s₁; s₂; … ]`: scoped notation for structured pointer-machine programs.

## Tactics

* `pm_straight` (scoped, like the notation): on a goal `ExecWithin c x ?y T` for straight-line code
  `c`, runs its data instructions in order, so that `?y` becomes the state reached, and proves
  that their number is at most `T`.

## References

* [R. E. Tarjan, *A class of algorithms which require nonlinear time to maintain disjoint
  sets*][Tarjan1979]
-/

public section

namespace Cslib.PointerMachine

/-- A statement of a structured pointer-machine program. -/
declare_syntax_cat pmStmt

/-- A test of a structured pointer-machine program. -/
declare_syntax_cat pmTest

/-- A block of statements, separated by semicolons. -/
syntax pmBlock := "[" sepBy1(pmStmt, "; ") "]"

/-- A structured pointer-machine program, written as a block of statements. -/
scoped syntax "pm[" sepBy1(pmStmt, "; ") "]" : term

/-- Internal: a nested block of statements, as a structured program. -/
scoped syntax "pm_block%" pmBlock : term

/-- Internal: a single statement, as a structured program. -/
scoped syntax "pm_stmt%" pmStmt : term

/-- Internal: a conditional on a test, with its alternatives as terms. -/
scoped syntax "pm_branch%" pmTest " then " term:max " else " term:max : term

/-- Internal: a loop on a test, with its body as a term. -/
scoped syntax "pm_while%" pmTest " then " term:max : term

/-- Two pointer registers are equal. -/
scoped syntax ident " = " ident : pmTest
/-- Two pointer registers differ. -/
scoped syntax ident " ≠ " ident : pmTest
/-- A predicate of the model, given by name, holds of two data registers. -/
scoped syntax ident ppSpace ident ppSpace ident : pmTest
/-- A predicate of the model, given as a term, holds of two data registers. -/
scoped syntax "(" term ")" ppSpace ident ppSpace ident : pmTest
/-- A predicate of the model, given by name, fails on two data registers. -/
scoped syntax "¬" ident ppSpace ident ppSpace ident : pmTest
/-- A predicate of the model, given as a term, fails on two data registers. -/
scoped syntax "¬" "(" term ")" ppSpace ident ppSpace ident : pmTest

/-- Clear a pointer register. -/
scoped syntax (priority := high) ident " ← " &"null" : pmStmt
/-- Create a record. -/
scoped syntax (priority := high) ident " ← " &"new" : pmStmt
/-- Copy a pointer register. -/
scoped syntax ident " ← " ident : pmStmt
/-- Load a pointer field. -/
scoped syntax ident " ← " ident noWs "[" ident "]" : pmStmt
/-- Store a pointer field. -/
scoped syntax ident noWs "[" ident "]" " ← " ident : pmStmt
/-- Copy a data register. -/
scoped syntax ident " := " ident : pmStmt
/-- Load a data field. -/
scoped syntax ident " := " ident noWs "[" ident "]" : pmStmt
/-- Store a data field. -/
scoped syntax ident noWs "[" ident "]" " := " ident : pmStmt
/-- An operation of the model on two data registers. -/
scoped syntax ident " := " term:max ppSpace ident ppSpace ident : pmStmt
/-- A conditional. -/
scoped syntax "if " pmTest " then " pmBlock " else " pmBlock : pmStmt
/-- A conditional without second alternative. -/
scoped syntax "if " pmTest " then " pmBlock : pmStmt
/-- A loop. -/
scoped syntax "while " pmTest " do " pmBlock : pmStmt
/-- A structured program given as a term. -/
scoped syntax "⟪" term "⟫" : pmStmt

scoped macro_rules
  | `(pm[ $s:pmStmt ]) => `(pm_stmt% $s)
  | `(pm[ $s:pmStmt; $ss;* ]) => `(Cslib.Program.Code.seq (pm_stmt% $s) (pm[ $ss;* ]))
  | `(pm_block% [ $ss;* ]) => `(pm[ $ss;* ])

scoped macro_rules
  | `(pm_branch% $a:ident = $b:ident then $p else $n) =>
    `(Cslib.Program.Code.branch (Cslib.PointerMachine.Test.ptrEq $a $b) $p $n)
  | `(pm_branch% $a:ident ≠ $b:ident then $p else $n) =>
    `(Cslib.Program.Code.branch (Cslib.PointerMachine.Test.ptrEq $a $b) $n $p)
  | `(pm_branch% $t:ident $a:ident $b:ident then $p else $n) =>
    `(Cslib.Program.Code.branch (Cslib.PointerMachine.Test.data $t $a $b) $p $n)
  | `(pm_branch% ($t:term) $a:ident $b:ident then $p else $n) =>
    `(Cslib.Program.Code.branch (Cslib.PointerMachine.Test.data $t $a $b) $p $n)
  | `(pm_branch% ¬$t:ident $a:ident $b:ident then $p else $n) =>
    `(Cslib.Program.Code.branch (Cslib.PointerMachine.Test.data $t $a $b) $n $p)
  | `(pm_branch% ¬($t:term) $a:ident $b:ident then $p else $n) =>
    `(Cslib.Program.Code.branch (Cslib.PointerMachine.Test.data $t $a $b) $n $p)
  | `(pm_while% $a:ident = $b:ident then $p) =>
    `(Cslib.Program.Code.loop (Cslib.PointerMachine.Test.ptrEq $a $b) $p)
  | `(pm_while% $a:ident ≠ $b:ident then $p) =>
    `(Cslib.Program.Code.loopUntil (Cslib.PointerMachine.Test.ptrEq $a $b) $p)
  | `(pm_while% $t:ident $a:ident $b:ident then $p) =>
    `(Cslib.Program.Code.loop (Cslib.PointerMachine.Test.data $t $a $b) $p)
  | `(pm_while% ($t:term) $a:ident $b:ident then $p) =>
    `(Cslib.Program.Code.loop (Cslib.PointerMachine.Test.data $t $a $b) $p)
  | `(pm_while% ¬$t:ident $a:ident $b:ident then $p) =>
    `(Cslib.Program.Code.loopUntil (Cslib.PointerMachine.Test.data $t $a $b) $p)
  | `(pm_while% ¬($t:term) $a:ident $b:ident then $p) =>
    `(Cslib.Program.Code.loopUntil (Cslib.PointerMachine.Test.data $t $a $b) $p)

scoped macro_rules
  | `(pm_stmt% $r:ident ← null) => `(Cslib.Program.Code.op (Cslib.PointerMachine.Op.null $r))
  | `(pm_stmt% $r:ident ← new) => `(Cslib.Program.Code.op (Cslib.PointerMachine.Op.create $r))
  | `(pm_stmt% $r:ident ← $s:ident) =>
    `(Cslib.Program.Code.op (Cslib.PointerMachine.Op.movePtr $r $s))
  | `(pm_stmt% $r:ident ← $base:ident[$f:ident]) =>
    `(Cslib.Program.Code.op (Cslib.PointerMachine.Op.loadPtr $r $f $base))
  | `(pm_stmt% $base:ident[$f:ident] ← $r:ident) =>
    `(Cslib.Program.Code.op (Cslib.PointerMachine.Op.storePtr $f $base $r))
  | `(pm_stmt% $s:ident := $t:ident) =>
    `(Cslib.Program.Code.op (Cslib.PointerMachine.Op.moveData $s $t))
  | `(pm_stmt% $s:ident := $base:ident[$f:ident]) =>
    `(Cslib.Program.Code.op (Cslib.PointerMachine.Op.loadData $s $f $base))
  | `(pm_stmt% $base:ident[$f:ident] := $s:ident) =>
    `(Cslib.Program.Code.op (Cslib.PointerMachine.Op.storeData $f $base $s))
  | `(pm_stmt% $s:ident := $o:term $a:ident $b:ident) =>
    `(Cslib.Program.Code.op (Cslib.PointerMachine.Op.op $o $s $a $b))
  | `(pm_stmt% if $t:pmTest then $p:pmBlock else $n:pmBlock) =>
    `(pm_branch% $t then (pm_block% $p) else (pm_block% $n))
  | `(pm_stmt% if $t:pmTest then $p:pmBlock) =>
    `(pm_branch% $t then (pm_block% $p) else Cslib.Program.Code.skip)
  | `(pm_stmt% while $t:pmTest do $b:pmBlock) => `(pm_while% $t then (pm_block% $b))
  | `(pm_stmt% ⟪$c⟫) => `(($c : Cslib.PointerMachine.Code _ _))

/-- `pm_straight` proves a goal `ExecWithin c x ?y T` for straight-line code `c`: a sequence of data
instructions. It runs them in order, so that `?y` becomes the state reached, in closed form as
nested `Op.effect`, and proves by `omega` that their number is at most `T`. At a conditional, a
loop or a program given by `⟪…⟫` it stops and leaves the execution of that part as a goal. -/
scoped syntax (name := pmStraight) "pm_straight" : tactic

scoped macro_rules
  | `(tactic| pm_straight) => `(tactic|
      (apply Cslib.Program.ExecWithin.of_exec
       case h =>
         repeat' first
           | exact Cslib.PointerMachine.Exec.op
           | exact Cslib.Program.Exec.skip
           | apply Cslib.Program.Exec.seq
       case hn => omega))

end Cslib.PointerMachine
