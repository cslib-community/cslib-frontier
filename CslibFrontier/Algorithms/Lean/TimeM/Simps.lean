/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TimeM.Simps.Init
public import Cslib.Algorithms.Lean.TimeM

/-!
# Return values and costs of programs in the time monad

A program `p` in `Cslib.Algorithms.Lean.TimeM` is specified by its return value `p.ret` and its
cost `p.time`. Both are computed by pushing the projection through the program: through `>>=`,
`pure`, `<$>`, `tick`, then through each program it calls, whose own specification is used. This
module makes that computation one step, so that a specification proof names the program and the
facts particular to it, and not the laws of the monad.

## The simp set

`simp only [time_simps]` pushes `.ret` and `.time` through a program. The set holds

* the laws of the monad: `ret_bind`, `time_bind`, `ret_pure`, `time_pure`, `ret_tick`, `time_tick`
  and the `<$>` and `<*>` forms;
* the loop lemmas of `CslibFrontier.Algorithms.Lean.TimeM.Loops`, when that module is imported;
* every specification tagged `@[time_simps]`. Tag the equation `(p x).ret = …` or `(p x).time = …`
  of a program that other programs call, so that their proofs use it without naming it;
* what a cost needs after that: the length, map and sum of an empty list and of a `cons`, the sum
  of a constant list (`List.map_const'`, `List.sum_replicate_nat`), `add_zero`, `zero_add`, and
  `implies_true` for the side conditions of the loop lemmas.

A bound `(p x).time ≤ …` cannot be a simp lemma: a caller states it with `have` and closes the goal
by arithmetic.

## The tactic

`time_spec p` proves a specification of the program `p`, and `time_spec p [h₁, h₂]` passes more
simp lemmas, such as the definition of the pure function that `p` computes. It is the whole proof.
See its docstring for the steps and for what it reports when it cannot close a goal.

## Main definitions

* `time_simps`: the simp set, declared in `CslibFrontier.Algorithms.Lean.TimeM.Simps.Init`.
* `time_spec`: the tactic.
-/

public section

namespace Cslib.Algorithms.Lean.TimeM

attribute [time_simps] ret_pure ret_bind ret_map ret_mapConst ret_seqRight ret_seqLeft ret_seq
  time_bind time_pure time_map time_seqRight time_seqLeft time_seq ret_tick time_tick
  List.length_nil List.length_cons List.map_nil List.map_cons List.sum_nil List.sum_cons
  List.map_const' List.sum_replicate_nat add_zero zero_add implies_true

end Cslib.Algorithms.Lean.TimeM

/--
`time_spec p` proves a specification of the program `p` in `Cslib.Algorithms.Lean.TimeM`: a
statement about `(p x).ret` or `(p x).time`, usually an equation or a bound. `time_spec p [h₁, h₂]`
also rewrites with the simp lemmas `h₁`, `h₂`.

It runs three steps.

1. Introduce the variables of a statement `∀ x, …`, then open `p` by `fun_induction p` or, when
   that does not apply, by `fun_cases p`. A recursive program gives one goal for each branch, with
   the induction hypotheses for its recursive calls.
2. On each goal, `simp only [time_simps, h₁, h₂]`, with `true_and`, `and_true` and `and_self` for
   a statement that is a conjunction. After `fun_induction` the hypotheses are rewrite rules too
   (`simp only [time_simps, h₁, h₂, *]`): this is how an induction hypothesis that is an equation
   is used. The `*` also takes the hypotheses of the theorem; after `fun_cases` there is no `*`.
3. Close each goal by `rfl` or `omega`. If neither does, `split` the first `if` or `match` in the
   goal, repeat step 2 and close every case by `rfl` or `omega`. If that fails too, try `grind` on
   the goal.

`grind` is the last resort. When the goal needs a fact that `rfl` and `omega` do not know, pass it
in the list: `time_spec p [Nat.succ_mul]` for `(k + 1) * c = k * c + c`,
`time_spec p [List.length_finRange]` for a loop over `List.finRange n`,
`time_spec p [Array.size_push]` for the size of an array that `p` builds by `push`.

The proof may depend on the axioms `propext`, `Quot.sound` and `Classical.choice`. `grind` proves by
contradiction, so it brings `Classical.choice`. A rewrite with a tagged specification brings the
axioms of that specification's proof, and a statement about the cost of `p` is rewritten with the
specifications of the values that `p` computes on the way. Check with `#print axioms` when a result
must avoid one of them.

`time_spec p` is meant to be the whole proof. A goal that step 3 cannot close is left as step 2
produced it, without the split, so the error is `unsolved goals` on the normalized goal, which shows
what is missing: usually the specification of a program that `p` calls, or a definition to pass in
the list. The tactic itself fails only when neither `fun_induction p` nor `fun_cases p` applies, for
instance when the goal has no call of `p` or `p` is applied to terms that are not variables.

For a statement that needs more than this, such as a bound that uses the bounds of the programs `p`
calls, do not continue after `time_spec`: write `simp only [p, time_simps]`, state those bounds with
`have`, and finish with `omega`.

The specifications of the programs that `p` calls must be in `time_simps` or among `h₁`, `h₂`, and
so must the definition of a pure function that the statement compares `p` with.
-/
syntax (name := timeSpec) "time_spec" (ppSpace colGt ident)
  (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

open Lean in
macro_rules
  | `(tactic| time_spec $f:ident $[[$extra,*]]?) => do
    let lemmas : Array (TSyntax ``Parser.Tactic.simpLemma) :=
      extra.map (·.getElems) |>.getD #[]
    -- An unhygienic reference: the simp set is found by its name.
    let set := mkIdent `time_simps
    let simpCases ← if lemmas.isEmpty then
        `(tactic| try simp only [$set:ident, true_and, and_true, and_self])
      else
        `(tactic| try simp only [$set:ident, true_and, and_true, and_self, $lemmas,*])
    -- With the hypotheses: the induction hypotheses are among them.
    let simpInd ← if lemmas.isEmpty then
        `(tactic| try simp only [$set:ident, true_and, and_true, and_self, *])
      else
        `(tactic| try simp only [$set:ident, true_and, and_true, and_self, $lemmas,*, *])
    -- `grind` is the last resort: it runs on a goal only after `rfl` and `omega` have failed on it
    -- and on its cases.
    let arith ← `(tactic| first | rfl | omega)
    let finish (simpStep : TSyntax `tactic) : MacroM (TSyntax `tactic) :=
      `(tactic| first
        | $arith:tactic
        | (split <;> ($simpStep:tactic) <;> $arith:tactic)
        | grind
        | skip)
    let finishInd ← finish simpInd
    let finishCases ← finish simpCases
    `(tactic| intros; first
      | (fun_induction $f <;> ($simpInd:tactic) <;> $finishInd:tactic)
      | (fun_cases $f <;> ($simpCases:tactic) <;> $finishCases:tactic))
