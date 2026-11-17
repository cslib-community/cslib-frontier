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
simp lemmas, such as the definition of the pure function that `p` computes. See its docstring for
the steps and for the goals it leaves.

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
`time_spec p` proves a specification of the program `p` in `Cslib.Algorithms.Lean.TimeM`: an
equation or a bound for `(p x).ret` or `(p x).time`. `time_spec p [h₁, h₂]` also rewrites with the
simp lemmas `h₁`, `h₂`.

It runs three steps.

1. Introduce the variables of a statement `∀ x, …`, then open `p` by the first of
   `fun_induction p`, `fun_cases p` and `unfold p` that applies. A recursive program gives one goal
   for each branch, with the induction hypotheses for its recursive calls. Write
   `time_spec (p x y)` to choose among several calls of `p` in the goal.
2. On each goal, `simp only [time_simps, h₁, h₂, *]`, with `true_and`, `and_true` and `and_self`
   for a statement that is a conjunction. The `*` supplies the induction hypotheses and the
   conditions of the branch; it also uses the hypotheses of the theorem.
3. Close what remains by the first of `rfl`, `omega` and `grind` that succeeds. If none
   does, `split` the first `if` or `match` in the goal, repeat step 2 and try to close each case;
   this is done at most twice.

A goal that step 3 cannot close is left as step 2 produced it, without any split, so `time_spec p`
followed by more tactics is a proof by normalization: for a bound that needs the bounds of the
programs `p` calls, state those with `have` and finish with `omega`. The tactic fails only when
step 1 does.

The specifications of the programs that `p` calls must be in `time_simps` or among `h₁`, `h₂`.
-/
syntax (name := timeSpec) "time_spec" (ppSpace colGt term:max)
  (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

open Lean in
macro_rules
  | `(tactic| time_spec $f:term $[[$extra,*]]?) => do
    let lemmas : Array (TSyntax ``Parser.Tactic.simpLemma) :=
      extra.map (·.getElems) |>.getD #[]
    -- An unhygienic reference: the simp set is found by its name.
    let set := mkIdent `time_simps
    let simpStep ← if lemmas.isEmpty then
        `(tactic| try simp only [$set:ident, true_and, and_true, and_self, *])
      else
        `(tactic| try simp only [$set:ident, true_and, and_true, and_self, $lemmas,*, *])
    let close ← `(tactic| first | rfl | omega | grind)
    let finish ← `(tactic| first
      | $close:tactic
      | (split <;> ($simpStep:tactic) <;> $close:tactic)
      | (split <;> ($simpStep:tactic) <;>
          first | $close:tactic | (split <;> ($simpStep:tactic) <;> $close:tactic))
      | skip)
    let start ← if f.raw.isIdent then
        `(tactic| first | fun_induction $f | fun_cases $f | unfold $(⟨f.raw⟩):ident)
      else
        `(tactic| first | fun_induction $f | fun_cases $f)
    `(tactic| intros; ($start:tactic) <;> ($simpStep:tactic) <;> $finish:tactic)
