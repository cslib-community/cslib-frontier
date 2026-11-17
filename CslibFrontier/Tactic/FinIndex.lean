/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Tactic.FailureNote
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.SplitIfs
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Linter.Util

/-!
# Comparing `Fin` indices by value

Registers, tape indices, vertices and layout slots are `Fin` values built from numbers:
`⟨6 * q + r, _⟩`, `Fin.castAdd m i`, a definition that returns one of these. That two of them are
equal, distinct or ordered is a linear fact about the numbers. `fin_index` proves it: it turns each
comparison of `Fin` values into the comparison of the numbers, moves `Fin.val` through
constructors and casts, and calls `omega`.

`omega` alone already compares `Fin` variables (it reads `i = j`, `i ≠ j`, `i < j` and `i ≤ j` in
`Fin n`, and knows `i.val < n`), so a goal with only variables and numerals needs no more than
`omega`. It does not look inside `Fin.val ⟨e, h⟩`, `Fin.val (Fin.castAdd m i)` or
`Fin.val (f i)` for a definition `f`: each is an unknown number to it. Mathlib's `fin_omega`
rewrites comparisons and `Fin` arithmetic to values but leaves the same terms opaque. `fin_index`
is the step in between: a fixed set of `Fin` lemmas for the constructors and casts, and the
definitions to unfold given at the call, as in `fin_index [stageLeft, stageRight]`.

The rewriting is `simp only … at *`, so facts in context are used in whatever form they have:
`h : f i = f j`, `hne : i ≠ j` and `h : ¬ i < j` all become facts about values, also when a term
such as `i.pred hne` depends on the hypothesis. A goal `Function.Injective f` is introduced
first.

When a definition branches on an `if` with numeric branches, `omega` cannot use it; `fin_index`
then splits every `if` in the goal and the context and calls `omega` on each case. This second
attempt runs only after `omega` has failed, and its cost doubles with each `if` in the goal and
the context.

`fin_index` is a finishing tactic: it closes the goal or fails and leaves it as it was. It is not
a way to rewrite a goal to values and continue.

The list holds what exposes the numbers: the definitions that build the indices, facts about
their values, local `let` variables. It is checked like a `simp only` list: an entry that the
rewriting never used at a call is reported under `linter.unusedSimpArgs`. A goal that needs
set-membership or logic lemmas before it is a comparison of indices is a `simp only [⋯]; omega`
goal; keep it that way.

## Main definitions

* `fin_index`: prove an equality, disequality or order fact between `Fin` values from the
  numbers.
-/

public section

namespace Cslib.Tactic.FinIndex

open Lean Parser.Tactic Elab Tactic Meta

/-- `fin_index` proves a fact about `Fin` values from the underlying numbers: `a = b`, `a ≠ b`,
`a < b`, `a ≤ b`, a conjunction of these, `Function.Injective f`, or `False` from such a
hypothesis.

It introduces the hypotheses of the goal, rewrites every comparison of `Fin` values in the goal
and the context to a comparison of numbers, moves `Fin.val` through `⟨_, _⟩`, `Fin.castAdd`,
`Fin.natAdd`, `Fin.castSucc`, `Fin.succ`, `Fin.last`, `Fin.cast`, `Fin.castLE`, `Fin.castLT`,
`Fin.addNat`, `Fin.subNat`, `Fin.pred`, `Fin.rev` and `if`, and calls `omega`.

* `fin_index [f, g, h]` also unfolds the definitions `f` and `g` and rewrites with the fact `h`.
  The list is a `simp only` list: definitions, local `let` variables, lemmas such as
  `(hf : ∀ i, (f i).val = i.val + 7)`, and `Prod.mk.injEq` for index pairs all go there.
* If `omega` fails and an `if` remains, every `if` in the goal and the context is split and
  `omega` runs on each case. This is a second attempt; its cost doubles with each `if`.

`fin_index` closes the goal or fails; it never leaves a rewritten goal behind. On failure the
error of `omega` ends with a note showing the rewritten goal: a term in its `where` list such as
`↑(f i)` names a definition missing from the list. An entry that is never used is reported under
`linter.unusedSimpArgs`. Without constructors, casts or definitions, use `omega`. -/
syntax (name := finIndex) "fin_index" (" [" (simpErase <|> simpLemma),* "]")? : tactic

meta section

/-- For one run of a `fin_index` call, which of its list entries the rewriting step used. The
linter below combines the runs of a call, since `t <;> fin_index [f, g]` may need `f` in one goal
and `g` in another. -/
private structure ListUse where
  mask : Array Bool
deriving TypeName

/-- The use mask that `simp` recorded for its argument list, if this info tree holds one. -/
private partial def simpArgsMask? : InfoTree → Option (Array Bool)
  | .context _ t => simpArgsMask? t
  | .node i ts =>
    let here := match i with
      | .ofCustomInfo ci => (ci.value.get? UnusedSimpArgsInfo).map (·.mask)
      | _ => none
    here <|> ts.findSome? simpArgsMask?
  | .hole _ => none

/-- Reports the entries of a `fin_index` list that no run of that call used. -/
private def unusedListEntries : Linter where
  run _ := do
    unless Linter.getLinterValue linter.unusedSimpArgs (← Linter.getLinterOptions) do return
    let mut uses : Std.HashMap Syntax.Range (Syntax × Array Bool) := {}
    for tree in (← get).infoState.trees do
      uses := tree.foldInfo (init := uses) fun _ info uses => Id.run do
        let .ofCustomInfo ci := info | return uses
        let some { mask } := ci.value.get? ListUse | return uses
        let some range := info.range? | return uses
        let mask := match uses[range]? with
          | some (_, seen) => Array.zipWith (· || ·) mask seen
          | none => mask
        return uses.insert range (ci.stx, mask)
    for (_, stx, mask) in uses.toArray.qsort (·.1.start < ·.1.start) do
      for entry in stx[1][1].getSepArgs, used in mask do
        unless used do
          Linter.logLint linter.unusedSimpArgs entry
            m!"This `fin_index` list entry is unused:{indentD entry}"

initialize addLinter unusedListEntries

end

elab_rules : tactic
  | `(tactic| fin_index $[[$args,*]]?) => focus do
    let args := (args.map (·.getElems)).getD #[]
    evalTactic (← `(tactic| intros))
    let g ← getMainGoal
    if (← whnfR (← g.getType)).isAppOf ``Function.Injective then
      let (_, g) ← g.introNP 3
      replaceMainGoal [g]
    -- `simp … at *` skips a hypothesis that the goal or another hypothesis depends on, such as
    -- `h : i ≠ 0` under `i.pred h`. Give each of these a copy that can be rewritten.
    let g ← getMainGoal
    let free ← g.getNondepPropHyps
    let copies ← g.withContext do
      (← getLCtx).foldlM (init := #[]) fun acc d => do
        if d.isImplementationDetail || free.contains d.fvarId || !(← isProp d.type) then
          return acc
        return acc.push { userName := d.userName, type := d.type, value := d.toExpr }
    let (_, g) ← g.assertHypotheses copies
    replaceMainGoal [g]
    let seen := (← getInfoState).trees.size
    withoutRecover <| evalTactic (← `(tactic| simp -failIfUnchanged only [ne_eq, Fin.ext_iff,
      Fin.lt_def, Fin.le_def, Fin.val_mk, Fin.val_castAdd, Fin.val_natAdd, Fin.val_castSucc,
      Fin.val_succ, Fin.val_last, Fin.val_cast, Fin.val_castLE, Fin.val_castLT, Fin.val_addNat,
      Fin.val_subNat, Fin.val_pred, Fin.val_rev, Fin.val_zero, Fin.val_one, apply_ite Fin.val,
      apply_dite Fin.val, $args,*] at *))
    -- The entries of the list are the last arguments of that `simp` call.
    if let some mask := ((← getInfoState).trees.toArray.extract seen).findSome? simpArgsMask? then
      pushInfoLeaf <| .ofCustomInfo
        { stx := ← getRef, value := .mk (ListUse.mk (mask.extract (mask.size - args.size))) }
    if (← getUnsolvedGoals).isEmpty then return
    let goal ← getMainGoal
    withFailureNote m!"fin_index rewrote the goal and the hypotheses to comparisons of numbers, \
        and `omega` could not close the result, also not after splitting each `if`:\
        {indentD goal}\nA term in the `where` list of `omega`, such as `↑(f i)`, names a \
        definition to unfold: `fin_index [f]`." do
      try
        evalTactic (← `(tactic| omega))
      catch ex =>
        try
          evalTactic (← `(tactic| split_ifs at * <;> first | omega | trivial | contradiction))
        catch _ => throw ex

end Cslib.Tactic.FinIndex

end
