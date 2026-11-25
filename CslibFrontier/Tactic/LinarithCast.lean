/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside `Mathlib/Tactic/Linarith/Preprocessing.lean`)

public import CslibFrontier.Init
public import Mathlib.Tactic.Linarith

/-!
# Casting natural-number and integer facts for `linarith`

A real-valued bound often rests on counting facts proved in `ℕ`: `hk : k < n`, `hcut : c ≤ a + b`.
`linarith` casts such facts to `ℤ` and no further, so a goal in `ℝ` does not see them, and each one
is restated in `ℝ` by hand first:

```lean
have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
have hcut' : (c : ℝ) ≤ a + b := by exact_mod_cast hcut
linarith
```

`cast_linarith` is `linarith` with one more preprocessing step: every comparison between natural
numbers or integers among the hypotheses and the supplied terms is also cast into each ordered
field in which the problem has a comparison, and the casts are pushed to the leaves with
`push_cast`. A strict comparison `a < b` of natural numbers or integers is first strengthened to
`a + 1 ≤ b`, which the field no longer knows. `linarith` itself then adds `0 ≤ (x : K)` for each
cast natural number `x`. The comparisons already in the field, the negated goal among them, have
their casts pushed to the leaves as well, so `↑(a + b)` and `↑a + ↑b` are one sum and a `push_cast`
before the call is not needed. The example above becomes `cast_linarith [hk, hcut]`, or with a
scoped hypothesis list, `cast_linarith only [hk, hcut]`.

`cast_nlinarith` is the same step in front of `nlinarith`.

## Main definitions

* `Mathlib.Tactic.Linarith.castToField`: the preprocessor.
* `cast_linarith`, `cast_nlinarith`: `linarith` and `nlinarith` with the preprocessor, taking the
  same arguments (`!`, a configuration, `only`, a list of terms).

## Implementation notes

The fields are the types, other than `ℕ` and `ℤ`, of the comparisons that reach the preprocessor
(the negated goal among them) and that are linearly ordered fields. Original facts are kept, so
`linarith`'s own cast to `ℤ` still applies. Each cast fact, and each comparison in a field that
contains a cast, costs one `push_cast` call; the cast to `ℤ` already costs one per natural-number
fact. `cast_linarith only [...]` limits both to the listed facts.

A cast term is compared with the other atoms up to reducible defeq, as in `linarith`. A local
definition `x := (n : ℝ)` made with `set` unfolds at that transparency, so `x` and the cast
`(n : ℝ)` are the same atom.
-/

public meta section

namespace Mathlib.Tactic.Linarith

open Lean Meta Elab Tactic

/-- Whether `K` is a linearly ordered field, a target of `castToField`. -/
private def isOrderedField (K : Expr) : MetaM Bool := do
  if K.isConstOf ``Nat || K.isConstOf ``Int then return false
  try
    let field ← synthInstance? (← mkAppM ``Field #[K])
    let order ← synthInstance? (← mkAppM ``LinearOrder #[K])
    let (some _, some _) := (field, order) | return false
    let strict ← synthInstance? (← mkAppOptM ``IsStrictOrderedRing #[K, none, none])
    return strict.isSome
  catch _ => return false

/-- For `pf : a R b` with `a b : ℕ` or `a b : ℤ`, a proof of `(a : K) R' (b : K)` with the casts
pushed to the leaves. A strict `a < b` becomes `(a : K) + 1 ≤ b`. Returns `none` for any other
fact, or when the cast fact is no longer a comparison. -/
private def castComparison (simpCtx : Simp.Context) (K pf : Expr) : MetaM (Option Expr) := do
  let some (rel, α, a, b) ← observing? do (← instantiateMVars (← inferType pf)).ineq?
    | return none
  let isNat := α.isConstOf ``Nat
  if !isNat && !α.isConstOf ``Int then return none
  try
    let monoCast (lePf : Expr) : MetaM Expr := do
      let mono ← mkAppOptM (if isNat then ``Nat.mono_cast else ``Int.cast_mono)
        #[K, none, none, none, none]
      mkAppM' mono #[lePf]
    let castPf ← match rel with
      | .eq =>
        let castFn ← mkAppOptM (if isNat then ``Nat.cast else ``Int.cast) #[K, none]
        mkAppM ``congrArg #[castFn, pf]
      | .le => monoCast pf
      | .lt =>
        let lePf ←
          if isNat then mkAppM ``Nat.succ_le_of_lt #[pf]
          else mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[some a, some b], pf]
        monoCast lePf
    let prop ← inferType castPf
    let (r, _) ← simp prop simpCtx
    let (pf', prop') ← Zify.applySimpResultToProp' castPf prop r
    if (← observing? prop'.ineq?).isSome then return some pf' else return none
  catch e =>
    trace[linarith] "castToField: could not cast {pf} into {K}: {e.toMessageData}"
    return none

/-- For `pf : a R b` in a field, the same comparison with its casts pushed to the leaves. Returns
`pf` when it has no cast, or when the result is no longer a comparison. -/
private def pushCasts (simpCtx : Simp.Context) (pf : Expr) : MetaM Expr := do
  let prop ← instantiateMVars (← inferType pf)
  unless prop.containsConst (fun n => n == ``Nat.cast || n == ``Int.cast) do return pf
  try
    let (r, _) ← simp prop simpCtx
    let (pf', prop') ← Zify.applySimpResultToProp' pf prop r
    if (← observing? prop'.ineq?).isSome then return pf' else return pf
  catch _ => return pf

/-- The `push_cast` simp context, as used by `castToField`. -/
private def pushCastContext : MetaM Simp.Context := do
  let some ext ← getSimpExtension? `push_cast | throwError "the simp set `push_cast` is missing"
  Simp.mkContext {failIfUnchanged := false} (simpTheorems := #[← ext.getTheorems])

/--
`castToField` casts every comparison between natural numbers or integers into each linearly
ordered field in which the input has a comparison, pushing the casts to the leaves. A strict
comparison `a < b` is cast as `(a : K) + 1 ≤ b`. The original comparisons are kept. The casts in
the comparisons of those fields are pushed to the leaves too, so that `↑(a + b)` and `↑a + ↑b`
are the same sum.

Run it after `filterComparisons`, so that negated comparisons are already rewritten, and before
`natToInt`, which adds `0 ≤ (x : K)` for the cast natural numbers `x`.
-/
def castToField : GlobalPreprocessor where
  description := "cast ℕ and ℤ comparisons into the ordered fields of the problem"
  transform l := do
    let mut fields : Array Expr := #[]
    for pf in l do
      let some (_, α, _, _) ← observing? do (← instantiateMVars (← inferType pf)).ineq?
        | continue
      unless ← fields.anyM (isDefEq · α) do
        if ← isOrderedField α then fields := fields.push α
    if fields.isEmpty then return l
    let simpCtx ← pushCastContext
    let l ← l.mapM fun pf => do
      let some (_, α, _, _) ← observing? do (← instantiateMVars (← inferType pf)).ineq?
        | return pf
      if ← fields.anyM (isDefEq · α) then pushCasts simpCtx pf else return pf
    let mut cast : Array Expr := #[]
    for K in fields do
      for pf in l do
        if let some pf' ← castComparison simpCtx K pf then cast := cast.push pf'
    return l ++ cast.toList

/-- Inserts `castToField` before `natToInt` in a list of preprocessors. When `natToInt` is absent,
it goes after `filterComparisons`, which turns negated comparisons into comparisons, or at the
front when that is absent too. -/
private def addCastToField (pps : List GlobalBranchingPreprocessor) :
    List GlobalBranchingPreprocessor :=
  if pps.any (·.name == natToInt.name) then
    pps.flatMap fun pp => if pp.name == natToInt.name then [castToField.branching, pp] else [pp]
  else if pps.any (·.name == filterComparisons.name) then
    pps.flatMap fun pp =>
      if pp.name == filterComparisons.name then [pp, castToField.branching] else [pp]
  else
    castToField.branching :: pps

end Mathlib.Tactic.Linarith

namespace Mathlib.Tactic

open Lean Elab Tactic Linarith

/--
`cast_linarith` is `linarith` that also uses the comparisons between natural numbers and between
integers among its hypotheses, cast into the ordered field of the goal. A strict comparison
`a < b` of naturals or integers is used as `(a : K) + 1 ≤ b`. The casts in the goal and in the
hypotheses in the field are pushed to the leaves.

```lean
example (k n : ℕ) (x : ℝ) (hk : k < n) (hx : x ≤ k) : x + 1 ≤ n := by
  cast_linarith [hk]
```

It takes the arguments of `linarith`: `cast_linarith!`, a configuration, `only` and a list of
terms. Each cast fact costs a `push_cast` call; `cast_linarith only [...]` casts only the listed
facts.
-/
syntax (name := castLinarith) "cast_linarith" "!"? linarithArgsRest : tactic

/-- `cast_nlinarith` is `nlinarith` with the preprocessing of `cast_linarith`: comparisons between
natural numbers and between integers are also cast into the ordered field of the goal. -/
syntax (name := castNlinarith) "cast_nlinarith" "!"? linarithArgsRest : tactic

@[tactic_alt castLinarith] macro "cast_linarith!" rest:linarithArgsRest : tactic =>
  `(tactic| cast_linarith ! $rest:linarithArgsRest)

@[tactic_alt castNlinarith] macro "cast_nlinarith!" rest:linarithArgsRest : tactic =>
  `(tactic| cast_nlinarith ! $rest:linarithArgsRest)

/-- Runs `linarith`, or `nlinarith` when `nonlinear`, with `castToField` among its
preprocessors. The other arguments are those of the `linarith` syntax. -/
private def evalCastLinarith (nonlinear : Bool) (bang : Bool)
    (cfg : TSyntax ``Parser.Tactic.optConfig) (only : Bool) (args : Array Term) :
    TacticM Unit := withMainContext do
  let args ← args.mapM (elabTermWithoutNewMVars `cast_linarith)
  let cfg := (← elabLinarithConfig cfg).updateReducibility bang
  let pps := addCastToField cfg.preprocessors
  let cfg := { cfg with preprocessors := if nonlinear then pps.concat nlinarithExtras else pps }
  commitIfNoEx do liftMetaFinishingTactic <| Linarith.linarith only args.toList cfg

elab_rules : tactic
  | `(tactic| cast_linarith $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) =>
    evalCastLinarith false bang.isSome cfg o.isSome ((args.map (·.getElems)).getD #[])
  | `(tactic| cast_nlinarith $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) =>
    evalCastLinarith true bang.isSome cfg o.isSome ((args.map (·.getElems)).getD #[])

end Mathlib.Tactic
