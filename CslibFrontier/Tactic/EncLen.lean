/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.ComponentBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Tactic.EncLen.Init
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.Tactic.Simp

/-!
# Closing bounds on encoded lengths

`enc_len` first tries component-to-container bounds, then expands standard encoded lengths and
counts with `omega`. If that fails, it retries from the original goal with the registered
`enc_len` equations too. Trying the standard rules first preserves opaque encoding lengths
that are already bounded by local hypotheses, unless the caller explicitly asks to unfold them.

Both expansions use `simp only` with the lemmas given at the call. The `enc_len` simp set
includes the standard encodings and `nil`, `cons`, and append of `encList`.
Register a reusable encoding equation with `attribute [local enc_len] eFoo_apply`, or use
`scoped enc_len` to activate it with its namespace. `enc_structure` registers its generated
equations and field bounds in the same scopes as its `fun_prop` rules. A one-off equation can
still be supplied at the call: `enc_len [eFoo_apply]`. The location works as for `simp`, so
hypotheses are expanded only when requested, as in `enc_len at h ⊢`.

`omega` treats a product of two lengths as an atom, which it can match only when both sides
expanded to the same term. Bound a product by a fact in its own step, and bound each component by
one context length in its own step, so that the last `enc_len` only adds. Expanding everything at
once costs more: `omega` slows sharply with the number of atoms and facts.

The tactic fails when nothing expands, naming the plain `omega` that is then the right call, and
when `omega` cannot close the expanded goal, showing that goal.

## Main definitions

* `enc_len`: expand encoded lengths into their fields and close the bound with `omega`.
-/

public section

namespace Cslib.Tactic.EncLen

open Lean Parser.Tactic Elab Tactic Turing.MultiTapeTM

/-- The original expansion rules, before any client-specific equations are tried. Keeping this
list separate preserves opaque lengths already bounded in hypotheses outside the location. -/
private meta def standardRules : Array Name := #[
  ``length_encPair, ``length_frame, ``encUnary_apply, ``List.length_replicate,
  ``encBits_apply, ``encBool_apply, ``encOption_none, ``encOption_some,
  ``encSum_inl, ``encSum_inr, ``encList_nil, ``encList_cons, ``List.length_nil,
  ``List.length_cons, ``List.length_append]

-- Register the standard rules from the same list used by the conservative first attempt.
run_cmd
  let rules := (standardRules.push ``encList_append).map mkCIdent
  Lean.Elab.Command.elabCommand (← `(command| attribute [enc_len] $rules*))

/-- `enc_len` closes a linear bound on encoded lengths: it expands standard encodings (pairs,
frames, unary numbers, raw bit lists, Booleans, options, sums, and framed list constructors)
and runs `omega`. If that fails, it retries with equations registered in the `enc_len` simp set.
Before either expansion it tries the component bounds in `enc_component`. Opaque record lengths
already bounded in local hypotheses can therefore remain atoms in the successful attempt.

* `enc_len [eFoo_apply]` also unfolds the local encoding `eFoo`.
* `attribute [local enc_len] eFoo_apply` registers that equation for calls in the current scope.
* `enc_len at h ⊢` also expands the hypothesis `h`; without a location only the goal is expanded.

Products of lengths are atoms for `omega`. Bound them by facts in context first. -/
syntax (name := encLen) "enc_len" (" [" (simpStar <|> simpErase <|> simpLemma),* "]")?
  (location)? : tactic

elab_rules : tactic
  | `(tactic| enc_len $[[$args,*]]? $[$loc]?) => focus do
    let args := (args.map (·.getElems)).getD #[]
    let saved ← saveState
    try
      evalTactic (← `(tactic| simp only [enc_component, $args,*] $[$loc]?))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()
    saved.restore
    let standard ← standardRules.mapM fun name => `(simpLemma| $(mkCIdent name):term)
    let closeExpanded (rules : Array Syntax) : TacticM Unit := do
      let rules : Syntax.TSepArray [``simpStar, ``simpErase, ``simpLemma] "," :=
        ⟨(Syntax.mkSep (rules ++ args.map (·.raw)) (mkAtom ",")).getArgs⟩
      try
        evalTactic (← `(tactic| simp only [$rules,*] $[$loc]?))
      catch ex =>
        throwError "enc_len: the expansion failed: {ex.toMessageData}\n\
          If there is no encoded length to expand, use `omega`."
      if (← getUnsolvedGoals).isEmpty then return
      let goal ← getMainGoal
      try
        evalTactic (← `(tactic| omega))
      catch ex =>
        throwError "enc_len: `omega` could not close the expanded goal. Products are atoms, so \
          bound them by facts in context, and unfold local encodings with `enc_len [eFoo_apply]`.\n\
          {goal}\n{ex.toMessageData}"
    try
      closeExpanded (standard.map (·.raw))
      return
    catch _ => saved.restore
    closeExpanded #[(← `(simpLemma| enc_len)).raw]

end Cslib.Tactic.EncLen

end
