/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Synthesis
public import CslibFrontier.Tactic.Synthesis

/-!
# Synthesizing Boolean expressions over available wires

`synthesis_bool` proves a goal `Synthesis interpretation s {fun x => e x} n` over the De Morgan
basis when `e x` is written with `!`, `&&`, `||`, `^^` and Boolean constants over functions that
`synthesis_available` finds in `s`. It replaces a hand-assembled tree of `Synthesis.of_mem`
certificates joined by `Synthesis.not`, `Synthesis.and`, `Synthesis.or` and `Synthesis.xor`.

Every operator in `e` becomes a gate. A constant, a negation, a conjunction and a disjunction cost
one gate and an exclusive or costs four. Each occurrence of a subexpression is charged, and
`omega` checks the total against `n`. Only a function that is not headed by an operator is looked
up in `s`. Operators are matched at reducible transparency, which sees through a local `let` but
never unfolds a definition: the caller unfolds what should be built.

The tactic does not reuse a compound wire: a function headed by an operator is built again even
when an earlier step retained it. Looking up every subexpression first would add a failed search
for each operator, and on a long `Synthesis.Builder` chain each of those takes seconds. To reuse
such a wire, apply the gate lemma to its `Synthesis.of_mem` certificate.

## Main definitions

* `synthesis_bool`: build a Boolean expression from available wires within a gate bound.
-/

public section

/-- The recursive search behind `synthesis_bool`. It applies the rule for the operator at the head
of the function and recurses into the operands, whose costs stay metavariables for those goals to
assign. A function with no operator at its head is looked up among the available wires, and is
left as a goal for `synthesis_bool` to report when it is not there. -/
local syntax (name := synthesisBoolSearch) "synthesis_bool_search" : tactic
macro_rules | `(tactic| synthesis_bool_search) => `(tactic| first
  | with_reducible exact Cslib.Circuits.Synthesis.const _
  | (with_reducible apply (config := { newGoals := .nonDependentOnly })
      Cslib.Circuits.Synthesis.not) <;> synthesis_bool_search
  | (with_reducible apply (config := { newGoals := .nonDependentOnly })
      Cslib.Circuits.Synthesis.and) <;> synthesis_bool_search
  | (with_reducible apply (config := { newGoals := .nonDependentOnly })
      Cslib.Circuits.Synthesis.or) <;> synthesis_bool_search
  | (with_reducible apply (config := { newGoals := .nonDependentOnly })
      Cslib.Circuits.Synthesis.xor) <;> synthesis_bool_search
  | (refine Cslib.Circuits.Synthesis.of_mem ?_; synthesis_available)
  | skip)

/-- Prove `Synthesis interpretation s {fun x => e x} n` when `e x` combines functions available in
`s` with `!`, `&&`, `||`, `^^` and constants, and the operators of `e` cost at most `n` gates.
Definitions are not unfolded, and a compound function is built even when it is available. -/
syntax (name := synthesisBool) "synthesis_bool" : tactic
macro_rules | `(tactic| synthesis_bool) => `(tactic|
  (first
   | apply (config := { newGoals := .nonDependentOnly }) Cslib.Circuits.Synthesis.mono
       (hs := Set.Subset.rfl) (ht := Set.Subset.rfl)
   | fail "synthesis_bool proves goals of the form `Synthesis interpretation s {f} n`."
   focus
     synthesis_bool_search
     first
     | done
     | fail "synthesis_bool could not build the functions below. Each is neither a constant, nor \
         `!`, `&&`, `||` or `^^` applied to other functions, nor found by `synthesis_available`. \
         Unfold definitions before calling it, and retain missing wires first."
   first
   | omega
   | fail "synthesis_bool built the expression, but its gates do not fit the bound: `omega` \
       could not prove the inequality below, whose left side counts the gates used."))

end
