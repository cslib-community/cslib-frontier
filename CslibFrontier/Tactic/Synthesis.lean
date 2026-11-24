/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Synthesis
public meta import Lean.Elab.Tactic

/-!
# Finding available circuit wires

`synthesis_available` proves membership and inclusion of wire families by following unions,
indexed bundles, and local availability hypotheses. It also finds the wires retained by a
`Synthesis.Builder`. Semantic rewrites and bounds on indices remain ordinary local lemmas.
The tactic never adds a gate or invokes a synthesis theorem.

It first exposes the `wires` field of concrete builders, without unfolding any of their wire
functions, and matches syntactic members of the resulting union `A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ` at reducible
transparency. Only if that fails does it run the general search, which
compares wire functions at default transparency. On wire families of equal width, such as the
bits of `BitVec` words, those comparisons unfold the word operations before they fail.
On a fifteen-step chain they exhaust the default heartbeat budget.

`synthesis_available [rules]` never runs the general search. It composes the listed zero-cost
rewiring lemmas and the local hypotheses at reducible transparency, closing each leaf by the
syntactic match, so a missing wire is reported at once. `synthesis_available []` is the syntactic
match alone.

## Main definitions

* `synthesis_available`: close an available-wire obligation by structural proof search.
* `synthesis_step b using rule`: append a certified construction to `b`, finding its input wires.
  `synthesis_step [rules] b using rule` finds them with `synthesis_available [rules]`.
-/

public section

open Lean Meta Elab Tactic

/-- Expose only the wire fields of concrete builders. Reducing the builder to its constructor
does not reduce its fields, so equal-width word operations remain opaque to the union search. -/
private meta def exposeBuilderWires : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let some info ← getProjectionFnInfo? ``Cslib.Circuits.Synthesis.Builder.wires
    | throwError "missing Builder.wires projection information"
  let target ← Meta.transform (← instantiateMVars (← goal.getType)) (pre := fun e => do
    let builder? := match e with
      | .proj ``Cslib.Circuits.Synthesis.Builder 0 builder => some (builder, #[])
      | _ =>
        if e.isAppOf ``Cslib.Circuits.Synthesis.Builder.wires then
          let args := e.getAppArgs
          args[info.numParams]?.map fun builder =>
            (builder, args.extract (info.numParams + 1) args.size)
        else none
    let some (builder, trailing) := builder? | return .continue
    let builder ← withDefault <| whnf builder
    unless builder.isAppOf info.ctorName do return .continue
    let some wires := builder.getAppArgs[info.numParams + info.i]? | return .continue
    return .visit (mkAppN wires trailing))
  replaceMainGoal [← goal.replaceTargetDefEq target]

/-- Close `X ⊆ A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ` when `X` is syntactically `A₀` or some `Tᵢ`, or is contained in
one of them by a local hypothesis, and close `f ∈ A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ` from a singleton `{f}` or a
local hypothesis `f ∈ A₀` or `f ∈ Tᵢ`. Matching is at reducible transparency and never looks inside
a wire family.
Each step uses `refine`, which unifies the goal before recursing, so the search ends after one
step per union in the goal and fails quickly on any other goal. -/
local syntax (name := synthesisUnion) "synthesis_union" : tactic
macro_rules | `(tactic| synthesis_union) => `(tactic| first
  | with_reducible assumption
  | with_reducible exact Set.Subset.rfl
  | with_reducible exact Set.mem_singleton _
  | with_reducible exact Set.subset_union_right
  | (with_reducible refine Set.subset_union_of_subset_left ?_ _); synthesis_union
  | (with_reducible refine Set.mem_union_right _ ?_); synthesis_union
  | (with_reducible refine Set.mem_union_left _ ?_); synthesis_union
  | (with_reducible refine Set.subset_union_of_subset_right ?_ _); with_reducible assumption)

/-- The recursive search behind `synthesis_available`. Its failures are discarded by the
alternatives that call it, so only `synthesis_available` reports one. A pair-indexed range is
tried before a singly indexed one: the pair form fails at once on any other index type, whereas
`Set.mem_range_self _` is slow to fail on a pair-indexed family. -/
local syntax (name := synthesisAvailableSearch) "synthesis_available_search" : tactic
macro_rules | `(tactic| synthesis_available_search) => `(tactic|
  first
  | assumption
  | exact Set.mem_range.mpr ⟨(_, _), rfl⟩
  | exact Set.mem_range_self _
  | rfl
  | (solve | apply Set.mem_union_right; synthesis_available_search)
  | (solve | apply Set.mem_union_left; synthesis_available_search)
  | (solve |
      change _ ∈ Set.iUnion _
      rw [Set.mem_iUnion]
      refine ⟨?_, ?_⟩
      rotate_left
      synthesis_available_search)
  | (solve | apply Set.range_subset_iff.mpr; intro i; synthesis_available_search)
  | (solve | apply Set.iUnion_subset; intro i; synthesis_available_search)
  | solve_by_elim (maxDepth := 3) (symm := false) (exfalso := false)
      (constructor := false) (intro := false) [Set.mem_range_self]
  | (solve | intro i; synthesis_available_search))

-- Close structural leaves before applying another rewiring rule. In particular, a rule with
-- a premise `X ⊆ A` should use a stored copy of `X`, rather than explore rewiring it again.
local syntax "synthesis_available_rewire" " [" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| synthesis_available_rewire [$rules,*]) => withMainContext do
    let union ← `(tactic| synthesis_union)
    let cfg : Lean.Meta.SolveByElim.SolveByElimConfig := {
      maxDepth := 32, transparency := .reducible, symm := false, exfalso := false,
      constructor := false, intro := false }
    let cfg := cfg.mainGoalProc fun g => do
      let some goals ← observing? <| Term.TermElabM.run' <| run g (evalTactic union)
        | failure
      pure goals
    replaceMainGoal (← Lean.Elab.Tactic.SolveByElim.processSyntax cfg true true
      rules.getElems.toList [] #[] [← getMainGoal])

/-- Find already available wires, without synthesizing new functions. Exposes concrete builders'
wire fields, matches members of the resulting union syntactically, then runs the general search.
`synthesis_available [rules]` instead composes the supplied availability lemmas and the local
hypotheses through the unions at reducible transparency, and never runs the general search: this
supports zero-cost rewiring without unfolding the functions computed by the circuit, and fails at
once when a wire is missing. -/
syntax (name := synthesisAvailable) "synthesis_available" (" [" term,* "]")? : tactic
elab_rules : tactic
  | `(tactic| synthesis_available $[[$rules,*]]?) => do
    exposeBuilderWires
    let find ← match rules with
      | some rules => `(tactic| synthesis_available_rewire [$rules,*])
      | none => `(tactic| first | synthesis_union | synthesis_available_search)
    evalTactic (← `(tactic|
      first
      | $find:tactic
      | fail "synthesis_available could not find these wires among the available ones. It follows \
          unions, indexed families, the wires of a `Synthesis.Builder` and local hypotheses, but \
          never adds a gate: append the missing construction first, with `synthesis_step` or \
          `Builder.add`. With a rule list it matches union members syntactically and does not \
          follow indexed families."))

/-- Append a synthesis rule to the named builder, solving its available-wire premises with
`synthesis_available`, or with `synthesis_available [rules]` when a rule list is given. -/
syntax (name := synthesisStep) "synthesis_step " (" [" term,* "] ")? ident " using " term : tactic
macro_rules
  | `(tactic| synthesis_step $[[$rules,*]]? $b:ident using $rule:term) =>
    `(tactic| let $b := ($b).add (by apply $rule <;> synthesis_available $[[$rules,*]]?))

end
