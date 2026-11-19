/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic
public import CslibFrontier.Tactic.PPT
public import CslibFrontier.Tactic.PolyTime

/-! # Classification memo scope without projecting unrelated search rules -/

public section
open Turing.MultiTapeTM
open Lean Elab Tactic

namespace CslibFrontierTests.PPTMemoScope

/-- An opaque routine has only a global construction certificate. -/
@[irreducible] def rawRoutine (word : List Bool) : List Bool := word.reverse

/-- Global construction evidence remains available to ordinary search. -/
private theorem rawRoutine_plain : ComputableInPolyTime rawRoutine encBits encBits := by
  unfold rawRoutine
  fun_prop

private noncomputable def rawFactor : ℕ :=
  Classical.choose (Internal.NormalForm.polyTime rawRoutine_plain)

private noncomputable def rawDegree : ℕ :=
  Classical.choose (Classical.choose_spec (Internal.NormalForm.polyTime rawRoutine_plain))

private noncomputable def rawBudget (n : ℕ) : ℕ := rawFactor * (n + 1) ^ rawDegree

-- Register only the machine property for this boundary regression.
attribute [local fun_prop] ComputableTidilyInTimeAndSpace

@[fun_prop] private theorem rawRoutine_raw :
    ComputableTidilyInTimeAndSpace rawRoutine encBits encBits
    (fun a => rawBudget (encBits a).length) (fun a => rawBudget (encBits a).length) := by
  exact Classical.choose_spec (Classical.choose_spec
    (Internal.NormalForm.polyTime rawRoutine_plain))

/-- A complete-arity alias tests fresh local proposition handling inside the memo scope. -/
private abbrev RawAlias {α β : Type*} (f : α → β)
    (input : α ↪ List Bool) (output : β ↪ List Bool) :=
  ComputableTidilyInTimeAndSpace f input output
    (fun a => rawBudget (input a).length) (fun a => rawBudget (input a).length)

@[fun_prop] private theorem rawAlias_toPlain {α β : Type*} {f : α → β}
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    (h : RawAlias f input output) : ComputableInPolyTime f input output := by
  refine ⟨rawBudget, rawBudget, ?_, ?_, h.computableInTimeAndSpace⟩ <;>
    unfold rawBudget <;> fun_prop

/-- The result has no global automation certificate. -/
@[irreducible] def localResult (word : List Bool) : List Bool := word

-- This fixture supplies ordinary Aesop with its raw construction rule independently of FunProp.
attribute [local aesop safe apply (rule_sets := [PolyTime])] rawRoutine_raw

-- The memo alone filters neither ordinary FunProp nor the builtin local-application descriptor.
example (h : ComputableTidilyInTimeAndSpace rawRoutine encBits encBits
    (fun a => rawBudget (encBits a).length) (fun a => rawBudget (encBits a).length) →
    ComputableInPolyTime localResult encBits encBits) :
    ComputableInPolyTime localResult encBits encBits := by
  run_tac Cslib.Tactic.PolyTime.Internal.withPlainRuleMemo do
    Lean.Elab.Tactic.evalTactic (← `(tactic| fail_if_success polytime))
    Lean.Elab.Tactic.evalTactic (← `(tactic| aesop (rule_sets := [PolyTime])))

example : ComputableInPolyTime rawRoutine encBits encBits := by
  run_tac Cslib.Tactic.PolyTime.Internal.withPlainRuleMemo do
    Lean.Elab.Tactic.evalTactic (← `(tactic| fun_prop))

-- Complete local facts remain usable; clearing one cannot be masked by a cached proof.
example (routine : List Bool → List Bool)
    (h : RawAlias routine encBits encBits → ComputableInPolyTime localResult encBits encBits)
    (hf : RawAlias routine encBits encBits) :
    ComputableInPolyTime localResult encBits encBits := by
  run_tac Cslib.Tactic.PolyTime.Internal.withPlainRuleMemo do
    Lean.Elab.Tactic.evalTactic (← `(tactic| fail_if_success (clear hf; polytime)))
    Lean.Elab.Tactic.evalTactic (← `(tactic| polytime))

-- Exceptions restore the scoped environment before ordinary global construction search.
example : ComputableInPolyTime rawRoutine encBits encBits := by
  run_tac do
    try
      Cslib.Tactic.PolyTime.Internal.withPlainRuleMemo do
        throwError "expected memo-scope exception"
    catch _ => pure ()
    Lean.Elab.Tactic.evalTactic (← `(tactic| fail_if_success polytime))
    Lean.Elab.Tactic.evalTactic (← `(tactic| fun_prop))

end CslibFrontierTests.PPTMemoScope
