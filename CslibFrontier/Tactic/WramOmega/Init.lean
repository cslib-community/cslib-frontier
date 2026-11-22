/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The attribute `wram_arith`

Declares the attribute `@[wram_arith]`, in a file of its own because an attribute cannot be used in
the file declaring it, and so that a module can tag its definitions without importing the tactic
`wram_omega` of `CslibFrontier.Tactic.WramOmega`, which reads the tags. The docstring of the
attribute says which definitions are tagged.

## Main definitions

* `wram_arith`: marks an arithmetic definition of a word-RAM development (an address, a size, a
  cost bound, a numeric parameter, or a predicate comparing such numbers) as one that `wram_omega`
  unfolds.
* `Cslib.Tactic.WramOmega.isPowerOfTwo`: the test for a power of two that `wram_omega` and `fits`
  share.
-/

public meta section

namespace Cslib.Tactic.WramOmega

open Lean Meta Elab

/-- What a `@[wram_arith]` definition returns once applied to all its arguments. -/
inductive Kind where
  /-- A natural number or an integer: `wram_omega` unfolds each application. -/
  | number
  /-- A proposition: `wram_omega` unfolds it in the goal and in the hypotheses. -/
  | predicate
  deriving Inhabited, BEq

/-- The definitions tagged `@[wram_arith]`, each with what it returns. -/
initialize wramArithExt : SimpleScopedEnvExtension (Name × Kind) (NameMap Kind) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun tagged (name, kind) => tagged.insert name kind
    initial := {}
  }

/-- What the definition `declName` returns, if `@[wram_arith]` accepts it: `ℕ`, `ℤ` or `Prop`,
after all the arguments its type names. -/
private def arithKind? (declName : Name) : MetaM (Option Kind) := do
  forallTelescope (← getConstInfo declName).type fun _ result => do
    let result ← whnfR result
    if result.isConstOf ``Nat || result.isConstOf ``Int then return some .number
    if result.isProp then return some .predicate
    return none

/-- Whether `e` is a power of two `2 ^ k` on natural numbers. `omega` reads such a power as an
unknown without knowing that it is positive, so `wram_omega` and `fits` add that fact for each one
they meet. -/
def isPowerOfTwo (e : Expr) : Bool :=
  match_expr e with
  | HPow.hPow α β _ _ b _ => α.isConstOf ``Nat && β.isConstOf ``Nat && b.nat? == some 2
  | _ => false

/-- `@[wram_arith]` marks a definition of a word-RAM development whose body is arithmetic that
proofs about the surrounding program have to see through, so that `wram_omega` unfolds it:

* a definition returning `ℕ` or `ℤ` that is an address, an index or an offset, a size, a capacity,
  a bound on steps or on cost, or a numeric parameter, given in closed form from numbers: its
  parameters and numeric fields such as a base, a length or a frontier;
* a definition returning `Prop` that compares such numbers, as the word-size bound
  `Cslib.WordRAM.Fits w v` and the ownership `Cslib.WordRAM.Block.Owns b a` of an address do.

The test is what the definition is, not the path of its file. The parameters of a data structure
or an algorithm designed for the word RAM qualify in whichever file they are written, also where
its program is not written yet, and so does a model over the memory oracle. These are not tagged,
even where `wram_omega` would prove the goal, and proofs about them name the definition
(`unfold a; omega`):

* a quantity read off stored data: a count or a sum over a list, a set, a tree or a memory state,
  the work of a run, or the value or the encoding of a word;
* a relation on data or on states, such as an order on keys or the invariant of a structure;
* a quantity of a development in another model of computation, such as a cell-probe lower bound.

A definition is tagged when a proof needs it, not in advance: a tag comes with a call of
`wram_omega` that unfolds the definition, so a family of definitions may be tagged in part. An
untagged definition stays an unknown to `omega`, whose failure message lists it under `where`.

A tag acts on every call: `wram_omega` unfolds each tagged definition it meets, and no call can
keep one folded. So tagging a definition changes what the existing calls unfold. `omega` then
mostly knows more, but it loses a bound that holds only with the definition folded, as when the
body divides by a variable. Such a call fails when its module is built (it cannot prove something
else instead), and the proof goes back to `unfold a b; omega` with the names it needs:
`Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compactedEpochWords_mono` keeps the
tagged `compactedItemWords` folded in this way.

Tag the definition where it is written, `@[wram_arith] def tableBase …`, or later with
`attribute [wram_arith] tableBase`; use `attribute [local wram_arith]` for a private definition.
The definition's body must be visible where `wram_omega` is called: the definition is exposed, or
the call is in its module. The tag does not expose the body and adds no `simp` lemma. -/
syntax (name := wramArith) "wram_arith" : attr

initialize registerBuiltinAttribute {
  name := `wramArith
  descr := "an arithmetic definition of a word-RAM development, which `wram_omega` unfolds"
  applicationTime := .afterTypeChecking
  add := fun declName stx kind => do
    unless stx.isOfKind ``wramArith do throwUnsupportedSyntax
    -- The body of a definition that is not exposed is visible in its own module only.
    let result ← withoutExporting do
      unless (← getConstInfo declName).hasValue do
        throwError "@[wram_arith]: `{.ofConstName declName}` is not a definition whose body is \
          visible here, so `wram_omega` could not unfold it."
      if ← isRecursiveDefinition declName then
        throwError "@[wram_arith]: `{.ofConstName declName}` is defined by recursion, so it has \
          no body that `wram_omega` could unfold."
      let some result ← MetaM.run' (arithKind? declName)
        | throwError "@[wram_arith]: `{.ofConstName declName}` returns neither a natural number, \
            an integer nor a proposition; `wram_omega` reasons by linear arithmetic over `ℕ` and \
            `ℤ`."
      pure result
    wramArithExt.add (declName, result) kind
}

end Cslib.Tactic.WramOmega

end
