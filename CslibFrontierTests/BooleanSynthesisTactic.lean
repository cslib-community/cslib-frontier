/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests for Boolean expression synthesis)

import CslibFrontier.Tactic.Synthesis

/-! # Boolean construction keeps source wires and gate budgets explicit -/

namespace CslibFrontierTests.BooleanSynthesisTactic

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

variable {n : ℕ} {s : Set (BooleanFunction n)} {f g h j : BooleanFunction n}

example : Synthesis interpretation (inputs 3) {fun x => x 0} 0 := by
  synthesis_bool

example : Synthesis interpretation (∅ : Set (BooleanFunction 2)) {fun _ => true} 1 := by
  synthesis_bool

example (hf : f ∈ s) (hg : g ∈ s) (hh : h ∈ s) :
    Synthesis interpretation s {fun x => f x ^^ (g x && !h x)} 6 := by
  synthesis_bool

-- A larger requested allowance does not need to be the constructor's exact syntactic sum.
example (hf : f ∈ s) (hg : g ∈ s) (hh : h ∈ s) :
    Synthesis interpretation s {fun x => f x ^^ (g x && !h x)} 10 := by
  synthesis_bool

private def updateBit (f g h j : BooleanFunction n) : BooleanFunction n :=
  fun x => f x ^^ (g x && (!h x && j x))

-- This is the seven-gate entry-update expression used by the Gauss–Jordan client.
example (hf : f ∈ s) (hg : g ∈ s) (hh : h ∈ s) (hj : j ∈ s) :
    Synthesis interpretation s {updateBit f g h j} 7 := by
  synthesis_bool [updateBit]

-- A compound expression already supplied as a wire is reused at zero cost.
example (hfg : (fun x => f x ^^ g x) ∈ s) :
    Synthesis interpretation s {fun x => f x ^^ g x} 0 := by
  synthesis_bool

-- Share the negation by retaining it in the builder; its two later uses do not add gates.
example : Synthesis interpretation (inputs 3)
    {fun x => (!x 0 && x 1) || !x 0} 3 := by
  let b := Synthesis.Builder.start interpretation (inputs 3)
  let b := b.add (show Synthesis interpretation (inputs 3) {fun x => !x 0} 1 from by
    synthesis_bool)
  let b := b.add (show Synthesis interpretation b.wires
    {fun x => (!x 0 && x 1) || !x 0} 2 from by synthesis_bool)
  exact b.finish (by synthesis_available) le_rfl

-- The four-gate XOR theorem must not be used at an allowance of three.
example (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis interpretation s {fun x => f x ^^ g x} 4 := by
  fail_if_success
    suffices hbad : Synthesis interpretation s {fun x => f x ^^ g x} 3 by
      exact hbad.mono Set.Subset.rfl Set.Subset.rfl (by decide)
    synthesis_bool
  synthesis_bool

-- A generous gate allowance cannot manufacture a missing input wire.
example : True := by
  fail_if_success
    have : Synthesis interpretation (∅ : Set (BooleanFunction 1)) {fun x => x 0} 100 := by
      synthesis_bool
  trivial

-- Constant gates are charged even when the source set is empty.
example : True := by
  fail_if_success
    have : Synthesis interpretation (∅ : Set (BooleanFunction 1)) {fun _ => false} 0 := by
      synthesis_bool
  trivial

end CslibFrontierTests.BooleanSynthesisTactic
