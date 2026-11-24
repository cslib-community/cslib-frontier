/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Word.Rewire
import CslibFrontier.Tactic.Synthesis
import Mathlib.Tactic.FinCases

/-!
# Synthesis builder clients

Sharing, zero-cost reuse, fixed gate budgets, indexed bundles, and failed availability queries.
-/

namespace CslibFrontierTests.SynthesisBuilder

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

-- Build the negated input once and use it in two distinct outputs: three gates total.
example : ∃ c : Circuit signature 3 2,
    c.Computes interpretation (fun x => ![!x 0 && x 1, !x 0 || x 2]) ∧ c.size ≤ 3 := by
  let b := Synthesis.Builder.start interpretation (inputs 3)
  let shared : BooleanFunction 3 := fun x => !x 0
  let b := b.add (Synthesis.of_mem (f := fun x => x 0) (by synthesis_available) |>.not)
  let b := b.add ((Synthesis.of_mem (f := shared) (by synthesis_available)).and
    (Synthesis.of_mem (f := fun x => x 1) (by synthesis_available)))
  let b := b.add ((Synthesis.of_mem (f := shared) (by synthesis_available)).or
    (Synthesis.of_mem (f := fun x => x 2) (by synthesis_available)))
  synthesis_step b using Synthesis.of_mem (f := shared)
  have hcost : b.cost = 3 := rfl
  fail_if_success
    have := b.finish (t := {shared}) (k := 2) (by synthesis_available) (by omega)
  have h := b.finish (k := 3)
    (t := Set.range fun i x => (![!x 0 && x 1, !x 0 || x 2] : BitString 2) i)
    (by rintro _ ⟨i, rfl⟩; fin_cases i <;> synthesis_available) (by omega)
  exact h.exists_circuit_outputs

-- An earlier indexed family remains available after an unrelated gate is appended.
example {n k w : ℕ} (records : Fin k → BitString n → BitVec w) (j : Fin k) :
    let b := (Synthesis.Builder.start interpretation (⋃ i, wordWires (records i))).add
      (Synthesis.const false)
    wordWires (records j) ⊆ b.wires := by
  intro b
  synthesis_available

-- Finding wires cannot synthesize a negation or choose an element of an empty bundle. The
-- failure says what the tactic follows and how to add the missing wires.
/-- error: synthesis_available could not find these wires among the available ones. -/
#guard_msgs (substring := true) in
example : (fun x : BitString 1 => !x 0) ∈ inputs 1 := by synthesis_available

/-- error: synthesis_available could not find these wires among the available ones. -/
#guard_msgs (substring := true) in
example : (fun _ : BitString 0 => false) ∈ inputs 0 := by synthesis_available

-- `synthesis_step` reports the same failure when a premise of the rule is not available.
/-- error: synthesis_available could not find these wires among the available ones. -/
#guard_msgs (substring := true) in
example : True := by
  let b := Synthesis.Builder.start interpretation (inputs 1)
  synthesis_step b using Synthesis.of_mem (f := fun x : BitString 1 => !x 0)
  trivial

-- `Synthesis.extend` keeps everything built so far and names each new family explicitly. Starting
-- from the sources, a negation and a conjunction that reuses it cost two gates.
example : Synthesis interpretation (inputs 2)
    ((inputs 2 ∪ {fun x : BitString 2 => !x 0}) ∪ {fun x => !x 0 && x 1}) 2 := by
  have S0 : Synthesis interpretation (inputs 2) (inputs 2) 0 := Synthesis.of_subset le_rfl
  have S1 := S0.extend {fun x : BitString 2 => !x 0}
    (Synthesis.of_mem (f := fun x => x 0) (by synthesis_available)).not
  have S2 := S1.extend {fun x : BitString 2 => !x 0 && x 1}
    ((Synthesis.of_mem (f := fun x : BitString 2 => !x 0) (by synthesis_available)).and
      (Synthesis.of_mem (f := fun x => x 1) (by synthesis_available)))
  exact S2

-- With a rule list, even an empty one, the lookup is syntactic: it closes containment in any
-- member of a union by a local hypothesis, here a middle member and the last one, and finds a
-- retained singleton.
example {α : Type} (X Y s T₁ T₂ T₃ : Set α) (hX : X ⊆ T₂) (hY : Y ⊆ T₃) :
    X ⊆ s ∪ T₁ ∪ T₂ ∪ T₃ ∧ Y ⊆ s ∪ T₁ ∪ T₂ ∪ T₃ :=
  ⟨by synthesis_available [], by synthesis_available []⟩

example {α : Type} (f : α) (s t : Set α) : f ∈ s ∪ {f} ∪ t := by synthesis_available []

-- Inside a union the rule-list form uses a hypothesis only by `assumption`. It does not find a
-- quantified hypothesis about one member until that is instantiated; the plain form does.
example {n : ℕ} (s t : Set (BooleanFunction n)) (hc : ∀ b : Bool, (fun _ => b) ∈ s) :
    (fun _ => false) ∈ s ∪ t ∧ (fun _ => false) ∈ s ∪ t := by
  refine ⟨by synthesis_available, ?_⟩
  fail_if_success synthesis_available []
  have := hc false
  synthesis_available []

-- Nor does it find a hypothesis stated about an earlier builder's wires, because only the goal
-- is exposed; the plain form does.
example {n : ℕ} (s X : Set (BooleanFunction n)) :
    let b := (Synthesis.Builder.start interpretation s).add (Synthesis.const false)
    X ⊆ b.wires → X ⊆ (b.add (Synthesis.const true)).wires := by
  intro b h
  fail_if_success synthesis_available []
  synthesis_available

-- The general search also finds a member of a pair-indexed family.
example {α β γ : Type} (f : α → β → γ) (a : α) (b : β) (s : Set γ) :
    f a b ∈ s ∪ Set.range (fun p : α × β => f p.1 p.2) := by synthesis_available

-- A builder over words accumulates a union of equal-width word families, here ten of them.
-- Each step finds its operands syntactically, through the one rule that restates a word bitwise.
private def wordBuilder {n w : ℕ} (a b : BitString n → BitVec w)
    (s : Set (BooleanFunction n)) (ha : wordWires a ⊆ s) (hb : wordWires b ⊆ s) :
    Synthesis.Builder interpretation s := by
  let build := Synthesis.Builder.start interpretation s
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_add a b
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_sub a b
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_not a
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_not b
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_add b a
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_sub b a
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_add a a
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_sub a a
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_add b b
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_sub b b
  exact build

-- `synthesis_available` finds the sources in that chain by exposing the builder's union and
-- matching its members syntactically. Comparing the members' bits at default transparency instead
-- unfolds the word operations, which costs about ten thousand heartbeats on a chain of this length
-- and exhausts the default budget on Karatsuba's fifteen stages.
set_option maxHeartbeats 3000 in
-- A small budget: the syntactic search must not fall back to comparing the families' bits.
example {n w : ℕ} (a b : BitString n → BitVec w) (s : Set (BooleanFunction n))
    (ha : wordWires a ⊆ s) (hb : wordWires b ⊆ s) (i : ℕ)
    (hi : (fun x => (b x).getLsbD i) ∈ s) :
    wordWires a ⊆ (wordBuilder a b s ha hb).wires ∧
      (fun x => (b x).getLsbD i) ∈ (wordBuilder a b s ha hb).wires :=
  ⟨by synthesis_available, by synthesis_available⟩

-- With a rule list there is no general search, so a word that was never made available is
-- reported at once: here an operand of an eleventh step on that chain.
set_option maxHeartbeats 3000 in
-- A small budget: the failure must be the documented one, not an exhausted search.
/-- error: synthesis_available could not find these wires among the available ones. -/
#guard_msgs (substring := true) in
example {n w : ℕ} (a b c : BitString n → BitVec w) (s : Set (BooleanFunction n))
    (ha : wordWires a ⊆ s) (hb : wordWires b ⊆ s) : True := by
  let build := wordBuilder a b s ha hb
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_add a c
  trivial

-- Extending and shifting the bits of a built word costs no gates.
example {n w v k : ℕ} (a b : BitString n → BitVec w) (s : Set (BooleanFunction n))
    (ha : wordWires a ⊆ s) (hb : wordWires b ⊆ s) (hz : (fun _ => false) ∈ s) :
    Synthesis interpretation s (wordWires fun x => (a x + b x).setWidth v <<< k)
      (12 * w + 1) := by
  let build := Synthesis.Builder.start interpretation s
  synthesis_step [wordWires_subset_iff.mp] build using Synthesis.word_add a b
  refine build.finish ?_ (by change 0 + (12 * w + 1) ≤ _; omega)
  synthesis_available [wordWires_shiftLeft_subset, wordWires_setWidth_subset]

-- A rewiring rule cannot provide the padding constant when it was never made available.
/-- error: synthesis_available could not find these wires among the available ones. -/
#guard_msgs (substring := true) in
example {n w : ℕ} (a : BitString n → BitVec w) (s : Set (BooleanFunction n))
    (_ha : wordWires a ⊆ s) : wordWires (fun x => (a x).setWidth (w + 1)) ⊆ s := by
  synthesis_available [wordWires_setWidth_subset]

end CslibFrontierTests.SynthesisBuilder
