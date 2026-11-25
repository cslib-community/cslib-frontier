/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Fusion.Converse
import Mathlib.Tactic.FinCases

/-!
# Semi-ultrafilter converse clients

The cases include no primary or auxiliary inputs, empty and full targets, the fixed empty
rejection on an empty carrier, a rejected self-pair, simultaneous acceptance of complementary
sets, compressed labels for duplicate sets, and a nonconstant XOR function with a one-pair cover
and a three-AND universal verifier using two auxiliary bits. Ordinary module imports exercise
the exported compiler and certificate API.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.FusionConverse

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Fusion PairCertificate

-- The fixed empty slot invalidates every certificate on an empty carrier, even with no pairs.
example : Invalid ([] : List (Set (Fin 0) × Set (Fin 0))) (fun _ : Fin 0 => ∅)
    Fin.elim0 Fin.elim0 := by
  refine ⟨none, rfl, Or.inr (Or.inl ⟨none, ?_, rfl⟩)⟩
  ext i
  exact i.elim0

-- Equal rejected indices must be checked: a rejected universe fails against itself.
example : Invalid ([(Set.univ, ∅)] : List (Set Bool × Set Bool)) (fun _ : Fin 0 => ∅)
    Fin.elim0 (fun _ => false) := by
  refine ⟨some (left _ 0), rfl, Or.inr (Or.inl ⟨some (left _ 0), ?_, rfl⟩)⟩
  simp

private def nonemptyFilter : Semifilter Bool :=
  Semifilter.ofRejected {∅} (by simp) (by
    simpa only [Set.mem_singleton_iff, forall_eq, Set.union_empty] using
      (Set.empty_ne_univ : (∅ : Set Bool) ≠ Set.univ))

example : nonemptyFilter.IsUltra := Semifilter.isUltra_ofRejected _ _ _

-- Semi-ultrafilters may accept both sides of a complementary pair.
example : nonemptyFilter {true} ∧ nonemptyFilter {false} := by
  change (∀ t ∈ ({∅} : Set (Set Bool)), ¬ ({true} : Set Bool) ⊆ t) ∧
    (∀ t ∈ ({∅} : Set (Set Bool)), ¬ ({false} : Set Bool) ⊆ t)
  simp

private def emptyCover : PairCover {_x : BitString 0 | false = true}
    (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra where
  pairs := []
  isCover w := (Bool.false_ne_true w.point.property).elim

private def fullCover : PairCover {_x : BitString 0 | true = true}
    (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra where
  pairs := []
  isCover w _ := w.filter.not_apply_empty (w.filter.monotone
    (fun x _ => (x.property rfl).elim) w.filter.apply_univ)

example : ∃ g : BooleanFunction 0, ∃ c : Circuit Monotone.signature 0 1,
    forallGuess (n := 0) (p := 0) g = (fun _ => false) ∧
      c.ComputesFrom Monotone.interpretation (single g) AltFormula.literals ∧
      c.program.cost Monotone.andCost = 0 :=
  emptyCover.exists_forallGuess (fun _ => false)

example : ∃ g : BooleanFunction 0, ∃ c : Circuit Monotone.signature 0 1,
    forallGuess (n := 0) (p := 0) g = (fun _ => true) ∧
      c.ComputesFrom Monotone.interpretation (single g) AltFormula.literals ∧
      c.program.cost Monotone.andCost = 0 :=
  fullCover.exists_forallGuess (fun _ => true)

private def xorCircuit : Circuit Monotone.signature 4 1 :=
  ⟨(((Program.empty : Program Monotone.signature 4 0).gate ⟨.or, ![.input 0, .input 1]⟩).gate
    ⟨.or, ![.input 2, .input 3]⟩).gate ⟨.and, ![.gate 0, .gate 1]⟩, fun _ => .gate 2⟩

private def xorVerifier : BooleanFunction (2 + 0) := fun x => x 0 ^^ x 1

private theorem xor_computes : xorCircuit.ComputesFrom Monotone.interpretation
    (single xorVerifier) AltFormula.literals := by
  unfold Circuit.ComputesFrom
  decide

-- A nonconstant target has an actual cover, so the converse's input is satisfiable.
example : ∃ a, ∃ g : BooleanFunction (2 + a),
    ∃ c : Circuit Monotone.signature ((2 + a) + (2 + a)) 1,
    forallGuess g = (fun x => x 0 ^^ x 1) ∧
      c.ComputesFrom Monotone.interpretation (single g) AltFormula.literals ∧
      c.program.cost Monotone.andCost = 3 ∧ a = 2 := by
  obtain ⟨cover, hcover⟩ := exists_pairCover_forallGuess xorVerifier xorCircuit xor_computes
  have hc : cover.pairs.length = 1 := hcover
  have hquant : forallGuess xorVerifier = (fun x => x 0 ^^ x 1) := by decide
  obtain ⟨g, c, hg, hcomputes, hcost⟩ := cover.exists_forallGuess (forallGuess xorVerifier)
  exact ⟨compactSize cover.pairs, g, c, hg.trans hquant, hcomputes, by simpa [hc] using hcost,
    by simp [compactSize, hc]⟩

-- Compressing the labels keeps the empty-carrier contradiction even when there are no pairs.
example : compactInvalid ([] : List (Set (Fin 0) × Set (Fin 0)))
    (fun _ : Fin 0 => ∅) Fin.elim0 Fin.elim0 := by
  refine Or.inl (Or.inr (Or.inl ⟨none, ?_, rfl⟩))
  ext i
  exact i.elim0

example : ¬ compactInvalid ([] : List (Set Bool × Set Bool))
    (fun _ : Fin 0 => ∅) Fin.elim0 Fin.elim0 := by
  rintro (h | ⟨i, _, _⟩ | ⟨i, _, _⟩)
  · rcases h with ⟨i, _, hi⟩ | ⟨i, hu, _⟩ | ⟨i, _, _⟩
    · cases i with
      | none => cases hi
      | some i => exact i.elim0
    · cases i with
      | none =>
        exact Set.empty_ne_univ (by simpa only [sets, Set.union_empty] using hu)
      | some i => exact i.elim0
    · exact i.elim0
  · exact i.elim0
  · exact i.elim0

-- Duplicate component sets cannot be assigned contradictory labels.
example : compactInvalid ([({false}, {false})] : List (Set Bool × Set Bool))
    (fun _ : Fin 0 => ∅) Fin.elim0 ![true, false] := by
  refine Or.inr (Or.inr ⟨0, rfl, Or.inl ⟨some (left _ 0), ?_, rfl⟩⟩)
  simp

-- For a complementary pair with empty intersection, precisely one component must be accepted.
-- Both false violate the covering condition; both true force acceptance of the empty set.
example (y : Fin 2 → Bool) :
    compactInvalid ([({false}, {true})] : List (Set Bool × Set Bool))
      (fun _ : Fin 0 => ∅) Fin.elim0 y ↔ y 0 = y 1 := by
  have hpoint (u : Bool) (h₀ : y 0 = !u) (h₁ : y 1 = u) :
      ¬ compactInvalid ([({false}, {true})] : List (Set Bool × Set Bool))
        (fun _ : Fin 0 => ∅) Fin.elim0 y := by
    have hy : y = compactPointLabels ([({false}, {true})] : List (Set Bool × Set Bool)) u := by
      funext i
      fin_cases i
      · change y 0 = pointLabels ([({false}, {true})] : List (Set Bool × Set Bool))
          u (left _ 0)
        cases u <;> simpa [pointLabels] using h₀
      · change y 1 = pointLabels ([({false}, {true})] : List (Set Bool × Set Bool))
          u (right _ 0)
        cases u <;> simpa [pointLabels] using h₁
    rw [← invalid_expandLabels_iff, hy, expandLabels_compactPointLabels]
    exact not_invalid_pointLabels _ _ _ u (fun i => i.elim0)
  cases h₀ : y 0 <;> cases h₁ : y 1
  · refine iff_of_true ?_ rfl
    refine Or.inr (Or.inl ⟨0, h₀, Or.inr (Or.inl ⟨some (right _ 0), ?_, ?_⟩)⟩)
    · ext b
      cases b <;> simp
    · rw [label, expandLabels_right]
      change y 1 = false
      exact h₁
  · exact iff_of_false (hpoint true h₀ h₁) (by decide)
  · exact iff_of_false (hpoint false h₀ h₁) (by decide)
  · refine iff_of_true ?_ rfl
    refine Or.inl (Or.inl ⟨some (inter _ 0), ?_, ?_⟩)
    · simp
    · simp [label, expandLabels_inter, h₀, h₁]

example : econondeterministicAndComplexity (fun x : BitString 2 => x 0 ^^ x 1) ≤ 1 := by
  exact econondeterministicAndComplexity_le_cost xorVerifier (by decide) xorCircuit xor_computes

end CslibFrontierTests.FusionConverse

