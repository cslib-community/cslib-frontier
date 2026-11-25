/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.FormalComplexityMeasure
public import CslibFrontier.Computability.Circuit.Boolean.Formula.Restriction
public import CslibFrontier.Computability.Circuit.Boolean.NegationNormalForm

/-!
# Removing constant gates from De Morgan formulas

Constant propagation by the empty restriction either produces a constant or removes all constant
gates. When at least one input is available, a constant has a formula with two literal occurrences.
The resulting formula can also be put in negation normal form without changing its leaf count.
Thus every native formula has a constant-free formula in negation normal form with at most the
larger of two and its original leaf count. This is a model bridge for literal-only formula bounds;
it does not identify zero-cost native constants with source formulas of zero literal complexity.
-/

public section

namespace Cslib.Circuits.Formula

open Boolean BitString

variable {n : ℕ}

/-- A simplified formula has no constant gates. -/
theorem IsSimplified.isConstantFree {F : Formula signature n} (hF : F.IsSimplified) :
    F.IsConstantFree := by
  induction hF <;> simp_all [IsConstantFree, Formula.not, Formula.and, Formula.or]

/-- Pushing negations to inputs preserves the absence of constant gates. -/
theorem IsConstantFree.nnf {F : Formula signature n} (hF : F.IsConstantFree) (b : Bool) :
    (F.nnf b).IsConstantFree := by
  induction F generalizing b with
  | input i => cases b <;> trivial
  | gate op args ih =>
    cases op with
    | const c => exact hF.elim
    | not => exact ih 0 hF (!b)
    | and | or =>
      cases b <;> exact ⟨ih 0 hF.1 _, ih 1 hF.2 _⟩

/-- Over a nonempty input set, every formula has an equivalent constant-free formula with negations
only on inputs and at most the larger of two and its original number of leaves. -/
theorem exists_constantFree_isNNF_leafSize_le (hn : 0 < n) (F : Formula signature n) :
    ∃ G : Formula signature n, G.IsConstantFree ∧ G.IsNNF ∧
      (∀ x, G.eval interpretation x = F.eval interpretation x) ∧
      G.leafSize ≤ max 2 F.leafSize := by
  let H := F.restrict PartialAssignment.empty
  have heval (x : BitString n) : H.eval interpretation x = F.eval interpretation x := by
    simp [H]
  have hsize : H.leafSize ≤ F.leafSize := by
    simpa only [PartialAssignment.free_empty, leafSizeIn_univ] using
      leafSize_restrict_le PartialAssignment.empty F
  rcases restrict_eq_const_or_isSimplified PartialAssignment.empty F with ⟨b, hb⟩ | hH
  · let i : Fin n := ⟨0, hn⟩
    cases b
    · refine ⟨(input i).and (input i).not, ⟨trivial, trivial⟩,
        .and (.input i) (.not_input i), ?_, ?_⟩
      · intro x
        rw [← heval x, show H = const false from hb]
        simp
      · simp
    · refine ⟨(input i).or (input i).not, ⟨trivial, trivial⟩,
        .or (.input i) (.not_input i), ?_, ?_⟩
      · intro x
        rw [← heval x, show H = const true from hb]
        simp
      · simp
  · exact ⟨H.nnf false, hH.isConstantFree.nnf false, H.isNNF_nnf false,
      fun x => by simpa using heval x, by
        simpa only [leafSize_nnf] using hsize.trans (le_max_right 2 F.leafSize)⟩

end Cslib.Circuits.Formula
