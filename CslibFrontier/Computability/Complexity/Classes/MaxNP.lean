/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LinearApproximation
public import CslibFrontier.Logics.SecondOrder.Encoding
public import Mathlib.ModelTheory.Complexity
import Mathlib.SetTheory.Cardinal.Finite

/-!
# MAX NP and MAX SNP

A solution interprets a fixed block of relation variables. Its value is the number of
tuples of input elements for which there is a witness tuple satisfying a fixed
quantifier-free formula in the expanded structure. This is the maximization form of
`∃ S ∀ x ∃ y φ` in [Papadimitriou and Yannakakis, §1, pp. 426–427][PapadimitriouYannakakis1991].
The generating MAX SNP class uses no existential first-order witness tuple.
The [Complexity Zoo](https://complexityzoo.net/Complexity_Zoo:M#maxsnp) calls that class
MAX SNP₀ and calls its L-reduction closure MAX SNP.

The input and solution use the library's enumerated relation tables.
`MaxNP` and `MaxSNP0` classify native optimization problems by their feasibility
and values on these encodings. The class predicates use an existing NPO certificate
for the problem being described.
-/

@[expose] public section

namespace Cslib.Complexity

open FirstOrder Cslib.Logic Turing.MultiTapeTM

/-- A fixed quantifier-free matrix, and the arities and lengths of its variable blocks. -/
structure MaxNPFormula (L : Language.{0, 0}) where
  /-- The number of relation variables that constitute the solution. -/
  relationCount : ℕ
  /-- The arity of each solution relation. -/
  arity : Fin relationCount → ℕ
  /-- The number of coordinates in the tuple counted by the objective. -/
  counted : ℕ
  /-- The number of coordinates in the existential first-order witness. -/
  witnesses : ℕ
  /-- The formula evaluated at the counted and witness tuples. -/
  matrix : (L.sum (ESO.varLanguage arity)).Formula (Fin counted ⊕ Fin witnesses)
  /-- The matrix is quantifier-free. -/
  matrix_isQF : matrix.IsQF

namespace MaxNPFormula

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The native encoding of well-formed input structures over `v`. -/
abbrev encInput (v : Vocabulary L) : {a : EncodedStructure // v.WellFormed a} ↪ List Bool :=
  (Function.Embedding.subtype _).trans encStructure

/-- A description uses only well-formed input structures and tables for the solution relations. -/
abbrev OptimizationProblem (v : Vocabulary L) :=
  NPOptimizationProblem (encInput v) (encList encBits)

/-- The table vocabulary for the relations selected by a solution. -/
abbrev solutionVocabulary (φ : MaxNPFormula L) : Vocabulary (ESO.varLanguage φ.arity) :=
  ESO.varLanguage.vocabulary φ.arity (Equiv.refl _)

/-- Count the tuples admitting a witness for the matrix under these solution relation tables. -/
noncomputable def score (φ : MaxNPFormula L) (v : Vocabulary L) (a : EncodedStructure)
    (tables : List (List Bool)) : ℕ :=
  letI := v.decode a
  letI := φ.solutionVocabulary.decode (a.1, tables)
  Nat.card {x : Fin φ.counted → Fin a.1 //
    ∃ y : Fin φ.witnesses → Fin a.1, φ.matrix.Realize (Sum.elim x y)}

/-- The formula describes the feasible solution tables and their objective values. -/
def Describes (φ : MaxNPFormula L) {v : Vocabulary L} (A : OptimizationProblem v) : Prop :=
  A.goal = .maximize ∧
    (∀ a tables, A.Feasible a tables ↔ φ.solutionVocabulary.WellFormed (a.val.1, tables)) ∧
    ∀ a tables, A.Feasible a tables → A.value (a, tables) = φ.score v a.val tables

end MaxNPFormula

/-- MAX NP, with the counted tuples allowed an existential first-order witness. -/
def MaxNP {L : Language.{0, 0}} [L.IsRelational] {v : Vocabulary L}
    (A : MaxNPFormula.OptimizationProblem v) : Prop :=
  ∃ φ : MaxNPFormula L, φ.Describes A

/-- The generating MAX SNP class, with a quantifier-free test on each counted tuple. -/
def MaxSNP0 {L : Language.{0, 0}} [L.IsRelational] {v : Vocabulary L}
    (A : MaxNPFormula.OptimizationProblem v) : Prop :=
  ∃ φ : MaxNPFormula L, φ.witnesses = 0 ∧ φ.Describes A

/-- MAX SNP is the L-reduction closure of the generating class. -/
def MaxSNP {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (A : NPOptimizationProblem encI encS) : Prop :=
  ∃ (L : Language.{0, 0}) (_ : L.IsRelational) (v : Vocabulary L)
    (B : MaxNPFormula.OptimizationProblem v), MaxSNP0 B ∧ Nonempty (LReduction A B)

/-- A generating MAX SNP objective is a MAX NP objective. -/
theorem MaxSNP0.maxNP {L : Language.{0, 0}} [L.IsRelational] {v : Vocabulary L}
    {A : MaxNPFormula.OptimizationProblem v} (hA : MaxSNP0 A) : MaxNP A := by
  obtain ⟨φ, _, hφ⟩ := hA
  exact ⟨φ, hφ⟩

/-- A generating MAX SNP problem belongs to MAX SNP by the identity reduction. -/
theorem MaxSNP0.maxSNP {L : Language.{0, 0}} [L.IsRelational] {v : Vocabulary L}
    {A : MaxNPFormula.OptimizationProblem v} (hA : MaxSNP0 A) : MaxSNP A :=
  ⟨L, inferInstance, v, A, hA, ⟨LReduction.refl A⟩⟩

end Cslib.Complexity
