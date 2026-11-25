/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.MaxNP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # A checked structural maximization problem -/

set_option linter.privateModule false

namespace CslibFrontierTests.MaxNP

open Cslib.Complexity Cslib.Logic FirstOrder Turing.MultiTapeTM

/-- The only feasible solution is the empty list of relation tables, of value one. -/
private def constantProblem {L : Language} (v : Vocabulary L) :
    MaxNPFormula.OptimizationProblem v where
  Feasible _ tables := tables = []
  exists_feasible _ := ⟨[], rfl⟩
  feasible_mem_P := mem_P.mpr ⟨fun p => p.2.isEmpty,
    (ComputableInPolyTime.listIsEmpty (encA := encBits)).comp (ComputableInPolyTime.snd _ _),
    fun _ => List.isEmpty_iff.symm⟩
  solution_length_bound := ⟨Polynomial.C ((encList encBits) []).length, by
    intro a b h
    subst b
    simp⟩
  value _ := 1
  computableInPolyTime_value := ComputableInPolyTime.const 1
  goal := .maximize

private def trueMatrix (L : Language) : MaxNPFormula L where
  relationCount := 0
  arity := Fin.elim0
  counted := 0
  witnesses := 0
  matrix := ⊤
  matrix_isQF := Language.BoundedFormula.IsQF.top

private theorem constant_mem_MaxSNP0 {L : Language} [L.IsRelational] (v : Vocabulary L) :
    MaxSNP0 (constantProblem v) := by
  refine ⟨trueMatrix L, rfl, rfl, ?_, ?_⟩
  · intro a tables
    change tables = [] ↔ (trueMatrix L).solutionVocabulary.WellFormed (a.val.1, tables)
    simp [Vocabulary.WellFormed, trueMatrix, ESO.varLanguage.vocabulary]
  · intro a tables _
    change 1 = (trueMatrix L).score v a.val tables
    let _ := v.decode a.val
    let _ := (trueMatrix L).solutionVocabulary.decode (a.val.1, tables)
    rw [MaxNPFormula.score]
    symm
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨⟨fun x y => Subtype.ext (funext fun i => i.elim0)⟩, ?_⟩
    refine ⟨⟨Fin.elim0, Fin.elim0, ?_⟩⟩
    exact (Language.Formula.realize_top).mpr trivial

example {L : Language} [L.IsRelational] (v : Vocabulary L) :
    MaxNP (constantProblem v) ∧ MaxSNP (constantProblem v) :=
  ⟨(constant_mem_MaxSNP0 v).maxNP, (constant_mem_MaxSNP0 v).maxSNP⟩

end CslibFrontierTests.MaxNP
