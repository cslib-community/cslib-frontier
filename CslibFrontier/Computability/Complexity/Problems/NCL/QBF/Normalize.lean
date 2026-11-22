/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Source
public import CslibFrontier.Computability.Complexity.Classes.Space.TQBF.Prenex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.List.Counting

/-!
# Closed source instances in polynomial time

Prepare arbitrary upstream `TQBFCNF` inputs for the NCL emitter. Replace inputs with free variables
by a fixed false instance and retain every closed input, including empty prefixes, matrices and
clauses. Repeated binders retain their ordinary shadowing semantics.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Source.normalize`: replace open inputs by a fixed false instance.

## Main results

* `Cslib.Complexity.NCL.QBF.Source.normalize_closed`: every normalized input is closed.
* `Cslib.Complexity.NCL.QBF.Source.normalize_mem_iff`: normalization preserves `TQBFCNF`.
* `Cslib.Complexity.NCL.QBF.Source.computableInPolyTime_normalize`: normalization is
  polynomial-time in the upstream binary encoding.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Source

open Cslib.Logic.PL Cslib.Logic.PL.QBF

/-- A fixed false closed source: `∃ x, ∀ y, y`. -/
@[expose] def noInput : PrenexCNF := ⟨[(0, 1)], [[(1, true)]]⟩

/-- Every literal's name occurs in the prefix, including shadowed names. -/
@[expose] def isClosedInput (x : PrenexCNF) : Bool :=
  x.matrix.all fun c => c.all fun l => decide (l.1 ∈ roundVars x.rounds)

private theorem isClosedInput_eq_true_iff (x : PrenexCNF) :
    isClosedInput x = true ↔ (rounds x.rounds (ofCNF x.matrix)).Closed := by
  simp only [isClosedInput, List.all_eq_true, decide_eq_true_eq, closed_rounds_ofCNF_iff]

/-- Retain closed formulas and replace open formulas by a fixed false instance. -/
@[expose] def normalize (x : PrenexCNF) : PrenexCNF :=
  if isClosedInput x then x else noInput

private theorem no_notMem : noInput ∉ TQBFCNF := by
  rw [mem_TQBFCNF, mem_TQBF]
  decide +kernel

/-- Every normalized input is closed. -/
theorem normalize_closed (x : PrenexCNF) :
    (rounds (normalize x).rounds (ofCNF (normalize x).matrix)).Closed := by
  unfold normalize
  split_ifs with hc
  · exact (isClosedInput_eq_true_iff x).1 hc
  · unfold noInput
    decide +kernel

/-- **Normalization preserves the full upstream source language**, including inputs with free
variables, empty prefixes, empty matrices, and empty clauses. -/
theorem normalize_mem_iff (x : PrenexCNF) : normalize x ∈ TQBFCNF ↔ x ∈ TQBFCNF := by
  unfold normalize
  split_ifs with hc
  · rfl
  · exact iff_of_false no_notMem fun h =>
      hc ((isClosedInput_eq_true_iff x).2 (mem_TQBF.mp (mem_TQBFCNF.mp h)).1)

open _root_.Turing.MultiTapeTM

/-- Normalization is polynomial-time in the upstream alternating prenex CNF encoding. -/
@[fun_prop]
theorem computableInPolyTime_normalize :
    ComputableInPolyTime normalize encPrenexCNF encPrenexCNF := by
  unfold normalize isClosedInput noInput roundVars
  simp only [List.decide_mem_eq_any]
  fun_prop

end Cslib.Complexity.NCL.QBF.Source
