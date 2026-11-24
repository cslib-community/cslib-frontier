/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Classes.PH.Complete
import CslibFrontier.Computability.Complexity.Problems.CircuitSAT.Levin
import CslibFrontier.Computability.Complexity.Reduction.Turing

/-! Checked clients for Goldreich's NP-completeness transfer results (draft `r1.pdf` of
30 December 2006): Proposition 2.20 in its Karp, Levin and Cook forms, Theorem 2.21 for both the
circuit satisfaction set and relation, and Proposition 2.34 for the complement of `SAT`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GoldreichNPCompleteness

open Cslib.Complexity Cslib.Logic.PL Cslib.Circuits.Boolean Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- Proposition 2.20, Karp form: an NP-complete problem reducing to a problem in `NP` makes it
NP-complete. -/
example (hA : NPComplete encA A) (hAB : PolyTimeReducible encA encB A B) (hB : B ∈ NP encB) :
    NPComplete encB B :=
  ⟨hB, hA.2.trans hAB⟩

/-- Proposition 2.20, Levin form: a PC-complete relation Levin-reducing to an NP relation makes it
PC-complete (an `NPRelation` is in PC by construction). -/
example {R : NPRelation encA} {S : NPRelation encB} (hR : LevinHard R)
    (r : LevinReduction R S) : LevinHard S :=
  hR.trans r

/-- Proposition 2.20, Cook form: an NP-complete set of bit strings under Cook reductions that
Cook-reduces to a problem in `NP` makes it NP-complete under Cook reductions. -/
example {L : Set (List Bool)} (hL : NPTuringComplete encBits L)
    (hLB : PolyTimeTuringReducible encBits encB L B) (hB : B ∈ NP encB) :
    NPTuringComplete encB B :=
  ⟨hB, PolyTimeTuringHard.trans hL.2 hLB⟩

/-- Theorem 2.21: the circuit satisfaction relation is PC-complete, and its language is
`CircuitSAT`, which is NP-complete. -/
example : LevinHard CircuitSAT.npRelation ∧ NPComplete (encCircuit 1) CircuitSAT :=
  ⟨CircuitSAT_levinHard, CircuitSAT_npComplete⟩

/-- The Karp hardness of `CircuitSAT` also follows from its Levin hardness. -/
example : NPHard (encCircuit 1) CircuitSAT :=
  CircuitSAT.language_npRelation ▸ CircuitSAT_levinHard.npHard

/-- A satisfying assignment of a formula, as a `SAT` witness, is carried to an input satisfying
its circuit, and back. -/
example {φ : CNF ℕ} {w : List Bool} (h : SAT.npRelation.IsWitness φ w) :
    CircuitSAT.npRelation.IsWitness (SAT.toCircuit φ) (SAT.toCircuitWitness (φ, w)) ∧
      SAT.npRelation.IsWitness φ
        (SAT.ofCircuitWitness (φ, SAT.toCircuitWitness (φ, w))) :=
  have hf := SAT.isWitness_toCircuitWitness h
  ⟨hf, SAT.isWitness_ofCircuitWitness hf⟩

/-- Proposition 2.34 for `SAT`: unless `NP = coNP` for bit languages, the unsatisfiable formulas
have no NP proof system. -/
example (h : NP encBits ≠ coNP encBits) : SATᶜ ∉ NP encCNF :=
  CookLevin.SAT_npComplete.compl_notMem_NP h

end CslibFrontierTests.GoldreichNPCompleteness
