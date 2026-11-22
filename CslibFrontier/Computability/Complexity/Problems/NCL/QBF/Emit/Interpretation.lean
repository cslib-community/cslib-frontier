/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.WordTarget
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Fixed

/-!
# Interpreting fixed source instructions

The emitter distinguishes blue-red scanning swaps from red-blue return swaps. Any interpretation
preserving identity, composition and tensor can instantiate its fixed fragment table.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.Target`: a composition-preserving interpretation.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.expand_circuit`: instructions expand to the
  interpreted circuit word.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

open Diagram

namespace Interpretation

/-- An interpretation preserving identity, sequential composition and parallel composition. -/
structure Target where
  /-- Interpret a source diagram as a primitive diagram with the same boundary. -/
  map : {a b : List Color} → Diagram Gate a b → Diagram Prim a b
  /-- Preserve identity wires. -/
  map_id (a : List Color) : map (Diagram.id a) = Diagram.id a
  /-- Preserve sequential composition. -/
  map_comp {a b c : List Color} (D₁ : Diagram Gate a b) (D₂ : Diagram Gate b c) :
    map (D₁.comp D₂) = (map D₁).comp (map D₂)
  /-- Preserve parallel composition. -/
  map_tensor {a b c d : List Color} (D₁ : Diagram Gate a b) (D₂ : Diagram Gate c d) :
    map (D₁.tensor D₂) = (map D₁).tensor (map D₂)

/-- Interpret the fixed fragments and the two color orders of adjacent swaps. -/
abbrev Target.language (T : Target) : Word.Fixed.Language where
  Opcode := Opcode
  enumeration := inferInstance
  fragment op := ⟨op.data.inputs, op.data.outputs, T.map op.data.diagram⟩

/-- Primitive diagram interpretation as a word-valued interpretation. -/
private def Target.wordTarget (T : Target) : WordTarget Slice where
  map D k := (T.map D).toWord Prim.interp k
  map_id a k := by rw [T.map_id]; rfl
  map_comp D₁ D₂ k := by rw [T.map_comp]; rfl
  map_tensor D₁ D₂ k := by rw [T.map_tensor]; rfl

variable (T : Target)

/-- Interpretation commutes with complete circuit emission. -/
theorem expand_circuit (qs : List Quantifier) (ms : List (List Bool)) :
    T.language.expand (circuit qs ms) =
      (T.map (OutputLatch.diagram.comp (Matrix.body qs ms))).toWord Prim.interp 0 :=
  T.wordTarget.expand_circuit qs ms

end Interpretation
end Cslib.Complexity.NCL.QBF.Emit
