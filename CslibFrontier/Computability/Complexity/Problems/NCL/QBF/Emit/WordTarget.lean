/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Layout

/-!
# Source emission into arbitrary word alphabets

A word interpretation preserves identity, stacking and juxtaposition, including wire offsets.
The source instruction correctness theorem is shared by primitive and marked word emission.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.WordTarget`: an interpretation into list words.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.WordTarget.expand_circuit`: exact source emission.
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit.Interpretation

open Diagram

/-- A word-valued interpretation preserving the three diagram operations and their offsets. -/
structure WordTarget (α : Type) where
  /-- Emit a source diagram at a wire offset. -/
  map : {a b : List Color} → Diagram Gate a b → ℕ → List α
  /-- Identity wires emit no layers. -/
  map_id (a : List Color) (k : ℕ) : map (Diagram.id a) k = []
  /-- Sequential parts emit consecutive words. -/
  map_comp {a b c : List Color} (D₁ : Diagram Gate a b) (D₂ : Diagram Gate b c) (k : ℕ) :
    map (D₁.comp D₂) k = map D₁ k ++ map D₂ k
  /-- The right parallel part starts after the left part's output wires. -/
  map_tensor {a b c d : List Color} (D₁ : Diagram Gate a b) (D₂ : Diagram Gate c d) (k : ℕ) :
    map (D₁.tensor D₂) k = map D₁ k ++ map D₂ (k + b.length)

variable {α : Type}

/-- Emit one of the fixed source fragments. -/
@[expose] def WordTarget.opcodeWord (T : WordTarget α) (op : Opcode) (k : ℕ) : List α :=
  T.map op.data.diagram k

/-- Interpret a source program in the chosen word alphabet. -/
@[expose] def WordTarget.expand (T : WordTarget α) (p : Program) : List α :=
  p.flatMap fun i => T.opcodeWord i.2 i.1

namespace WordTarget

variable (T : WordTarget α)

private theorem expand_layout {a b : List Color} {D : Diagram Gate a b}
    {s : D.Edge → Bool} {k : ℕ} {p : Program} {recorded : Bool} (h : Layout recorded D s k p) :
    T.expand p = T.map D k := by
  induction h with
  | id => exact (T.map_id _ _).symm
  | cell => exact List.flatMap_singleton _ _
  | comp _ _ ih₁ ih₂ =>
    rw [T.map_comp, ← ih₁, ← ih₂]
    exact List.flatMap_append
  | tensor _ _ ih₁ ih₂ =>
    rw [T.map_tensor, ← ih₁, ← ih₂]
    exact List.flatMap_append

/-- Interpretation commutes with terminal emission. -/
theorem expand_terminal (k p : ℕ) (ms : List (List Bool)) :
    T.expand (terminal k p ms) = (T.map (Matrix.terminalBase p ms)) k :=
  expand_layout T (Layout.terminalBase (recorded := false) k p ms)

/-- Interpretation commutes with complete circuit emission. -/
theorem expand_circuit (qs : List Quantifier) (ms : List (List Bool)) :
    T.expand (circuit qs ms) = (T.map (OutputLatch.diagram.comp (Matrix.body qs ms))) 0 :=
  expand_layout T (Layout.circuit false qs ms)

end WordTarget

end Cslib.Complexity.NCL.QBF.Emit.Interpretation
