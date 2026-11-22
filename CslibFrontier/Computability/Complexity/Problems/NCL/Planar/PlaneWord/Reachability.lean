/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Compile
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Encoding
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Plane

/-!
# Plane AND/OR NCL decision problems

Instances contain a structural word describing adjacent single-vertex layers. Its color stack
checks from the empty boundary to the empty boundary. Compilation supplies the finite graph
for the three reachability questions.

## Main definitions

* `Cslib.Complexity.NCL.PlaneWordAndOrNCL`: configuration-to-configuration plane NCL.
* `Cslib.Complexity.NCL.PlaneWordAndOrNCLEdge`: configuration-to-edge plane NCL.
* `Cslib.Complexity.NCL.PlaneWordAndOrNCLEdgeToEdge`: directional edge-to-edge plane NCL.
* `Cslib.Complexity.NCL.encPlaneWordAndOrNCL` and its edge variants: structural instance encodings.

## References

* These are the three problems of [Hearn and Demaine][HearnDemaine2005, Section 2.1].
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

/-- A well-typed closed plane word compiling to valid, loop-free finite AND/OR graph data. -/
@[expose] def Word.ValidPlane (w : Word) : Prop :=
  w.checkPlane = true ∧ w.WellTyped [] [] ∧
    (Word.compile w).Valid ∧ (Word.compile w).graph.LoopFree

/-- A plane word with initial and target configuration lists. -/
structure PlaneWordAndOrNCL.Instance where
  /-- The structural plane word. -/
  word : Word
  /-- The initial orientation bits. -/
  initial : List Bool
  /-- The target orientation bits. -/
  target : List Bool

/-- A plane word with an initial configuration and an edge to reverse. -/
structure PlaneWordAndOrNCLEdge.Instance where
  /-- The structural plane word. -/
  word : Word
  /-- The initial orientation bits. -/
  initial : List Bool
  /-- The edge to reverse. -/
  edge : ℕ

/-- A plane word with two prescribed edge directions. -/
structure PlaneWordAndOrNCLEdgeToEdge.Instance where
  /-- The structural plane word. -/
  word : Word
  /-- The prescribed direction in the starting configuration. -/
  first : Port ℕ
  /-- The prescribed direction in the reachable configuration. -/
  second : Port ℕ

/-- A closed plane word with a legal initial configuration can reach its fixed target. -/
@[expose] def PlaneWordAndOrNCL : Set PlaneWordAndOrNCL.Instance := {x |
  x.word.checkPlane = true ∧ x.word.WellTyped [] [] ∧
    (⟨Word.compile x.word, x.initial, x.target⟩ : AndOrNCL.Instance) ∈ AndOrNCL}

/-- A closed plane word with a legal initial configuration can reverse its named edge. -/
@[expose] def PlaneWordAndOrNCLEdge : Set PlaneWordAndOrNCLEdge.Instance := {x |
  x.word.checkPlane = true ∧ x.word.WellTyped [] [] ∧
    (⟨Word.compile x.word, x.initial, x.edge⟩ : AndOrNCLEdge.Instance) ∈ AndOrNCLEdge}

/-- A closed plane word admits a legal start and reachable end with the prescribed directions. -/
@[expose] def PlaneWordAndOrNCLEdgeToEdge : Set PlaneWordAndOrNCLEdgeToEdge.Instance := {x |
  x.word.checkPlane = true ∧ x.word.WellTyped [] [] ∧
    (⟨Word.compile x.word, x.first, x.second⟩ : AndOrNCLEdgeToEdge.Instance) ∈ AndOrNCLEdgeToEdge}

/-- Encode a plane word and its initial and target configuration lists. -/
enc_structure encPlaneWordAndOrNCL : PlaneWordAndOrNCL.Instance where
  word : encWord, initial : (encList encBool), target : (encList encBool)

/-- Encode a plane word, its initial configuration and a target edge number. -/
enc_structure encPlaneWordAndOrNCLEdge : PlaneWordAndOrNCLEdge.Instance where
  word : encWord, initial : (encList encBool), edge : encNat

/-- Encode a plane word and two edge numbers with their prescribed directions. -/
enc_structure encPlaneWordAndOrNCLEdgeToEdge : PlaneWordAndOrNCLEdgeToEdge.Instance where
  word : encWord, first : (encPort encNat), second : (encPort encNat)

end Cslib.Complexity.NCL
