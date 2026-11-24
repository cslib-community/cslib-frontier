/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Metadata.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Problem

/-!
# Canonical word-network direction metadata

Selectors read one word symbol, and relation branches read their character endpoints. Only the
row anchor is complemented by the row implementation's boundary reference direction. Missing
symbols use the same fixed zero-symbol convention as the total target-word map.

## Main definitions

* `HWord.Metadata.stateBlocks`: canonical direction blocks in actual owner order.
-/

public section

namespace Cslib.Complexity.NCL.HWord.Metadata

open SelectorNetwork.AndOr

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Whether a natural-coordinate character is selected by the supplied word list. -/
@[expose] def selected (word : List (Fin q)) (position : ℕ) (symbol : Fin q) : Bool :=
  decide (word.getD position ⟨0, hq⟩ = symbol)

/-- A unit branch's canonical direction is the selection at its character endpoint. -/
@[expose] def branchBit (n : ℕ) (word : List (Fin q)) (b : Branch q) : Bool :=
  selected hq word (endpointRow n b) (endpointSymbol b)

/-- Canonical local boundary directions in top-then-bottom reference order. -/
@[expose] def boundaryBits (n : ℕ) (word : List (Fin q)) (position : ℕ) : Tag q → List Bool
  | .inl _ => ((List.finRange q).filter (fun a => decide (a.val ≠ 0))).map
      (selected hq word position) ++ [!(selected hq word position ⟨0, hq⟩)]
  | .inr (.inl a) => (incident n position a).map (branchBit hq n word) ++
      [selected hq word position a]
  | .inr (.inr (a, b)) =>
      [branchBit hq n word ⟨position, a, b, false⟩,
        branchBit hq n word ⟨position, a, b, true⟩]

/-- Canonical directions of shared wires created at one source cell. -/
@[expose] def ownedBits (n : ℕ) (word : List (Fin q)) (position : ℕ) : Tag q → List Bool
  | .inl _ => []
  | .inr (.inl a) => [selected hq word position a]
  | .inr (.inr (a, b)) =>
      [branchBit hq n word ⟨position, a, b, false⟩,
        branchBit hq n word ⟨position, a, b, true⟩]

/-- One canonical orientation block, using the graph's actual bounded implementation shape. -/
@[expose] def stateBlock (n : ℕ) (word : List (Fin q)) (position : ℕ) (tag : Tag q) :
    Program.StateBlock (3 * q) where
  shape := shape H hq n position tag
  boundary := boundaryBits hq n word position tag
  owned := ownedBits hq n word position tag

/-- Complete canonical directions in the graph emitter's exact owner and creation order. -/
@[expose] def stateBlocks (n : ℕ) (word : List (Fin q)) : List (Program.StateBlock (3 * q)) :=
  (List.range n).flatMap fun position => (tags q).map (stateBlock H hq n word position)

end Cslib.Complexity.NCL.HWord.Metadata
