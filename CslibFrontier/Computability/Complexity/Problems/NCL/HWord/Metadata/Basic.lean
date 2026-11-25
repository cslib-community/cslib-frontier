/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.AndOr
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Program

/-!
# Natural-coordinate metadata for actual word-network emission

Positions are natural numbers in the explicit list program. The finite local tags use the
same row, character, and relation order as the certified source graph. Intermediate wire names
are unary sparse addresses; the block emitter compacts them by first-index lookup.

## Main definitions

* `HWord.Metadata.Branch`: natural-coordinate relation-side data.
* `HWord.Metadata.block`: graph metadata for one source cell.
* `HWord.Metadata.blocks`: actual row-major graph metadata.
-/

public section

namespace Cslib.Complexity.NCL.HWord.Metadata

open SelectorNetwork.AndOr _root_.Turing.MultiTapeTM

/-- The mathematical row/character/relation tag used by `PortGraph.rowTag`. -/
abbrev Tag (q : ℕ) := Fin 1 ⊕ Fin q ⊕ (Fin q × Fin q)

/-- A relation branch with an explicit natural position. -/
structure Branch (q : ℕ) where
  /-- Position of the relation cell owning this branch. -/
  position : ℕ
  /-- Left symbol of the relation. -/
  first : Fin q
  /-- Right symbol of the relation. -/
  second : Fin q
  /-- Which character endpoint this branch meets. -/
  side : Bool

/-- A unary position and fixed finite symbols and side. -/
enc_structure encBranch (q : ℕ) : Branch q where
  position : encUnary, first : (encFinEnum (Fin q)), second : (encFinEnum (Fin q)), side : encBool

/-- The fixed local tags in the certified source order. -/
@[expose] def tags (q : ℕ) : List (Tag q) := List.ofFn (PortGraph.tagEquiv q).symm

/-- Number of source cells in one row. -/
abbrev rowWidth (q : ℕ) : ℕ := 1 + (q + q * q)

/-- The bounded local wire interval used for sparse names. -/
abbrev stride (q : ℕ) : ℕ := 66 + 69 * q

/-- Sparse name of a local owner and slot. -/
@[expose] def name {q : ℕ} (position : ℕ) (tag : Tag q) (slot : ℕ) : ℕ :=
  stride q * ((PortGraph.tagEquiv q tag).val + rowWidth q * position) + slot

/-- Sparse name of a selector owned by its character cell. -/
@[expose] def selector {q : ℕ} (position : ℕ) (symbol : Fin q) : ℕ :=
  name position (.inr (.inl symbol)) 0

/-- Sparse name of a unit edge owned by its relation cell. -/
@[expose] def branchName {q : ℕ} (b : Branch q) : ℕ :=
  name b.position (.inr (.inr (b.first, b.second))) b.side.toNat

/-- Every relation branch in the source network's position/symbol/side order. -/
@[expose] def branches (q n : ℕ) : List (Branch q) :=
  (List.range n).flatMap fun position =>
    ((List.finRange q).product (List.finRange q)).flatMap fun symbols =>
      [⟨position, symbols.1, symbols.2, false⟩, ⟨position, symbols.1, symbols.2, true⟩]

/-- The right endpoint advances one row except at the final-row fallback. -/
@[expose] def endpointRow {q : ℕ} (n : ℕ) (b : Branch q) : ℕ :=
  if b.side && decide (b.position + 1 < n) then b.position + 1 else b.position

/-- Symbol of the character endpoint of a relation branch. -/
@[expose] def endpointSymbol {q : ℕ} (b : Branch q) : Fin q :=
  if b.side then b.second else b.first

/-- Unit branches meeting one character, in the actual source enumeration order. -/
@[expose] def incident {q : ℕ} (n position : ℕ) (symbol : Fin q) : List (Branch q) :=
  (branches q n).filter fun b => decide (endpointRow n b = position ∧ endpointSymbol b = symbol)

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Shared wire names in the local top/bottom boundary reference order. -/
@[expose] def boundaryNames (n position : ℕ) : Tag q → List ℕ
  | .inl _ => ((List.finRange q).filter (fun a => decide (a.val ≠ 0))).map
      (selector position) ++ [selector position ⟨0, hq⟩]
  | .inr (.inl a) => (incident n position a).map branchName ++ [selector position a]
  | .inr (.inr (a, b)) =>
      [branchName ⟨position, a, b, false⟩, branchName ⟨position, a, b, true⟩]

/-- The same finite implementation shapes, with bounded total arity on arbitrary coordinates. -/
@[expose] def shape (n position : ℕ) : Tag q → Cell.Bounded (3 * q)
  | .inl _ => ⟨.row ((List.finRange q).filter (fun a => decide (a.val ≠ 0))).length, by
      simp only [Cell.top, Gadgets.OrTree.length_bundle]
      have h := List.length_filter_le (fun a : Fin q => decide (a.val ≠ 0)) (List.finRange q)
      rw [List.length_finRange] at h
      omega⟩
  | .inr (.inl a) => ⟨.character (min (incident n position a).length (3 * q)), by
      simpa only [Cell.top, Gadgets.OrTree.length_bundle] using Nat.min_le_right _ _⟩
  | .inr (.inr (a, b)) => ⟨.relation (decide (position + 1 < n ∧ ¬H.Adj a b)), Nat.zero_le _⟩

/-- Original shared names emitted at their owner cell. -/
@[expose] def ownedNames (position : ℕ) : Tag q → List ℕ
  | .inl _ => []
  | .inr (.inl a) => [selector position a]
  | .inr (.inr (a, b)) =>
      [branchName ⟨position, a, b, false⟩, branchName ⟨position, a, b, true⟩]

/-- Concrete graph-emission block for one source coordinate. -/
@[expose] def block (n position : ℕ) (tag : Tag q) : Program.Block (3 * q) where
  shape := shape H hq n position tag
  context :=
    { boundaryNames := boundaryNames hq n position tag
      privateBase := name position tag 2
      reverse := tag.isLeft
      anchor := if tag.isLeft then selector position ⟨0, hq⟩ else 0 }
  ownedNames := ownedNames position tag
  row := position

/-- Complete row-major block list for a word of length `n`. -/
@[expose] def blocks (n : ℕ) : List (Program.Block (3 * q)) :=
  (List.range n).flatMap fun position => (tags q).map (block H hq n position)

end Cslib.Complexity.NCL.HWord.Metadata
