/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Metadata.Correctness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Polynomial-time word-network metadata scans

The alphabet and each local tag are fixed. Natural positions are scanned by unary ranges;
branch incidence is an explicit filter, and bounded cell templates are emitted by the standard
block-list program.

## Main results

* `HWord.Metadata.computableInPolyTime_blocks`: actual graph metadata at a given word length.
-/

public section

namespace Cslib.Complexity.NCL.HWord.Metadata

open SelectorNetwork.AndOr _root_.Turing.MultiTapeTM

private theorem computableInPolyTime_branches (q : ℕ) :
    ComputableInPolyTime (branches q) encUnary (encList (encBranch q)) := by
  unfold branches
  exact ComputableInPolyTime.flatMapWithInput ComputableInPolyTime.range
    (ComputableInPolyTime.flatMapConst _ fun _ _ => by fun_prop)

@[local fun_prop]
private theorem computableInPolyTime_endpointRow (q : ℕ) :
    ComputableInPolyTime (fun p : ℕ × Branch q => endpointRow p.1 p.2)
      (encPair encUnary (encBranch q)) encUnary := by
  unfold endpointRow
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_endpointSymbol (q : ℕ) :
    ComputableInPolyTime (endpointSymbol (q := q)) (encBranch q) (encFinEnum (Fin q)) := by
  unfold endpointSymbol
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_branchName (q : ℕ) :
    ComputableInPolyTime (branchName (q := q)) (encBranch q) encUnary := by
  have ht : ComputableInPolyTime (fun b : Branch q =>
      (PortGraph.tagEquiv q (.inr (.inr (b.first, b.second)))).val) (encBranch q) encUnary :=
    (ComputableInPolyTime.of_finite
      (fun p : Fin q × Fin q => (PortGraph.tagEquiv q (.inr (.inr p))).val)).comp
      (g := fun b : Branch q => (b.first, b.second)) (by fun_prop)
  unfold branchName name
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_incident (q : ℕ) (a : Fin q) :
    ComputableInPolyTime (fun p : ℕ × ℕ => incident p.1 p.2 a)
      (encPair encUnary encUnary) (encList (encBranch q)) := by
  unfold incident
  apply ComputableInPolyTime.filterWithInput
    ((computableInPolyTime_branches q).comp (by fun_prop))
  have hr := (computableInPolyTime_endpointRow q).comp
    (encIn := encPair (encPair encUnary encUnary) (encBranch q))
    (g := fun p : (ℕ × ℕ) × Branch q => (p.1.1, p.2)) (by fun_prop)
  fun_prop

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

private theorem computableInPolyTime_boundaryNames (tag : Tag q) :
    ComputableInPolyTime (fun p : ℕ × ℕ => boundaryNames hq p.1 p.2 tag)
      (encPair encUnary encUnary) (encList encUnary) := by
  rcases tag with _ | (a | ⟨a, b⟩)
  · have hm : ComputableInPolyTime (fun p : ℕ × ℕ =>
        ((List.finRange q).filter (fun a => decide (a.val ≠ 0))).map (selector p.2))
        (encPair encUnary encUnary) (encList encUnary) :=
      ComputableInPolyTime.mapConst _ fun _ _ => by
        unfold selector name
        fun_prop
    unfold boundaryNames selector name
    fun_prop
  · have hm := (ComputableInPolyTime.map (computableInPolyTime_branchName q)).comp
      (computableInPolyTime_incident q a)
    unfold boundaryNames selector name
    fun_prop
  · unfold boundaryNames
    fun_prop

private theorem computableInPolyTime_shape (tag : Tag q) :
    ComputableInPolyTime (fun p : ℕ × ℕ => shape H hq p.1 p.2 tag)
      (encPair encUnary encUnary) (Cell.encBounded (3 * q)) := by
  rcases tag with _ | (a | ⟨a, b⟩)
  · exact ComputableInPolyTime.const _
  · exact ((ComputableInPolyTime.sumInr encUnary (encSum encUnary encBool)).comp
      ((ComputableInPolyTime.sumInl encUnary encBool).comp (g := fun p : ℕ × ℕ =>
        min (incident p.1 p.2 a).length (3 * q)) (by fun_prop))).of_enc_eq fun _ => rfl
  · exact ((ComputableInPolyTime.sumInr encUnary (encSum encUnary encBool)).comp
      ((ComputableInPolyTime.sumInr encUnary encBool).comp (g := fun p : ℕ × ℕ =>
        decide (p.2 + 1 < p.1 ∧ ¬H.Adj a b)) (by fun_prop))).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_ownedNames (tag : Tag q) :
    ComputableInPolyTime (fun p : ℕ × ℕ => ownedNames p.2 tag)
      (encPair encUnary encUnary) (encList encUnary) := by
  rcases tag with _ | (a | ⟨a, b⟩)
  · exact ComputableInPolyTime.const []
  · dsimp only [ownedNames, selector, name]
    fun_prop
  · dsimp only [ownedNames, branchName, name]
    fun_prop

private theorem computableInPolyTime_block (tag : Tag q) :
    ComputableInPolyTime (fun p : ℕ × ℕ => block H hq p.1 p.2 tag)
      (encPair encUnary encUnary) (Program.encBlock (3 * q)) := by
  dsimp only [block, selector, name]
  refine Program.encBlock_mk_polyTime (3 * q) (computableInPolyTime_shape H hq tag) ?_
    (computableInPolyTime_ownedNames tag) (ComputableInPolyTime.snd _ _)
  refine encTemplateContext_mk_polyTime (computableInPolyTime_boundaryNames hq tag) (by fun_prop)
    (ComputableInPolyTime.const _) ?_
  split_ifs <;> fun_prop

/-- The complete actual graph metadata is polynomial-time in the unary word length. -/
theorem computableInPolyTime_blocks : ComputableInPolyTime (blocks H hq) encUnary
    (encList (Program.encBlock (3 * q))) := by
  unfold blocks
  exact ComputableInPolyTime.flatMapWithInput ComputableInPolyTime.range
    (ComputableInPolyTime.mapConst _ fun tag _ => computableInPolyTime_block H hq tag)

/-- The actual certified finite standard graph is polynomial-time in the unary word length. -/
theorem computableInPolyTime_graph : ComputableInPolyTime
    (fun n => AndOrGraph.ofFinite (Planarized.finiteGraph (n := n) H hq)) encUnary
      encAndOrGraph :=
  ((Program.computableInPolyTime_graph (3 * q)).comp
    (computableInPolyTime_blocks H hq)).of_enc_eq fun n =>
      congrArg encAndOrGraph (graph_blocks_eq (n := n) H hq).symm

/-- Unary graph length together with a word in the shared framed alphabet encoding. -/
abbrev encStateInput (q : ℕ) : (ℕ × List (Fin q)) ↪ List Bool := encPair encUnary (encWord q)

private abbrev encStatePosition (q : ℕ) : ((ℕ × List (Fin q)) × ℕ) ↪ List Bool :=
  encPair (encStateInput q) encUnary

@[local fun_prop]
private theorem computableInPolyTime_selectedAt (a : Fin q) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => selected hq p.1.2 p.2 a)
      (encStatePosition q) encBool := by
  unfold selected
  fun_prop

private theorem computableInPolyTime_branchBit : ComputableInPolyTime
    (fun p : (ℕ × List (Fin q)) × Branch q => branchBit hq p.1.1 p.1.2 p.2)
      (encPair (encStateInput q) (encBranch q)) encBool := by
  have hr := (computableInPolyTime_endpointRow q).comp
    (encIn := encPair (encStateInput q) (encBranch q))
    (g := fun p : (ℕ × List (Fin q)) × Branch q => (p.1.1, p.2)) (by fun_prop)
  unfold branchBit selected
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_fixedBranchBit (a b : Fin q) (side : Bool) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
      branchBit hq p.1.1 p.1.2 ⟨p.2, a, b, side⟩) (encStatePosition q) encBool :=
  (computableInPolyTime_branchBit hq).comp
    (g := fun p : (ℕ × List (Fin q)) × ℕ => (p.1, (⟨p.2, a, b, side⟩ : Branch q))) (by fun_prop)

private theorem computableInPolyTime_relationBits (a b : Fin q) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
      [branchBit hq p.1.1 p.1.2 ⟨p.2, a, b, false⟩,
        branchBit hq p.1.1 p.1.2 ⟨p.2, a, b, true⟩]) (encStatePosition q) (encList encBool) := by
  fun_prop

private theorem computableInPolyTime_boundaryBits (tag : Tag q) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
      boundaryBits hq p.1.1 p.1.2 p.2 tag) (encStatePosition q) (encList encBool) := by
  rcases tag with _ | (a | ⟨a, b⟩)
  · have hm := ComputableInPolyTime.mapConst
      ((List.finRange q).filter fun a => decide (a.val ≠ 0))
      fun a _ => computableInPolyTime_selectedAt hq a
    unfold boundaryBits
    fun_prop
  · have hm : ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
        (incident p.1.1 p.2 a).map (branchBit hq p.1.1 p.1.2))
        (encStatePosition q) (encList encBool) :=
      ComputableInPolyTime.mapWithInput
        ((computableInPolyTime_incident q a).comp (encIn := encStatePosition q)
          (g := fun p : (ℕ × List (Fin q)) × ℕ => (p.1.1, p.2)) (by fun_prop))
        ((computableInPolyTime_branchBit hq).comp
          (encIn := encPair (encStatePosition q) (encBranch q))
          (g := fun p : ((ℕ × List (Fin q)) × ℕ) × Branch q => (p.1.1, p.2)) (by fun_prop))
    unfold boundaryBits
    fun_prop
  · exact computableInPolyTime_relationBits hq a b

private theorem computableInPolyTime_ownedBits (tag : Tag q) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => ownedBits hq p.1.1 p.1.2 p.2 tag)
      (encStatePosition q) (encList encBool) := by
  rcases tag with _ | (a | ⟨a, b⟩)
  · exact ComputableInPolyTime.const []
  · unfold ownedBits
    fun_prop
  · exact computableInPolyTime_relationBits hq a b

private theorem computableInPolyTime_stateBlock (tag : Tag q) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => stateBlock H hq p.1.1 p.1.2 p.2 tag)
      (encStatePosition q) (Program.encStateBlock (3 * q)) := by
  unfold stateBlock
  exact Program.encStateBlock_mk_polyTime (3 * q)
    ((computableInPolyTime_shape H hq tag).comp
      (g := fun p : (ℕ × List (Fin q)) × ℕ => (p.1.1, p.2)) (by fun_prop))
    (computableInPolyTime_boundaryBits hq tag) (computableInPolyTime_ownedBits hq tag)

/-- The canonical direction metadata is polynomial-time for an explicit length and word list. -/
private theorem computableInPolyTime_stateBlocks : ComputableInPolyTime
    (fun p : ℕ × List (Fin q) => stateBlocks H hq p.1 p.2) (encStateInput q)
      (encList (Program.encStateBlock (3 * q))) := by
  unfold stateBlocks
  exact ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.mapConst _ fun tag _ => computableInPolyTime_stateBlock H hq tag)

/-- Canonical directions of the actual numbered graph have a standard polynomial-time emitter. -/
theorem computableInPolyTime_bits : ComputableInPolyTime
    (fun p : ℕ × List (Fin q) => Program.bits (stateBlocks H hq p.1 p.2))
      (encStateInput q) (encList encBool) := by
  simpa only [Function.comp_def] using (Program.computableInPolyTime_bits (3 * q)).comp
    (computableInPolyTime_stateBlocks H hq)

end Cslib.Complexity.NCL.HWord.Metadata
