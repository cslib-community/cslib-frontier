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
  apply ComputableInPolyTime.flatMapWithInput ComputableInPolyTime.range
  apply ComputableInPolyTime.flatMapConst
  intro symbols _
  fun_prop

private theorem computableInPolyTime_endpointRow (q : ℕ) :
    ComputableInPolyTime (fun p : ℕ × Branch q => endpointRow p.1 p.2)
      (encPair encUnary (encBranch q)) encUnary := by
  unfold endpointRow
  fun_prop

private theorem computableInPolyTime_endpointSymbol (q : ℕ) :
    ComputableInPolyTime (endpointSymbol (q := q)) (encBranch q) (encFinEnum (Fin q)) := by
  unfold endpointSymbol
  fun_prop

private theorem computableInPolyTime_branchName (q : ℕ) :
    ComputableInPolyTime (branchName (q := q)) (encBranch q) encUnary := by
  have ht : ComputableInPolyTime (fun b : Branch q =>
      (PortGraph.tagEquiv q (.inr (.inr (b.first, b.second)))).val) (encBranch q) encUnary := by
    have h := ComputableInPolyTime.of_finite (encIn := encPair
      (encFinEnum (Fin q)) (encFinEnum (Fin q))) (encOut := encUnary)
      (fun p : Fin q × Fin q => (PortGraph.tagEquiv q (.inr (.inr p))).val)
    simpa only [Function.comp_def] using h.comp
      ((encBranch_first_polyTime q ComputableInPolyTime.id').prod
        (encBranch_second_polyTime q ComputableInPolyTime.id'))
  unfold branchName name
  fun_prop

private theorem computableInPolyTime_incident (q : ℕ) (a : Fin q) :
    ComputableInPolyTime (fun p : ℕ × ℕ => incident p.1 p.2 a)
      (encPair encUnary encUnary) (encList (encBranch q)) := by
  unfold incident
  apply ComputableInPolyTime.filterWithInput
    ((computableInPolyTime_branches q).comp (ComputableInPolyTime.fst _ _))
  have hr : ComputableInPolyTime (fun p : (ℕ × ℕ) × Branch q => endpointRow p.1.1 p.2)
      (encPair (encPair encUnary encUnary) (encBranch q)) encUnary := by
    simpa only [Function.comp_def] using (computableInPolyTime_endpointRow q).comp
      (show ComputableInPolyTime (fun p : (ℕ × ℕ) × Branch q => (p.1.1, p.2))
        (encPair (encPair encUnary encUnary) (encBranch q))
        (encPair encUnary (encBranch q)) from by fun_prop)
  have hs := (computableInPolyTime_endpointSymbol q).comp
    (ComputableInPolyTime.snd (encPair encUnary encUnary) (encBranch q))
  fun_prop

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

private theorem computableInPolyTime_boundaryNames (tag : Tag q) :
    ComputableInPolyTime (fun p : ℕ × ℕ => boundaryNames hq p.1 p.2 tag)
      (encPair encUnary encUnary) (encList encUnary) := by
  rcases tag with _ | (a | ⟨a, b⟩)
  · have hm : ComputableInPolyTime (fun p : ℕ × ℕ =>
        ((List.finRange q).filter (fun a => decide (a.val ≠ 0))).map (selector p.2))
        (encPair encUnary encUnary) (encList encUnary) := by
      apply ComputableInPolyTime.mapConst
      intro a _
      unfold selector name
      fun_prop
    change ComputableInPolyTime (fun p : ℕ × ℕ => _ ++ [selector p.2 ⟨0, hq⟩]) _ _
    unfold selector name
    fun_prop
  · have hm := (ComputableInPolyTime.map (computableInPolyTime_branchName q)).comp
      (computableInPolyTime_incident q a)
    change ComputableInPolyTime (fun p : ℕ × ℕ =>
      (incident p.1 p.2 a).map branchName ++ [selector p.2 a]) _ _
    unfold selector name
    fun_prop
  · change ComputableInPolyTime (fun p : ℕ × ℕ =>
      [branchName ⟨p.2, a, b, false⟩, branchName ⟨p.2, a, b, true⟩]) _ _
    dsimp only [branchName, name]
    fun_prop

private theorem computableInPolyTime_shape (tag : Tag q) :
    ComputableInPolyTime (fun p : ℕ × ℕ => shape H hq p.1 p.2 tag)
      (encPair encUnary encUnary) (Cell.encBounded (3 * q)) := by
  rcases tag with _ | (a | ⟨a, b⟩)
  · exact ComputableInPolyTime.const _
  · have hl : ComputableInPolyTime (fun p : ℕ × ℕ =>
        min (incident p.1 p.2 a).length (3 * q)) (encPair encUnary encUnary) encUnary := by
      have hi := computableInPolyTime_incident q a
      fun_prop
    have h := (ComputableInPolyTime.sumInr encUnary (encSum encUnary encBool)).comp
      ((ComputableInPolyTime.sumInl encUnary encBool).comp hl)
    exact h.of_enc_eq (fun _ => rfl)
  · have hb : ComputableInPolyTime (fun p : ℕ × ℕ =>
        decide (p.2 + 1 < p.1 ∧ ¬H.Adj a b)) (encPair encUnary encUnary) encBool := by fun_prop
    have h := (ComputableInPolyTime.sumInr encUnary (encSum encUnary encBool)).comp
      ((ComputableInPolyTime.sumInr encUnary encBool).comp hb)
    exact h.of_enc_eq (fun _ => rfl)

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
  have hs := computableInPolyTime_shape H hq tag
  have hb := computableInPolyTime_boundaryNames hq tag
  have ho := computableInPolyTime_ownedNames tag
  dsimp only [block, selector, name]
  refine Program.encBlock_mk_polyTime (3 * q) hs ?_ ho (ComputableInPolyTime.snd _ _)
  refine encTemplateContext_mk_polyTime hb (by fun_prop) (ComputableInPolyTime.const _) ?_
  split_ifs <;> fun_prop

/-- The complete actual graph metadata is polynomial-time in the unary word length. -/
theorem computableInPolyTime_blocks : ComputableInPolyTime (blocks H hq) encUnary
    (encList (Program.encBlock (3 * q))) := by
  unfold blocks
  apply ComputableInPolyTime.flatMapWithInput ComputableInPolyTime.range
  apply ComputableInPolyTime.mapConst
  intro tag _
  exact computableInPolyTime_block H hq tag

/-- The actual certified finite standard graph is polynomial-time in the unary word length. -/
theorem computableInPolyTime_graph : ComputableInPolyTime
    (fun n => AndOrGraph.ofFinite (Planarized.finiteGraph (n := n) H hq)) encUnary
      encAndOrGraph := by
  have h := (Program.computableInPolyTime_graph (3 * q)).comp
    (computableInPolyTime_blocks H hq)
  exact h.of_enc_eq (fun n => congrArg encAndOrGraph (graph_blocks_eq (n := n) H hq).symm)

/-- Unary graph length together with a word in the shared framed alphabet encoding. -/
abbrev encStateInput (q : ℕ) : (ℕ × List (Fin q)) ↪ List Bool := encPair encUnary (encWord q)

private abbrev encStatePosition (q : ℕ) : ((ℕ × List (Fin q)) × ℕ) ↪ List Bool :=
  encPair (encStateInput q) encUnary

private theorem computableInPolyTime_selectedAt (a : Fin q) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => selected hq p.1.2 p.2 a)
      (encStatePosition q) encBool := by
  unfold selected
  fun_prop

private theorem computableInPolyTime_branchBit : ComputableInPolyTime
    (fun p : (ℕ × List (Fin q)) × Branch q => branchBit hq p.1.1 p.1.2 p.2)
      (encPair (encStateInput q) (encBranch q)) encBool := by
  have hr : ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × Branch q =>
      endpointRow p.1.1 p.2) (encPair (encStateInput q) (encBranch q)) encUnary := by
    simpa only [Function.comp_def] using (computableInPolyTime_endpointRow q).comp
      (show ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × Branch q => (p.1.1, p.2))
        (encPair (encStateInput q) (encBranch q)) (encPair encUnary (encBranch q)) from by fun_prop)
  have hs := (computableInPolyTime_endpointSymbol q).comp
    (ComputableInPolyTime.snd (encStateInput q) (encBranch q))
  unfold branchBit selected
  fun_prop

private theorem computableInPolyTime_fixedBranchBit (a b : Fin q) (side : Bool) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
      branchBit hq p.1.1 p.1.2 ⟨p.2, a, b, side⟩) (encStatePosition q) encBool := by
  have hp : ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
      (p.1, (⟨p.2, a, b, side⟩ : Branch q))) (encStatePosition q)
      (encPair (encStateInput q) (encBranch q)) := by fun_prop
  simpa only [Function.comp_def] using (computableInPolyTime_branchBit hq).comp hp

private theorem computableInPolyTime_relationBits (a b : Fin q) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
      [branchBit hq p.1.1 p.1.2 ⟨p.2, a, b, false⟩,
        branchBit hq p.1.1 p.1.2 ⟨p.2, a, b, true⟩]) (encStatePosition q) (encList encBool) := by
  have hf := computableInPolyTime_fixedBranchBit hq a b false
  have ht := computableInPolyTime_fixedBranchBit hq a b true
  fun_prop

private theorem computableInPolyTime_boundaryBits (tag : Tag q) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
      boundaryBits hq p.1.1 p.1.2 p.2 tag) (encStatePosition q) (encList encBool) := by
  rcases tag with _ | (a | ⟨a, b⟩)
  · have hm : ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
        ((List.finRange q).filter (fun a => decide (a.val ≠ 0))).map (selected hq p.1.2 p.2))
        (encStatePosition q) (encList encBool) := by
      apply ComputableInPolyTime.mapConst
      intro a _
      exact computableInPolyTime_selectedAt hq a
    have ha := computableInPolyTime_selectedAt hq ⟨0, hq⟩
    change ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
      _ ++ [!(selected hq p.1.2 p.2 ⟨0, hq⟩)]) _ _
    fun_prop
  · have hi : ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => incident p.1.1 p.2 a)
        (encStatePosition q) (encList (encBranch q)) := by
      simpa only [Function.comp_def] using (computableInPolyTime_incident q a).comp
        (show ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => (p.1.1, p.2))
          (encStatePosition q) (encPair encUnary encUnary) from by fun_prop)
    have hm : ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
        (incident p.1.1 p.2 a).map (branchBit hq p.1.1 p.1.2))
        (encStatePosition q) (encList encBool) := by
      apply ComputableInPolyTime.mapWithInput hi
      have hp : ComputableInPolyTime (fun p : ((ℕ × List (Fin q)) × ℕ) × Branch q =>
          (p.1.1, p.2)) (encPair (encStatePosition q) (encBranch q))
          (encPair (encStateInput q) (encBranch q)) := by fun_prop
      simpa only [Function.comp_def] using (computableInPolyTime_branchBit hq).comp hp
    have ha := computableInPolyTime_selectedAt hq a
    change ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ =>
      _ ++ [selected hq p.1.2 p.2 a]) _ _
    fun_prop
  · exact computableInPolyTime_relationBits hq a b

private theorem computableInPolyTime_ownedBits (tag : Tag q) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => ownedBits hq p.1.1 p.1.2 p.2 tag)
      (encStatePosition q) (encList encBool) := by
  rcases tag with _ | (a | ⟨a, b⟩)
  · exact ComputableInPolyTime.const []
  · have ha := computableInPolyTime_selectedAt hq a
    change ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => [selected hq p.1.2 p.2 a]) _ _
    fun_prop
  · exact computableInPolyTime_relationBits hq a b

private theorem computableInPolyTime_stateBlock (tag : Tag q) :
    ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => stateBlock H hq p.1.1 p.1.2 p.2 tag)
      (encStatePosition q) (Program.encStateBlock (3 * q)) := by
  have hs : ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => shape H hq p.1.1 p.2 tag)
      (encStatePosition q) (Cell.encBounded (3 * q)) := by
    simpa only [Function.comp_def] using (computableInPolyTime_shape H hq tag).comp
      (show ComputableInPolyTime (fun p : (ℕ × List (Fin q)) × ℕ => (p.1.1, p.2))
        (encStatePosition q) (encPair encUnary encUnary) from by fun_prop)
  unfold stateBlock
  exact Program.encStateBlock_mk_polyTime (3 * q) hs
    (computableInPolyTime_boundaryBits hq tag) (computableInPolyTime_ownedBits hq tag)

/-- The canonical direction metadata is polynomial-time for an explicit length and word list. -/
private theorem computableInPolyTime_stateBlocks : ComputableInPolyTime
    (fun p : ℕ × List (Fin q) => stateBlocks H hq p.1 p.2) (encStateInput q)
      (encList (Program.encStateBlock (3 * q))) := by
  unfold stateBlocks
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.fst _ _))
  apply ComputableInPolyTime.mapConst
  intro tag _
  exact computableInPolyTime_stateBlock H hq tag

/-- Canonical directions of the actual numbered graph have a standard polynomial-time emitter. -/
theorem computableInPolyTime_bits : ComputableInPolyTime
    (fun p : ℕ × List (Fin q) => Program.bits (stateBlocks H hq p.1 p.2))
      (encStateInput q) (encList encBool) := by
  simpa only [Function.comp_def] using (Program.computableInPolyTime_bits (3 * q)).comp
    (computableInPolyTime_stateBlocks H hq)

end Cslib.Complexity.NCL.HWord.Metadata
