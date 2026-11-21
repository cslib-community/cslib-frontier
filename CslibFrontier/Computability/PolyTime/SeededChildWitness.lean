/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededPacketPlacement
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortFinish
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Checking the short fields of a child endpoint witness

A proposed parent edge supplies two vertex keys and six binary counts. The machine checks the
edge's position among the row or column ports and the two claimed child keys. It computes the
parent's packet from the same seed and class rank. All inputs to this calculation have short
encodings. The parent edge and its proposed counts can be checked on separate universal branches.
-/

public section

namespace Cslib.SeededChildWitness

open Turing.MultiTapeTM ComputableInPolyTime

/-- Proposed prefix counts, group totals and the parent edge's class rank. -/
structure Counts where
  rowPrefix : ℕ
  colPrefix : ℕ
  rowTotal : ℕ
  vertexPrefix : ℕ
  vertexTotal : ℕ
  classRank : ℕ

/-- All six proposals are binary integers. -/
enc_structure encCounts : Counts where
  rowPrefix : encNat, colPrefix : encNat, rowTotal : encNat,
  vertexPrefix : encNat, vertexTotal : encNat, classRank : encNat

/-- The seed context holds the chosen parent edge index. The two pairs contain the parent
endpoint witness and the requested child endpoints respectively. -/
structure Input where
  context : SeededPredecessor.Context
  coordinate : ℕ
  group : ℕ
  child : ℕ
  ends : ℕ × ℕ
  answer : ℕ × ℕ
  counts : Counts

/-- The coordinate is unary. Vertex, edge and group numbers use binary. -/
enc_structure encInput : Input where
  context : SeededPredecessor.encContext, coordinate : encUnary, group : encNat, child : encNat,
  ends : (encPair encNat encNat), answer : (encPair encNat encNat), counts : encCounts

/-- If the proposed indices and counts fit in `w` binary bits, their contribution to the
external word is linear in `w`. The seed context and unary coordinate are charged separately. -/
theorem length_encInput_le (x : Input) (w : ℕ)
    (h : ∀ n ∈ [x.group, x.child, x.ends.1, x.ends.2, x.answer.1, x.answer.2,
      x.counts.rowPrefix, x.counts.colPrefix, x.counts.rowTotal, x.counts.vertexPrefix,
      x.counts.vertexTotal, x.counts.classRank], n.size ≤ w) :
    (encInput x).length ≤ 2 * (SeededPredecessor.encContext x.context).length +
      2 * x.coordinate + 32 * (w + 1) := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, forall_const,
    and_true] at h
  simp only [encInput_apply, encInputFields, encCounts_apply, encCountsFields, length_encPair,
    encNat_apply, Nat.size_eq_bits_len, encUnary_apply, List.length_replicate]
  omega

/-- The child list consists of row ports followed by column ports. Its second endpoint is
indexed after all retained vertices. -/
@[expose] def run (x : Input) : Bool :=
  let c := x.counts
  let label := RootPortFinish.symbol x.context x.coordinate
  let packet := (SeededPacketPlacement.run ⟨x.context, x.ends.1, x.ends.2, c.classRank⟩).1
  decide (((label x.ends.1 = x.group ∧ c.rowPrefix = x.child) ∨
    (label x.ends.2 = x.group ∧ c.rowTotal + c.colPrefix = x.child)) ∧
    x.answer = (c.vertexPrefix, c.vertexTotal + packet))

/-- One native machine checks both orientations and all numeric fields of the claim. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput encBool := by
  have hc := encInput_context_deg.computableInPolyTime
  have hi := encInput_coordinate_deg.computableInPolyTime
  have hg := encInput_group_deg.computableInPolyTime
  have hj := encInput_child_deg.computableInPolyTime
  have he := encInput_ends_deg.computableInPolyTime
  have hn := encInput_counts_deg.computableInPolyTime
  have hr := decide_eq' (RootPortFinish.computableInPolyTime_symbol hc hi he.fst') hg
  have hs := decide_eq' (RootPortFinish.computableInPolyTime_symbol hc hi he.snd') hg
  have hrow := decide_eq' (encCounts_rowPrefix_polyTime hn) hj
  have hcol := decide_eq' (binary_add' (encCounts_rowTotal_polyTime hn)
    (encCounts_colPrefix_polyTime hn)) hj
  have hport := ComputableInPolyTime.decide_or
    (ComputableInPolyTime.decide_and hr hrow)
    (ComputableInPolyTime.decide_and hs hcol)
  have hpacket := SeededPacketPlacement.computableInPolyTime_run.comp
    (SeededPacketPlacement.encInput_mk_polyTime hc he.fst' he.snd'
      (encCounts_classRank_polyTime hn))
  have hanswer := decide_eq' encInput_answer_deg.computableInPolyTime
    ((encCounts_vertexPrefix_polyTime hn).prod (binary_add' (encCounts_vertexTotal_polyTime hn)
      hpacket.fst'))
  exact ComputableInPolyTime.decide_and hport hanswer

end Cslib.SeededChildWitness
