/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantVertex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits

/-!
# Native polynomial-time preparation and interpretation of vertex ancestry words

The initializer concatenates one short word per stored frame. The deterministic terminal
consumes at most one frame per iteration and stops after the first Boolean verdict. A parent
vertex is read from a field bounded by the popped frame's binary universe length. Removing
that frame therefore pays for both new binary query fields; the cursor can grow only by the
two symbols of its final verdict.

## Main results

* `Turing.MultiTapeTM.DescendantVertex.flags_polyTime`: native preparation of all frame flags.
* `Turing.MultiTapeTM.DescendantVertex.program_polyTime`: native evaluation of the completed
  word, with polynomial encoded storage throughout the frame traversal.
-/

public section

namespace Turing.MultiTapeTM.DescendantVertex

open Cslib ComputableInPolyTime MultiTapeATM
open DescendantEndpoint (Frame encFrame)

private theorem rankQuery_polyTime {α : Type} {enc : α ↪ List Bool}
    {f : α → Frame} {bound value : α → ℕ}
    (hf : ComputableInPolyTime f enc encFrame)
    (hb : ComputableInPolyTime bound enc encNat)
    (hv : ComputableInPolyTime value enc encNat) :
    ComputableInPolyTime (fun a => rankQuery (f a) (bound a) (value a)) enc
      SeededVertexRank.encQuery :=
  SeededVertexRank.encQuery_mk_polyTime
    (SeededPredecessor.encContext_mk_polyTime
      (DescendantEndpoint.encFrame_vertices_polyTime hf)
      (DescendantEndpoint.encFrame_coordinates_polyTime hf)
      (DescendantEndpoint.encFrame_c0_polyTime hf) (DescendantEndpoint.encFrame_c1_polyTime hf)
      (DescendantEndpoint.encFrame_c2_polyTime hf) (DescendantEndpoint.encFrame_c3_polyTime hf)
      (const 0) (const 0))
    (DescendantEndpoint.encFrame_coordinate_polyTime hf)
    (DescendantEndpoint.encFrame_group_polyTime hf) hb hv

private theorem symbol_polyTime {α : Type} {enc : α ↪ List Bool}
    {f : α → Frame} {v : α → ℕ} (hf : ComputableInPolyTime f enc encFrame)
    (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun a => symbol (f a) (v a)) enc encNat :=
  RootPortFinish.computableInPolyTime_symbol
    (SeededVertexRank.encQuery_context_polyTime (rankQuery_polyTime hf (const 0) (const 0)))
    (DescendantEndpoint.encFrame_coordinate_polyTime hf) hv

private theorem frameFlags_polyTime : ComputableInPolyTime frameFlags encFrame encBits := by
  have hU := DescendantEndpoint.encFrame_vertices_deg.computableInPolyTime
  exact ((bitsReplicate false).comp (binary_size.comp hU)).bitsAppend
    ((const [true]).bitsAppend (SeededVertexRank.computableInPolyTime_flags.comp hU))

/-- Prepare the entire ancestry word in polynomial time in the encoded frame stack. -/
theorem flags_polyTime : ComputableInPolyTime flags (encList encFrame) encBits :=
  flatMapToBitsWithInput id' (frameFlags_polyTime.comp (snd (encList encFrame) encFrame))

private abbrev encInstruction := encSum encBool encNat

private theorem dispatch_polyTime :
    ComputableInPolyTime (Function.uncurry dispatch) (encPair encQuery encBits)
      encInstruction := by
  let enc := encPair encQuery encBits
  have hq := fst encQuery encBits
  have hx := snd encQuery encBits
  have hframes := encQuery_frames_polyTime hq
  have hvertex := encQuery_vertex_polyTime hq
  have horigin := encQuery_origin_polyTime hq
  have hstage := encOrigin_stage_polyTime horigin
  have hindex := encOrigin_index_polyTime horigin
  have hlength := length_list_binary' hframes
  have hvalid := decide_and (binary_lt' hvertex (encQuery_vertices_polyTime hq))
    (binary_le' hstage hlength)
  let halt := sumInl encBool encNat
  let recurse := sumInr encBool encNat
  have hbase := halt.comp (decide_eq' hindex hvertex)
  have hp := fst enc encFrame
  have hf := snd enc encFrame
  have hU := DescendantEndpoint.encFrame_vertices_polyTime hf
  have hw := binary_size.comp hU
  have hparent := bitsToNat.comp (bitsTakeWithInput (hx.comp hp) hw)
  have hrest := bitsDropWithInput (hx.comp hp) hw
  have hword := bitsTail.comp hrest
  have hside := (headD (encA := encBool) (encL := encBits) false).comp hrest
  have hbirth := decide_eq' (hstage.comp hp) (hlength.comp hp)
  have hpacket := bool_and' (binary_le' (hindex.comp hp) (hvertex.comp hp))
    (SeededVertexRank.computableInPolyTime_program.comp
      ((rankQuery_polyTime hf hU (binary_sub' (hvertex.comp hp) (hindex.comp hp))).prod hword))
  have hretained := bool_and'
    (decide_and (binary_lt' hparent hU)
      (decide_eq' (symbol_polyTime hf hparent) (DescendantEndpoint.encFrame_group_polyTime hf)))
    (SeededVertexRank.computableInPolyTime_program.comp
      ((rankQuery_polyTime hf hparent (hvertex.comp hp)).prod hword))
  have hsome := ite_decide hbirth (halt.comp hpacket)
    (ite hside (recurse.comp hparent) (halt.comp hretained))
  have hbody := optionElimWithInput
    (body := fun (p : Query × List Bool) (f : Frame) =>
      let parent := ofBits (p.2.take f.vertices.size)
      let rest := p.2.drop f.vertices.size
      if p.1.origin.stage = p.1.frames.length then
        Sum.inl (decide (p.1.origin.index ≤ p.1.vertex) &&
          SeededVertexRank.program
            (rankQuery f f.vertices (p.1.vertex - p.1.origin.index), rest.tail))
      else if rest.headD false then Sum.inr parent
      else Sum.inl (decide (parent < f.vertices ∧ symbol f parent = f.group) &&
        SeededVertexRank.program (rankQuery f parent p.1.vertex, rest.tail)))
    ((head? encFrame).comp hframes) hbase hsome
  apply (ite_decide hvalid hbody (halt.comp (const false))).of_enc_eq
  intro p
  cases hframes : p.1.frames <;> simp [Function.uncurry, dispatch, hframes]

private structure Cursor where
  query : Query
  choices : List Bool
  verdict : Option Bool

private enc_structure encCursor : Cursor where query : encQuery, choices : encBits,
  verdict : (encOption encBool)

private def emptyFrame : Frame := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def advance (s : Cursor) : Cursor :=
  if s.verdict.isSome then s else
    let f := s.query.frames.headD emptyFrame
    let cut := (frameFlags f).length
    (dispatch s.query (s.choices.take cut)).elim
      (fun b => { s with verdict := some b })
      (fun parent => ⟨⟨s.query.frames.tail, f.vertices, parent, s.query.origin⟩,
        s.choices.drop cut, none⟩)

private def finish (s : Cursor) : Bool := s.verdict.getD false

private theorem advance_cons (f : Frame) (fs : List Frame) (vertices vertex : ℕ)
    (origin : Origin) (xs : List Bool) :
    advance ⟨⟨f :: fs, vertices, vertex, origin⟩, xs, none⟩ =
      (dispatch ⟨f :: fs, vertices, vertex, origin⟩ (xs.take (frameFlags f).length)).elim
        (fun b => ⟨⟨f :: fs, vertices, vertex, origin⟩, xs, some b⟩)
        (fun parent => ⟨⟨fs, f.vertices, parent, origin⟩,
          xs.drop (frameFlags f).length, none⟩) := rfl

private theorem advance_polyTime : ComputableInPolyTime advance encCursor encCursor := by
  have hq := encCursor_query_deg.computableInPolyTime
  have hx := encCursor_choices_deg.computableInPolyTime
  have hv := encCursor_verdict_deg.computableInPolyTime
  have hframes := encQuery_frames_polyTime hq
  have hf := (headD (encA := encFrame) emptyFrame).comp hframes
  have hk := length_bits_comp (frameFlags_polyTime.comp hf)
  have hd := dispatch_polyTime.comp (hq.prod (bitsTakeWithInput hx hk))
  have hl := fst encCursor encBool
  have hb := snd encCursor encBool
  have hhalt := encCursor_mk_polyTime (hq.comp hl) (hx.comp hl)
    ((optionSome encBool).comp hb)
  have hr := fst encCursor encNat
  have hp := snd encCursor encNat
  have hnext := encCursor_mk_polyTime
    (encQuery_mk_polyTime ((tail (encA := encFrame)).comp (hframes.comp hr))
      (DescendantEndpoint.encFrame_vertices_polyTime (hf.comp hr)) hp
      ((encQuery_origin_polyTime hq).comp hr))
    ((bitsDropWithInput hx hk).comp hr) (const none)
  have hstep := ComputableInPolyTime.sumElimWithInput
    (eg := encCursor) (ed := encCursor)
    (left := fun (s : Cursor) b => { s with verdict := some b })
    (right := fun (s : Cursor) parent =>
      let f := s.query.frames.headD emptyFrame
      ⟨⟨s.query.frames.tail, f.vertices, parent, s.query.origin⟩,
        s.choices.drop (frameFlags f).length, none⟩) hd hhalt hnext
  exact ite hv.optionIsSome id' hstep

private theorem dispatch_inr_size {f : Frame} {fs : List Frame} {vertices vertex : ℕ}
    {origin : Origin} {xs : List Bool} {parent : ℕ}
    (h : dispatch ⟨f :: fs, vertices, vertex, origin⟩ xs = .inr parent) :
    parent.size ≤ f.vertices.size := by
  have he : parent = ofBits (xs.take f.vertices.size) := by
    simp only [dispatch] at h
    split_ifs at h; simp_all
  rw [he]
  exact (Nat.size_le.mpr (ofBits_lt_two_pow _)).trans (List.length_take_le _ _)

private theorem growth (s : Cursor) :
    (encCursor (advance s)).length ≤ (encCursor s).length + 2 := by
  rcases s with ⟨⟨frames, vertices, vertex, origin⟩, xs, verdict⟩
  cases verdict with
  | some b => simp [advance]
  | none =>
    cases frames with
    | nil =>
      by_cases h : vertex < vertices ∧ origin.stage = 0 <;>
        simp [advance, dispatch, h, encCursor_apply, encCursorFields] <;> omega
    | cons f fs =>
      let q : Query := ⟨f :: fs, vertices, vertex, origin⟩
      let cut := (frameFlags f).length
      cases hd : dispatch q (xs.take cut) with
      | inl b =>
        rw [advance_cons, hd]
        simp [encCursor_apply, encCursorFields]; omega
      | inr parent =>
        have hp := dispatch_inr_size hd
        rw [advance_cons, hd, Sum.elim_inr]
        simp only [encCursor_apply, encCursorFields, encQuery_apply, encQueryFields,
          DescendantEndpoint.encFrame_apply, DescendantEndpoint.encFrameFields,
          length_encPair, encList_cons, List.length_append, length_frame, encNat_apply,
          Nat.size_eq_bits_len, encBits_apply, encOption_none, List.length_nil,
          List.length_drop] at hp ⊢
        omega

private theorem iterate_halted (q : Query) (xs : List Bool) (b : Bool) (n : ℕ) :
    advance^[n] ⟨q, xs, some b⟩ = ⟨q, xs, some b⟩ :=
  Function.iterate_fixed (by simp [advance]) n

private theorem finish_iterate (frames : List Frame) (vertices vertex : ℕ) (origin : Origin)
    (xs : List Bool) :
    finish (advance^[frames.length + 1] ⟨⟨frames, vertices, vertex, origin⟩, xs, none⟩) =
      run vertices vertex origin frames xs := by
  induction frames generalizing vertices vertex xs with
  | nil =>
    by_cases h : vertex < vertices ∧ origin.stage = 0 <;>
      simp [advance, run, dispatch, finish, h]
  | cons f fs ih =>
    let q : Query := ⟨f :: fs, vertices, vertex, origin⟩
    let cut := (frameFlags f).length
    rw [show (f :: fs).length + 1 = (fs.length + 1) + 1 by rfl,
      Function.iterate_succ_apply, advance_cons]
    cases hd : dispatch q (xs.take cut) with
    | inl b =>
      rw [Sum.elim_inl, iterate_halted, run, hd]
      rfl
    | inr parent =>
      rw [Sum.elim_inr, run, hd]
      exact ih f.vertices parent (xs.drop cut)

/-- Interpret the entire completed word in polynomial time in its compressed query and bits.
The iteration count is the frame-list length plus one; no vertex universe is traversed. -/
theorem program_polyTime : ComputableInPolyTime program (encPair encQuery encBits) encBool := by
  have hq := fst encQuery encBits
  have hx := snd encQuery encBits
  have hc := unary_add' ((length_list encFrame).comp (encQuery_frames_polyTime hq)) (const 1)
  have hi := encCursor_mk_polyTime hq hx (const none)
  have hrun := iterate_of_bounded_growth hc hi advance_polyTime growth
  have hf : ComputableInPolyTime finish encCursor encBool :=
    optionGetDWithInput encCursor_verdict_deg.computableInPolyTime (const false)
  apply (hf.comp hrun).of_enc_eq
  intro p
  congr 1
  exact (finish_iterate p.1.frames p.1.vertices p.1.vertex p.1.origin p.2).symm

end Turing.MultiTapeTM.DescendantVertex
