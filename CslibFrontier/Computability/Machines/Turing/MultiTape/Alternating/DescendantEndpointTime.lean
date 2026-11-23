/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantEndpoint
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Native short updates of the descendant endpoint controller

The concrete updates use the shared seeded-child program. Their polynomial applies only to
the encoded frame stack, current endpoint query and quantified choices; the protected root
schedule is absent from every input to these computations.
-/

public section

namespace Turing.MultiTapeTM.DescendantEndpoint

open Cslib SeededChildWitness ComputableInPolyTime MultiTapeATM SeededChildCounts

private theorem header_polyTime {α : Type} {enc : α ↪ List Bool}
    {f : α → Frame} {edge row column : α → ℕ}
    (hf : ComputableInPolyTime f enc encFrame)
    (he : ComputableInPolyTime edge enc encNat)
    (hr : ComputableInPolyTime row enc encNat)
    (hc : ComputableInPolyTime column enc encNat) :
    ComputableInPolyTime (fun a => (f a).header (edge a) (row a, column a)) enc
      Joined.encHeader :=
  Joined.encHeader_mk_polyTime
    (Dispatch.encPublic_mk_polyTime (encFrame_edges_polyTime hf)
      (encFrame_vertices_polyTime hf) he)
    (Cslib.SeededPredecessor.encContext_mk_polyTime (encFrame_vertices_polyTime hf)
      (encFrame_coordinates_polyTime hf) (encFrame_c0_polyTime hf) (encFrame_c1_polyTime hf)
      (encFrame_c2_polyTime hf) (encFrame_c3_polyTime hf) (const 0) (const 0))
    (encFrame_coordinate_polyTime hf) (encFrame_group_polyTime hf) (hr.prod hc)

/-- Generate a frame's quantifier owners from its encoded short seed metadata. -/
theorem flags_polyTime : ComputableInPolyTime Frame.flags encFrame encBits :=
  Joined.computableInPolyTime_flags.comp
    (Dispatch.encPublic_mk_polyTime encFrame_edges_deg.computableInPolyTime
      encFrame_vertices_deg.computableInPolyTime (const 0))

/-- Initialize the quantified choices without reading the protected root schedule. -/
theorem root_polyTime {α : Type} {enc : α ↪ List Bool}
    {copies : α → ℕ} {frames : α → List Frame} {edge row column : α → ℕ}
    (hc : ComputableInPolyTime copies enc encNat)
    (hf : ComputableInPolyTime frames enc (encList encFrame))
    (he : ComputableInPolyTime edge enc encNat)
    (hr : ComputableInPolyTime row enc encNat)
    (hl : ComputableInPolyTime column enc encNat) :
    ComputableInPolyTime (fun a => root (copies a) (frames a) (edge a) (row a, column a))
      enc encPosition := by
  have hhead := (head? encFrame).comp hf
  have hflags : ComputableInPolyTime
      (fun a => (frames a).head?.elim [] Frame.flags) enc encBits :=
    optionElimWithInput hhead (const [])
      (flags_polyTime.comp (snd enc encFrame))
  exact encPosition_mk_polyTime hc hf he hr hl hflags (const []) (const none)

/-- The owner of a live position is computable from its short metadata. -/
theorem player_polyTime : ComputableInPolyTime player encPosition (encOption encBool) := by
  have hv := encPosition_verdict_deg.computableInPolyTime
  have hsome := (of_finite (encIn := encOption encBool) (encOut := encBool)
    Option.isSome).comp hv
  have hf := encPosition_frames_deg.computableInPolyTime
  have hhead := (head? encFrame).comp hf
  have hbit := (ListEncoding.headD (enc₁ := encBool) (enc := encBits)
    false).computableInPolyTime.comp encPosition_pending_deg.computableInPolyTime
  have ho := (optionSome encBool).comp hbit
  have h : ComputableInPolyTime (fun p : Position =>
      if p.verdict.isSome then none else p.frames.head?.elim none (fun _ => some
        (p.pending.headD false))) encPosition (encOption encBool) :=
    ite hsome (const none)
      (optionElimWithInput hhead (const none) (ho.comp (fst encPosition encFrame)))
  exact h.of_enc_eq fun p => by cases hf : p.frames <;> simp [player, hf]

private def dispatch (a : Position × Frame) : Position :=
  match Joined.program (a.2.header a.1.edge (a.1.row, a.1.column), a.1.choices) with
  | .inl verdict => { root a.1.copies [] 0 (0, 0) with verdict := some verdict }
  | .inr (edge, answer) => root a.1.copies a.1.frames.tail edge answer

private theorem dispatch_polyTime : ComputableInPolyTime dispatch
    (encPair encPosition encFrame) encPosition := by
  let enc := encPair encPosition encFrame
  have hp := fst encPosition encFrame
  have hf := snd encPosition encFrame
  have hc := encPosition_copies_polyTime hp
  have hframes := (tail (encA := encFrame)).comp (encPosition_frames_polyTime hp)
  have hrun := Joined.computableInPolyTime_program.comp
    ((header_polyTime hf (encPosition_edge_polyTime hp) (encPosition_row_polyTime hp)
      (encPosition_column_polyTime hp)).prod (encPosition_choices_polyTime hp))
  have ha := fst enc encBool
  have hb := snd enc encBool
  have hleft := encPosition_mk_polyTime (hc.comp ha) (const []) (const 0)
    (const 0) (const 0) (const []) (const []) ((optionSome encBool).comp hb)
  let eq := encPair encNat (encPair encNat encNat)
  have houter := fst enc eq
  have hquery := snd enc eq
  have hright := root_polyTime (hc.comp houter) (hframes.comp houter) hquery.fst'
    hquery.snd'.fst' hquery.snd'.snd'
  have h : ComputableInPolyTime (fun a : Position × Frame =>
      (Joined.program (a.2.header a.1.edge (a.1.row, a.1.column), a.1.choices)).elim
        (fun verdict => { root a.1.copies [] 0 (0, 0) with verdict := some verdict })
        (fun query => root a.1.copies a.1.frames.tail query.1 query.2))
      (encPair encPosition encFrame) encPosition :=
    ComputableInPolyTime.sumElimWithInput
      (eg := encPair encPosition encFrame) (ed := encPosition)
      (ea := encBool) (eb := encPair encNat (encPair encNat encNat))
      (left := fun (a : Position × Frame) (verdict : Bool) =>
        { root a.1.copies [] 0 (0, 0) with verdict := some verdict })
      (right := fun (a : Position × Frame) (query : ℕ × (ℕ × ℕ)) =>
        root a.1.copies a.1.frames.tail query.1 query.2)
      hrun hleft hright
  exact h.of_enc_eq fun a => by
    unfold dispatch
    cases Joined.program (a.2.header a.1.edge (a.1.row, a.1.column), a.1.choices) <;> rfl

private theorem choose_polyTime : ComputableInPolyTime
    (fun x : Bool × Position =>
      { x.2 with pending := x.2.pending.tail, choices := x.2.choices ++ [x.1] })
    (encPair encBool encPosition) encPosition := by
  have hp := snd encBool encPosition
  have hb := fst encBool encPosition
  have hpending := encPosition_pending_polyTime hp
  have hchoice := encPosition_choices_polyTime hp
  have htail := bitsTail.comp hpending
  have happend := hchoice.bitsAppend (bitsCons hb (const []))
  exact encPosition_mk_polyTime (encPosition_copies_polyTime hp) (encPosition_frames_polyTime hp)
    (encPosition_edge_polyTime hp) (encPosition_row_polyTime hp)
    (encPosition_column_polyTime hp) htail happend (encPosition_verdict_polyTime hp)

private theorem frame_step_polyTime : ComputableInPolyTime
    (fun a : (Bool × Position) × Frame =>
      if a.1.2.pending.head?.isNone then
        dispatch (a.1.2, a.2)
      else { a.1.2 with pending := a.1.2.pending.tail, choices := a.1.2.choices ++ [a.1.1] })
    (encPair (encPair encBool encPosition) encFrame) encPosition := by
  let enc := encPair encBool encPosition
  have hp := snd encBool encPosition
  have hpending := encPosition_pending_polyTime hp
  have hempty := (of_finite (encIn := encOption encBool) (encOut := encBool)
    Option.isNone).comp ((head? encBool).comp hpending)
  have ha := fst enc encFrame
  have hf := snd enc encFrame
  exact ite (hempty.comp ha) (dispatch_polyTime.comp ((hp.comp ha).prod hf))
    (choose_polyTime.comp ha)

/-- Each Boolean choice updates only short state, executing one real child program when its
choice word is complete. -/
theorem next_polyTime : ComputableInPolyTime (fun x : Bool × Position => next x.2 x.1)
    (encPair encBool encPosition) encPosition := by
  have hp := snd encBool encPosition
  have hsome := (of_finite (encIn := encOption encBool) (encOut := encBool)
    Option.isSome).comp (encPosition_verdict_polyTime hp)
  have hhead := (head? encFrame).comp (encPosition_frames_polyTime hp)
  have h : ComputableInPolyTime (fun x : Bool × Position =>
      if x.2.verdict.isSome then x.2 else x.2.frames.head?.elim x.2 (fun f =>
        if x.2.pending.head?.isNone then
          dispatch (x.2, f)
        else { x.2 with pending := x.2.pending.tail, choices := x.2.choices ++ [x.1] }))
      (encPair encBool encPosition) encPosition :=
    ite hsome hp (optionElimWithInput hhead hp frame_step_polyTime)
  refine h.of_enc_eq fun x => ?_
  apply congrArg encPosition
  rcases x with ⟨bit,p⟩
  cases hv : p.verdict <;> cases hf : p.frames <;> cases ht : p.pending <;>
    simp only [next, dispatch, hv, hf, ht, Option.isSome_none, Option.isSome_some,
      List.head?_nil, List.head?_cons, Option.elim_none, Option.elim_some,
      Option.isNone_none, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, List.tail_cons]
  rfl

/-- The complete short native round includes recomputing the next owner. -/
theorem step_polyTime : ComputableInPolyTime step (encPair encBool encPosition)
    (encPair (encOption encBool) encPosition) :=
  (player_polyTime.comp next_polyTime).prod next_polyTime

end Turing.MultiTapeTM.DescendantEndpoint
