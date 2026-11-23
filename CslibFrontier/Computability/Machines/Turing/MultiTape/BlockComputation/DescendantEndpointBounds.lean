/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantEndpoint
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DescendantEndpointTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives

/-!
# Storage bounds for compressed descendant queries

An ancestry frame emits parent indices whose bit lengths are bounded by its graph-size width.
Thus query lengths do not grow by repeated composition of polynomial output bounds. The single
starting bound below controls every mutable position and all remaining quantified choices. Its
polynomial depends only on the serialized short position, never on the protected root schedule.
-/

public section

namespace Turing.MultiTapeTM.DescendantEndpoint

open Cslib MultiTapeATM SeededChildCounts SeededChildWitness.Dispatch

/-- A uniform bound on the encoded ancestry, its remaining choice flags, the four binary
query fields, and the partial word at the current frame. -/
structure Bounded (bound : ℕ) (p : Position) : Prop where
  /-- Framed seed records fit within the initial bound. -/
  frames : (encList encFrame p.frames).length ≤ bound
  /-- All unprocessed frame words and their dispatches fit within the initial bound. -/
  flags : (p.frames.map (fun f => f.flags.length + 1)).sum ≤ bound
  /-- The original Boolean copy count remains short. -/
  copies : p.copies.size ≤ bound
  /-- The requested current edge has a bounded binary index. -/
  edge : p.edge.size ≤ bound
  /-- The proposed row endpoint has a bounded binary index. -/
  row : p.row.size ≤ bound
  /-- The proposed column endpoint has a bounded binary index. -/
  column : p.column.size ≤ bound
  /-- Consuming flags moves one bit to the choice word without increasing their total length. -/
  choices : p.pending.length + p.choices.length ≤ bound

/-- The initial serialized position plus all its local word lengths and dispatches. -/
@[expose] noncomputable def storageBound (p : Position) : ℕ :=
  (encPosition p).length + (p.frames.map (fun f => f.flags.length + 1)).sum + 1

private theorem frame_width_le (f : Frame) :
    width ⟨f.edges, f.vertices, 0⟩ ≤ (encFrame f).length := by
  simp only [width, encFrame_apply, encFrameFields, length_encPair, encNat_apply,
    encUnary_apply, List.length_replicate, Nat.size_eq_bits_len]
  rcases le_total f.edges f.vertices with h | h
  · rw [Nat.max_eq_right h]
    omega
  · rw [Nat.max_eq_left h]
    omega

private theorem bounded_root_of_le {bound copies edge : ℕ} {frames : List Frame}
    {answer : ℕ × ℕ} (hframes : (encList encFrame frames).length ≤ bound)
    (hflags : (frames.map (fun f => f.flags.length + 1)).sum ≤ bound)
    (hcopies : copies.size ≤ bound) (hedge : edge.size ≤ bound)
    (hrow : answer.1.size ≤ bound) (hcolumn : answer.2.size ≤ bound) :
    Bounded bound (root copies frames edge answer) := by
  refine ⟨hframes, hflags, hcopies, hedge, hrow, hcolumn, ?_⟩
  cases frames with
  | nil => simp [root]
  | cons f fs =>
    simp only [List.map_cons, List.sum_cons] at hflags
    simpa only [root, List.head?_cons, Option.elim_some, List.length_nil, Nat.add_zero] using
      (show f.flags.length ≤ bound by omega)

/-- A raw root position starts within a bound determined entirely by its own encoded fields. -/
theorem bounded_root (copies : ℕ) (frames : List Frame) (edge : ℕ) (answer : ℕ × ℕ) :
    Bounded (storageBound (root copies frames edge answer)) (root copies frames edge answer) := by
  let p := root copies frames edge answer
  let bound := storageBound p
  change Bounded bound p
  have henc : (encPosition p).length ≤ bound := by dsimp [bound, storageBound]; omega
  have hflags : (frames.map (fun f => f.flags.length + 1)).sum ≤ bound := by
    dsimp [bound, storageBound, p, root]
    omega
  simp only [p, encPosition_apply, encPositionFields, length_encPair, root,
    encNat_apply, Nat.size_eq_bits_len, encBits_apply, encOption_none,
    List.length_nil] at henc
  exact bounded_root_of_le (bound := bound) (by omega) hflags
    (by omega) (by omega) (by omega) (by omega)

/-- Every native move preserves the same bound, including adversarially chosen words and
rejecting branches. A popped frame supplies fresh bounded parent indices. -/
theorem Bounded.next {bound : ℕ} {p : Position} (hp : Bounded bound p) (bit : Bool) :
    Bounded bound (next p bit) := by
  cases hv : p.verdict with
  | some verdict =>
    simpa only [DescendantEndpoint.next, hv, Option.isSome_some, ↓reduceIte] using hp
  | none =>
    cases hf : p.frames with
    | nil =>
      simpa only [DescendantEndpoint.next, hv, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, hf] using hp
    | cons f fs =>
      cases hg : p.pending with
      | cons flag flags =>
        simp only [DescendantEndpoint.next, hv, Option.isSome_none, Bool.false_eq_true,
          ↓reduceIte, hf, hg]
        refine ⟨?_, ?_, hp.copies, hp.edge, hp.row, hp.column, ?_⟩
        · simpa only [hf] using hp.frames
        · simpa only [hf] using hp.flags
        · have hc := hp.choices
          simpa only [hg, List.length_cons, List.length_append, List.length_nil,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
      | nil =>
        have hframes := hp.frames
        have hflags := hp.flags
        rw [hf] at hframes hflags
        have htail : (encList encFrame fs).length ≤ bound :=
          (length_encList_sublist encFrame (List.sublist_cons_self f fs)).trans hframes
        have htailFlags : (fs.map (fun f => f.flags.length + 1)).sum ≤ bound := by
          simp only [List.map_cons, List.sum_cons] at hflags
          omega
        have hw : width ⟨f.edges, f.vertices, 0⟩ ≤ bound :=
          (frame_width_le f).trans ((SizedListEncoding.length_elem_le
            (encA := encFrame) (encL := encList encFrame) (f :: fs) f
            List.mem_cons_self).trans hframes)
        cases hrun : Joined.program (f.header p.edge (p.row, p.column), p.choices) with
        | inl verdict =>
          simp only [DescendantEndpoint.next, hv, Option.isSome_none, Bool.false_eq_true,
            ↓reduceIte, hf, hg, hrun]
          exact ⟨by simp [root], by simp [root], hp.copies, by simp [root], by simp [root],
            by simp [root], by simp [root]⟩
        | inr query =>
          simp only [DescendantEndpoint.next, hv, Option.isSome_none, Bool.false_eq_true,
            ↓reduceIte, hf, hg, hrun]
          obtain ⟨he, hr, hc⟩ := Joined.program_inr_bounds hrun
          exact bounded_root_of_le htail htailFlags hp.copies
            ((Nat.size_le.mpr he).trans hw) ((Nat.size_le.mpr hr).trans hw)
            ((Nat.size_le.mpr hc).trans hw)

/-- The entire mutable word is bounded uniformly, including framing and the optional verdict. -/
theorem Bounded.length_encPosition_le {bound : ℕ} {p : Position} (hp : Bounded bound p) :
    (encPosition p).length ≤ 16 * (bound + 1) := by
  obtain ⟨hf, _, hc, he, hr, hcol, hwords⟩ := hp
  cases hv : p.verdict <;>
    simp only [encPosition_apply, encPositionFields, length_encPair, encNat_apply,
      Nat.size_eq_bits_len, encBits_apply, hv, encOption_none, encOption_some,
      encBool_apply, List.length_cons, List.length_nil] <;> omega

/-- The bound for the complete ancestry is polynomial in its original encoded position.
It is computed from short seed records and binary graph sizes, with no explicit edge table. -/
theorem storageBound_polyBounded : PolyBounded (fun p => (encPosition p).length) storageBound := by
  have hm := ComputableInPolyTime.map flags_polyTime
  have hs : PolyBounded (fun fs : List Frame => (encList encFrame fs).length)
      (fun fs => (fs.map (fun f => f.flags.length + 1)).sum) := by
    refine (hm.polyBounded_length.add PolyBounded.self).mono fun fs => ?_
    have hlength := length_le_length_encList encFrame fs
    have hsum := sum_length_le_length_encList encBits (fs.map Frame.flags)
    simp only [List.map_map, Function.comp_def, encBits_apply] at hsum
    have heq : (fs.map (fun f => f.flags.length + 1)).sum =
        (fs.map (fun f => f.flags.length)).sum + fs.length := by simp [List.sum_map_add]
    rw [heq]
    omega
  exact (PolyBounded.self.add
    (hs.comp encPosition_frames_deg.computableInPolyTime.polyBounded_length)).add (.const 1)

end Turing.MultiTapeTM.DescendantEndpoint
