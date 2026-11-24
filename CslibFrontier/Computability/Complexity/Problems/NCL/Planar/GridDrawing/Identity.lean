/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Basic

/-!
# The orthogonal drawing of identity wires

Identity wires are disjoint vertical paths of height one.

## Main definitions

* `Cslib.Complexity.NCL.GridDrawing.identity`: draw the identity diagram.

## Main results

The drawing uses the same ordered wire columns on both boundary rows.
-/

public section

namespace Cslib.Complexity.NCL.GridDrawing

open Diagram GridRouting

variable {Γ : List Color → List Color → Type} (I : Interp Γ)

/-- The vertical unit segment for an ordered identity wire. -/
@[expose] def WireTrace {n : ℕ} : Fin n ⊕ Empty → Point → Prop
  | .inl i, p => p.1 = 4 * i.val ∧ p.2 ≤ 1
  | .inr e, _ => e.elim

/-- A boundary row of the identity trace has exactly the ordered wire columns. -/
theorem wireTrace_boundary {n : ℕ} (e : Fin n ⊕ Empty) (x y : ℕ) (hy : y ≤ 1) :
    WireTrace e (x, y) ↔ ∃ i, Sum.inl i = e ∧ x = 4 * i.val := by
  rcases e with i | e
  · constructor
    · intro h
      exact ⟨i, rfl, h.1⟩
    · rintro ⟨j, he, hx⟩
      cases he
      exact ⟨hx, hy⟩
  · exact e.elim

/-- Draw identity wires as disjoint vertical unit segments. -/
@[expose] def identity (a : List Color) : DiagramDrawing I (Diagram.id a) where
  height := 1
  height_pos := by decide
  vertex := Empty.elim
  vertex_injective := fun v => v.elim
  vertex_rows v := v.elim
  vertex_separation v := v.elim
  source := Sum.elim (fun i => (4 * i.val, 0)) Empty.elim
  target := Sum.elim (fun i => (4 * i.val, 1)) Empty.elim
  trace := WireTrace
  edge_rows e := by
    rcases e with i | e
    · exact Nat.zero_lt_one
    · exact e.elim
  path e := by
    rcases e with i | e
    · refine ⟨Path.vertical (4 * i.val) 0 1 (by decide), fun _ hp => ?_⟩
      exact ⟨hp.1, hp.2.2⟩
    · exact e.elim
  row_le e _ := by
    rcases e with i | e
    · exact And.right
    · exact e.elim
  top_iff e x := wireTrace_boundary e x 0 (Nat.zero_le 1)
  bottom_iff e x := wireTrace_boundary e x 1 le_rfl
  source_top _ := rfl
  target_bottom _ := rfl
  source_spec e := by
    rcases e with i | e
    · exact .inl ⟨i, rfl⟩
    · exact e.elim
  target_spec e := by
    rcases e with i | e
    · exact .inl ⟨i, rfl⟩
    · exact e.elim
  source_port v := v.elim
  target_port v := v.elim
  vertex_meet _ v := v.elim
  meet e f p hef hp hq := by
    rcases e with i | e
    · rcases f with j | e
      · have he : i = j := Fin.ext (by have := hp.1; have := hq.1; omega)
        exact (hef (congrArg Sum.inl he)).elim
      · exact e.elim
    · exact e.elim

end Cslib.Complexity.NCL.GridDrawing
