/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Basic

/-!
# Stacking orthogonal drawings

An output edge of the upper drawing joins the corresponding input edge below. All other edges
retain their old path. The only possible intersection between drawing bands is their common
boundary, where matching columns carry the same graph edge.

## Main definitions

* `Cslib.Complexity.NCL.GridDrawing.comp`: stack drawings of composable diagrams.

## Main results

* The resulting paths draw the exact graph of the composed diagram.
-/

public section

namespace Cslib.Complexity.NCL.GridDrawing

open Diagram GridRouting

variable {Γ : List Color → List Color → Type} {I : Interp Γ} {a b c : List Color}
  {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}

namespace Comp

/-- The two rows of vertex positions after stacking. -/
private def vertex (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂) :
    (D₁.comp D₂).Vtx I → Point := Sum.elim P.vertex (shift P.height ∘ Q.vertex)

/-- Edge traces after identifying the shared boundary wires. -/
private def Trace (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : (D₁.comp D₂).Edge) (p : Point) : Prop :=
  (∃ e₁, compLeft D₁ D₂ e₁ = e ∧ P.trace e₁ p) ∨
    (P.height ≤ p.2 ∧ ∃ e₂, compRight D₁ D₂ e₂ = e ∧ Q.trace e₂ (p.1, p.2 - P.height))

/-- First endpoints are inherited from the drawing where the edge was created. -/
private def source (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂) :
    (D₁.comp D₂).Edge → Point
  | .inl i => P.source (.inl i)
  | .inr (.inl e) => P.source (.inr e)
  | .inr (.inr e) => shift P.height (Q.source (.inr e))

/-- An upper edge continues below exactly when it exits through the shared interface. -/
private noncomputable def targetLeft (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : D₁.Edge) : Point := by
  classical
  exact if h : ∃ j, D₁.bottom j = e then shift P.height (Q.target (.inl h.choose)) else P.target e

/-- The final endpoints after extending each shared edge through the lower drawing. -/
private noncomputable def target (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂) :
    (D₁.comp D₂).Edge → Point
  | .inl i => targetLeft P Q (.inl i)
  | .inr (.inl e) => targetLeft P Q (.inr e)
  | .inr (.inr e) => shift P.height (Q.target (.inr e))

@[simp] private theorem source_left (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : D₁.Edge) :
    source P Q (compLeft D₁ D₂ e) = P.source e := by cases e <;> rfl

@[simp] private theorem target_left (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : D₁.Edge) :
    target P Q (compLeft D₁ D₂ e) = targetLeft P Q e := by cases e <;> rfl

/-- Extending a named output wire selects that same input wire below. -/
private theorem targetLeft_bottom (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (j : Fin b.length) : targetLeft P Q (D₁.bottom j) = shift P.height (Q.target (.inl j)) := by
  classical
  unfold targetLeft
  split_ifs with h
  · exact congrArg (fun j => shift P.height (Q.target (.inl j)))
      ((bottom_injective D₁) h.choose_spec)
  · exact (h ⟨j, rfl⟩).elim

@[simp] private theorem target_right (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : D₂.Edge) :
    target P Q (compRight D₁ D₂ e) = shift P.height (Q.target e) := by
  cases e with
  | inl j => exact (target_left P Q _).trans (targetLeft_bottom P Q j)
  | inr _ => rfl

/-- A point in the upper drawing remains in the combined edge Trace. -/
private theorem trace_left (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : D₁.Edge) {p : Point} (h : P.trace e p) : Trace P Q (compLeft D₁ D₂ e) p :=
  .inl ⟨e, rfl, h⟩

/-- A point in the lower drawing translates into the combined edge Trace. -/
private theorem trace_right (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : D₂.Edge) {p : Point} (h : Shift P.height (Q.trace e) p) :
    Trace P Q (compRight D₁ D₂ e) p := .inr ⟨h.1, e, rfl, h.2⟩

/-- Vertex incidences in the upper part are retained by composition. -/
private theorem port_left {v : D₁.Vtx I} {e : D₁.Edge} {d : Bool}
    (h : HasPort (D₁.graph I) v e d) :
    HasPort ((D₁.comp D₂).graph I) (.inl v) (compLeft D₁ D₂ e) d := h.map _

/-- Vertex incidences in the lower part are retained by composition. -/
private theorem port_right {v : D₂.Vtx I} {e : D₂.Edge} {d : Bool}
    (h : HasPort (D₂.graph I) v e d) :
    HasPort ((D₁.comp D₂).graph I) (.inr v) (compRight D₁ D₂ e) d := h.map _

/-- Two distinct vertex positions remain distinct after stacking. -/
private theorem vertex_injective (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂) :
    Function.Injective (vertex P Q) := by
  rintro (v | v) (w | w) he
  · exact congrArg Sum.inl (P.vertex_injective he)
  · exact absurd (congrArg Prod.snd he) ((P.vertex_rows v).2.trans_le (Nat.le_add_left _ _)).ne
  · exact absurd (congrArg Prod.snd he).symm ((P.vertex_rows w).2.trans_le (Nat.le_add_left _ _)).ne
  · simp only [vertex, Sum.elim_inr, Function.comp_def, shift, Prod.mk.injEq,
      Nat.add_right_cancel_iff] at he
    exact congrArg Sum.inr (Q.vertex_injective (Prod.ext he.1 he.2))

/-- All stacked vertices stay strictly inside the combined drawing. -/
private theorem vertex_rows (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (v : (D₁.comp D₂).Vtx I) :
    0 < (vertex P Q v).2 ∧ (vertex P Q v).2 < P.height + Q.height := by
  rcases v with v | v
  · exact ⟨(P.vertex_rows v).1, (P.vertex_rows v).2.trans_le (Nat.le_add_right _ _)⟩
  · have := Q.vertex_rows v
    simp only [vertex, Sum.elim_inr, Function.comp_def, shift]
    omega

/-- The composed endpoints of every old edge have positive downward displacement. -/
private theorem edge_rows_left (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂) (e : D₁.Edge) :
    (source P Q (compLeft D₁ D₂ e)).2 < (target P Q (compLeft D₁ D₂ e)).2 := by
  classical
  rw [source_left, target_left, targetLeft]
  split_ifs with h
  · have hp := P.edge_rows e
    have hb := congrArg Prod.snd ((congrArg P.target h.choose_spec).symm.trans
      (P.target_bottom h.choose))
    have hq := (Q.source_top h.choose) ▸ Q.edge_rows (.inl h.choose)
    simp only [shift] at hb hq ⊢
    omega
  · exact P.edge_rows e

/-- Stacking preserves the empty integer row between distinct vertex rows. -/
private theorem vertex_separation (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (v w : (D₁.comp D₂).Vtx I) (hvw : v ≠ w) :
    (vertex P Q v).2 + 1 < (vertex P Q w).2 ∨
      (vertex P Q w).2 + 1 < (vertex P Q v).2 := by
  rcases v with v | v <;> rcases w with w | w
  · exact P.vertex_separation v w (fun he => hvw (congrArg Sum.inl he))
  · exact Or.inl ((Nat.succ_le_of_lt (P.vertex_rows v).2).trans_lt
      (Nat.lt_add_of_pos_left (Q.vertex_rows w).1))
  · exact Or.inr ((Nat.succ_le_of_lt (P.vertex_rows w).2).trans_lt
      (Nat.lt_add_of_pos_left (Q.vertex_rows v).1))
  · have := Q.vertex_separation v w (fun he => hvw (congrArg Sum.inr he))
    simp only [vertex, Sum.elim_inr, Function.comp_def, shift]
    omega

/-- Every edge still has a complete finite path after boundary identification. -/
private theorem path_left (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂) (e : D₁.Edge) :
    Connected (Trace P Q (compLeft D₁ D₂ e))
      (source P Q (compLeft D₁ D₂ e)) (target P Q (compLeft D₁ D₂ e)) := by
  classical
  rw [source_left, target_left]
  by_cases h : ∃ j, D₁.bottom j = e
  · have he : P.target e = shift P.height (Q.source (.inl h.choose)) := by
      calc P.target e = P.target (D₁.bottom h.choose) := congrArg P.target h.choose_spec.symm
        _ = (4 * h.choose.val, P.height) := P.target_bottom _
        _ = shift P.height (Q.source (.inl h.choose)) := by simp [Q.source_top, shift]
    have hp := he ▸ (P.path e).mono (fun _ hp => trace_left P Q e hp)
    have hq : Connected (Trace P Q (compLeft D₁ D₂ e))
        (shift P.height (Q.source (.inl h.choose)))
        (shift P.height (Q.target (.inl h.choose))) := by
      simpa only [compRight, h.choose_spec] using ((Q.path (.inl h.choose)).shift P.height).mono
        (fun _ hq => trace_right P Q (.inl h.choose) hq)
    simpa only [targetLeft, dite_eq_left h] using hp.comp hq
  · simpa only [targetLeft, dite_eq_right h] using
      (P.path e).mono (fun _ hp => trace_left P Q e hp)

/-- Newly created lower edges retain their translated path. -/
private theorem path_new (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂) (e : D₂.Inner) :
    Connected (Trace P Q (.inr (.inr e)))
      (source P Q (.inr (.inr e))) (target P Q (.inr (.inr e))) :=
  ((Q.path (.inr e)).shift P.height).mono (fun _ h => trace_right P Q (.inr e) h)

/-- All path traces stay in the combined row band. -/
private theorem row_le (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : (D₁.comp D₂).Edge) (p : Point) (h : Trace P Q e p) : p.2 ≤ P.height + Q.height := by
  rcases h with ⟨e, _, hp⟩ | ⟨hy, e, _, hq⟩
  · exact (P.row_le e p hp).trans (Nat.le_add_right _ _)
  · have := Q.row_le e _ hq
    omega

/-- The combined top row retains the original input names. -/
private theorem top_iff (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : (D₁.comp D₂).Edge) (x : ℕ) :
    Trace P Q e (x, 0) ↔ ∃ i : Fin a.length, Sum.inl i = e ∧ x = 4 * i.val := by
  constructor
  · rintro (⟨e', he, hp⟩ | ⟨hy, _⟩)
    · obtain ⟨i, hi, hx⟩ := (P.top_iff e' x).1 hp
      exact ⟨i, (congrArg (compLeft D₁ D₂) hi).trans he, hx⟩
    · have := P.height_pos
      omega
  · rintro ⟨i, rfl, rfl⟩
    exact trace_left P Q (.inl i) ((P.top_iff _ _).2 ⟨i, rfl, rfl⟩)

/-- The combined bottom row retains the final output names. -/
private theorem bottom_iff (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : (D₁.comp D₂).Edge) (x : ℕ) :
    Trace P Q e (x, P.height + Q.height) ↔
      ∃ j : Fin c.length, (D₁.comp D₂).bottom j = e ∧ x = 4 * j.val := by
  constructor
  · rintro (⟨e', _, hp⟩ | ⟨hy, e', he, hq⟩)
    · exact (((P.row_le e' _ hp).trans_lt (Nat.lt_add_of_pos_right Q.height_pos)).ne rfl).elim
    · obtain ⟨j, hj, hx⟩ := (Q.bottom_iff _ _).1 (by simpa only [Nat.add_sub_cancel_left] using hq)
      exact ⟨j, (bottom_comp D₁ D₂ j).trans ((congrArg (compRight D₁ D₂) hj).trans he), hx⟩
  · rintro ⟨j, rfl, rfl⟩
    rw [bottom_comp]
    exact trace_right P Q (D₂.bottom j)
      ⟨by omega, by simpa only [Nat.add_sub_cancel_left] using
        (Q.bottom_iff _ _).2 ⟨j, rfl, rfl⟩⟩

/-- An upper true-direction port cannot leave the upper drawing through its bottom boundary. -/
private theorem target_port_left (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    {v : D₁.Vtx I} {e : D₁.Edge} (hp : HasPort (D₁.graph I) v e true) :
    target P Q (compLeft D₁ D₂ e) = vertex P Q (.inl v) := by
  classical
  have hn : ¬∃ j, D₁.bottom j = e := by
    rintro ⟨j, rfl⟩
    have hy := congrArg Prod.snd ((P.target_bottom j).symm.trans (P.target_port v _ hp))
    have := (P.vertex_rows v).2
    dsimp only at hy
    omega
  rw [target_left, targetLeft, dite_eq_right hn]
  exact P.target_port v e hp

/-- A lower false-direction port is created inside the lower drawing. -/
private theorem source_port_right (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    {v : D₂.Vtx I} {e : D₂.Edge} (hp : HasPort (D₂.graph I) v e false) :
    source P Q (compRight D₁ D₂ e) = vertex P Q (.inr v) := by
  cases e with
  | inl i =>
    have hy := congrArg Prod.snd ((Q.source_top i).symm.trans (Q.source_port v (.inl i) hp))
    have := (Q.vertex_rows v).1
    dsimp only at hy
    omega
  | inr e => exact congrArg (shift P.height) (Q.source_port v (.inr e) hp)

/-- Every lower final endpoint retains its output or vertex interpretation. -/
private theorem target_spec_right (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : D₂.Edge) :
    (∃ j, (D₁.comp D₂).bottom j = compRight D₁ D₂ e) ∨
      ∃ v, HasPort ((D₁.comp D₂).graph I) v (compRight D₁ D₂ e) true ∧
        target P Q (compRight D₁ D₂ e) = vertex P Q v := by
  rcases Q.target_spec e with ⟨j, hj⟩ | ⟨v, hp, hv⟩
  · exact .inl ⟨j, (bottom_comp D₁ D₂ j).trans (congrArg (compRight D₁ D₂) hj)⟩
  · exact .inr ⟨.inr v, port_right hp, (target_right P Q e).trans (congrArg (shift P.height) hv)⟩

/-- Upper first endpoints remain input ports or upper vertex ports. -/
private theorem source_spec_left (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂) (e : D₁.Edge) :
    (∃ i : Fin a.length, Sum.inl i = compLeft D₁ D₂ e) ∨
      ∃ v, HasPort ((D₁.comp D₂).graph I) v (compLeft D₁ D₂ e) false ∧
        source P Q (compLeft D₁ D₂ e) = vertex P Q v := by
  rcases P.source_spec e with ⟨i, hi⟩ | ⟨v, hp, hv⟩
  · exact .inl ⟨i, congrArg (compLeft D₁ D₂) hi⟩
  · exact .inr ⟨.inl v, port_left hp, (source_left P Q e).trans hv⟩

/-- Every upper edge ends at an upper vertex or continues to a lower endpoint. -/
private theorem target_spec_left (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂) (e : D₁.Edge) :
    (∃ j, (D₁.comp D₂).bottom j = compLeft D₁ D₂ e) ∨
      ∃ v, HasPort ((D₁.comp D₂).graph I) v (compLeft D₁ D₂ e) true ∧
        target P Q (compLeft D₁ D₂ e) = vertex P Q v := by
  classical
  by_cases h : ∃ j, D₁.bottom j = e
  · exact congrArg (compLeft D₁ D₂) h.choose_spec ▸ target_spec_right P Q (.inl h.choose)
  · rcases P.target_spec e with ⟨j, hj⟩ | ⟨v, hp, hv⟩
    · exact (h ⟨j, hj⟩).elim
    · exact .inr ⟨.inl v, port_left hp, target_port_left P Q hp⟩

/-- No translated lower path can pass through an upper vertex, or conversely. -/
private theorem vertex_meet (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e : (D₁.comp D₂).Edge) (v : (D₁.comp D₂).Vtx I)
    (h : Trace P Q e (vertex P Q v)) : Incident ((D₁.comp D₂).graph I) v e := by
  rcases v with v | v
  · rcases h with ⟨e', he, hp⟩ | ⟨hy, _⟩
    · obtain ⟨d, hd⟩ := P.vertex_meet e' v hp
      exact he ▸ ⟨d, port_left hd⟩
    · have := (P.vertex_rows v).2
      change P.height ≤ (P.vertex v).2 at hy
      omega
  · rcases h with ⟨e', _, hp⟩ | ⟨hy, e', he, hq⟩
    · have hh := P.row_le e' _ hp
      have := (Q.vertex_rows v).1
      change (Q.vertex v).2 + P.height ≤ P.height at hh
      omega
    · have hq' : Q.trace e' (Q.vertex v) := by
        simpa only [vertex, Sum.elim_inr, Function.comp_def, shift,
          Nat.add_sub_cancel_right, Prod.eta] using hq
      obtain ⟨d, hd⟩ := Q.vertex_meet e' v hq'
      exact he ▸ ⟨d, port_right hd⟩

private theorem cross_equal (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    {e : D₁.Edge} {f : D₂.Edge} {p : Point}
    (hp : P.trace e p) (hq : Shift P.height (Q.trace f) p) :
    compLeft D₁ D₂ e = compRight D₁ D₂ f := by
  have hy : p.2 = P.height := le_antisymm (P.row_le e p hp) hq.1
  obtain ⟨i, hi, hxi⟩ := (P.bottom_iff _ _).1 ((Prod.ext rfl hy : p = (p.1, P.height)) ▸ hp)
  obtain ⟨j, hj, hxj⟩ := (Q.top_iff _ _).1 (by simpa only [hy, Nat.sub_self] using hq.2)
  obtain rfl : i = j := Fin.ext (by omega)
  exact (congrArg (compLeft D₁ D₂) hi).symm.trans (congrArg (compRight D₁ D₂) hj)

/-- The common boundary joins equal edges, so new crossings cannot appear there. -/
private theorem meet (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (e f : (D₁.comp D₂).Edge) (p : Point) (hef : e ≠ f)
    (hp : Trace P Q e p) (hq : Trace P Q f p) :
    ∃ v, p = vertex P Q v ∧ Incident ((D₁.comp D₂).graph I) v e ∧
      Incident ((D₁.comp D₂).graph I) v f := by
  rcases hp with ⟨e', he, hp⟩ | ⟨hye, e', he, hp⟩ <;>
    rcases hq with ⟨f', hf, hq⟩ | ⟨hyf, f', hf, hq⟩
  · have hne : e' ≠ f' := fun h => hef (he.symm.trans ((congrArg _ h).trans hf))
    obtain ⟨v, hv, ⟨de, hde⟩, ⟨df, hdf⟩⟩ := P.meet e' f' p hne hp hq
    exact ⟨.inl v, hv, he ▸ ⟨de, port_left hde⟩, hf ▸ ⟨df, port_left hdf⟩⟩
  · exact (hef (he.symm.trans ((cross_equal P Q hp ⟨hyf, hq⟩).trans hf))).elim
  · exact (hef (he.symm.trans ((cross_equal P Q hq ⟨hye, hp⟩).symm.trans hf))).elim
  · have hne : e' ≠ f' := fun h => hef (he.symm.trans ((congrArg _ h).trans hf))
    obtain ⟨v, hv, ⟨de, hde⟩, ⟨df, hdf⟩⟩ := Q.meet e' f' _ hne hp hq
    have hpv : p = shift P.height (Q.vertex v) := by
      have hx := congrArg Prod.fst hv
      refine Prod.ext hx ?_
      have hh : p.2 - P.height = (Q.vertex v).2 := congrArg Prod.snd hv
      change p.2 = (Q.vertex v).2 + P.height
      omega
    exact ⟨.inr v, hpv, he ▸ ⟨de, port_right hde⟩, hf ▸ ⟨df, port_right hdf⟩⟩

/-- All false-direction ports remain first endpoints after stacking. -/
private theorem source_port (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (v : (D₁.comp D₂).Vtx I) (e : (D₁.comp D₂).Edge)
    (hp : HasPort ((D₁.comp D₂).graph I) v e false) : source P Q e = vertex P Q v := by
  rcases v with v | v
  · obtain ⟨e', he', rfl⟩ := (hasPort_map_iff (D₁.graph I) _ v e false).1 hp
    exact (source_left P Q e').trans (P.source_port v e' he')
  · obtain ⟨e', he', rfl⟩ := (hasPort_map_iff (D₂.graph I) _ v e false).1 hp
    exact source_port_right P Q he'

/-- All true-direction ports remain last endpoints after stacking. -/
private theorem target_port (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂)
    (v : (D₁.comp D₂).Vtx I) (e : (D₁.comp D₂).Edge)
    (hp : HasPort ((D₁.comp D₂).graph I) v e true) : target P Q e = vertex P Q v := by
  rcases v with v | v
  · obtain ⟨e', he', rfl⟩ := (hasPort_map_iff (D₁.graph I) _ v e true).1 hp
    exact target_port_left P Q he'
  · obtain ⟨e', he', rfl⟩ := (hasPort_map_iff (D₂.graph I) _ v e true).1 hp
    exact (target_right P Q e').trans (congrArg (shift P.height) (Q.target_port v e' he'))

end Comp

/-- Stack two orthogonal drawings, joining exactly the corresponding boundary edges. -/
noncomputable def comp (P : DiagramDrawing I D₁) (Q : DiagramDrawing I D₂) :
    DiagramDrawing I (D₁.comp D₂) := by
  classical
  refine
    { height := P.height + Q.height
      height_pos := by have := P.height_pos; omega
      vertex := Comp.vertex P Q
      vertex_injective := Comp.vertex_injective P Q
      vertex_rows := Comp.vertex_rows P Q
      vertex_separation := Comp.vertex_separation P Q
      source := Comp.source P Q
      target := Comp.target P Q
      trace := Comp.Trace P Q
      edge_rows := ?_
      path := ?_
      row_le := Comp.row_le P Q
      top_iff := Comp.top_iff P Q
      bottom_iff := Comp.bottom_iff P Q
      source_top := fun i => P.source_top i
      target_bottom := ?_
      source_spec := ?_
      target_spec := ?_
      source_port := Comp.source_port P Q
      target_port := Comp.target_port P Q
      vertex_meet := Comp.vertex_meet P Q
      meet := Comp.meet P Q }
  · rintro (i | (e | e))
    · exact Comp.edge_rows_left P Q (.inl i)
    · exact Comp.edge_rows_left P Q (.inr e)
    · exact Nat.add_lt_add_right (Q.edge_rows (.inr e)) P.height
  · rintro (i | (e | e))
    · exact Comp.path_left P Q (.inl i)
    · exact Comp.path_left P Q (.inr e)
    · exact Comp.path_new P Q e
  · intro j
    rw [bottom_comp, Comp.target_right, Q.target_bottom]
    simp only [shift]
    congr 1
    omega
  · rintro (i | (e | e))
    · exact Comp.source_spec_left P Q (.inl i)
    · exact Comp.source_spec_left P Q (.inr e)
    · rcases Q.source_spec (.inr e) with ⟨i, hi⟩ | ⟨v, hp, hv⟩
      · cases hi
      · exact .inr ⟨.inr v, Comp.port_right hp, congrArg (shift P.height) hv⟩
  · rintro (i | (e | e))
    · exact Comp.target_spec_left P Q (.inl i)
    · exact Comp.target_spec_left P Q (.inr e)
    · exact Comp.target_spec_right P Q (.inr e)

end Cslib.Complexity.NCL.GridDrawing
