/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridPath
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Basic

/-!
# Orthogonal graph drawings

Every edge has an actual finite orthogonal path. Vertex incidences determine its two endpoints;
paths meet only at common incident vertices and avoid all other vertices.

## Main definitions

* `Cslib.Complexity.NCL.GridDrawing.Open`: a drawing with ordered open boundaries.
* `Cslib.Complexity.NCL.GridDrawing.Closed`: a drawing of a constraint graph.

## Main results

* `Cslib.Complexity.NCL.GridDrawing.Open.close`: close empty boundary interfaces.
-/

public section

namespace Cslib.Complexity.NCL.GridDrawing

open GridRouting Diagram

variable {V E : Type*}

/-- An edge has a port with the specified reference direction at a vertex. -/
@[expose] def HasPort (G : ConstraintGraph V E) (v : V) (e : E) (d : Bool) : Prop :=
  ∃ weight, ⟨⟨e, d⟩, weight⟩ ∈ (G v).ports

/-- Edge renaming carries ports to the corresponding renamed edges. -/
theorem HasPort.map {E' : Type*} {G : ConstraintGraph V E} {v : V} {e : E} {d : Bool}
    (h : HasPort G v e d) (f : E → E') : HasPort (G.map f) v (f e) d := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, List.mem_map.2 ⟨⟨⟨e, d⟩, w⟩, hw, rfl⟩⟩

/-- Every renamed port comes from an original port of the same direction. -/
theorem hasPort_map_iff {E' : Type*} (G : ConstraintGraph V E) (f : E → E')
    (v : V) (e' : E') (d : Bool) :
    HasPort (G.map f) v e' d ↔ ∃ e, HasPort G v e d ∧ f e = e' := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨⟨⟨e, d'⟩, w'⟩, hp, he⟩ := List.mem_map.1 hw
    simp only [WeightedPort.map, WeightedPort.mk.injEq, Port.map, Port.mk.injEq] at he
    obtain ⟨⟨he, rfl⟩, rfl⟩ := he
    exact ⟨e, ⟨_, hp⟩, he⟩
  · rintro ⟨e, hp, rfl⟩
    exact hp.map f

/-- An edge is incident to a vertex. -/
@[expose] def Incident (G : ConstraintGraph V E) (v : V) (e : E) : Prop := ∃ d, HasPort G v e d

/-- A finite orthogonal path lying in a specified trace. -/
@[expose] def Connected (T : Point → Prop) (p q : Point) : Prop :=
  ∃ P : Path p q, ∀ x, P.Contains x → T x

/-- Enlarging a trace preserves the same path witness. -/
theorem Connected.mono {T U : Point → Prop} {p q : Point} (h : Connected T p q)
    (hTU : ∀ x, T x → U x) : Connected U p q := by
  obtain ⟨P, hp⟩ := h
  exact ⟨P, fun x hx => hTU x (hp x hx)⟩

/-- Paths with matching endpoints concatenate inside a common trace. -/
theorem Connected.comp {T : Point → Prop} {p q r : Point}
    (h : Connected T p q) (h' : Connected T q r) : Connected T p r := by
  obtain ⟨P, hp⟩ := h
  obtain ⟨Q, hq⟩ := h'
  exact ⟨P.comp Q, fun x hx => hx.elim (hp x) (hq x)⟩

/-- Shift a point down by an integer number of rows. -/
@[expose] def shift (dy : ℕ) (p : Point) : Point := (p.1, p.2 + dy)

/-- Shift the trace down by the same number of rows. -/
@[expose] def Shift (dy : ℕ) (T : Point → Prop) (p : Point) : Prop :=
  dy ≤ p.2 ∧ T (p.1, p.2 - dy)

/-- Translate a path and its containing trace. -/
theorem Connected.shift {T : Point → Prop} {p q : Point} (h : Connected T p q) (dy : ℕ) :
    Connected (Shift dy T) (shift dy p) (shift dy q) := by
  change Connected (Shift dy T) (p.1, p.2 + dy) (q.1, q.2 + dy)
  obtain ⟨P, hp⟩ := h
  refine ⟨(P.translate 0 dy).cast (by simp) (by simp), ?_⟩
  intro x hx
  rw [Path.contains_cast_iff, Path.contains_translate] at hx
  exact ⟨hx.2.1, hp _ (by simpa only [Nat.sub_zero] using hx.2.2)⟩

/-- A graph drawing with explicit ordered top and bottom boundary ports. -/
structure Open (G : ConstraintGraph V E) {m n : ℕ} (top : Fin m → E) (bottom : Fin n → E) where
  /-- Total drawing height. -/
  height : ℕ
  /-- Positive height separates the two boundary interfaces. -/
  height_pos : 0 < height
  /-- Integer-grid vertex positions. -/
  vertex : V → Point
  /-- Distinct vertices occupy distinct points. -/
  vertex_injective : Function.Injective vertex
  /-- Vertices lie strictly between the two boundary rows. -/
  vertex_rows (v) : 0 < (vertex v).2 ∧ (vertex v).2 < height
  /-- Different vertices have at least one unoccupied integer row between them. -/
  vertex_separation (v w) : v ≠ w →
    (vertex v).2 + 1 < (vertex w).2 ∨ (vertex w).2 + 1 < (vertex v).2
  /-- The first endpoint of each edge path. -/
  source : E → Point
  /-- The last endpoint of each edge path. -/
  target : E → Point
  /-- A containing trace for each edge. -/
  trace : E → Point → Prop
  /-- Each edge runs strictly downwards between its endpoint rows. -/
  edge_rows (e) : (source e).2 < (target e).2
  /-- An actual finite orthogonal path inside that trace. -/
  path (e) : Connected (trace e) (source e) (target e)
  /-- All trace points stay within the drawing's row band. -/
  row_le (e p) : trace e p → p.2 ≤ height
  /-- The top row contains exactly the ordered input ports. -/
  top_iff (e x) : trace e (x, 0) ↔ ∃ i, top i = e ∧ x = 4 * i.val
  /-- The bottom row contains exactly the ordered output ports. -/
  bottom_iff (e x) : trace e (x, height) ↔ ∃ j, bottom j = e ∧ x = 4 * j.val
  /-- The first endpoint of each input wire is its top port. -/
  source_top (i) : source (top i) = (4 * i.val, 0)
  /-- The last endpoint of each output wire is its bottom port. -/
  target_bottom (j) : target (bottom j) = (4 * j.val, height)
  /-- Every first endpoint is an input port or a false-direction vertex port. -/
  source_spec (e) : (∃ i, top i = e) ∨ ∃ v, HasPort G v e false ∧ source e = vertex v
  /-- Every last endpoint is an output port or a true-direction vertex port. -/
  target_spec (e) : (∃ j, bottom j = e) ∨ ∃ v, HasPort G v e true ∧ target e = vertex v
  /-- False-direction ports are the first endpoints. -/
  source_port (v e) : HasPort G v e false → source e = vertex v
  /-- True-direction ports are the last endpoints. -/
  target_port (v e) : HasPort G v e true → target e = vertex v
  /-- An edge avoids every vertex not incident to it. -/
  vertex_meet (e v) : trace e (vertex v) → Incident G v e
  /-- Distinct edge traces meet only at a common incident vertex. -/
  meet (e f p) : e ≠ f → trace e p → trace f p →
    ∃ v, p = vertex v ∧ Incident G v e ∧ Incident G v f

/-- A complete orthogonal drawing with one explicit finite path for every graph edge. -/
structure Closed (G : ConstraintGraph V E) where
  /-- Vertex positions on the grid. -/
  vertex : V → Point
  /-- Distinct vertices are distinct points. -/
  vertex_injective : Function.Injective vertex
  /-- Different vertex rows have a gap, excluding shared unit segments between vertices. -/
  vertex_separation (v w) : v ≠ w →
    (vertex v).2 + 1 < (vertex w).2 ∨ (vertex w).2 + 1 < (vertex v).2
  /-- The false-direction endpoint of each edge. -/
  source : E → V
  /-- The true-direction endpoint of each edge. -/
  target : E → V
  /-- The source vertex has the declared port. -/
  source_port (e) : HasPort G (source e) e false
  /-- The target vertex has the declared port. -/
  target_port (e) : HasPort G (target e) e true
  /-- Every edge has strictly increasing endpoint rows. -/
  edge_rows (e) : (vertex (source e)).2 < (vertex (target e)).2
  /-- Every graph edge is a finite orthogonal path between those endpoints. -/
  path (e) : Path (vertex (source e)) (vertex (target e))
  /-- Every listed false-direction port occurs at its path's source. -/
  source_eq (v e) : HasPort G v e false → source e = v
  /-- Every listed true-direction port occurs at its path's target. -/
  target_eq (v e) : HasPort G v e true → target e = v
  /-- A path avoids nonincident vertices. -/
  vertex_meet (e v) : (path e).Contains (vertex v) → Incident G v e
  /-- Distinct paths meet only at common incident vertices. -/
  meet (e f p) : e ≠ f → (path e).Contains p → (path f).Contains p →
    ∃ v, p = vertex v ∧ Incident G v e ∧ Incident G v f

/-- Positive row displacement excludes loop edges. -/
theorem Closed.source_ne_target {G : ConstraintGraph V E} (D : Closed G) (e : E) :
    D.source e ≠ D.target e := by
  intro he
  have hr := D.edge_rows e
  rw [he] at hr
  exact Nat.lt_irrefl _ hr

/-- Open drawings of a diagram use its own ordered boundary edge maps. -/
abbrev DiagramDrawing {Γ : List Color → List Color → Type} (I : Diagram.Interp Γ)
    {a b : List Color} (D : Diagram Γ a b) :=
  Open (D.graph I) Sum.inl D.bottom

/-- Empty boundary interfaces turn an open drawing into a drawing of the graph itself. -/
@[expose] noncomputable def Open.close {G : ConstraintGraph V E}
    {top bottom : Fin 0 → E} (D : Open G top bottom) : Closed G := by
  classical
  have hs (e) : ∃ v, HasPort G v e false ∧ D.source e = D.vertex v :=
    (D.source_spec e).resolve_left (fun ⟨i, _⟩ => i.elim0)
  have ht (e) : ∃ v, HasPort G v e true ∧ D.target e = D.vertex v :=
    (D.target_spec e).resolve_left (fun ⟨i, _⟩ => i.elim0)
  let s (e) := (hs e).choose
  let t (e) := (ht e).choose
  have hsp (e) : HasPort G (s e) e false := (hs e).choose_spec.1
  have htp (e) : HasPort G (t e) e true := (ht e).choose_spec.1
  have hse (e) : D.source e = D.vertex (s e) := (hs e).choose_spec.2
  have hte (e) : D.target e = D.vertex (t e) := (ht e).choose_spec.2
  let P (e) : Path (D.vertex (s e)) (D.vertex (t e)) :=
    (D.path e).choose.cast (hse e) (hte e)
  have hP (e p) : (P e).Contains p → D.trace e p := by
    intro hp
    exact (D.path e).choose_spec p ((Path.contains_cast_iff _ _ _ _).1 hp)
  exact
    { vertex := D.vertex
      vertex_injective := D.vertex_injective
      vertex_separation := D.vertex_separation
      source := s
      target := t
      source_port := hsp
      target_port := htp
      edge_rows e := by rw [← hse e, ← hte e]; exact D.edge_rows e
      path := P
      source_eq := fun v e h => D.vertex_injective ((hse e).symm.trans (D.source_port v e h))
      target_eq := fun v e h => D.vertex_injective ((hte e).symm.trans (D.target_port v e h))
      vertex_meet := fun e v h => D.vertex_meet e v (hP e _ h)
      meet := fun e f p h h₁ h₂ => D.meet e f p h (hP e p h₁) (hP f p h₂) }

end Cslib.Complexity.NCL.GridDrawing
