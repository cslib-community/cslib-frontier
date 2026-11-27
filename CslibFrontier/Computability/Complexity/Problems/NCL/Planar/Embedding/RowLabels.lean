/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.CrossingRows
public import Mathlib.Data.Nat.Dist
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases

/-!
# Edge locality of the canonical planarization rows

The wire labels assign rows to the original stubs. Crossover interiors receive their crossing
row, and boundary labels extend through the supplied open implementations.

## Main results

* `Planar.Embedding.planeVertexRow_edge_bounds`: actual edge endpoints are at most two rows apart.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding
open Diagram

private def Near {E : Type*} (v : Vertex E) (row : ℕ) (owner : E → ℕ) : Prop :=
  ∀ p ∈ v.ports, row ≤ owner p.port.edge + 1 ∧ owner p.port.edge ≤ row + 1

private theorem near_map {E E' : Type*} {v : Vertex E} {row : ℕ} {owner : E' → ℕ}
    (f : E → E') (h : Near v row (owner ∘ f)) : Near (v.map f) row owner := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact h q hq

private structure RowLabeling {a b : List Color} (D : Diagram Prim a b)
    (row : D.Vtx Prim.interp → ℕ) (xs ys : List ℕ) where
  labels : Labeling D xs ys
  localPort : ∀ v, Near (D.graph Prim.interp v) (row v) labels.label

private def RowLabeling.comp {a b c : List Color} {D : Diagram Prim a b} {D' : Diagram Prim b c}
    {row : D.Vtx Prim.interp → ℕ} {row' : D'.Vtx Prim.interp → ℕ} {xs ys zs : List ℕ}
    (s : RowLabeling D row xs ys) (t : RowLabeling D' row' ys zs) :
    RowLabeling (D.comp D') (Sum.elim row row') xs zs where
  labels := s.labels.comp t.labels
  localPort := by
    rintro (v | v)
    · apply near_map (compLeft D D')
      rw [Labeling.comp_label_left]
      exact s.localPort v
    · apply near_map (compRight D D')
      rw [Labeling.comp_label_right]
      exact t.localPort v

private def RowLabeling.tensor {a b c d : List Color}
    {D : Diagram Prim a b} {D' : Diagram Prim c d}
    {row : D.Vtx Prim.interp → ℕ} {row' : D'.Vtx Prim.interp → ℕ}
    {xs ys xs' ys' : List ℕ} (s : RowLabeling D row xs ys) (t : RowLabeling D' row' xs' ys') :
    RowLabeling (D.tensor D') (Sum.elim row row') (xs ++ xs') (ys ++ ys') where
  labels := s.labels.tensor t.labels
  localPort := by
    rintro (v | v)
    · apply near_map (tensorLeft D D')
      rw [Labeling.tensor_label_left]
      exact s.localPort v
    · apply near_map (tensorRight D D')
      rw [Labeling.tensor_label_right]
      exact t.localPort v

private def RowLabeling.castLabels {a b : List Color} {D : Diagram Prim a b}
    {row : D.Vtx Prim.interp → ℕ} {xs ys xs' ys' : List ℕ}
    (hx : xs = xs') (hy : ys = ys') (L : RowLabeling D row xs ys) :
    RowLabeling D row xs' ys' := hx ▸ hy ▸ L

private def relabel {Γ : List Color → List Color → Type} {a b : List Color} {D : Diagram Γ a b}
    {Label : Type*} {xs ys : List Label} (L : Labeling D xs ys) (f : Label → ℕ) :
    Labeling D (xs.map f) (ys.map f) where
  label := f ∘ L.label
  top_eq := (List.ofFn_comp' (fun i : Fin a.length => L.label (.inl i)) f).trans
    (congrArg (List.map f) L.top_eq)
  bot_eq := (List.ofFn_comp' (fun i : Fin b.length => L.label (D.bottom i)) f).trans
    (congrArg (List.map f) L.bot_eq)

private noncomputable def extendLabels {Γ : List Color → List Color → Type} {I : Interp Γ}
    {a b : List Color} {D : Diagram Γ a b} {D' : Diagram Prim a b} {xs ys : List ℕ}
    (S : OpenSim I Prim.interp D D') (L : Labeling D xs ys) (row : ℕ) : Labeling D' xs ys where
  label := Function.extend S.ι L.label (fun _ => row)
  top_eq := by
    refine Eq.trans ?_ L.top_eq
    apply congrArg List.ofFn
    funext i
    exact (congrArg (Function.extend S.ι L.label (fun _ => row)) (S.ι_top i)).symm.trans
      (S.ι_injective.extend_apply L.label _ _)
  bot_eq := by
    refine Eq.trans ?_ L.bot_eq
    apply congrArg List.ofFn
    funext i
    exact (congrArg (Function.extend S.ι L.label (fun _ => row)) (S.ι_bottom i)).symm.trans
      (S.ι_injective.extend_apply L.label _ _)

private theorem extendLabels_near {Γ : List Color → List Color → Type} {I : Interp Γ}
    {a b : List Color} {D : Diagram Γ a b} {D' : Diagram Prim a b} {xs ys : List ℕ}
    (S : OpenSim I Prim.interp D D') (L : Labeling D xs ys) (row : ℕ)
    (hL : ∀ e, row ≤ L.label e + 1 ∧ L.label e ≤ row + 1) (v : D'.Vtx Prim.interp) :
    Near (D'.graph Prim.interp v) row (extendLabels S L row).label := by
  classical
  intro p _hp
  by_cases he : ∃ e, S.ι e = p.port.edge
  · obtain ⟨e, he⟩ := he
    simp only [extendLabels, ← he, S.ι_injective.extend_apply]
    exact hL e
  · simp only [extendLabels, Function.extend_apply' _ _ _ he]
    omega

private def crossingLabels (c d : Color) (a b : ℕ) :
    Labeling (gen (Prim.cross c d)) [a, b] [b, a] where
  label := Sum.elim (fun i => if i.val = 0 then a else b) (fun i => if i.val = 0 then b else a)
  top_eq := rfl
  bot_eq := rfl

private noncomputable def crossingRows (c d : Color) (a b : ℕ)
    (hab : a ≤ b + 1) (hba : b ≤ a + 1) :
    RowLabeling (Crossover.diagram c d) (fun _ => min a b) [a, b] [b, a] where
  labels := extendLabels (Crossover.openSim c d) (crossingLabels c d a b) (min a b)
  localPort := by
    apply extendLabels_near
    have hA : min a b ≤ a + 1 ∧ a ≤ min a b + 1 := by omega
    have hB : min a b ≤ b + 1 ∧ b ≤ min a b + 1 := by omega
    intro e
    rcases e with i | i <;> fin_cases i
    · exact hA
    · exact hB
    · exact hB
    · exact hA

private def atRow (pairs : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  let pair := pairs.getD i (0, 0)
  min pair.1 pair.2

private theorem atRow_append_left (xs ys : List (ℕ × ℕ)) (i : ℕ) (hi : i < xs.length) :
    atRow (xs ++ ys) i = atRow xs i := by
  simp only [atRow, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem atRow_append_right (xs ys : List (ℕ × ℕ)) (i : ℕ) :
    atRow (xs ++ ys) (xs.length + i) = atRow ys i := by
  simp only [atRow, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

private theorem atRow_crossingPairs_append_left {Γ : List Color → List Color → Type}
    {a b : List Color} (D : Diagram Γ a b) (label : D.Edge → ℕ) (ys : List (ℕ × ℕ)) (i : ℕ)
    (hi : i < D.swapCount) :
    atRow (D.crossingPairs label ++ ys) i = atRow (D.crossingPairs label) i :=
  atRow_append_left _ _ _ (by rw [length_crossingPairs]; exact hi)

private theorem atRow_crossingPairs_append_right {Γ : List Color → List Color → Type}
    {a b : List Color} (D : Diagram Γ a b) (label : D.Edge → ℕ) (ys : List (ℕ × ℕ)) (i : ℕ) :
    atRow (D.crossingPairs label ++ ys) (D.swapCount + i) = atRow ys i := by
  rw [← length_crossingPairs D label]
  exact atRow_append_right _ _ _

private def wireVertexRow {Γ : List Color → List Color → Type}
    (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) {a b : List Color}
    (D : Diagram Γ a b) (h : D.checkGens (fun _ => false) = true) (label : D.Edge → ℕ)
    (v : (planarizeAlong H D).Vtx Prim.interp) : ℕ :=
  atRow (D.crossingPairs label) (crossingOrigin H D h v).val

private theorem wireVertexRow_comp {Γ : List Color → List Color → Type}
    (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) {a b c : List Color}
    (D : Diagram Γ a b) (D' : Diagram Γ b c)
    (h : (D.comp D').checkGens (fun _ => false) = true) (label : (D.comp D').Edge → ℕ) :
    wireVertexRow H (D.comp D') h label =
      Sum.elim
        (wireVertexRow H D (Bool.and_eq_true_iff.mp h).1 (label ∘ compLeft D D'))
        (wireVertexRow H D' (Bool.and_eq_true_iff.mp h).2 (label ∘ compRight D D')) := by
  funext v
  rcases v with v | v
  · exact atRow_crossingPairs_append_left D (label ∘ compLeft D D') _ _
      (crossingOrigin H D (Bool.and_eq_true_iff.mp h).1 v).isLt
  · exact atRow_crossingPairs_append_right D (label ∘ compLeft D D')
      (D'.crossingPairs (label ∘ compRight D D')) _

private theorem wireVertexRow_tensor {Γ : List Color → List Color → Type}
    (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) {a b c d : List Color}
    (D : Diagram Γ a b) (D' : Diagram Γ c d)
    (h : (D.tensor D').checkGens (fun _ => false) = true) (label : (D.tensor D').Edge → ℕ) :
    wireVertexRow H (D.tensor D') h label =
      Sum.elim
        (wireVertexRow H D (Bool.and_eq_true_iff.mp h).1 (label ∘ tensorLeft D D'))
        (wireVertexRow H D' (Bool.and_eq_true_iff.mp h).2 (label ∘ tensorRight D D')) := by
  funext v
  rcases v with v | v
  · exact atRow_crossingPairs_append_left D (label ∘ tensorLeft D D') _ _
      (crossingOrigin H D (Bool.and_eq_true_iff.mp h).1 v).isLt
  · exact atRow_crossingPairs_append_right D (label ∘ tensorLeft D D')
      (D'.crossingPairs (label ∘ tensorRight D D')) _

private def CrossNear {Γ : List Color → List Color → Type} {a b : List Color}
    (D : Diagram Γ a b) (label : D.Edge → ℕ) : Prop :=
  ∀ x y, (x, y) ∈ D.crossingPairs label → x ≤ y + 1 ∧ y ≤ x + 1

private noncomputable def wireRows {Γ : List Color → List Color → Type}
    (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) :
    ∀ {a b : List Color} (D : Diagram Γ a b)
      (h : D.checkGens (fun _ => false) = true) (label : D.Edge → ℕ), CrossNear D label →
      RowLabeling (planarizeAlong H D) (wireVertexRow H D h label)
        (D.topList label) (D.botList label)
  | _, _, .gen _, h, _, _ => by cases h
  | _, _, .id _, _, label, _ =>
      ⟨⟨label, rfl, rfl⟩, fun v => v.elim⟩
  | _, _, .swap c d, _, label, hl => by
      have h := hl (label (.inl 0)) (label (.inl 1)) (by simp [crossingPairs])
      exact crossingRows c d (label (.inl 0)) (label (.inl 1)) h.1 h.2
  | _, _, .comp D D', h, label, hl => by
      let left := wireRows H D (Bool.and_eq_true_iff.mp h).1 (label ∘ compLeft D D')
        (fun x y hp => hl x y (List.mem_append_left _ hp))
      let right := wireRows H D' (Bool.and_eq_true_iff.mp h).2 (label ∘ compRight D D')
        (fun x y hp => hl x y (List.mem_append_right _ hp))
      change RowLabeling ((planarizeAlong H D).comp (planarizeAlong H D')) _ _ _
      simpa only [wireVertexRow_comp, topList_compLeft, botList_compRight] using left.comp right
  | _, _, .tensor D D', h, label, hl => by
      let left := wireRows H D (Bool.and_eq_true_iff.mp h).1 (label ∘ tensorLeft D D')
        (fun x y hp => hl x y (List.mem_append_left _ hp))
      let right := wireRows H D' (Bool.and_eq_true_iff.mp h).2 (label ∘ tensorRight D D')
        (fun x y hp => hl x y (List.mem_append_right _ hp))
      change RowLabeling ((planarizeAlong H D).tensor (planarizeAlong H D')) _ _ _
      simpa only [wireVertexRow_tensor, topList_tensor, botList_tensor] using left.tensor right

private noncomputable def sourceRows_one {Label : Type*} (color : Label → Color)
    (tags : List Label) (need : ℕ) (owner : Label → ℕ) (row : ℕ)
    (h : ∀ tag ∈ tags, row ≤ owner tag + 1 ∧ owner tag ≤ row + 1) :
    RowLabeling (Cell.expand (Cell.source (tags.map color) need)) (fun _ => row) []
      (tags.map owner) where
  labels := extendLabels (Cell.expandOpenSim (Cell.source (tags.map color) need))
    (relabel (Sources.labels color tags need) owner) row
  localPort := by
    apply extendLabels_near
    rintro (i | i)
    · exact i.elim0
    · change row ≤ owner (tags.get (i.cast (List.length_map ..))) + 1 ∧
        owner (tags.get (i.cast (List.length_map ..))) ≤ row + 1
      exact h _ (List.get_mem ..)

private noncomputable def capRows_one (color : Color) (row : ℕ) :
    RowLabeling (Gadgets.Wire.cap color) (fun _ => row) [row, row] [] where
  labels := extendLabels (Cell.expandOpenSim (Cell.cap color))
    ⟨fun _ => row, rfl, rfl⟩ row
  localPort := by
    apply extendLabels_near
    intro _
    change row ≤ row + 1 ∧ row ≤ row + 1
    omega

private noncomputable def sourceRows {E : Type*} (color : Port E → Color) (owner : Port E → ℕ) :
    ∀ (vs : List (Vertex E)) (row : Fin vs.length → ℕ),
      (∀ i p, p ∈ (vs.get i).ports → row i ≤ owner p.port + 1 ∧ owner p.port ≤ row i + 1) →
      RowLabeling (planarizeAlong Cell.expand (Sources.vertices color vs).diagram)
        (row ∘ sourceVertexOrigin color vs) [] ((Sources.vertexLabels vs).map owner)
  | [], _, _ => ⟨Labeling.id [] [] rfl, fun v => v.elim⟩
  | v :: vs, row, h => by
      let first := sourceRows_one color (v.ports.map WeightedPort.port) v.minInflow owner (row 0)
        (by
          intro tag ht
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
          exact h 0 p hp)
      let rest := sourceRows color owner vs (fun i => row i.succ) (fun i p hp => h i.succ p hp)
      change RowLabeling
        ((Cell.expand (Cell.source ((v.ports.map WeightedPort.port).map color) v.minInflow)).tensor
          (planarizeAlong Cell.expand (Sources.vertices color vs).diagram))
        (row ∘ Sum.elim (fun _ => 0) (fun w => (sourceVertexOrigin color vs w).succ)) _ _
      erw [Sum.comp_elim]
      simpa only [Function.comp_def, Sources.vertexLabels, List.flatMap_cons, List.map_append,
        List.nil_append] using
        first.tensor rest

private noncomputable def capRows {E : Type*} (color : E → Color) (owner : E → ℕ) :
    ∀ es : List E,
      RowLabeling (planarizeAlong Cell.expand (Sinks.caps color es).diagram)
        (owner ∘ capVertexOrigin color es)
        ((Sinks.pairLabels es).map fun p => owner p.edge) []
  | [] => ⟨Labeling.id [] [] rfl, fun v => v.elim⟩
  | e :: es => by
      let first := capRows_one (color e) (owner e)
      let rest := capRows color owner es
      change RowLabeling ((Gadgets.Wire.cap (color e)).tensor
        (planarizeAlong Cell.expand (Sinks.caps color es).diagram))
        (owner ∘ Sum.elim (fun _ => e) (capVertexOrigin color es)) _ _
      erw [Sum.comp_elim]
      simpa only [Function.comp_def, Sinks.pairLabels, List.flatMap_cons, List.map_append,
        List.map_cons, List.map_nil, List.nil_append, List.append_nil] using first.tensor rest

private theorem atRow_map_get {Label : Type*} (pairs : List (Label × Label))
    (owner : Label → ℕ) (i : Fin pairs.length) :
    atRow (pairs.map (Prod.map owner owner)) i.val =
      min (owner (pairs.get i).1) (owner (pairs.get i).2) := by
  have hi : i.val < (pairs.map (Prod.map owner owner)).length := by
    simpa only [List.length_map] using i.isLt
  unfold atRow
  rw [← List.getElem_eq_getD (h := hi) (0, 0)]
  simp only [List.getElem_map, Prod.map, List.get_eq_getElem]

private noncomputable def wiringRows {m : ℕ} (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (srcRow ownerRow : Port (Fin m) → ℕ)
    (hxs : (Sources.vertexLabels vs).Pairwise (fun a b => srcRow a ≤ srcRow b))
    (hys : (Sinks.pairLabels (List.finRange m)).Pairwise (fun a b => ownerRow a ≤ ownerRow b))
    (hrow : ∀ a ∈ Sources.vertexLabels vs,
      ownerRow a ≤ srcRow a ∧ srcRow a ≤ ownerRow a + 1) :
    RowLabeling (planarizeAlong Cell.expand (routing vs color hw).diagram)
      (fun v => crossingRow vs color hw ownerRow
        (crossingOrigin Cell.expand _ (routing vs color hw).noGens v))
      ((Sources.vertexLabels vs).map ownerRow)
      ((Sinks.pairLabels (List.finRange m)).map ownerRow) := by
  let W := routing vs color hw
  let L := relabel W.labeling ownerRow
  have hl : CrossNear W.diagram L.label := by
    intro a b hp
    change (a, b) ∈ W.diagram.crossingPairs (ownerRow ∘ W.labeling.label) at hp
    rw [crossingPairs_map] at hp
    obtain ⟨⟨x, y⟩, hxy, he⟩ := List.mem_map.mp hp
    obtain ⟨ha, hb⟩ := Prod.mk.inj he
    subst a
    subst b
    change (x, y) ∈ (routing vs color hw).diagram.crossingPairs
      (routing vs color hw).labeling.label at hxy
    unfold routing at hxy
    rw [Wiring.crossingPairs_cast] at hxy
    obtain ⟨hyx, hxy⟩ := owner_bounds_crossingPairs_reorder (fun p => color p.edge) _ _
      (incidencePerm vs hw) srcRow ownerRow hxs hys hrow hxy
    exact ⟨hxy, hyx.trans (Nat.le_succ _)⟩
  let R := (wireRows Cell.expand W.diagram W.noGens L.label hl).castLabels L.top_eq L.bot_eq
  have hr : wireVertexRow Cell.expand W.diagram W.noGens L.label =
      fun v => crossingRow vs color hw ownerRow
        (crossingOrigin Cell.expand W.diagram W.noGens v) := by
    funext v
    let k := crossingOrigin Cell.expand W.diagram W.noGens v
    let i := k.cast (length_crossingPairs W.diagram W.labeling.label).symm
    change atRow (W.diagram.crossingPairs (ownerRow ∘ W.labeling.label)) i.val =
      min (ownerRow ((W.diagram.crossingPairs W.labeling.label).get i).1)
        (ownerRow ((W.diagram.crossingPairs W.labeling.label).get i).2)
    rw [crossingPairs_map]
    exact atRow_map_get _ _ i
  exact hr ▸ R

section Layout
variable {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (vertexRow : Fin vs.length → ℕ) (srcRow : Port (Fin m) → ℕ) (ownerRow : Fin m → ℕ)
    (hxs : (Sources.vertexLabels vs).Pairwise (fun a b => srcRow a ≤ srcRow b))
    (hys : (Sinks.pairLabels (List.finRange m)).Pairwise
      (fun a b => ownerRow a.edge ≤ ownerRow b.edge))
    (hrow : ∀ a ∈ Sources.vertexLabels vs,
      ownerRow a.edge ≤ srcRow a ∧ srcRow a ≤ ownerRow a.edge + 1)
    (hports : ∀ i p, p ∈ (vs.get i).ports →
      vertexRow i ≤ ownerRow p.port.edge + 1 ∧ ownerRow p.port.edge ≤ vertexRow i + 1)

private noncomputable def planeRows :
    RowLabeling (planeDiagram vs hw) (planeVertexRow vs hw vertexRow ownerRow) [] [] := by
  let source := sourceRows (fun p => color vs p.edge) (fun p => ownerRow p.edge) vs vertexRow hports
  let middle := wiringRows vs (color vs) hw srcRow (fun p => ownerRow p.edge) hxs hys hrow
  let sink := capRows (color vs) ownerRow (List.finRange m)
  let total := source.comp (middle.comp sink)
  have hr : planeVertexRow vs hw vertexRow ownerRow =
      Sum.elim (vertexRow ∘ sourceVertexOrigin (fun p => color vs p.edge) vs)
        (Sum.elim
          (fun v => crossingRow vs (color vs) hw (fun p => ownerRow p.edge)
            (crossingOrigin Cell.expand _ (routing vs (color vs) hw).noGens v))
          (ownerRow ∘ capVertexOrigin (color vs) (List.finRange m))) := by
    funext v
    rcases v with v | v | v <;> rfl
  exact hr.symm ▸ total

include hxs hys hrow hports in
/-- Every actual planarized edge joins vertices in rows at distance at most two. -/
theorem planeVertexRow_edge_bounds
    (u v : (planeDiagram vs hw).Vtx Prim.interp)
    (p : WeightedPort (planeDiagram vs hw).Edge)
    (hp : p ∈ ((planeDiagram vs hw).graph Prim.interp u).ports)
    (q : WeightedPort (planeDiagram vs hw).Edge)
    (hq : q ∈ ((planeDiagram vs hw).graph Prim.interp v).ports)
    (he : p.port.edge = q.port.edge) :
    Nat.dist (planeVertexRow vs hw vertexRow ownerRow u)
      (planeVertexRow vs hw vertexRow ownerRow v) ≤ 2 := by
  let R := planeRows vs hw vertexRow srcRow ownerRow hxs hys hrow hports
  have hu := R.localPort u p hp
  have hv := R.localPort v q hq
  rw [he] at hu
  simp only [Nat.dist]
  omega

end Layout

end Cslib.Complexity.NCL.Planar.Embedding
