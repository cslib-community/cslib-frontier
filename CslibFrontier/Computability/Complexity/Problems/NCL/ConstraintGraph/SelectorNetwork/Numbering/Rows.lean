/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Numbering
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Sparse
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Incidence

/-!
# Source and owner rows in explicit finite numbering

Source-cell order is retained by the vertex and edge enumerations. Ports recover their source
cell from the original endpoint or private-wire owner, so canonical drawing labels inherit the
source row order and consecutive owner rows.

## Main definitions

* `SelectorNetwork.AndOr.Numbering.vertexRow`: the row of a numbered implementation vertex.
* `SelectorNetwork.AndOr.Numbering.ownerRow`: the row of a numbered wire's owner.
* `SelectorNetwork.AndOr.Numbering.portRow`: the source row of an actual incidence label.

## Main results

* `SelectorNetwork.AndOr.Numbering.vertexLabels_pairwise`: source labels are ordered by row.
* `SelectorNetwork.AndOr.Numbering.pairLabels_pairwise`: paired labels are ordered by owner row.
-/

public section

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr.Numbering

variable {U C R : Type*} [DecidableEq U] [DecidableEq C] [DecidableEq R]
variable (N : SelectorNetwork U C R) (A : RowSection N)
variable {m : ℕ} (order : Vert U C R ≃ Fin m) (row : Vert U C R → ℕ)

private theorem pairwise_flatMap_row {α β : Type*} (xs : List α) (f : α → List β)
    (r : α → ℕ) (s : β → ℕ) (hxs : xs.Pairwise (fun a b => r a ≤ r b))
    (hf : ∀ a, ∀ b ∈ f a, s b = r a) :
    (xs.flatMap f).Pairwise (fun a b => s a ≤ s b) :=
  List.pairwise_flatMap.mpr
    ⟨fun a _ => List.pairwise_of_forall_mem_list fun b hb c hc => by rw [hf a b hb, hf a c hc],
      hxs.imp fun {a b} hab x hx y hy => by simpa only [hf a x hx, hf b y hy] using hab⟩

omit [DecidableEq U] [DecidableEq C] [DecidableEq R] in
private theorem source_pairwise
    (hrow : Monotone (fun i => row (order.symm i))) :
    (List.ofFn order.symm).Pairwise (fun a b => row a ≤ row b) :=
  List.pairwise_ofFn.mpr (fun _ _ hij => hrow hij.le)

omit [DecidableEq R] in
private theorem vertexList_pairwise
    (hrow : Monotone (fun i => row (order.symm i))) :
    (vertexList N A order).Pairwise (fun a b => row a.1 ≤ row b.1) := by
  unfold vertexList List.sigma
  apply pairwise_flatMap_row _ _ row (fun v : TargetVertex N A => row v.1)
    (source_pairwise order row hrow)
  intro v w hw
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hw
  rfl

/-- Source row of a numbered standard vertex. -/
@[expose] def vertexRow (i : Fin (vertexList N A order).length) : ℕ :=
  row ((vertexEquiv N A order).symm i).1

/-- Owner row of a numbered shared or private implementation wire. -/
@[expose] def ownerRow (e : Fin (edgeList N A order).length) : ℕ :=
  row (edgeOwner N A ((edgeEquiv N A order).symm e))

/-- Actual source row of a numbered incidence label. -/
@[expose] def portRow (p : Port (Fin (edgeList N A order).length)) : ℕ :=
  row (cellEndpoint N A ((edgeEquiv N A order).symm p.edge) p.dir)

/-- A numbered port has the row of the vertex containing it. -/
theorem portRow_of_mem (i : Fin (vertexList N A order).length)
    (p : WeightedPort (Fin (edgeList N A order).length)) (hp : p ∈ (graph N A order i).ports) :
    portRow N A order row p.port = vertexRow N A order row i := by
  change p ∈ ((AndOr.graph N A ((vertexEquiv N A order).symm i)).ports.map
    (WeightedPort.map (edgeEquiv N A order))) at hp
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
  simpa only [portRow, vertexRow, WeightedPort.map, Port.map, Equiv.symm_apply_apply] using
    congrArg row (cellEndpoint_of_mem N A _ p hp')

/-- A source edge's same-or-next-row discipline extends to every implementation port. -/
theorem portRow_bounds
    (h : ∀ e d, row (N.endpoints.endpoint e false) ≤ row (N.endpoints.endpoint e d) ∧
      row (N.endpoints.endpoint e d) ≤ row (N.endpoints.endpoint e false) + 1)
    (p : Port (Fin (edgeList N A order).length)) :
    ownerRow N A order row p.edge ≤ portRow N A order row p ∧
      portRow N A order row p ≤ ownerRow N A order row p.edge + 1 := by
  unfold ownerRow portRow
  generalize he : (edgeEquiv N A order).symm p.edge = e
  rcases e with e | ⟨v, e⟩
  · have ho : edgeOwner N A (.inl e) = N.endpoints.endpoint e false := by cases e <;> rfl
    simpa only [cellEndpoint, ho] using h e p.dir
  · simp only [cellEndpoint, edgeOwner, le_refl, true_and, Nat.le_add_right]

/-- Numbered standard vertices retain the supplied monotone source-cell row order. -/
private theorem monotone_vertexRow (hrow : Monotone (fun i => row (order.symm i))) :
    Monotone (vertexRow N A order row) := fun i j hij => by
  change row ((vertexList N A order).get i).1 ≤ row ((vertexList N A order).get j).1
  exact (vertexList_pairwise N A order row hrow).rel_get_of_le hij

/-- Numbered edges retain their owners' source-cell row order. -/
private theorem monotone_ownerRow (hrow : Monotone (fun i => row (order.symm i))) :
    Monotone (ownerRow N A order row) := by
  have hs : (edgeList N A order).Pairwise
      (fun a b => row (edgeOwner N A a) ≤ row (edgeOwner N A b)) := by
    unfold edgeList
    exact pairwise_flatMap_row _ _ row (fun e => row (edgeOwner N A e))
      (source_pairwise order row hrow) fun v e he =>
        congrArg row (owner_mem_localEdges N A v e he)
  intro i j hij
  change row (edgeOwner N A ((edgeList N A order).get i)) ≤
    row (edgeOwner N A ((edgeList N A order).get j))
  exact hs.rel_get_of_le hij

/-- The actual incidence list is ordered by the source rows of its vertex occurrences. -/
theorem vertexLabels_pairwise (hrow : Monotone (fun i => row (order.symm i))) :
    (Planar.Embedding.Sources.vertexLabels (List.ofFn (graph N A order))).Pairwise
      (fun a b => portRow N A order row a ≤ portRow N A order row b) := by
  unfold Planar.Embedding.Sources.vertexLabels
  rw [List.ofFn_eq_map, List.flatMap_map]
  apply pairwise_flatMap_row (List.finRange _) _ (vertexRow N A order row) (portRow N A order row)
  · rw [← List.ofFn_id]
    exact List.pairwise_ofFn.mpr (fun _ _ hij => monotone_vertexRow N A order row hrow hij.le)
  · intro i p hp
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
    exact portRow_of_mem N A order row i p hp'

/-- The actual edge-pair target list is ordered by owner row. -/
theorem pairLabels_pairwise (hrow : Monotone (fun i => row (order.symm i))) :
    (Planar.Embedding.Sinks.pairLabels (List.finRange (edgeList N A order).length)).Pairwise
      (fun a b => ownerRow N A order row a.edge ≤ ownerRow N A order row b.edge) := by
  unfold Planar.Embedding.Sinks.pairLabels
  apply pairwise_flatMap_row _ _ (ownerRow N A order row)
    (fun p : Port (Fin (edgeList N A order).length) => ownerRow N A order row p.edge)
  · rw [← List.ofFn_id]
    exact List.pairwise_ofFn.mpr (fun _ _ hij => monotone_ownerRow N A order row hrow hij.le)
  · intro e p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl

/-- A bounded number of standard vertices per source cell bounds every numbered row fiber. -/
theorem vertexRow_card_le [Fintype U] [Fintype C] [Fintype R] (B L : ℕ)
    (hrow : ∀ r, Fintype.card {v // row v = r} ≤ B)
    (hlocal : ∀ v, ((cell N A v).diagram.vertexList Prim.interp).length ≤ L) (r : ℕ) :
    Fintype.card {i // vertexRow N A order row i = r} ≤ B * L := by
  let f : {i // vertexRow N A order row i = r} → {v // row v = r} × Fin L := fun i =>
    let v := (vertexEquiv N A order).symm i.val
    (⟨v.1, i.property⟩, ⟨((Diagram.vertexEquiv Prim.interp (cell N A v.1).diagram) v.2).val,
      lt_of_lt_of_le ((Diagram.vertexEquiv Prim.interp (cell N A v.1).diagram) v.2).isLt
        (hlocal v.1)⟩)
  have hf : Function.Injective f := fun i j hij => by
    have hv : ((vertexEquiv N A order).symm i.val).1 =
        ((vertexEquiv N A order).symm j.val).1 := congrArg (fun x => x.1.val) hij
    have hn := congrArg (fun x => x.2.val) hij
    dsimp only [f] at hn
    refine Subtype.ext ((vertexEquiv N A order).symm.injective ?_)
    rcases hu : (vertexEquiv N A order).symm i.val with ⟨u, w⟩
    rcases hv' : (vertexEquiv N A order).symm j.val with ⟨v, z⟩
    rw [hu, hv'] at hv hn
    change u = v at hv
    subst v
    exact congrArg (Sigma.mk u)
      ((Diagram.vertexEquiv Prim.interp (cell N A u).diagram).injective (Fin.ext hn))
  exact (Fintype.card_le_of_injective f hf).trans (by
    rw [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right L (hrow r))

/-- A bounded owner slot count per source cell bounds every numbered wire row fiber. -/
theorem ownerRow_card_le [Fintype U] [Fintype C] [Fintype R] (B stride : ℕ)
    (hrow : ∀ r, Fintype.card {v // row v = r} ≤ B)
    (hlocal : ∀ v, (cell N A v).top.length + (cell N A v).diagram.innerCount + 2 ≤ stride)
    (r : ℕ) : Fintype.card {e // ownerRow N A order row e = r} ≤ B * stride := by
  let f : {e // ownerRow N A order row e = r} → {v // row v = r} × Fin stride := fun e =>
    let w := (edgeEquiv N A order).symm e.val
    (⟨edgeOwner N A w, e.property⟩,
      ⟨Sparse.slot N A w, Sparse.slot_lt N A stride hlocal w⟩)
  have hf : Function.Injective f := fun e e' hef => by
    refine Subtype.ext ((edgeEquiv N A order).symm.injective
      (Sparse.code_injective N A order stride hlocal ?_))
    have ho := congrArg (fun x => x.1.val) hef
    have hs := congrArg (fun x => x.2.val) hef
    dsimp only [f] at ho hs
    simp only [Sparse.code, ho, hs]
  exact (Fintype.card_le_of_injective f hf).trans (by
    rw [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right stride (hrow r))

private theorem filter_pairLabels_length {E : Type*} (es : List E) (p : E → Bool) :
    ((Planar.Embedding.Sinks.pairLabels es).filter (fun x => p x.edge)).length =
      2 * (es.filter p).length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change ((Port.mk e false :: Port.mk e true :: Planar.Embedding.Sinks.pairLabels es).filter
      (fun x => p x.edge)).length = 2 * ((e :: es).filter p).length
    cases hp : p e <;> simp [hp, ih, Nat.mul_add]

/-- Every edge owner contributes exactly two original incidence labels in that owner's row. -/
theorem vertexLabels_filter_length (r : ℕ) :
    ((Planar.Embedding.Sources.vertexLabels (List.ofFn (graph N A order))).filter
      (fun p => ownerRow N A order row p.edge == r)).length =
      2 * Fintype.card {e // ownerRow N A order row e = r} := by
  have hp := (Planar.Embedding.incidencePerm (List.ofFn (graph N A order))
    (by
      simpa only [List.get_ofFn, Function.comp_def, finCongr_apply] using
        (wellFormed N A order).reindex (finCongr (List.length_ofFn (f := graph N A order))))).filter
        (fun p => ownerRow N A order row p.edge == r)
  rw [hp.length_eq, filter_pairLabels_length (List.finRange (edgeList N A order).length)
    (fun e => ownerRow N A order row e == r)]
  congr 1
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
  simp [List.toFinset_filter, Fintype.card_subtype]

end Cslib.Complexity.NCL.SelectorNetwork.AndOr.Numbering
