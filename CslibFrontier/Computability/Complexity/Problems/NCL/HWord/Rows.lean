/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Planarized
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Numbering.Rows

/-!
# Actual row budgets for the word-network drawing

The explicit source order, owner order, and port rows satisfy the canonical planarizer's
monotonicity and neighboring-row premises. Their fiber budgets depend only on the alphabet.

## Main definitions

* `HWord.Planarized.sourceRow`: source rows of the actual numbered vertex list.
* `HWord.Planarized.ownerRow`: owner rows of its actual numbered wires.
* `HWord.Planarized.portRow`: source rows of its original incidence labels.

## Main results

* `HWord.Planarized.vertexLabels_pairwise`: source row order for the actual drawing.
* `HWord.Planarized.pairLabels_pairwise`: owner row order for the actual drawing.
* `HWord.Planarized.incidenceRow_length_le`: constant original-label budget per owner row.
-/

public section

namespace Cslib.Complexity.NCL.HWord.Planarized

open SelectorNetwork.AndOr

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Source rows in the exact numbered standard-vertex order. -/
@[expose] def sourceRow (i : Fin (vertexCount (n := n) H hq)) : ℕ :=
  Numbering.vertexRow (PortGraph.network H n) (AndOr.rowSection H hq)
    (PortGraph.bandwidthCertificate H).order (Fin.val ∘ PortGraph.vertexRow) i

/-- Source rows indexed by the actual finite vertex list supplied to the planarizer. -/
@[expose] def vertexRow (i : Fin (vertices (n := n) H hq).length) : ℕ :=
  sourceRow H hq (i.cast (List.length_ofFn (f := finiteGraph H hq)))

/-- Owner rows in the exact shared/private wire order. -/
@[expose] def ownerRow (e : Fin (width (n := n) H hq)) : ℕ :=
  Numbering.ownerRow (PortGraph.network H n) (AndOr.rowSection H hq)
    (PortGraph.bandwidthCertificate H).order (Fin.val ∘ PortGraph.vertexRow) e

/-- Source row of an original incidence label. -/
@[expose] def portRow (p : Port (Fin (width (n := n) H hq))) : ℕ :=
  Numbering.portRow (PortGraph.network H n) (AndOr.rowSection H hq)
    (PortGraph.bandwidthCertificate H).order (Fin.val ∘ PortGraph.vertexRow) p

/-- The exact source labels supplied to canonical routing are ordered by source row. -/
theorem vertexLabels_pairwise :
    (Planar.Embedding.Sources.vertexLabels (vertices (n := n) H hq)).Pairwise
    (fun a b => portRow H hq a ≤ portRow H hq b) :=
  Numbering.vertexLabels_pairwise _ _ _ _ (PortGraph.monotone_order_row H)

/-- The exact paired edge labels supplied to canonical routing are ordered by owner row. -/
theorem pairLabels_pairwise :
    (Planar.Embedding.Sinks.pairLabels (List.finRange (width (n := n) H hq))).Pairwise
      (fun a b => ownerRow H hq a.edge ≤ ownerRow H hq b.edge) :=
  Numbering.pairLabels_pairwise _ _ _ _ (PortGraph.monotone_order_row H)

/-- Original ports are in their owner's row or its next row. -/
theorem portRow_bounds (p : Port (Fin (width (n := n) H hq))) :
    ownerRow H hq p.edge ≤ portRow H hq p ∧ portRow H hq p ≤ ownerRow H hq p.edge + 1 :=
  Numbering.portRow_bounds _ _ _ _ (PortGraph.endpoint_row_bounds H) p

private theorem local_vertices_le
    (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    ((cell (PortGraph.network H n) (AndOr.rowSection H hq) v).diagram.vertexList
      Prim.interp).length ≤
      64 + 66 * q := by
  have h := ((cell (PortGraph.network H n) (AndOr.rowSection H hq) v).size_le).1
  have ha := AndOr.input_arity_le H hq v
  omega

/-- Every source row has a constant number of actual standard vertices. -/
private theorem sourceRow_card_le (r : ℕ) : Fintype.card {i // sourceRow (n := n) H hq i = r} ≤
    (1 + (q + q * q)) * (64 + 66 * q) :=
  Numbering.vertexRow_card_le _ _ _ _ _ _ (PortGraph.card_row_le)
    (local_vertices_le H hq) r

/-- Every owner row has a constant number of actual shared and private wires. -/
theorem ownerRow_card_le (r : ℕ) : Fintype.card {e // ownerRow (n := n) H hq e = r} ≤
    (1 + (q + q * q)) * (66 + 69 * q) :=
  Numbering.ownerRow_card_le _ _ _ _ _ _ (PortGraph.card_row_le) (AndOr.slot_budget_le H hq) r

/-- The actual list-indexed source rows have the same uniform vertex budget. -/
theorem vertexRow_card_le (r : ℕ) : Fintype.card {i // vertexRow (n := n) H hq i = r} ≤
    (1 + (q + q * q)) * (64 + 66 * q) := by
  let f : {i // vertexRow (n := n) H hq i = r} → {i // sourceRow (n := n) H hq i = r} :=
    fun i => ⟨i.val.cast (List.length_ofFn (f := finiteGraph H hq)), i.property⟩
  exact (Fintype.card_le_of_injective f (fun _ _ h => Subtype.ext (Fin.ext
    (congrArg (fun i => i.val.val) h)))).trans (sourceRow_card_le H hq r)

/-- A port's incidence row is the row assigned to its actual source-list vertex. -/
theorem portRow_of_mem (i : Fin (vertices (n := n) H hq).length)
    (p : WeightedPort (Fin (width (n := n) H hq))) (hp : p ∈ ((vertices H hq).get i).ports) :
    portRow H hq p.port = vertexRow H hq i := by
  rw [show (vertices H hq).get i = finiteGraph H hq
    (i.cast (List.length_ofFn (f := finiteGraph H hq))) from List.get_ofFn _ i] at hp
  exact Numbering.portRow_of_mem _ _ _ _ _ p hp

/-- The actual source ports meet owner rows at distance at most one. -/
theorem vertexRow_port_bounds (i : Fin (vertices (n := n) H hq).length)
    (p : WeightedPort (Fin (width (n := n) H hq))) (hp : p ∈ ((vertices H hq).get i).ports) :
    vertexRow H hq i ≤ ownerRow H hq p.port.edge + 1 ∧
      ownerRow H hq p.port.edge ≤ vertexRow H hq i + 1 := by
  have h := portRow_bounds H hq p.port
  rw [portRow_of_mem H hq i p hp] at h
  omega

/-- Every owner row contains at most twice its wire budget in actual original incidence labels. -/
theorem incidenceRow_length_le (r : ℕ) :
    ((Planar.Embedding.Sources.vertexLabels (vertices (n := n) H hq)).filter
      (fun p => ownerRow H hq p.edge == r)).length ≤
      2 * ((1 + (q + q * q)) * (66 + 69 * q)) := by
  calc
    _ = 2 * Fintype.card {e // ownerRow (n := n) H hq e = r} :=
      Numbering.vertexLabels_filter_length _ _ _ _ r
    _ ≤ _ := Nat.mul_le_mul_left 2 (ownerRow_card_le H hq r)

end Cslib.Complexity.NCL.HWord.Planarized
