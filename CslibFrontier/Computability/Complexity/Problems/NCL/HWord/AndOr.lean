/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.ConstraintGraph
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.AndOr

/-!
# Standard AND/OR networks for word reconfiguration

Each position uses the zero symbol as its final row port. The complete network implements
canonical word configurations exactly, with input arity bounded by the fixed alphabet.

## Main definitions

* `HWord.AndOr.graph`: the standard network of a fixed compatibility graph.
* `HWord.AndOr.orientation`: the physical encoding of a word.

## Main results

* `HWord.AndOr.reachable_orientation_iff`: exact word reconfiguration.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner
  Cslib.Complexity.NCL.Diagram.instDecidableEqInner

namespace Cslib.Complexity.NCL.HWord.AndOr

open SelectorNetwork

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Symbol zero is the final port of every row OR tree. -/
@[expose] def rowSection : RowSection (PortGraph.network H n) where
  character i := (i, ⟨0, hq⟩)
  row_character i := PortGraph.network_row H (i, ⟨0, hq⟩)

/-- The standard vertices of the word network. -/
abbrev TargetVertex := SelectorNetwork.AndOr.TargetVertex (PortGraph.network H n) (rowSection H hq)

/-- Shared selector/relation edges and fresh private implementation wires. -/
abbrev TargetEdge := Edge (Fin n × Fin q) (RelationSite q n) ⊕
  SelectorNetwork.AndOr.Private (PortGraph.network H n) (rowSection H hq)

/-- The actual finite standard AND/OR network implementing the word constraints. -/
@[expose] def graph : ConstraintGraph (TargetVertex (n := n) H hq) (TargetEdge (n := n) H hq) :=
  SelectorNetwork.AndOr.graph (PortGraph.network H n) (rowSection H hq)

/-- Canonical physical configurations of a word. -/
@[expose] def orientation (w : Fin n → Fin q) : TargetEdge (n := n) H hq → Bool :=
  (SelectorNetwork.AndOr.simulation (PortGraph.network H n) (rowSection H hq)).enc
    ((PortGraph.network H n).encode (oneHot w))

/-- The encoded physical state is legal exactly when the word is compatible. -/
theorem legal_orientation_iff (w : Fin n → Fin q) :
    (graph H hq).Legal (orientation H hq w) ↔ Legal H w :=
  (SelectorNetwork.AndOr.simulation (PortGraph.network H n) (rowSection H hq)).legal_enc_iff.trans
    (PortGraph.legal_oneHot_iff H w)

/-- Canonical physical states preserve and reflect all word-reconfiguration paths. -/
theorem reachable_orientation_iff (s t : Fin n → Fin q) :
    (graph H hq).Reachable (orientation H hq s) (orientation H hq t) ↔ Reachable H s t :=
  ((SelectorNetwork.AndOr.simulation (PortGraph.network H n)
    (rowSection H hq)).reachable_enc_iff).trans (PortGraph.reachable_oneHot_iff H s t)

/-- Every word-network vertex is standard AND or OR. -/
theorem isAndOr : (graph (n := n) H hq).IsAndOr :=
  SelectorNetwork.AndOr.isAndOr _ _

/-- Word-network implementations have no self-loops. -/
theorem loopFree : (graph (n := n) H hq).LoopFree :=
  SelectorNetwork.AndOr.loopFree _ _

/-- Every implementation edge has exactly two opposite ports with the same weight. -/
theorem wellFormed : (graph (n := n) H hq).WellFormed :=
  SelectorNetwork.AndOr.wellFormed _ _

private theorem rowInputs_length_le (i : Fin n) :
    (SelectorNetwork.AndOr.rowInputs (PortGraph.network H n) (rowSection H hq) i).length ≤ q := by
  let xs := SelectorNetwork.AndOr.rowInputs (PortGraph.network H n) (rowSection H hq) i
  have hinj : Set.InjOn Prod.snd (↑xs.toFinset : Set (Fin n × Fin q)) := fun c hc d hd hcd => by
    have hc' := (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hc)).2).1
    have hd' := (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hd)).2).1
    exact Prod.ext (((PortGraph.network_row H c).symm.trans hc').trans
      (hd'.symm.trans (PortGraph.network_row H d))) hcd
  have hn : xs.Nodup := (PortGraph.network H n).characters_nodup.filter _
  change xs.length ≤ q
  rw [← List.toFinset_card_of_nodup hn, ← Finset.card_image_of_injOn hinj]
  exact (Finset.card_le_univ _).trans_eq (by simp)

/-- Every local implementation has at most `3q` inputs. -/
theorem input_arity_le (v : Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    (SelectorNetwork.AndOr.cell (PortGraph.network H n)
      (rowSection H hq) v).top.length ≤ 3 * q := by
  rcases v with i | (c | _)
  · exact (Gadgets.OrTree.length_bundle _).le.trans ((rowInputs_length_le H hq i).trans (by omega))
  · have hc : ((PortGraph.network H n).incident c).length + 1 ≤ 3 * q + 1 :=
      PortGraph.selectorWeight_le H c
    exact (Gadgets.OrTree.length_bundle _).le.trans (by omega)
  · exact Nat.zero_le _

/-- Shared slots zero and one plus every private creation slot fit in one fixed local interval. -/
theorem slot_budget_le (v : Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    (SelectorNetwork.AndOr.cell (PortGraph.network H n) (rowSection H hq) v).top.length +
      (SelectorNetwork.AndOr.cell (PortGraph.network H n) (rowSection H hq) v).diagram.innerCount +
        2 ≤ 66 + 69 * q := by
  have h := ((SelectorNetwork.AndOr.cell (PortGraph.network H n) (rowSection H hq) v).size_le).2
  have ha := input_arity_le H hq v
  omega

end Cslib.Complexity.NCL.HWord.AndOr
