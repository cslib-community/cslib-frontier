/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Metadata.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Metadata.State
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Planarized
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Program.Correctness
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Boundary

/-!
# Natural-coordinate metadata agrees with the certified word network

Position and symbol scans preserve the actual source, branch, boundary, and owner orders.
Their portable blocks therefore emit the same numbered standard graph.

## Main results

* `HWord.Metadata.graph_blocks_eq`: exact agreement with the certified finite network.
-/

public section

namespace Cslib.Complexity.NCL.HWord.Metadata

open SelectorNetwork.AndOr

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

private def lowerBranch (e : RelationSite q n × Bool) : Branch q :=
  ⟨e.1.position.val, e.1.first, e.1.second, e.2⟩

private theorem branches_eq : branches q n = (PortGraph.network H n).branches.map lowerBranch := by
  rw [branches, ← List.map_coe_finRange_eq_range]
  simp only [SelectorNetwork.branches, PortGraph.network_relations, List.product,
    List.map_flatMap, List.flatMap_map, List.flatMap_assoc, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, lowerBranch]

private theorem incident_eq (c : Fin n × Fin q) :
    incident n c.1.val c.2 = ((PortGraph.network H n).incident c).map lowerBranch := by
  rw [incident, SelectorNetwork.incident, branches_eq H, List.filter_map]
  refine congrArg (List.map lowerBranch) (List.filter_congr fun e _ => ?_)
  have hr : endpointRow n (lowerBranch e) = ((PortGraph.network H n).endpoint e.1 e.2).1.val :=
    (PortGraph.network_endpoint_row H e.1 e.2).symm
  have hs : endpointSymbol (lowerBranch e) = ((PortGraph.network H n).endpoint e.1 e.2).2 :=
    (PortGraph.network_endpoint_symbol H e.1 e.2).symm
  simp only [Function.comp_def, hr, hs, Prod.ext_iff, Fin.ext_iff]

private theorem filter_product_left {α β : Type*} [DecidableEq α] (xs : List α)
    (ys : List β) (i : α) (p : β → Bool) :
    (xs.product ys).filter (fun x => decide (x.1 = i) && p x.2) =
      (xs.filter fun a => decide (a = i)).product (ys.filter p) := by
  unfold List.product
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases eq_or_ne a i with rfl | ha <;> simp [List.filter_map, Function.comp_def, *]

private theorem rowInputs_eq (i : Fin n) :
    rowInputs (PortGraph.network H n) (AndOr.rowSection H hq) i =
      ((List.finRange q).filter (fun a => decide (a.val ≠ 0))).map (Prod.mk i) := by
  unfold rowInputs
  rw [PortGraph.network_characters]
  simp only [PortGraph.network_row]
  change ((List.finRange n).product (List.finRange q)).filter
    (fun c => decide (c.1 = i ∧ c ≠ (i, ⟨0, hq⟩))) = _
  have hp : (fun c : Fin n × Fin q => decide (c.1 = i ∧ c ≠ (i, ⟨0, hq⟩))) =
      (fun c => decide (c.1 = i) && decide (c.2.val ≠ 0)) := funext fun c => by
    by_cases hi : c.1 = i <;> simp [hi, Prod.ext_iff, Fin.ext_iff]
  rw [hp, filter_product_left (List.finRange n) (List.finRange q) i (fun a => decide (a.val ≠ 0)),
    List.filter_eq, List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange i)]
  simp [List.product]

private theorem name_eq (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n))
    (slot : ℕ) : name (PortGraph.vertexRow v).val (PortGraph.rowTag v).2 slot =
      stride q * ((PortGraph.bandwidthCertificate H).order v).val + slot := by
  rw [PortGraph.order_val]
  rcases v with i | (c | r) <;> rfl

private theorem selector_eq (c : Fin n × Fin q) : selector c.1.val c.2 =
    Sparse.code (PortGraph.network H n) (AndOr.rowSection H hq)
      (PortGraph.bandwidthCertificate H).order (stride q) (.inl (.inl c)) :=
  name_eq H (.inr (.inl c)) 0

private theorem branchName_eq (e : RelationSite q n × Bool) : branchName (lowerBranch e) =
    Sparse.code (PortGraph.network H n) (AndOr.rowSection H hq)
      (PortGraph.bandwidthCertificate H).order (stride q) (.inl (.inr e)) := by
  rcases e with ⟨r, _ | _⟩
  · exact name_eq H (.inr (.inr r)) 0
  · exact name_eq H (.inr (.inr r)) 1

private theorem shape_eq (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    (shape H hq n (PortGraph.vertexRow v).val (PortGraph.rowTag v).2).val =
      cell (PortGraph.network H n) (AndOr.rowSection H hq) v := by
  rcases v with i | (c | r)
  · simp [shape, PortGraph.rowTag, cell, rowInputs_eq H hq]
  · have ha := AndOr.input_arity_le H hq (.inr (.inl c))
    change (Gadgets.OrTree.bundle ((PortGraph.network H n).incident c).length).length ≤ 3 * q at ha
    rw [Gadgets.OrTree.length_bundle] at ha
    simp only [shape, PortGraph.vertexRow, PortGraph.rowTag, Equiv.coe_fn_mk, cell,
      incident_eq H, List.length_map, Nat.min_eq_left ha]
  · simp only [shape, PortGraph.vertexRow, PortGraph.rowTag, Equiv.coe_fn_mk, cell,
      PortGraph.network_required]
    rfl

private theorem boundaryNames_eq
    (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    boundaryNames hq n (PortGraph.vertexRow v).val (PortGraph.rowTag v).2 =
      (Sparse.context (PortGraph.network H n) (AndOr.rowSection H hq)
        (PortGraph.bandwidthCertificate H).order (stride q) v).boundaryNames := by
  let f := fun e => Sparse.code (PortGraph.network H n) (AndOr.rowSection H hq)
    (PortGraph.bandwidthCertificate H).order (stride q) (.inl e)
  change _ = List.ofFn (fun i => f (port (PortGraph.network H n) (AndOr.rowSection H hq) v
    (finSumFinEquiv.symm i)))
  rw [ofFn_map_port]
  rcases v with i | (c | r)
  · simp only [PortGraph.vertexRow, PortGraph.rowTag, Equiv.coe_fn_mk, boundaryNames,
      boundaryList, rowInputs_eq H hq, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Function.comp_def, f, ← selector_eq H hq]
    rfl
  · simp only [PortGraph.vertexRow, PortGraph.rowTag, Equiv.coe_fn_mk, boundaryNames,
      boundaryList, incident_eq H, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Function.comp_def, f, branchName_eq H hq, selector_eq H hq]
  · change [branchName (lowerBranch (r, false)), branchName (lowerBranch (r, true))] =
      [f (.inr (r, false)), f (.inr (r, true))]
    rw [branchName_eq H hq, branchName_eq H hq]

private theorem ownedNames_eq
    (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    ownedNames (PortGraph.vertexRow v).val (PortGraph.rowTag v).2 =
      (Numbering.ownedShared v).map (fun e => Sparse.code (PortGraph.network H n)
        (AndOr.rowSection H hq) (PortGraph.bandwidthCertificate H).order (stride q) (.inl e)) := by
  rcases v with i | (c | r)
  · rfl
  · exact congrArg (fun e => [e]) (selector_eq H hq c)
  · change [branchName (lowerBranch (r, false)), branchName (lowerBranch (r, true))] = _
    rw [branchName_eq H hq, branchName_eq H hq]; rfl

private theorem block_eq
    (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    block H hq n (PortGraph.vertexRow v).val (PortGraph.rowTag v).2 =
      { shape := ⟨cell (PortGraph.network H n) (AndOr.rowSection H hq) v,
          AndOr.input_arity_le H hq v⟩
        context := Sparse.context (PortGraph.network H n) (AndOr.rowSection H hq)
          (PortGraph.bandwidthCertificate H).order (stride q) v
        ownedNames := (Numbering.ownedShared v).map (fun e => Sparse.code (PortGraph.network H n)
          (AndOr.rowSection H hq) (PortGraph.bandwidthCertificate H).order (stride q) (.inl e))
        row := (PortGraph.vertexRow v).val } := by
  unfold block Sparse.context
  rw [Program.Block.mk.injEq, TemplateContext.mk.injEq]
  refine ⟨Subtype.ext (shape_eq H hq v), ⟨boundaryNames_eq H hq v, name_eq H v 2, ?_, ?_⟩,
    ownedNames_eq H hq v, rfl⟩
  · rcases v with i | (c | r) <;> rfl
  · rcases v with i | (c | r)
    · exact selector_eq H hq (i, ⟨0, hq⟩)
    · rfl
    · rfl

private theorem scan_eq_source {α : Type*} (f : ℕ → Tag q → α)
    (g : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n) → α)
    (hf : ∀ v, f (PortGraph.vertexRow v).val (PortGraph.rowTag v).2 = g v) :
    (List.range n).flatMap (fun position => (tags q).map (f position)) =
      (List.ofFn (PortGraph.bandwidthCertificate H).order.symm).map g := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map, PortGraph.sourceList_eq,
    List.map_flatMap]
  refine List.flatMap_congr fun i _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun tag _ => ?_
  have hpos : PortGraph.vertexRow (PortGraph.rowTag.symm (i, tag)) = i := by
    rcases tag with _ | (_ | _) <;> rfl
  simpa only [hpos, congrArg Prod.snd (PortGraph.rowTag.apply_symm_apply (i, tag)),
    Function.comp_def] using hf (PortGraph.rowTag.symm (i, tag))

/-- The natural-coordinate scan is the actual certified source-cell block enumeration. -/
private theorem blocks_eq : blocks H hq n =
    Program.blocks (PortGraph.network H n) (AndOr.rowSection H hq)
      (PortGraph.bandwidthCertificate H).order (AndOr.input_arity_le H hq) (stride q)
      (Fin.val ∘ PortGraph.vertexRow) :=
  scan_eq_source H _ _ (block_eq H hq)

/-- Metadata emission gives exactly the certified finite word-network graph. -/
theorem graph_blocks_eq : Program.graph (blocks H hq n) =
    AndOrGraph.ofFinite (Planarized.finiteGraph (n := n) H hq) := by
  rw [blocks_eq]
  exact Program.graph_blocks _ _ _ _ _ _ (AndOr.slot_budget_le H hq)

private theorem selected_eq (word : List (Fin q)) (w : Fin n → Fin q)
    (hw : ∀ i, word.getD i.val ⟨0, hq⟩ = w i) (c : Fin n × Fin q) :
    selected hq word c.1.val c.2 = (PortGraph.network H n).encode (oneHot w) (.inl c) := by
  change decide (word.getD c.1.val ⟨0, hq⟩ = c.2) = decide (w c.1 = c.2)
  rw [hw c.1]

private theorem branchBit_eq (word : List (Fin q)) (w : Fin n → Fin q)
    (hw : ∀ i, word.getD i.val ⟨0, hq⟩ = w i) (e : RelationSite q n × Bool) :
    branchBit hq n word (lowerBranch e) =
      (PortGraph.network H n).encode (oneHot w) (.inr e) := by
  have hr : endpointRow n (lowerBranch e) = ((PortGraph.network H n).endpoint e.1 e.2).1.val :=
    (PortGraph.network_endpoint_row H e.1 e.2).symm
  have hs : endpointSymbol (lowerBranch e) = ((PortGraph.network H n).endpoint e.1 e.2).2 :=
    (PortGraph.network_endpoint_symbol H e.1 e.2).symm
  change decide (word.getD (endpointRow n (lowerBranch e)) ⟨0, hq⟩ =
      endpointSymbol (lowerBranch e)) =
    decide (w ((PortGraph.network H n).endpoint e.1 e.2).1 =
      ((PortGraph.network H n).endpoint e.1 e.2).2)
  rw [hr, hs, hw]

private theorem ownedBits_eq (word : List (Fin q)) (w : Fin n → Fin q)
    (hw : ∀ i, word.getD i.val ⟨0, hq⟩ = w i)
    (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    ownedBits hq n word (PortGraph.vertexRow v).val (PortGraph.rowTag v).2 =
      (Numbering.ownedShared v).map ((PortGraph.network H n).encode (oneHot w)) := by
  rcases v with i | (c | r)
  · rfl
  · exact congrArg (fun b => [b]) (selected_eq H hq word w hw c)
  · change [branchBit hq n word (lowerBranch (r, false)),
      branchBit hq n word (lowerBranch (r, true))] = _
    rw [branchBit_eq H hq word w hw, branchBit_eq H hq word w hw]; rfl

private theorem rowSelector_bit (word : List (Fin q)) (w : Fin n → Fin q)
    (hw : ∀ i, word.getD i.val ⟨0, hq⟩ = w i) (i : Fin n) (a : Fin q) :
    (polarity (PortGraph.network H n) (AndOr.rowSection H hq) (.inl i) +
      (PortGraph.network H n).encode (oneHot w)) (.inl (i, a)) =
      if a = ⟨0, hq⟩ then !(selected hq word i.val a) else selected hq word i.val a := by
  simp only [selected_eq H hq word w hw (i, a)]
  rcases eq_or_ne a ⟨0, hq⟩ with rfl | ha <;>
    simp [polarity, AndOr.rowSection, Pi.add_apply, Bool.add_eq_xor, *]

private theorem boundaryBits_eq (word : List (Fin q)) (w : Fin n → Fin q)
    (hw : ∀ i, word.getD i.val ⟨0, hq⟩ = w i)
    (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    boundaryBits hq n word (PortGraph.vertexRow v).val (PortGraph.rowTag v).2 =
      List.ofFn (fun i : Fin ((cell (PortGraph.network H n) (AndOr.rowSection H hq) v).top.length +
        (cell (PortGraph.network H n) (AndOr.rowSection H hq) v).bottom.length) =>
          (polarity (PortGraph.network H n) (AndOr.rowSection H hq) v +
            (PortGraph.network H n).encode (oneHot w))
              (port (PortGraph.network H n) (AndOr.rowSection H hq) v
                (finSumFinEquiv.symm i))) := by
  let s := (PortGraph.network H n).encode (oneHot w)
  let f := polarity (PortGraph.network H n) (AndOr.rowSection H hq) v + s
  change _ = List.ofFn (fun i => f (port (PortGraph.network H n) (AndOr.rowSection H hq) v
    (finSumFinEquiv.symm i)))
  rw [ofFn_map_port]
  rcases v with i | (c | r)
  · simp only [PortGraph.vertexRow, PortGraph.rowTag, Equiv.coe_fn_mk, boundaryBits,
      boundaryList, rowInputs_eq H hq, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Function.comp_def]
    apply congrArg₂ (fun a b : List Bool => a ++ b)
    · apply List.map_congr_left
      intro a ha
      have hne : a ≠ ⟨0, hq⟩ := fun he =>
        (of_decide_eq_true (List.mem_filter.mp ha).2) (congrArg Fin.val he)
      simp only [f, s, rowSelector_bit H hq word w hw, ite_eq_right hne]
    · change [!selected hq word i.val ⟨0, hq⟩] = [f (.inl (i, ⟨0, hq⟩))]
      simp only [f, s, rowSelector_bit H hq word w hw, ite_true]
  · simp only [PortGraph.vertexRow, PortGraph.rowTag, Equiv.coe_fn_mk, boundaryBits,
      boundaryList, incident_eq H, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Function.comp_def]
    simp only [branchBit_eq H hq word w hw, selected_eq H hq word w hw,
      f, polarity, Pi.add_apply, Bool.add_eq_xor, Bool.false_xor, s]
  · change [branchBit hq n word (lowerBranch (r, false)),
      branchBit hq n word (lowerBranch (r, true))] = _
    rw [branchBit_eq H hq word w hw, branchBit_eq H hq word w hw]
    simp [boundaryList, f, polarity, Pi.add_apply, Bool.add_eq_xor, s]

private theorem stateBlock_eq (word : List (Fin q)) (w : Fin n → Fin q)
    (hw : ∀ i, word.getD i.val ⟨0, hq⟩ = w i)
    (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    stateBlock H hq n word (PortGraph.vertexRow v).val (PortGraph.rowTag v).2 =
      { shape := ⟨cell (PortGraph.network H n) (AndOr.rowSection H hq) v,
          AndOr.input_arity_le H hq v⟩
        boundary := List.ofFn (fun i : Fin
          ((cell (PortGraph.network H n) (AndOr.rowSection H hq) v).top.length +
            (cell (PortGraph.network H n) (AndOr.rowSection H hq) v).bottom.length) =>
          (polarity (PortGraph.network H n) (AndOr.rowSection H hq) v +
            (PortGraph.network H n).encode (oneHot w))
              (port (PortGraph.network H n) (AndOr.rowSection H hq) v (finSumFinEquiv.symm i)))
        owned := (Numbering.ownedShared v).map ((PortGraph.network H n).encode (oneHot w)) } := by
  unfold stateBlock
  rw [Program.StateBlock.mk.injEq]
  exact ⟨Subtype.ext (shape_eq H hq v), boundaryBits_eq H hq word w hw v,
    ownedBits_eq H hq word w hw v⟩

/-- Natural-coordinate direction scans enumerate the actual canonical simulation blocks. -/
private theorem stateBlocks_eq (word : List (Fin q)) (w : Fin n → Fin q)
    (hw : ∀ i, word.getD i.val ⟨0, hq⟩ = w i) : stateBlocks H hq n word =
    Program.stateBlocks (PortGraph.network H n) (AndOr.rowSection H hq)
      (PortGraph.bandwidthCertificate H).order (AndOr.input_arity_le H hq)
      ((PortGraph.network H n).encode (oneHot w)) :=
  scan_eq_source H _ _ (stateBlock_eq H hq word w hw)

/-- Metadata directions are exactly the same numbered network's canonical orientation. -/
theorem bits_stateBlocks_eq (word : List (Fin q)) (w : Fin n → Fin q)
    (hw : ∀ i, word.getD i.val ⟨0, hq⟩ = w i) :
    Program.bits (stateBlocks H hq n word) = List.ofFn
      ((Numbering.simulation (PortGraph.network H n) (AndOr.rowSection H hq)
        (PortGraph.bandwidthCertificate H).order).enc (AndOr.orientation H hq w)) := by
  rw [stateBlocks_eq H hq word w hw]
  exact Program.bits_stateBlocks _ _ _ _ _

end Cslib.Complexity.NCL.HWord.Metadata
