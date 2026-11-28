/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Simulation
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Bandwidth
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.DeriveFintype

/-!
# Finite weighted word-selector networks

Each position has one row vertex, one vertex per character, and one relation vertex per ordered
symbol pair. Relations at consecutive positions enforce the forbidden pairs. The last position
uses inactive relations, so the same finite index sets and row blocks work at every length.

## Main definitions

* `HWord.RelationSite`: a position and an ordered symbol pair.
* `HWord.PortGraph.network`: the explicit weighted selector network for a fixed digraph.

## Main results

* `HWord.PortGraph.wellFormed`: every edge has two consistently weighted, opposite ports.
* `HWord.PortGraph.loopFree`: every edge joins two distinct vertices.
* `HWord.PortGraph.bandwidthCertificate`: an explicit order with span independent of word length.

## References

* The row-local construction follows [VanDerZanden2015, Theorem 6].
-/

public section

namespace Cslib.Complexity.NCL.HWord

/-- A possible forbidden pair at one position and its successor. -/
@[ext] structure RelationSite (q n : ℕ) where
  /-- The position of the first symbol. -/
  position : Fin n
  /-- The selected symbol at this position. -/
  first : Fin q
  /-- The selected symbol at the next position. -/
  second : Fin q
  deriving DecidableEq, Fintype

namespace PortGraph

variable {q n : ℕ}

private def sites (q n : ℕ) : List (RelationSite q n) :=
  ((List.finRange n).product ((List.finRange q).product (List.finRange q))).map
    fun ⟨i, a, b⟩ => ⟨i, a, b⟩

private theorem sites_nodup : (sites q n).Nodup := by
  apply List.Nodup.map _ ((List.nodup_finRange n).product
    ((List.nodup_finRange q).product (List.nodup_finRange q)))
  rintro ⟨i, a, b⟩ ⟨j, c, d⟩ h
  cases h
  rfl

private theorem sites_complete (c : RelationSite q n) : c ∈ sites q n := by
  exact List.mem_map.mpr ⟨(c.position, c.first, c.second), by simp, rfl⟩

private def next (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else i

/-- The enumerated character and relation network of the fixed directed compatibility graph. -/
def network (H : Digraph (Fin q)) [DecidableRel H.Adj] (n : ℕ) :
    SelectorNetwork (Fin n) (Fin n × Fin q) (RelationSite q n) where
  row := Prod.fst
  endpoint c b := if b then (next c.position, c.second) else (c.position, c.first)
  required c := decide (c.position.val + 1 < n ∧ ¬H.Adj c.first c.second)
  characters := (List.finRange n).product (List.finRange q)
  characters_nodup := (List.nodup_finRange n).product (List.nodup_finRange q)
  characters_complete c := List.mem_product.mpr
    ⟨List.mem_finRange c.1, List.mem_finRange c.2⟩
  relations := sites q n
  relations_nodup := sites_nodup
  relations_complete := sites_complete

/-- The row of a word character is its position. -/
theorem network_row (H : Digraph (Fin q)) [DecidableRel H.Adj] (c : Fin n × Fin q) :
    (network H n).row c = c.1 := by rfl

/-- The actual character list is ordered by position then symbol. -/
theorem network_characters (H : Digraph (Fin q)) [DecidableRel H.Adj] :
    (network H n).characters = (List.finRange n).product (List.finRange q) := by rfl

/-- The actual relation list is ordered by position and its two symbols. -/
theorem network_relations (H : Digraph (Fin q)) [DecidableRel H.Adj] :
    (network H n).relations =
      ((List.finRange n).product ((List.finRange q).product (List.finRange q))).map
        (fun ⟨i, a, b⟩ => (⟨i, a, b⟩ : RelationSite q n)) := by rfl

/-- Natural row of a branch's character endpoint, including the final-row fallback. -/
theorem network_endpoint_row (H : Digraph (Fin q)) [DecidableRel H.Adj]
    (r : RelationSite q n) (b : Bool) :
    ((network H n).endpoint r b).1.val =
      if b && decide (r.position.val + 1 < n) then r.position.val + 1 else r.position.val := by
  cases b with
  | false => rfl
  | true =>
    simp only [network, ite_true, Bool.true_and, decide_eq_true_eq]
    unfold next
    split_ifs <;> rfl

/-- Symbol read at the character endpoint of a relation branch. -/
theorem network_endpoint_symbol (H : Digraph (Fin q)) [DecidableRel H.Adj]
    (r : RelationSite q n) (b : Bool) :
    ((network H n).endpoint r b).2 = if b then r.second else r.first := by cases b <;> rfl

/-- Exactly the forbidden consecutive symbol pairs require an exclusion relation. -/
theorem network_required (H : Digraph (Fin q)) [DecidableRel H.Adj] (r : RelationSite q n) :
    (network H n).required r = decide (r.position.val + 1 < n ∧ ¬H.Adj r.first r.second) := by rfl

/-- The second endpoint of an active relation is at the following word position. -/
theorem network_endpoint_true (H : Digraph (Fin q)) [DecidableRel H.Adj]
    (r : RelationSite q n) (hr : r.position.val + 1 < n) :
    (network H n).endpoint r true = (⟨r.position.val + 1, hr⟩, r.second) := by
  simp only [network, ite_true, next, hr, dite_true]

/-- The first endpoint of a relation selects its first symbol at its own position. -/
theorem network_endpoint_false (H : Digraph (Fin q)) [DecidableRel H.Adj]
    (r : RelationSite q n) :
    (network H n).endpoint r false = (r.position, r.first) := by rfl

variable (H : Digraph (Fin q)) [DecidableRel H.Adj]

/-- The physical weighted graph has the exact two-port incidence discipline. -/
theorem wellFormed : (network H n).graph.WellFormed := (network H n).wellFormed

/-- Selectors join rows to characters, and unit edges join characters to relations. -/
theorem loopFree : (network H n).graph.LoopFree := by
  refine (network H n).endpoints.loopFree _ (network H n).edges_nodup ?_
  rintro (c | e) <;> simp [SelectorNetwork.endpoints]

/-- The source row of a row, character, or relation vertex. -/
@[expose] def vertexRow : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n) → Fin n
  | .inl i => i
  | .inr (.inl c) => c.1
  | .inr (.inr c) => c.position

/-- The source row and the row/character/relation tag of each source vertex. -/
@[expose] def rowTag : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n) ≃
    Fin n × (Fin 1 ⊕ Fin q ⊕ (Fin q × Fin q)) where
  toFun
    | .inl i => (i, .inl 0)
    | .inr (.inl c) => (c.1, .inr (.inl c.2))
    | .inr (.inr c) => (c.position, .inr (.inr (c.first, c.second)))
  invFun
    | (i, .inl _) => .inl i
    | (i, .inr (.inl a)) => .inr (.inl (i, a))
    | (i, .inr (.inr (a, b))) => .inr (.inr ⟨i, a, b⟩)
  left_inv v := by rcases v with i | (c | c) <;> rfl
  right_inv v := by
    rcases v with ⟨i, j | (a | ⟨a, b⟩)⟩
    · cases Fin.eq_zero j
      rfl
    · rfl
    · rfl

/-- The explicit edge list has `q` selectors and `2q²` unit edges per position. -/
theorem length_edges : ((network H n).edges).length = n * q + 2 * (n * (q * q)) := by
  have hlen {α β : Type} (xs : List α) (ys : List β) :
      (xs.product ys).length = xs.length * ys.length := List.length_product xs ys
  simp [SelectorNetwork.edges, SelectorNetwork.branches, network, sites, hlen,
    Nat.mul_comm]

/-- The fixed row, character, and relation tags in local creation order. -/
@[expose] def tagEquiv (q : ℕ) :
    (Fin 1 ⊕ Fin q ⊕ (Fin q × Fin q)) ≃ Fin (1 + (q + q * q)) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

/-- Row and fixed local tag of every source vertex. -/
@[expose] def rowEquiv :
    SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n) ≃
      Fin n × Fin (1 + (q + q * q)) :=
  rowTag.trans (Equiv.prodCongr (Equiv.refl _) (tagEquiv q))

private theorem next_dist (i : Fin n) : Nat.dist i.val (next i).val ≤ 1 := by
  unfold next
  split_ifs <;> simp [Nat.dist]

private theorem endpoint_rows (e : SelectorNetwork.Edge (Fin n × Fin q) (RelationSite q n))
    (b c : Bool) :
    Nat.dist (vertexRow ((network H n).endpoints.endpoint e b)).val
      (vertexRow ((network H n).endpoints.endpoint e c)).val ≤ 1 := by
  rcases e with ⟨i, a⟩ | r
  · cases b <;> cases c <;> simp [SelectorNetwork.endpoints, network, vertexRow, Nat.dist]
  · rcases r with ⟨r, d⟩
    cases b <;> cases c <;> cases d <;>
      simp only [SelectorNetwork.endpoints, network, vertexRow, Bool.coe_false,
        ite_false, ite_true, Nat.dist_self, Nat.zero_le]
    all_goals first
      | exact next_dist r.position
      | exact (Nat.dist_comm _ _).trans_le (next_dist r.position)

/-- Each row block has `1 + q + q²` vertices, and edges join only consecutive blocks. -/
def bandwidthCertificate : ConstraintGraph.BandwidthCertificate (network H n).graph
    (2 * (1 + (q + q * q)) - 1) :=
  ConstraintGraph.BandwidthCertificate.ofBlocks (network H n).graph rowEquiv (by
    intro u v p hp r hr he
    have hpu := ((network H n).endpoints.mem_ports _ u p.port p.weight).mp hp
    have hrv := ((network H n).endpoints.mem_ports _ v r.port r.weight).mp hr
    have hrow (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
        (rowEquiv v).1 = vertexRow v := by rcases v with i | (c | c) <;> rfl
    simp only [hrow]
    rw [← hpu.2.2, ← hrv.2.2, ← he]
    exact endpoint_rows H p.port.edge p.port.dir r.port.dir)

/-- The row coordinate of the explicit block equivalence is the source row. -/
private theorem rowEquiv_fst (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    (rowEquiv v).1 = vertexRow v := by rcases v with i | (c | c) <;> rfl

/-- The actual source order is the row-major flattening of its fixed local tags. -/
theorem order_val (v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    ((bandwidthCertificate H).order v).val =
      (rowEquiv v).2.val + (1 + (q + q * q)) * (vertexRow v).val := by
  rw [bandwidthCertificate]
  change (rowEquiv v).2.val + (1 + (q + q * q)) * (rowEquiv v).1.val = _
  rw [rowEquiv_fst]

/-- The actual source enumeration scans rows and then the fixed local tags. -/
theorem sourceList_eq : List.ofFn (bandwidthCertificate (n := n) H).order.symm =
    (List.finRange n).flatMap fun i =>
      (List.ofFn (tagEquiv q).symm).map (fun tag => rowTag.symm (i, tag)) := by
  change List.ofFn (rowEquiv.trans finProdFinEquiv).symm = _
  rw [List.ofFn_mul]
  have hi (i : Fin n) (j : Fin (1 + (q + q * q)))
      (h : i.val * (1 + (q + q * q)) + j.val < n * (1 + (q + q * q))) :
      (⟨i.val * (1 + (q + q * q)) + j.val, h⟩ : Fin (n * (1 + (q + q * q)))) =
        finProdFinEquiv (i, j) := Fin.ext <| by
    change i.val * (1 + (q + q * q)) + j.val = j.val + (1 + (q + q * q)) * i.val
    ac_rfl
  simp only [Equiv.symm_trans_apply, hi, Equiv.symm_apply_apply]
  simp only [List.ofFn_eq_map, List.flatten_eq_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def]
  rfl

/-- Source rows increase in the actual source-vertex enumeration. -/
theorem monotone_order_row : Monotone (fun i =>
    (vertexRow ((bandwidthCertificate (n := n) H).order.symm i)).val) := by
  intro i j hij
  let u := (bandwidthCertificate (n := n) H).order.symm i
  let v := (bandwidthCertificate (n := n) H).order.symm j
  have hi : ((bandwidthCertificate H).order u).val = i.val :=
    congrArg Fin.val ((bandwidthCertificate H).order.apply_symm_apply i)
  have hj : ((bandwidthCertificate H).order v).val = j.val :=
    congrArg Fin.val ((bandwidthCertificate H).order.apply_symm_apply j)
  rw [order_val] at hi hj
  have hu := (rowEquiv u).2.isLt
  by_contra h
  change ¬(vertexRow u).val ≤ (vertexRow v).val at h
  have hmul := Nat.mul_le_mul_left (1 + (q + q * q))
    (show (vertexRow v).val + 1 ≤ (vertexRow u).val from by omega)
  change i.val ≤ j.val at hij
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  omega

/-- A source row contains at most one row cell, `q` character cells, and `q²` relation cells. -/
theorem card_row_le (r : ℕ) : Fintype.card
    {v : SelectorNetwork.Vert (Fin n) (Fin n × Fin q) (RelationSite q n) //
      (vertexRow v).val = r} ≤ 1 + (q + q * q) := by
  apply (Fintype.card_le_of_injective (fun v => (rowEquiv v.val).2) ?_).trans_eq
    (Fintype.card_fin _)
  intro u v h
  refine Subtype.ext (rowEquiv.injective (Prod.ext (Fin.ext ?_) h))
  simpa only [rowEquiv_fst] using u.property.trans v.property.symm

/-- Every port row is its owning edge row or the following row. -/
theorem endpoint_row_bounds
    (e : SelectorNetwork.Edge (Fin n × Fin q) (RelationSite q n)) (b : Bool) :
    (vertexRow ((network H n).endpoints.endpoint e false)).val ≤
        (vertexRow ((network H n).endpoints.endpoint e b)).val ∧
      (vertexRow ((network H n).endpoints.endpoint e b)).val ≤
        (vertexRow ((network H n).endpoints.endpoint e false)).val + 1 := by
  rcases e with ⟨i, a⟩ | ⟨r, d⟩
  · cases b <;> simp [SelectorNetwork.endpoints, network, vertexRow]
  · cases b <;> cases d <;>
      simp only [SelectorNetwork.endpoints, network, vertexRow, Bool.coe_false,
        ite_false, ite_true, le_refl, true_and]
    all_goals first | omega | (unfold next; split_ifs <;> simp)

private def branchCode (c : Fin n × Fin q) (e : RelationSite q n × Bool) : Fin 3 × Fin q :=
  if e.2 then (if e.1.position = c.1 then 1 else 2, e.1.first) else (0, e.1.second)

private theorem next_fiber {i j k : Fin n} (hi : next i = k) (hj : next j = k)
    (htag : (if i = k then (1 : Fin 3) else 2).val =
      (if j = k then (1 : Fin 3) else 2).val) : i = j := by
  have step {x : Fin n} (hx : next x = k) (hxk : x ≠ k) : x.val + 1 = k.val := by
    unfold next at hx
    split_ifs at hx
    · exact congrArg Fin.val hx
    · exact (hxk hx).elim
  by_cases hik : i = k <;> by_cases hjk : j = k
  · exact hik.trans hjk.symm
  · simp [hik, hjk] at htag
  · simp [hik, hjk] at htag
  · exact Fin.ext (Nat.succ.inj ((step hi hik).trans (step hj hjk).symm))

private theorem branchCode_injective (c : Fin n × Fin q)
    {e f : RelationSite q n × Bool}
    (he : (network H n).endpoint e.1 e.2 = c)
    (hf : (network H n).endpoint f.1 f.2 = c)
    (hcode : branchCode c e = branchCode c f) : e = f := by
  rcases e with ⟨e, eb⟩
  rcases f with ⟨f, fb⟩
  have htag := congrArg (fun x => x.1.val) hcode
  have hsymbol := congrArg Prod.snd hcode
  cases eb <;> cases fb
  · simp only [network, Bool.coe_false, ite_false] at he hf
    exact Prod.ext (RelationSite.ext
      ((congrArg Prod.fst he).trans (congrArg Prod.fst hf).symm)
      ((congrArg Prod.snd he).trans (congrArg Prod.snd hf).symm) hsymbol) rfl
  · simp only [branchCode, Bool.coe_false, ite_false, ite_true] at htag
    split_ifs at htag <;> simp at htag
  · simp only [branchCode, Bool.coe_false, ite_false, ite_true] at htag
    split_ifs at htag <;> simp at htag
  · simp only [network, ite_true] at he hf
    exact Prod.ext (RelationSite.ext
      (next_fiber (congrArg Prod.fst he) (congrArg Prod.fst hf) htag) hsymbol
      ((congrArg Prod.snd he).trans (congrArg Prod.snd hf).symm)) rfl

/-- Every character meets at most three rows of `q` unit edges, including the last-row fallback. -/
theorem selectorWeight_le (c : Fin n × Fin q) : (network H n).selectorWeight c ≤ 3 * q + 1 := by
  let es := ((network H n).incident c).toFinset
  have hinj : Set.InjOn (branchCode c) es := fun e he f hf heq =>
    branchCode_injective H c
      (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp he)).2)
      (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hf)).2) heq
  refine Nat.add_le_add_right ?_ 1
  have hn : ((network H n).incident c).Nodup := (network H n).branches_nodup.filter _
  rw [← List.toFinset_card_of_nodup hn]
  change es.card ≤ 3 * q
  rw [← Finset.card_image_of_injOn hinj]
  exact (Finset.card_le_univ _).trans_eq (by simp)

end PortGraph
end Cslib.Complexity.NCL.HWord
