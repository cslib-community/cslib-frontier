/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Equivalent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Networks of tensors

A tensor that is the value of a network is a restriction of the product of the wires on the
edges of the network and of the tensors at its vertices, wherever the vertices are placed
(`PartyTensor.push_le_of_network`, and `PartyTensor.push_le_of_edges` without tensors at the
vertices). The statements are about functions, not graphs: the edge `e` has the ends `a e` and
`b e` and labels in `Λ e`, the vertex `v` is placed at the party `ξ v` and has a table `T v`, a
function of all labels that is *local*: it depends only on the labels of the edges at `v`, on the
legs of the tensors at `v` and on the indices held by the party of `v`. This is the contraction of
a tensor network (`Cslib.Circuits.Frontier.TensorNetwork.contraction`) with open legs at the
parties, and with an index set of its own on each edge.

Special cases are that the wire `⟨q⟩_uw` is a restriction of `⟨q⟩_uv ⟨q⟩_vw`
(`PartyTensor.wire_le_mul_wire`, from the proof of Lemma A.2 of [AnthropicVPVNP2026]), the same
for trees, and moving legs along wires (`PartyTensor.push_le_mul_push`).

## Main definitions

* `Cslib.PartyTensor.outer`, `Cslib.PartyTensor.outerPair`: products of tensors with separate
  legs.

## Main results

* `Cslib.PartyTensor.push_le_of_network`, `Cslib.PartyTensor.push_le_of_edges`: networks.
* `Cslib.PartyTensor.antisymmRel_push_outer`, `Cslib.PartyTensor.antisymmRel_push_outerPair`:
  pushing products with separate legs.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Ov.Core.Network`
-/

public section

namespace Cslib.PartyTensor

open Finset

variable {K : Type} [CommSemiring K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
  [DecidableEq J]
variable {V : Type} [Fintype V]

/-- Contraction with one tensor. The legs of `t` are at vertices (the leg `l` at `ρ l`), every
vertex `v` is placed at the party `ξ v` and has a local table `T v`: it depends only on the legs of
`s` that are held by the party `ξ v` and on the legs of `t` at `v`. If `s` is the sum over all
labels of the legs of `t` of the product of the tables and of `t`, then `s` is a restriction of
`t`, with the legs at their places. -/
private theorem push_le_push_of_contract {L : Type} [Fintype L] [DecidableEq L] (π : J → I)
    (ξ : V → I) (ρ : L → V) (s : PartyTensor K J) (t : PartyTensor K L)
    (T : V → (∀ j, s.Index j) → (∀ l, t.Index l) → K)
    (hT : ∀ v x x' y y', (∀ j, π j = ξ v → x j = x' j) → (∀ l, ρ l = v → y l = y' l) →
      T v x y = T v x' y')
    (h : ∀ x, s.entry x = ∑ y, (∏ v, T v x y) * t.entry y) :
    push π s ≤ push (fun l => ξ (ρ l)) t := by
  classical
  rcases isEmpty_or_nonempty (∀ j, s.Index j) with hs | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ _ _ => 0, fun x => (hs.false fun j => x (π j) ⟨j, rfl⟩).elim⟩
  rcases isEmpty_or_nonempty (∀ l, t.Index l) with ht | ⟨⟨y₀⟩⟩
  · refine ⟨fun _ _ _ => 0, fun x => ?_⟩
    rw [push_entry, h, Finset.univ_eq_empty, Finset.sum_empty]
    have : IsEmpty (∀ q, (push (fun l => ξ (ρ l)) t).Index q) :=
      ⟨fun y => ht.false fun l => y (ξ (ρ l)) ⟨l, rfl⟩⟩
    rw [localApply, Finset.univ_eq_empty, Finset.sum_empty]
  let ex : ∀ q, (∀ j : {j : J // π j = q}, s.Index j.val) → ∀ j, s.Index j :=
    fun q a j => if hj : π j = q then a ⟨j, hj⟩ else x₀ j
  let ey : ∀ q, (∀ l : {l : L // ξ (ρ l) = q}, t.Index l.val) → ∀ l, t.Index l :=
    fun q b l => if hl : ξ (ρ l) = q then b ⟨l, hl⟩ else y₀ l
  refine ⟨fun q a b => ∏ v : {v : V // ξ v = q}, T v.val (ex q a) (ey q b), fun x => ?_⟩
  rw [push_entry, h, localApply]
  symm
  refine Fintype.sum_equiv
    (Equiv.piCongrFiberwise (f := fun l => ξ (ρ l)) fun _ => Equiv.refl _).symm _ _ fun y => ?_
  congr 1
  rw [← Fintype.prod_fiberwise ξ]
  refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨v, rfl⟩ := v
  refine hT v _ _ _ _ (fun j hj => ?_) (fun l hl => ?_)
  · have : ex (ξ v) (x (ξ v)) j = x (ξ v) ⟨j, hj⟩ := dite_eq_left hj
    rw [this]
    clear this
    revert hj
    generalize ξ v = q
    rintro rfl
    rfl
  · subst hl
    exact dite_eq_left rfl

section Outer

variable {κ : Type} [Fintype κ] {M : κ → Type}

/-- The product of tensors with separate legs. -/
@[expose] def outer (t : ∀ k, PartyTensor K (M k)) : PartyTensor K (Σ k, M k) where
  Index l := (t l.1).Index l.2
  entry y := ∏ k, (t k).entry fun m => y ⟨k, m⟩

/-- Giving the legs of a product with separate legs to parties. -/
theorem antisymmRel_push_outer [DecidableEq κ] [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
    (π : (Σ k, M k) → I) (t : ∀ k, PartyTensor K (M k)) :
    AntisymmRel (· ≤ ·) (push π (outer t)) (prod fun k => push (fun m => π ⟨k, m⟩) (t k)) :=
  antisymmRel_of_equiv
    (fun _ => ⟨fun y k j => y ⟨⟨k, j.val⟩, j.property⟩, fun z l => z l.val.1 ⟨l.val.2, l.property⟩,
      fun _ => rfl, fun _ => rfl⟩)
    fun _ => rfl

end Outer

section Two

variable {L L' : Type} [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L']

/-- The product of two tensors with separate legs. -/
@[expose] def outerPair (s : PartyTensor K L) (t : PartyTensor K L') :
    PartyTensor K (L ⊕ L') where
  Index l := Sum.elim s.Index t.Index l
  fintype l := match l with
    | Sum.inl l => s.fintype l
    | Sum.inr l => t.fintype l
  decEq l := match l with
    | Sum.inl l => s.decEq l
    | Sum.inr l => t.decEq l
  entry y := s.entry (fun l => y (Sum.inl l)) * t.entry (fun l => y (Sum.inr l))

/-- Giving the legs of a product of two tensors with separate legs to parties. -/
theorem antisymmRel_push_outerPair (π : L ⊕ L' → I) (s : PartyTensor K L)
    (t : PartyTensor K L') :
    AntisymmRel (· ≤ ·) (push π (outerPair s t))
      (push (fun l => π (Sum.inl l)) s * push (fun l => π (Sum.inr l)) t) :=
  antisymmRel_of_equiv
    (fun q => ⟨fun y =>
        (fun l => y ⟨Sum.inl l.val, l.property⟩, fun l => y ⟨Sum.inr l.val, l.property⟩),
      fun z l => match l with
        | ⟨Sum.inl l, h⟩ => z.1 ⟨l, h⟩
        | ⟨Sum.inr l, h⟩ => z.2 ⟨l, h⟩,
      fun y => by funext l; obtain ⟨l | l, h⟩ := l <;> rfl, fun z => rfl⟩)
    fun _ => rfl

end Two

/-- A sum over pairs of labels that must be equal. -/
theorem sum_mul_prod_unit {E : Type} [Fintype E] [DecidableEq E] (n : E → ℕ)
    (g : (∀ e, Fin 2 → Fin (n e)) → K) :
    ∑ z : ∀ e, Fin 2 → Fin (n e), g z * ∏ e, (unit K (Fin 2) (n e)).entry (z e) =
      ∑ l : ∀ e, Fin (n e), g fun e _ => l e := by
  symm
  refine Finset.sum_of_injOn (fun l e _ => l e) (fun l _ l' _ h => ?_) (fun _ _ => by simp)
    (fun z _ hz => ?_) (fun l _ => ?_)
  · funext e
    exact congr_fun (congr_fun h e) 0
  · obtain ⟨e, he⟩ : ∃ e, ¬ ∀ i j, z e i = z e j := not_forall.mp fun hcon =>
      hz ⟨fun e => z e 0, by simp, funext fun e => funext fun i => hcon e 0 i⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ e), mul_zero]
    exact ite_eq_right he
  · rw [Finset.prod_eq_one, mul_one]
    intro e _
    exact ite_eq_left fun _ _ => rfl

/-- **Networks.** The vertices `v` are placed at the parties `ξ v`, the legs `j` of `s` are held
by the parties `π j`. There are edges `e` with labels in `Λ e` and ends `a e`, `b e`, and tensors
`t k` with their legs `m` at the vertices `ρ k m`. Each vertex has a local table `T v`: it depends
only on the legs of `s` held by the party `ξ v`, on the labels of the edges at `v`, and on the legs
of the `t k` at `v`. If `s` is the sum over all labels of the product of the tables and of the
`t k`, then `s` is a restriction of the product of the wires on the edges and of the `t k`, all at
their places. -/
theorem push_le_of_network {E κ : Type} [Fintype E] [DecidableEq E] [Fintype κ] [DecidableEq κ]
    {M : κ → Type} [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
    (π : J → I) (ξ : V → I) (s : PartyTensor K J) (Λ : E → Type) [∀ e, Fintype (Λ e)]
    (a b : E → V) (t : ∀ k, PartyTensor K (M k)) (ρ : ∀ k, M k → V)
    (T : V → (∀ j, s.Index j) → (∀ e, Λ e) → (∀ k m, (t k).Index m) → K)
    (hT : ∀ v x x' l l' y y', (∀ j, π j = ξ v → x j = x' j) →
      (∀ e, a e = v ∨ b e = v → l e = l' e) → (∀ k m, ρ k m = v → y k m = y' k m) →
      T v x l y = T v x' l' y')
    (h : ∀ x, s.entry x = ∑ l : ∀ e, Λ e, ∑ y : ∀ k m, (t k).Index m,
      (∏ v, T v x l y) * ∏ k, (t k).entry (y k)) :
    push π s ≤
      (prod (fun e => wire K (Fintype.card (Λ e)) (ξ (a e)) (ξ (b e))) *
        prod (fun k => push (fun m => ξ (ρ k m)) (t k))) := by
  classical
  let n : E → ℕ := fun e => Fintype.card (Λ e)
  let eq : ∀ e, Fin (n e) ≃ Λ e := fun e => (Fintype.equivFin (Λ e)).symm
  let U : PartyTensor K (Σ _ : E, Fin 2) := outer fun e => unit K (Fin 2) (n e)
  let ρ' : (Σ _ : E, Fin 2) ⊕ (Σ k, M k) → V :=
    Sum.elim (fun l => ![a l.1, b l.1] l.2) (fun l => ρ l.1 l.2)
  let T' : V → (∀ j, s.Index j) → (∀ l, (outerPair U (outer t)).Index l) → K := fun v x y =>
    T v x (fun e => eq e (if a e = v then y (Sum.inl ⟨e, 0⟩) else y (Sum.inl ⟨e, 1⟩)))
      (fun k m => y (Sum.inr ⟨k, m⟩))
  have key : push π s ≤ push (fun l => ξ (ρ' l)) (outerPair U (outer t)) := by
    refine push_le_push_of_contract π ξ ρ' s (outerPair U (outer t)) T'
      (fun v x x' y y' hx hy => ?_) fun x => ?_
    · refine hT v _ _ _ _ _ _ hx (fun e he => ?_) fun k m hm => hy (Sum.inr ⟨k, m⟩) hm
      by_cases ha : a e = v
      · simp only [ha, ↓reduceIte, hy (Sum.inl ⟨e, 0⟩) ha]
      · simp only [ha, ↓reduceIte, hy (Sum.inl ⟨e, 1⟩) (he.resolve_left ha)]
    · rw [h]
      let Φ : (∀ l, (outerPair U (outer t)).Index l) ≃
          (∀ e, Fin 2 → Fin (n e)) × (∀ k m, (t k).Index m) :=
        ⟨fun y => (fun e i => y (Sum.inl ⟨e, i⟩), fun k m => y (Sum.inr ⟨k, m⟩)),
          fun z l => match l with
            | Sum.inl l => z.1 l.1 l.2
            | Sum.inr l => z.2 l.1 l.2,
          fun y => by funext l; rcases l with l | l <;> rfl, fun z => rfl⟩
      let g : (∀ e, Fin 2 → Fin (n e)) → (∀ k m, (t k).Index m) → K := fun z y =>
        (∏ v, T v x (fun e => eq e (if a e = v then z e 0 else z e 1)) y) *
          ∏ k, (t k).entry (y k)
      have e1 : ∑ y, (∏ v, T' v x y) * (outerPair U (outer t)).entry y =
          ∑ z : (∀ e, Fin 2 → Fin (n e)) × (∀ k m, (t k).Index m),
            g z.1 z.2 * ∏ e, (unit K (Fin 2) (n e)).entry (z.1 e) := by
        refine Fintype.sum_equiv Φ _ _ fun y => ?_
        change (∏ v, T' v x y) * ((∏ e, (unit K (Fin 2) (n e)).entry ((Φ y).1 e)) *
          ∏ k, (t k).entry ((Φ y).2 k)) = (∏ v, T' v x y) * (∏ k, (t k).entry ((Φ y).2 k)) *
            ∏ e, (unit K (Fin 2) (n e)).entry ((Φ y).1 e)
        ring
      have e2 : ∀ y : ∀ k m, (t k).Index m,
          ∑ z : ∀ e, Fin 2 → Fin (n e), g z y * ∏ e, (unit K (Fin 2) (n e)).entry (z e) =
            ∑ l : ∀ e, Λ e, (∏ v, T v x l y) * ∏ k, (t k).entry (y k) := by
        intro y
        rw [sum_mul_prod_unit n fun z => g z y]
        refine Fintype.sum_equiv (Equiv.piCongrRight eq) _ _ fun l => ?_
        simp only [g, ite_self]
        rfl
      rw [e1, Fintype.sum_prod_type_right, Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => (e2 y).symm
  refine key.trans ((antisymmRel_push_outerPair _ U (outer t)).1.trans (mul_le_mul' ?_ ?_))
  · refine (antisymmRel_push_outer (fun l : Σ _ : E, Fin 2 => ξ (ρ' (Sum.inl l))) _).1.trans
      (prod_le_prod fun e => ?_)
    rw [show (fun m => ξ (ρ' (Sum.inl ⟨e, m⟩))) = ![ξ (a e), ξ (b e)] from
      funext fun m => by fin_cases m <;> rfl]
    exact le_rfl
  · exact (antisymmRel_push_outer (fun l : Σ k, M k => ξ (ρ' (Sum.inr l))) t).1

/-- Networks without other tensors: if `s` is the sum over all labels of the edges of the product
of local tables, then `s` is a restriction of the product of the wires on the edges, at their
places. -/
theorem push_le_of_edges {E : Type} [Fintype E] [DecidableEq E]
    (π : J → I) (ξ : V → I) (s : PartyTensor K J) (Λ : E → Type) [∀ e, Fintype (Λ e)]
    (a b : E → V) (T : V → (∀ j, s.Index j) → (∀ e, Λ e) → K)
    (hT : ∀ v x x' l l', (∀ j, π j = ξ v → x j = x' j) →
      (∀ e, a e = v ∨ b e = v → l e = l' e) → T v x l = T v x' l')
    (h : ∀ x, s.entry x = ∑ l : ∀ e, Λ e, ∏ v, T v x l) :
    push π s ≤ prod fun e => wire K (Fintype.card (Λ e)) (ξ (a e)) (ξ (b e)) := by
  have := push_le_of_network (κ := Empty) (M := fun _ => Empty) π ξ s Λ a b
    (fun k => k.elim) (fun k => k.elim) (fun v x l _ => T v x l)
    (fun v x x' l l' _ _ hx hl _ => hT v x x' l l' hx hl)
    (fun x => (h x).trans (Finset.sum_congr rfl fun l _ => by simp))
  exact this.trans <|
    (mul_le_mul' le_rfl (antisymmRel_prod_of_isEmpty _).le).trans (antisymmRel_mul_one _).le

end Cslib.PartyTensor
