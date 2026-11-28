/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Substitution
public import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators

/-!
# Joint replacements with partially occupied batches

Merging vertices into a single tensor keeps every old wire and multiplies the old tables in
each fiber. A shared verifier for a product of tables can therefore implement one whole group,
even when old wires connect vertices within a group. Unused slots of the verifier are fixed to
an input of weight one.
-/

public section

namespace Cslib.Circuits.Frontier.OpenBitNetwork

private def atPort {R I V E : Type*} [Finite I] [Finite V] [Finite E]
    (N : OpenBitNetwork R I V E) : (E ⊕ E) ⊕ I → V := Sum.elim (Sum.elim N.src N.tgt) N.site

section Group

variable {R I V W E : Type*} [Finite I] [Fintype V] [Finite W] [Finite E] [CommSemiring R]
  (N : OpenBitNetwork R I V E) (g : V → W)

open scoped Classical in
/-- Multiply the old vertex tables in each fiber of `g`, keeping the old internal wires. Wires
whose endpoints now belong to the same group become loops. -/
noncomputable def group : OpenBitNetwork R I W E where
  src := g ∘ N.src
  tgt := g ∘ N.tgt
  site := g ∘ N.site
  tensor w α x := ∏ v : {v // g v = w}, N.tensor v.val α x
  tensor_congr w α β h := by
    funext x
    refine Finset.prod_congr rfl fun v _ => congrFun (N.tensor_congr v.val _ _ ?_) x
    exact fun e he => h e (he.imp (fun hs => (congrArg g hs).trans v.prop)
      (fun ht => (congrArg g ht).trans v.prop))
  exterior_congr w α x y h := Finset.prod_congr rfl fun v _ => N.exterior_congr v.val _ _ _
    fun i hi => h i ((congrArg g hi).trans v.prop)

/-- Grouping old vertices preserves the contraction. -/
theorem contraction_group [Fintype W] [Fintype E] [DecidableEq E] (x : I → Bool) :
    (N.group g).contraction x = N.contraction x := by
  classical
  simp only [TensorNetwork.contraction, Finset.sum_apply, Finset.prod_apply, group]
  exact Finset.sum_congr rfl fun α _ => Fintype.prod_fiberwise g (fun v => N.tensor v α x)

private theorem atPort_group (p : (E ⊕ E) ⊕ I) : (N.group g).atPort p = g (N.atPort p) := by
  rcases p with (e | e) | i <;> rfl

/-- The legs of a group are the disjoint union of its old members' legs. In particular a wire
between two different members contributes two distinct legs at the grouped vertex. -/
def groupPorts (w : W) : (N.group g).Port w ≃ Σ v : {v // g v = w}, N.Port v.val where
  toFun p := ⟨⟨N.atPort p.val, (N.atPort_group g p.val).symm.trans p.prop⟩, ⟨p.val, rfl⟩⟩
  invFun p := ⟨p.2.val, (N.atPort_group g p.2.val).trans ((congrArg g p.2.prop).trans p.1.prop)⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨v, hv⟩, ⟨p, hp⟩⟩; cases hp; rfl

end Group

section Partial

variable {R L T S U H : Type*} [Finite L] [Fintype T] [Fintype S] [Fintype U] [Fintype H]
  [DecidableEq H] [CommSemiring R] (D : OpenBitNetwork R (T × L) U H)

/-- All occupied slots may use the same batch verifier, including a final partial group. Pinning
the remaining slots to an accepted assignment retains the verifier's vertices and internal wires. -/
theorem exists_pin_batch (hd : D.Trivalent) (slot : S ↪ T) (table : (L → Bool) → R)
    (accepted : L → Bool) (ha : table accepted = 1)
    (hD : ∀ x, D.contraction x = ∏ t, table (fun l => x (t, l))) :
    ∃ M : OpenBitNetwork R (S × L) U H, M.toMultigraph = D.toMultigraph ∧ M.Trivalent ∧
      ∀ x, M.contraction x = ∏ s, table (fun l => x (s, l)) := by
  classical
  let e := slot.prodMap (Function.Embedding.refl L)
  obtain ⟨M, hg, _, ht, _, hM⟩ := D.exists_pin hd e (fun p => accepted p.2)
  refine ⟨M, hg, ht, fun x => ?_⟩
  rw [hM, hD]
  symm
  apply Finset.prod_of_injOn slot slot.injective.injOn (fun _ _ => Finset.mem_univ _)
  · intro t _ ht
    convert! ha using 2
    funext l
    apply Function.extend_apply'
    rintro ⟨⟨s, l'⟩, hs⟩
    exact ht ⟨s, Finset.mem_univ _, congrArg Prod.fst hs⟩
  · intro s _
    congr 1
    funext l
    exact (e.injective.extend_apply x _ (s, l)).symm

end Partial

section Batch

variable {R I O C G E L : Type} [Finite I] [Fintype O] [Fintype C] [Fintype G] [Finite E]
  [CommSemiring R] (N : OpenBitNetwork R I (O ⊕ C) E) (batch : C → G)

private def callMembers (b : G) : {v : O ⊕ C // Sum.map id batch v = .inr b} ≃
    {c // batch c = b} where
  toFun | ⟨.inl _, h⟩ => nomatch h | ⟨.inr c, h⟩ => ⟨c, Sum.inr.inj h⟩
  invFun c := ⟨.inr c.val, congrArg Sum.inr c.prop⟩
  left_inv := by
    rintro ⟨o | c, h⟩
    · cases h
    · rfl
  right_inv _ := rfl

private def ordinaryPorts (o : O) : (N.group (Sum.map id batch)).Port (.inl o) ≃
    N.Port (.inl o) := Equiv.subtypeEquivRight fun p => by
  change (N.group (Sum.map id batch)).atPort p = Sum.inl o ↔ N.atPort p = Sum.inl o
  rw [atPort_group]
  rcases N.atPort p with o | c <;> simp

private def batchPorts (ports : ∀ c, N.Port (.inr c) ≃ L) (b : G) :
    (N.group (Sum.map id batch)).Port (.inr b) ≃ {c // batch c = b} × L :=
  let inside : ∀ v : {v : O ⊕ C // Sum.map id batch v = .inr b}, N.Port v.val ≃ L :=
    fun | ⟨.inl _, h⟩ => nomatch h | ⟨.inr c, _⟩ => ports c
  (N.groupPorts (Sum.map id batch) (.inr b)).trans ((Equiv.sigmaCongrRight inside).trans
    ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodCongr (callMembers batch b) (Equiv.refl L))))

/-- Joint substitution for any partition of the calls. The injection gives each call a distinct
slot within its own batch. Empty slots are pinned to `accepted`; even the final partial batch
uses just one copy of the verifier's interior. -/
theorem exists_replace_call_batches {I O C G E L U H T : Type} [Finite I] [Fintype O] [Fintype C]
    [Finite G] [Fintype E] [DecidableEq E] [Finite L] [Fintype U] [Fintype H] [DecidableEq H]
    [Fintype T] (N : OpenBitNetwork R I (O ⊕ C) E) (D : OpenBitNetwork R (T × L) U H)
    (batch : C → G) (slot : ∀ b, {c // batch c = b} ↪ T) (ports : ∀ c, N.Port (.inr c) ≃ L)
    (table : (L → Bool) → R) (accepted : L → Bool) (ha : table accepted = 1)
    (ho : ∀ o, Nat.card (N.Port (.inl o)) ≤ 3) (hd : D.Trivalent)
    (hD : ∀ x, D.contraction x = ∏ t, table (fun l => x (t, l)))
    (h : ∀ c (α : E → Bool) (x : I → Bool), N.tensor (.inr c) α x =
      table (fun j => Sum.elim (Sum.elim α α) x ((ports c).symm j).val)) :
    ∃ (W F : Type) (_ : Fintype W) (_ : Fintype F) (_ : DecidableEq F)
      (M : OpenBitNetwork R I W F), M.Trivalent ∧
      M.volume = Nat.card O + Nat.card E + Nat.card I + Nat.card G * (Nat.card U + Nat.card H) ∧
      ∀ x, M.contraction x = N.contraction x := by
  classical
  let := Fintype.ofFinite G
  choose B _ ht hB using fun b => D.exists_pin_batch hd (slot b) table accepted ha hD
  let g := Sum.map (id : O → O) batch
  obtain ⟨W, F, iW, iF, dF, M, hM, hsize, heval⟩ := exists_replace_call_family (N.group g) B
    (N.batchPorts batch ports) (fun o => (Nat.card_congr (N.ordinaryPorts batch o)).le.trans (ho o))
    ht (fun b α x => by
      rw [hB]
      simp only [group]
      symm
      let : DecidablePred (fun v : O ⊕ C => Sum.map id batch v = .inr b) :=
        fun _ => Classical.propDecidable _
      refine Fintype.prod_equiv (callMembers batch b) _ _ ?_
      rintro ⟨o | c, hp⟩
      · cases hp
      · exact h c α x)
  exact ⟨W, F, iW, iF, dF, M, hM, hsize, fun x => (heval x).trans (N.contraction_group g x)⟩

/-- Use the fewest batches of this verifier that cover the calls. If its volume per argument is
`p`, then the replacement costs at most `p` times three host volumes plus one batch of arguments.
The latter term accounts for a partially occupied final batch. -/
theorem exists_replace_call_batches_le {I O C E L U H T : Type} [Finite I] [Fintype O] [Fintype C]
    [Fintype E] [DecidableEq E] [Finite L] [Nonempty L] [Fintype U] [Fintype H] [DecidableEq H]
    [Fintype T] [Nonempty T] (N : OpenBitNetwork R I (O ⊕ C) E)
    (D : OpenBitNetwork R (T × L) U H) (ports : ∀ c, N.Port (.inr c) ≃ L)
    (table : (L → Bool) → R) (accepted : L → Bool) (ha : table accepted = 1)
    (ho : ∀ o, Nat.card (N.Port (.inl o)) ≤ 3) (hd : D.Trivalent)
    (hD : ∀ x, D.contraction x = ∏ t, table (fun l => x (t, l)))
    (h : ∀ c (α : E → Bool) (x : I → Bool), N.tensor (.inr c) α x =
      table (fun j => Sum.elim (Sum.elim α α) x ((ports c).symm j).val)) :
    ∃ (W F : Type) (_ : Fintype W) (_ : Fintype F) (_ : DecidableEq F)
      (M : OpenBitNetwork R I W F), M.Trivalent ∧
      M.volume ≤ N.volume + (Nat.card C ⌈/⌉ Nat.card T) * D.volume ∧
      (M.volume : ℝ) ≤ D.volume / (Nat.card T * Nat.card L : ℕ) *
        (3 * N.volume + (Nat.card T * Nat.card L : ℕ)) ∧
      ∀ x, M.contraction x = N.contraction x := by
  classical
  let b := Nat.card C ⌈/⌉ Nat.card T
  have ht : 0 < Nat.card T := Nat.card_pos
  have hcapacity : Nat.card C ≤ Nat.card T * b := (ceilDiv_le_iff_le_mul ht).1 le_rfl
  obtain ⟨pack⟩ : Nonempty (C ↪ Fin b × T) := Function.Embedding.nonempty_of_card_le
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_prod, Nat.card_fin,
             Nat.mul_comm]; exact hcapacity)
  let groupOf (c : C) := (pack c).1
  let slot (k : Fin b) : {c // groupOf c = k} ↪ T :=
    ⟨fun c => (pack c.val).2, fun c d he => Subtype.ext (pack.injective
      (Prod.ext (c.prop.trans d.prop.symm) he))⟩
  obtain ⟨W, F, iW, iF, dF, M, htri, hsize, heval⟩ := exists_replace_call_batches N D groupOf
    slot ports table accepted ha ho hd hD h
  have hhost : M.volume ≤ N.volume + b * D.volume := by
    rw [hsize, Nat.card_fin]
    simp only [volume, Nat.card_sum]
    exact Nat.add_le_add (by lia) (Nat.mul_le_mul_left _ (Nat.le_add_right ..))
  refine ⟨W, F, iW, iF, dF, M, htri, hhost, ?_, heval⟩
  let k := Nat.card T * Nat.card L
  let p : ℝ := D.volume / k
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.mul_pos ht (Nat.card_pos (α := L))
  have hone : 1 ≤ p := (one_le_div hk).2 (by
    exact_mod_cast (show k ≤ D.volume by simp [k, volume, Nat.card_prod]))
  have hp : p * k = D.volume := div_mul_cancel₀ _ hk.ne'
  have hwires : Nat.card C * Nat.card L ≤ 2 * N.volume :=
    (N.call_arity_le ports).trans (by simp only [volume, Nat.card_sum]; lia)
  have hround : b * Nat.card T ≤ Nat.card C + Nat.card T :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le ..)
  have hbound : b * k ≤ 2 * N.volume + k := by
    calc _ = (b * Nat.card T) * Nat.card L := (Nat.mul_assoc ..).symm
         _ ≤ (Nat.card C + Nat.card T) * Nat.card L := Nat.mul_le_mul_right _ hround
         _ ≤ _ := by rw [Nat.add_mul]; exact Nat.add_le_add_right hwires _
  have hr : (b : ℝ) * k ≤ 2 * N.volume + k := by exact_mod_cast hbound
  calc (M.volume : ℝ) ≤ N.volume + b * (D.volume : ℝ) := by exact_mod_cast hhost
       _ = N.volume + p * (b * (k : ℝ)) := by rw [← hp]; ring
       _ ≤ p * N.volume + p * (2 * N.volume + k) := add_le_add
         (le_mul_of_one_le_left (Nat.cast_nonneg _) hone) (mul_le_mul_of_nonneg_left hr (by
           exact zero_le_one.trans hone))
       _ = _ := by change _ = p * (3 * N.volume + k); ring

end Batch

end Cslib.Circuits.Frontier.OpenBitNetwork
