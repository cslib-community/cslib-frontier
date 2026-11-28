/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Open bit tensor networks

An open network has one exterior wire per named input bit. Its contraction is a function of
these bits. The table at a vertex may read only its incident internal wires and exterior bits.
In the volume convention of [OpenAI2026MatrixExponentNineFourths, Theorem 2.2], each internal
wire, exterior wire and vertex costs one. A loop contributes two incidences at its vertex.

Contracting an exterior bit against a unary table sums it out locally at its incident vertex.
This includes pinning a bit and taking a signed sum over its two values. Several such
contractions can be made simultaneously on the same graph.

## Main results

* `OpenBitNetwork.contraction_cap` computes the resulting exterior table.
* `OpenBitNetwork.Trivalent.cap` and `OpenBitNetwork.volume_cap_le` bound its arity and volume.
* `OpenBitNetwork.exists_pin` keeps an injectively named subset of the exterior bits and fixes
  all remaining bits.
-/

public section

namespace Cslib.Circuits.Frontier

/-- A finite network of bit wires with exterior bits `I`. Internal edges carry Boolean labels
and the coefficient of each local table is a function of the exterior input. -/
structure OpenBitNetwork (R I V E : Type*) [Finite I] [Finite V] [Finite E] extends
    TensorNetwork ((I → Bool) → R) Bool V E where
  /-- Vertex incident to each named exterior wire. -/
  site : I → V
  /-- Only exterior bits incident to a vertex affect its table. -/
  exterior_congr : ∀ v α x y, (∀ i, site i = v → x i = y i) → tensor v α x = tensor v α y

namespace OpenBitNetwork

variable {R I V E J H : Type*} [Finite I] [Finite V] [Finite E] (N : OpenBitNetwork R I V E)

/-- Each local table has at most three bit arguments. A loop uses an input and an output
incidence at its vertex. -/
@[expose] def Trivalent : Prop := ∀ v,
  {e | N.src e = v}.ncard + {e | N.tgt e = v}.ncard + {i | N.site i = v}.ncard ≤ 3

/-- Number of vertices plus the numbers of internal and exterior wires. -/
@[expose] noncomputable def volume (_ : OpenBitNetwork R I V E) : ℕ :=
  Nat.card V + Nat.card E + Nat.card I

variable [Finite J] [Fintype H] [CommSemiring R]

open scoped Classical in
/-- Keep the `J` exterior wires and contract the remaining `H` wires against unary tables.
The equivalence specifies which old wire occupies each position. -/
noncomputable def cap (legs : J ⊕ H ≃ I) (weight : H → Bool → R) : OpenBitNetwork R J V E where
  src := N.src
  tgt := N.tgt
  site j := N.site (legs (.inl j))
  tensor v α x := ∑ z : {h // N.site (legs (.inr h)) = v} → Bool,
    (∏ h, weight h.val (z h)) *
      N.tensor v α (Sum.elim x (Function.extend Subtype.val z (fun _ => false)) ∘ legs.symm)
  tensor_congr v α β h := by
    funext x
    simp only [N.tensor_congr v α β h]
  exterior_congr v α x y h := by
    apply Finset.sum_congr rfl
    intro z _
    congr 1
    apply N.exterior_congr
    intro i hi
    obtain ⟨j | j, rfl⟩ := legs.surjective i
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using h j hi
    · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]

theorem Trivalent.cap {N : OpenBitNetwork R I V E} (hN : N.Trivalent)
    (legs : J ⊕ H ≃ I) (weight : H → Bool → R) : (N.cap legs weight).Trivalent := by
  intro v
  apply le_trans _ (hN v)
  apply Nat.add_le_add_left
  exact Set.ncard_le_ncard_of_injOn (fun j => legs (.inl j)) (fun _ h => h)
    (legs.injective.comp Sum.inl_injective).injOn

theorem volume_cap_le (legs : J ⊕ H ≃ I) (weight : H → Bool → R) :
    (N.cap legs weight).volume ≤ N.volume := by
  exact Nat.add_le_add_left
    (Nat.card_le_card_of_injective (fun j => legs (.inl j))
      (legs.injective.comp Sum.inl_injective)) _

open scoped Classical in
/-- The exterior tensor of a capped network is the weighted sum over the capped bits. -/
theorem contraction_cap [Fintype V] [Fintype E] [DecidableEq E]
    (legs : J ⊕ H ≃ I) (weight : H → Bool → R) (x : J → Bool) :
    (N.cap legs weight).contraction x = ∑ z : H → Bool, (∏ h, weight h (z h)) *
      N.contraction (Sum.elim x z ∘ legs.symm) := by
  classical
  let atSite (h : H) := N.site (legs (.inr h))
  simp only [TensorNetwork.contraction, Finset.sum_apply, Finset.prod_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  simp only [cap, Fintype.prod_sum]
  symm
  refine Fintype.sum_equiv (Equiv.piCongrFiberwise (f := atSite) fun _ => Equiv.refl _) _ _
    fun z => ?_
  simp only [Equiv.piCongrFiberwise_apply, Equiv.refl_apply, Finset.prod_mul_distrib]
  congr 1
  · exact (Fintype.prod_fiberwise atSite (fun h => weight h (z h))).symm
  refine Finset.prod_congr rfl fun v _ => N.exterior_congr v α _ _ ?_
  intro i hi
  obtain ⟨j | h, rfl⟩ := legs.surjective i
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    exact (Subtype.val_injective.extend_apply (fun j => z j.val) (fun _ => false) ⟨h, hi⟩).symm

/-- Fix the exterior bits outside an embedding. The restriction keeps the internal graph,
is trivalent whenever the starting network is, and has smaller or equal volume. -/
theorem exists_pin [Fintype V] [Fintype E] [DecidableEq E] (hN : N.Trivalent)
    (e : J ↪ I) (fill : I → Bool) :
    ∃ M : OpenBitNetwork R J V E, M.toMultigraph = N.toMultigraph ∧ M.site = N.site ∘ e ∧
      M.Trivalent ∧
      M.volume ≤ N.volume ∧ ∀ x, M.contraction x = N.contraction (Function.extend e x fill) := by
  classical
  let hidden : Set I := (Set.range e)ᶜ
  let legs : J ⊕ hidden ≃ I :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl hidden)).trans
      (Equiv.Set.sumCompl (Set.range e))
  let pin (h : hidden) (b : Bool) : R := if b = fill h then 1 else 0
  let : Fintype hidden := Fintype.ofFinite _
  refine ⟨N.cap legs pin, rfl, rfl, hN.cap legs pin, N.volume_cap_le legs pin, fun x => ?_⟩
  rw [N.contraction_cap]
  simp only [pin, Fintype.prod_boole, ← funext_iff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  apply congrArg N.contraction
  funext i
  obtain ⟨j | h, rfl⟩ := legs.surjective i
  · change (Sum.elim x _ ∘ legs.symm) (legs (.inl j)) = Function.extend e x fill (e j)
    simp [e.injective.extend_apply]
  · change (Sum.elim x _ ∘ legs.symm) (legs (.inr h)) = Function.extend e x fill h.val
    simp [Function.extend_apply' _ _ _ h.prop]

/-- Rename the exterior bits of a trivalent network, preserving its whole table and volume. -/
theorem exists_reindex [Fintype V] [Fintype E] [DecidableEq E] (hN : N.Trivalent) (e : J ≃ I) :
    ∃ M : OpenBitNetwork R J V E, M.Trivalent ∧ M.volume = N.volume ∧
      ∀ x, M.contraction x = N.contraction (x ∘ e.symm) := by
  obtain ⟨M, _, _, hM, _, h⟩ := N.exists_pin hN e.toEmbedding (fun _ => false)
  refine ⟨M, hM, ?_, fun x => (h x).trans ?_⟩
  · simp only [volume, Nat.card_congr e]
  · apply congrArg N.contraction
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact (e.injective.extend_apply x (fun _ => false) j).trans
      (congrArg x (e.symm_apply_apply j)).symm

open scoped Classical in
/-- Apply the same exterior contraction to every factor of a tensor power. The initial network
may tie distinct factors together internally. The new network uses its same internal graph
and its volume can only decrease. -/
theorem exists_tensorPower_cap {T : Type*} [Fintype T] [Fintype V] [Fintype E] [DecidableEq E]
    (N : OpenBitNetwork R (T × I) V E) (hN : N.Trivalent) (legs : J ⊕ H ≃ I)
    (weight : H → Bool → R) (table : (I → Bool) → R)
    (htable : ∀ x, N.contraction x = ∏ a : T, table (fun i => x (a, i))) :
    ∃ M : OpenBitNetwork R (T × J) V E, M.toMultigraph = N.toMultigraph ∧ M.Trivalent ∧
      M.volume ≤ N.volume ∧
      ∀ x, M.contraction x = ∏ a : T, ∑ z : H → Bool, (∏ b, weight b (z b)) *
        table (Sum.elim (fun j => x (a, j)) z ∘ legs.symm) := by
  classical
  let e := (Equiv.prodSumDistrib T J H).symm.trans (Equiv.prodCongr (Equiv.refl T) legs)
  let weight' (b : T × H) := weight b.2
  let : DecidableEq (T × H) := Classical.decEq _
  refine ⟨N.cap e weight', rfl, hN.cap _ _, N.volume_cap_le _ _, fun x => ?_⟩
  rw [contraction_cap, Fintype.prod_sum]
  refine Fintype.sum_equiv (M := R) (Equiv.curry T H Bool) _ _ fun z => ?_
  rw [htable, Finset.prod_mul_distrib, Fintype.prod_prod_type]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  apply congrArg table
  funext i
  obtain ⟨j | b, rfl⟩ := legs.surjective i
  · simp [e, Equiv.curry]
  · simp [e, Equiv.curry, Function.curry]

end OpenBitNetwork
end Cslib.Circuits.Frontier
