/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.GridSum
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.NetworkPolynomial

/-!
# The network polynomial as a projection of the permanent: Lemma E.3

The polynomial `f_{k,ℓ}` of the complete network on `k` nodes with strings of `ℓ` bits
(`Flat.networkPolynomial`) is a clause sum over the bits of the strings on the wires: for every
node `a` and every view `ρ` of `a` (`Flat.NodeView`), there is a clause with the weight `x_{a,ρ}`
whose literals say that `a` sees `ρ`. Each of the at most `k * 2 ^ (k ℓ)` views has at most `k ℓ`
literals, so by Corollary E.2 `f_{k,ℓ}` is an affine projection of `G.poly M` for every family `G`
complete for grid sums with blow-up `c` and every `M ≥ c k³ ℓ 2^{kℓ}`
(`Flat.isAffineProjection_networkPolynomial`). For the permanent this is Lemma E.3: when `2 ≠ 0`,
a circuit with `s` nodes for `PERM_M`, `M ≥ 3 k³ ℓ 2^{kℓ}`, gives one with `5 s` nodes for
`f_{k,ℓ}` (`Flat.computedWithin_networkPolynomial`).

The paper's `f_{k,ℓ}` has a variable `x_{a,ρ}` only for the views `ρ`, which have no string for
`a` itself. `Flat.networkPolynomialOnViews` is this polynomial; renaming its variables gives
`Flat.networkPolynomial` (`Flat.rename_networkPolynomialOnViews`), so a circuit for it is one for
`Flat.networkPolynomial` with the same number of nodes (`ComputedWithin.rename`).

## Main definitions

* `Flat.NodeView`: what a node sees, the variables of the paper's `f_{k,ℓ}`.
* `Flat.networkPolynomialOnViews`: `f_{k,ℓ}` in these variables.

## Main results

* `Flat.rename_networkPolynomialOnViews`: renaming the variables gives the network polynomial.
* `Flat.isAffineProjection_networkPolynomial`: a projection of every family complete for grid
  sums.
* `Flat.computedWithin_networkPolynomial`: Lemma E.3.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma E.3 and its proof (p. 33), Corollary E.2 (p. 32); module `Paper.Flat`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset MvPolynomial

variable {k ℓ : ℕ}

/-- What a node of the complete network sees: the strings on its wires to the other nodes, and the
zero string for itself. -/
@[ext]
structure NodeView (k ℓ : ℕ) where
  /-- The node. -/
  node : Fin k
  /-- The strings that the node sees, one for each node. -/
  strings : Fin k → BitString ℓ
  /-- The string for the node itself is zero. -/
  strings_node : strings node = fun _ => false
  deriving DecidableEq

noncomputable instance : Fintype (NodeView k ℓ) :=
  Fintype.ofInjective (fun v => (v.node, v.strings)) fun _ _ h =>
    NodeView.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The polynomial of the complete network in the variables of the views, as printed in the
paper: the sum, over the strings on all wires, of the product of the variables of what the nodes
see. -/
noncomputable def networkPolynomialOnViews (F : Type*) [CommSemiring F] (k ℓ : ℕ) :
    MvPolynomial (NodeView k ℓ) F :=
  ∑ s : Pair k → BitString ℓ, ∏ a, X ⟨a, assemble (fun e _ => s e) a, assemble_self _ a⟩

/-- Renaming the views to the pairs of a node and strings gives the network polynomial. -/
theorem rename_networkPolynomialOnViews (F : Type*) [CommSemiring F] :
    rename (fun v : NodeView k ℓ => (v.node, v.strings)) (networkPolynomialOnViews F k ℓ) =
      networkPolynomial F k ℓ := by
  simp only [networkPolynomialOnViews, networkPolynomial, map_sum, map_prod, rename_X]

/-! ### The clause sum -/

/-- The wire between a node `a` and another node `b`. -/
private def wireAt (a b : Fin k) (h : b ≠ a) : Pair k :=
  if hab : a < b then ⟨a, b, hab⟩ else ⟨b, a, lt_of_le_of_ne (not_lt.1 hab) h⟩

private theorem assemble_wireAt (s : Pair k → BitString ℓ) {a b : Fin k} (h : b ≠ a) :
    assemble (fun e _ => s e) a b = s (wireAt a b h) := by
  unfold assemble wireAt
  split_ifs <;> first | rfl | omega

/-- The literals of the clause of a view: every bit of every string that the node sees is the bit
of the string on the wire. -/
private noncomputable def lits (v : NodeView k ℓ) : List ((Pair k × Fin ℓ) × Bool) :=
  (univ : Finset ({b // b ≠ v.node} × Fin ℓ)).toList.map fun p =>
    ((wireAt v.node p.1 p.1.prop, p.2), v.strings p.1 p.2)

private theorem forall_lits (v : NodeView k ℓ) (x : Pair k × Fin ℓ → Bool) :
    (∀ l ∈ lits v, x l.1 = l.2) ↔ v.strings = assemble (fun e _ i => x (e, i)) v.node := by
  simp only [lits, List.forall_mem_map, mem_toList, mem_univ, forall_const, Prod.forall,
    Subtype.forall]
  constructor
  · refine fun h => funext fun b => ?_
    by_cases hb : b = v.node
    · rw [hb, v.strings_node, assemble_self]
    · rw [assemble_wireAt (fun e i => x (e, i)) hb]
      exact funext fun i => (h b hb i).symm
  · rintro h b hb i
    rw [h, assemble_wireAt (fun e i => x (e, i)) hb]

/-- The network polynomial is the clause sum of the views, each with its variable as weight. -/
private theorem clauseSum_lits (F : Type*) [CommSemiring F] :
    clauseSum lits (fun v : NodeView k ℓ => (X (v.node, v.strings) : MvPolynomial _ F)) =
      networkPolynomial F k ℓ := by
  refine Fintype.sum_equiv (Equiv.curry _ _ _) _ _ fun x => ?_
  simp only [forall_lits, ← prod_filter]
  refine prod_nbij' NodeView.node (fun a => ⟨a, assemble (fun e _ i => x (e, i)) a,
    assemble_self _ a⟩) (fun _ _ => mem_univ _)
    (fun a _ => mem_filter.2 ⟨mem_univ _, rfl⟩) (fun v hv => ?_) (fun _ _ => rfl) (fun v hv => ?_)
  · exact NodeView.ext rfl (mem_filter.1 hv).2.symm
  · rw [(mem_filter.1 hv).2]
    rfl

private theorem lits_ne_nil (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (v : NodeView k ℓ) : lits v ≠ [] := by
  have := Fin.nontrivial_iff_two_le.2 hk
  obtain ⟨b, hb⟩ := exists_ne v.node
  simp only [lits, ne_eq, List.map_eq_nil_iff, toList_eq_nil, univ_eq_empty_iff, not_isEmpty_iff]
  exact ⟨(⟨b, hb⟩, ⟨0, hℓ⟩)⟩

private theorem exists_mem_lits (b : Pair k × Fin ℓ) : ∃ v, ∃ l ∈ lits v, l.1 = b := by
  obtain ⟨e, i⟩ := b
  refine ⟨⟨e.low, fun _ _ => false, rfl⟩, _, List.mem_map.2
    ⟨(⟨e.high, e.low_lt_high.ne'⟩, i), mem_toList.2 (mem_univ _), rfl⟩, ?_⟩
  simp [wireAt, e.low_lt_high]

private theorem sum_length_lits_le (hk : 1 ≤ k) :
    ∑ v : NodeView k ℓ, (lits v).length ≤ k ^ 3 * ℓ * 2 ^ (k * ℓ) := by
  have h1 (v : NodeView k ℓ) : (lits v).length ≤ k * ℓ := by
    simp only [lits, List.length_map, length_toList, card_univ, Fintype.card_prod,
      Fintype.card_fin]
    exact Nat.mul_le_mul_right _ ((Fintype.card_subtype_le _).trans_eq (Fintype.card_fin k))
  have h2 : Fintype.card (NodeView k ℓ) ≤ k * 2 ^ (k * ℓ) := by
    refine (Fintype.card_le_of_injective (fun v => (v.node, v.strings)) fun v w h =>
      NodeView.ext (congrArg Prod.fst h) (congrArg Prod.snd h)).trans_eq ?_
    simp [← pow_mul, mul_comm ℓ k]
  calc ∑ v : NodeView k ℓ, (lits v).length ≤ Fintype.card (NodeView k ℓ) * (k * ℓ) := by
        simpa using sum_le_card_nsmul univ _ _ fun v _ => h1 v
    _ ≤ k * 2 ^ (k * ℓ) * (k * k * ℓ) :=
        Nat.mul_le_mul h2 (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left k hk))
    _ = _ := by ring

/-! ### Lemma E.3 -/

variable {K : Type} [Field K]

/-- **The network polynomial is a projection of every family complete for grid sums.** If `G` is
complete for grid sums with blow-up `c`, `k ≥ 2`, `ℓ ≥ 1` and `M ≥ c k³ ℓ 2^{kℓ}`, then `f_{k,ℓ}`
is an affine projection of `G.poly M`. -/
theorem isAffineProjection_networkPolynomial {G : PolynomialFamily K} {c : ℕ}
    (hG : GridComplete G c) (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {M : ℕ}
    (hM : c * k ^ 3 * ℓ * 2 ^ (k * ℓ) ≤ M) :
    IsAffineProjection (networkPolynomial K k ℓ) (G.poly M) := by
  rw [← clauseSum_lits]
  refine hG.isAffineProjection_clauseSum lits (lits_ne_nil hk hℓ) exists_mem_lits _
    (fun _ => Or.inl ⟨_, rfl⟩) ((Nat.mul_le_mul_left c (sum_length_lits_le (by omega))).trans ?_)
  simpa only [mul_assoc] using hM

/-- **Paper: Lemma E.3** (p. 33). Let `2 ≠ 0` in `K`, `k ≥ 2` and `ℓ ≥ 1`. If `PERM_M` is
computed by a circuit with `s` nodes and `M ≥ 3 k³ ℓ 2^{kℓ}`, then `f_{k,ℓ}` is computed by one
with `5 s` nodes. -/
theorem computedWithin_networkPolynomial (h2 : (2 : K) ≠ 0) (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {M s : ℕ}
    (hM : 3 * k ^ 3 * ℓ * 2 ^ (k * ℓ) ≤ M) (hs : ComputedWithin ((permFamily K).poly M) s) :
    ComputedWithin (networkPolynomial K k ℓ) (5 * s) :=
  hs.of_isAffineProjection
    (isAffineProjection_networkPolynomial (gridComplete_permFamily h2) hk hℓ hM)

end Cslib.Circuits.Arithmetic.Separation.Flat
