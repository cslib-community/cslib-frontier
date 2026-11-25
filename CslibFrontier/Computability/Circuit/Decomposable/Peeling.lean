/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Decomposable
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Peeling large rectangles from deterministic decomposable DAGs

A smooth decomposable DAG has *disjoint unions* (`DecomposableDAG.DisjointUnions`) when no input
is accepted by two distinct children of a union node. Over `Bool` with literal leaves, these are
the smooth deterministic DNNFs (d-DNNFs) of knowledge compilation [Darwiche2001].

In any smooth decomposable DAG, the inputs for which a node `v` occurs on an accepting certificate
form the rectangle of its accepted assignments and its contexts
(`DecomposableDAG.occurs_eq_rectangle`). When unions are disjoint, every accepted input has a
*unique* accepting certificate, so replacing `v` by an empty leaf (`DecomposableDAG.eraseNode`)
removes *precisely* that rectangle from the accepted set and no other inputs
(`DecomposableDAG.accepted_eraseNode`), even when `v` is shared across many branches that partition
the coordinates in incompatible ways.

**Peeling** (`DecomposableDAG.abs_signedCount_accepted_le`). Let `S` have bias at most `b ≥ 0` on
rectangles with both sides of size at least `K` (`RectangleBias`). While some occurring node `v`
has at least `K` accepted assignments and at least `K` contexts, its occurring inputs form such a
rectangle, and deleting `v` peels that rectangle cleanly without increasing the number of union
edges or products. Once no such node remains, every node has a side smaller than `K`, so threshold
counting (`DecomposableDAG.ncard_accepted_le_of_smallSides`) bounds the remaining accepted inputs
by `(K - 1) ^ 2 · #(union edges) + (K - 1) ^ 3 · #(products)` when at least `K` remain, and by
`K - 1` otherwise (covering the single-leaf case where `unionEdges = products = 0`). Combining
both phases extends Sam McGuire's branching-program peeling lemma to deterministic decomposable
DAGs:

`|signedCount S accepted| ≤ 2 b |accepted| + (K - 1) ^ 2 · #(union edges)`
`                           + (K - 1) ^ 3 · #(products) + (K - 1)`.

These node-deletion and `RectangleBias` peeling theorems on `DecomposableDAG` are original to this
library, adapting the d-DNNF determinism condition of [Darwiche2001] and rectangle decomposition of
[BovaCapelliMengelSlivovsky2016] to Sam McGuire's peeling method in
`CslibFrontier.Computability.Circuit.Frontier.AverageCase`.

## Main definitions

* `Cslib.Circuits.DecomposableDAG.DisjointUnions`: determinism (disjoint children at every union).
* `Cslib.Circuits.DecomposableDAG.eraseNode`: the DAG with a node replaced by an empty leaf.

## Main results

* `Cslib.Circuits.DecomposableDAG.accepted_eraseNode`: under `DisjointUnions`, deleting a node
  removes exactly the inputs for which it occurs.
* `Cslib.Circuits.DecomposableDAG.abs_signedCount_accepted_le`: McGuire peeling for deterministic
  smooth decomposable DAGs.
* `Cslib.Circuits.DecomposableDAG.abs_signedCount_accepted_le_size`: peeling in terms of `size`.

## References

* [A. Darwiche, *Decomposable negation normal form*][Darwiche2001]
* [S. Bova, F. Capelli, S. Mengel, F. Slivovsky, *Knowledge compilation meets communication
  complexity*][BovaCapelliMengelSlivovsky2016]
-/

public section

namespace Cslib.Circuits.DecomposableDAG

open Set Frontier

variable {ι U N : Type*}

/-- A smooth decomposable DAG has *disjoint unions* (is *deterministic*) when no two distinct
children of any union node accept a common input. -/
@[expose] def DisjointUnions (P : DecomposableDAG ι U N) : Prop :=
  ∀ v c, P.gate v = .union c → ∀ u₁ ∈ c, ∀ u₂ ∈ c, u₁ ≠ u₂ →
    Disjoint (P.accepts u₁) (P.accepts u₂)

/-! ### Deleting a node -/

section Erase

variable (P : DecomposableDAG ι U N)

/-- Recomputed node assignment sets after replacing `v₀` by an empty leaf, defined bottom-up by
well-founded recursion on `P.rank`. -/
private def eraseValues [DecidableEq N] (v₀ : N) (w : N) : Set (P.scope w → U) :=
  if w = v₀ then ∅
  else match hg : P.gate w with
    | .leaf => P.values w
    | .union c =>
      {a | ∃ (u : N) (hu : u ∈ c),
        (fun i : P.scope u => a ⟨i.1, P.scope_union w c hg u hu ▸ i.2⟩) ∈ eraseValues v₀ u}
    | .product l r =>
      {a | (fun i : P.scope l =>
          a ⟨i.1, P.scope_product w l r hg ▸ mem_union_left _ i.2⟩) ∈ eraseValues v₀ l ∧
        (fun i : P.scope r =>
          a ⟨i.1, P.scope_product w l r hg ▸ mem_union_right _ i.2⟩) ∈ eraseValues v₀ r}
termination_by P.rank w
decreasing_by
  · exact P.rank_union w c hg u hu
  · exact (P.rank_product w l r hg).1
  · exact (P.rank_product w l r hg).2

/-- The smooth decomposable DAG obtained by replacing the node `v₀` with an empty leaf and
recomputing acceptance bottom-up along the rank order. -/
noncomputable def eraseNode (v₀ : N) : DecomposableDAG ι U N :=
  open Classical in
  { scope := P.scope
    root := P.root
    scope_root := P.scope_root
    gate := fun w => if w = v₀ then .leaf else P.gate w
    rank := P.rank
    values := P.eraseValues v₀
    values_subsingleton := fun w hg => by
      unfold eraseValues
      by_cases hw : w = v₀
      · simp only [hw, ↓reduceIte]
        exact subsingleton_empty
      · simp only [hw, ↓reduceIte] at hg ⊢
        split
        · exact P.values_subsingleton w hg
        · rename_i c hgw
          rw [hgw] at hg
          cases hg
        · rename_i l r hgw
          rw [hgw] at hg
          cases hg
    scope_union := fun w c hg u hu => by
      by_cases hw : w = v₀
      · simp [hw] at hg
      · simp only [hw, ↓reduceIte] at hg
        exact P.scope_union w c hg u hu
    rank_union := fun w c hg u hu => by
      by_cases hw : w = v₀
      · simp [hw] at hg
      · simp only [hw, ↓reduceIte] at hg
        exact P.rank_union w c hg u hu
    values_union := fun w c hg x => by
      by_cases hw : w = v₀
      · simp [hw] at hg
      · simp only [hw, ↓reduceIte] at hg
        rw [eraseValues]
        simp only [hw, ↓reduceIte]
        split
        · rename_i hgw; rw [hg] at hgw; cases hgw
        · rename_i c' hgw
          rw [hg] at hgw
          injection hgw with hc'
          subst hc'
          simp only [mem_ofPred_eq]
          exact ⟨fun ⟨u, hu, h⟩ => ⟨u, hu, h⟩, fun ⟨u, hu, h⟩ => ⟨u, hu, h⟩⟩
        · rename_i l' r' hgw; rw [hg] at hgw; cases hgw
    scope_product := fun w l r hg => by
      by_cases hw : w = v₀
      · simp [hw] at hg
      · simp only [hw, ↓reduceIte] at hg
        exact P.scope_product w l r hg
    disjoint_product := fun w l r hg => by
      by_cases hw : w = v₀
      · simp [hw] at hg
      · simp only [hw, ↓reduceIte] at hg
        exact P.disjoint_product w l r hg
    rank_product := fun w l r hg => by
      by_cases hw : w = v₀
      · simp [hw] at hg
      · simp only [hw, ↓reduceIte] at hg
        exact P.rank_product w l r hg
    values_product := fun w l r hg x => by
      by_cases hw : w = v₀
      · simp [hw] at hg
      · simp only [hw, ↓reduceIte] at hg
        rw [eraseValues]
        simp only [hw, ↓reduceIte]
        split
        · rename_i hgw; rw [hg] at hgw; cases hgw
        · rename_i c' hgw; rw [hg] at hgw; cases hgw
        · rename_i l' r' hgw
          rw [hg] at hgw
          injection hgw with hll hrr
          subst hll hrr
          rfl }

@[simp] theorem eraseNode_scope (v₀ : N) : (P.eraseNode v₀).scope = P.scope := by rfl
@[simp] theorem eraseNode_root (v₀ : N) : (P.eraseNode v₀).root = P.root := by rfl
@[simp] theorem eraseNode_rank (v₀ : N) : (P.eraseNode v₀).rank = P.rank := by rfl

/-- Deleting a node does not increase the number of union edges. -/
theorem unionEdges_eraseNode_le [Fintype N] (v₀ : N) :
    (P.eraseNode v₀).unionEdges ≤ P.unionEdges := by
  classical
  refine Finset.sum_le_sum fun w _ => ?_
  change (match if w = v₀ then Gate.leaf else P.gate w with | .union c => c.card | _ => 0) ≤ _
  by_cases hw : w = v₀
  · simp [hw]
  · simp only [hw, ↓reduceIte]
    exact le_rfl

/-- Deleting a node does not increase the number of products. -/
theorem products_eraseNode_le [Fintype N] (v₀ : N) :
    (P.eraseNode v₀).products ≤ P.products := by
  classical
  refine Finset.sum_le_sum fun w _ => ?_
  change (match if w = v₀ then Gate.leaf else P.gate w with | .product _ _ => 1 | _ => 0) ≤ _
  by_cases hw : w = v₀
  · simp [hw]
  · simp only [hw, ↓reduceIte]
    exact le_rfl

/-- Deleting a node does not increase `size`. -/
theorem size_eraseNode_le [Fintype N] (v₀ : N) :
    (P.eraseNode v₀).size ≤ P.size :=
  Nat.add_le_add (P.unionEdges_eraseNode_le v₀) (P.products_eraseNode_le v₀)

/-! ### Top-down sub-certificates -/

/-- Node `v` occurs in an accepting sub-certificate for `x` rooted at `w`. -/
private inductive OccursFrom (x : ι → U) : N → N → Prop
  | refl {w : N} : x ∈ P.accepts w → OccursFrom x w w
  | union {w u v : N} {c : Finset N} :
      P.gate w = .union c → u ∈ c → OccursFrom x u v → OccursFrom x w v
  | left {w l r v : N} :
      P.gate w = .product l r → x ∈ P.accepts r → OccursFrom x l v → OccursFrom x w v
  | right {w l r v : N} :
      P.gate w = .product l r → x ∈ P.accepts l → OccursFrom x r v → OccursFrom x w v

variable {P}

private theorem OccursFrom.accepts_left {x : ι → U} {w v : N} (h : P.OccursFrom x w v) :
    x ∈ P.accepts w := by
  induction h with
  | refl hx => exact hx
  | @union w u _ c hg hu _ ih => exact (P.values_union w c hg x).mpr ⟨u, hu, ih⟩
  | @left w l r _ hg hr _ ih => exact (P.values_product w l r hg x).mpr ⟨ih, hr⟩
  | @right w l r _ hg hl _ ih => exact (P.values_product w l r hg x).mpr ⟨hl, ih⟩

private theorem OccursFrom.trans {x : ι → U} {w₁ w₂ w₃ : N} (h₁ : P.OccursFrom x w₁ w₂)
    (h₂ : P.OccursFrom x w₂ w₃) : P.OccursFrom x w₁ w₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | union hg hu _ ih => exact .union hg hu (ih h₂)
  | left hg hr _ ih => exact .left hg hr (ih h₂)
  | right hg hl _ ih => exact .right hg hl (ih h₂)

private theorem OccursFrom.to_occurs {x : ι → U} {w v : N} (hw : P.Occurs x w)
    (h : P.OccursFrom x w v) : P.Occurs x v := by
  induction h with
  | refl _ => exact hw
  | union hg hu huv ih => exact ih (.union hw hg hu huv.accepts_left)
  | left hg _ _ ih => exact ih (.left hw hg)
  | right hg _ _ ih => exact ih (.right hw hg)

private theorem Occurs.to_occursFrom {x : ι → U} {v : N} (h : P.Occurs x v) :
    P.OccursFrom x P.root v := by
  induction h with
  | root hx => exact .refl hx
  | union _ hg hu hxu ih => exact ih.trans (.union hg hu (.refl hxu))
  | @left w l r hw hg ih =>
    have hp := (P.values_product w l r hg x).mp hw.accepts
    exact ih.trans (.left hg hp.2 (.refl hp.1))
  | @right w l r hw hg ih =>
    have hp := (P.values_product w l r hg x).mp hw.accepts
    exact ih.trans (.right hg hp.1 (.refl hp.2))

private theorem occursFrom_root_iff {x : ι → U} {v : N} :
    P.OccursFrom x P.root v ↔ P.Occurs x v :=
  ⟨fun h => h.to_occurs (.root h.accepts_left), Occurs.to_occursFrom⟩

/-- Under `DisjointUnions`, a node `w` in `P.eraseNode v₀` accepts `x` iff `w` accepts `x` in `P`
and `v₀` does not occur in the accepting sub-certificate of `x` rooted at `w`. -/
private theorem accepts_eraseNode_iff (hP : P.DisjointUnions) (v₀ w : N) (x : ι → U) :
    x ∈ (P.eraseNode v₀).accepts w ↔ x ∈ P.accepts w ∧ ¬ P.OccursFrom x w v₀ := by
  classical
  induction hn : P.rank w using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    subst hn
    by_cases hw : w = v₀
    · subst hw
      have h0 : x ∉ (P.eraseNode w).accepts w := by
        change (P.scope w).domRestrict x ∈ P.eraseValues w w → False
        unfold eraseValues
        simp
      exact ⟨fun h => False.elim (h0 h), fun ⟨hx, hocc⟩ => False.elim (hocc (.refl hx))⟩
    · cases hg : P.gate w with
      | leaf =>
        have hval : (P.eraseNode v₀).accepts w = P.accepts w := by
          ext y
          change (P.scope w).domRestrict y ∈ P.eraseValues v₀ w ↔ _
          rw [eraseValues]
          simp only [hw, ↓reduceIte]
          split <;> first | rfl | (rename_i hgw; rw [hg] at hgw; cases hgw)
        rw [hval]
        refine ⟨fun hx => ⟨hx, fun hocc => ?_⟩, fun h => h.1⟩
        cases hocc with
        | refl => exact hw rfl
        | union hg' | left hg' | right hg' => rw [hg] at hg'; cases hg'
      | union c =>
        have hgate : (P.eraseNode v₀).gate w = .union c := by simp [eraseNode, hw, hg]
        have hlhs : x ∈ (P.eraseNode v₀).accepts w ↔
            ∃ u ∈ c, x ∈ P.accepts u ∧ ¬ P.OccursFrom x u v₀ :=
          ((P.eraseNode v₀).values_union w c hgate x).trans (exists_congr fun u =>
            and_congr_right fun hu => ih _ (P.rank_union w c hg u hu) u rfl)
        rw [hlhs, show x ∈ P.accepts w ↔ ∃ u ∈ c, x ∈ P.accepts u from P.values_union w c hg x]
        constructor
        · rintro ⟨u, hu, hxu, hnu⟩
          refine ⟨⟨u, hu, hxu⟩, fun hocc => ?_⟩
          cases hocc with
          | refl => exact hw rfl
          | @union _ u' _ c' hg' hu' hu'v₀ =>
            obtain rfl := Gate.union.inj (hg.symm.trans hg')
            rcases eq_or_ne u u' with rfl | huu'
            exacts [hnu hu'v₀, (hP w c hg u hu u' hu' huu').le_bot ⟨hxu, hu'v₀.accepts_left⟩]
          | left hg' | right hg' => rw [hg] at hg'; cases hg'
        · rintro ⟨⟨u, hu, hxu⟩, hnw⟩
          exact ⟨u, hu, hxu, fun huv₀ => hnw (.union hg hu huv₀)⟩
      | product l r =>
        have hgate : (P.eraseNode v₀).gate w = .product l r := by simp [eraseNode, hw, hg]
        have hrk := P.rank_product w l r hg
        have hlhs : x ∈ (P.eraseNode v₀).accepts w ↔
            (x ∈ P.accepts l ∧ ¬ P.OccursFrom x l v₀) ∧
              (x ∈ P.accepts r ∧ ¬ P.OccursFrom x r v₀) :=
          ((P.eraseNode v₀).values_product w l r hgate x).trans
            (and_congr (ih _ hrk.1 l rfl) (ih _ hrk.2 r rfl))
        rw [hlhs, show x ∈ P.accepts w ↔ x ∈ P.accepts l ∧ x ∈ P.accepts r from
          P.values_product w l r hg x]
        constructor
        · rintro ⟨⟨hxl, hnl⟩, ⟨hxr, hnr⟩⟩
          refine ⟨⟨hxl, hxr⟩, fun hocc => ?_⟩
          cases hocc with
          | refl => exact hw rfl
          | union hg' => rw [hg] at hg'; cases hg'
          | left hg' _ hlv₀ =>
            obtain ⟨rfl, -⟩ := Gate.product.inj (hg.symm.trans hg')
            exact hnl hlv₀
          | right hg' _ hrv₀ =>
            obtain ⟨-, rfl⟩ := Gate.product.inj (hg.symm.trans hg')
            exact hnr hrv₀
        · rintro ⟨⟨hxl, hxr⟩, hnw⟩
          exact ⟨⟨hxl, fun hlv₀ => hnw (.left hg hxr hlv₀)⟩,
            ⟨hxr, fun hrv₀ => hnw (.right hg hxl hrv₀)⟩⟩

/-- Deleting a node preserves `DisjointUnions`. -/
theorem DisjointUnions.eraseNode (hP : P.DisjointUnions) (v₀ : N) :
    (P.eraseNode v₀).DisjointUnions := by
  classical
  intro w c hgate u₁ hu₁ u₂ hu₂ hne
  by_cases hw : w = v₀
  · change (if w = v₀ then Gate.leaf else P.gate w) = .union c at hgate
    simp [hw] at hgate
  · change (if w = v₀ then Gate.leaf else P.gate w) = .union c at hgate
    simp only [hw, ↓reduceIte] at hgate
    exact (hP w c hgate u₁ hu₁ u₂ hu₂ hne).mono
      (fun x hx => (accepts_eraseNode_iff hP v₀ u₁ x).mp hx |>.1)
      (fun x hx => (accepts_eraseNode_iff hP v₀ u₂ x).mp hx |>.1)

/-- **Exact rectangle deletion.** In a smooth decomposable DAG with disjoint unions, replacing a
node `v₀` by an empty leaf removes *precisely* the inputs for which `v₀` occurs. -/
theorem accepted_eraseNode (hP : P.DisjointUnions) (v₀ : N) :
    (P.eraseNode v₀).accepted = P.accepted \ {x | P.Occurs x v₀} := by
  ext x
  change x ∈ (P.eraseNode v₀).accepts P.root ↔ x ∈ P.accepts P.root ∧ ¬ P.Occurs x v₀
  rw [accepts_eraseNode_iff hP v₀ P.root x, occursFrom_root_iff]

end Erase

/-! ### McGuire peeling -/

section Peeling

variable [Finite ι] [Finite U] [Fintype N] (P : DecomposableDAG ι U N)

/-- **Peeling for deterministic decomposable DAGs.** Let `S` have bias at most `b ≥ 0` on
rectangles with both sides of size at least `K`. For any smooth decomposable DAG `P` with disjoint
unions, the accepted inputs in `S` and those outside `S` differ in number by at most

`2 b |accepted| + (K - 1) ^ 2 · #(union edges) + (K - 1) ^ 3 · #(products) + (K - 1)`.

The final `+(K - 1)` term accounts for the base case where fewer than `K` accepted inputs remain
(such as a single leaf DAG with `unionEdges = products = 0`). -/
theorem abs_signedCount_accepted_le (hP : P.DisjointUnions) {S : Set (ι → U)} {K : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hS : RectangleBias S K b) :
    |signedCount S P.accepted| ≤ 2 * b * P.accepted.ncard +
      (((K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products + (K - 1) : ℕ) : ℝ) := by
  induction hn : P.accepted.ncard using Nat.strong_induction_on generalizing P with
  | ind n ih =>
    subst hn
    by_cases hthick : ∃ v : N, (∃ x, P.Occurs x v) ∧
        K ≤ (P.values v).ncard ∧ K ≤ (P.contexts v).ncard
    · obtain ⟨v, ⟨x₀, hx₀⟩, hA, hB⟩ := hthick
      set R : Set (ι → U) := {x | P.Occurs x v}
      have hR : R ⊆ P.accepted := fun _ hx => hx.mem_accepted_self
      have hpos : 0 < R.ncard := (ncard_pos (toFinite R)).mpr ⟨x₀, hx₀⟩
      have hacc : (P.eraseNode v).accepted = P.accepted \ R := accepted_eraseNode hP v
      have hcard := ncard_sdiff_add_ncard_of_subset hR
      have hrest := ih _ (by rw [hacc]; omega) (P.eraseNode v) (hP.eraseNode v) rfl
      rw [hacc] at hrest
      have hrect : |signedCount S R| ≤ 2 * b * R.ncard := by
        rw [show R = rectangle (P.scope v) (P.values v) (P.contexts v) from P.occurs_eq_rectangle v]
        exact hS.abs_signedCount_rectangle_le hA hB
      have hsize : (((K - 1) ^ 2 * (P.eraseNode v).unionEdges +
          (K - 1) ^ 3 * (P.eraseNode v).products + (K - 1) : ℕ) : ℝ) ≤
          (((K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products + (K - 1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right
          (Nat.add_le_add (Nat.mul_le_mul_left _ (P.unionEdges_eraseNode_le v))
            (Nat.mul_le_mul_left _ (P.products_eraseNode_le v))) _
      have hcardR : ((P.accepted \ R).ncard : ℝ) + R.ncard = P.accepted.ncard := by
        exact_mod_cast hcard
      rw [signedCount_eq_add_sdiff S hR]
      calc |signedCount S R + signedCount S (P.accepted \ R)|
          ≤ |signedCount S R| + |signedCount S (P.accepted \ R)| := abs_add_le _ _
        _ ≤ 2 * b * P.accepted.ncard +
              (((K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products + (K - 1) : ℕ) : ℝ) := by
            rw [← hcardR]
            linarith
    · push Not at hthick
      have hrem : P.accepted.ncard ≤
          (K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products + (K - 1) := by
        rcases Nat.eq_zero_or_pos K with rfl | hKpos
        · have hemp : P.accepted = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => by
            have := hthick P.root ⟨x, .root hx⟩ (Nat.zero_le _)
            omega
          simp [hemp]
        · have hsmall : P.SmallSides K := fun v => by
            by_cases hex : ∃ x, P.Occurs x v
            · by_cases hA : K ≤ (P.values v).ncard
              · exact Or.inr (encard_lt_coe_iff_finite_ncard_lt.mpr
                  ⟨toFinite _, hthick v hex hA⟩)
              · exact Or.inl (encard_lt_coe_iff_finite_ncard_lt.mpr
                  ⟨toFinite _, not_le.mp hA⟩)
            · have hctx : P.contexts v = ∅ := by
                ext c
                simp only [contexts, mem_image, mem_ofPred_eq, mem_empty_iff_false, iff_false]
                rintro ⟨x, hx, -⟩
                exact hex ⟨x, hx⟩
              exact Or.inr (by simp [hctx, hKpos])
          by_cases hK : K ≤ P.accepted.ncard
          · exact (P.ncard_accepted_le_of_smallSides hsmall hK).trans (Nat.le_add_right _ _)
          · omega
      have hremR : (P.accepted.ncard : ℝ) ≤
          (((K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products + (K - 1) : ℕ) : ℝ) := by
        exact_mod_cast hrem
      linarith [abs_signedCount_le S P.accepted,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * b) (Nat.cast_nonneg (α := ℝ) P.accepted.ncard)]

/-- **Peeling by size.** Under the hypotheses of `abs_signedCount_accepted_le`,
`|signedCount S accepted| ≤ 2 b |accepted| + (K - 1) ^ 3 · size + (K - 1)`. -/
theorem abs_signedCount_accepted_le_size (hP : P.DisjointUnions) {S : Set (ι → U)} {K : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hS : RectangleBias S K b) :
    |signedCount S P.accepted| ≤
      2 * b * P.accepted.ncard + (((K - 1) ^ 3 * P.size + (K - 1) : ℕ) : ℝ) := by
  have hpow : (K - 1) ^ 2 ≤ (K - 1) ^ 3 := by
    rcases Nat.eq_zero_or_pos (K - 1) with h | h
    · simp [h]
    · exact Nat.pow_le_pow_right h (by omega)
  have hsize : (K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products + (K - 1) ≤
      (K - 1) ^ 3 * P.size + (K - 1) := by
    rw [size, mul_add]
    gcongr
  have hsizeR : (((K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products + (K - 1) : ℕ) : ℝ) ≤
      (((K - 1) ^ 3 * P.size + (K - 1) : ℕ) : ℝ) := by exact_mod_cast hsize
  linarith [P.abs_signedCount_accepted_le hP hb hS]

end Peeling

end Cslib.Circuits.DecomposableDAG
