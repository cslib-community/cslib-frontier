/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Decomposable.Peeling
import Mathlib.Tactic.FinCases

/-!
# Checked clients and sharpness witnesses for `Decomposable.Peeling`

1. **Sharpness of `+(K - 1)` on a single-leaf d-DNNF** (`singleLeafDAG`): on `Fin 1 → Bool`, every
   `2 × 2` rectangle is impossible, so `S = {fun _ => true}` satisfies `RectangleBias S 2 0`, while
   a single leaf accepts `S` with `unionEdges = products = 0` and `|signedCount S accepted| = 1`,
   attaining `2 * 0 * 1 + (0 + 0 + (2 - 1)) = 1` with equality.
2. **Shared-node deletion (`eraseNode`) on a diamond d-DNNF** (`sharedDAG` on `Fin 8`): a
   deterministic DAG on `Fin 2 → Bool` where two product branches (`5` and `6`) share a common
   union node (`4`) on coordinate `1`. Deleting branch `5` removes `{x | x 0 = false}` while
   keeping `{x | x 0 = true}` intact.
-/

public section

open Set Cslib.Circuits Cslib.Circuits.Frontier

namespace CslibFrontierTests.DecomposablePeeling

/-! ### 1. Sharpness of the `+(K - 1)` leaf term -/

/-- Single-leaf d-DNNF on `Fin 1 → Bool` accepting `{fun _ => true}` with zero union edges and
zero product nodes. -/
def singleLeafDAG : DecomposableDAG (Fin 1) Bool Unit where
  scope _ := univ
  root := ()
  scope_root := rfl
  gate _ := .leaf
  rank _ := 0
  values _ := {fun _ => true}
  values_subsingleton _ _ := subsingleton_singleton
  scope_union _ _ hg := by cases hg
  rank_union _ _ hg := by cases hg
  values_union _ _ hg := by cases hg
  scope_product _ _ _ hg := by cases hg
  disjoint_product _ _ _ hg := by cases hg
  rank_product _ _ _ hg := by cases hg
  values_product _ _ _ hg := by cases hg

private theorem singleLeafDAG_disjointUnions : singleLeafDAG.DisjointUnions := by
  intro _ _ hg
  cases hg

/-- On `Fin 1 → Bool`, no cut has both sides of size at least `2`, so *every* set has bias `0` at
threshold `K = 2`. -/
private theorem rectangleBias_two_zero_fin1 (S : Set (Fin 1 → Bool)) :
    RectangleBias S 2 0 := by
  intro X A B hA hB
  by_cases h0 : (0 : Fin 1) ∈ X
  · have hXc : Xᶜ = ∅ := eq_empty_iff_forall_notMem.mpr fun i hi =>
      hi (Subsingleton.elim i 0 ▸ h0)
    have hcard : (univ : Set (↥Xᶜ → Bool)).ncard = 1 := by
      rw [Set.ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hXc, ncard_empty, pow_zero]
    have hle : B.ncard ≤ (univ : Set (↥Xᶜ → Bool)).ncard :=
      ncard_le_ncard (subset_univ B) (toFinite _)
    omega
  · have hX : X = ∅ := eq_empty_iff_forall_notMem.mpr fun i hi =>
      h0 (Subsingleton.elim i 0 ▸ hi)
    have hcard : (univ : Set (X → Bool)).ncard = 1 := by
      rw [Set.ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hX, ncard_empty, pow_zero]
    have hle : A.ncard ≤ (univ : Set (X → Bool)).ncard :=
      ncard_le_ncard (subset_univ A) (toFinite _)
    omega

/-- Peeling applied to `singleLeafDAG` with `K = 2` and `b = 0` yields `|signedCount| ≤ 1`,
exercising the `+(K - 1)` term where `unionEdges = products = 0`. -/
theorem abs_signedCount_singleLeafDAG_le_one :
    |signedCount singleLeafDAG.accepted singleLeafDAG.accepted| ≤ 1 := by
  have h := singleLeafDAG.abs_signedCount_accepted_le singleLeafDAG_disjointUnions
    le_rfl (rectangleBias_two_zero_fin1 singleLeafDAG.accepted)
  have hu : singleLeafDAG.unionEdges = 0 := rfl
  have hp : singleLeafDAG.products = 0 := rfl
  rw [hu, hp] at h
  norm_num at h
  exact h

/-! ### 2. Shared-node deterministic DAG (`sharedDAG`) on `Fin 8` -/

-- Nodes `0..3` are literal leaves (`x₀=F, x₀=T, x₁=F, x₁=T`), `4` is the shared union on `{1}`,
-- `5 = product 0 4`, `6 = product 1 4`, and `7 = union {5, 6}` is the root.
private def dScope (v : Fin 8) : Set (Fin 2) :=
  if v.val < 2 then {0} else if v.val < 5 then {1} else univ

private def dGate : Fin 8 → DecomposableDAG.Gate (Fin 8)
  | 0 => .leaf
  | 1 => .leaf
  | 2 => .leaf
  | 3 => .leaf
  | 4 => .union {2, 3}
  | 5 => .product 0 4
  | 6 => .product 1 4
  | 7 => .union {5, 6}

private def dRank (v : Fin 8) : ℕ :=
  if v.val < 4 then 0 else if v.val = 4 then 1 else if v.val < 7 then 2 else 3

private def dValues : (v : Fin 8) → Set (dScope v → Bool)
  | 0 => {fun _ => false}
  | 1 => {fun _ => true}
  | 2 => {fun _ => false}
  | 3 => {fun _ => true}
  | 4 => univ
  | 5 => {a | a ⟨0, mem_univ 0⟩ = false}
  | 6 => {a | a ⟨0, mem_univ 0⟩ = true}
  | 7 => univ

/-- 8-node diamond d-DNNF on `Fin 2 → Bool` where product branches `5` and `6` share union node
`4`. -/
def sharedDAG : DecomposableDAG (Fin 2) Bool (Fin 8) where
  scope := dScope
  root := 7
  scope_root := rfl
  gate := dGate
  rank := dRank
  values := dValues
  values_subsingleton v hg := by
    fin_cases v <;> simp only [dGate, reduceCtorEq] at hg
    all_goals exact subsingleton_singleton
  scope_union v c hg u hu := by
    fin_cases v <;> simp only [dGate, reduceCtorEq] at hg
    · injection hg with hc
      subst hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> rfl
    · injection hg with hc
      subst hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> rfl
  rank_union v c hg u hu := by
    fin_cases v <;> simp only [dGate, reduceCtorEq] at hg
    · injection hg with hc
      subst hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> decide
    · injection hg with hc
      subst hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> decide
  values_union v c hg x := by
    fin_cases v <;> simp only [dGate, reduceCtorEq] at hg
    · injection hg with hc
      subst hc
      simp only [dValues, mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
      cases hx1 : x 1
      · refine ⟨2, Or.inl rfl, ?_⟩
        simp only [mem_singleton_iff]
        funext ⟨i, hi⟩
        change x i = false
        rw [mem_singleton_iff.mp hi]
        exact hx1
      · refine ⟨3, Or.inr rfl, ?_⟩
        simp only [mem_singleton_iff]
        funext ⟨i, hi⟩
        change x i = true
        rw [mem_singleton_iff.mp hi]
        exact hx1
    · injection hg with hc
      subst hc
      simp only [dValues, mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
      cases hx0 : x 0
      · exact ⟨5, Or.inl rfl, hx0⟩
      · exact ⟨6, Or.inr rfl, hx0⟩
  scope_product v l r hg := by
    fin_cases v <;> simp only [dGate, reduceCtorEq] at hg
    · injection hg with hl hr
      subst hl hr
      ext i; fin_cases i <;> simp [dScope]
    · injection hg with hl hr
      subst hl hr
      ext i; fin_cases i <;> simp [dScope]
  disjoint_product v l r hg := by
    fin_cases v <;> simp only [dGate, reduceCtorEq] at hg
    · injection hg with hl hr; subst hl hr; simp [dScope]
    · injection hg with hl hr; subst hl hr; simp [dScope]
  rank_product v l r hg := by
    fin_cases v <;> simp only [dGate, reduceCtorEq] at hg
    · injection hg with hl hr; subst hl hr; decide
    · injection hg with hl hr; subst hl hr; decide
  values_product v l r hg x := by
    fin_cases v <;> simp only [dGate, reduceCtorEq] at hg
    · injection hg with hl hr
      subst hl hr
      simp only [dValues, mem_singleton_iff, mem_univ, and_true]
      exact ⟨fun h => funext fun ⟨i, hi⟩ => mem_singleton_iff.mp hi ▸ h,
        fun h => congrFun h ⟨0, mem_singleton 0⟩⟩
    · injection hg with hl hr
      subst hl hr
      simp only [dValues, mem_singleton_iff, mem_univ, and_true]
      exact ⟨fun h => funext fun ⟨i, hi⟩ => mem_singleton_iff.mp hi ▸ h,
        fun h => congrFun h ⟨0, mem_singleton 0⟩⟩

private theorem sharedDAG_disjointUnions : sharedDAG.DisjointUnions := by
  intro v c hg u₁ hu₁ u₂ hu₂ hne
  fin_cases v <;> simp only [sharedDAG, dGate, reduceCtorEq] at hg
  · injection hg with hc
    subst hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu₁ hu₂
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    rcases hu₁ with rfl | rfl <;> rcases hu₂ with rfl | rfl
    · exact hne rfl
    · have h1 : x 1 = false := congrFun hx₁ ⟨1, mem_singleton 1⟩
      have h2 : x 1 = true := congrFun hx₂ ⟨1, mem_singleton 1⟩
      rw [h1] at h2; cases h2
    · have h1 : x 1 = true := congrFun hx₁ ⟨1, mem_singleton 1⟩
      have h2 : x 1 = false := congrFun hx₂ ⟨1, mem_singleton 1⟩
      rw [h1] at h2; cases h2
    · exact hne rfl
  · injection hg with hc
    subst hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu₁ hu₂
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    rcases hu₁ with rfl | rfl <;> rcases hu₂ with rfl | rfl
    · exact hne rfl
    · change x 0 = false at hx₁
      change x 0 = true at hx₂
      rw [hx₁] at hx₂; cases hx₂
    · change x 0 = true at hx₁
      change x 0 = false at hx₂
      rw [hx₁] at hx₂; cases hx₂
    · exact hne rfl

/-- Deleting branch `5` (`x₀ = false`) removes `{x | x 0 = false}` while preserving
`{x | x 0 = true}`, despite branches `5` and `6` sharing union node `4`. -/
theorem accepted_eraseNode_branch5 :
    (sharedDAG.eraseNode 5).accepted = {x : Fin 2 → Bool | x 0 = true} := by
  rw [sharedDAG.accepted_eraseNode sharedDAG_disjointUnions 5]
  ext x
  simp only [mem_sdiff, mem_ofPred_eq]
  have hroot_acc : x ∈ sharedDAG.accepted := trivial
  constructor
  · rintro ⟨-, hnocc⟩
    cases hx0 : x 0
    · exfalso
      exact hnocc (.union (.root hroot_acc) rfl (by simp) hx0)
    · rfl
  · intro hx0
    refine ⟨hroot_acc, fun hocc => ?_⟩
    have hxF : x ∈ sharedDAG.accepts 5 := hocc.accepts
    change x 0 = false at hxF
    rw [hx0] at hxF
    cases hxF

end CslibFrontierTests.DecomposablePeeling
