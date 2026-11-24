/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.DisjointUnion
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Sym.Card

/-!
# Worst-case comparison complexity over labeled multigraphs

The topology-dependent optimum is maximized over the finite type of all endpoint assignments
on exactly `m` edges and `n` vertices. This is the labeled multigraph model, including repeated
edges, loops, and isolated vertices. The maximum of an empty topology class is zero.
-/

public section

namespace Cslib.Multigraph.OptimalTree

open scoped Sym2

variable {m n k v : ℕ}

/-- Worst-case optimal MSF comparison budget on exactly `m` labeled edges and `n` vertices. -/
noncomputable def worstCase (m n : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup (fun L : Fin m → Sym2 (Fin n) => optimalMSFComparisons L)

/-- Every realized topology is bounded by the maximum at its two sizes. -/
theorem optimalMSFComparisons_le_worstCase (L : Fin m → Sym2 (Fin n)) :
    optimalMSFComparisons L ≤ worstCase m n := by
  classical
  exact Finset.le_sup (f := optimalMSFComparisons) (Finset.mem_univ L)

private theorem worstCase_le {d : ℕ}
    (bound : ∀ L : Fin m → Sym2 (Fin n), optimalMSFComparisons L ≤ d) : worstCase m n ≤ d := by
  classical
  exact Finset.sup_le fun L _ => bound L

/-- If a topology of these sizes exists, one such topology attains the worst-case budget. -/
theorem exists_worstCase (h : Nonempty (Fin m → Sym2 (Fin n))) :
    ∃ L : Fin m → Sym2 (Fin n), worstCase m n = optimalMSFComparisons L := by
  classical
  obtain ⟨x⟩ := h
  obtain ⟨L, _, eq⟩ := Finset.exists_mem_eq_sup Finset.univ
    ⟨x, Finset.mem_univ _⟩ optimalMSFComparisons
  exact ⟨L, eq⟩

private theorem worstCase_of_noTopology (h : ¬Nonempty (Fin m → Sym2 (Fin n))) :
    worstCase m n = 0 := Nat.eq_zero_of_le_zero (worstCase_le fun L => False.elim (h ⟨L⟩))

private theorem optimal_noEdges (L : Fin 0 → Sym2 (Fin n)) : optimalMSFComparisons L = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply optimalMSFComparisons_le L (.pure ∅) 0
  intro w _
  exact ⟨Subsingleton.elim _ _, le_rfl⟩

private def padEdges (L : Fin m → Sym2 (Fin n)) (k : ℕ) (a : Fin n) :
    Fin (m + k) → Sym2 (Fin n) :=
  Sum.elim L (fun _ : Fin k => s(a,a)) ∘ finSumFinEquiv.symm

private theorem forestsSplit_padEdges (L : Fin m → Sym2 (Fin n)) (k : ℕ) (a : Fin n) :
    ForestsSplit L (fun _ : Fin k => s(a,a)) (padEdges L k a) finSumFinEquiv := by
  intro W inst w _
  let e : (Fin m ⊕ Fin k) ≃ Fin (m + k) := finSumFinEquiv
  have left (x : Fin m) : padEdges L k a (e (.inl x)) = (L x).map id := by
    simp [e, padEdges]
  have right (y : Fin k) : padEdges L k a (e (.inr y)) = s(a,a) := by
    simp [e, padEdges]
  ext f
  rw [Finset.mem_map_equiv]
  cases f with
  | inl x =>
    rw [Finset.inl_mem_disjSum]
    have proj (_ : Fin n) : ∃ p, Function.LeftInverse p id ∧ ∀ f,
        (∃ z, (e ∘ Sum.inl) z = f) ∨ ((padEdges L k a f).map p).IsDiag := by
      refine ⟨id, fun _ => rfl, ?_⟩
      intro f
      obtain ⟨z, rfl⟩ := e.surjective f
      cases z with
      | inl x => exact Or.inl ⟨x, rfl⟩
      | inr y => exact Or.inr (by rw [right, Sym2.map_mk, Sym2.mk_isDiag_iff])
    have h := mem_msf_of_component_retraction L (padEdges L k a) (e ∘ Sum.inl) id left proj
      (w ∘ e.symm) x
    simpa [e, Function.comp_def] using h
  | inr y =>
    rw [Finset.inr_mem_disjSum]
    apply iff_of_false
    · apply notMem_msf_of_isDiag
      change (padEdges L k a (e (.inr y))).IsDiag
      rw [right, Sym2.mk_isDiag_iff]
    · exact notMem_msf_of_isDiag _ (Sym2.mk_isDiag_iff.mpr rfl)

/-- Enlarging either size cannot decrease the worst-case comparison budget. Edge padding adds
loops at an existing vertex, and vertex padding adds isolated vertices. -/
theorem worstCase_mono (hm : m ≤ k) (hn : n ≤ v) : worstCase m n ≤ worstCase k v := by
  apply worstCase_le
  intro L
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  by_cases h : 0 < n
  · let a : Fin n := ⟨0, h⟩
    have hpad := optimalMSFComparisons_eq_add_of_forestsSplit _ _ _ _
      (forestsSplit_padEdges L d a)
    let empty : Fin 0 → Sym2 (Fin b) := Fin.elim0
    have hv := optimalMSFComparisons_disjointTopology (padEdges L d a) empty
    have cap := optimalMSFComparisons_le_worstCase (disjointTopology (padEdges L d a) empty)
    change _ ≤ worstCase (m + d) (n + b) at cap
    omega
  · have hn : n = 0 := by omega
    subst n
    cases m with
    | zero => rw [optimal_noEdges]; exact Nat.zero_le _
    | succ m =>
      obtain ⟨a,b,ha⟩ : ∃ a b, L 0 = s(a,b) := by
        induction L 0 using Sym2.ind with | _ a b => exact ⟨a,b,rfl⟩
      exact Fin.elim0 a

/-- Worst-case comparison complexity is superadditive in the two graph sizes taken together.
For inhabited size classes, this follows by taking the disjoint union of two maximizers. -/
theorem worstCase_add (m n k v : ℕ) :
    worstCase m n + worstCase k v ≤ worstCase (m+k) (n+v) := by
  classical
  by_cases hl : Nonempty (Fin m → Sym2 (Fin n))
  · by_cases hr : Nonempty (Fin k → Sym2 (Fin v))
    · obtain ⟨L,hL⟩ := exists_worstCase hl
      obtain ⟨R,hR⟩ := exists_worstCase hr
      rw [hL,hR, ← optimalMSFComparisons_disjointTopology]
      exact optimalMSFComparisons_le_worstCase _
    · rw [worstCase_of_noTopology hr, Nat.add_zero]
      exact worstCase_mono (by omega) (by omega)
  · rw [worstCase_of_noTopology hl, Nat.zero_add]
    exact worstCase_mono (by omega) (by omega)

/-- Doubling property used in [PettieRamachandran2002], Corollary 5.7, in the labeled
multigraph model. -/
theorem twice_worstCase_le (m n : ℕ) : 2 * worstCase m n ≤ worstCase (2*m) (2*n) := by
  simpa only [two_mul] using worstCase_add m n m n

end Cslib.Multigraph.OptimalTree
