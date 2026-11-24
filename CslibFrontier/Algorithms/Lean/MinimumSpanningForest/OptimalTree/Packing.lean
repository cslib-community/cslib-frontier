/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.WorstCase

/-!
# Packing independent MSF comparison problems at a common vertex

Identifying one vertex from each nonempty graph preserves its cycles and its minimum spanning
forest for every order of the weights. This construction charges a collection of local problems
to one global optimum using their total number of edges and one plus the sum of their
vertex counts minus one.
-/

public section

namespace Cslib.Multigraph.OptimalTree

open scoped Sym2

variable {m n k v : ℕ}

/-- Inclusion of the left vertex set into a one-vertex union. -/
@[expose] def leftVertex (n v : ℕ) (z : Fin (n + 1)) : Fin ((n + 1) + v) :=
  finSumFinEquiv (.inl z : Fin (n + 1) ⊕ Fin v)

/-- Inclusion of the right vertex set, identifying its zero vertex with the left zero vertex. -/
@[expose] def rightVertex (n v : ℕ) : Fin (v + 1) → Fin ((n + 1) + v) :=
  Fin.cases (leftVertex n v 0) (fun t => finSumFinEquiv (.inr t : Fin (n + 1) ⊕ Fin v))

/-- Join the two graphs along their vertex with label zero. -/
@[expose] def wedgeTopology (L : Fin m → Sym2 (Fin (n + 1))) (R : Fin k → Sym2 (Fin (v + 1))) :
    Fin (m + k) → Sym2 (Fin ((n + 1) + v)) :=
  Sum.elim (fun z => (L z).map (leftVertex n v)) (fun z => (R z).map (rightVertex n v))
    ∘ finSumFinEquiv.symm

/-- The two local forests split for all weight orders, even though the graphs share a vertex. -/
theorem forestsSplit_wedgeTopology (L : Fin m → Sym2 (Fin (n + 1)))
    (R : Fin k → Sym2 (Fin (v + 1))) :
    ForestsSplit L R (wedgeTopology L R) finSumFinEquiv := by
  intro W inst w _
  let e : (Fin m ⊕ Fin k) ≃ Fin (m + k) := finSumFinEquiv
  let i : (Fin (n + 1) ⊕ Fin v) ≃ Fin ((n + 1) + v) := finSumFinEquiv
  let l := leftVertex n v
  let r := rightVertex n v
  let G := wedgeTopology L R
  have left (x : Fin m) : G (e (.inl x)) = (L x).map l := by simp [e, G, wedgeTopology, l]
  have right (x : Fin k) : G (e (.inr x)) = (R x).map r := by simp [e, G, wedgeTopology, r]
  ext z
  rw [Finset.mem_map_equiv]
  cases z with
  | inl x =>
    rw [Finset.inl_mem_disjSum]
    let p := Sum.elim id (fun _ : Fin v => (0 : Fin (n + 1))) ∘ i.symm
    have pl : Function.LeftInverse p l := fun _ => by simp [p, l, i, leftVertex]
    have pr (z : Fin (v + 1)) : p (r z) = 0 := by
      refine Fin.cases ?_ (fun t => ?_) z <;> simp [p, r, i, rightVertex, leftVertex]
    have project (f : Fin (m + k)) : (∃ x, (e ∘ Sum.inl) x = f) ∨ ((G f).map p).IsDiag := by
      obtain ⟨z, rfl⟩ := e.surjective f
      cases z with
      | inl x => exact Or.inl ⟨x, rfl⟩
      | inr y =>
        right
        rw [right, Sym2.map_map]
        induction R y using Sym2.ind with | _ a b => simp [pr]
    have h := mem_msf_of_component_retraction L G (e ∘ Sum.inl) l left
      (fun _ => ⟨p, pl, project⟩) (w ∘ e.symm) x
    simpa [e, G, Function.comp_def] using h
  | inr y =>
    rw [Finset.inr_mem_disjSum]
    let p := Sum.elim (fun _ : Fin (n + 1) => (0 : Fin (v + 1))) Fin.succ ∘ i.symm
    have pl (z : Fin (n + 1)) : p (l z) = 0 := by simp [p, l, i, leftVertex]
    have pr : Function.LeftInverse p r := by
      intro z
      refine Fin.cases ?_ (fun t => ?_) z <;> simp [p, r, i, rightVertex, leftVertex]
    have project (f : Fin (m + k)) : (∃ y, (e ∘ Sum.inr) y = f) ∨ ((G f).map p).IsDiag := by
      obtain ⟨z, rfl⟩ := e.surjective f
      cases z with
      | inr y => exact Or.inl ⟨y, rfl⟩
      | inl x =>
        right
        rw [left, Sym2.map_map]
        induction L x using Sym2.ind with | _ a b => simp [pl]
    have h := mem_msf_of_component_retraction R G (e ∘ Sum.inr) r right
      (fun _ => ⟨p, pr, project⟩) (w ∘ e.symm) y
    simpa [e, G, Function.comp_def] using h

/-- Gluing at an articulation point saves one vertex in the size bound for a direct sum. -/
theorem worstCase_wedge (m n k v : ℕ) :
    worstCase m (n + 1) + worstCase k (v + 1) ≤ worstCase (m + k) (n + v + 1) := by
  obtain ⟨L, hl⟩ := exists_worstCase (m := m) (n := n + 1) ⟨fun _ => s(0,0)⟩
  obtain ⟨R, hr⟩ := exists_worstCase (m := k) (n := v + 1) ⟨fun _ => s(0,0)⟩
  rw [hl, hr, ← optimalMSFComparisons_eq_add_of_forestsSplit _ _ _ _
    (forestsSplit_wedgeTopology L R)]
  exact (optimalMSFComparisons_le_worstCase _).trans (worstCase_mono le_rfl (by omega))

/-- All the local optimal budgets fit a single worst-case budget. Zero-vertex pieces contribute
zero to the count of vertices beyond the shared articulation point. -/
theorem sum_worstCase_le (sizes : List (ℕ × ℕ)) :
    (sizes.map fun s => worstCase s.1 s.2).sum ≤
      worstCase (sizes.map Prod.fst).sum ((sizes.map fun s => s.2 - 1).sum + 1) := by
  induction sizes with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    have h := Nat.add_le_add
      (worstCase_mono (le_refl x.1) (show x.2 ≤ x.2 - 1 + 1 by omega)) ih
    exact h.trans (worstCase_wedge ..)

end Cslib.Multigraph.OptimalTree
