/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.DirectSum
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The optimal comparison budget on a disjoint union

The disjoint union is a concrete instance of the forest decomposition in
[PettieRamachandran2002], Property 5.3. Projection of a walk onto either component sends each
edge from the other component to a loop. Consequently each component retains exactly its own
minimum spanning forest edges. This construction gives the size-doubling example used in
Corollary 5.7.
-/

public section

namespace Cslib.Multigraph.OptimalTree

open scoped Sym2

variable {E E' V V' : Type} {m n k v : ℕ}

/-- Restriction to a component commutes with the MSF if walks can be projected back to it
while sending every outside edge to a loop. The projection may depend on a vertex of the
component, so the statement also covers empty vertex types. -/
theorem mem_msf_of_component_retraction [Fintype E] [Fintype E']
    {W : Type*} [LinearOrder W] (L : E → Sym2 V) (G : E' → Sym2 V') (j : E → E') (i : V → V')
    (inc : ∀ f, G (j f) = (L f).map i)
    (proj : ∀ _ : V, ∃ r : V' → V, Function.LeftInverse r i ∧
      ∀ f, (∃ x, j x = f) ∨ ((G f).map r).IsDiag)
    (w : E' → W) (e : E) : j e ∈ msf G w Finset.univ ↔ e ∈ msf L (w ∘ j) Finset.univ := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, L e = s(a,b) := by
    induction L e using Sym2.ind with | _ a b => exact ⟨a, b, rfl⟩
  obtain ⟨r, left, project⟩ := proj a
  have hab' : G (j e) = s(i a, i b) := by rw [inc, hab]; rfl
  rw [mem_msf_iff w hab', mem_msf_iff (w ∘ j) hab]
  simp only [Finset.mem_univ, true_and]
  apply not_congr
  constructor
  · intro connected
    have projected := Joins.lift (ends' := L) (T := {f | w (j f) < w (j e)}) r
      (fun f hf c d hcd => by
        rcases project f with ⟨x, rfl⟩ | loop
        · apply Joins.of_mem (e := x) hf
          calc
            L x = ((L x).map i).map r := by
              rw [Sym2.map_map, left.comp_eq_id, Sym2.map_id, id_eq]
            _ = s(r c, r d) := by rw [← inc, hcd]; rfl
        · rw [hcd, Sym2.map_mk, Sym2.mk_isDiag_iff] at loop
          rw [loop]) connected
    simpa only [Function.comp_apply, left _] using projected
  · exact Joins.lift i fun f hf c d hcd =>
      Joins.of_mem (e := j f) hf (by rw [inc, hcd]; rfl)

/-- Disjoint union with dense edge and vertex labels. The original labels are recovered by
`finSumFinEquiv.symm` in each sort. -/
@[expose] def disjointTopology (L : Fin m → Sym2 (Fin n)) (R : Fin k → Sym2 (Fin v)) :
    Fin (m+k) → Sym2 (Fin (n+v)) := fun f =>
  match finSumFinEquiv.symm f with
  | .inl e => (L e).map (fun a => finSumFinEquiv (.inl a : Fin n ⊕ Fin v))
  | .inr e => (R e).map (fun b => finSumFinEquiv (.inr b : Fin n ⊕ Fin v))

/-- The MSF of a disjoint union is the disjoint union of the two MSFs. -/
theorem forestsSplit_disjointTopology (L : Fin m → Sym2 (Fin n)) (R : Fin k → Sym2 (Fin v)) :
    ForestsSplit L R (disjointTopology L R) finSumFinEquiv := by
  intro W inst w _
  let e : (Fin m ⊕ Fin k) ≃ Fin (m+k) := finSumFinEquiv
  let i : (Fin n ⊕ Fin v) ≃ Fin (n+v) := finSumFinEquiv
  have left (x : Fin m) : disjointTopology L R (e (.inl x)) = (L x).map (i ∘ Sum.inl) := by
    simp [disjointTopology, e, i, Function.comp_def]
  have right (y : Fin k) : disjointTopology L R (e (.inr y)) = (R y).map (i ∘ Sum.inr) := by
    simp [disjointTopology, e, i, Function.comp_def]
  ext edge
  rw [Finset.mem_map_equiv]
  cases edge with
  | inl x =>
    rw [Finset.inl_mem_disjSum]
    have proj (a : Fin n) :
        ∃ p, Function.LeftInverse p (i ∘ Sum.inl) ∧ ∀ f,
          (∃ z, (e ∘ Sum.inl) z = f) ∨ ((disjointTopology L R f).map p).IsDiag := by
      let p := Sum.elim id (fun _ : Fin v => a) ∘ i.symm
      refine ⟨p, fun z => by simp [p], ?_⟩
      intro f
      obtain ⟨z, rfl⟩ := e.surjective f
      cases z with
      | inl x => exact Or.inl ⟨x, rfl⟩
      | inr y =>
        right
        rw [right, Sym2.map_map]
        induction R y using Sym2.ind with
        | _ c d => simp [p, Sym2.map_mk]
    have h := mem_msf_of_component_retraction L (disjointTopology L R)
      (e ∘ Sum.inl) (i ∘ Sum.inl) left proj (w ∘ e.symm) x
    simpa [e, Function.comp_def] using h
  | inr y =>
    rw [Finset.inr_mem_disjSum]
    have proj (a : Fin v) :
        ∃ p, Function.LeftInverse p (i ∘ Sum.inr) ∧ ∀ f,
          (∃ z, (e ∘ Sum.inr) z = f) ∨ ((disjointTopology L R f).map p).IsDiag := by
      let p := Sum.elim (fun _ : Fin n => a) id ∘ i.symm
      refine ⟨p, fun z => by simp [p], ?_⟩
      intro f
      obtain ⟨z, rfl⟩ := e.surjective f
      cases z with
      | inr y => exact Or.inl ⟨y, rfl⟩
      | inl x =>
        right
        rw [left, Sym2.map_map]
        induction L x using Sym2.ind with
        | _ c d => simp [p, Sym2.map_mk]
    have h := mem_msf_of_component_retraction R (disjointTopology L R)
      (e ∘ Sum.inr) (i ∘ Sum.inr) right proj (w ∘ e.symm) y
    simpa [e, Function.comp_def] using h

/-- Fixed-topology optimal comparison complexity is additive on disjoint unions. -/
theorem optimalMSFComparisons_disjointTopology (L : Fin m → Sym2 (Fin n))
    (R : Fin k → Sym2 (Fin v)) :
    optimalMSFComparisons (disjointTopology L R) =
      optimalMSFComparisons L + optimalMSFComparisons R :=
  optimalMSFComparisons_eq_add_of_forestsSplit _ _ _ _ (forestsSplit_disjointTopology L R)

end Cslib.Multigraph.OptimalTree
