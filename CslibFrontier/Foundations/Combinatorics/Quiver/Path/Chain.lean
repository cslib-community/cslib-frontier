/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.List.IsChainFromTo
public import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Paths as vertex-list chains

For a quiver with at most one arrow between each pair, paths are equivalent to nonempty
vertex-list chains with the same endpoints. This connects the path APIs used for min-isolation
to the vertex lists used by reachability scans in #6747, preserving path identity and length.
-/

public section

namespace Quiver.Path

variable {V : Type*} [Quiver V] {a b : V}

/-- A path's vertices form a chain of inhabited arrows with the same endpoints. -/
theorem vertices_isChainFromTo (p : Path a b) :
    p.vertices.IsChainFromTo (fun u v => Nonempty (u ⟶ v)) a b := by
  induction p with
  | nil => exact List.isChainFromTo_singleton
  | cons p e ih => simpa only [vertices_cons, List.concat_eq_append] using ih.snoc ⟨e⟩

private theorem reverse_vertices (p : Path a b) : p.vertices.reverse = b :: p.toList := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [vertices_cons, List.concat_eq_append, ih]

/-- Without parallel arrows, the vertex list determines a path. -/
theorem vertices_injective [∀ u v : V, Subsingleton (u ⟶ v)] :
    Function.Injective (vertices : Path a b → List V) := by
  intro p q h
  apply toList_injective a b
  have h' := congrArg List.reverse h
  rw [reverse_vertices, reverse_vertices] at h'
  exact List.cons.inj h' |>.2

private theorem exists_vertices {l : List V}
    (h : l.IsChainFromTo (fun u v => Nonempty (u ⟶ v)) a b) :
    ∃ p : Path a b, p.vertices = l := by
  induction h using List.IsChainFromTo.head_induction_on with
  | h_refl => exact ⟨.nil, rfl⟩
  | @h_head a b c l hab hc ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨e⟩ := hab
    exact ⟨e.toPath.comp p, by simp [vertices_comp, hp]⟩

/-- Paths without parallel arrows, represented by vertex lists with checked endpoints. -/
noncomputable def equivChain [∀ u v : V, Subsingleton (u ⟶ v)] (a b : V) :
    Path a b ≃ {l : List V // l.IsChainFromTo (fun u v => Nonempty (u ⟶ v)) a b} :=
  Equiv.ofBijective (fun p => ⟨p.vertices, p.vertices_isChainFromTo⟩) ⟨
    fun _ _ h => vertices_injective (congrArg Subtype.val h),
    fun l => by obtain ⟨p, hp⟩ := exists_vertices l.property; exact ⟨p, Subtype.ext hp⟩⟩

@[simp] theorem equivChain_apply [∀ u v : V, Subsingleton (u ⟶ v)] (a b : V) (p : Path a b) :
    (equivChain a b p).val = p.vertices := by
  simp [equivChain, Equiv.ofBijective]

end Quiver.Path
