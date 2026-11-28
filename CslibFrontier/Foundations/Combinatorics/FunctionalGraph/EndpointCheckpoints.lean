/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph
public import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Basic

/-!
# Endpoint minima as orbit checkpoints

Rank the states of a functional graph. Mark a state when its next `L + 1` states, counting
the state itself, are distinct and either endpoint has minimum rank. An orbit with a simple
prefix of length `2 * L` then reaches a mark in fewer than `L` steps. More precisely, the
index of *any* minimum in the prefix determines the mark by a single comparison.

The selection rule adapts Edgar's closed syncmers to orbit windows
[Edgar, Methods, “Closed syncmers”, and Fig. 1][Edgar2021Syncmers]. Edgar breaks ties on the
left. Here either endpoint may be tied for the minimum. The size of the mark set depends
on the ranking.
-/

public section

namespace Cslib.FunctionalGraph

variable {α β : Type*} [LinearOrder β] (f : α → α) (rank : α → β)

/-- The orbit window from `z` through `f^[L] z` is simple and has a minimum at an endpoint. -/
@[expose] def IsEndpointCheckpoint (L : ℕ) (z : α) : Prop :=
  Function.Injective (fun j : Fin (L + 1) => f^[j.val] z) ∧
    ((∀ j : Fin (L + 1), rank z ≤ rank (f^[j.val] z)) ∨
      ∀ j : Fin (L + 1), rank (f^[L] z) ≤ rank (f^[j.val] z))

/-- Folding a minimum index in a simple prefix of length `2 * L` selects a window whose
minimum is at the left endpoint in the first half and at the right endpoint in the second. -/
theorem isEndpointCheckpoint_of_min {L : ℕ} {x : α}
    (hinj : Function.Injective (fun j : Fin (2 * L) => f^[j.val] x))
    (i : Fin (2 * L)) (hmin : ∀ j : Fin (2 * L), rank (f^[i.val] x) ≤ rank (f^[j.val] x)) :
    IsEndpointCheckpoint f rank L (f^[if i.val < L then i.val else i.val - L] x) := by
  let d := if i.val < L then i.val else i.val - L
  have hd : d < L := by dsimp [d]; split <;> have := i.isLt <;> lia
  let idx (j : Fin (L + 1)) : Fin (2 * L) := ⟨j.val + d, by have := j.isLt; lia⟩
  have hshift (j : Fin (L + 1)) : f^[j.val] (f^[d] x) = f^[(idx j).val] x :=
    (Function.iterate_add_apply f j.val d x).symm
  refine ⟨fun j k heq => Fin.ext ?_, ?_⟩
  · have h : j.val + d = k.val + d :=
      congrArg Fin.val (hinj ((hshift j).symm.trans (heq.trans (hshift k))))
    lia
  · by_cases hi : i.val < L
    · refine .inl fun j => ?_
      rw [hshift]
      simpa only [d, ite_eq_left hi] using hmin (idx j)
    · refine .inr fun j => ?_
      have he : L + d = i.val := by
        simp only [d, ite_eq_right hi]
        lia
      rw [hshift, ← Function.iterate_add_apply, he]
      exact hmin (idx j)

/-- Every simple prefix of length `2 * L` reaches an endpoint checkpoint within its first
`L` states. The ranking and the starting state are arbitrary. -/
theorem exists_endpointCheckpoint {L : ℕ} (hL : 0 < L) {x : α}
    (hinj : Function.Injective (fun j : Fin (2 * L) => f^[j.val] x)) :
    ∃ d < L, IsEndpointCheckpoint f rank L (f^[d] x) := by
  classical
  have : Nonempty (Fin (2 * L)) := ⟨⟨0, by lia⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_min (fun j : Fin (2 * L) => rank (f^[j.val] x))
  exact ⟨_, by split <;> have := i.isLt <;> lia,
    isEndpointCheckpoint_of_min f rank hinj i hi⟩

/-- For an orbit still in its transient part after at least `2 * L` steps, some checkpoint
on that orbit is at most `2 * L` steps before the target. The first inequality on depths
ensures that a forward walk from the checkpoint can reach the target. -/
theorem exists_endpointCheckpoint_near_transient [Finite α] {L t : ℕ} (hL : 0 < L)
    (x : α) (hfar : 2 * L ≤ t) (ht : t ≤ transientDepth f x) :
    ∃ a, IsEndpointCheckpoint f rank L a ∧
      (∃ j ≤ transientDepth f x, f^[j] x = a) ∧
      transientDepth f (f^[t] x) ≤ transientDepth f a ∧
      transientDepth f a ≤ transientDepth f (f^[t] x) + 2 * L := by
  let b := t - 2 * L
  let z := f^[b] x
  have hb : b + 2 * L = t := Nat.sub_add_cancel hfar
  have hz : transientDepth f z = transientDepth f x - b := transientDepth_iterate f x b
  have hinj : Function.Injective (fun i : Fin (2 * L) => f^[i.val] z) := fun i j he => by
    have hd := congrArg (transientDepth f) he
    simp only [transientDepth_iterate, hz] at hd
    have := i.isLt
    have := j.isLt
    exact Fin.ext (by lia)
  obtain ⟨d, hd, ha⟩ := exists_endpointCheckpoint f rank hL hinj
  refine ⟨f^[d] z, ha, ⟨d + b, by lia, Function.iterate_add_apply f d b x⟩, ?_⟩
  simp only [transientDepth_iterate, hz]
  lia

/-- Every ancestor in the target depth window yields the same answer. Taking the difference
of depths gives the exact suffix length to walk, bounded by the width of the window. -/
theorem iterate_of_ancestor_depth_window [Finite α] {x a : α} {t K : ℕ}
    (ht : t ≤ transientDepth f x) (ha : ∃ j ≤ transientDepth f x, f^[j] x = a)
    (hlo : transientDepth f (f^[t] x) ≤ transientDepth f a)
    (hhi : transientDepth f a ≤ transientDepth f (f^[t] x) + K) :
    let k := transientDepth f a - transientDepth f (f^[t] x)
    k ≤ K ∧ f^[k] a = f^[t] x := by
  obtain ⟨j, hj, rfl⟩ := ha
  simp only [transientDepth_iterate] at hlo hhi ⊢
  refine ⟨by lia, ?_⟩
  rw [← Function.iterate_add_apply]
  exact congrArg (f^[·] x) (by lia)

end Cslib.FunctionalGraph
