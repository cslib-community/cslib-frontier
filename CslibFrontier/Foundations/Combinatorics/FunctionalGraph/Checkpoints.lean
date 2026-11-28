/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.EquivFin

/-!
# Sparse checkpoints in a functional graph

Fix `L > 0`. Inside a finite set `S`, greedily pack disjoint simple paths of `L` states and mark
the last state of each. At most `|S| / L` paths fit, so there are at most `|S| / L` marks. Every
orbit whose first `L` states lie in `S` either repeats a state among them, or meets a packed path
within `L` steps and then reaches its mark within `L - 1` further steps
(`exists_checkpoints_on`). When `S` is invariant under `f`, this applies to every orbit starting
in `S` (`exists_checkpoints`); on a finite type, to every orbit (`exists_checkpoints_finite`).

The state type may live in any universe and need not be finite; only `S` is.

## Main definitions

* `Cslib.FunctionalGraph.Repeats`: the first `L` states of an orbit contain a repeat.

## Main results

* `Cslib.FunctionalGraph.exists_checkpoints_on`: checkpoints for orbits staying in `S`.
* `Cslib.FunctionalGraph.exists_checkpoints`: checkpoints on an invariant finite set.
* `Cslib.FunctionalGraph.exists_checkpoints_finite`: at most `card α / L` checkpoints.
* `Cslib.FunctionalGraph.exists_checkpoints_fin`: the same checkpoints, enumerated injectively.

## References

* Adapted from lean/Proofs/Checkpoints.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

universe u
variable {α : Type u} (f : α → α) {L : ℕ}

/-- A repeated state among the first `L` states of an orbit. -/
def Repeats (x : α) (L : ℕ) : Prop :=
  ∃ i j : ℕ, i < j ∧ j < L ∧ f^[i] x = f^[j] x

/-- **Checkpoints on a finite set.** For `L > 0` there are at most `|S| / L` marks in `S` such
that every orbit whose first `L` states lie in `S` repeats a state among them or reaches a mark
in fewer than `2 L` steps. -/
theorem exists_checkpoints_on (S : Finset α) (hL : 0 < L) :
    ∃ H : Finset α, H ⊆ S ∧ H.card * L ≤ S.card ∧
      ∀ x, (∀ i : Fin L, f^[i.val] x ∈ S) →
        Repeats f x L ∨ ∃ d < 2 * L, f^[d] x ∈ H := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hex : ∃ a, (∀ i : Fin L, f^[i.val] a ∈ S) ∧
        Function.Injective (fun i : Fin L => f^[i.val] a)
    · obtain ⟨a, ha, hinj⟩ := hex
      let P := Finset.univ.image (fun i : Fin L => f^[i.val] a)
      have hPS : P ⊆ S := Finset.image_subset_iff.mpr fun i _ => ha i
      have hcard : P.card = L := by
        simp only [P, Finset.card_image_of_injective _ hinj, Finset.card_univ,
          Fintype.card_fin]
      have hc := Finset.card_sdiff_add_card_eq_card hPS
      let e := f^[L - 1] a
      have heP : e ∈ P := Finset.mem_image.mpr
        ⟨⟨L - 1, by lia⟩, Finset.mem_univ _, rfl⟩
      obtain ⟨H, hHS, hsize, hcover⟩ := ih (S \ P) (Finset.sdiff_ssubset hPS ⟨e, heP⟩)
      have heH : e ∉ H := fun h => (Finset.mem_sdiff.mp (hHS h)).2 heP
      refine ⟨insert e H, Finset.insert_subset (hPS heP) (hHS.trans Finset.sdiff_subset),
        ?_, fun x hx => ?_⟩
      · rw [Finset.card_insert_of_notMem heH, Nat.add_mul]
        lia
      by_cases havoid : ∀ i : Fin L, f^[i.val] x ∉ P
      · exact (hcover x fun i => Finset.mem_sdiff.mpr ⟨hx i, havoid i⟩).imp_right
          fun ⟨d, hd, hh⟩ => ⟨d, hd, Finset.mem_insert_of_mem hh⟩
      push Not at havoid
      obtain ⟨i, hi⟩ := havoid
      obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hi
      refine Or.inr ⟨i.val + (L - 1 - j.val), by lia, Finset.mem_insert.mpr (Or.inl ?_)⟩
      rw [Nat.add_comm i.val, Function.iterate_add_apply, ← hji, ← Function.iterate_add_apply,
        Nat.sub_add_cancel (by lia)]
    · refine ⟨∅, Finset.empty_subset _, by simp, fun x hx => Or.inl ?_⟩
      obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp fun hi => hex ⟨x, hx, hi⟩
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact ⟨i.val, j.val, hij, j.isLt, heq⟩
      · exact ⟨j.val, i.val, hji, i.isLt, heq.symm⟩

/-- **Checkpoints on an invariant set.** If `S` is finite and `f` maps `S` into itself, every
orbit starting in `S` repeats a state among its first `L` or reaches one of at most `|S| / L`
marks in fewer than `2 L` steps. -/
theorem exists_checkpoints (S : Finset α)
    (hS : ∀ x ∈ S, f x ∈ S) (hL : 0 < L) :
    ∃ H : Finset α, H ⊆ S ∧ H.card * L ≤ S.card ∧
      ∀ x ∈ S, Repeats f x L ∨ ∃ d < 2 * L, f^[d] x ∈ H := by
  obtain ⟨H, hHS, hsize, hcover⟩ := exists_checkpoints_on f S hL
  refine ⟨H, hHS, hsize, fun x hx => hcover x fun i => ?_⟩
  have hiter : ∀ t, f^[t] x ∈ S := by
    intro t
    induction t with
    | zero => exact hx
    | succ t ih => simpa only [Function.iterate_succ_apply'] using hS _ ih
  exact hiter i.val

/-- **Checkpoints on a finite type**, at most `card α / L` of them. -/
theorem exists_checkpoints_finite [Fintype α] (hL : 0 < L) :
    ∃ H : Finset α, H.card ≤ Fintype.card α / L ∧
      ∀ x, Repeats f x L ∨ ∃ d < 2 * L, f^[d] x ∈ H := by
  obtain ⟨H, _, hsize, hcover⟩ := exists_checkpoints f Finset.univ
    (fun _ _ => Finset.mem_univ _) hL
  refine ⟨H, (Nat.le_div_iff_mul_le hL).mpr ?_, fun x => hcover x (Finset.mem_univ x)⟩
  simpa using hsize

/-- **Enumerated checkpoints on a finite type**: `exists_checkpoints_finite` with the marks listed
without repetition as `cp : Fin M → α`. -/
theorem exists_checkpoints_fin [Fintype α] (hL : 0 < L) :
    ∃ (M : ℕ) (cp : Fin M → α), Function.Injective cp ∧ M ≤ Fintype.card α / L ∧
      ∀ x, Repeats f x L ∨ ∃ d < 2 * L, ∃ j, f^[d] x = cp j := by
  classical
  obtain ⟨H, hcard, hcover⟩ := exists_checkpoints_finite f hL
  refine ⟨H.card, fun j => (H.equivFin.symm j).val,
    fun _ _ h => H.equivFin.symm.injective (Subtype.ext h), hcard, fun x => ?_⟩
  rcases hcover x with hr | ⟨d, hd, hm⟩
  · exact Or.inl hr
  · exact Or.inr ⟨d, hd, H.equivFin ⟨_, hm⟩, by simp⟩

end Cslib.FunctionalGraph
