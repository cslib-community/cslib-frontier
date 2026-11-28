/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Operations

/-!
# Counting disagreements using even delta-matroid exchange

A forbidden two-coordinate move at a feasible base tuple bounds disagreements on one set
of coordinates by disagreements on another. The proof uses one-sided exchange at a specified
coordinate and induction on Hamming distance; it requires neither simultaneous exchange nor
matching realizability. Common parity may be either even or odd.

## Main results

* `IsEvenDeltaMatroid.card_disagree_le`: a local counting bound from forbidden base moves.
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R : Set (ι → Bool)} {x y : ι → Bool}

/-- If every feasible two-coordinate move from `x` entering `I` must also enter `O`, then
any feasible tuple disagrees with `x` on at most as many coordinates of `I` as of `O`.
The sets must be disjoint. This is a counting consequence of one-sided even exchange. -/
theorem IsEvenDeltaMatroid.card_disagree_le (hR : IsEvenDeltaMatroid R)
    (hx : x ∈ R) (hy : y ∈ R) (I O : Finset ι) (hIO : Disjoint I O)
    (hmove : ∀ i ∈ I, ∀ j ∉ O, j ≠ i → flipOn {i, j} x ∉ R) :
    (I.filter fun i => x i ≠ y i).card ≤ (O.filter fun i => x i ≠ y i).card := by
  induction y using (_root_.measure fun y => hammingDist y x).wf.induction
  rename_i y ih
  by_cases hO : ∃ e ∈ O, x e ≠ y e
  · obtain ⟨e, heO, he⟩ := hO
    obtain ⟨j, hje, hj, hy'⟩ := hR.exchange hy hx (Ne.symm he)
    have hd := hammingDist_flipOn_pair_add_two hje.symm (Ne.symm he) hj
    set y' := flipOn {e, j} y
    have hy'_of_ne {i : ι} (hie : i ≠ e) (hij : i ≠ j) : y' i = y i := by
      simp [y', flipOn_apply, hie, hij]
    have hb := ih y' ((Nat.lt_add_of_pos_right (by decide : 0 < 2)).trans_eq hd) hy'
    have hI : (I.filter fun i => x i ≠ y i) ⊆ insert j (I.filter fun i => x i ≠ y' i) := by
      intro i hi
      obtain ⟨hiI, hxy⟩ := mem_filter.mp hi
      by_cases hij : i = j
      · exact mem_insert.mpr (Or.inl hij)
      · have hie : i ≠ e := fun h => Finset.disjoint_left.mp hIO (h ▸ hiI) heO
        exact mem_insert_of_mem (mem_filter.mpr ⟨hiI, by rwa [hy'_of_ne hie hij]⟩)
    have hO' : (O.filter fun i => x i ≠ y' i) ⊆ (O.filter fun i => x i ≠ y i).erase e := by
      intro i hi
      obtain ⟨hiO, hxy'⟩ := mem_filter.mp hi
      have hie : i ≠ e := by
        rintro rfl
        exact hxy' ((Bool.eq_not_iff.mpr he).trans (by simp [y', flipOn_apply]))
      exact mem_erase.mpr ⟨hie, mem_filter.mpr ⟨hiO,
        if hij : i = j then hij ▸ hj.symm else hy'_of_ne hie hij ▸ hxy'⟩⟩
    have h₁ := (card_le_card hI).trans (card_insert_le j _)
    have h₂ := (card_le_card hO').trans_lt (card_erase_lt_of_mem (mem_filter.mpr ⟨heO, he⟩))
    omega
  · rw [filter_eq_empty_iff.mpr fun i hiI hi => by
        obtain ⟨j, hji, hj, hf⟩ := hR.exchange hx hy hi
        exact hmove i hiI j (fun hjO => hO ⟨j, hjO, hj⟩) hji hf,
      card_empty]
    exact Nat.zero_le _

end Cslib.BitString
