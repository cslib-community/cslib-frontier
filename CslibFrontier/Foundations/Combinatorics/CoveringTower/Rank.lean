/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
import Cslib.Tactic.Membership
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

/-!
# Ranks within key classes

`Cslib.CoveringTower.rk idx key F u` counts the elements of `F` with the key of `u` and a
smaller index: ranks within the classes of equal keys, used to number the elements of a class.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tow.Rank`.

## Main definitions

* `Cslib.CoveringTower.rk`: the rank.

## Main results

* `Cslib.CoveringTower.rk_lt`, `Cslib.CoveringTower.injOn_rk`: ranks are below the class size and
  injective on every class, the condition the ranking clients use.
-/

public section

namespace Cslib.CoveringTower

open Finset

variable {U κ : Type*} [DecidableEq κ] (idx : U → ℕ) (key : U → κ)

/-- The rank of an element among those with the same key. -/
def rk (F : Finset U) (u : U) : ℕ := (F.filter fun v => key v = key u ∧ idx v < idx u).card

variable {idx key}

/-- The rank of `u` is the number of elements of `F` with its key and a smaller index. -/
theorem rk_eq (F : Finset U) (u : U) :
    rk idx key F u = (F.filter fun v => key v = key u ∧ idx v < idx u).card := by
  rw [rk]

theorem rk_congr {F F' : Finset U} {u : U} (h : ∀ v, key v = key u → (v ∈ F ↔ v ∈ F')) :
    rk idx key F u = rk idx key F' u := by
  rw [rk_eq, rk_eq]
  refine congrArg card (ext fun v => ?_)
  simp only [mem_filter, and_congr_left_iff]
  exact fun ⟨h2, _⟩ => h v h2

theorem rk_lt {F : Finset U} {u : U} (hu : u ∈ F) : rk idx key F u <
    (F.filter fun v => key v = key u).card := by
  refine card_lt_card ((ssubset_iff_of_subset fun v hv =>
    mem_filter.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hv).2.1⟩).mpr ?_)
  exact ⟨u, mem_filter.mpr ⟨hu, rfl⟩, fun h => lt_irrefl _ (mem_filter.mp h).2.2⟩

theorem rk_lt_rk {F : Finset U} {u v : U} (hu : u ∈ F) (huv : key u = key v) (h : idx u < idx v) :
    rk idx key F u < rk idx key F v := by
  refine card_lt_card ?_
  rw [ssubset_iff_of_subset]
  · exact ⟨u, mem_filter.mpr ⟨hu, huv, h⟩, fun h => lt_irrefl _ (mem_filter.mp h).2.2⟩
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨h1, h2.trans huv, h3.trans h⟩

theorem rk_inj (hidx : Function.Injective idx) {F : Finset U} {u v : U} (hu : u ∈ F) (hv : v ∈ F)
    (huv : key u = key v) (h : rk idx key F u = rk idx key F v) : u = v := by
  rcases lt_trichotomy (idx u) (idx v) with h1 | h1 | h1
  · have := rk_lt_rk hu huv h1
    omega
  · exact hidx h1
  · have := rk_lt_rk hv huv.symm h1
    omega

/-- The rank is injective on every key fiber. -/
theorem injOn_rk (hidx : Function.Injective idx) (F : Finset U) (k : κ) :
    Set.InjOn (rk idx key F) (F.filter fun u => key u = k) := by
  intro u hu v hv h
  have hu' := mem_filter.1 (mem_coe.1 hu)
  have hv' := mem_filter.1 (mem_coe.1 hv)
  exact rk_inj hidx hu'.1 hv'.1 (hu'.2.trans hv'.2.symm) h

theorem card_rk_le (hidx : Function.Injective idx) (F : Finset U) (k : κ) (a b : ℕ) :
    (F.filter fun u => key u = k ∧ a ≤ rk idx key F u ∧ rk idx key F u < b).card ≤ b - a := by
  rw [← Nat.card_Ico]
  refine card_le_card_of_injOn (rk idx key F) ?_ ?_
  · intro u hu
    have := (mem_filter.1 (mem_coe.1 hu)).2
    exact mem_coe.2 (mem_Ico.2 this.2)
  · refine (injOn_rk (key := key) hidx F k).mono fun u hu => ?_
    have hu' := mem_filter.1 (mem_coe.1 hu)
    exact mem_coe.2 (mem_filter.2 ⟨hu'.1, hu'.2.1⟩)

/-- Every rank occurs. -/
theorem exists_rk (hidx : Function.Injective idx) (F : Finset U) (k : κ) {w : ℕ}
    (hw : w < (F.filter fun u => key u = k).card) : ∃ u ∈ F, key u = k ∧ rk idx key F u = w := by
  have hinj := injOn_rk (key := key) hidx F k
  have himg : (F.filter fun u => key u = k).image (rk idx key F) =
      range (F.filter fun u => key u = k).card := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro ρ hρ
      obtain ⟨u, hu, rfl⟩ := mem_image.1 hρ
      obtain ⟨h1, h2⟩ := mem_filter.1 hu
      exact mem_range.2 (h2 ▸ rk_lt h1)
    · rw [card_range, card_image_of_injOn hinj]
  obtain ⟨u, hu, rfl⟩ := mem_image.1 (himg ▸ mem_range.2 hw)
  exact ⟨u, (mem_filter.1 hu).1, (mem_filter.1 hu).2, rfl⟩

end Cslib.CoveringTower
