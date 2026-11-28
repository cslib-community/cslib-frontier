/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Constants
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Transfer
public import CslibFrontier.Foundations.GroupTheory.SLTower.Tower
import Mathlib.Data.Fintype.Order

/-!
# The towers of all sizes

The first step of the proof of Theorem H.2 of [AnthropicVPVNP2026] (p. 46). Let laws at the
vertices of the tower of `U_h` (Theorem G.2) have a contraction with `1 + 8 C₁ ≤ h / 4`. For
`y ≥ 1` take the least `n` with `y ≤ |G_n|`, so that `|G_n| ≤ c y` by Proposition H.1(c)
(`SLTower.card_G_succ`), and the tower `SLTower.tower h n` with routes from the words of
Proposition H.1(d) (`SLTower.exists_diam`, `SLTower.exists_routes`). The laws are transferred to it
(`VertexLaws.transfer`) and mapped to any algebra (`VertexLaws.map`); the tower and its laws
satisfy `TowerConstants` with one constant `c` for all `n`, at the rate `1 / 2`, with the gain
`(1 / 2) ^ e(h) 2 ^ e(h) = 1` (`exists_towers`).

## Main results

* `exists_towers`: the towers of all sizes, with their routes and laws.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition H.1 (p. 44) and the proof of Theorem H.2 (p. 46); modules `Paper.Tower` and
  `Paper.Tree`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Trees

open Finset Cslib.CoveringTower Cut TowerPlan

/-- **The towers of all sizes** (the proof of Theorem H.2 of [AnthropicVPVNP2026], p. 46: "Take
the least `n ≥ 1` with `M ≤ |G_n|`, so that `|G_n| = O(M)` by Proposition H.1(c)", with
Proposition H.1(c), (d), p. 44): for laws at the vertices of the tower of `U_h` with
`1 + 8 C₁ ≤ h / 4` there is a constant `c` such that for every `y ≥ 1` and every ring
homomorphism `f` some tower `SLTower.tower h n`, with the laws transferred to it and mapped by `f`,
satisfies the conditions `TowerConstants` with `c`, the rate `1 / 2` and the gain
`(1 / 2) ^ e(h) 2 ^ e(h) = 1`, has between `y` and `c y` chambers at the level `0`, and has routes
of at most `m` steps with `1 ≤ m ≤ c (J + 1) ^ 7` that use every edge at most `2 |X 0| m` times
in all. -/
theorem exists_towers {A₀ : Type*} [CommSemiring A₀] {h : ℕ} [NeZero h] (h3 : 3 ≤ h)
    (FL : VertexLaws A₀ (SLTower.tower h 0 (by omega)))
    (hgain : 1 + 8 * FL.contraction ≤ (h : ℝ) / 4) :
    ∃ c, ∀ (R : Type*) [CommSemiring R] (f : A₀ →+* R) (y : ℕ), 1 ≤ y → ∃ n m Uu : ℕ,
      Nonempty (Routes (SLTower.tower h n (by omega)) m Uu) ∧
      TowerConstants ((FL.map f).transfer (SLTower.tower h n (by omega)) (Equiv.refl _)
          (Equiv.refl _) fun _ => rfl)
        (((univ : Finset FL.Kind).toList.map FL.law).map fun L => L.map f) c (1 / 2) 1
        (SLTower.ee h) ∧
      y ≤ Fintype.card ((SLTower.tower h n (by omega)).X 0) ∧
      Fintype.card ((SLTower.tower h n (by omega)).X 0) ≤ c * y ∧ 1 ≤ m ∧
      m ≤ c * (SLTower.JJ h n + 1) ^ 7 ∧
      Uu ≤ 2 * Fintype.card ((SLTower.tower h n (by omega)).X 0) * m := by
  have h2 : 2 ≤ h := by omega
  have hee : 2 ≤ SLTower.ee h := by
    have : 3 * 2 ≤ h * (h - 1) := Nat.mul_le_mul h3 (by omega)
    unfold SLTower.ee
    omega
  have heeh : SLTower.ee h ≤ h ^ 2 - 1 := by
    have h4 : h * (h - 1) ≤ h * h := Nat.mul_le_mul_left _ (by omega)
    have h6 : 9 ≤ h * h := Nat.mul_le_mul h3 h3
    unfold SLTower.ee
    rw [pow_two]
    omega
  obtain ⟨C₀, hC₀⟩ := SLTower.exists_diam h h2 h3
  obtain ⟨B₁, hB₁⟩ := Finite.exists_le fun x : Σ d, (FL.law d).Index × (FL.law d).Channel =>
    (FL.law x.1).length x.2.1 x.2.2
  obtain ⟨B₂, hB₂⟩ := Finite.exists_le fun d => Fintype.card (FL.law d).Slot
  obtain ⟨B₃, hB₃⟩ := Finite.exists_le fun d => (FL.law d).labelLength
  set g := fun n => Nat.card (SLTower.G h n) with hg
  have hg0 (n : ℕ) : g (n + 1) = g n * 2 ^ (h ^ 2 - 1) := SLTower.card_G_succ
  have hg2 (n : ℕ) : 2 ^ n ≤ g n := by
    induction n with
    | zero => exact Nat.card_pos
    | succ n ih =>
      rw [hg0, pow_succ]
      exact Nat.mul_le_mul ih (Nat.le_self_pow (by omega) 2)
  obtain ⟨c, hc⟩ : ∃ c, ∀ a ∈ [h, 2 ^ SLTower.ee h, Fintype.card (SLTower.NN h), FL.lengthBound,
      Fintype.card FL.Kind, Fintype.card (Sym2 (SLTower.U h)), B₁, B₂, B₃,
      Nat.card (SLTower.SL2 h) * 2 ^ SLTower.ee h, ⌈√(h : ℝ) + √FL.contraction * FL.scale⌉₊, 2,
      g 0, 2 ^ (h ^ 2 - 1), C₀ + 1], a ≤ c := ⟨_, fun a ha => List.le_sum_of_mem ha⟩
  refine ⟨c, fun R _ f y hy => ?_⟩
  have hex : ∃ n, y ≤ g n := ⟨y, Nat.lt_two_pow_self.le.trans (hg2 y)⟩
  set n := Nat.find hex
  have hn1 : y ≤ g n := Nat.find_spec hex
  have hn2 : g n ≤ c * y := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]
      exact (hc _ (by simp)).trans (Nat.le_mul_of_pos_right _ hy)
    · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have h4 : ¬ y ≤ g k := Nat.find_min hex (show k < n by omega)
      rw [hk, hg0, mul_comm c y]
      exact Nat.mul_le_mul (by omega) (hc _ (by simp))
  have hnJ : n ≤ SLTower.JJ h n := by
    unfold SLTower.JJ
    rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
    exact Nat.mul_le_mul_right _ heeh
  have hX0 : Fintype.card ((SLTower.tower h n h2).X 0) = g n := by
    have := SLTower.card_XX (h := h) (n := n) (j := 0) (Nat.zero_le _)
    rw [pow_zero, mul_one] at this
    exact this
  obtain ⟨Rt⟩ := SLTower.exists_routes (n := n) h2 (m := (C₀ + 1) * (n + 1) ^ 7) fun x =>
    (hC₀ n x).mono (Nat.mul_le_mul_right _ (Nat.le_succ C₀))
  refine ⟨n, _, _, ⟨Rt⟩, ?_, hX0 ▸ hn1, hX0 ▸ hn2, Nat.mul_pos (by omega) (by positivity),
    Nat.mul_le_mul (hc _ (by simp)) (Nat.pow_le_pow_left (by omega) 7), (mul_assoc _ _ _).symm.le⟩
  have hmem (d : FL.Kind) :
      (FL.law d).map f ∈ ((univ : Finset FL.Kind).toList.map FL.law).map fun L => L.map f :=
    List.mem_map.2 ⟨_, List.mem_map.2 ⟨d, mem_toList.2 (mem_univ d), rfl⟩, rfl⟩
  have hlaw {L : Law R}
      (hL : L ∈ ((univ : Finset FL.Kind).toList.map FL.law).map fun L => L.map f) :
      ∃ d, L = (FL.law d).map f := by
    obtain ⟨_, h1, rfl⟩ := List.mem_map.1 hL
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 h1
    exact ⟨d, rfl⟩
  have h4 : (4 : ℝ) ≤ ((2 ^ SLTower.ee h : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right two_pos hee
  exact {
    r_pos := one_pos
    b_pos := by positivity
    h_pos := by omega
    b_le := by omega
    ρ_pos := by norm_num
    one_add_le := hgain.trans_eq (by ring)
    two_le := by linarith
    rate_lt_one := by norm_num
    exists_nearPair := fun x => by
      rcases Sym2.eq_iff.1 (SLTower.npair_sym (⟨0, by omega⟩ : Fin (h - 1)) x) with
        ⟨e1, -⟩ | ⟨e1, -⟩
      exacts [⟨_, Or.inl e1.symm⟩, ⟨_, Or.inr e1.symm⟩]
    two_mul_le := by omega
    rate_pow_mul_le_one := by
      push_cast
      rw [pow_one, ← mul_pow]
      norm_num
    law_mem := hmem
    types_le := hc _ (by simp)
    places_le := hc _ (by simp)
    degree_le := (hc 2 (by simp)).trans' (by norm_num)
    card_nearPair_le := show Fintype.card (SLTower.NN h) ≤ c from hc _ (by simp)
    lengthBound_le := show FL.lengthBound ≤ c from hc _ (by simp)
    card_kind_le := show Fintype.card FL.Kind ≤ c from hc _ (by simp)
    card_pair_le := show Fintype.card (Sym2 (SLTower.U h)) ≤ c from hc _ (by simp)
    card_slot_le := fun d => (hB₂ d).trans (hc _ (by simp))
    card_X_last_le := (SLTower.card_XJ h n h2).le.trans (hc _ (by simp))
    card_X_last_pos := Fintype.card_pos_iff.2 ⟨QuotientGroup.mk 1⟩
    normFactor_le := by
      rw [Nat.cast_one, mul_one]
      exact (Nat.le_ceil _).trans
        (Nat.cast_le.2 (hc ⌈√(h : ℝ) + √FL.contraction * FL.scale⌉₊ (by simp)))
    inv_one_sub_le := by
      rw [show (1 : ℝ) / (1 - 1 / 2) = (2 : ℕ) by norm_num]
      exact_mod_cast hc 2 (by simp)
    lengthLE := fun L hL => by
      obtain ⟨d, rfl⟩ := hlaw hL
      exact fun i ν => (hB₁ ⟨d, i, ν⟩).trans (hc _ (by simp))
    labelLength_le := fun L hL => by
      obtain ⟨d, rfl⟩ := hlaw hL
      exact (hB₃ d).trans (hc _ (by simp)) }

end Cslib.Circuits.Arithmetic.Separation.Trees
