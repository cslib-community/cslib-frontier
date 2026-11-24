/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.GroupTheory.SLTower.Layer
public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow

/-!
# A chain of subgroups in the kernel

Two steps of the tower construction [AnthropicVPVNP2026, paper §H.1, PDF p. 44, before
Proposition H.1]. The kernel `Ker h n` of the value at `s = 0` is a 2-group of order
`2^((h² − 1) n)`, so by Sylow's theorem it contains a chain `1 = Γ 0 ≤ Γ 1 ≤ ⋯` of subgroups of
orders `(2^e)^j` for
`j ≤ JJ h n = ⌊(h² − 1) n / e⌋`, where `e = h(h − 1)/2` (`b = 2^e` is the number of chambers at a
vertex).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tower.Chain`.

## Main definitions

* `Cslib.SLTower.Ker h n`: the kernel of the value at `s = 0`.
* `Cslib.SLTower.ee h`, `Cslib.SLTower.JJ h n`: the exponent `e` and the number of steps.

## Main results

* `Cslib.SLTower.isPGroup_ker`: the kernel is a 2-group of order `2^((h² − 1) n)`.
* `Cslib.SLTower.exists_chain`: the chain of subgroups.
-/

public section

namespace Cslib.SLTower

variable {h n : ℕ} [NeZero h]

/-- The kernel of the value at `s = 0`. -/
noncomputable def Ker (h n : ℕ) : Subgroup (G h n) := (evG : G h n →* SL2 h).ker

omit [NeZero h] in
theorem mem_Ker {g : G h n} : g ∈ Ker h n ↔ evG g = 1 := Iff.rfl

/-- A step of the tower construction: the kernel of the value at `s = 0` is a 2-group of order
`2^((h² − 1) n)` [AnthropicVPVNP2026, paper §H.1, PDF p. 44, just before Proposition H.1]. -/
theorem isPGroup_ker (h n : ℕ) [NeZero h] :
    IsPGroup 2 (Ker h n) ∧ Nat.card (Ker h n) = 2 ^ ((h ^ 2 - 1) * n) :=
  ⟨IsPGroup.of_card card_ker_evG, card_ker_evG⟩

/-- The exponent of the number b of chambers at a vertex: b = 2^e. -/
@[expose] def ee (h : ℕ) : ℕ := h * (h - 1) / 2

/-- The number of steps of the tower. -/
@[expose] def JJ (h n : ℕ) : ℕ := (h ^ 2 - 1) * n / ee h

/-- A step of the tower construction: a chain of subgroups of the kernel of orders `(2^e)^j`,
from Sylow's theorem. -/
theorem exists_chain (h n : ℕ) [NeZero h] : ∃ Γ : ℕ → Subgroup (G h n),
    Γ 0 = ⊥ ∧ (∀ j, Γ j ≤ Γ (j + 1)) ∧
    (∀ j, Γ j ≤ Ker h n) ∧ ∀ j ≤ JJ h n, Nat.card (Γ j) = (2 ^ ee h) ^ j := by
  classical
  have step : ∀ j, ∀ H : Subgroup (Ker h n), Nat.card H = 2 ^ (ee h * j) → j < JJ h n →
      ∃ H' : Subgroup (Ker h n), Nat.card H' = 2 ^ (ee h * (j + 1)) ∧ H ≤ H' := by
    intro j H hH hj
    obtain ⟨K, hK, hHK, -⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two (n := ee h *
        (j + 1)) (L := ⊤)
      (by rw [hH]; exact pow_dvd_pow 2 (Nat.mul_le_mul_left _ (Nat.le_succ j)))
      (by
        rw [Subgroup.card_top, (isPGroup_ker h n).2]
        refine pow_dvd_pow 2 ?_
        calc ee h * (j + 1) ≤ ee h * JJ h n := Nat.mul_le_mul_left _ hj
          _ ≤ _ := Nat.mul_div_le _ _) le_top
    exact ⟨K, hK, hHK⟩
  have h0 : Nat.card (⊥ : Subgroup (Ker h n)) = 2 ^ (ee h * min 0 (JJ h n)) := by simp
  have step' : ∀ j, ∀ H : {H : Subgroup (Ker h n) // Nat.card H = 2 ^ (ee h * min j (JJ h n))},
      ∃ H' : {H : Subgroup (Ker h n) // Nat.card H = 2 ^ (ee h * min (j + 1) (JJ h n))},
          H.val ≤ H'.val := by
    intro j H
    by_cases hj : j < JJ h n
    · obtain ⟨H', h1, h2⟩ := step j H.val (by rw [H.property, min_eq_left hj.le]) hj
      exact ⟨⟨H', by rw [h1, min_eq_left (Nat.succ_le_of_lt hj)]⟩, h2⟩
    · refine ⟨⟨H.val, ?_⟩, le_rfl⟩
      rw [H.property, min_eq_right (not_lt.1 hj),
          min_eq_right ((not_lt.1 hj).trans (Nat.le_succ j))]
  choose nxt hnxt using step'
  let f : (j : ℕ) → {H : Subgroup (Ker h n) // Nat.card H = 2 ^ (ee h * min j (JJ h n))} := fun j =>
    Nat.rec ⟨⊥, h0⟩ nxt j
  have hf : ∀ j, (f j).val ≤ (f (j + 1)).val := fun j => hnxt j (f j)
  refine ⟨fun j => (f j).val.map (Ker h n).subtype, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_bot _
  · exact fun j => Subgroup.map_mono (hf j)
  · intro j g hg
    obtain ⟨k, -, rfl⟩ := hg
    exact k.property
  · intro j hj
    rw [Nat.card_congr
        ((f j).val.equivMapOfInjective _ (Subgroup.subtype_injective _)).toEquiv.symm,
      (f j).property, min_eq_left hj, pow_mul]

end Cslib.SLTower
