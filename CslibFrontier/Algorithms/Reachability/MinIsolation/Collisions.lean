/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Weights
public import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Ring

/-!
# Collisions between Hoza's minimum path weights

Fix an interval and its dominant layer. Consider two nonempty path families
whose columns at the dominant layer are fixed. Any seed tying their minimum
weights is determined by its restriction to the coordinates on which the two
columns' codewords agree [Hoza2026NLUL, Theorem 2.4].

## Main results

* `Cslib.Reachability.Hoza.card_tyingSeeds_le` bounds the number of tying seeds by
  two raised to the number of agreeing codeword coordinates.
-/

public section

namespace Cslib.Reachability.Hoza

open Finset Function

variable {ℓ : ℕ}

private theorem update_agrees {x y : Fin ℓ → Bool} (j : Fin ℓ)
    (h : ∀ i : Fin ℓ, i.val < j.val → x i = y i) :
    ∀ i : Fin ℓ, i.val < j.val + 1 → update x j (y j) i = y i := by
  intro i hi
  by_cases hij : i = j
  · subst i
    simp
  · have hval : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rw [update_of_ne hij]
    exact h i (by omega)

private theorem suffix_change_le (δ : (Fin ℓ → Bool) → ℤ) {A : ℤ} (hA : 0 ≤ A)
    (hstep : ∀ x j b, |δ (update x j b) - δ x| ≤ 3 * (A * 6 ^ (ℓ - (j.val + 1))))
    (k : ℕ) (hk : k ≤ ℓ) (x y : Fin ℓ → Bool)
    (hxy : ∀ i : Fin ℓ, i.val < k → x i = y i) :
    5 * |δ y - δ x| ≤ 3 * (A * 6 ^ (ℓ - k)) := by
  by_cases hlt : k < ℓ
  · let j : Fin ℓ := ⟨k, hlt⟩
    let x' := update x j (y j)
    have htail := suffix_change_le δ hA hstep (k + 1) (by omega) x' y (update_agrees j hxy)
    have hhead := hstep x j (y j)
    have htriangle : |δ y - δ x| ≤ |δ y - δ x'| + |δ x' - δ x| := by
      convert abs_add_le (δ y - δ x') (δ x' - δ x) using 2
      ring
    have hexp : ℓ - k = ℓ - (k + 1) + 1 := by omega
    change |δ x' - δ x| ≤ 3 * (A * 6 ^ (ℓ - (k + 1))) at hhead
    have hscale : 3 * (A * 6 ^ (ℓ - k)) = 18 * (A * 6 ^ (ℓ - (k + 1))) := by
      rw [hexp, pow_succ]
      ring
    rw [hscale]
    omega
  · have heq : x = y := funext fun i => hxy i (by have := i.isLt; omega)
    rw [heq, sub_self, abs_zero, mul_zero]
    positivity
termination_by ℓ - k
decreasing_by omega

private theorem eq_of_agrees_on_equal_bits {c d : Fin ℓ → Bool} (δ : (Fin ℓ → Bool) → ℤ)
    {A : ℤ} (hA : 0 < A)
    (hstep : ∀ x j b, |δ (update x j b) - δ x| ≤ 3 * (A * 6 ^ (ℓ - (j.val + 1))))
    (hgap : ∀ x j b, x j ≠ b → c j ≠ d j →
      A * 6 ^ (ℓ - (j.val + 1)) ≤ |δ (update x j b) - δ x|)
    {x y : Fin ℓ → Bool} (hx : δ x = 0) (hy : δ y = 0)
    (hxy : ∀ j, c j = d j → x j = y j) : x = y := by
  classical
  by_contra hne
  have hex : ∃ k : ℕ, ∃ j : Fin ℓ, j.val = k ∧ x j ≠ y j := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    exact ⟨j.val, j, rfl, hj⟩
  obtain ⟨j, hj, hjdiff⟩ := Nat.find_spec hex
  have hagree : ∀ i : Fin ℓ, i.val < j.val → x i = y i := by
    intro i hi
    by_contra hdiff
    exact Nat.find_min hex (hj ▸ hi) ⟨i, rfl, hdiff⟩
  have hsmall := suffix_change_le δ hA.le hstep (j.val + 1) j.isLt
    (update x j (y j)) y (update_agrees j hagree)
  have hlarge := hgap x j (y j) hjdiff (hjdiff ∘ hxy j)
  rw [hy, zero_sub, abs_neg] at hsmall
  rw [hx, sub_zero] at hlarge
  have hpos : 0 < A * 6 ^ (ℓ - (j.val + 1)) := by positivity
  omega

private theorem abs_update_sub_eq {δ : (Fin ℓ → Bool) → ℤ} {x : Fin ℓ → Bool}
    {j : Fin ℓ} {b : Bool} (h : x j ≠ b) :
    |δ (update x j b) - δ x| = |δ (update x j true) - δ (update x j false)| := by
  cases hj : x j <;> cases b
  · exact (h hj).elim
  · have hself : update x j false = x := update_eq_self_iff.mpr hj.symm
    rw [hself]
  · have hself : update x j true = x := update_eq_self_iff.mpr hj.symm
    rw [hself, abs_sub_comm]
  · exact (h hj).elim

/-- For two path families with fixed columns at the dominant layer, the number of seeds
that tie their minimum weights is at most two to the number of agreeing codeword bits. -/
theorem card_tyingSeeds_le {V P : Type*} (code : V → Fin ℓ → Bool)
    {a b mid : ℕ} (ha : 0 < a) (hm : mid ∈ Icc a b)
    (hmax : ∀ i ∈ Icc a b, multiplicity 2 i ≤ multiplicity 2 mid)
    (column : P → ℕ → V) {paths₁ paths₂ : Finset P}
    (hne₁ : paths₁.Nonempty) (hne₂ : paths₂.Nonempty)
    (u v : V) (hu : ∀ p ∈ paths₁, column p mid = u)
    (hv : ∀ p ∈ paths₂, column p mid = v) :
    let f seed := minIntervalWeight code seed (Icc a b) column paths₁ hne₁
    let g seed := minIntervalWeight code seed (Icc a b) column paths₂ hne₂
    (univ.filter fun seed => f seed = g seed).card ≤ 2 ^ (ℓ - hammingDist (code u) (code v)) := by
  classical
  dsimp only
  let f seed := minIntervalWeight code seed (Icc a b) column paths₁ hne₁
  let g seed := minIntervalWeight code seed (Icc a b) column paths₂ hne₂
  change (univ.filter fun seed => f seed = g seed).card ≤ _
  let δ (x : Fin ℓ → Bool) : ℤ := 2 * ((f x : ℤ) - (g x : ℤ))
  let A : ℤ := 6 ^ padicValNat 2 mid
  have hA : 0 < A := by dsimp [A]; positivity
  have hcoeff (j : Fin ℓ) : (coefficient mid j : ℤ) = A * 6 ^ (ℓ - (j.val + 1)) := by
    simp [coefficient, A]
  have hflip (x : Fin ℓ → Bool) (j : Fin ℓ) :
      |δ (update x j true) - δ (update x j false)| ≤ 3 * (coefficient mid j : ℤ) ∧
      (code u j ≠ code v j → (coefficient mid j : ℤ) ≤
        |δ (update x j true) - δ (update x j false)|) := by
    have h₁ := minIntervalWeight_update_bounds code x ha hm hmax column hne₁ u hu j
    have h₂ := minIntervalWeight_update_bounds code x ha hm hmax column hne₂ v hv j
    change f (update x j false) + coefficient mid j * (code u j).toNat ≤
        f (update x j true) ∧ f (update x j true) ≤
        f (update x j false) + coefficient mid j * (code u j).toNat + coefficient mid j / 2 at h₁
    change g (update x j false) + coefficient mid j * (code v j).toNat ≤
        g (update x j true) ∧ g (update x j true) ≤
        g (update x j false) + coefficient mid j * (code v j).toNat + coefficient mid j / 2 at h₂
    dsimp only [δ]
    cases hcu : code u j <;> cases hcv : code v j <;>
      simp only [hcu, hcv, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one, add_zero] at *
    all_goals refine ⟨abs_le.mpr ⟨by omega, by omega⟩, fun h => ?_⟩
    · exact (h rfl).elim
    · exact (by omega : (coefficient mid j : ℤ) ≤ -_).trans (neg_le_abs _)
    · exact (by omega : (coefficient mid j : ℤ) ≤ _).trans (le_abs_self _)
    · exact (h rfl).elim
  have hstep (x : Fin ℓ → Bool) (j : Fin ℓ) (b : Bool) :
      |δ (update x j b) - δ x| ≤ 3 * (A * 6 ^ (ℓ - (j.val + 1))) := by
    by_cases h : x j = b
    · rw [update_eq_self_iff.mpr h.symm, sub_self, abs_zero]
      positivity
    · rw [abs_update_sub_eq h, ← hcoeff]
      exact (hflip x j).1
  have hgap (x : Fin ℓ → Bool) (j : Fin ℓ) (b : Bool) :
      x j ≠ b → code u j ≠ code v j →
        A * 6 ^ (ℓ - (j.val + 1)) ≤ |δ (update x j b) - δ x| := by
    intro h hcode
    rw [abs_update_sub_eq h, ← hcoeff]
    exact (hflip x j).2 hcode
  let agree := univ.filter fun j => code u j = code v j
  let restrict (seed : Fin ℓ → Bool) (j : agree) := seed j
  have hcount : (univ.filter fun seed => f seed = g seed).card ≤
      (univ : Finset (agree → Bool)).card := by
    refine card_le_card_of_injOn restrict (fun _ _ => mem_univ _) ?_
    intro x hx y hy he
    have hzero (seed : Fin ℓ → Bool) (h : seed ∈ univ.filter fun s => f s = g s) :
        δ seed = 0 := by simp [δ, (mem_filter.mp h).2]
    apply eq_of_agrees_on_equal_bits δ hA hstep hgap (hzero x hx) (hzero y hy)
    intro j hj
    exact congrFun he ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
  have hagree : agree.card = ℓ - hammingDist (code u) (code v) := by
    have hcard := card_filter_add_card_filter_not (s := (univ : Finset (Fin ℓ)))
      (fun j => code u j = code v j)
    rw [card_univ, Fintype.card_fin] at hcard
    change agree.card + hammingDist (code u) (code v) = ℓ at hcard
    omega
  rwa [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hagree] at hcount

end Cslib.Reachability.Hoza
