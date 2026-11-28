/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Multiset.Filter
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Logic.Function.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Base-six level-profile weights and collision bounds

This module extracts the shared combinatorial core of Hoza's base-six min-isolation method
([Hoza2026NLUL], §2.1–2.2, Lemma 2.3 and Theorem 2.4):

* An item at nonnegative scale level `k` with binary codeword `word : Fin ℓ → Bool` receives
  the seeded weight `∑ j, 6 ^ (k + (ℓ - (j + 1))) * (word j).toNat * (seed j).toNat`.
* For a multiset of items with one dominant item at level `m` and at most `2 ^ (m - k)` items
  at each strictly lower level `k < m`, the total contribution of the lower levels is at most
  half the dominant power of six (`two_mul_sum_six_pow_multiset_le`), giving the two-sided
  seed-update derivative bound (`multisetWeight_update_bounds`).
* Taking a pointwise minimum over any nonempty finite family sharing the same dominant level
  and codeword preserves the two-sided derivative bound (`minWeight_update_bounds`).
* For any two seed functions satisfying the two-sided derivative bound at the same level `m`
  with codewords `c` and `d`, at most `2 ^ (ℓ - hammingDist c d)` seeds equate them
  (`card_tyingSeeds_le_of_update_bounds`).

Both paths in layered digraphs (`Cslib.Reachability.Hoza`) and proof trees in layered
semi-unbounded Boolean circuits (`Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit`)
instantiate these lemmas directly.

## Main definitions

* `Cslib.MinIsolation.BaseSix.levelBitCoeff`: the base-six coefficient at a given level and bit.
* `Cslib.MinIsolation.BaseSix.levelWeight`: seeded base-six weight of one `(level, word)` pair.
* `Cslib.MinIsolation.BaseSix.multisetWeight`: sum of seeded weights over a multiset of items.

## Main results

* `Cslib.MinIsolation.BaseSix.two_mul_sum_six_pow_multiset_le`: geometric half-bound from a
  `2 ^ (m - k)` level profile.
* `Cslib.MinIsolation.BaseSix.multisetWeight_update_bounds`: two-sided seed derivative bound
  for one weighted multiset.
* `Cslib.MinIsolation.BaseSix.minWeight_update_bounds`: Hoza's exchange argument preserving the
  derivative bound under pointwise minimum.
* `Cslib.MinIsolation.BaseSix.card_tyingSeeds_le_of_update_bounds`: upper bound
  `2 ^ (ℓ - hammingDist c d)` on seeds tying two functions with matching derivative bounds.
-/

public section

namespace Cslib.MinIsolation.BaseSix

open Finset Function

variable {α P : Type*} {ℓ : ℕ}

/-- The base-six coefficient of bit `j : Fin ℓ` at scale level `level`. -/
@[expose] def levelBitCoeff (level : ℕ) (j : Fin ℓ) : ℕ :=
  6 ^ level * 6 ^ (ℓ - (j.val + 1))

/-- The seeded base-six weight of an item at `level` with binary codeword `word`. -/
@[expose] def levelWeight (level : ℕ) (word seed : Fin ℓ → Bool) : ℕ :=
  ∑ j : Fin ℓ, levelBitCoeff level j * (word j).toNat * (seed j).toNat

/-- Every seeded level weight is strictly below `6 ^ (level + ℓ)`. -/
theorem levelWeight_lt_pow (level : ℕ) (word seed : Fin ℓ → Bool) :
    levelWeight level word seed < 6 ^ (level + ℓ) := by
  calc
    levelWeight level word seed ≤ ∑ j : Fin ℓ, levelBitCoeff level j :=
      sum_le_sum fun j _ => by cases word j <;> cases seed j <;> simp
    _ = 6 ^ level * ∑ k ∈ range ℓ, 6 ^ k := by
      rw [mul_sum, ← Fin.sum_univ_eq_sum_range]
      calc
        (∑ j : Fin ℓ, levelBitCoeff level j) =
            ∑ j : Fin ℓ, levelBitCoeff level (Fin.revPerm j) :=
          (Equiv.sum_comp Fin.revPerm _).symm
        _ = _ := sum_congr rfl fun j _ => congrArg (6 ^ level * 6 ^ ·) (by
          have := j.isLt
          simp only [Fin.revPerm_apply, Fin.val_rev]; omega)
    _ < 6 ^ (level + ℓ) := by
      rw [pow_add]
      exact Nat.mul_lt_mul_of_pos_left
        (Nat.geomSum_lt (by decide) fun _ hk => mem_range.mp hk) (by positivity)

/-- Switching seed bit `j` from `false` to `true` increases `levelWeight` by the masked
coefficient at `j`. -/
theorem levelWeight_update (level : ℕ) (word seed : Fin ℓ → Bool) (j : Fin ℓ) :
    levelWeight level word (update seed j true) =
      levelWeight level word (update seed j false) + levelBitCoeff level j * (word j).toNat := by
  have hsingle : (∑ k : Fin ℓ, if k = j then levelBitCoeff level j * (word j).toNat else 0) =
      levelBitCoeff level j * (word j).toNat := by simp
  rw [levelWeight, levelWeight, ← hsingle, ← sum_add_distrib]
  exact sum_congr rfl fun k _ => by by_cases h : k = j <;> simp [h]

private theorem two_mul_sum_six_pow_le (m : ℕ) :
    2 * (∑ k ∈ range m, (2 : ℕ) ^ (m - k) * 6 ^ k) ≤ 6 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsum : (∑ k ∈ range m, (2 : ℕ) ^ (m + 1 - k) * 6 ^ k) =
        2 * ∑ k ∈ range m, (2 : ℕ) ^ (m - k) * 6 ^ k := by
      rw [mul_sum]
      exact sum_congr rfl fun k hk => by
        rw [Nat.succ_sub (Nat.le_of_lt (mem_range.mp hk)), pow_succ']; ring
    rw [sum_range_succ, hsum, Nat.add_sub_cancel_left, pow_one, pow_succ 6]
    omega

private theorem sum_six_pow_multiset_eq_sum_range (s : Multiset α) (level : α → ℕ) {m : ℕ}
    (hlt : ∀ x ∈ s, level x < m) :
    (s.map fun x => (6 : ℕ) ^ level x).sum =
      ∑ k ∈ range m, (s.filter fun x => level x = k).card * 6 ^ k := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have hfilter (k : ℕ) :
        ((a ::ₘ t).filter fun x => level x = k).card * 6 ^ k =
          (if level a = k then 6 ^ k else 0) +
            (t.filter fun x => level x = k).card * 6 ^ k := by
      rw [Multiset.filter_cons]
      split_ifs <;> simp [Nat.add_mul, Nat.add_comm]
    rw [Multiset.map_cons, Multiset.sum_cons, ih fun x hx => hlt x (Multiset.mem_cons_of_mem hx)]
    simp_rw [hfilter, sum_add_distrib]
    simp [sum_ite_eq, hlt a (Multiset.mem_cons_self a t)]

/-- If every element of a multiset has level strictly below `m` and at most `2 ^ (m - k)`
elements sit at each level `k < m`, then all elements together contribute at most half of
`6 ^ m`. -/
theorem two_mul_sum_six_pow_multiset_le (s : Multiset α) (level : α → ℕ) {m : ℕ}
    (hlt : ∀ x ∈ s, level x < m)
    (hcard : ∀ k < m, (s.filter fun x => level x = k).card ≤ 2 ^ (m - k)) :
    2 * (s.map fun x => (6 : ℕ) ^ level x).sum ≤ 6 ^ m := by
  rw [sum_six_pow_multiset_eq_sum_range s level hlt]
  refine le_trans (Nat.mul_le_mul_left 2 ?_) (two_mul_sum_six_pow_le m)
  exact sum_le_sum fun k hk => Nat.mul_le_mul_right _ (hcard k (mem_range.mp hk))

/-- Sum of seeded base-six weights over a multiset of items. -/
@[expose] def multisetWeight (level : α → ℕ) (code : α → Fin ℓ → Bool)
    (seed : Fin ℓ → Bool) (s : Multiset α) : ℕ :=
  (s.map fun x => levelWeight (level x) (code x) seed).sum

/-- The weight of the empty multiset is zero. -/
@[simp] theorem multisetWeight_zero (level : α → ℕ) (code : α → Fin ℓ → Bool)
    (seed : Fin ℓ → Bool) :
    multisetWeight level code seed 0 = 0 := rfl

/-- Adding one item adds its seeded weight. -/
@[simp] theorem multisetWeight_cons (level : α → ℕ) (code : α → Fin ℓ → Bool)
    (seed : Fin ℓ → Bool) (a : α) (s : Multiset α) :
    multisetWeight level code seed (a ::ₘ s) =
      levelWeight (level a) (code a) seed + multisetWeight level code seed s := by
  simp only [multisetWeight, Multiset.map_cons, Multiset.sum_cons]

/-- The weight of a sum of multisets is the sum of their weights. -/
@[simp] theorem multisetWeight_add (level : α → ℕ) (code : α → Fin ℓ → Bool)
    (seed : Fin ℓ → Bool) (s t : Multiset α) :
    multisetWeight level code seed (s + t) =
      multisetWeight level code seed s + multisetWeight level code seed t := by
  simp only [multisetWeight, Multiset.map_add, Multiset.sum_add]

private theorem multisetWeight_update (level : α → ℕ) (code : α → Fin ℓ → Bool)
    (seed : Fin ℓ → Bool) (s : Multiset α) (j : Fin ℓ) :
    multisetWeight level code (update seed j true) s =
      multisetWeight level code (update seed j false) s +
        (s.map fun x => levelBitCoeff (level x) j * (code x j).toNat).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    simp only [multisetWeight_cons, Multiset.map_cons, Multiset.sum_cons,
      levelWeight_update, ih]
    omega

/-- For a multiset with one dominant item `r` at level `m` and a `2 ^ (m - k)` level profile on
the remaining items `rest`, flipping bit `j` changes `multisetWeight` by between
`levelBitCoeff m j * (code r j).toNat` and that quantity plus `levelBitCoeff m j / 2`. -/
theorem multisetWeight_update_bounds (level : α → ℕ) (code : α → Fin ℓ → Bool)
    (seed : Fin ℓ → Bool) (r : α) (rest : Multiset α) {m : ℕ}
    (hr : level r = m) (hlt : ∀ x ∈ rest, level x < m)
    (hcard : ∀ k < m, (rest.filter fun x => level x = k).card ≤ 2 ^ (m - k))
    (j : Fin ℓ) :
    let w₀ := multisetWeight level code (update seed j false) (r ::ₘ rest)
    let w₁ := multisetWeight level code (update seed j true) (r ::ₘ rest)
    w₀ + levelBitCoeff m j * (code r j).toNat ≤ w₁ ∧
      w₁ ≤ w₀ + levelBitCoeff m j * (code r j).toNat + levelBitCoeff m j / 2 := by
  dsimp only
  rw [multisetWeight_update, Multiset.map_cons, Multiset.sum_cons, hr]
  have hsum : (rest.map fun x => levelBitCoeff (level x) j * (code x j).toNat).sum ≤
      (rest.map fun x => (6 : ℕ) ^ level x).sum * 6 ^ (ℓ - (j.val + 1)) := by
    clear hlt hcard
    induction rest using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Nat.add_mul]
      exact Nat.add_le_add (by cases code a j <;> simp [levelBitCoeff]) ih
  have hdouble : 2 * (rest.map fun x => levelBitCoeff (level x) j * (code x j).toNat).sum ≤
      levelBitCoeff m j :=
    (Nat.mul_le_mul_left 2 hsum).trans ((Nat.mul_assoc ..).symm ▸
      Nat.mul_le_mul_right _ (two_mul_sum_six_pow_multiset_le rest level hlt hcard))
  omega

/-- Hoza's exchange argument: a pointwise minimum over a nonempty finite family of seed functions
inherits any common two-sided base-six derivative bound. -/
theorem minWeight_update_bounds (weight : P → (Fin ℓ → Bool) → ℕ)
    {F : Finset P} (hne : F.Nonempty) {m : ℕ} {c : Fin ℓ → Bool}
    (seed : Fin ℓ → Bool) (j : Fin ℓ)
    (hbound : ∀ p ∈ F,
      weight p (update seed j false) + levelBitCoeff m j * (c j).toNat ≤
        weight p (update seed j true) ∧
      weight p (update seed j true) ≤
        weight p (update seed j false) + levelBitCoeff m j * (c j).toNat +
          levelBitCoeff m j / 2) :
    let d₀ := (F.image fun p => weight p (update seed j false)).min' (hne.image _)
    let d₁ := (F.image fun p => weight p (update seed j true)).min' (hne.image _)
    d₀ + levelBitCoeff m j * (c j).toNat ≤ d₁ ∧
      d₁ ≤ d₀ + levelBitCoeff m j * (c j).toNat + levelBitCoeff m j / 2 := by
  dsimp only
  obtain ⟨p₀, hp₀, h₀⟩ := mem_image.mp
    (min'_mem (F.image fun p => weight p (update seed j false)) (hne.image _))
  obtain ⟨p₁, hp₁, h₁⟩ := mem_image.mp
    (min'_mem (F.image fun p => weight p (update seed j true)) (hne.image _))
  exact ⟨(Nat.add_le_add_right (min'_le _ _ (mem_image_of_mem _ hp₁)) _).trans
      (h₁ ▸ (hbound p₁ hp₁).1),
    (min'_le _ _ (mem_image_of_mem _ hp₀)).trans (h₀ ▸ (hbound p₀ hp₀).2)⟩

private theorem update_agrees {x y : Fin ℓ → Bool} (j : Fin ℓ)
    (h : ∀ i : Fin ℓ, i.val < j.val → x i = y i) :
    ∀ i : Fin ℓ, i.val < j.val + 1 → update x j (y j) i = y i := by
  intro i hi
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [update_of_ne hij]
    exact h i (lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) (Fin.val_ne_of_ne hij))

private theorem suffix_change_le (δ : (Fin ℓ → Bool) → ℤ) {A : ℤ} (hA : 0 ≤ A)
    (hstep : ∀ x j b, |δ (update x j b) - δ x| ≤ 3 * (A * 6 ^ (ℓ - (j.val + 1))))
    (k : ℕ) (hk : k ≤ ℓ) (x y : Fin ℓ → Bool)
    (hxy : ∀ i : Fin ℓ, i.val < k → x i = y i) :
    5 * |δ y - δ x| ≤ 3 * (A * 6 ^ (ℓ - k)) := by
  by_cases hlt : k < ℓ
  · let j : Fin ℓ := ⟨k, hlt⟩
    let x' := update x j (y j)
    have htail := suffix_change_le δ hA hstep (k + 1) (by omega) x' y (update_agrees j hxy)
    have hhead : |δ x' - δ x| ≤ 3 * (A * 6 ^ (ℓ - (k + 1))) := hstep x j (y j)
    have htri : |δ y - δ x| ≤ |δ y - δ x'| + |δ x' - δ x| := by
      simpa only [sub_add_sub_cancel] using abs_add_le (δ y - δ x') (δ x' - δ x)
    have hscale : 3 * (A * 6 ^ (ℓ - k)) = 18 * (A * 6 ^ (ℓ - (k + 1))) := by
      rw [show ℓ - k = ℓ - (k + 1) + 1 by omega, pow_succ]
      ring
    rw [hscale]
    omega
  · have heq : x = y := funext fun i => hxy i (by have := i.isLt; omega)
    rw [heq, sub_self, abs_zero, mul_zero]
    positivity
termination_by ℓ - k

private theorem eq_of_agrees_on_equal_bits {c d : Fin ℓ → Bool} (δ : (Fin ℓ → Bool) → ℤ)
    {A : ℤ} (hA : 0 < A)
    (hstep : ∀ x j b, |δ (update x j b) - δ x| ≤ 3 * (A * 6 ^ (ℓ - (j.val + 1))))
    (hgap : ∀ x j b, x j ≠ b → c j ≠ d j →
      A * 6 ^ (ℓ - (j.val + 1)) ≤ |δ (update x j b) - δ x|)
    {x y : Fin ℓ → Bool} (hx : δ x = 0) (hy : δ y = 0)
    (hxy : ∀ j, c j = d j → x j = y j) : x = y := by
  classical
  by_contra hne
  have hex : ∃ k : ℕ, ∃ j : Fin ℓ, j.val = k ∧ x j ≠ y j :=
    (Function.ne_iff.mp hne).elim fun j hj => ⟨j.val, j, rfl, hj⟩
  obtain ⟨j, hj, hjdiff⟩ := Nat.find_spec hex
  have hsmall := suffix_change_le δ hA.le hstep (j.val + 1) j.isLt (update x j (y j)) y
    (update_agrees j fun i hi => by_contra fun hd => Nat.find_min hex (hj ▸ hi) ⟨i, rfl, hd⟩)
  have hlarge := hgap x j (y j) hjdiff (hjdiff ∘ hxy j)
  rw [hy, zero_sub, abs_neg] at hsmall
  rw [hx, sub_zero] at hlarge
  have : 0 < A * 6 ^ (ℓ - (j.val + 1)) := by positivity
  omega

private theorem abs_update_sub_eq {δ : (Fin ℓ → Bool) → ℤ} {x : Fin ℓ → Bool}
    {j : Fin ℓ} {b : Bool} (h : x j ≠ b) :
    |δ (update x j b) - δ x| = |δ (update x j true) - δ (update x j false)| := by
  nth_rw 2 [← update_eq_self j x]
  revert h
  cases x j <;> cases b <;> simp [abs_sub_comm]

/-- If two seed functions satisfy the two-sided base-six derivative bound at the same scale level
`m` with codewords `c` and `d`, then every tying seed is uniquely determined by its bits on
coordinates where `c` and `d` agree, so at most `2 ^ (ℓ - hammingDist c d)` seeds equate them. -/
theorem card_tyingSeeds_le_of_update_bounds (f g : (Fin ℓ → Bool) → ℕ)
    {m : ℕ} {c d : Fin ℓ → Bool}
    (hf : ∀ seed j,
      f (update seed j false) + levelBitCoeff m j * (c j).toNat ≤ f (update seed j true) ∧
      f (update seed j true) ≤
        f (update seed j false) + levelBitCoeff m j * (c j).toNat + levelBitCoeff m j / 2)
    (hg : ∀ seed j,
      g (update seed j false) + levelBitCoeff m j * (d j).toNat ≤ g (update seed j true) ∧
      g (update seed j true) ≤
        g (update seed j false) + levelBitCoeff m j * (d j).toNat + levelBitCoeff m j / 2) :
    (univ.filter fun seed => f seed = g seed).card ≤ 2 ^ (ℓ - hammingDist c d) := by
  classical
  let δ (x : Fin ℓ → Bool) : ℤ := 2 * ((f x : ℤ) - (g x : ℤ))
  have hcoeff (j : Fin ℓ) : (levelBitCoeff m j : ℤ) = (6 : ℤ) ^ m * 6 ^ (ℓ - (j.val + 1)) := by
    simp [levelBitCoeff]
  have hflip (x : Fin ℓ → Bool) (j : Fin ℓ) :
      |δ (update x j true) - δ (update x j false)| ≤ 3 * (levelBitCoeff m j : ℤ) ∧
      (c j ≠ d j → (levelBitCoeff m j : ℤ) ≤
        |δ (update x j true) - δ (update x j false)|) := by
    have h₁ := hf x j
    have h₂ := hg x j
    dsimp only [δ]
    cases hc : c j <;> cases hd : d j <;>
      simp only [hc, hd, Bool.toNat_false, Bool.toNat_true] at h₁ h₂ ⊢ <;>
      refine ⟨abs_le.mpr ⟨by omega, by omega⟩, fun h => le_abs.mpr ?_⟩
    exacts [absurd rfl h, by omega, by omega, absurd rfl h]
  let agree := univ.filter fun j => c j = d j
  have hcount : (univ.filter fun seed => f seed = g seed).card ≤
      (univ : Finset (agree → Bool)).card := by
    refine card_le_card_of_injOn (fun seed (j : agree) => seed j) (fun _ _ => mem_univ _)
      fun x hx y hy he => eq_of_agrees_on_equal_bits δ (A := 6 ^ m) (by positivity)
        (fun z j b => ?_) (fun z j b h hc => ?_) (by simp [δ, (mem_filter.mp hx).2])
        (by simp [δ, (mem_filter.mp hy).2]) fun j hj =>
          congrFun he ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
    · by_cases h : z j = b
      · rw [update_eq_self_iff.mpr h.symm, sub_self, abs_zero]; positivity
      · simpa only [abs_update_sub_eq h, ← hcoeff] using (hflip z j).1
    · simpa only [abs_update_sub_eq h, ← hcoeff] using (hflip z j).2 hc
  have hcard : agree.card = ℓ - hammingDist c d := eq_tsub_of_add_eq
    (by simpa [hammingDist] using
      card_filter_add_card_filter_not (s := (univ : Finset (Fin ℓ))) (fun j => c j = d j))
  simpa [Fintype.card_coe, hcard] using hcount

end Cslib.MinIsolation.BaseSix
