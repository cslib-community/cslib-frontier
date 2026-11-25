/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.PadicValNat
import CslibFrontier.Foundations.Combinatorics.MinIsolation.BaseSix
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Multiplicities of two in positive intervals

An interval containing no multiple of `2 ^ (m + 1)` is confined to one block
between consecutive multiples. In that block the numbers of multiplicity `k ≤ m`
have residue `2 ^ k` modulo `2 ^ (k + 1)`. This gives the counting bound in
[Hoza2026NLUL, Lemma 2.1] and uniqueness at the maximum.

## Main results

* `Nat.card_filter_Icc_multiplicity_two_le`: at most `2 ^ (m - k)` points have
  multiplicity `k` when every point has multiplicity at most `m`.
* `Nat.existsUnique_max_multiplicity_two_Icc`: a nonempty positive interval
  has exactly one point of maximum multiplicity.
* `Nat.two_mul_sum_six_pow_multiplicity_erase_le`: the contribution of all other
  points is at most half the dominant power of six.
-/

public section

namespace Nat

private theorem mod_pow_succ_of_multiplicity_two {x k : ℕ} (hx : x ≠ 0)
    (hk : multiplicity 2 x = k) : x % 2 ^ (k + 1) = 2 ^ k := by
  obtain ⟨y, hy⟩ := (pow_dvd_iff_le_multiplicity (by decide : (2 : ℕ) ≠ 1) hx).2 hk.ge
  have hyodd : ¬2 ∣ y := by
    intro h
    have hdvd : (2 : ℕ) ^ (k + 1) ∣ x := by
      rw [hy, pow_succ]
      exact Nat.mul_dvd_mul_left _ h
    have hbad := (pow_dvd_iff_le_multiplicity (by decide : (2 : ℕ) ≠ 1) hx).1 hdvd
    omega
  have hyrem : y % 2 = 1 := by
    have hne := Nat.dvd_iff_mod_eq_zero.not.mp hyodd
    have hlt := Nat.mod_lt y (by decide : 0 < 2)
    omega
  rw [hy, pow_succ, Nat.mul_mod_mul_left, hyrem, Nat.mul_one]

/-- A positive interval with multiplicity at most `m` contains at most
`2 ^ (m - k)` points of multiplicity `k ≤ m`. -/
theorem card_filter_Icc_multiplicity_two_le {a b m k : ℕ} (ha : 0 < a) (hk : k ≤ m)
    (hm : ∀ x ∈ Finset.Icc a b, multiplicity 2 x ≤ m) :
    ((Finset.Icc a b).filter fun x => multiplicity 2 x = k).card ≤ 2 ^ (m - k) := by
  let D := (2 : ℕ) ^ (m + 1)
  let E := (2 : ℕ) ^ (k + 1)
  have hD : 0 < D := pow_pos (by decide) _
  have hE : 0 < E := pow_pos (by decide) _
  have hfactor : D = E * 2 ^ (m - k) := by
    dsimp [D, E]
    rw [← pow_add]
    congr 1
    omega
  have hbound : b < D * (a / D + 1) := by
    by_contra! hb
    have hleft := Nat.lt_mul_div_succ a hD
    have hx : D * (a / D + 1) ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨hleft.le, hb⟩
    have hmul := hm _ hx
    have hdiv : D ∣ D * (a / D + 1) := dvd_mul_right _ _
    have hbad := (pow_dvd_iff_le_multiplicity (by decide : (2 : ℕ) ≠ 1)
      (Nat.ne_of_gt (ha.trans hleft))).1 hdiv
    omega
  have hblock (x : ℕ) (hx : x ∈ Finset.Icc a b) : x / D = a / D := by
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hx
    have hlow : a / D ≤ x / D := Nat.div_le_div_right hl
    have hhigh : x / D < a / D + 1 :=
      (Nat.div_lt_iff_lt_mul hD).2 (by rw [Nat.mul_comm]; exact hr.trans_lt hbound)
    omega
  have hdvd : E ∣ D := ⟨_, hfactor⟩
  rw [← Finset.card_range (2 ^ (m - k))]
  refine Finset.card_le_card_of_injOn (fun x => x % D / E) ?_ ?_
  · intro x _
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hE).2
    rw [Nat.mul_comm, ← hfactor]
    exact Nat.mod_lt x hD
  · intro x hx y hy hxy
    obtain ⟨hxI, hxk⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyI, hyk⟩ := Finset.mem_filter.mp hy
    have hpos (z : ℕ) (hz : z ∈ Finset.Icc a b) : z ≠ 0 :=
      Nat.ne_of_gt (ha.trans_le (Finset.mem_Icc.mp hz).1)
    have hrem : x % D % E = y % D % E := by
      rw [Nat.mod_mod_of_dvd x hdvd, Nat.mod_mod_of_dvd y hdvd]
      exact (mod_pow_succ_of_multiplicity_two (hpos x hxI) hxk).trans
        (mod_pow_succ_of_multiplicity_two (hpos y hyI) hyk).symm
    change x % D / E = y % D / E at hxy
    have hmod : x % D = y % D := by
      rw [← Nat.mod_add_div (x % D) E, ← Nat.mod_add_div (y % D) E, hrem, hxy]
    rw [← Nat.mod_add_div x D, ← Nat.mod_add_div y D, hmod, hblock x hxI, hblock y hyI]

/-- The highest multiplicity of two in a nonempty interval of positive naturals
occurs exactly once. -/
theorem existsUnique_max_multiplicity_two_Icc {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    ∃! x, x ∈ Finset.Icc a b ∧ ∀ y ∈ Finset.Icc a b, multiplicity 2 y ≤ multiplicity 2 x := by
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (Finset.Icc a b) (multiplicity 2)
    ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  refine ⟨x, ⟨hx, hmax⟩, ?_⟩
  rintro y ⟨hy, hymax⟩
  have hcard : ((Finset.Icc a b).filter
      fun z => multiplicity 2 z = multiplicity 2 x).card ≤ 1 := by
    simpa using card_filter_Icc_multiplicity_two_le ha le_rfl hmax
  exact Finset.card_le_one_iff.mp hcard
    (Finset.mem_filter.mpr ⟨hy, (hmax y hy).antisymm (hymax x hx)⟩)
    (Finset.mem_filter.mpr ⟨hx, rfl⟩)

open Finset in
/-- The nonmaximal layers together contribute at most half the maximal power of six.
This is the finite geometric estimate used in [Hoza2026NLUL, Lemma 2.3]. -/
theorem two_mul_sum_six_pow_multiplicity_erase_le {a b j : ℕ} (ha : 0 < a)
    (hj : j ∈ Icc a b) (hmax : ∀ i ∈ Icc a b, multiplicity 2 i ≤ multiplicity 2 j) :
    2 * (∑ i ∈ (Icc a b).erase j, (6 : ℕ) ^ multiplicity 2 i) ≤
      6 ^ multiplicity 2 j := by
  let m := multiplicity 2 j
  have hm : ((Icc a b).filter fun i => multiplicity 2 i = m).card ≤ 1 := by
    simpa using card_filter_Icc_multiplicity_two_le ha le_rfl hmax
  have hlt : ∀ i ∈ ((Icc a b).erase j).val, multiplicity 2 i < m := by
    intro i hi
    obtain ⟨hne, hi⟩ := mem_erase.mp (show i ∈ (Icc a b).erase j from hi)
    refine (hmax i hi).lt_of_ne fun h => hne ?_
    exact card_le_one_iff.mp hm (mem_filter.mpr ⟨hi, h⟩) (mem_filter.mpr ⟨hj, rfl⟩)
  have hcard : ∀ k < m, ((((Icc a b).erase j).val).filter fun i => multiplicity 2 i = k).card ≤
      2 ^ (m - k) := by
    intro k hk
    change (((Icc a b).erase j).filter fun i => multiplicity 2 i = k).card ≤ 2 ^ (m - k)
    refine (card_le_card fun i hi => ?_).trans
      (card_filter_Icc_multiplicity_two_le ha hk.le hmax)
    obtain ⟨hi, he⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_of_mem_erase hi, he⟩
  exact Cslib.MinIsolation.BaseSix.two_mul_sum_six_pow_multiset_le
    ((Icc a b).erase j).val (multiplicity 2) hlt hcard

end Nat
