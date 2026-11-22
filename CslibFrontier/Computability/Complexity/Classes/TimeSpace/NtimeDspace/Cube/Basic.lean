/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Nat.Bitwise

/-!
# Requests, labels and walks on the cube: the basic objects

This file fixes the representations used throughout `Cslib.Complexity.NtimeDspace.Cube`, the
formalization of the
current proof of Theorem 2.3 (`separating-ntime-from-space.tex`, §§3–6).

* A *request* has a *type* `i : ℕ` and the weight `i + 1`. A multiset of requests is a
  `Multiset ℕ` of types, with weight `wt σ = ∑ (i + 1)` (§4.1).
* A *label* is a pair of multisets of requests, `Multiset ℕ × Multiset ℕ`; its weight is the sum
  of the two weights. `labelsLE a` is the finite set `Λ_≤(a)` of labels of weight at most `a`,
  and `labelsEq a` the set `Λ(a)` of labels of weight exactly `a`.
* On the cube (§5.1): `d i j = i ^^^ j` is the distance in which bit `e` has length `2^e`,
  `ip i j` is the number of common one-bits of `i` and `j`, `chi i j = (-1)^(ip i j)` the sign of
  a step, and `C i j = chi i j • T^(d i j)` the step as a Laurent polynomial in `z = T 1`.

## Main results

* `wt_add`, `labelWt`, `mem_labelsLE`, `mem_labelsEq`: weights and the finite label sets.
* `d_le_add` and `le_add_d`: the two inequalities (eq:metric), `d i j ≤ i + j` and
  `j ≤ i + d i j`.
* `d_add_mod_two`: `d i j ≡ i + j (mod 2)`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

/-! ### Requests and labels -/

/-- The weight of a multiset of requests: a request of type `i` weighs `i + 1`. -/
def wt (σ : Multiset ℕ) : ℕ := (σ.map (· + 1)).sum

@[simp] theorem wt_zero : wt 0 = 0 := by simp [wt]

@[simp] theorem wt_add (σ τ : Multiset ℕ) : wt (σ + τ) = wt σ + wt τ := by
  simp [wt, Multiset.map_add, Multiset.sum_add]

@[simp] theorem wt_cons (i : ℕ) (σ : Multiset ℕ) : wt (i ::ₘ σ) = (i + 1) + wt σ := by
  simp [wt]

@[simp] theorem wt_singleton (i : ℕ) : wt {i} = i + 1 := by simp [wt]

/-- A request of a multiset has type below the weight of the multiset. -/
theorem lt_wt_of_mem {σ : Multiset ℕ} {i : ℕ} (h : i ∈ σ) : i < wt σ := by
  obtain ⟨τ, rfl⟩ := Multiset.exists_cons_of_mem h
  simp only [wt_cons]; omega

theorem wt_mono {σ τ : Multiset ℕ} (h : σ ≤ τ) : wt σ ≤ wt τ := by
  obtain ⟨ρ, rfl⟩ := Multiset.le_iff_exists_add.mp h
  rw [wt_add]; exact Nat.le_add_right _ _

theorem card_le_wt (σ : Multiset ℕ) : Multiset.card σ ≤ wt σ := by
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons i σ ih => simp; omega

/-- A label: the requests sent and the requests received, or, on a pair `u < v` of nodes, the
requests `u` sends to `v` and those `v` sends to `u`. -/
abbrev Label := Multiset ℕ × Multiset ℕ

/-- The weight of a label. -/
def labelWt (l : Label) : ℕ := wt l.1 + wt l.2

/-- The largest multiset of weight-`a` support: `Σ_{i<a} (a / (i+1)) · {i}`. Every multiset of
weight at most `a` lies below it. -/
def bigMultiset (a : ℕ) : Multiset ℕ :=
  ((Finset.range a).val).bind fun i => Multiset.replicate (a / (i + 1)) i

theorem count_le_of_wt_le {σ : Multiset ℕ} {a i : ℕ} (h : wt σ ≤ a) :
    σ.count i * (i + 1) ≤ a := by
  have : (Multiset.replicate (σ.count i) i) ≤ σ := Multiset.le_count_iff_replicate_le.mp le_rfl
  have hw : wt (Multiset.replicate (σ.count i) i) ≤ wt σ := wt_mono this
  have e : wt (Multiset.replicate (σ.count i) i) = σ.count i * (i + 1) := by
    simp [wt, Multiset.map_replicate, Multiset.sum_replicate, smul_eq_mul]
  omega

theorem le_bigMultiset {σ : Multiset ℕ} {a : ℕ} (h : wt σ ≤ a) : σ ≤ bigMultiset a := by
  rw [Multiset.le_iff_count]
  intro i
  by_cases hi : i < a
  · have hc := count_le_of_wt_le (i := i) h
    have : σ.count i ≤ a / (i + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr hc
    refine this.trans ?_
    have hmem : i ∈ (Finset.range a).val := Finset.mem_range.mpr hi
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hmem
    simp only [bigMultiset, Multiset.count_bind, ht, Multiset.map_cons, Multiset.sum_cons,
      Multiset.count_replicate_self]
    exact Nat.le_add_right _ _
  · have : σ.count i = 0 := by
      rw [Multiset.count_eq_zero]
      intro hm
      have := lt_wt_of_mem hm
      omega
    simp [this]

/-- `Λ_≤(a)`: the labels of weight at most `a`. -/
def labelsLE (a : ℕ) : Finset Label :=
  ((bigMultiset a).powerset.toFinset ×ˢ (bigMultiset a).powerset.toFinset).filter
    fun l => labelWt l ≤ a

/-- `Λ(a)`: the labels of weight exactly `a`. -/
def labelsEq (a : ℕ) : Finset Label := (labelsLE a).filter fun l => labelWt l = a

theorem mem_labelsLE {a : ℕ} {l : Label} : l ∈ labelsLE a ↔ labelWt l ≤ a := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h⟩
    · simp only [Multiset.mem_toFinset, Multiset.mem_powerset]
      exact le_bigMultiset (by unfold labelWt at h; omega)
    · simp only [Multiset.mem_toFinset, Multiset.mem_powerset]
      exact le_bigMultiset (by unfold labelWt at h; omega)

theorem mem_labelsEq {a : ℕ} {l : Label} : l ∈ labelsEq a ↔ labelWt l = a := by
  unfold labelsEq
  rw [Finset.mem_filter, mem_labelsLE]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h.le, h⟩

/-! ### Walks on the cube -/

/-- The distance on the cube in which bit `e` has length `2^e`: the exclusive or, read as an
integer. -/
def d (i j : ℕ) : ℕ := i ^^^ j

/-- The number of positions where both `i` and `j` have a one (`⟨i, j⟩` of the paper, before
reduction modulo 2). -/
def ip (i j : ℕ) : ℕ := ((Finset.range (i + 1)).filter fun e => i.testBit e && j.testBit e).card

/-- The sign of a step from `i` to `j`. -/
def chi (i j : ℕ) : ℤ := (-1) ^ ip i j

open LaurentPolynomial in
/-- A step from `i` to `j`: `C_{i,j}(z) = (-1)^{⟨i,j⟩} z^{d(i,j)}`. -/
noncomputable def C (i j : ℕ) : LaurentPolynomial ℤ := LaurentPolynomial.C (chi i j) * T (d i j)

theorem d_comm (i j : ℕ) : d i j = d j i := Nat.xor_comm i j

@[simp] theorem d_self (i : ℕ) : d i i = 0 := Nat.xor_self i

theorem d_le_or (i j : ℕ) : d i j ≤ i ||| j :=
  Nat.le_of_testBit fun e h => by
    simp only [d, Nat.testBit_xor, Nat.testBit_or] at h ⊢
    cases hi : i.testBit e <;> cases hj : j.testBit e <;> simp_all

/-- The first inequality of (eq:metric). -/
theorem d_le_add (i j : ℕ) : d i j ≤ i + j := (d_le_or i j).trans Nat.or_le_add

/-- The second inequality of (eq:metric): `j ≤ i + d(i,j)`. -/
theorem le_add_d (i j : ℕ) : j ≤ i + d i j := by
  have h1 : j ≤ i ||| d i j :=
    Nat.le_of_testBit fun e h => by
      simp only [d, Nat.testBit_xor, Nat.testBit_or] at h ⊢
      cases hi : i.testBit e <;> cases hj : j.testBit e <;> simp_all
  exact h1.trans Nat.or_le_add

/-- `d i j ≡ i + j (mod 2)`: the last bit of `i ^^^ j` is the parity of `i + j`. -/
theorem d_add_mod_two (i j : ℕ) : d i j % 2 = (i + j) % 2 := by
  have h : (d i j).testBit 0 = (i.testBit 0 ^^ j.testBit 0) := Nat.testBit_xor i j 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
    rcases Nat.mod_two_eq_zero_or_one (d i j) with hd | hd <;>
    simp [hi, hj, hd] at h <;> omega

end Cslib.Complexity.NtimeDspace.Cube
