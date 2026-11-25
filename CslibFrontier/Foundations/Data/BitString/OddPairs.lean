/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.Code.Hadamard

/-!
# Averages over the odd pairs of bit strings

Rigidity arguments for Pauli operators average over the pairs `(a, b)` of bit strings with
`a · b = 1`, the *odd* pairs, on which `X(a)` and `Z(b)` anticommute. The **masked average**
`oddExpect f = E_{a,b} [a · b = 1] f(a, b)` (`Cslib.BitString.oddExpect`) averages `f` over all
pairs with the even pairs set to `0`. It is the density `(1 - 2⁻ⁿ) / 2` of the odd pairs times the
conditional average over them (`Cslib.BitString.oddExpect_eq_dens_smul`,
`Cslib.BitString.dens_oddPairs`); for `n = 0` there are no odd pairs and it is `0`. It is monotone
and linear on the odd pairs (`Cslib.BitString.oddExpect_mono`, `Cslib.BitString.oddExpect_add`,
`Cslib.BitString.oddExpect_const_mul`). Each coordinate marginal is half the uniform
average with the zero string masked out (`Cslib.BitString.oddExpect_fst`,
`Cslib.BitString.oddExpect_snd`).

A nonzero `a` has `a · c = 1` for exactly half of the `c`, so a bound holding for every such `c`
holds for twice the masked average over `c`: if `g ≤ h(c)` whenever `a · c = 1`, then
`g ≤ 2 E_c [a · c = 1] h(c)` (`Cslib.BitString.le_two_mul_expect_ite_of_forall`). This turns
pointwise estimates through an auxiliary odd string `c` into averaged ones.

## Main definitions

* `Cslib.BitString.oddPairs`: the odd pairs.
* `Cslib.BitString.oddExpect`: the masked average over the odd pairs.

## Main results

* `Cslib.BitString.oddExpect_eq_dens_smul`, `Cslib.BitString.dens_oddPairs`: the masked average is
  `(1 - 2⁻ⁿ) / 2` times the conditional average over the odd pairs.
* `Cslib.BitString.le_two_mul_expect_ite_of_forall`: a bound over the strings `c` with `a · c = 1`
  bounds twice the masked average.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exactly half the strings have odd inner product with a fixed nonzero string. -/
theorem dens_oddFiber {a : ι → Bool} (ha : a ≠ 0) :
    (((univ.filter fun b => a ⬝ᵥ b = true).dens : ℚ≥0) : ℝ) = 1 / 2 := by
  set S := (univ : Finset (ι → Bool)).filter fun c => a ⬝ᵥ c = true
  have hcard : 2 * (S.card : ℝ) = Fintype.card (ι → Bool) := by
    have hc := two_mul_card_dotProduct_eq_true_add a
    simp only [ha, ↓reduceIte, add_zero] at hc
    rw [Fintype.card_fun, Fintype.card_bool]
    exact_mod_cast hc
  have hpos : (0 : ℝ) < Fintype.card (ι → Bool) := by exact_mod_cast Fintype.card_pos
  rw [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast, ← hcard]
  have hS : (S.card : ℝ) ≠ 0 := by linarith
  field_simp

/-- Every nonzero string has a partner with odd inner product. -/
theorem oddFiber_nonempty {a : ι → Bool} (ha : a ≠ 0) :
    (univ.filter fun b => a ⬝ᵥ b = true).Nonempty := by
  by_contra! h
  have hd := dens_oddFiber ha
  norm_num [h] at hd

/-- A nonzero bit string gives a bound holding on its odd partners, which then holds
for twice the masked average over all partners. -/
theorem le_two_mul_expect_ite_of_forall {a : ι → Bool} (ha : a ≠ 0) {g : ℝ}
    {h : (ι → Bool) → ℝ} (hg : ∀ c, a ⬝ᵥ c = true → g ≤ h c) :
    g ≤ 2 * 𝔼 c, if a ⬝ᵥ c = true then h c else 0 := by
  let S := (univ : Finset (ι → Bool)).filter fun c => a ⬝ᵥ c = true
  have hmask : (𝔼 c, if a ⬝ᵥ c = true then h c else 0) = (1 / 2 : ℝ) * 𝔼 c ∈ S, h c := by
    simp_rw [show ∀ c, (a ⬝ᵥ c = true) ↔ c ∈ S from fun c => by simp [S]]
    rw [Fintype.expect_ite_mem, NNRat.smul_def, dens_oddFiber ha]
  rw [hmask]
  linarith [Finset.le_expect (oddFiber_nonempty ha) fun c hc => hg c (mem_filter.mp hc).2]

/-- The **odd pairs** `(a, b)` of bit strings, with `a · b = 1`. -/
def oddPairs (ι : Type*) [Fintype ι] [DecidableEq ι] : Finset ((ι → Bool) × (ι → Bool)) :=
  univ.filter fun p => p.1 ⬝ᵥ p.2 = true

/-- A pair is odd exactly when its bitwise inner product is one. -/
@[simp] theorem mem_oddPairs {p : (ι → Bool) × (ι → Bool)} :
    p ∈ oddPairs ι ↔ p.1 ⬝ᵥ p.2 = true := by
  simp [oddPairs]

/-- A nonempty index type has an odd pair: take the same one-hot string twice. -/
theorem oddPairs_nonempty [Nonempty ι] : Nonempty ↥(oddPairs ι) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨⟨(Pi.single i true, Pi.single i true), mem_oddPairs.mpr (by simp; rfl)⟩⟩

/-- The odd pairs have density `(1 - 2⁻ⁿ) / 2` among all pairs of `n`-bit strings; for `n = 0` there
are none. -/
theorem dens_oddPairs : ((oddPairs ι).dens : ℝ) = (1 - ((2 : ℝ) ^ Fintype.card ι)⁻¹) / 2 := by
  have hN : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  rw [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_bool]
  have hc' : 2 * ((oddPairs ι).card : ℝ) + 2 ^ Fintype.card ι =
      2 ^ Fintype.card ι * 2 ^ Fintype.card ι := by
    exact_mod_cast two_mul_card_dotProduct_eq_true_add_two_pow (ι := ι)
  push_cast
  field_simp
  linarith

/-- The **masked average over the odd pairs**: `E_{a,b} [a · b = 1] f(a, b)`. -/
noncomputable def oddExpect (f : (ι → Bool) → (ι → Bool) → ℝ) : ℝ :=
  𝔼 a, 𝔼 b, if a ⬝ᵥ b = true then f a b else 0

theorem oddExpect_def (f : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect f = 𝔼 a, 𝔼 b, if a ⬝ᵥ b = true then f a b else 0 := by
  unfold oddExpect
  rfl

variable {f g : (ι → Bool) → (ι → Bool) → ℝ}

theorem oddExpect_mono (h : ∀ a b, a ⬝ᵥ b = true → f a b ≤ g a b) :
    oddExpect f ≤ oddExpect g := by
  rw [oddExpect_def, oddExpect_def]
  exact expect_le_expect fun a _ => expect_le_expect fun b _ => by
    split_ifs with hab
    exacts [h a b hab, le_rfl]

theorem oddExpect_nonneg (h : ∀ a b, a ⬝ᵥ b = true → 0 ≤ f a b) : 0 ≤ oddExpect f := by
  simpa [oddExpect_def] using oddExpect_mono (f := fun _ _ => 0) h

/-- At most half of all pairs have odd inner product. -/
theorem dens_oddPairs_le_half : ((oddPairs ι).dens : ℝ) ≤ 1 / 2 := by
  rw [dens_oddPairs]
  linarith [show 0 ≤ ((2 : ℝ) ^ Fintype.card ι)⁻¹ by positivity]

/-- The masked average is the density of the odd pairs times the conditional average over them. -/
theorem oddExpect_eq_dens_smul (f : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect f = ((oddPairs ι).dens : ℝ) * 𝔼 p ∈ oddPairs ι, f p.1 p.2 := by
  rw [oddExpect_def, ← Finset.expect_product' univ univ (fun a b =>
    if a ⬝ᵥ b = true then f a b else 0), Finset.univ_product_univ]
  simp_rw [← mem_oddPairs]
  rw [Fintype.expect_ite_mem, NNRat.smul_def]

/-- The masked average is the density times the uniform average on the subtype of odd pairs. -/
theorem oddExpect_eq_dens_mul_expect (f : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect f = ((oddPairs ι).dens : ℝ) * (𝔼 p : ↥(oddPairs ι), f p.val.1 p.val.2) := by
  rw [oddExpect_eq_dens_smul, univ_eq_attach]
  congr 1
  rw [Finset.expect, Finset.expect, card_attach,
    sum_attach (oddPairs ι) (fun p => f p.1 p.2)]

/-- The first marginal of the masked odd-pair average is half the uniform
average with the zero string removed by a mask. -/
theorem oddExpect_fst (g : (ι → Bool) → ℝ) :
    oddExpect (fun a _ => g a) = (1 / 2 : ℝ) * 𝔼 a, if a = 0 then 0 else g a := by
  rw [oddExpect_def, Finset.mul_expect]
  refine expect_congr rfl fun a _ => ?_
  by_cases ha : a = 0
  · simp [ha]
  simp only [ha, ite_false]
  let S := (univ : Finset (ι → Bool)).filter fun b => a ⬝ᵥ b = true
  simp_rw [show ∀ b, (a ⬝ᵥ b = true) ↔ b ∈ S by simp [S]]
  rw [Fintype.expect_ite_mem, NNRat.smul_def, dens_oddFiber ha,
    Finset.expect_const (oddFiber_nonempty ha)]

/-- Swapping the two coordinates preserves the masked odd-pair average. -/
theorem oddExpect_swap (g : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect (fun a b => g b a) = oddExpect g := by
  rw [oddExpect_def, oddExpect_def, Finset.expect_comm]
  exact expect_congr rfl fun a _ => expect_congr rfl fun b _ => by rw [dotProduct_comm b a]

/-- The second marginal has the same distribution as the first. -/
theorem oddExpect_snd (g : (ι → Bool) → ℝ) :
    oddExpect (fun _ b => g b) = (1 / 2 : ℝ) * 𝔼 b, if b = 0 then 0 else g b := by
  rw [oddExpect_swap (fun a _ => g a), oddExpect_fst]

/-- Recover the uniform average from the masked first marginal and the contribution at zero. -/
theorem expect_eq_two_mul_oddExpect_fst_add_zero (g : (ι → Bool) → ℝ) :
    (𝔼 a, g a) = 2 * oddExpect (fun a _ => g a) + g 0 / Fintype.card (ι → Bool) := by
  rw [show (𝔼 a, g a) = (𝔼 a, if a = 0 then 0 else g a) + (𝔼 a, if a = 0 then g a else 0) by
      rw [← Finset.expect_add_distrib]
      exact expect_congr rfl fun _ _ => by split_ifs <;> simp,
    oddExpect_fst, Fintype.expect_ite_eq']
  simp only [NNRat.smul_def, NNRat.cast_inv, NNRat.cast_natCast, div_eq_inv_mul]
  ring

theorem oddExpect_add (f g : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect (fun a b => f a b + g a b) = oddExpect f + oddExpect g := by
  simp only [oddExpect_def, ← expect_add_distrib]
  refine expect_congr rfl fun a _ => expect_congr rfl fun b _ => ?_
  split_ifs <;> ring

theorem oddExpect_const_mul (r : ℝ) (f : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect (fun a b => r * f a b) = r * oddExpect f := by
  simp only [oddExpect_def, mul_expect]
  refine expect_congr rfl fun a _ => expect_congr rfl fun b _ => ?_
  split_ifs <;> ring

end Cslib.BitString
