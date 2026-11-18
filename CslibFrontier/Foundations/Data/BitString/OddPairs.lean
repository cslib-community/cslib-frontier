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
`Cslib.BitString.oddExpect_const_mul`).

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

/-- A nonzero bit string `a` gives a bound `g ≤ h(c)` for every `c` with `a · c = 1`, the half of
the strings with odd inner product; then `g ≤ 2 E_c [a · c = 1] h(c)`. -/
theorem le_two_mul_expect_ite_of_forall {a : ι → Bool} (ha : a ≠ 0) {g : ℝ}
    {h : (ι → Bool) → ℝ} (hg : ∀ c, a ⬝ᵥ c = true → g ≤ h c) :
    g ≤ 2 * 𝔼 c, if a ⬝ᵥ c = true then h c else 0 := by
  set S := (univ : Finset (ι → Bool)).filter fun c => a ⬝ᵥ c = true
  have hcard : 2 * (S.card : ℝ) = Fintype.card (ι → Bool) := by
    have hc := two_mul_card_dotProduct_eq_true_add a
    simp only [ha, ↓reduceIte, add_zero] at hc
    rw [Fintype.card_fun, Fintype.card_bool]
    exact_mod_cast hc
  have hS : S.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Fintype.card (ι → Bool) := by exact_mod_cast Fintype.card_pos
    exact_mod_cast (by linarith : (0 : ℝ) < S.card)
  have hdens : (S.dens : ℝ) = 1 / 2 := by
    have hS0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
    rw [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast, ← hcard]
    field_simp
  have hmask : (𝔼 c, if a ⬝ᵥ c = true then h c else 0) = (1 / 2 : ℝ) * 𝔼 c ∈ S, h c := by
    simp_rw [show ∀ c, (a ⬝ᵥ c = true) ↔ c ∈ S from fun c => by simp [S]]
    rw [Fintype.expect_ite_mem, NNRat.smul_def, hdens]
  rw [hmask]
  linarith [Finset.le_expect hS fun c hc => hg c (mem_filter.mp hc).2]

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
  let u : ι → Bool := Pi.single i true
  refine ⟨⟨(u, u), mem_oddPairs.mpr ?_⟩⟩
  simpa [u] using (show true * true = true from rfl)

/-- The odd pairs have density `(1 - 2⁻ⁿ) / 2` among all pairs of `n`-bit strings; for `n = 0` there
are none. -/
theorem dens_oddPairs : ((oddPairs ι).dens : ℝ) = (1 - ((2 : ℝ) ^ Fintype.card ι)⁻¹) / 2 := by
  have hc := two_mul_card_dotProduct_eq_true_add_two_pow (ι := ι)
  have hN : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  rw [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_bool]
  have hc' : 2 * ((oddPairs ι).card : ℝ) + 2 ^ Fintype.card ι =
      2 ^ Fintype.card ι * 2 ^ Fintype.card ι := by exact_mod_cast hc
  push_cast
  field_simp
  linarith

/-- The **masked average over the odd pairs**: `E_{a,b} [a · b = 1] f(a, b)`. -/
noncomputable def oddExpect (f : (ι → Bool) → (ι → Bool) → ℝ) : ℝ :=
  𝔼 a, 𝔼 b, if a ⬝ᵥ b = true then f a b else 0

theorem oddExpect_def (f : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect f = 𝔼 a, 𝔼 b, if a ⬝ᵥ b = true then f a b else 0 := by
  unfold oddExpect; rfl

variable {f g : (ι → Bool) → (ι → Bool) → ℝ}

theorem oddExpect_mono (h : ∀ a b, a ⬝ᵥ b = true → f a b ≤ g a b) :
    oddExpect f ≤ oddExpect g := by
  rw [oddExpect_def, oddExpect_def]
  exact expect_le_expect fun a _ => expect_le_expect fun b _ => by
    split_ifs with hab
    · exact h a b hab
    · exact le_rfl

theorem oddExpect_nonneg (h : ∀ a b, a ⬝ᵥ b = true → 0 ≤ f a b) : 0 ≤ oddExpect f := by
  have h0 := oddExpect_mono (f := fun _ _ => 0) h
  rwa [oddExpect_def (fun _ _ => 0), show (𝔼 a : ι → Bool, 𝔼 b : ι → Bool,
    if a ⬝ᵥ b = true then (0 : ℝ) else 0) = 0 by simp] at h0

/-- The masked average is the density of the odd pairs times the conditional average over them. -/
theorem oddExpect_eq_dens_smul (f : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect f = ((oddPairs ι).dens : ℝ) * 𝔼 p ∈ oddPairs ι, f p.1 p.2 := by
  rw [oddExpect_def, ← Finset.expect_product' univ univ (fun a b =>
    if a ⬝ᵥ b = true then f a b else 0), Finset.univ_product_univ]
  simp_rw [← mem_oddPairs]
  rw [Fintype.expect_ite_mem, NNRat.smul_def]

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
