/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Noise
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.ExpectPi

/-!
# Noise sensitivity from total influence

For a Boolean function `f` on `ι`, a string `z` and a map `π : ι → Fin m` partitioning the
coordinates into `m` blocks, let `g_{z, π}(w) = f (z + w ∘ π)` on `m` bits: `f` with the variables
of each block identified and those selected by `z` negated. Negating the block of a uniformly
random `j` in a uniformly random `w` flips each coordinate of `z + w ∘ π` independently with
probability `1 / m` when `z` and `π` are uniformly random as well, so the noise sensitivity of `f`
at `1 / m` is the average over `z` and `π` of the average influence `I[g_{z, π}] / m`
(`BitString.noiseSensitivity_inv_eq_expect_totalInfluence`). The mask `i ↦ φ (π i)` of a uniformly
random map `π` has independent coordinates, each selected with probability `Pr_c [φ c]`
(`BitString.expect_comp_eq_bernoulliAverage`).

Consequently, if every `g_{z, π}` with `m = ⌊1 / δ⌋` blocks has total influence at most `A`, then
`NS_δ[f] ≤ A / m` for `0 < δ ≤ 1 / 2` (`BitString.noiseSensitivity_le_div_of_totalInfluence_le`).
For a class of functions closed under negating input variables, identifying them and adding
dummy variables, each of whose members on `m` bits has total influence at most `A(m)`, the
functions `g_{z, π}` of a member are members, so every member has `NS_δ[f] ≤ A(m) / m`
(`BitString.noiseSensitivity_le_div_of_comp_add_comp_mem`) [O'Donnell, Theorem 5.35][ODonnell2014].
The book states Theorem 5.35 for classes closed under negation and identification only; its proof
also uses the functions `g_{z, π}` with `π` not onto, which have dummy variables, so it uses
closure under adding dummy variables implicitly. Without it the statement fails: the class
`{χ₁, -χ₁}` of functions on one bit is closed under negation and identification, and with
`A(1) = 1` and `A(m) = 0` for `m ≥ 2` it would give `NS_{1/4}[χ₁] ≤ 0`, while
`NS_{1/4}[χ₁] = 1/4`.

## Main results

* `Cslib.BitString.expect_comp_eq_bernoulliAverage`: the mask `i ↦ φ (π i)` of a uniformly random
  map `π` is a Bernoulli mask.
* `Cslib.BitString.noiseSensitivity_inv_eq_expect_totalInfluence`: `NS_{1/m}[f]` is the average of
  `I[g_{z, π}] / m`.
* `Cslib.BitString.noiseSensitivity_le_div_of_totalInfluence_le`: noise sensitivity from the total
  influence of the functions `g_{z, π}`.
* `Cslib.BitString.noiseSensitivity_le_div_of_comp_add_comp_mem`: noise sensitivity from total
  influence for a class closed under negating, identifying and adding dummy input variables.

## Usage

Open `Cslib.BitString`. The function `g_{z, π}` is written `fun w => f (z + fun i => w (π i))`
for `z : ι → Bool` and `π : ι → Fin m`; `Cslib.BitString.IsPTF.comp_add_comp` shows that it is
again a polynomial threshold function of the same degree. In
`Cslib.BitString.noiseSensitivity_le_div_of_comp_add_comp_mem` the class is a family `B n` of
functions on `Fin n → Bool`, closed under every `f ↦ g_{z, π}`, including maps `π` that are not
surjective (the unused variables are dummies). Negation (`π` the identity) and identification
(`z = 0`, `π` onto) are special cases; composing them gives `g_{z, π}` only for `π` onto, and the
remaining maps also add dummy variables. For a single function on
any finite type, with a bound on its own functions `g_{z, π}`, use
`Cslib.BitString.noiseSensitivity_le_div_of_totalInfluence_le`.
`CslibFrontier.Foundations.BooleanAnalysis.Peres` applies the class form to linear threshold
functions.

The checked clients in
[CslibFrontierTests/BooleanAnalysisPeres.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisPeres.lean)
apply the exact identity to the majority of three bits at `m = 2`, the class form with
`A(m) = √m` at `δ = 1 / 3`, the single-function form to `¬x₀ ∧ x₁`, and check that a random map
to `Fin 4` puts a coordinate in block `0` with probability `1 / 4`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A predicate of a uniformly random map is a Bernoulli mask**: for a uniformly random map
`π : ι → κ`, the mask `i ↦ φ (π i)` selects the coordinates independently, each with the
probability `Pr_c [φ c]` that `φ` holds at a uniformly random `c`. -/
theorem expect_comp_eq_bernoulliAverage {κ : Type*} [Fintype κ] [Nonempty κ] (φ : κ → Bool)
    (h : (ι → Bool) → ℝ) :
    𝔼 π : ι → κ, h (fun i => φ (π i)) = bernoulliAverage (dens {c | φ c} : ℝ) h := by
  have hc (b : Bool) : 𝔼 c, (if φ c = b then (1 : ℝ) else 0) =
      if b then (dens {c | φ c} : ℝ) else 1 - dens {c | φ c} := by
    have h1 := Fintype.expect_boole (𝕜 := ℝ) fun c => φ c = true
    cases b
    · rw [expect_congr rfl fun c _ => show (if φ c = false then (1 : ℝ) else 0) =
          1 - if φ c = true then 1 else 0 by cases φ c <;> norm_num,
        expect_sub_distrib, h1, Fintype.expect_const]
      rfl
    · exact h1
  calc 𝔼 π : ι → κ, h (fun i => φ (π i))
      = 𝔼 π : ι → κ, ∑ a, h a * ∏ i, (if φ (π i) = a i then (1 : ℝ) else 0) :=
        expect_congr rfl fun _ _ => by
          simp only [prod_boole, mem_univ, forall_const, ← funext_iff, mul_ite, mul_one, mul_zero]
          rw [Fintype.sum_ite_eq]
    _ = ∑ a, h a * ∏ i, 𝔼 c, (if φ c = a i then (1 : ℝ) else 0) := by
        rw [expect_sum_comm]
        exact sum_congr rfl fun a _ => by
          rw [← mul_expect, ← Fintype.prod_expect fun i c => if φ c = a i then (1 : ℝ) else 0]
    _ = bernoulliAverage (dens {c | φ c} : ℝ) h := by
        simp only [hc, bernoulliAverage, bernoulliWeight, mul_comm (h _)]

omit [Fintype ι] [DecidableEq ι] in
/-- Negating block `j` of `w` negates the coordinates of `w ∘ π` in the preimage of `j`. -/
private theorem comp_update_not {m : ℕ} (w : Fin m → Bool) (π : ι → Fin m) (j : Fin m) :
    (fun i => Function.update w j (!w j) (π i)) =
      (fun i => w (π i)) + fun i => decide (π i = j) := by
  funext i
  rw [Pi.add_apply, Bool.add_eq_xor]
  by_cases h : π i = j <;> simp [h]

/-- **Noise sensitivity as average influence** [O'Donnell, proof of Theorem 5.35][ODonnell2014]:
the noise sensitivity of `f` at `1 / m` is the average, over uniformly random strings `z` and maps
`π : ι → Fin m`, of `1 / m` times the total influence of `g_{z, π}(w) = f (z + w ∘ π)`, the
function of `m` bits obtained from `f` by identifying the variables in each block of `π` and
negating those selected by `z`. -/
theorem noiseSensitivity_inv_eq_expect_totalInfluence (f : (ι → Bool) → Bool) (m : ℕ) :
    noiseSensitivity (m : ℝ)⁻¹ f =
      (m : ℝ)⁻¹ * 𝔼 z : ι → Bool, 𝔼 π : ι → Fin m,
        totalInfluence fun w : Fin m → Bool => signVal (f (z + fun i => w (π i))) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, inv_zero, noiseSensitivity_zero, zero_mul]
  have : NeZero m := ⟨hm.ne'⟩
  -- The probability that the noise `P` changes the value of `f` at a uniformly random point.
  set H : (ι → Bool) → ℝ := fun P => 𝔼 x, if f x ≠ f (x + P) then 1 else 0
  -- The influence of block `j` on `g_{z, π}` is the probability that negating it changes `f`.
  have hinf (z : ι → Bool) (π : ι → Fin m) :
      totalInfluence (fun w : Fin m → Bool => signVal (f (z + fun i => w (π i)))) =
        ∑ j, 𝔼 w : Fin m → Bool, (if f (z + fun i => w (π i)) ≠
          f ((z + fun i => w (π i)) + fun i => decide (π i = j)) then 1 else 0) :=
    sum_congr rfl fun j _ => by
      rw [influence_signVal]
      refine expect_congr rfl fun w _ => ?_
      rw [comp_update_not, ← add_assoc]
      by_cases h : f ((z + fun i => w (π i)) + fun i => decide (π i = j)) =
          f (z + fun i => w (π i)) <;>
        simp only [h, Ne.symm, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]
  -- Averaging over `z` first, the translate `z + w ∘ π` of `z` is uniformly random.
  have htrans (π : ι → Fin m) :
      𝔼 z : ι → Bool, totalInfluence
          (fun w : Fin m → Bool => signVal (f (z + fun i => w (π i)))) =
        ∑ j, H (fun i => decide (π i = j)) := by
    simp only [hinf, expect_sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [expect_comm]
    refine (expect_congr rfl fun w _ => ?_).trans (Fintype.expect_const _)
    exact Fintype.expect_equiv (Equiv.addRight fun i => w (π i)) _ _ fun _ => rfl
  have hNS : noiseSensitivity (m : ℝ)⁻¹ f = bernoulliAverage (m : ℝ)⁻¹ H :=
    (bernoulliAverage_expect_comm univ _ fun P x => if f x ≠ f (x + P) then (1 : ℝ) else 0).symm
  rw [hNS, expect_comm, expect_congr rfl fun π _ => htrans π, expect_sum_comm]
  -- The preimage of a block of a uniformly random map is a mask of rate `1 / m`.
  have hblock (j : Fin m) :
      𝔼 π : ι → Fin m, H (fun i => decide (π i = j)) = bernoulliAverage (m : ℝ)⁻¹ H := by
    rw [expect_comp_eq_bernoulliAverage (fun c : Fin m => decide (c = j)) H]
    congr 1
    simp [filter_eq', dens_singleton]
  simp only [hblock, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Noise sensitivity from the total influence of the functions `g_{z, π}`**: for
`0 < δ ≤ 1 / 2` and `m = ⌊1 / δ⌋`, if each function `g_{z, π}(w) = f (z + w ∘ π)` of `m` bits,
obtained from `f` by negating and identifying input variables, has total influence at most `A`,
then `NS_δ[f] ≤ A / m`. This is the argument of [O'Donnell, Theorem 5.35][ODonnell2014] for a
single function; the book's statement for a class is
`BitString.noiseSensitivity_le_div_of_comp_add_comp_mem`. -/
theorem noiseSensitivity_le_div_of_totalInfluence_le {δ A : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (f : (ι → Bool) → Bool)
    (hA : ∀ (z : ι → Bool) (π : ι → Fin ⌊δ⁻¹⌋₊),
      totalInfluence (fun w : Fin ⌊δ⁻¹⌋₊ → Bool => signVal (f (z + fun i => w (π i)))) ≤ A) :
    noiseSensitivity δ f ≤ A / ⌊δ⁻¹⌋₊ := by
  set m := ⌊δ⁻¹⌋₊
  have hm2 : 2 ≤ m := Nat.le_floor (by rw [Nat.cast_ofNat, le_inv_comm₀ two_pos hδ]; linarith)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have : NeZero m := ⟨by omega⟩
  have hδm : δ ≤ (m : ℝ)⁻¹ := (le_inv_comm₀ hδ hmpos).2 (Nat.floor_le (inv_nonneg.2 hδ.le))
  calc noiseSensitivity δ f
      ≤ noiseSensitivity (m : ℝ)⁻¹ f :=
        noiseSensitivity_mono hδm (one_div (2 : ℝ) ▸ inv_anti₀ two_pos (by exact_mod_cast hm2)) f
    _ = (m : ℝ)⁻¹ * 𝔼 z : ι → Bool, 𝔼 π : ι → Fin m,
        totalInfluence fun w : Fin m → Bool => signVal (f (z + fun i => w (π i))) :=
      noiseSensitivity_inv_eq_expect_totalInfluence f m
    _ ≤ A / m := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left
        (expect_le univ_nonempty fun z _ => expect_le univ_nonempty fun π _ => hA z π)
        (inv_nonneg.2 hmpos.le)

/-- **Noise sensitivity from total influence** [O'Donnell, Theorem 5.35][ODonnell2014]: let `B` be
a class of Boolean functions, `B n` on `n` bits, closed under negating, identifying and adding
dummy input variables, whose members on `n` bits have total influence at most `A n`. Then for
`0 < δ ≤ 1 / 2` and `m = ⌊1 / δ⌋`, every member `f` of `B` has `NS_δ[f] ≤ A(m) / m`. Closure is
asked for the maps `f ↦ (w ↦ f (z + w ∘ π))` with arbitrary `z` and `π : Fin n → Fin m`; `π`
need not be surjective, so the unused variables of `w` are dummies. The book asks only for
closure under negation and identification, but its proof uses these maps for every `π`, and the
statement fails without closure under adding dummy variables (see the module docstring). -/
theorem noiseSensitivity_le_div_of_comp_add_comp_mem {B : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop}
    {A : ℕ → ℝ} (hB : ∀ {n m : ℕ} {f : (Fin n → Bool) → Bool} (z : Fin n → Bool)
      (π : Fin n → Fin m), B n f → B m fun w => f (z + fun i => w (π i)))
    (hA : ∀ {n : ℕ} {f : (Fin n → Bool) → Bool}, B n f →
      totalInfluence (fun x => signVal (f x)) ≤ A n)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : B n f) :
    noiseSensitivity δ f ≤ A ⌊δ⁻¹⌋₊ / ⌊δ⁻¹⌋₊ :=
  noiseSensitivity_le_div_of_totalInfluence_le hδ hδ' f fun z π => hA (hB z π hf)

end Cslib.BitString
