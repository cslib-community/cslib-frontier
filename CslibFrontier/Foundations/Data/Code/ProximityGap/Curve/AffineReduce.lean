/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.Internal
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Generic Affine-Space-to-Curve and Line-to-Affine Reductions

Fiber-averaging reductions over finite fields `F`: lifts a parameterized-curve correlated agreement
bound into an affine space via the `(Fˣ)^ℓ × Fˣ` bijection
(`exists_correlatedAgreement_affine_of_curve`) and lifts a line dichotomy into a
dimension-independent affine proximity gap (`proximityGap_affine_of_line`).

## Main results

* `Cslib.Code.exists_correlatedAgreement_affine_of_curve`: affine-to-curve fiber averaging.
* `Cslib.Code.proximityGap_affine_of_line`: dimension-independent line-to-affine dichotomy.
-/

public section

namespace Cslib.Code

open scoped BigOperators
open Finset Polynomial

/-- **Generic affine-space-to-curve correlated agreement reduction**:

Given any degree-`ℓ` curve correlated-agreement theorem `hcurve` with scalar threshold `B_curve`
for a pointwise proximity predicate `P : (ι → F) → Prop` and shared-agreement predicate
`Q : Finset ι → Prop`, any affine space `u₀ + ∑ j : Fin ℓ, z j • u j` (`1 ≤ ℓ`) over a finite
field `F` whose good set `T ⊆ (Fin ℓ → F)` satisfies `(B_curve + ℓ) * |F| ^ (ℓ - 1) < #T`
(density strictly greater than `(B_curve + ℓ) / |F|`, linear in `ℓ`) admits a single shared
agreement set `D'` satisfying `Q D'` together with codewords `v₀, v j ∈ reedSolomon α k`.

The proof excludes tuples with a zero coordinate (at most `ℓ * |F| ^ (ℓ - 1)` tuples), averages
over the fiber bijection `(a, t) ↦ (a j * t ^ (j + 1))_j` on `(Fin ℓ → Fˣ) × Fˣ`, applies
`hcurve` along the resulting degree-`ℓ` curve `u₀ + ∑ j, t ^ (j + 1) • (a j • u j)`, and
unscales each recovered codeword by `(a j)⁻¹`. -/
theorem exists_correlatedAgreement_affine_of_curve
    {F : Type*} [Field F] [Fintype F]
    {ι : Type*}
    {α : ι → F} {k ℓ B_curve : ℕ}
    (hℓ : 1 ≤ ℓ)
    {P : (ι → F) → Prop} {Q : Finset ι → Prop}
    (hcurve : ∀ (u' : Fin (ℓ + 1) → (ι → F)) (S : Finset F),
      B_curve < S.card →
      (∀ z ∈ S, P (∑ j : Fin (ℓ + 1), z ^ (j : ℕ) • u' j)) →
      ∃ D' : Finset ι, Q D' ∧
        ∃ v' : Fin (ℓ + 1) → (ι → F), (∀ j, v' j ∈ reedSolomon α k) ∧
          ∀ i ∈ D', ∀ j, u' j i = v' j i)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : (B_curve + ℓ) * (Fintype.card F) ^ (ℓ - 1) < T.card)
    (hclose : ∀ z ∈ T, P (u₀ + ∑ j : Fin ℓ, z j • u j)) :
    ∃ D' : Finset ι, Q D' ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F),
        (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  classical
  let T_nz : Finset (Fin ℓ → F) := T.filter fun z => ∀ j : Fin ℓ, z j ≠ 0
  have hzero_le : (T \ T_nz).card ≤ ℓ * (Fintype.card F) ^ (ℓ - 1) := by
    have hsub : T \ T_nz ⊆ (Finset.univ : Finset (Fin ℓ)).biUnion
        fun j => Finset.univ.filter fun z : Fin ℓ → F => z j = 0 := fun z hz => by
      simp only [T_nz, mem_sdiff, mem_filter, not_and, not_forall, not_not] at hz
      simpa using hz.2 hz.1
    exact (Finset.card_le_card hsub).trans <| Finset.card_biUnion_le.trans_eq <|
      (Finset.sum_congr rfl fun j _ => card_filter_coord_eq_zero j).trans <| by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hT_nz : B_curve * (Fintype.card F) ^ (ℓ - 1) < T_nz.card := by
    have : (T \ T_nz).card + T_nz.card = T.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ T)
    rw [Nat.add_mul] at hT; omega
  have hT_nz_units : B_curve * (Fintype.card Fˣ) ^ ℓ < Fintype.card Fˣ * T_nz.card := by
    rw [← mul_pow_sub_one (by omega : ℓ ≠ 0), mul_left_comm]
    refine Nat.mul_lt_mul_of_pos_left (lt_of_le_of_lt ?_ hT_nz) Fintype.card_pos
    gcongr
    exact Fintype.card_le_of_injective _ Units.val_injective
  let phi : (Fin ℓ → Fˣ) → Fˣ → (Fin ℓ → F) := fun a t j => (a j : F) * (t : F) ^ ((j : ℕ) + 1)
  have hfiber (t : Fˣ) : (Finset.univ.filter fun a : Fin ℓ → Fˣ => phi a t ∈ T_nz).card =
      T_nz.card :=
    Finset.card_bij (fun a _ => phi a t) (fun _ ha => (mem_filter.1 ha).2)
      (fun _ _ _ _ heq => funext fun j => Units.ext <|
        mul_right_cancel₀ (pow_ne_zero _ t.ne_zero) (congrFun heq j))
      fun z hz =>
        let a : Fin ℓ → Fˣ := fun j =>
          Units.mk0 (z j) ((mem_filter.1 hz).2 j) * (t ^ ((j : ℕ) + 1))⁻¹
        have hphi : phi a t = z := funext fun j => by
          simp only [phi, a, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val,
            Units.val_pow_eq_pow_val, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ t.ne_zero), mul_one]
        ⟨a, mem_filter.2 ⟨mem_univ a, hphi.symm ▸ hz⟩, hphi⟩
  have hsum_lt : (∑ _a : Fin ℓ → Fˣ, B_curve) <
      ∑ a : Fin ℓ → Fˣ, (Finset.univ.filter fun t : Fˣ => phi a t ∈ T_nz).card := by
    have hsum : (∑ a : Fin ℓ → Fˣ, (Finset.univ.filter fun t : Fˣ => phi a t ∈ T_nz).card) =
        Fintype.card Fˣ * T_nz.card := by
      simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
      simp_rw [← Finset.card_filter, hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      smul_eq_mul, mul_comm]
    exact hT_nz_units
  obtain ⟨a, _, ha_gt⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  let S : Finset F := (Finset.univ.filter fun t : Fˣ => phi a t ∈ T_nz).image Units.val
  let u' : Fin (ℓ + 1) → (ι → F) := Fin.cons u₀ fun j => (a j : F) • u j
  obtain ⟨D', hQD', v', hv'RS, hagree'⟩ := hcurve u' S
    (by rwa [Finset.card_image_of_injective _ Units.val_injective]) fun z hz => by
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hz
      have hsum : (∑ j : Fin (ℓ + 1), (t : F) ^ (j : ℕ) • u' j) =
          u₀ + ∑ j : Fin ℓ, phi a t j • u j := by
        rw [Fin.sum_univ_succ]; simp only [u', Fin.val_zero, pow_zero, one_smul, Fin.cons_zero,
          Fin.val_succ, Fin.cons_succ]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm])
      rw [hsum]; exact hclose (phi a t) (mem_filter.1 (mem_filter.1 ht).2).1
  refine ⟨D', hQD', v' 0, hv'RS 0, fun j => (a j : F)⁻¹ • v' j.succ,
    fun j => Submodule.smul_mem _ _ (hv'RS j.succ), fun i hi =>
      ⟨by simpa only [u', Fin.cons_zero] using hagree' i hi 0, fun j => ?_⟩⟩
  have hs : (a j : F) * u j i = v' j.succ i := by
    simpa only [u', Fin.cons_succ, Pi.smul_apply, smul_eq_mul] using hagree' i hi j.succ
  simp only [Pi.smul_apply, smul_eq_mul, ← hs, inv_mul_cancel_left₀ (a j).ne_zero]

/-- **Generic 1D-line-to-affine-space proximity-gap dichotomy (dimension-independent)**:

Given any pointwise predicate `P : (ι → F) → Prop` satisfying a 1D line dichotomy with threshold
`B_line` (whenever strictly more than `B_line` points on a line `a + t • b` satisfy `P`, every
point on the line satisfies `P`), every `ℓ`-dimensional affine space `u₀ + ∑ j : Fin ℓ, z j • u j`
over a finite field `F` satisfies either:
* every point of the affine space satisfies `P`, or
* `(|F| - 1) * #{z | P (u₀ + ∑ j, z j • u j)} ≤ B_line * (|F| ^ ℓ - 1)`.

For `ℓ = 1` this recovers `#T ≤ B_line` exactly; for all `ℓ ≥ 1` the density bound is at most
`B_line / (|F| - 1)`, completely independent of the dimension `ℓ`. -/
theorem proximityGap_affine_of_line
    {F : Type*} [Field F] [Fintype F]
    {ι : Type*}
    {ℓ B_line : ℕ}
    {P : (ι → F) → Prop}
    (hline : ∀ (a b : ι → F) (S : Finset F),
      B_line < S.card → (∀ t ∈ S, P (a + t • b)) → ∀ t : F, P (a + t • b))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => P (u₀ + ∑ j : Fin ℓ, z j • u j)] :
    (∀ z : Fin ℓ → F, P (u₀ + ∑ j : Fin ℓ, z j • u j)) ∨
      (Fintype.card F - 1) *
        (Finset.univ.filter fun z : Fin ℓ → F => P (u₀ + ∑ j : Fin ℓ, z j • u j)).card ≤
        B_line * ((Fintype.card F) ^ ℓ - 1) := by
  classical
  by_cases hall : ∀ z : Fin ℓ → F, P (u₀ + ∑ j : Fin ℓ, z j • u j)
  · exact Or.inl hall
  · right
    push Not at hall; obtain ⟨y, hy⟩ := hall
    set T := Finset.univ.filter fun z : Fin ℓ → F => P (u₀ + ∑ j : Fin ℓ, z j • u j)
    let B_nz : Finset (Fin ℓ → F) := Finset.univ.erase 0
    have hB_nz_card : B_nz.card = (Fintype.card F) ^ ℓ - 1 := by
      rw [Finset.card_erase_of_mem (mem_univ 0), Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin]
    let pairs := (B_nz ×ˢ (Finset.univ : Finset Fˣ)).filter fun p => y + (p.2 : F) • p.1 ∈ T
    have hpairs_eq : pairs.card = (Fintype.card F - 1) * T.card := by
      have hbij : pairs.card = (T ×ˢ (Finset.univ : Finset Fˣ)).card :=
        Finset.card_bij (fun p _ => (y + (p.2 : F) • p.1, p.2))
          (fun p hp => mem_product.2 ⟨(mem_filter.1 hp).2, mem_univ p.2⟩)
          (fun p₁ _ p₂ _ heq => by
            obtain ⟨h1, h2⟩ := Prod.mk.inj heq; rw [h2] at h1
            exact Prod.ext (funext fun j => mul_left_cancel₀ p₂.2.ne_zero
              (congrFun (add_left_cancel h1) j)) h2)
          fun q hq => by
            let b : Fin ℓ → F := ((q.2⁻¹ : Fˣ) : F) • (q.1 - y)
            have hyb : y + (q.2 : F) • b = q.1 := by
              simp only [b, smul_smul, Units.mul_inv, one_smul, add_sub_cancel]
            have hb_ne : b ≠ 0 := fun h0 => hy <| (mem_filter.1 (mem_product.1 hq).1).2 |>
              fun hp => (by simpa only [h0, smul_zero, add_zero] using hyb) ▸ hp
            exact ⟨(b, q.2), mem_filter.2 ⟨mem_product.2 ⟨mem_erase.2 ⟨hb_ne, mem_univ _⟩,
              mem_univ _⟩, hyb.symm ▸ (mem_product.1 hq).1⟩, Prod.ext hyb rfl⟩
      rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_units, Nat.mul_comm]
    have hline_eval (b : Fin ℓ → F) (t : F) : u₀ + ∑ j : Fin ℓ, (y + t • b) j • u j =
        (u₀ + ∑ j : Fin ℓ, y j • u j) + t • (∑ j : Fin ℓ, b j • u j) := by
      funext i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]
    have hfiber_le (b : Fin ℓ → F) :
        ((Finset.univ : Finset Fˣ).filter fun t : Fˣ => y + (t : F) • b ∈ T).card ≤ B_line := by
      by_contra hgt
      set S := ((Finset.univ : Finset Fˣ).filter fun t : Fˣ => y + (t : F) • b ∈ T).image Units.val
      have h0 := hline _ (∑ j : Fin ℓ, b j • u j) S
        (by rw [Finset.card_image_of_injective _ Units.val_injective]; omega)
        (fun t ht => by
          obtain ⟨tu, htu, rfl⟩ := mem_image.1 ht
          exact (hline_eval b tu) ▸ (mem_filter.1 (mem_filter.1 htu).2).2) 0
      exact hy (by rwa [zero_smul, add_zero] at h0)
    have hsum_eq : pairs.card = ∑ b ∈ B_nz,
        ((Finset.univ : Finset Fˣ).filter fun t : Fˣ => y + (t : F) • b ∈ T).card := by
      rw [Finset.card_filter, Finset.sum_product]; simp_rw [Finset.card_filter]
    have hpairs_le := hsum_eq ▸ (Finset.sum_le_sum fun b _ => hfiber_le b).trans_eq (by
      rw [Finset.sum_const, smul_eq_mul, hB_nz_card, Nat.mul_comm])
    omega

end Cslib.Code
