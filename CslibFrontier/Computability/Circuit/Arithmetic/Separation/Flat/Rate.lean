/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.GridSum
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.NetworkPolynomial
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.Convexity
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.CubeEndPoints
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.LowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.NetworkProjection
import CslibFrontier.Foundations.Analysis.Normed.Module.Basic
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.BorderCover
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# The rate in the flat case: Proposition E.10 and Theorem E.11

Proposition E.10 of [AnthropicVPVNP2026] repeats the proof of Proposition E.5
(`Flat.networkPolynomial_size_ge`) with an explicit rate. The ends of the wires stand at facet
centres of the cube `[-1/2, 1/2] ^ k` (`Flat.cubeEndPoint`), with two hubs `±x` for every balanced
set of nodes (`Flat.exists_norm_eq_sum_dist_cubeEndPoint_le`). The spectral point is that of
Proposition E.9 (`Flat.exists_spectralPoint_cube`): its scaled wire exponents are the distances up
to `δ = 1 / (1000 k)`, and its scaled unit exponent at the ends is at most `√k + δ`. The cover of
the network tensor by the hub tensors (`Flat.networkTensor_coveredBy_hubTensor`) enters through
Lemma E.7, the lemma on sums with few terms
(`PartyTensor.SpectralPoint.apply_le_of_borderCoveredBy`), in which the at most `2 ^ k` balanced
sets cost only `k` times this unit exponent. So in the flat case, for `k ≥ 2` and `ℓ ≥ 100 √k`,
every circuit for `f_{k,ℓ}` has at least `2 ^ (ℓ k^{3/2} / 16)` nodes
(`Flat.networkPolynomial_size_ge_of_sqrt_le`). A circuit for the polynomial in the variables
printed in the paper (`Flat.networkPolynomialOnViews`) is one for `Flat.networkPolynomial` with
the same number of nodes (`Flat.rename_networkPolynomialOnViews`), so the bound holds for it too.

Theorem E.11 applies Proposition E.10 to `k = r²` and `ℓ = 100 r` for the largest `r` with
`200 r³ ≤ ⌊log m⌋` (`Flat.exists_two_rpow_lt_of_networkPolynomial`). With Corollary E.2
(`Flat.isAffineProjection_networkPolynomial`) this gives, for every family `G` complete for grid
sums with blow-up `κ`, an `m₀` depending only on `κ` such that in the flat case every circuit for
`G.poly m`, `m ≥ m₀`, has more than `2 ^ ((log m)^{4/3} / 1600²)` nodes
(`Flat.size_gt_of_gridComplete`). For the permanent this is Theorem E.11
(`TwoCases.FlatCase.perm_size_gt`).

## Main results

* `Flat.networkPolynomial_size_ge_of_sqrt_le`: Proposition E.10.
* `Flat.exists_two_rpow_lt_of_networkPolynomial`: from Proposition E.10 to the bound in `log m`.
* `Flat.size_gt_of_gridComplete`: the flat case for every family complete for grid sums.
* `TwoCases.FlatCase.perm_size_gt`: Theorem E.11.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma E.7 (p. 35), Proposition E.10 and its proof (pp. 36–37), Theorem E.11 and its proof
  (p. 37); module `Paper.Rate`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.TwoCases

variable {k : ℕ}

/-- The last step of the proof of Proposition E.10 (p. 37): the three estimates of the wire
exponents and the estimate `c g ≤ √k + δ` of the unit exponent of the ends turn the comparison
`ℓ S1 ≤ k g + ℓ S2 + S3 lg` into `ℓ k √k / 16 ≤ lg`. -/
private theorem rate_numbers {k ℓ c N δ S1 S2 S3 g lg : ℝ} (hk1 : 1 ≤ k) (hℓ : 100 * √k ≤ ℓ)
    (hc : 0 ≤ c) (hN : N = k * (k - 1) / 2) (hδ : δ = 1 / (1000 * k)) (hlog : 0 ≤ lg)
    (hw : N * (1 - δ) ≤ c * S1) (hh : c * S2 ≤ N - 4 / 81 * k + 2 * N * δ)
    (hm : c * S3 ≤ 4 / (9 * √k) + δ) (hg : c * g ≤ √k + δ)
    (h1 : ℓ * S1 ≤ k * g + (ℓ * S2 + S3 * lg)) : ℓ * (k * √k) / 16 ≤ lg := by
  have hℓ0 : 0 ≤ ℓ := le_trans (by positivity) hℓ
  have h3 : ℓ * (N * (1 - δ)) ≤
      k * (√k + δ) + ℓ * (N - 4 / 81 * k + 2 * N * δ) + (4 / (9 * √k) + δ) * lg := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hc, mul_le_mul_of_nonneg_left hw hℓ0,
      mul_le_mul_of_nonneg_left hh hℓ0, mul_le_mul_of_nonneg_right hm hlog,
      mul_le_mul_of_nonneg_left hg (by linarith : (0 : ℝ) ≤ k)]
  obtain ⟨r, hr, rfl⟩ : ∃ r, 1 ≤ r ∧ r ^ 2 = k :=
    ⟨√k, Real.one_le_sqrt.2 hk1, Real.sq_sqrt (by linarith)⟩
  rw [Real.sqrt_sq (by linarith)] at h3 hℓ ⊢
  subst hN hδ
  have hr0 : 0 < r := by linarith
  field_simp at h3
  nlinarith [mul_le_mul_of_nonneg_left hℓ (by positivity : (0 : ℝ) ≤ r ^ 4),
    mul_le_mul_of_nonneg_right hr hlog, mul_nonneg hℓ0 (sq_nonneg r), mul_nonneg hℓ0 hr0.le]

/-- **Lower bound for the network polynomial** (Proposition E.10 of [AnthropicVPVNP2026], p. 36).
In the flat case, for `k ≥ 2` and `ℓ ≥ 100 √k`, every circuit over `K` for `f_{k,ℓ}` has at least
`2 ^ (ℓ k^{3/2} / 16)` nodes. -/
theorem networkPolynomial_size_ge_of_sqrt_le {K : Type} [Field K] (hK : FlatCase K) (hk : 2 ≤ k)
    {ℓ s : ℕ} (hℓ : 100 * √k ≤ ℓ) (hP : ComputedWithin (networkPolynomial K k ℓ) s) :
    (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ s := by
  classical
  have hs : 1 ≤ s := hP.pos
  -- the hubs `±x S` of the balanced sets `S`
  choose! x hx using fun S (hS : S ∈ balancedSets k) => exists_norm_eq_sum_dist_cubeEndPoint_le
    (by omega) S (mem_balancedSets.1 hS).1 (mem_balancedSets.1 hS).2
  -- the ends at facet centres of the cube, and the hubs; a spectral point by Proposition E.9
  let pos : (Σ _ : Pair k, Bool) ⊕ (Finset (Fin k) × Bool) → EuclideanSpace ℝ (Fin k) :=
    Sum.elim (fun a => cubeEndPoint a.1 (bif a.2 then 1 else 0))
      fun o => if o.2 then x o.1 else -x o.1
  set δ : ℝ := 1 / (1000 * k) with hδ
  have hPV : univ.image (fun a => pos (.inl a)) ⊆ univ.image pos :=
    image_subset_iff.2 fun a _ => mem_image_of_mem _ (mem_univ _)
  obtain ⟨F, c, hc, hF, hg⟩ := exists_spectralPoint_cube hK _ _ hPV
    ⟨_, mem_image_of_mem _ (mem_univ ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.mk_lt_mk.2 one_pos⟩,
      false⟩)⟩
    (fun y hy => by
      obtain ⟨⟨e, d⟩, -, rfl⟩ := mem_image.1 hy
      exact ⟨e.low, !d, by cases d <;> simp [pos, cubeEndPoint]⟩)
    (by positivity : 0 < δ)
  -- pulled back to the ends and the hubs as parties
  let place (z : (Σ _ : Pair k, Bool) ⊕ (Finset (Fin k) × Bool)) : univ.image pos :=
    ⟨pos z, mem_image_of_mem _ (mem_univ z)⟩
  set F' := F.pull place
  have hF' (a b) : |c * F'.wireExponent a b - dist (pos a) (pos b)| < δ :=
    F.pull_wireExponent place a b ▸ hF _ _
  have hg' : c * F'.unitExponent Sum.inl ≤ √k + δ := by
    refine (congrArg (c * ·) ?_).trans_le hg
    exact (F.pull_unitExponent _ _).trans (F.unitExponent_congr_range _ _
      (Set.ext fun ⟨_, _⟩ => by simp [place, Subtype.ext_iff]))
  -- Lemma E.7 with the cover of the network tensor by the hub tensors, with the hubs `(S, true)`
  -- and `(S, false)`
  have hcov := networkTensor_coveredBy_hubTensor hP hk Sum.inl (fun S => .inr (S, true))
    fun S => .inr (S, false)
  have : Nonempty (balancedSets k) := (balancedSets_nonempty hk).coe_sort
  obtain ⟨A, hA, hmax⟩ := exists_max_image (balancedSets k)
    (fun S => F' (hubTensor K ℓ s Sum.inl S (.inr (S, true)) (.inr (S, false))))
    (balancedSets_nonempty hk)
  have h1 := F'.apply_le_of_borderCoveredBy Sum.inl (push Sum.inl (networkTensor K k ℓ))
    (fun q hq => by
      have : IsEmpty {a // Sum.inl a = q} := ⟨fun a => hq ⟨a.1, a.2⟩⟩
      exact inferInstanceAs (Subsingleton (∀ a : {a // Sum.inl a = q}, _)))
    hcov.borderCoveredBy fun S : balancedSets k => hmax S S.2
  have hcard : (Fintype.card (balancedSets k) : ℝ) ^ F'.unitExponent Sum.inl ≤
      2 ^ (k * F'.unitExponent Sum.inl) := by
    rw [Real.rpow_mul two_pos.le, Real.rpow_natCast]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast (Fintype.card_coe _).trans_le (card_balancedSets_le k))
      (F'.unitExponent_nonneg _)
  have h2 := h1.trans (mul_le_mul_of_nonneg_right hcard (F'.nonneg _))
  rw [apply_push_networkTensor, apply_hubTensor F' hs, ← Real.rpow_add two_pos,
    Real.rpow_le_rpow_left_iff one_lt_two] at h2
  obtain ⟨hxn, hxs⟩ := hx A hA
  -- the three estimates of the wire exponents by the distances
  have hw : (k : ℝ) * (k - 1) / 2 * (1 - δ) ≤
      c * ∑ e, F'.wireExponent (.inl ⟨e, false⟩) (.inl ⟨e, true⟩) := by
    rw [← sum_pair_one, sum_mul, mul_sum]
    refine sum_le_sum fun e _ => ?_
    have h3 : dist (pos (.inl ⟨e, false⟩)) (pos (.inl ⟨e, true⟩)) = 1 := dist_cubeEndPoint e
    linarith [(abs_lt.1 (hF' (.inl ⟨e, false⟩) (.inl ⟨e, true⟩))).1]
  have hh : c * ∑ a, F'.wireExponent (.inl a)
      (if a.1.node a.2 ∈ A then .inr (A, true) else .inr (A, false)) ≤
      (k : ℝ) * (k - 1) / 2 - 4 / 81 * k + 2 * ((k : ℝ) * (k - 1) / 2) * δ := by
    have h3 (a : Σ _ : Pair k, Bool) : c * F'.wireExponent (.inl a)
        (if a.1.node a.2 ∈ A then .inr (A, true) else .inr (A, false)) ≤
          dist (pos (.inl a)) (if a.1.node a.2 ∈ A then x A else -x A) + δ := by
      have h4 := (abs_lt.1 (hF' (.inl a)
        (if a.1.node a.2 ∈ A then .inr (A, true) else .inr (A, false)))).2
      split_ifs at h4 ⊢ <;> exact (sub_lt_iff_lt_add'.1 h4).le
    have hN : (Fintype.card (Pair k) : ℝ) = k * (k - 1) / 2 := by simpa using sum_pair_one (k := k)
    rw [mul_sum, Fintype.sum_sigma]
    calc _ ≤ ∑ e : Pair k, ((dist (cubeEndPoint e 0) (if e.low ∈ A then x A else -x A) +
          dist (cubeEndPoint e 1) (if e.high ∈ A then x A else -x A)) + 2 * δ) :=
          sum_le_sum fun e _ => by
            have h5 : c * _ ≤ dist (cubeEndPoint e 0) (if e.low ∈ A then x A else -x A) + δ :=
              h3 ⟨e, false⟩
            have h6 : c * _ ≤ dist (cubeEndPoint e 1) (if e.high ∈ A then x A else -x A) + δ :=
              h3 ⟨e, true⟩
            rw [Fintype.sum_bool]; linarith
      _ ≤ _ := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hN]; linarith
  have hm : c * F'.wireExponent (.inr (A, true)) (.inr (A, false)) ≤ 4 / (9 * √k) + δ := by
    have h3 : dist (pos (.inr (A, true))) (pos (.inr (A, false))) = 4 / (9 * √k) := by
      change dist (x A) (-x A) = _
      rw [dist_self_neg, hxn]; ring
    linarith [(abs_lt.1 (hF' (.inr (A, true)) (.inr (A, false)))).2]
  have key := rate_numbers (by exact_mod_cast (by omega : 1 ≤ k)) hℓ hc rfl hδ
    (Real.logb_nonneg one_lt_two (by exact_mod_cast hs)) hw hh hm hg' h2
  rwa [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' (Nat.cast_nonneg k) (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow,
    ← Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hs)]

/-! ### Theorem E.11 -/

/-- **From the network polynomial to the bound** (proof of Theorem E.11, p. 37). There is `m₀`,
depending only on `κ`, with the following property for every `P : ℕ → ℕ → Prop`, such as
`P m s`: some circuit with `s` nodes computes the member `m` of a family. Suppose that `P m s`
gives the bound of Proposition E.10 for `5 s`, `2 ^ (ℓ k^{3/2} / 16) ≤ 5 s`, whenever `k ≥ 2`,
`ℓ ≥ 1`, `ℓ ≥ 100 √k` and `κ k³ ℓ 2^{kℓ} ≤ m`. Then `P m s` implies
`2 ^ ((log m)^{4/3} / 1600²) < s` for `m ≥ m₀`. The proof takes `k = r²` and `ℓ = 100 r` for the
largest `r` with `200 r³ ≤ ⌊log m⌋`. -/
theorem exists_two_rpow_lt_of_networkPolynomial (κ : ℕ) : ∃ m₀ : ℕ, ∀ P : ℕ → ℕ → Prop,
    (∀ k ℓ m s : ℕ, 2 ≤ k → 1 ≤ ℓ → 100 * √k ≤ ℓ → κ * k ^ 3 * ℓ * 2 ^ (k * ℓ) ≤ m → P m s →
      (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ ((5 * s : ℕ) : ℝ)) →
    ∀ m ≥ m₀, ∀ s, P m s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  refine ⟨2 ^ (200 * (κ + 3) ^ 3), fun P hP m hm s hs => ?_⟩
  -- `r` is the largest number with `200 r³ ≤ B = ⌊log m⌋`
  have hm0 : 0 < m := (Nat.two_pow_pos _).trans_le hm
  set B := Nat.log 2 m
  set r := Nat.nthRoot 3 (B / 200)
  have hB : 200 * (κ + 3) ^ 3 ≤ B := Nat.le_log_of_pow_le one_lt_two hm
  have hr : κ + 3 ≤ r := (Nat.le_nthRoot_iff (by norm_num)).2 (by omega)
  have hr3 : 200 * r ^ 3 ≤ B := by
    have : r ^ 3 ≤ B / 200 := Nat.pow_nthRoot_le_iff.2 (.inl (by norm_num))
    omega
  have hBr : B + 1 ≤ 1600 * r ^ 3 := by
    have h1 : B / 200 < (r + 1) ^ 3 := Nat.lt_pow_nthRoot_add_one (by norm_num) _
    have h2 : (r + 1) ^ 3 ≤ 8 * r ^ 3 :=
      (Nat.pow_le_pow_left (show r + 1 ≤ 2 * r by omega) 3).trans_eq (by ring)
    omega
  -- Lemma E.3 and Proposition E.10 apply to `k = r²` and `ℓ = 100 r`
  have hfit : κ * (r ^ 2) ^ 3 * (100 * r) * 2 ^ (r ^ 2 * (100 * r)) ≤ m := by
    have h1 : κ * (r ^ 2) ^ 3 * (100 * r) ≤ 2 ^ (100 * r ^ 3) :=
      calc κ * (r ^ 2) ^ 3 * (100 * r) ≤ r * (r ^ 2) ^ 3 * (100 * r) := by gcongr; omega
        _ = 100 * r ^ 8 := by ring
        _ ≤ 2 ^ 7 * (2 ^ r) ^ 8 :=
          Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left Nat.lt_two_pow_self.le 8)
        _ = 2 ^ (7 + 8 * r) := by ring
        _ ≤ 2 ^ (100 * r ^ 3) := Nat.pow_le_pow_right two_pos
          (by have := Nat.le_self_pow (by norm_num : 3 ≠ 0) r; omega)
    calc _ ≤ 2 ^ (100 * r ^ 3) * 2 ^ (100 * r ^ 3) := by
          rw [show r ^ 2 * (100 * r) = 100 * r ^ 3 by ring]
          exact Nat.mul_le_mul_right _ h1
      _ = 2 ^ (200 * r ^ 3) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ B := Nat.pow_le_pow_right two_pos hr3
      _ ≤ m := Nat.pow_log_le_self 2 hm0.ne'
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast (by omega : 2 ≤ r)
  have hlow := hP (r ^ 2) (100 * r) m s (by nlinarith) (by omega)
    (by push_cast; rw [Real.sqrt_sq (by linarith)]) hfit hs
  rw [Nat.cast_pow, ← Real.rpow_natCast (r : ℝ) 2, ← Real.rpow_mul (by linarith),
    show ((2 : ℕ) : ℝ) * (3 / 2) = (3 : ℕ) by norm_num, Real.rpow_natCast] at hlow
  push_cast at hlow
  -- `log m ≤ 1600 r³ ≤ (12 r)³`, so `(log m)^{4/3} / 1600² ≤ (12 r)⁴ / 1600² ≤ r⁴`
  have hL : Real.logb 2 m ≤ ((12 * r : ℕ) : ℝ) ^ (3 : ℕ) := by
    refine ((Real.logb_lt_iff_lt_rpow one_lt_two (by exact_mod_cast hm0)).2 ?_).le.trans
      (b := ((B + 1 : ℕ) : ℝ)) (by exact_mod_cast hBr.trans (by ring_nf; omega))
    rw [Real.rpow_natCast]
    exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two m
  have hL4 : Real.logb 2 m ^ (4 / 3 : ℝ) ≤ ((12 * r : ℕ) : ℝ) ^ 4 := by
    refine (Real.rpow_le_rpow (Real.logb_nonneg one_lt_two (by exact_mod_cast hm0)) hL
      (by norm_num)).trans_eq ?_
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  -- and `8 · 2 ^ (r⁴) ≤ 2 ^ (25 r⁴ / 4) ≤ 5 s`
  have h8 : (2 : ℝ) ^ ((r : ℝ) ^ 4 + 3) ≤ 5 * s :=
    (Real.rpow_le_rpow_of_exponent_le one_le_two
      (by nlinarith [one_le_pow₀ (n := 4) (by linarith : (1 : ℝ) ≤ r)])).trans hlow
  rw [Real.rpow_add two_pos] at h8; norm_num at h8
  calc (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) ≤ 2 ^ ((r : ℝ) ^ 4) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (by
          rw [div_le_iff₀ (by norm_num)]
          push_cast at hL4
          nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) r) 4])
    _ < s := by linarith [Real.rpow_pos_of_pos two_pos ((r : ℝ) ^ 4)]

/-- **The flat case for every family complete for grid sums** (Theorem E.11, p. 37, with
Corollary E.2, p. 32). There is `m₀`, depending only on `κ`, such that in the flat case, for every
family `G` complete for grid sums with blow-up `κ` and `m ≥ m₀`, every circuit for `G.poly m` has
more than `2 ^ ((log m)^{4/3} / 1600²)` nodes. -/
theorem size_gt_of_gridComplete (κ : ℕ) : ∃ m₀ : ℕ, ∀ (K : Type) [Field K], FlatCase K →
    ∀ G : PolynomialFamily K, GridComplete G κ → ∀ m ≥ m₀, ∀ s,
      ComputedWithin (G.poly m) s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ := exists_two_rpow_lt_of_networkPolynomial κ
  exact ⟨m₀, fun K _ hK G hG => h _ fun k ℓ m s hk hℓ hℓk hm hs =>
    networkPolynomial_size_ge_of_sqrt_le hK hk hℓk
      (hs.of_isAffineProjection (isAffineProjection_networkPolynomial hG hk hℓ hm))⟩

end Cslib.Circuits.Arithmetic.Separation.Flat

namespace Cslib.Circuits.Arithmetic.Separation.TwoCases

/-- **Lower bound for the permanent in the flat case** (Theorem E.11 of [AnthropicVPVNP2026],
p. 37). In the flat case, if `2 ≠ 0` in `K`, there is `m₀` such that for `m ≥ m₀` every circuit
over `K` for the permanent `PERM_m` has more than `2 ^ ((log m)^{4/3} / 1600²)` nodes. -/
theorem FlatCase.perm_size_gt {K : Type} [Field K] (hK : FlatCase K) (h2 : (2 : K) ≠ 0) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, ComputedWithin ((permFamily K).poly m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s :=
  let ⟨m₀, h⟩ := Flat.size_gt_of_gridComplete 3
  ⟨m₀, h K hK _ (gridComplete_permFamily h2)⟩

end Cslib.Circuits.Arithmetic.Separation.TwoCases
