/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ComputedWithin
public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.BalancedProducts
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.NetworkTensor
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.EndPoints
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.LowerNumbers
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.NetworkProjection
import CslibFrontier.Foundations.Analysis.Normed.Module.Basic
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Hubs

/-!
# The lower bound in the flat case: Proposition E.5 and Theorem E.6

A set `S` of the `k` nodes of the complete network is *balanced* (`Flat.balancedSets`) if
`k ≤ 3 |S| ≤ 2 k`. Let a polynomial `P` in the variables of the network polynomial `f_{k,ℓ}` be
computed by a circuit with at most `s` nodes. By Lemma E.4 (`Flat.exists_balanced_products`) and
Lemma A.3 (`PartyTensor.push_le_prod_wire_hubs`), the tensor on the ends of the wires of the
coefficients of `P` at the views of the nodes is covered by the tensors `Flat.hubTensor` of the
balanced sets, with a wire of dimension `s` between the hubs (`Flat.coveredBy_hubTensor`). For
`P = f_{k,ℓ}` this tensor is `T_{k,ℓ}` (`Flat.networkTensor`), which is then covered by the hub
tensors (`Flat.networkTensor_coveredBy_hubTensor`).

In the flat case (`TwoCases.FlatCase`) the ends and two hubs for every balanced set, placed in
`ℝ ^ k` as in `Flat.exists_norm_eq_sum_dist_endPoint_le`, have their distances close to the wire
exponents of one spectral point, up to a factor `c`. Comparing the values of this spectral point
at `T_{k,ℓ}` and at the hub tensors (`Flat.lower_numbers`) gives Proposition E.5: for every
`k ≥ 2` there is `ℓ₀` such that for `ℓ ≥ ℓ₀` every circuit for `f_{k,ℓ}` has at least
`2 ^ (ℓ k^{3/2} / 6)` nodes (`Flat.networkPolynomial_size_ge`). With Lemma E.3
(`Flat.computedWithin_networkPolynomial`) this gives Theorem E.6: when `2 ≠ 0`, the permanent has
no circuits of polynomial size (`Flat.not_computedWithin_permFamily`).

## Main results

* `Flat.coveredBy_hubTensor`: the tensor of a polynomial with a small circuit is covered by the
  hub tensors of the balanced sets.
* `Flat.networkTensor_coveredBy_hubTensor`: so is `T_{k,ℓ}` when `f_{k,ℓ}` has a small circuit.
* `Flat.networkPolynomial_size_ge`: Proposition E.5.
* `Flat.not_computedWithin_permFamily`: Theorem E.6.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition E.5 and its proof (pp. 33–34), Theorem E.6 (p. 35); module `Paper.Flat`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset MvPolynomial Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.TwoCases

variable {k : ℕ}

/-! ### The tensor of a small circuit -/

/-- What the nodes see when the ends of the wires hold the strings with the numbers `z`. -/
private abbrev views {ℓ : ℕ} (z : (Σ _ : Pair k, Bool) → Fin (2 ^ ℓ)) :
    Fin k → Fin k → BitString ℓ :=
  assemble fun e d => (BitString.equivFin ℓ).symm (z ⟨e, d⟩)

/-- What the nodes of `S` see depends only on the strings at the ends at these nodes. -/
private theorem ofProd_views_congr {ℓ : ℕ} {S : Finset (Fin k)}
    {z z' : (Σ _ : Pair k, Bool) → Fin (2 ^ ℓ)} (h : ∀ a, a.1.node a.2 ∈ S → z a = z' a) :
    BlockChoice.ofProd S (views z) = BlockChoice.ofProd S (views z') := by
  have key (i : Fin k) (hi : i ∈ S) : views z i = views z' i :=
    assemble_congr (fun e he => by rw [h ⟨e, false⟩ (show e.low ∈ S from he ▸ hi)])
      (fun e he => by rw [h ⟨e, true⟩ (show e.high ∈ S from he ▸ hi)])
  funext i
  exact Subtype.ext (Prod.ext rfl (key i i.2))

/-- **A small circuit routes the network tensor through two hubs** ([AnthropicVPVNP2026], proof of
Proposition E.5, p. 34, by Lemmas E.4 and A.3). Let `P` be a polynomial over a commutative
semiring in the variables of the network polynomial `f_{k,ℓ}`, `k ≥ 2`, computed by a circuit with
at most `s` nodes, and let the ends of the wires be at the parties `π`. Consider the tensor on the
ends whose entry at the strings `z` is the coefficient of `P` at the monomial of what the nodes see
(for `P = f_{k,ℓ}` this is `T_{k,ℓ}`, by `networkTensor_entry`). It is covered by the tensors
`hubTensor` of Lemma A.3, one for each balanced set `S`, with the hubs `o₁ S` and `o₂ S` and a
wire of dimension `s` between them. -/
theorem coveredBy_hubTensor {K : Type} [CommSemiring K] {I : Type} [Fintype I] [DecidableEq I]
    {ℓ : ℕ} {P : MvPolynomial (Fin k × (Fin k → BitString ℓ)) K} {s : ℕ}
    (hP : ComputedWithin P s) (hk : 2 ≤ k) (π : (Σ _ : Pair k, Bool) → I)
    (o₁ o₂ : Finset (Fin k) → I) :
    (push π ((networkTensor K k ℓ).withEntry fun z => P.coeff (blockMonomial Prod.fst univ
        (BlockChoice.ofProd univ (assemble fun e d => (BitString.equivFin ℓ).symm (z ⟨e, d⟩)))))
      ).CoveredBy fun S : balancedSets k => hubTensor K ℓ s π S (o₁ S) (o₂ S) := by
  classical
  obtain ⟨g, h, hg, hh, he⟩ := exists_balanced_products hP Prod.fst hk
  -- the factors of the products of Lemma E.4, as functions of the strings at the ends
  let α (S : Finset (Fin k)) (δ : Fin s) (z : (Σ _ : Pair k, Bool) → Fin (2 ^ ℓ)) : K :=
    (g S δ).coeff (blockMonomial Prod.fst S (BlockChoice.ofProd S (views z)))
  let β (S : Finset (Fin k)) (δ : Fin s) (z : (Σ _ : Pair k, Bool) → Fin (2 ^ ℓ)) : K :=
    (h S δ).coeff (blockMonomial Prod.fst Sᶜ (BlockChoice.ofProd Sᶜ (views z)))
  refine ((CoveredBy.withEntry _ (fun (S : balancedSets k) z => ∑ δ, α S δ z * β S δ z)
    fun z => ?_).push π).mono fun S => ?_
  · rw [withEntry_entry, ← coeff_smProj_of_mem ⟨_, rfl⟩, he, coeff_sum]
    change ∑ S ∈ balancedSets k, _ = _
    rw [← sum_coe_sort]
    exact sum_congr rfl fun S _ => (coeff_sum ..).trans
      (sum_congr rfl fun δ _ => coeff_mul_blockMonomial_ofProd (hg _ δ) (hh _ δ) _)
  · refine (push_le_prod_wire_hubs π _ (fun a => a.1.node a.2 ∈ (S : Finset (Fin k))) (α S) (β S)
      (fun δ z z' hz => by simp only [α, ofProd_views_congr hz])
      (fun δ z z' hz => by simp only [β, ofProd_views_congr fun a ha => hz a (mem_compl.1 ha)])
      (fun z => rfl) (o₁ S) (o₂ S)).trans_eq ?_
    exact congrArg (· * _) (congrArg prod (funext fun a =>
      congrArg (wire K · _ _) (Fintype.card_fin _)))

/-- **A small circuit for `f_{k,ℓ}` routes `T_{k,ℓ}` through two hubs** ([AnthropicVPVNP2026],
proof of Proposition E.5, p. 34): if a circuit with at most `s` nodes computes `f_{k,ℓ}`, `k ≥ 2`,
then `T_{k,ℓ}` with the ends at the parties `π` is covered by the tensors `hubTensor` of the
balanced sets `S`, with the hubs `o₁ S` and `o₂ S` and a wire of dimension `s` between them. -/
theorem networkTensor_coveredBy_hubTensor {K : Type} [CommSemiring K] {I : Type} [Fintype I]
    [DecidableEq I] {ℓ s : ℕ} (hP : ComputedWithin (networkPolynomial K k ℓ) s) (hk : 2 ≤ k)
    (π : (Σ _ : Pair k, Bool) → I) (o₁ o₂ : Finset (Fin k) → I) :
    (push π (networkTensor K k ℓ)).CoveredBy
      fun S : balancedSets k => hubTensor K ℓ s π S (o₁ S) (o₂ S) := by
  have h := coveredBy_hubTensor hP hk π o₁ o₂
  rwa [← congrArg (networkTensor K k ℓ).withEntry (funext networkTensor_entry)] at h

/-! ### Proposition E.5 -/

/-- If `2 ^ a` is at most a sum of `2 ^ f S` over a nonempty set of at most `2 ^ k` indices, then
`a ≤ k + f S` for one of them. -/
private theorem exists_le_add_of_two_rpow_le_sum {ι : Type*} {B : Finset ι} (hB : B.Nonempty)
    (hcard : #B ≤ 2 ^ k) {a : ℝ} {f : ι → ℝ} (h : (2 : ℝ) ^ a ≤ ∑ S ∈ B, (2 : ℝ) ^ f S) :
    ∃ S ∈ B, a ≤ k + f S := by
  obtain ⟨A, hA, hmax⟩ := exists_max_image B f hB
  refine ⟨A, hA, (Real.rpow_le_rpow_left_iff one_lt_two).1 (h.trans ?_)⟩
  calc ∑ S ∈ B, (2 : ℝ) ^ f S ≤ #B • (2 : ℝ) ^ f A :=
        sum_le_card_nsmul _ _ _ fun S hS =>
          Real.rpow_le_rpow_of_exponent_le one_le_two (hmax S hS)
    _ ≤ (2 : ℝ) ^ k * 2 ^ f A := by
        rw [nsmul_eq_mul]
        gcongr
        exact_mod_cast hcard
    _ = 2 ^ ((k : ℝ) + f A) := by rw [Real.rpow_add two_pos, Real.rpow_natCast]

/-- `x ^ (3 / 2) = x √x` for `x ≥ 0`. -/
private theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * √x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-- **Paper: Proposition E.5** (a first lower bound for the network polynomial, p. 33). In the flat
case, for every `k ≥ 2` there is `ℓ₀` such that for `ℓ ≥ ℓ₀` every circuit over `K` for
`f_{k,ℓ}` has at least `2 ^ (ℓ k^{3/2} / 6)` nodes. The polynomial here is `networkPolynomial`,
which has a variable for every node and every family of strings; a circuit for the polynomial in
the variables printed in the paper (`networkPolynomialOnViews`) is one for it with the same number
of nodes (`rename_networkPolynomialOnViews`), so the bound holds for that polynomial too. -/
theorem networkPolynomial_size_ge {K : Type} [Field K] (hK : FlatCase K) (hk : 2 ≤ k) :
    ∃ ℓ₀ : ℕ, ∀ ℓ ≥ ℓ₀, ∀ s : ℕ, ComputedWithin (networkPolynomial K k ℓ) s →
      (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 6) ≤ s := by
  classical
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  -- the hubs `±x S` of the balanced sets `S`
  choose x hx using fun S : Finset (Fin k) =>
    if hS : S ∈ balancedSets k then
      (exists_norm_eq_sum_dist_endPoint_le (by omega) S (mem_balancedSets.1 hS).1
        (mem_balancedSets.1 hS).2).imp fun _ hx _ => hx
    else ⟨0, fun h => absurd h hS⟩
  -- a spectral point on the ends and the hubs, close to their distances up to the factor `c`
  let place : (Σ _ : Pair k, Bool) ⊕ (Finset (Fin k) × Bool) → EuclideanSpace ℝ (Fin k) :=
    Sum.elim (fun a => endPoint (a.1.node a.2) (a.1.node !a.2))
      fun o => if o.2 then x o.1 else -x o.1
  set δ : ℝ := 1 / (150 * k) with hδ
  obtain ⟨F, c, hc, hF⟩ := (hK k _ place).exists_spectralPoint id (by positivity : 0 < δ)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_nat_ge (100 * c)
  refine ⟨ℓ₀, fun ℓ hℓ s hP => ?_⟩
  have hs : 1 ≤ s := hP.pos
  -- the network tensor is covered by the hub tensors, with the hubs `(S, true)` and `(S, false)`,
  -- so `F` at it is at most `2 ^ k` times `F` at one of them
  have h1 : F (push Sum.inl (networkTensor K k ℓ)) ≤ ∑ S : balancedSets k,
      F (hubTensor K ℓ s Sum.inl S (.inr (S, true)) (.inr (S, false))) :=
    F.le_sum _ _ (networkTensor_coveredBy_hubTensor hP hk Sum.inl (fun S => .inr (S, true))
      fun S => .inr (S, false))
  rw [apply_push_networkTensor, sum_coe_sort (balancedSets k)
    fun S => F (hubTensor K ℓ s Sum.inl S (.inr (S, true)) (.inr (S, false)))] at h1
  simp only [apply_hubTensor F hs] at h1
  obtain ⟨A, hA, h2⟩ := exists_le_add_of_two_rpow_le_sum (balancedSets_nonempty hk)
    (card_balancedSets_le k) h1
  obtain ⟨hxn, hxs⟩ := hx A hA
  -- the three estimates of the wire exponents by the distances
  have hw : (k : ℝ) * (k - 1) / 2 * (1 - δ) ≤
      c * ∑ e, F.wireExponent (Sum.inl ⟨e, false⟩) (Sum.inl ⟨e, true⟩) := by
    rw [← sum_pair_one, sum_mul, mul_sum]
    refine sum_le_sum fun e _ => ?_
    have h3 := (abs_lt.1 (hF (Sum.inl ⟨e, false⟩) (Sum.inl ⟨e, true⟩))).2
    have h4 : dist (place (Sum.inl ⟨e, false⟩)) (place (Sum.inl ⟨e, true⟩)) = 1 :=
      dist_endPoint e.low_lt_high.ne
    simp only [id, h4] at h3; linarith
  have hh : c * ∑ a, F.wireExponent (Sum.inl a)
      (if a.1.node a.2 ∈ A then .inr (A, true) else .inr (A, false)) ≤
      (k : ℝ) * (k - 1) / 2 - k / 12 + 2 * ((k : ℝ) * (k - 1) / 2) * δ := by
    have h3 (a : Σ _ : Pair k, Bool) : c * F.wireExponent (Sum.inl a)
        (if a.1.node a.2 ∈ A then .inr (A, true) else .inr (A, false)) ≤
          dist (endPoint (a.1.node a.2) (a.1.node !a.2))
            (if a.1.node a.2 ∈ A then x A else -x A) + δ := by
      have h4 := (abs_lt.1 (hF (Sum.inl a)
        (if a.1.node a.2 ∈ A then .inr (A, true) else .inr (A, false)))).1
      split_ifs at h4 ⊢ <;>
        simp only [id, place, Sum.elim_inl, Sum.elim_inr, ite_true, Bool.false_eq_true,
          ite_false] at h4 <;> linarith
    rw [mul_sum]
    calc _ ≤ _ := sum_le_sum fun a _ => h3 a
      _ = ∑ e : Pair k, ((dist (endPoint e.low e.high) (if e.low ∈ A then x A else -x A) + δ) +
          (dist (endPoint e.high e.low) (if e.high ∈ A then x A else -x A) + δ)) := by
        rw [Fintype.sum_sigma]
        exact sum_congr rfl fun e _ => by rw [Fintype.sum_bool]; exact add_comm _ _
      _ = _ := sum_pair_add_add_swap (fun a b => dist (endPoint a b)
          (if a ∈ A then x A else -x A)) δ
      _ ≤ _ := by linarith
  have hm : c * F.wireExponent (.inr (A, true)) (.inr (A, false)) ≤ 1 / (3 * √k) + δ := by
    have h3 := (abs_lt.1 (hF (.inr (A, true)) (.inr (A, false)))).1
    have h4 : dist (place (.inr (A, true))) (place (.inr (A, false))) = 1 / (3 * √k) := by
      change dist (x A) (-x A) = _
      rw [dist_self_neg, hxn]; ring
    simp only [id, h4] at h3; linarith
  have key := lower_numbers hk1 (Nat.cast_nonneg ℓ) hc rfl hδ
    (Real.logb_nonneg one_lt_two (by exact_mod_cast hs)) (hℓ₀.trans (by exact_mod_cast hℓ))
    hw hh hm (h2.trans_eq (add_assoc _ _ _).symm)
  rwa [rpow_three_halves (Nat.cast_nonneg k),
    ← Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hs)]

/-! ### Theorem E.6 -/

/-- **Paper: Theorem E.6** (no circuits of polynomial size in the flat case, p. 35). In the flat
case, if `2 ≠ 0` in `K`, then for every `C` there is `m₀` such that for `m ≥ m₀` no circuit over
`K` with at most `m ^ C` nodes computes the permanent `PERM_m`. The hypothesis `2 ≠ 0` is that of
Lemma E.3, on which the paper's proof rests. -/
theorem not_computedWithin_permFamily {K : Type} [Field K] (hK : FlatCase K) (h2 : (2 : K) ≠ 0)
    (C : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, ¬ ComputedWithin ((permFamily K).poly m) (m ^ C) := by
  -- `k = n ^ 2` with `n = 30 (C + 1)`, and `ℓ = ⌊log_{4^k} m⌋`
  set n := 30 * (C + 1) with hn
  have hk : 2 ≤ n ^ 2 := by nlinarith
  obtain ⟨ℓ₀, hℓ₀⟩ := networkPolynomial_size_ge hK hk
  set ℓ₁ := ℓ₀ + 3 * (n ^ 2) ^ 3 + 1
  have hb : 1 < 2 ^ (2 * n ^ 2) := Nat.one_lt_two_pow (by omega)
  refine ⟨(2 ^ (2 * n ^ 2)) ^ ℓ₁, fun m hm hP => ?_⟩
  set ℓ := Nat.log (2 ^ (2 * n ^ 2)) m
  have hℓ : ℓ₁ ≤ ℓ := Nat.le_log_of_pow_le hb hm
  have hm0 : m ≠ 0 := ((pow_pos (pow_pos two_pos _) ℓ₁).trans_le hm).ne'
  have hlow := Nat.pow_log_le_self (2 ^ (2 * n ^ 2)) hm0
  have hhigh := Nat.lt_pow_succ_log_self hb m
  -- Lemma E.3 applies at `ℓ`
  have hsize : 3 * (n ^ 2) ^ 3 * ℓ * 2 ^ (n ^ 2 * ℓ) ≤ m := by
    have h3 : 3 * (n ^ 2) ^ 3 * ℓ ≤ 2 ^ (n ^ 2 * ℓ) :=
      calc 3 * (n ^ 2) ^ 3 * ℓ ≤ 2 ^ ℓ * 2 ^ ℓ :=
            Nat.mul_le_mul ((Nat.lt_two_pow_self).le.trans' (by omega)) Nat.lt_two_pow_self.le
        _ = 2 ^ (2 * ℓ) := by rw [← pow_add, two_mul]
        _ ≤ _ := Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right ℓ hk)
    calc _ ≤ 2 ^ (n ^ 2 * ℓ) * 2 ^ (n ^ 2 * ℓ) := Nat.mul_le_mul_right _ h3
      _ = (2 ^ (2 * n ^ 2)) ^ ℓ := by rw [← pow_add, ← pow_mul]; ring_nf
      _ ≤ m := hlow
  have h1 := hℓ₀ ℓ (by omega) _ (computedWithin_networkPolynomial h2 hk (by omega) hsize hP)
  -- and `5 m ^ C < 2 ^ (3 + 2 n² (ℓ + 1) C)`
  have h5 : 5 * m ^ C ≤ 2 ^ (3 + 2 * n ^ 2 * (ℓ + 1) * C) := by
    rw [pow_add, pow_mul, pow_mul 2]
    exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hhigh.le C)
  -- so `ℓ n³ / 6 ≤ 3 + 2 n² (ℓ + 1) C`, which is false for `n = 30 (C + 1)`
  have h6 := h1.trans (Nat.cast_le.2 h5)
  push_cast [hn] at h6
  rw [rpow_three_halves (by positivity), Real.sqrt_sq (by positivity), ← Real.rpow_natCast 2,
    Real.rpow_le_rpow_left_iff one_lt_two] at h6
  push_cast at h6
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
  linarith [mul_nonneg (mul_nonneg (sq_nonneg ((C : ℝ) + 1)) (Nat.cast_nonneg C))
      (sub_nonneg.2 hℓ1),
    mul_nonneg (sq_nonneg ((C : ℝ) + 1)) (Nat.cast_nonneg C),
    one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (n := 2) (le_add_of_nonneg_left (Nat.cast_nonneg C))) hℓ1]

end Cslib.Circuits.Arithmetic.Separation.Flat
