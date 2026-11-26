/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.LinearCombination

/-!
# Boolean Möbius reconstruction

A polynomial of degree at most `q`, evaluated at a Boolean assignment, is reconstructed from
its values on subsets of at most `q` coordinates. Summing this identity permits the polynomial
to depend on the original assignment. Coefficients may lie in any commutative ring.

The proof uses the existing Boolean low-degree span; it introduces no multilinear polynomial
representation. It follows Lemma 3.3, equation (3.10), p24 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH].

The Möbius transform on the subsets of a set (`Cslib.BitString.subsetMobius`) inverts subset
sums (`Cslib.BitString.sum_powerset_subsetMobius`). Applied to the values of a function on the
indicators of subsets, it gives the function's coefficient at a monomial
(`Cslib.BitString.subsetMobius_monomial`), so it vanishes above the degree
(`Cslib.BitString.subsetMobius_eq_zero_of_mem_lowDegree`). This is the subset inversion in the
proof of Lemma D.2, p. 56 of [OpenAI2026ETH].

## Main definitions

* `Cslib.BitString.subsetMobius`: `∑_{T ⊆ S} (-1) ^ (#S - #T) • f T`.

## Main results

* `Cslib.BitString.lowDegree_reconstruction`: pointwise reconstruction in the existing span.
* `Cslib.BitString.sum_eval_eq_restricted_subsets`: the assignment-dependent polynomial sum.
* `Cslib.BitString.sum_powerset_subsetMobius`: Möbius inversion on the subsets of a set.
* `Cslib.BitString.subsetMobius_eq_zero_of_mem_lowDegree`: the transform vanishes above the
  degree.
* `Cslib.BitString.subsetMobius_bitVal_mul`: multiplying by the bit `x i` shifts the transform.
* `Cslib.BitString.eq_sum_subsetMobius_of_local`: a function depending only on the coordinates
  in `I` is the combination of the monomials of subsets of `I`.
* `Cslib.BitString.eq_sum_subsetMobius_smul_monomial`: every function on a finite cube is the
  combination of the monomials with its subset Möbius coefficients.
* `Cslib.BitString.mem_lowDegree_iff_subsetMobius_eq_zero`: a function has degree at most `D`
  exactly when its transform vanishes on every set of more than `D` elements.
-/

open scoped BigOperators
open Finset

namespace Cslib.BitString

variable {ι R : Type*} [CommRing R]

open Classical in
private theorem subset_kernel (S E : Finset ι) :
    (∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) * (if S ⊆ U then 1 else 0)) =
      if S = E then 1 else 0 := by
  classical
  by_cases hSE : S ⊆ E
  · have hbij :
        (∑ U ∈ E.powerset.filter (S ⊆ ·), (-1 : R) ^ (#E - #U)) =
          ∑ Z ∈ (E \ S).powerset, (-1 : R) ^ #Z := by
      refine sum_nbij' (E \ ·) (E \ ·) (fun U hU => ?_) (fun Z hZ => ?_)
        (fun U hU => ?_) (fun Z hZ => ?_) fun U hU => ?_
      · exact mem_powerset.mpr (Finset.sdiff_subset_sdiff_right E (mem_filter.mp hU).2)
      · refine mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, fun i hi => ?_⟩
        exact mem_sdiff.mpr ⟨hSE hi, fun hiZ => (mem_sdiff.mp (mem_powerset.mp hZ hiZ)).2 hi⟩
      · exact Finset.sdiff_sdiff_eq_self (mem_powerset.mp (mem_filter.mp hU).1)
      · exact Finset.sdiff_sdiff_eq_self ((mem_powerset.mp hZ).trans sdiff_subset)
      · rw [card_sdiff_of_subset (mem_powerset.mp (mem_filter.mp hU).1)]
    have hcancel : (∑ Z ∈ (E \ S).powerset, (-1 : R) ^ #Z) =
        if E \ S = ∅ then 1 else 0 := by
      simpa only [map_sum, map_pow, map_neg, map_one, apply_ite, map_zero] using
        congrArg (Int.castRingHom R) (sum_powerset_neg_one_pow_card (x := E \ S))
    simp only [mul_ite, mul_one, mul_zero, ← sum_filter, hbij, hcancel]
    exact if_congr ⟨fun h => hSE.antisymm (sdiff_eq_empty_iff_subset.mp h), fun h => by simp [h]⟩
      rfl rfl
  · rw [ite_eq_right fun h : S = E => hSE h.subset]
    exact sum_eq_zero fun U hU =>
      mul_eq_zero_of_right _ (ite_eq_right fun hSU => hSE (hSU.trans (mem_powerset.mp hU)))

/-! ### The Möbius transform on the subsets of a set -/

section SubsetMobius

variable {M : Type*} [AddCommGroup M]

/-- The **Möbius transform on the subsets of `S`** of a function `f` on finite sets,
`∑_{T ⊆ S} (-1) ^ (#S - #T) • f T`. It inverts subset sums
(`Cslib.BitString.sum_powerset_subsetMobius`). When `f T` is the value of a function on the cube
at the indicator of `T`, it is the coefficient of that function at the monomial of `S`
(`Cslib.BitString.subsetMobius_monomial`). -/
@[expose] public def subsetMobius (f : Finset ι → M) (S : Finset ι) : M :=
  ∑ T ∈ S.powerset, (-1 : ℤ) ^ (#S - #T) • f T

/-- An additive map commutes with the subset Möbius transform. -/
public theorem map_subsetMobius {N : Type*} [AddCommGroup N] (φ : M →+ N) (f : Finset ι → M)
    (S : Finset ι) : φ (subsetMobius f S) = subsetMobius (fun T => φ (f T)) S := by
  simp only [subsetMobius, map_sum, map_zsmul]

/-- The subset Möbius transform is additive. -/
public theorem subsetMobius_add (f g : Finset ι → M) (S : Finset ι) :
    subsetMobius (fun T => f T + g T) S = subsetMobius f S + subsetMobius g S := by
  simp only [subsetMobius, smul_add, sum_add_distrib]

/-- The signed count of the sets between `U` and `T`. -/
private theorem sum_neg_one_pow_superset [DecidableEq ι] {U T : Finset ι} (hUT : U ⊆ T) :
    (∑ S ∈ T.powerset with U ⊆ S, (-1 : ℤ) ^ (#S - #U)) = if U = T then 1 else 0 := by
  have hbij : (∑ S ∈ T.powerset with U ⊆ S, (-1 : ℤ) ^ (#S - #U)) =
      ∑ Z ∈ (T \ U).powerset, (-1 : ℤ) ^ #Z :=
    sum_nbij' (· \ U) (· ∪ U)
      (fun S hS => mem_powerset.mpr
        (sdiff_subset_sdiff (mem_powerset.mp (mem_filter.mp hS).1) subset_rfl))
      (fun Z hZ => mem_filter.mpr
        ⟨mem_powerset.mpr (union_subset ((mem_powerset.mp hZ).trans sdiff_subset) hUT),
          subset_union_right⟩)
      (fun S hS => sdiff_union_of_subset (mem_filter.mp hS).2)
      (fun Z hZ => union_sdiff_cancel_right
        (disjoint_of_subset_left (mem_powerset.mp hZ) sdiff_disjoint))
      fun S hS => by rw [card_sdiff_of_subset (mem_filter.mp hS).2]
  rw [hbij, sum_powerset_neg_one_pow_card]
  exact if_congr ⟨fun he => hUT.antisymm (sdiff_eq_empty_iff_subset.mp he), fun h => by simp [h]⟩
    rfl rfl

/-- **Möbius inversion on the subsets of a set**: summing the subset Möbius transform of `f` over
the subsets of `T` gives back `f T`. -/
public theorem sum_powerset_subsetMobius (f : Finset ι → M) (T : Finset ι) :
    ∑ S ∈ T.powerset, subsetMobius f S = f T := by
  classical
  simp only [subsetMobius]
  rw [sum_comm' (t' := T.powerset) (s' := fun U => T.powerset.filter (U ⊆ ·))]
  · simp_rw [← sum_smul]
    rw [sum_eq_single T]
    · rw [sum_neg_one_pow_superset subset_rfl, ite_eq_left rfl, one_smul]
    · intro U hU hUT
      rw [sum_neg_one_pow_superset (mem_powerset.mp hU), ite_eq_right hUT, zero_smul]
    · exact (absurd (mem_powerset_self T) ·)
  · intro S U
    simp only [mem_powerset, mem_filter]
    exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => h.1⟩

/-- **The subset Möbius transform of a monomial**: at the indicators of subsets, the monomial of
`U` has transform `1` at `U` and `0` at every other set. -/
public theorem subsetMobius_monomial [DecidableEq ι] (U S : Finset ι) :
    subsetMobius (fun T => monomial R U fun i => decide (i ∈ T)) S = if U = S then 1 else 0 := by
  convert subset_kernel (R := R) U S using 1
  · rw [subsetMobius]
    exact sum_congr rfl fun T _ => by simp [monomial_apply, ← subset_iff, zsmul_eq_mul]
  · split_ifs <;> rfl

/-- **The subset Möbius transform vanishes above the degree**: for a function of degree at most
`D`, the transform of its values at the indicators of subsets vanishes at every set of more than
`D` elements. -/
public theorem subsetMobius_eq_zero_of_mem_lowDegree [DecidableEq ι] {D : ℕ}
    {f : (ι → Bool) → R} (hf : f ∈ lowDegree R ι D) {S : Finset ι} (hS : D < #S) :
    subsetMobius (fun T => f fun i => decide (i ∈ T)) S = 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨U, hU, rfl⟩ := hg
    exact (subsetMobius_monomial (R := R) U S).trans
      (ite_eq_right fun h => absurd (h ▸ hU) hS.not_ge)
  | zero => simp only [Pi.zero_apply, subsetMobius, smul_zero, sum_const_zero]
  | add g h _ _ hg hh => simp only [Pi.add_apply, subsetMobius_add, hg, hh, add_zero]
  | smul c g _ hg =>
    simpa only [AddMonoidHom.coe_mulLeft, hg, mul_zero, Pi.smul_apply, smul_eq_mul] using
      (map_subsetMobius (AddMonoidHom.mulLeft c) (fun T => g fun i => decide (i ∈ T)) S).symm

/-- The subset Möbius transform commutes with subtraction. -/
public theorem subsetMobius_sub (f g : Finset ι → M) (S : Finset ι) :
    subsetMobius (fun T => f T - g T) S = subsetMobius f S - subsetMobius g S := by
  simp only [subsetMobius, smul_sub, sum_sub_distrib]

/-- The subset Möbius transform commutes with finite sums. -/
public theorem subsetMobius_sum {κ : Type*} (s : Finset κ) (f : κ → Finset ι → M)
    (S : Finset ι) :
    subsetMobius (fun T => ∑ k ∈ s, f k T) S = ∑ k ∈ s, subsetMobius (f k) S := by
  simp only [subsetMobius, smul_sum]
  exact sum_comm

/-- The subset Möbius transform commutes with multiplication by a constant. -/
public theorem subsetMobius_const_mul (c : R) (f : Finset ι → R) (S : Finset ι) :
    subsetMobius (fun T => c * f T) S = c * subsetMobius f S :=
  (map_subsetMobius (AddMonoidHom.mulLeft c) f S).symm

/-- **Multiplying by a bit shifts the transform.** Multiplying the values `f T` by the bit of `i`
at the indicator of `T` gives the transform `μ S + μ (S \ {i})` at the sets containing `i`, and `0`
elsewhere, where `μ` is the transform of `f`. -/
public theorem subsetMobius_bitVal_mul [DecidableEq ι] (i : ι) (f : Finset ι → R)
    (S : Finset ι) :
    subsetMobius (fun T => bitVal R (decide (i ∈ T)) * f T) S =
      if i ∈ S then subsetMobius f S + subsetMobius f (S.erase i) else 0 := by
  have hzero {X : Finset ι} (hiX : i ∉ X) (k : ℕ) :
      ∑ T ∈ X.powerset, (-1 : ℤ) ^ (k - #T) • (bitVal R (decide (i ∈ T)) * f T) = 0 :=
    sum_eq_zero fun T hT => by
      rw [decide_eq_false (fun h => hiX (mem_powerset.1 hT h)), bitVal_false, zero_mul, smul_zero]
  split_ifs with hi
  · set S' := S.erase i with hS'
    have hiS' : i ∉ S' := notMem_erase i S
    rw [(insert_erase hi).symm, ← hS']
    simp only [subsetMobius, sum_powerset_insert hiS', card_insert_of_notMem hiS',
      mem_insert_self, decide_true, bitVal_true, one_mul, hzero hiS', zero_add]
    have h3 : ∑ T ∈ S'.powerset, ((-1 : ℤ) ^ (#S' + 1 - #T) • f T +
        (-1 : ℤ) ^ (#S' - #T) • f T) = 0 :=
      sum_eq_zero fun T hT => by
        have := card_le_card (mem_powerset.1 hT)
        rw [show #S' + 1 - #T = (#S' - #T) + 1 by omega, pow_succ, mul_neg_one, neg_smul,
          neg_add_cancel]
    rw [sum_add_distrib] at h3
    linear_combination -h3
  · exact hzero hi #S

end SubsetMobius

section MonomialExpansion

variable [Fintype ι] [DecidableEq ι]

/-- **A local function in the monomials of its scope**: if `g` depends only on the coordinates in
`I`, then `g x` is the sum over the subsets `S ⊆ I` of the subset Möbius transform of
`T ↦ g 1_T` at `S`, times the monomial of `S` at `x`. -/
public theorem eq_sum_subsetMobius_of_local {I : Finset ι} {g : (ι → Bool) → R}
    (hg : ∀ x y : ι → Bool, (∀ v ∈ I, x v = y v) → g x = g y) (x : ι → Bool) :
    g x = ∑ S ∈ I.powerset, subsetMobius (fun T => g fun v => decide (v ∈ T)) S *
      if ∀ v ∈ S, x v = true then 1 else 0 := by
  set W := I.filter fun v => x v = true
  have hgx : g x = g fun v => decide (v ∈ W) :=
    hg _ _ fun v hv => by simp only [W, mem_filter, hv, true_and, Bool.decide_eq_true]
  rw [hgx, ← sum_powerset_subsetMobius (fun T => g fun v => decide (v ∈ T)) W]
  simp only [mul_ite, mul_one, mul_zero, ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext S
  simp [W, subset_iff, forall_and]

/-- **Monomial expansion on the cube.** Every function on a finite cube is the combination of the
monomials with coefficients the subset Möbius transform of its values at indicators of sets: the
case `I = univ` of `Cslib.BitString.eq_sum_subsetMobius_of_local`. -/
public theorem eq_sum_subsetMobius_smul_monomial (g : (ι → Bool) → R) :
    g = ∑ S : Finset ι, subsetMobius (fun T => g fun i => decide (i ∈ T)) S • monomial R S := by
  funext x
  rw [eq_sum_subsetMobius_of_local (I := univ) (fun x y h => congrArg g (funext fun v =>
    h v (mem_univ v))) x, powerset_univ]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, monomial_apply]
  exact sum_congr rfl fun S _ => by congr

end MonomialExpansion

section MonomialExpansionFinite

variable [Finite ι] [DecidableEq ι]

/-- **Low degree through the Möbius transform.** A function on a finite cube has degree at most
`D` exactly when the subset Möbius transform of its values vanishes on every set of more than `D`
elements. -/
public theorem mem_lowDegree_iff_subsetMobius_eq_zero {D : ℕ} {g : (ι → Bool) → R} :
    g ∈ lowDegree R ι D ↔
      ∀ S : Finset ι, D < #S → subsetMobius (fun T => g fun i => decide (i ∈ T)) S = 0 := by
  have := Fintype.ofFinite ι
  refine ⟨fun hg S hS => subsetMobius_eq_zero_of_mem_lowDegree hg hS, fun hg => ?_⟩
  rw [eq_sum_subsetMobius_smul_monomial g]
  refine Submodule.sum_mem _ fun S _ => ?_
  by_cases hS : #S ≤ D
  · exact Submodule.smul_mem _ _ (monomial_mem_lowDegree hS)
  · rw [hg S (by omega), zero_smul]
    exact Submodule.zero_mem _

/-- A function on a finite cube whose subset Möbius transform vanishes everywhere is zero. -/
public theorem eq_zero_of_subsetMobius_eq_zero {g : (ι → Bool) → R}
    (hg : ∀ S : Finset ι, subsetMobius (fun T => g fun i => decide (i ∈ T)) S = 0) : g = 0 := by
  have := Fintype.ofFinite ι
  rw [eq_sum_subsetMobius_smul_monomial g]
  exact sum_eq_zero fun S _ => by rw [hg S, zero_smul]

end MonomialExpansionFinite

open Classical in
private noncomputable def reconstruction [Fintype ι] (q : ℕ) (x : ι → Bool) :
    ((ι → Bool) → R) →ₗ[R] R :=
  ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
    if ∀ i ∈ E, x i = true then
      ∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) •
        (LinearMap.proj (fun i => decide (i ∈ U)) : ((ι → Bool) → R) →ₗ[R] R)
    else 0

open Classical in
private theorem reconstruction_apply [Fintype ι] (q : ℕ) (x : ι → Bool)
    (f : (ι → Bool) → R) :
    reconstruction q x f =
      ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
        if ∀ i ∈ E, x i = true then
          ∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) * f (fun i => decide (i ∈ U))
        else 0 := by
  unfold reconstruction
  simp only [LinearMap.sum_apply]
  refine sum_congr rfl fun E _ => ?_
  split_ifs <;> simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, LinearMap.zero_apply]

open Classical in
private theorem reconstruction_monomial [Fintype ι] (q : ℕ) (x : ι → Bool)
    (S : Finset ι) (hS : #S ≤ q) :
    reconstruction q x (monomial R S) = monomial R S x := by
  rw [reconstruction_apply]
  simp_rw [monomial_apply, decide_eq_true_eq, ← Finset.subset_iff, subset_kernel]
  rw [sum_eq_single S]
  · simp
  · intro E _ hES
    simp [Ne.symm hES]
  · simp [hS]

open Classical in
/-- A low-degree function on the cube is reconstructed from its subset evaluations. -/
public theorem lowDegree_reconstruction [Fintype ι] {q : ℕ} {f : (ι → Bool) → R}
    (hf : f ∈ lowDegree R ι q) (x : ι → Bool) :
    f x = ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
      if ∀ i ∈ E, x i = true then
        ∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) * f (fun i => decide (i ∈ U))
      else 0 := by
  rw [← reconstruction_apply]
  induction hf using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨S, hS, rfl⟩ := h
    exact (reconstruction_monomial q x S hS).symm
  | zero => simp
  | add _ _ _ _ hf hg => simp only [Pi.add_apply, map_add, hf, hg]
  | smul _ _ _ hf => simp only [Pi.smul_apply, map_smul, hf]

private theorem aeval_bit_apply (p : MvPolynomial ι R) (x : ι → Bool) :
    (MvPolynomial.aeval (fun i (y : ι → Bool) => bitVal R (y i)) p) x =
      MvPolynomial.eval (fun i => bitVal R (x i)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr => simp only [map_add, Pi.add_apply, hp, hr]
  | mul_X p i hp => simp only [map_mul, Pi.mul_apply, MvPolynomial.aeval_X,
      MvPolynomial.eval_X, hp]

/-- The values of a polynomial of total degree at most `q` on the cube, read through `bitVal`,
lie in `lowDegree R ι q`. -/
public theorem eval_mem_lowDegree (p : MvPolynomial ι R) {q : ℕ}
    (hp : p.totalDegree ≤ q) :
    (fun x : ι → Bool => MvPolynomial.eval (fun i => bitVal R (x i)) p) ∈ lowDegree R ι q := by
  rw [lowDegree_eq_map_restrictTotalDegree]
  exact ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hp, funext (aeval_bit_apply p)⟩

open Classical in
/-- Boolean Möbius reconstruction for an assignment-dependent polynomial family, over any
commutative ring (Lemma 3.3, equation (3.10) of the cited manuscript). The polynomial evaluated
at `1_U` is still `p x`, indexed by the original assignment in the restricted inner sum. -/
public theorem sum_eval_eq_restricted_subsets [Fintype ι] (q : ℕ)
    (p : (ι → Bool) → MvPolynomial ι R) (hp : ∀ x, (p x).totalDegree ≤ q) :
    (∑ x : ι → Bool, MvPolynomial.eval (fun i => bitVal R (x i)) (p x)) =
      ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) *
          ∑ x ∈ (univ : Finset (ι → Bool)).filter (fun x => ∀ i ∈ E, x i = true),
            MvPolynomial.eval (fun i => bitVal R (decide (i ∈ U))) (p x) := by
  calc
    _ = ∑ x : ι → Bool,
        ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
          if ∀ i ∈ E, x i = true then
            ∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) *
              MvPolynomial.eval (fun i => bitVal R (decide (i ∈ U))) (p x)
          else 0 :=
      sum_congr rfl fun x _ => lowDegree_reconstruction (eval_mem_lowDegree (p x) (hp x)) x
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun E _ => ?_
      rw [← sum_filter, sum_comm]
      exact sum_congr rfl fun U _ => (mul_sum _ _ _).symm

end Cslib.BitString
