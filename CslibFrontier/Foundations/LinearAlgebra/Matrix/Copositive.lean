/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/Copositive.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Rat.ClearDenom
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BasicSolution
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Matrix

/-!
# Copositive Matrices and Polynomial-Size Integer Witnesses

A symmetric integer or rational matrix `M` is *copositive* if `x ⬝ᵥ M *ᵥ x ≥ 0` for all
entrywise nonnegative vectors `x`. By minimizing the quadratic form `x ⬝ᵥ M *ᵥ x` over the
compact standard simplex (`Convexity.StdSimplex`), KKT stationarity forces `M *ᵥ x*` to be
constant and strictly negative on the support of any negative minimizer `x*`. Applying
`Matrix.exists_int_nonneg_mulVec_eq` to the principal submatrix on that support produces a
nonnegative integer vector `p` with `p ⬝ᵥ M *ᵥ p < 0` whose entries are singly exponentially
bounded in the dimension and entry bit-length, hence of polynomial bit-length.

As a consequence, copositivity over `ℝ`, `ℚ`, and `ℕ` coincides for symmetric rational matrices.
[MurtyKabadi1987] is cited at paper level from bibliographic metadata only without inspecting
the published text; the KKT + `Matrix.exists_int_nonneg_mulVec_eq` proof and the explicit witness
bound `Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V`
are original to this library.

## Main definitions

- `Matrix.IsCopositive`: entrywise nonnegative vectors have nonnegative quadratic form.

## Main results

- `Matrix.dotProduct_add_smul_symm`: expansion of `x ⬝ᵥ M *ᵥ x` along `x + t • d` for
  symmetric matrices.
- `Matrix.dotProduct_submatrix_equiv`, `Matrix.IsCopositive.submatrix_equiv_iff`: quadratic
  form and copositivity invariance under simultaneous row-and-column equivalence reindexing.
- `Matrix.exists_nonneg_dotProduct_lt_zero_iff_stdSimplex`: non-copositivity is witnessed on
  `Convexity.StdSimplex`.
- `Matrix.dotProduct_scale_of_eq`, `Matrix.intCast_dotProduct_mulVec_nat`,
  `Rat.clearDenom_entry`: quadratic form scaling and rational denominator clearing.
- `Matrix.exists_nat_dotProduct_lt_zero_of_isSymm`: a non-copositive symmetric integer matrix has
  a bounded nonnegative integer certificate `p` with `p ⬝ᵥ M *ᵥ p < 0`.
- `Matrix.isCopositive_int_real_iff_nat`: copositivity over `ℝ` and `ℕ` coincide for symmetric
  integer matrices.
- `Matrix.exists_nat_dotProduct_lt_zero_of_rat`: rational version via a cleared common denominator.
- `Matrix.isCopositive_rat_iff_map_real`: copositivity over `ℚ` and `ℝ` coincide for symmetric
  rational matrices.
- `Matrix.isCopositive_rat_iff_nat`: copositivity over `ℚ` and `ℕ` coincide for symmetric
  rational matrices.

## References

- [MurtyKabadi1987] K. G. Murty and S. N. Kabadi, *Some NP-complete problems in quadratic and
  nonlinear programming*, Mathematical Programming 39(2), 1987, 117–129 (bibliographic metadata
  only; the published article text is uninspected, and no internal theorem numbers are claimed).
-/

public section

namespace Matrix

open Matrix

/-- A square matrix `M` over an ordered commutative semiring is *copositive* if `x ⬝ᵥ M *ᵥ x ≥ 0`
for every entrywise nonnegative vector `x`. -/
@[expose] def IsCopositive {V K : Type*} [Fintype V] [CommSemiring K] [PartialOrder K]
    (M : Matrix V V K) : Prop :=
  ∀ x : V → K, (∀ v, 0 ≤ x v) → 0 ≤ x ⬝ᵥ M *ᵥ x

/-- Expansion of the quadratic form of a symmetric matrix along `x + t • d`. -/
theorem dotProduct_add_smul_symm {V K : Type*} [Fintype V] [CommRing K]
    {M : Matrix V V K} (hSymm : M.IsSymm) (x d : V → K) (t : K) :
    (x + t • d) ⬝ᵥ (M *ᵥ (x + t • d)) =
      x ⬝ᵥ (M *ᵥ x) + 2 * t * (d ⬝ᵥ (M *ᵥ x)) + t ^ 2 * (d ⬝ᵥ (M *ᵥ d)) := by
  have hxMd : x ⬝ᵥ (M *ᵥ d) = d ⬝ᵥ (M *ᵥ x) := by
    rw [← dotProduct_transpose_mulVec M d x, hSymm]
  rw [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
    dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_dotProduct, hxMd]
  ring

/-- Reindexing the quadratic form of a matrix along an equivalence `e : W ≃ V`. -/
theorem dotProduct_submatrix_equiv {V W K : Type*} [Fintype V] [Fintype W] [CommSemiring K]
    (M : Matrix V V K) (e : W ≃ V) (x : W → K) :
    x ⬝ᵥ (M.submatrix e e *ᵥ x) = (x ∘ e.symm) ⬝ᵥ (M *ᵥ (x ∘ e.symm)) := by
  simp only [dotProduct, mulVec, submatrix_apply, Function.comp_apply]
  refine Fintype.sum_equiv e _ _ fun i => ?_
  simp only [Equiv.symm_apply_apply]
  refine congrArg (x i * ·) ?_
  exact Fintype.sum_equiv e _ _ fun _ => by simp only [Equiv.symm_apply_apply]

/-- Copositivity is invariant under simultaneous row-and-column reindexing by an equivalence. -/
theorem IsCopositive.submatrix_equiv_iff {V W K : Type*} [Fintype V] [Fintype W]
    [CommSemiring K] [PartialOrder K] (M : Matrix V V K) (e : W ≃ V) :
    (M.submatrix e e).IsCopositive ↔ M.IsCopositive := by
  constructor
  · intro hcop x hx
    have h := hcop (x ∘ e) fun w => hx (e w)
    rwa [dotProduct_submatrix_equiv M e (x ∘ e), Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] at h
  · intro hcop x hx
    rw [dotProduct_submatrix_equiv M e x]
    exact hcop (x ∘ e.symm) fun v => hx (e.symm v)

/-- A nonnegative vector whose entries sum to `1`, as a point of `Convexity.StdSimplex`. -/
private noncomputable def stdSimplexOfFun {V K : Type*} [Fintype V] [Semiring K] [PartialOrder K]
    (y : V → K) (hy0 : ∀ v, 0 ≤ y v) (hy1 : ∑ v, y v = 1) : Convexity.StdSimplex K V where
  weights := Finsupp.equivFunOnFinite.symm y
  nonneg := hy0
  total := by rwa [Finsupp.sum_fintype _ _ fun _ => rfl]

/-- Non-copositivity over a linearly ordered field is witnessed on the standard simplex
`Convexity.StdSimplex K V`. -/
theorem exists_nonneg_dotProduct_lt_zero_iff_stdSimplex {V K : Type*} [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] (M : Matrix V V K) :
    (∃ x : V → K, (∀ v, 0 ≤ x v) ∧ x ⬝ᵥ (M *ᵥ x) < 0) ↔
      ∃ x : Convexity.StdSimplex K V,
        (x.weights : V → K) ⬝ᵥ (M *ᵥ (x.weights : V → K)) < 0 := by
  refine ⟨fun ⟨x, hx0, hlt⟩ => ?_, fun ⟨x, hlt⟩ => ⟨_, x.weights_nonneg, hlt⟩⟩
  have hsum_pos : 0 < ∑ v, x v := by
    refine (Finset.sum_nonneg fun v _ => hx0 v).lt_of_ne fun hsum0 => hlt.not_ge ?_
    simp [dotProduct, (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hx0 w).1 hsum0.symm]
  refine ⟨stdSimplexOfFun ((∑ v, x v)⁻¹ • x)
    (fun v => mul_nonneg (inv_nonneg.2 hsum_pos.le) (hx0 v))
    (by simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, inv_mul_cancel₀ hsum_pos.ne']),
    ?_⟩
  change ((∑ v, x v)⁻¹ • x) ⬝ᵥ (M *ᵥ ((∑ v, x v)⁻¹ • x)) < 0
  rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  exact mul_neg_of_pos_of_neg (mul_pos (inv_pos.2 hsum_pos) (inv_pos.2 hsum_pos)) hlt

/-- Scaling a quadratic form when `c * M₁ i j = M₂ i j` entrywise. -/
theorem dotProduct_scale_of_eq {V K : Type*} [Fintype V] [CommSemiring K]
    {c : K} {M₁ M₂ : Matrix V V K} (hM : ∀ i j, c * M₁ i j = M₂ i j) (x : V → K) :
    c * (x ⬝ᵥ (M₁ *ᵥ x)) = x ⬝ᵥ (M₂ *ᵥ x) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  calc
    c * (x i * (M₁ i j * x j)) = x i * ((c * M₁ i j) * x j) := by ring
    _ = x i * (M₂ i j * x j) := by rw [hM i j]

/-- Casting an integer quadratic form evaluated on a `ℕ`-vector to any ring `K`. -/
theorem intCast_dotProduct_mulVec_nat {V K : Type*} [Fintype V] [Ring K]
    (M : Matrix V V ℤ) (p : V → ℕ) :
    (((fun i => (p i : ℤ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℤ)) : ℤ) : K) =
      (fun i => (p i : K)) ⬝ᵥ (M.map (Int.cast : ℤ → K) *ᵥ fun i => (p i : K)) := by
  simp only [dotProduct, mulVec, map_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

private theorem kkt_stationarity_on_simplex {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hSymm : M.IsSymm) {x : Fin n → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∑ i, x i = 1)
    (hmin : ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → ∑ i, y i = 1 → x ⬝ᵥ M *ᵥ x ≤ y ⬝ᵥ M *ᵥ y)
    {i j : Fin n} (hi : 0 < x i) (hj : 0 < x j) :
    (M *ᵥ x) i = (M *ᵥ x) j := by
  by_cases hij : i = j
  · subst hij
    rfl
  · by_contra hne
    set d : Fin n → ℝ := Pi.single i 1 - Pi.single j 1
    set a : ℝ := (M *ᵥ x) i - (M *ᵥ x) j
    set c : ℝ := d ⬝ᵥ M *ᵥ d
    have ha_ne : a ≠ 0 := sub_ne_zero.2 hne
    have hδ_pos : 0 < min (x i) (x j) := lt_min hi hj
    set t₀ : ℝ := min (min (x i) (x j)) (|a| / (2 * (|c| + 1)))
    have ht₀_pos : 0 < t₀ := by positivity
    have ht₀_xi : t₀ ≤ x i := le_trans (min_le_left _ _) (min_le_left _ _)
    have ht₀_xj : t₀ ≤ x j := le_trans (min_le_left _ _) (min_le_right _ _)
    have ht₀_c : t₀ ≤ |a| / (2 * (|c| + 1)) := min_le_right _ _
    have hquad_nonneg : ∀ t : ℝ, -x i ≤ t → t ≤ x j → 0 ≤ 2 * t * a + t ^ 2 * c := by
      intro t hti htj
      have hy0 (k) : 0 ≤ (x + t • d) k := by
        have := hx0 k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, Pi.sub_apply, Pi.single_apply]
        split_ifs <;> subst_vars <;> first | exact absurd rfl hij | linarith
      have hy1 : ∑ k, (x + t • d) k = 1 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, hx1,
          ← Finset.mul_sum, d, Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, sub_self, mul_zero, add_zero]
      have hdAx : d ⬝ᵥ M *ᵥ x = a := by
        simp only [d, a, Pi.sub_apply, dotProduct, Pi.single_apply, sub_mul,
          Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
      have hmin_y := hmin (x + t • d) hy0 hy1
      rw [dotProduct_add_smul_symm hSymm x d t, hdAx] at hmin_y
      exact sub_nonneg.1 (by linarith)
    have habs_bound : t₀ * |c| < |a| := by
      have hc1 : (0 : ℝ) < |c| + 1 := by positivity
      have hmul : t₀ * (2 * (|c| + 1)) ≤ |a| := (le_div_iff₀ (by positivity)).1 ht₀_c
      have hle : t₀ * |c| ≤ t₀ * (|c| + 1) := mul_le_mul_of_nonneg_left (by linarith) ht₀_pos.le
      nlinarith
    rcases lt_or_gt_of_ne ha_ne with ha_neg | ha_pos
    · have hnonneg := hquad_nonneg t₀ (by linarith [hx0 i]) ht₀_xj
      have ha_abs : |a| = -a := abs_of_neg ha_neg
      have htc : t₀ * c ≤ t₀ * |c| := mul_le_mul_of_nonneg_left (le_abs_self c) ht₀_pos.le
      nlinarith
    · have hnonneg := hquad_nonneg (-t₀) (by linarith) (by linarith [hx0 j])
      have ha_abs : |a| = a := abs_of_pos ha_pos
      have htc : (-t₀) ^ 2 * c ≤ t₀ ^ 2 * |c| := by
        rw [neg_sq]
        exact mul_le_mul_of_nonneg_left (le_abs_self c) (sq_nonneg t₀)
      nlinarith

private theorem exists_nat_dotProduct_lt_zero_of_isSymm_fin {n B : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    (hSymm : M.IsSymm) (hB : ∀ i j, |M i j| ≤ (B : ℤ))
    (hnc : ¬ (M.map (Int.cast : ℤ → ℝ)).IsCopositive) :
    ∃ p : Fin n → ℕ,
      (∀ i, p i ≤ Nat.factorial n * (n * (max B 1) ^ 2 + 1) ^ n) ∧
        (fun i => (p i : ℤ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℤ)) < 0 := by
  rw [IsCopositive] at hnc
  push Not at hnc
  obtain ⟨y₀, hy₀_neg⟩ :=
    (exists_nonneg_dotProduct_lt_zero_iff_stdSimplex (M.map (Int.cast : ℤ → ℝ))).1 hnc
  set MR : Matrix (Fin n) (Fin n) ℝ := M.map Int.cast
  have hweights : Continuous fun y : Convexity.StdSimplex ℝ (Fin n) => (y.weights : Fin n → ℝ) :=
    continuous_pi fun i => Convexity.StdSimplex.continuous_weights_apply ℝ i
  obtain ⟨xStd, _, hxmin⟩ := isCompact_univ.exists_isMinOn ⟨y₀, Set.mem_univ _⟩
    (hweights.dotProduct (continuous_const.matrix_mulVec hweights)).continuousOn
  let x : Fin n → ℝ := xStd.weights
  have hx0 : ∀ i, 0 ≤ x i := xStd.weights_nonneg
  have hx1 : ∑ i, x i = 1 := xStd.total_of_fintype
  set lam : ℝ := x ⬝ᵥ (MR *ᵥ x)
  have hlam_neg : lam < 0 := lt_of_le_of_lt (hxmin (Set.mem_univ y₀)) hy₀_neg
  -- On the support `S` of the minimizer `x`, KKT stationarity makes `MR *ᵥ x` constant (`= lam`).
  let S : Finset (Fin n) := Finset.univ.filter fun i => 0 < x i
  have hxout (i) (hi : i ∉ S) : x i = 0 := le_antisymm (by simpa [S] using hi) (hx0 i)
  obtain ⟨i₀, -, hi₀_pos⟩ :=
    Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℝ)) (g := x) (by simp [hx1])
  have hconst : ∀ i ∈ S, (MR *ᵥ x) i = (MR *ᵥ x) i₀ := fun i hi =>
    kkt_stationarity_on_simplex (hSymm.map _) hx0 hx1
      (fun y hy0 hy1 => hxmin (Set.mem_univ (stdSimplexOfFun y hy0 hy1)))
      (Finset.mem_filter.1 hi).2 hi₀_pos
  have hlam_eq : (MR *ᵥ x) i₀ = lam := by
    have hterm (i) : x i * (MR *ᵥ x) i = x i * (MR *ᵥ x) i₀ := by
      by_cases hi : i ∈ S
      · rw [hconst i hi]
      · rw [hxout i hi, zero_mul, zero_mul]
    simp only [lam, dotProduct, hterm, ← Finset.sum_mul, hx1, one_mul]
  -- Rescale `x` on `S` to a nonnegative solution of `MS z = -1` and round it to integers.
  let MS : Matrix S S ℤ := Matrix.of fun i j => M i.val j.val
  let B' : ℕ := max B 1
  have hMS_le : ∀ i j : S, |MS i j| ≤ (B' : ℤ) := fun i j =>
    (hB i.val j.val).trans (by exact_mod_cast le_max_left B 1)
  have hb_le : ∀ _ : S, |(-1 : ℤ)| ≤ (B' : ℤ) := fun _ => by simp [B']
  let z : S → ℝ := fun j => (-lam)⁻¹ * x j.val
  have hz_nonneg : 0 ≤ z := fun j =>
    mul_nonneg (inv_nonneg.2 (neg_pos.2 hlam_neg).le) (hx0 j.val)
  have hMSz : MS.map (Int.cast : ℤ → ℝ) *ᵥ z = fun _ => ((-1 : ℤ) : ℝ) := by
    ext i
    have hxS_sum : ∑ j : S, (M i.val j.val : ℝ) * x j.val = (MR *ᵥ x) i.val :=
      (Finset.sum_coe_sort S fun j => (M i.val j : ℝ) * x j).trans
        (Finset.sum_subset (Finset.subset_univ S) fun j _ hj => by rw [hxout j hj, mul_zero])
    simp only [mulVec, dotProduct, map_apply, MS, of_apply, z, mul_left_comm _ (-lam)⁻¹,
      ← Finset.mul_sum, Int.cast_neg, Int.cast_one]
    rw [hxS_sum, (hconst i.val i.property).trans hlam_eq]
    field_simp [hlam_neg.ne]
  obtain ⟨d, pS, hd_pos, hpS_nonneg, hAp, _, hpS_le⟩ :=
    Matrix.exists_int_nonneg_mulVec_eq (K := ℝ) hMS_le hb_le hz_nonneg hMSz
  let p : Fin n → ℕ := fun i => if hi : i ∈ S then (pS ⟨i, hi⟩).toNat else 0
  have hcard : Fintype.card S ≤ n := by simpa using S.card_le_univ
  refine ⟨p, fun i => ?_, ?_⟩
  · dsimp only [p]
    split_ifs with hi
    · refine Int.toNat_le.2 ((hpS_le ⟨i, hi⟩).trans (Int.ofNat_le.2 ?_))
      gcongr; omega
    · exact Nat.zero_le _
  · have hp (i : S) : (p i : ℤ) = pS i := by
      simp only [p, i.property, dite_true, Subtype.coe_eta, Int.toNat_of_nonneg (hpS_nonneg i)]
    have hsum (f : Fin n → ℤ) : ∑ j, f j * (p j : ℤ) = ∑ j : S, f j * pS j := by
      rw [← Finset.sum_subset (Finset.subset_univ S) fun j _ hj => by simp [p, hj],
        ← Finset.sum_coe_sort S]
      simp only [hp]
    have hMp (i : S) : (M *ᵥ fun j => (p j : ℤ)) i = -d := by
      simpa [mulVec, dotProduct, hsum, MS] using congrFun hAp i
    have hpS_sum_pos : 0 < ∑ i : S, pS i := by
      refine (Finset.sum_nonneg fun i _ => hpS_nonneg i).lt_of_ne fun h0 => ?_
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hpS_nonneg i).1 h0.symm
      have := hMp ⟨i₀, by simpa [S] using hi₀_pos⟩
      simp only [mulVec, dotProduct, hsum, hz, Finset.mem_univ, mul_zero,
        Finset.sum_const_zero] at this
      omega
    rw [dotProduct_comm, dotProduct, hsum]
    simp only [hMp, ← Finset.mul_sum]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.2 hd_pos) hpS_sum_pos

/-- If a symmetric integer matrix `M` has a nonnegative real vector with negative quadratic form,
then it has a nonnegative integer vector `p` with `p ⬝ᵥ M *ᵥ p < 0` and entries bounded by
`Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V`, where
`B` bounds `|M i j|`. (The KKT + `Matrix.exists_int_nonneg_mulVec_eq` proof and this explicit
bound are this library's formulation, not verified against [MurtyKabadi1987].) -/
theorem exists_nat_dotProduct_lt_zero_of_isSymm {V : Type*} [Fintype V] {B : ℕ} {M : Matrix V V ℤ}
    (hSymm : M.IsSymm) (hB : ∀ i j, |M i j| ≤ (B : ℤ))
    (hnc : ¬ (M.map (Int.cast : ℤ → ℝ)).IsCopositive) :
    ∃ p : V → ℕ,
      (∀ v, p v ≤
          Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V) ∧
        (fun v => (p v : ℤ)) ⬝ᵥ (M *ᵥ fun v => (p v : ℤ)) < 0 := by
  classical
  obtain ⟨e⟩ := Fintype.truncEquivFin V
  let M_fin : Matrix (Fin (Fintype.card V)) (Fin (Fintype.card V)) ℤ :=
    M.submatrix e.symm e.symm
  have hSymm_fin : M_fin.IsSymm := by
    ext i j
    simp only [M_fin, transpose_apply, submatrix_apply]
    exact congrFun (congrFun hSymm (e.symm i)) (e.symm j)
  have hB_fin : ∀ i j, |M_fin i j| ≤ (B : ℤ) := fun i j => hB (e.symm i) (e.symm j)
  have hnc_fin : ¬ (M_fin.map (Int.cast : ℤ → ℝ)).IsCopositive := by
    have hmap : M_fin.map (Int.cast : ℤ → ℝ) = (M.map (Int.cast : ℤ → ℝ)).submatrix e.symm e.symm :=
      rfl
    rwa [hmap, IsCopositive.submatrix_equiv_iff]
  obtain ⟨p_fin, hp_le, hp_neg⟩ :=
    exists_nat_dotProduct_lt_zero_of_isSymm_fin hSymm_fin hB_fin hnc_fin
  refine ⟨fun v => p_fin (e v), fun v => hp_le (e v), ?_⟩
  have hdotZ := dotProduct_submatrix_equiv M e.symm (fun i => (p_fin i : ℤ))
  simpa only [Function.comp_def, Equiv.symm_symm] using hdotZ ▸ hp_neg

/-- For a symmetric integer matrix, copositivity over `ℝ` coincides with nonnegativity on all
nonnegative integer vectors. -/
theorem isCopositive_int_real_iff_nat {V : Type*} [Fintype V] {M : Matrix V V ℤ}
    (hSymm : M.IsSymm) :
    (M.map (Int.cast : ℤ → ℝ)).IsCopositive ↔
      ∀ p : V → ℕ, 0 ≤ (fun i => (p i : ℤ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℤ)) := by
  constructor
  · intro hcop p
    have hreal := hcop (fun i => (p i : ℝ)) fun i => Nat.cast_nonneg (p i)
    rw [← intCast_dotProduct_mulVec_nat (K := ℝ) M p] at hreal
    exact not_lt.1 fun hn => not_le_of_gt (Int.cast_lt_zero (R := ℝ).2 hn) hreal
  · intro hnat
    by_contra hnc
    have hB (i j) : |M i j| ≤ ((Finset.univ.sup fun p : V × V => (M p.1 p.2).natAbs : ℕ) : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast Finset.le_sup (f := fun p : V × V => (M p.1 p.2).natAbs)
        (Finset.mem_univ (i, j))
    obtain ⟨p, _, hp_neg⟩ := exists_nat_dotProduct_lt_zero_of_isSymm hSymm hB hnc
    exact (not_lt_of_ge (hnat p)) hp_neg

private theorem isCopositive_of_map_real {V : Type*} [Fintype V] {M : Matrix V V ℚ}
    (hcopR : (M.map (Rat.cast : ℚ → ℝ)).IsCopositive) : M.IsCopositive := by
  intro x hx
  have hR := hcopR (fun i => ((x i : ℚ) : ℝ)) fun i => Rat.cast_nonneg.2 (hx i)
  have hcast :
      (Rat.cast (x ⬝ᵥ (M *ᵥ x)) : ℝ) =
        (fun i => ((x i : ℚ) : ℝ)) ⬝ᵥ (M.map (Rat.cast : ℚ → ℝ) *ᵥ fun i => ((x i : ℚ) : ℝ)) := by
    simp only [dotProduct, mulVec, map_apply, Rat.cast_sum, Rat.cast_mul]
  rw [← hcast] at hR
  exact Rat.cast_nonneg.1 hR

private theorem exists_rat_clearDenom {V : Type*} [Finite V] (M : Matrix V V ℚ) :
    ∃ (d B : ℕ) (M_Z : Matrix V V ℤ),
      0 < d ∧ (∀ i j, (d : ℚ) * M i j = (M_Z i j : ℚ)) ∧ ∀ i j, |M_Z i j| ≤ (B : ℤ) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let d : ℕ := Finset.univ.prod fun p : V × V => (M p.1 p.2).den
  have hd : 0 < d := Finset.prod_pos fun p _ => (M p.1 p.2).pos
  let M_Z : Matrix V V ℤ := Matrix.of fun i j =>
    (M i j).num * ((d / (M i j).den : ℕ) : ℤ)
  have hMZ : ∀ i j, (d : ℚ) * M i j = (M_Z i j : ℚ) := fun i j => by
    have hdvd : (M i j).den ∣ d :=
      Finset.dvd_prod_of_mem (fun p : V × V => (M p.1 p.2).den) (Finset.mem_univ (i, j))
    simpa only [M_Z, of_apply] using Rat.clearDenom_entry hdvd
  refine ⟨d, Finset.univ.sup fun p : V × V => (M_Z p.1 p.2).natAbs, M_Z, hd, hMZ, fun i j => ?_⟩
  rw [← Int.natCast_natAbs]
  exact_mod_cast Finset.le_sup (f := fun p : V × V => (M_Z p.1 p.2).natAbs) (Finset.mem_univ (i, j))

private theorem exists_nat_dotProduct_lt_zero_of_rat_real {V : Type*} [Fintype V] {d B : ℕ}
    {M : Matrix V V ℚ} {M_Z : Matrix V V ℤ}
    (hd : 0 < d) (hSymm : M.IsSymm) (hMZ : ∀ i j, (d : ℚ) * M i j = (M_Z i j : ℚ))
    (hB : ∀ i j, |M_Z i j| ≤ (B : ℤ)) (hnc : ¬ (M.map (Rat.cast : ℚ → ℝ)).IsCopositive) :
    ∃ p : V → ℕ,
      (∀ i, p i ≤
          Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V) ∧
        (fun i => (p i : ℚ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℚ)) < 0 := by
  have hSymmZ : M_Z.IsSymm := by
    ext i j
    apply Int.cast_injective (α := ℚ)
    rw [transpose_apply, ← hMZ j i, ← hMZ i j]
    exact congrArg (fun z : ℚ => (d : ℚ) * z) (congrFun (congrFun hSymm i) j)
  have hncZ : ¬ (M_Z.map (Int.cast : ℤ → ℝ)).IsCopositive := by
    intro hcopZ
    apply hnc
    intro x hx
    have hrealZ := hcopZ x hx
    have hscale := dotProduct_scale_of_eq (c := (d : ℝ))
      (M₁ := M.map (Rat.cast : ℚ → ℝ)) (M₂ := M_Z.map (Int.cast : ℤ → ℝ))
      (fun i j => by
        have hcast := congrArg (Rat.cast : ℚ → ℝ) (hMZ i j)
        simpa only [map_apply, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast] using hcast) x
    rw [← hscale] at hrealZ
    exact (mul_nonneg_iff_of_pos_left (Nat.cast_pos.2 hd)).1 hrealZ
  obtain ⟨p, hp_le, hp_negZ⟩ := exists_nat_dotProduct_lt_zero_of_isSymm hSymmZ hB hncZ
  refine ⟨p, hp_le, ?_⟩
  have hscaleQ := dotProduct_scale_of_eq (c := (d : ℚ)) (M₁ := M)
    (M₂ := M_Z.map (Int.cast : ℤ → ℚ))
    (fun i j => by simpa only [map_apply] using hMZ i j) (fun i => (p i : ℚ))
  rw [← intCast_dotProduct_mulVec_nat (K := ℚ) M_Z p] at hscaleQ
  have hnegQ : (((fun i => (p i : ℤ)) ⬝ᵥ (M_Z *ᵥ fun i => (p i : ℤ)) : ℤ) : ℚ) < 0 :=
    Int.cast_lt_zero.2 hp_negZ
  rw [← hscaleQ] at hnegQ
  exact lt_of_not_ge fun h => not_lt_of_ge (mul_nonneg (Nat.cast_nonneg d) h) hnegQ

/-- Given a symmetric rational matrix `M` and an integer scaling `(d : ℚ) * M = M_Z` with `0 < d`
and `|M_Z i j| ≤ B`, non-copositivity of `M` yields a nonnegative integer certificate `p` with
`p ⬝ᵥ M *ᵥ p < 0` and entries bounded by
`Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V`
(library proof and bound, not verified against [MurtyKabadi1987]). -/
theorem exists_nat_dotProduct_lt_zero_of_rat {V : Type*} [Fintype V] {d B : ℕ}
    {M : Matrix V V ℚ} {M_Z : Matrix V V ℤ}
    (hd : 0 < d) (hSymm : M.IsSymm) (hMZ : ∀ i j, (d : ℚ) * M i j = (M_Z i j : ℚ))
    (hB : ∀ i j, |M_Z i j| ≤ (B : ℤ)) (hnc : ¬ M.IsCopositive) :
    ∃ p : V → ℕ,
      (∀ i, p i ≤
          Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V) ∧
        (fun i => (p i : ℚ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℚ)) < 0 :=
  exists_nat_dotProduct_lt_zero_of_rat_real hd hSymm hMZ hB fun hreal =>
    hnc (isCopositive_of_map_real hreal)

/-- For a symmetric rational matrix, copositivity over `ℚ` and over `ℝ` coincide. -/
theorem isCopositive_rat_iff_map_real {V : Type*} [Fintype V] {M : Matrix V V ℚ}
    (hSymm : M.IsSymm) :
    M.IsCopositive ↔ (M.map (Rat.cast : ℚ → ℝ)).IsCopositive := by
  constructor
  · intro hcop
    by_contra hncR
    obtain ⟨d, B, M_Z, hd, hMZ, hB⟩ := exists_rat_clearDenom M
    obtain ⟨p, _, hp_neg⟩ := exists_nat_dotProduct_lt_zero_of_rat_real hd hSymm hMZ hB hncR
    exact (not_lt_of_ge (hcop (fun i => (p i : ℚ)) fun i => Nat.cast_nonneg (p i))) hp_neg
  · exact isCopositive_of_map_real

/-- For a symmetric rational matrix, copositivity over `ℚ` coincides with nonnegativity on all
nonnegative integer vectors. -/
theorem isCopositive_rat_iff_nat {V : Type*} [Fintype V] {M : Matrix V V ℚ} (hSymm : M.IsSymm) :
    M.IsCopositive ↔ ∀ p : V → ℕ, 0 ≤ (fun i => (p i : ℚ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℚ)) := by
  constructor
  · intro hcop p
    exact hcop (fun i => (p i : ℚ)) fun i => Nat.cast_nonneg (p i)
  · intro hnat
    by_contra hnc
    obtain ⟨d, B, M_Z, hd, hMZ, hB⟩ := exists_rat_clearDenom M
    obtain ⟨p, _, hp_neg⟩ := exists_nat_dotProduct_lt_zero_of_rat hd hSymm hMZ hB hnc
    exact (not_lt_of_ge (hnat p)) hp_neg

end Matrix
