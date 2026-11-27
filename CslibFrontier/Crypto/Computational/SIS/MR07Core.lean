/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.Lattice.GIVP
public import CslibFrontier.Crypto.Computational.SIS.Ell2
public import CslibFrontier.Foundations.Analysis.Lattice.Dual
public import CslibFrontier.Foundations.Probability.Gaussian.Discrete
public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.StatisticalDistance.CloseTo

import CslibFrontier.Foundations.Probability.Gaussian.MassBounds
import CslibFrontier.Foundations.Probability.Gaussian.MomentsDiscrete
import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance.Product
import CslibFrontier.Probability.Uniform
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite distributional core of the Micciancio–Regev `IncGDD` to `ℓ₂`-SIS reduction

This module formalizes the non-asymptotic, single-call distributional core of the reduction from
incremental guaranteed distance decoding (`IncGDD`) to the Euclidean short integer solution problem
(`ℓ₂`-SIS) from [MicciancioRegev2007] (§5.2, pp. 20–24), formulated on the fine discrete grid
`G_q = (1 / q) ℤⁿ` with ideal discrete-grid and quotient samplers and an explicit dual-mass premise.

Strict-PPT sampler realization, independent amplification, iterative basis shortening, and the
asymptotic worst-case-to-average-case theorems (`Theorem 5.9`, `Corollary 5.13`, `Theorem 5.16`)
are not formalized here; they are tracked separately in
[#6861](https://github.com/cslib-community/cslib-frontier/issues/6861).

## Main definitions

* `Cslib.Crypto.SIS.MR07.intCol`, `intLattice`, `gridLattice`, `modParallelepiped`, `GridRep`,
  `SublatticeQuot`: full-rank integer lattice bases, the fine grid `G_q = (1 / q) ℤⁿ`, and finite
  parallelepiped representative types.
* `Cslib.Crypto.SIS.MR07.idealGridSample`: ideal discrete-grid sampler producing `(c, y)` with
  `c ∈ G_q ∩ P(B)` and `y ∈ L(B)`.
* `Cslib.Crypto.SIS.MR07.quotientHom`, `combineColumn`, `combineMatrix`, `combineOutput`: HNF-free
  quotient surjection `(ℤ / D ℤ)ⁿ ↠ L(B) ∩ P(S)` (`D = |det(B⁻¹ S)|`) and discrete-grid combining
  procedure.
* `Cslib.Crypto.SIS.MR07.idealIncGDDStep`: single-call finite distributional `IncGDD` step using
  ideal discrete-grid and quotient samplers.

## Main results

* `Cslib.Crypto.SIS.MR07.card_gridRep`, `card_sublatticeQuot`, `gaussianMass_dual_gridLattice_le`:
  exact cardinalities and dual-mass monotonicity for the discrete grid `G_q = (1 / q) ℤⁿ`.
* `Cslib.Crypto.SIS.MR07.idealGridSample_eq_bind_discreteGaussian`,
  `idealGridSample_fst_closeTo_uniform`: finite discrete-grid sampling lemma (discrete-grid step
  toward [MicciancioRegev2007], Lemma 5.7, p. 20).
* `Cslib.Crypto.SIS.MR07.map_quotientHom_uniform_eq_uniform_sublatticeQuot`,
  `idealCombine_matrix_eq_uniform`, `combineOutput_mem_intLattice`,
  `combineOutput_mem_intLattice_and_norm_sub_le`: HNF-free uniform quotient sampling and
  discrete-grid combining lemma (discrete-grid step toward [MicciancioRegev2007], Lemma 5.8,
  pp. 20–21), with unconditional lattice membership of `combineOutput`.
* `Cslib.Crypto.SIS.MR07.idealIncGDDStep_support_mem_intLattice`,
  `idealIncGDDStep_succProb_of_sisEll2`, `incGDD_succProb_of_closeTo_idealIncGDDStep`:
  unconditional output membership in `L(B)`, single-call success probability lower bound
  `(1 / 3) * (δ / (2 * ⌊β⌋ * m) - m * ε / (2 * (1 - ε)))` (finite distributional step toward
  [MicciancioRegev2007], Theorem 5.9, pp. 22–24), and `CloseTo` transfer to approximate samplers.

## References

* [D. Micciancio and O. Regev, *Worst-Case to Average-Case Reductions Based on Gaussian
  Measures*][MicciancioRegev2007], §2 (p. 8) and §5.2 (Lemmas 5.7–5.8 and Theorem 5.9,
  pp. 20–24 of the December 27, 2005 author's copy).
-/

public section

namespace Cslib.Crypto.SIS.MR07

open ZLattice Module MeasureTheory ProbabilityTheory Cslib.Probability
open scoped _root_.Matrix BigOperators ENNReal NNReal RealInnerProductSpace

/-! ### Part 1: Integer lattice bases, fine grid, parallelepiped representatives, dual bounds -/

/-- Column `j` of an integer matrix `B` viewed in `EuclideanSpace ℝ (Fin n)`. -/
@[expose] def intCol {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => (B i j : ℝ)

/-- Integer lattice `L(B) ⊂ ℝⁿ` spanned by the columns of `B`. -/
@[expose] def intLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℤ (Set.range (intCol B))

/-- Fine discrete grid lattice `G_q = (1 / q) ℤⁿ ⊂ ℝⁿ`. [MicciancioRegev2007] §2 (p. 8) remarks in
prose on fine-grid discretization; setting `G_q = (1 / q) ℤⁿ` at the SIS modulus `q` is this
module's representation choice. -/
@[expose] noncomputable def gridLattice (n q : ℕ) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℤ (Set.range fun j : Fin n =>
    ((q : ℝ)⁻¹ : ℝ) • EuclideanSpace.basisFun (Fin n) ℝ j)

/-- Real matrix cast of an integer matrix. -/
abbrev matR {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  B.map Int.cast

/-- Embed an integer vector in `EuclideanSpace ℝ (Fin n)`. -/
private noncomputable abbrev toVecℤ {n : ℕ} (v : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => (v i : ℝ)

/-- Embed a `G_q` grid integer coordinate vector `(1 / q) • v` in `EuclideanSpace ℝ (Fin n)`. -/
private noncomputable abbrev gridVec {n : ℕ} (q : ℕ) (u : Fin n → ℤ) :
    EuclideanSpace ℝ (Fin n) :=
  ((q : ℝ)⁻¹ : ℝ) • toVecℤ u

/-- The real cast of an integer matrix with nonzero determinant has unit determinant. -/
theorem isUnit_matR_det {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0) :
    IsUnit (matR B).det := by
  refine isUnit_iff_ne_zero.mpr ?_
  rw [show (matR B).det = (B.det : ℝ) by simpa [matR] using ((Int.castRingHom ℝ).map_det B).symm]
  exact Int.cast_ne_zero.mpr hB

/-- Right-inverse identity `matR B * (matR B)⁻¹ = 1` for `B.det ≠ 0`. -/
theorem matR_mul_inv {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0) :
    matR B * (matR B)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv (matR B) (isUnit_matR_det hB)

/-- Left-inverse identity `(matR B)⁻¹ * matR B = 1` for `B.det ≠ 0`. -/
theorem matR_inv_mul {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0) :
    (matR B)⁻¹ * matR B = 1 :=
  Matrix.nonsing_inv_mul (matR B) (isUnit_matR_det hB)

private theorem toVecℤ_injective {n : ℕ} : Function.Injective (toVecℤ (n := n)) :=
  fun _ _ h => funext fun i => Int.cast_injective (congrArg (fun v => v i) h)

private theorem gridVec_injective {n q : ℕ} (hq : 0 < q) :
    Function.Injective (gridVec (n := n) q) := by
  intro u v h
  exact toVecℤ_injective (smul_right_injective _ (inv_ne_zero (Nat.cast_ne_zero.mpr hq.ne')) h)

private theorem gridVec_mul_nat {n q : ℕ} (hq : 0 < q) (v : Fin n → ℤ) :
    gridVec q (fun i => (q : ℤ) * v i) = toVecℤ v := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  ext i
  simp [inv_mul_cancel_left₀ hq0]

private theorem ofLp_toVecℤ_mulVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Fin n → ℤ) :
    WithLp.ofLp (toVecℤ (B *ᵥ k)) = matR B *ᵥ fun j => (k j : ℝ) := by
  funext i
  simp [matR, Matrix.mulVec, dotProduct]

private theorem matR_mulVec_eq_sum_intCol {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℝ) :
    WithLp.toLp 2 (matR B *ᵥ v) = ∑ j : Fin n, v j • intCol B j := by
  ext i
  simp [intCol, matR, Matrix.mulVec, dotProduct, mul_comm]

private theorem norm_sq_toVecℤ {m : ℕ} (z : Fin m → ℤ) :
    ∑ j : Fin m, (z j : ℝ) ^ 2 = ‖toVecℤ z‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

private theorem sum_abs_le_sqrt_mul_norm {m : ℕ} (z : Fin m → ℤ) :
    ∑ j : Fin m, |(z j : ℝ)| ≤ Real.sqrt m * ‖toVecℤ z‖ := by
  have hsq := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
    (f := fun j => |(z j : ℝ)|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs, norm_sq_toVecℤ] at hsq
  rw [show (m : ℝ) * ‖toVecℤ z‖ ^ 2 = (Real.sqrt m * ‖toVecℤ z‖) ^ 2 by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]] at hsq
  exact le_of_sq_le_sq hsq (by positivity)

/-- The columns of an invertible integer matrix `B` form an `ℝ`-basis of
`EuclideanSpace ℝ (Fin n)`. -/
private noncomputable def intColBasis {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  Basis.ofEquivFun
    { toFun := fun x => (matR B)⁻¹ *ᵥ WithLp.ofLp x
      map_add' := fun _ _ => Matrix.mulVec_add _ _ _
      map_smul' := fun _ _ => Matrix.mulVec_smul _ _ _
      invFun := fun v => WithLp.toLp 2 (matR B *ᵥ v)
      left_inv := fun x => by
        ext i; change (matR B *ᵥ ((matR B)⁻¹ *ᵥ WithLp.ofLp x)) i = x i
        rw [Matrix.mulVec_mulVec, matR_mul_inv hB, Matrix.one_mulVec]
      right_inv := fun v => by
        change (matR B)⁻¹ *ᵥ (matR B *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, matR_inv_mul hB, Matrix.one_mulVec] }

private theorem intLattice_eq_span_basis {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    intLattice B = Submodule.span ℤ (Set.range (intColBasis B hB)) := by
  have hcoe : ⇑(intColBasis B hB) = intCol B := by
    ext j i; simp [intColBasis, intCol, matR]
  rw [intLattice, hcoe]

/-- Every integer lattice `intLattice B` is discrete in `EuclideanSpace ℝ (Fin n)`. -/
instance discreteTopology_intLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    DiscreteTopology (intLattice B) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  refine DiscreteTopology.of_subset (inferInstance : DiscreteTopology (Submodule.span ℤ
    (Set.range b))) (Submodule.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  have heq : intCol B j = ∑ i : Fin n, B i j • b i := by
    ext i; simp [intCol, b, EuclideanSpace.basisFun_apply, Pi.single_apply]
  rw [SetLike.mem_coe, heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Full-rank integer lattices are full-rank `ℤ`-lattices in `EuclideanSpace ℝ (Fin n)`. -/
theorem isZLattice_intLattice {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0) :
    IsZLattice ℝ (intLattice B) :=
  ⟨by rw [intLattice_eq_span_basis B hB]; exact IsZLattice.span_top⟩

/-- Rank of a full-rank integer lattice equals the ambient dimension `n`. -/
theorem finrank_intLattice {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0) :
    Module.finrank ℤ (intLattice B) = n := by
  have := isZLattice_intLattice hB
  rw [ZLattice.rank ℝ (intLattice B), finrank_euclideanSpace_fin]

/-- Transport the columns of `S` across `finrank_intLattice hB` to match `Fin (finrank ℤ L)`. -/
@[expose] noncomputable def intColCast {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    Fin (Module.finrank ℤ (intLattice B)) → EuclideanSpace ℝ (Fin n) :=
  intCol S ∘ Fin.cast (finrank_intLattice hB)

/-- Transporting `intCol S` across `finrank_intLattice` preserves its Pi supremum norm. -/
theorem norm_intColCast {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    ‖intColCast B S hB‖ = ‖intCol S‖ := by
  refine le_antisymm ?_ ?_ <;> rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)] <;> intro i
  · exact norm_le_pi_norm (intCol S) _
  · simpa [intColCast] using norm_le_pi_norm (intColCast B S hB)
      (Fin.cast (finrank_intLattice hB).symm i)

/-- The `ℝ`-basis of the fine grid `G_q = (1 / q) ℤⁿ`. -/
private noncomputable def gridBasis (n q : ℕ) (hq : 0 < q) :
    Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.unitsSMul
    (fun _ => Units.mk0 ((q : ℝ)⁻¹) (inv_ne_zero (Nat.cast_ne_zero.mpr hq.ne')))

private theorem gridLattice_eq_span_basis {n q : ℕ} (hq : 0 < q) :
    gridLattice n q = Submodule.span ℤ (Set.range (gridBasis n q hq)) := by
  unfold gridLattice gridBasis; congr 1; ext x; simp [Basis.unitsSMul_apply]

/-- The fine grid `G_q = (1 / q) ℤⁿ` is discrete for every `q : ℕ`. -/
instance discreteTopology_gridLattice (n q : ℕ) : DiscreteTopology (gridLattice n q) := by
  rcases q.eq_zero_or_pos with rfl | hq
  · have hbot : gridLattice n 0 = ⊥ :=
      Submodule.span_eq_bot.mpr fun _ ⟨_, hj⟩ => by simpa using hj.symm
    have : Subsingleton (gridLattice n 0) := by rw [hbot]; infer_instance
    infer_instance
  · rw [gridLattice_eq_span_basis hq]; infer_instance

/-- The fine grid `G_q = (1 / q) ℤⁿ` is a full-rank `ℤ`-lattice for `q > 0`. -/
theorem isZLattice_gridLattice {n q : ℕ} (hq : 0 < q) :
    IsZLattice ℝ (gridLattice n q) :=
  ⟨by rw [gridLattice_eq_span_basis hq]; exact IsZLattice.span_top⟩

/-- Characterization of membership in `intLattice B`. -/
theorem mem_intLattice_iff {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ intLattice B ↔ ∃ k : Fin n → ℤ, x = WithLp.toLp 2 (fun i => ((B *ᵥ k) i : ℝ)) := by
  rw [intLattice, Submodule.mem_span_range_iff_exists_fun]
  exact exists_congr fun k => by
    rw [eq_comm, show WithLp.toLp 2 (fun i => ((B *ᵥ k) i : ℝ)) = ∑ j : Fin n, k j • intCol B j by
      ext i; simp [intCol, Matrix.mulVec, dotProduct, mul_comm]]

/-- Characterization of membership in `gridLattice n q`. -/
theorem mem_gridLattice_iff {n q : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ gridLattice n q ↔
      ∃ u : Fin n → ℤ, x = ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ)) := by
  rw [gridLattice, Submodule.mem_span_range_iff_exists_fun]
  exact exists_congr fun u => by
    rw [eq_comm, show ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ)) =
      ∑ j : Fin n, u j • (((q : ℝ)⁻¹ : ℝ) • EuclideanSpace.basisFun (Fin n) ℝ j) by
      ext i; simp [EuclideanSpace.basisFun_apply, Pi.single_apply, mul_comm]]

/-- Every integer lattice is contained in the fine grid `G_q` for `q > 0`. -/
theorem intLattice_le_gridLattice {n q : ℕ} (hq : 0 < q) (B : Matrix (Fin n) (Fin n) ℤ) :
    intLattice B ≤ gridLattice n q := by
  intro x hx
  obtain ⟨k, rfl⟩ := (mem_intLattice_iff B x).1 hx
  exact (mem_gridLattice_iff _).2 ⟨fun i => (q : ℤ) * (B *ᵥ k) i, (gridVec_mul_nat hq _).symm⟩

/-- Dual-mass monotonicity from `intLattice B` to the fine grid `gridLattice n q`. -/
theorem gaussianMass_dual_gridLattice_le {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    {q : ℕ} (hq : 0 < q) {s : ℝ} (hs : 0 < s) :
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n)))
        (gridLattice n q)) (1 / s) 0 - 1 ≤
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n)))
        (intLattice B)) (1 / s) 0 - 1 := by
  have := isZLattice_intLattice hB
  have := isZLattice_gridLattice (n := n) hq
  have := discreteTopology_dualSubmodule (intLattice B)
  have := discreteTopology_dualSubmodule (gridLattice n q)
  have hsub : LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n)))
      (gridLattice n q) ≤
      LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B) :=
    fun _ hw y hy => hw y (intLattice_le_gridLattice hq B hy)
  have hinv : 0 < 1 / s := one_div_pos.mpr hs
  refine sub_le_sub_right ?_ 1
  exact (summable_gaussianWeight _ (1 / s) hinv 0).tsum_le_tsum_of_inj
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)
    (fun _ _ => (gaussianWeight_pos _ _).le) (fun _ => le_rfl)
    (summable_gaussianWeight _ (1 / s) hinv 0)

/-- Parallelepiped representative `x mod P(B) = B * frac(B⁻¹ x)` for invertible `B`. -/
@[expose] noncomputable def modParallelepiped {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  let Bℝ : Matrix (Fin n) (Fin n) ℝ := B.map Int.cast
  let ξ := Bℝ⁻¹ *ᵥ (WithLp.ofLp x)
  WithLp.toLp 2 (Bℝ *ᵥ fun k => ξ k - (Int.floor (ξ k) : ℝ))

private theorem modParallelepiped_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    modParallelepiped B 0 = 0 := by
  ext i; simp [modParallelepiped, Matrix.mulVec, dotProduct]

private theorem inv_mulVec_modParallelepiped {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    (matR B)⁻¹ *ᵥ WithLp.ofLp (modParallelepiped B x) =
      fun k => Int.fract (((matR B)⁻¹ *ᵥ WithLp.ofLp x) k) := by
  change (matR B)⁻¹ *ᵥ (matR B *ᵥ fun k => _ - (Int.floor _ : ℝ)) = _
  rw [Matrix.mulVec_mulVec, matR_inv_mul hB, Matrix.one_mulVec]
  rfl

private theorem sub_modParallelepiped_mem {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) : x - modParallelepiped B x ∈ intLattice B := by
  let ξ := (matR B)⁻¹ *ᵥ WithLp.ofLp x
  refine (mem_intLattice_iff B _).2 ⟨fun k => Int.floor (ξ k), ?_⟩
  ext i
  have hx : WithLp.ofLp x = matR B *ᵥ ξ := by
    simp [ξ, Matrix.mulVec_mulVec, matR_mul_inv hB]
  rw [PiLp.sub_apply, modParallelepiped]
  change (WithLp.ofLp x - matR B *ᵥ (fun k => ξ k - (Int.floor (ξ k) : ℝ))) i = _
  rw [hx, ← Matrix.mulVec_sub]
  simp [matR, Matrix.mulVec, dotProduct]

private theorem modParallelepiped_add_mem {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ intLattice B) :
    modParallelepiped B (x + y) = modParallelepiped B x := by
  obtain ⟨m, rfl⟩ := (mem_intLattice_iff B y).1 hy
  have hinv : (matR B)⁻¹ *ᵥ WithLp.ofLp (x + toVecℤ (B *ᵥ m)) =
      (matR B)⁻¹ *ᵥ WithLp.ofLp x + fun k => (m k : ℝ) := by
    change (matR B)⁻¹ *ᵥ (WithLp.ofLp x + WithLp.ofLp (toVecℤ (B *ᵥ m))) = _
    rw [Matrix.mulVec_add, ofLp_toVecℤ_mulVec, Matrix.mulVec_mulVec, matR_inv_mul hB,
      Matrix.one_mulVec]
  unfold modParallelepiped
  dsimp only
  rw [hinv]
  congr 2; funext k
  simp [Int.floor_add_intCast]

/-- Reducing modulo the fundamental parallelepiped `P(B)` is idempotent for `B.det ≠ 0`. -/
theorem modParallelepiped_idemp {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    modParallelepiped B (modParallelepiped B x) = modParallelepiped B x := by
  have h := inv_mulVec_modParallelepiped hB x
  unfold modParallelepiped
  dsimp only
  change WithLp.toLp 2 (matR B *ᵥ fun k =>
    ((matR B)⁻¹ *ᵥ WithLp.ofLp (modParallelepiped B x)) k -
      (Int.floor (((matR B)⁻¹ *ᵥ WithLp.ofLp (modParallelepiped B x)) k) : ℝ)) = _
  rw [h]
  congr 2; funext k
  change Int.fract _ - (Int.floor (Int.fract _) : ℝ) = _
  rw [Int.floor_fract, Int.cast_zero, sub_zero, Int.fract]

private theorem modParallelepiped_eq_iff_sub_mem {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : B.det ≠ 0) (x y : EuclideanSpace ℝ (Fin n)) :
    modParallelepiped B x = modParallelepiped B y ↔ x - y ∈ intLattice B := by
  refine ⟨fun h => ?_, fun h => by rw [show x = y + (x - y) by abel,
    modParallelepiped_add_mem hB h]⟩
  rw [show x - y = (x - modParallelepiped B x) - (y - modParallelepiped B y) by rw [h]; abel]
  exact Submodule.sub_mem _ (sub_modParallelepiped_mem hB x) (sub_modParallelepiped_mem hB y)

/-- Reducing modulo `P(B)` preserves membership in any superlattice `L ≥ intLattice B`. -/
theorem modParallelepiped_mem_of_le {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    {L : Submodule ℤ (EuclideanSpace ℝ (Fin n))} (hBL : intLattice B ≤ L)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ L) : modParallelepiped B x ∈ L := by
  rw [show modParallelepiped B x = x - (x - modParallelepiped B x) by abel]
  exact Submodule.sub_mem _ hx (hBL (sub_modParallelepiped_mem hB x))

/-- Coordinatewise bound `|(modParallelepiped B x) i| ≤ ∑ j, |B i j|` on `P(B)`. -/
theorem modParallelepiped_abs_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |(modParallelepiped B x) i| ≤ ∑ j : Fin n, |(B i j : ℝ)| := by
  unfold modParallelepiped
  dsimp only [WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (sub_lt_iff_lt_add'.mpr (Int.lt_floor_add_one _)).le

/-- Canonical finite set of representatives `G_q ∩ P(B)`. -/
@[expose] def GridRep {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) : Type :=
  { u : Fin n → ℤ //
      (∀ i, |u i| ≤ (q : ℤ) * ∑ j : Fin n, |B i j|) ∧
      modParallelepiped B (((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ))) =
        ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ)) }

/-- Embed a `GridRep B q` element into `EuclideanSpace ℝ (Fin n)`. -/
@[expose] noncomputable def GridRep.toVec {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {q : ℕ}
    (c : GridRep B q) : EuclideanSpace ℝ (Fin n) :=
  ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (c.1 i : ℝ))

private theorem GridRep.modParallelepiped_toVec {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {q : ℕ}
    (c : GridRep B q) : modParallelepiped B c.toVec = c.toVec := c.2.2

private theorem GridRep.mem_gridLattice {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {q : ℕ}
    (c : GridRep B q) : c.toVec ∈ gridLattice n q :=
  (mem_gridLattice_iff _).2 ⟨c.1, rfl⟩

private theorem GridRep.ext_toVec {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {q : ℕ} (hq : 0 < q)
    {c₁ c₂ : GridRep B q} (h : c₁.toVec = c₂.toVec) : c₁ = c₂ :=
  Subtype.ext (gridVec_injective hq h)

/-- `GridRep B q` is always nonempty (`0` is a representative). -/
instance {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) : Nonempty (GridRep B q) := by
  have hz : (((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 fun i : Fin n => (((0 : Fin n → ℤ) i : ℤ) : ℝ)) =
      0 := by ext i; simp
  exact ⟨⟨0, fun i => by
    simpa only [Pi.zero_apply, abs_zero] using
      mul_nonneg (Nat.cast_nonneg q) (Finset.sum_nonneg fun _ _ => abs_nonneg _),
    by rw [hz, modParallelepiped_zero]⟩⟩

/-- `GridRep B q` is finite (explicit coordinate box). -/
noncomputable instance {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) :
    Fintype (GridRep B q) := by
  let M : Fin n → ℤ := fun i => (q : ℤ) * ∑ j : Fin n, |B i j|
  have : Finite (GridRep B q) := Finite.of_injective
    (fun c : GridRep B q => (fun i => ⟨c.1 i, Finset.mem_Icc.mpr (abs_le.mp (c.2.1 i))⟩ :
      ∀ i : Fin n, { x : ℤ // x ∈ Finset.Icc (-M i) (M i) }))
    fun _ _ h => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
  exact Fintype.ofFinite (GridRep B q)

/-- Construct the `GridRep B q` element representing `modParallelepiped B x` for `x ∈ G_q`. -/
private noncomputable def mkGridRep {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ gridLattice n q) :
    GridRep B q := by
  have hw := modParallelepiped_mem_of_le hB (intLattice_le_gridLattice hq B) hx
  let u := Classical.choose ((mem_gridLattice_iff _).1 hw)
  have hu : modParallelepiped B x = ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 fun i => (u i : ℝ) :=
    Classical.choose_spec ((mem_gridLattice_iff _).1 hw)
  refine ⟨u, fun i => ?_, by rw [← hu, modParallelepiped_idemp hB]⟩
  have h1 := modParallelepiped_abs_le B x i
  rw [hu, PiLp.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hq)), inv_mul_le_iff₀ (Nat.cast_pos.mpr hq)] at h1
  exact_mod_cast (by simpa [Int.cast_abs, Int.cast_sum] using h1 :
    (|u i| : ℝ) ≤ ((q : ℤ) * ∑ j : Fin n, |B i j| : ℤ))

private theorem mkGridRep_toVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ gridLattice n q) :
    (mkGridRep B hB q hq x hx).toVec = modParallelepiped B x :=
  (Classical.choose_spec ((mem_gridLattice_iff _).1
    (modParallelepiped_mem_of_le hB (intLattice_le_gridLattice hq B) hx))).symm

/-- Scale an integer matrix by a natural number `q`. -/
private def scaleMat {n : ℕ} (q : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  (q : ℤ) • B

private theorem mem_range_scaleMat_iff {n q : ℕ} (hq : 0 < q) (B : Matrix (Fin n) (Fin n) ℤ)
    (u : Fin n → ℤ) :
    u ∈ LinearMap.range (scaleMat q B).mulVecLin ↔ gridVec q u ∈ intLattice B := by
  rw [mem_intLattice_iff]
  have hmul (k : Fin n → ℤ) : (scaleMat q B).mulVecLin k = fun i => (q : ℤ) * (B *ᵥ k) i := by
    change ((q : ℤ) • B) *ᵥ k = _; rw [Matrix.smul_mulVec]; rfl
  refine ⟨fun ⟨k, hk⟩ => ⟨k, by rw [← hk, hmul, gridVec_mul_nat hq]⟩,
    fun ⟨k, hk⟩ => ⟨k, gridVec_injective hq ?_⟩⟩
  rw [hmul, gridVec_mul_nat hq]; exact hk.symm

/-- `GridRep B q` is in bijection with `(Fin n → ℤ) ⧸ range ((scaleMat q B).mulVecLin)`. -/
private noncomputable def gridRepEquivQuot {n q : ℕ} (hq : 0 < q)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    GridRep B q ≃ ((Fin n → ℤ) ⧸ LinearMap.range (scaleMat q B).mulVecLin) :=
  Equiv.ofBijective (fun c : GridRep B q => Submodule.Quotient.mk c.1)
    ⟨fun c₁ c₂ h => by
      rw [Submodule.Quotient.eq, mem_range_scaleMat_iff hq B] at h
      have hsub : c₁.toVec - c₂.toVec ∈ intLattice B := by
        convert h using 1; ext i; simp [GridRep.toVec, sub_eq_add_neg, mul_add]
      exact GridRep.ext_toVec hq <| by
        rw [← c₁.modParallelepiped_toVec, ← c₂.modParallelepiped_toVec]
        exact (modParallelepiped_eq_iff_sub_mem hB _ _).2 hsub,
    fun z => Quotient.inductionOn' z fun u => by
      let c := mkGridRep B hB q hq (gridVec q u) ((mem_gridLattice_iff _).2 ⟨u, rfl⟩)
      refine ⟨c, ?_⟩
      change Submodule.Quotient.mk c.1 = Submodule.Quotient.mk u
      rw [Submodule.Quotient.eq, mem_range_scaleMat_iff hq B]
      have hc : gridVec q (c.1 - u) = c.toVec - gridVec q u := by
        ext i; simp [GridRep.toVec, sub_eq_add_neg, mul_add]
      rw [hc, ← modParallelepiped_eq_iff_sub_mem hB, c.modParallelepiped_toVec, mkGridRep_toVec]⟩

private theorem mulVec_int_injective {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} (hM : M.det ≠ 0) :
    Function.Injective M.mulVec := by
  intro x y h
  have hdet : M.det • (x - y) = 0 := by
    rw [← Matrix.one_mulVec (x - y), ← Matrix.smul_mulVec, ← Matrix.adjugate_mul,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, h, sub_self, Matrix.mulVec_zero]
  exact sub_eq_zero.mp (funext fun i => (mul_eq_zero.mp (congrFun hdet i)).resolve_left hM)

private theorem card_quot_range_mulVecLin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.det ≠ 0) :
    Nat.card ((Fin n → ℤ) ⧸ LinearMap.range M.mulVecLin) = M.det.natAbs := by
  let bN := (Pi.basisFun ℤ (Fin n)).map (LinearEquiv.ofInjective M.mulVecLin
    (mulVec_int_injective hM))
  rw [← Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin n)) _ bN,
    Pi.basisFun_det_apply]
  congr 1
  rw [show Matrix.of (Subtype.val ∘ bN) = Mᵀ by
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply, Matrix.transpose_apply, bN, Basis.map_apply,
      Pi.basisFun_apply]
    change (M *ᵥ Pi.single i 1) j = M j i
    simp [Matrix.mulVec_single], Matrix.det_transpose]

/-- Exact cardinality `Fintype.card (GridRep B q) = q^n * |det B|`. -/
theorem card_gridRep {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    {q : ℕ} (hq : 0 < q) :
    Fintype.card (GridRep B q) = q ^ n * B.det.natAbs := by
  have hMdet : (scaleMat q B).det = (q : ℤ) ^ n * B.det := by
    rw [scaleMat, Matrix.det_smul, Fintype.card_fin]
  have hMne : (scaleMat q B).det ≠ 0 := by
    rw [hMdet]; exact mul_ne_zero (pow_ne_zero n (Int.natCast_ne_zero.mpr hq.ne')) hB
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (gridRepEquivQuot hq B hB),
    card_quot_range_mulVecLin _ hMne, hMdet, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]

/-! ### Part 2: Discrete-Grid Sampling Lemma (Finite MR07 Lemma 5.7, p. 20) -/

/-- Map a grid point `r ∈ G_q` to its parallelepiped representative `c = (-r) mod P(B)`
and lattice point `y = r + c ∈ L(B)`. -/
private noncomputable def gridSplit {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (r : gridLattice n q) : GridRep B q × intLattice B :=
  let c := mkGridRep B hB q hq (-r.1) (Submodule.neg_mem _ r.2)
  have hy : r.1 + c.toVec ∈ intLattice B := by
    rw [show r.1 + c.toVec = -(-r.1 - modParallelepiped B (-r.1)) by
      rw [← mkGridRep_toVec B hB q hq (-r.1) (Submodule.neg_mem _ r.2)]; abel]
    exact Submodule.neg_mem _ (sub_modParallelepiped_mem hB (-r.1))
  (c, ⟨r.1 + c.toVec, hy⟩)

private theorem gridSplit_fst_toVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (r : gridLattice n q) :
    (gridSplit B hB q hq r).1.toVec = modParallelepiped B (-r.1) :=
  mkGridRep_toVec B hB q hq (-r.1) (Submodule.neg_mem _ r.2)

private theorem gridSplit_bijective {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) : Function.Bijective (gridSplit B hB q hq) := by
  refine ⟨fun r₁ r₂ h => ?_, fun ⟨c, y⟩ => ?_⟩
  · have h1 : (gridSplit B hB q hq r₁).1 = (gridSplit B hB q hq r₂).1 := congrArg Prod.fst h
    have h2 : r₁.1 + (gridSplit B hB q hq r₁).1.toVec =
        r₂.1 + (gridSplit B hB q hq r₂).1.toVec :=
      congrArg (fun p : GridRep B q × intLattice B => (p.2 : EuclideanSpace ℝ (Fin n))) h
    exact Subtype.ext (add_right_cancel (h1 ▸ h2))
  · let r : gridLattice n q :=
      ⟨(y : EuclideanSpace ℝ (Fin n)) - c.toVec,
        Submodule.sub_mem _ (intLattice_le_gridLattice hq B y.2) c.mem_gridLattice⟩
    have hc : (gridSplit B hB q hq r).1 = c := GridRep.ext_toVec hq <| by
      rw [gridSplit_fst_toVec, show -r.1 = c.toVec + -(y : EuclideanSpace ℝ (Fin n)) by
        simp [r]; abel, modParallelepiped_add_mem hB (Submodule.neg_mem _ y.2),
        c.modParallelepiped_toVec]
    exact ⟨r, Prod.ext hc (Subtype.ext (by
      change r.1 + (gridSplit B hB q hq r).1.toVec = y.1
      rw [hc]; simp [r]))⟩

/-- Ideal discrete-grid sampler `S_q(B, t, s)` (finite MR07 Lemma 5.7, p. 20). -/
noncomputable def idealGridSample {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (s : ℝ) (hs : 0 < s) (t : EuclideanSpace ℝ (Fin n)) :
    PMF (GridRep B q × intLattice B) :=
  (ZLattice.discreteGaussian (gridLattice n q) s hs t).map (gridSplit B hB q hq)

/-- Characterization of `idealGridSample` as pushing the discrete Gaussian on `G_q` through any
splitting map `r ↦ (c, y)` satisfying `c = (-r) mod P(B)` and `y = r + c`. -/
theorem idealGridSample_eq_map {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (s : ℝ) (hs : 0 < s) (t : EuclideanSpace ℝ (Fin n))
    (f : gridLattice n q → GridRep B q × intLattice B)
    (hf_fst : ∀ r, (f r).1.toVec = modParallelepiped B (-r.1))
    (hf_snd : ∀ r, ((f r).2 : EuclideanSpace ℝ (Fin n)) = r.1 + (f r).1.toVec) :
    idealGridSample B hB q hq s hs t =
      (ZLattice.discreteGaussian (gridLattice n q) s hs t).map f := by
  unfold idealGridSample
  congr 1; funext r
  have h1 := GridRep.ext_toVec hq ((gridSplit_fst_toVec B hB q hq r).trans (hf_fst r).symm)
  exact Prod.ext h1 (Subtype.ext (by
    change r.1 + (gridSplit B hB q hq r).1.toVec = _; rw [hf_snd, h1]))

private theorem idealGridSample_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (s : ℝ) (hs : 0 < s) (t : EuclideanSpace ℝ (Fin n))
    (c : GridRep B q) (y : intLattice B) :
    idealGridSample B hB q hq s hs t (c, y) =
      ENNReal.ofReal (gaussianWeight s ((y : EuclideanSpace ℝ (Fin n)) - (t + c.toVec)) /
        gaussianMass (gridLattice n q) s t) := by
  have hbij := gridSplit_bijective B hB q hq
  let r : gridLattice n q := ⟨(y : EuclideanSpace ℝ (Fin n)) - c.toVec,
    Submodule.sub_mem _ (intLattice_le_gridLattice hq B y.2) c.mem_gridLattice⟩
  have hr : gridSplit B hB q hq r = (c, y) := by
    obtain ⟨r', hr'⟩ := hbij.2 (c, y)
    have h2 : r'.1 + (gridSplit B hB q hq r').1.toVec = y.1 :=
      congrArg (fun p : GridRep B q × intLattice B => (p.2 : EuclideanSpace ℝ (Fin n))) hr'
    rw [congrArg Prod.fst hr'] at h2
    exact (Subtype.ext (eq_sub_of_add_eq h2) : r' = r) ▸ hr'
  rw [idealGridSample, PMF.map_apply, tsum_eq_single r fun r' hne => by
    have hneq : (c, y) ≠ gridSplit B hB q hq r' := fun h => hne (hbij.1 (h.symm.trans hr.symm))
    simp [hneq]]
  simp only [hr, ↓reduceIte]
  rw [ZLattice.discreteGaussian_apply,
    show (r : EuclideanSpace ℝ (Fin n)) - t = (y : EuclideanSpace ℝ (Fin n)) - (t + c.toVec) by
      simp [r]; abel, ← ENNReal.ofReal_div_of_pos (gaussianMass_pos _ s hs t)]

/-- Marginal of `idealGridSample` on `GridRep B q` has exact mass proportional to
`gaussianMass (intLattice B) s (t + c.toVec)`. -/
private theorem idealGridSample_fst_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (s : ℝ) (hs : 0 < s) (t : EuclideanSpace ℝ (Fin n)) (c : GridRep B q) :
    ((idealGridSample B hB q hq s hs t).map Prod.fst c).toReal =
      gaussianMass (intLattice B) s (t + c.toVec) / gaussianMass (gridLattice n q) s t := by
  classical
  have hZpos : 0 < gaussianMass (gridLattice n q) s t := gaussianMass_pos _ s hs t
  have hmap : (idealGridSample B hB q hq s hs t).map Prod.fst c =
      ∑' y : intLattice B, idealGridSample B hB q hq s hs t (c, y) := by
    rw [PMF.map_apply, ← (Equiv.sigmaEquivProd _ _).tsum_eq, tsum_sigma',
      tsum_eq_single c (fun c' hc' => by simp [Ne.symm hc'])]
    simp
  rw [hmap]
  simp_rw [idealGridSample_apply]
  have hnn : ∀ y : intLattice B, 0 ≤ gaussianWeight s ((y : EuclideanSpace ℝ (Fin n)) -
      (t + c.toVec)) / gaussianMass (gridLattice n q) s t := fun _ => by
    exact div_nonneg (gaussianWeight_pos _ _).le hZpos.le
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn
    ((summable_gaussianWeight (intLattice B) s hs (t + c.toVec)).div_const _),
    ENNReal.toReal_ofReal (tsum_nonneg hnn), tsum_div_const]
  rfl

/-- Exact conditional law `y | c ~ D_{L(B), s, t + c}` (MR07 Lemma 5.7, item 2). -/
theorem idealGridSample_eq_bind_discreteGaussian {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (q : ℕ) (hq : 0 < q) (s : ℝ) (hs : 0 < s)
    (t : EuclideanSpace ℝ (Fin n)) :
    idealGridSample B hB q hq s hs t =
      ((idealGridSample B hB q hq s hs t).map Prod.fst).bind fun c =>
        (ZLattice.discreteGaussian (intLattice B) s hs (t + c.toVec)).map fun y => (c, y) := by
  ext ⟨c, y⟩
  rw [PMF.bind_apply, tsum_eq_single c (fun c' hc' => by simp [PMF.map_apply, Ne.symm hc'])]
  have hmap : ((ZLattice.discreteGaussian (intLattice B) s hs (t + c.toVec)).map
      fun y => (c, y)) (c, y) = ZLattice.discreteGaussian (intLattice B) s hs (t + c.toVec) y := by
    rw [PMF.map_apply, tsum_eq_single y (fun y' hy' => by simp [Ne.symm hy'])]; simp
  rw [hmap, ← ENNReal.ofReal_toReal (PMF.apply_ne_top _ c), idealGridSample_fst_apply,
    idealGridSample_apply, ZLattice.discreteGaussian_apply,
    ← ENNReal.ofReal_div_of_pos (gaussianMass_pos _ s hs _)]
  have hMc := gaussianMass_pos (intLattice B) s hs (t + c.toVec)
  have hMq := gaussianMass_pos (gridLattice n q) s hs t
  rw [← ENNReal.ofReal_mul (div_nonneg hMc.le hMq.le)]
  congr 1; field_simp [hMc.ne', hMq.ne']

/-- Pure real bound underlying `closeTo_uniform_of_mem_Icc`: if `a x ∈ [1 - ε, 1 + ε]` with mean
`A`, then `∑ x with A ≤ a x, (a x - A) ≤ |α| * ε / 2`. -/
private theorem sum_pos_dev_le {α : Type} [Fintype α] [Nonempty α]
    {a : α → ℝ} {ε : ℝ} (hε0 : 0 ≤ ε) (ha : ∀ x, 1 - ε ≤ a x ∧ a x ≤ 1 + ε) :
    let A : ℝ := (∑ y : α, a y) / Fintype.card α
    ∑ x ∈ Finset.univ.filter (fun x => A ≤ a x), (a x - A) ≤
      (Fintype.card α : ℝ) * ε / 2 := by
  classical
  intro A
  let N : ℝ := Fintype.card α
  have hNpos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hA_lo : 1 - ε ≤ A := (le_div_iff₀ hNpos).2 <| by
    simpa only [Finset.card_univ, nsmul_eq_mul, mul_comm] using
      Finset.card_nsmul_le_sum Finset.univ a (1 - ε) fun y _ => (ha y).1
  have hA_hi : A ≤ 1 + ε := (div_le_iff₀ hNpos).2 <| by
    simpa only [Finset.card_univ, nsmul_eq_mul, mul_comm] using
      Finset.sum_le_card_nsmul Finset.univ a (1 + ε) fun y _ => (ha y).2
  set sPos := Finset.univ.filter fun x => A ≤ a x
  set sNeg := Finset.univ.filter fun x => ¬ A ≤ a x
  set T : ℝ := ∑ x ∈ sPos, (a x - A)
  have hcard : (sPos.card : ℝ) + (sNeg.card : ℝ) = N := by
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
      (fun x => A ≤ a x)
    dsimp only [N]; exact_mod_cast hc.trans Finset.card_univ
  have hsum_zero : ∑ x : α, (a x - A) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      show N * A = ∑ y : α, a y from mul_div_cancel₀ _ hNpos.ne', sub_self]
  have hT_neg : T = ∑ x ∈ sNeg, (A - a x) := by
    have hs := Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => A ≤ a x) (· |> (a · - A))
    have : ∑ x ∈ sNeg, (A - a x) = -∑ x ∈ sNeg, (a x - A) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
    linarith
  have hT1 : T ≤ (sPos.card : ℝ) * (1 + ε - A) := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul sPos (fun x => a x - A) (1 + ε - A)
      fun x _ => by linarith [(ha x).2]
  have hT2 : T ≤ (sNeg.card : ℝ) * (A - (1 - ε)) := by
    rw [hT_neg]
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul sNeg (fun x => A - a x) (A - (1 - ε))
      fun x _ => by linarith [(ha x).1]
  rcases hε0.eq_or_lt with rfl | hεpos
  · have hA1 : A = 1 := by linarith
    simpa [hA1] using hT1
  · have h1 := mul_le_mul_of_nonneg_right hT1 (by linarith : 0 ≤ A - (1 - ε))
    have h2 := mul_le_mul_of_nonneg_right hT2 (by linarith : 0 ≤ 1 + ε - A)
    have hcomb : 2 * ε * T ≤ N * (ε ^ 2 - (A - 1) ^ 2) := by nlinarith
    nlinarith [mul_nonneg hNpos.le (sq_nonneg (A - 1))]

/-- Elementary finite-distribution uniformity bound: if positive weights `a : α → ℝ` lie in
`[1 - ε, 1 + ε]` (`0 ≤ ε < 1`), then the normalized PMF is within `ε / (2 * (1 - ε))` of uniform
in `CloseTo`. -/
private theorem closeTo_uniform_of_mem_Icc {α : Type} [Fintype α] [Nonempty α]
    (p : PMF α) {a : α → ℝ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (ha : ∀ x, 1 - ε ≤ a x ∧ a x ≤ 1 + ε)
    (hp : ∀ x, (p x).toReal = a x / ∑ y : α, a y) :
    CloseTo p (PMF.uniformOfFintype α) (ENNReal.ofReal (ε / (2 * (1 - ε)))) := by
  classical
  let N : ℝ := Fintype.card α
  set S : ℝ := ∑ y : α, a y
  set A : ℝ := S / N
  have hNpos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hS_lo : (1 - ε) * N ≤ S := by
    simpa only [Finset.card_univ, nsmul_eq_mul, mul_comm] using
      Finset.card_nsmul_le_sum Finset.univ a (1 - ε) fun y _ => (ha y).1
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hS_lo
  rw [closeTo_iff_tsum_tsub_le, tsum_fintype]
  have hterm (x : α) : p x - PMF.uniformOfFintype α x =
      ENNReal.ofReal (if A ≤ a x then (a x - A) / S else 0) := by
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top p x),
      ← ENNReal.ofReal_toReal (PMF.apply_ne_top (PMF.uniformOfFintype α) x),
      ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, hp x, PMF.uniformOfFintype_apply,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    have hdiff : a x / S - N⁻¹ = (a x - A) / S := by
      have hSN : S = N * A := (mul_div_cancel₀ S hNpos.ne').symm
      field_simp [hSpos.ne', hNpos.ne']; linarith
    rw [hdiff]
    split_ifs with h
    · rfl
    · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hSpos.le),
        ENNReal.ofReal_zero]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => by
    split_ifs with h
    · exact div_nonneg (sub_nonneg.2 h) hSpos.le
    · rfl]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_filter, ← Finset.sum_div, div_le_div_iff₀ hSpos (by positivity)]
  have := sum_pos_dev_le hε0 ha
  nlinarith [hS_lo, show 0 ≤ 1 - ε by linarith]

/-- Marginal closeness of `c` to uniform on `GridRep B q` (finite MR07 Lemma 5.7, p. 20). -/
theorem idealGridSample_fst_closeTo_uniform
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) {s ε : ℝ} (hs : 0 < s) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B)) (1 / s) 0 - 1 ≤ ε)
    (t : EuclideanSpace ℝ (Fin n)) :
    CloseTo ((idealGridSample B hB q hq s hs t).map Prod.fst)
      (PMF.uniformOfFintype (GridRep B q)) (ENNReal.ofReal (ε / (2 * (1 - ε)))) := by
  have := isZLattice_intLattice hB
  let M : ℝ := s ^ finrank ℝ (EuclideanSpace ℝ (Fin n)) / covolume (intLattice B)
  have hMpos : 0 < M := div_pos (pow_pos hs _) (covolume_pos (intLattice B) volume)
  let a : GridRep B q → ℝ := fun c => gaussianMass (intLattice B) s (t + c.toVec) / M
  have hsumMass : ∑ c : GridRep B q, gaussianMass (intLattice B) s (t + c.toVec) =
      gaussianMass (gridLattice n q) s t := by
    have h1 := ((idealGridSample B hB q hq s hs t).map Prod.fst).tsum_coe
    rw [tsum_fintype] at h1
    ennreal_to_real at h1
    simp_rw [idealGridSample_fst_apply B hB q hq s hs t] at h1
    rw [← Finset.sum_div] at h1
    exact (div_eq_one_iff_eq (gaussianMass_pos (gridLattice n q) s hs t).ne').1 h1
  refine closeTo_uniform_of_mem_Icc _ hε0 hε1 (a := a) (fun c => ?_) (fun c => ?_)
  · have hmem := gaussianMass_mem_Icc_of_dual_mass_le (intLattice B) s hs ε hdual (t + c.toVec)
    exact ⟨(le_div_iff₀ hMpos).2 (by simpa [M, mul_comm] using hmem.1),
      (div_le_iff₀ hMpos).2 (by simpa [M, mul_comm] using hmem.2)⟩
  · rw [idealGridSample_fst_apply]
    simp only [a, ← Finset.sum_div, hsumMass, div_div_div_cancel_right₀ hMpos.ne']

/-! ### Part 3: Sublattice Quotient & Discrete-Grid Combining Procedure (Finite MR07 Lemma 5.8) -/

/-- For `L(S) ≤ L(B)`, construct the integer transition matrix `U` satisfying `B * U = S`. -/
noncomputable def sublatticeMat {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hSB : intLattice S ≤ intLattice B) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => Classical.choose ((mem_intLattice_iff B (intCol S j)).1
    (hSB (Submodule.subset_span ⟨j, rfl⟩))) i

/-- The integer transition matrix `sublatticeMat B S hSB` satisfies
`B * sublatticeMat B S hSB = S`. -/
theorem mul_sublatticeMat {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hSB : intLattice S ≤ intLattice B) : B * sublatticeMat B S hSB = S := by
  ext i j
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i)
    (Classical.choose_spec ((mem_intLattice_iff B (intCol S j)).1
      (hSB (Submodule.subset_span ⟨j, rfl⟩))))
  exact Int.cast_injective (α := ℝ) <| by
    simpa only [Matrix.mul_apply, sublatticeMat, intCol, Matrix.mulVec, dotProduct,
      Int.cast_sum, Int.cast_mul] using hi.symm

/-- For invertible `B` and `L(S) ≤ L(B)`, `(sublatticeMat B S hSB).det = S.det / B.det`. -/
theorem det_sublatticeMat {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    (hSB : intLattice S ≤ intLattice B) : (sublatticeMat B S hSB).det = S.det / B.det := by
  have hdet : B.det * (sublatticeMat B S hSB).det = S.det := by
    rw [← Matrix.det_mul, mul_sublatticeMat]
  rw [← hdet, Int.mul_ediv_cancel_left _ hB]

/-- For invertible `S` and `L(S) ≤ L(B)`, `sublatticeMat B S hSB` has nonzero determinant. -/
theorem det_sublatticeMat_ne_zero {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    (sublatticeMat B S hSB).det ≠ 0 := fun h0 =>
  hS (by rw [← mul_sublatticeMat B S hSB, Matrix.det_mul, h0, mul_zero])

/-- Canonical finite set of quotient representatives `L(B) ∩ P(S)` (cardinality `|det(B⁻¹ S)|`). -/
@[expose] def SublatticeQuot {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) : Type :=
  { v : Fin n → ℤ //
      (∀ i, |v i| ≤ ∑ j : Fin n, |S i j|) ∧
      WithLp.toLp 2 (fun i => (v i : ℝ)) ∈ intLattice B ∧
      modParallelepiped S (WithLp.toLp 2 (fun i => (v i : ℝ))) =
        WithLp.toLp 2 (fun i => (v i : ℝ)) }

/-- Embed a `SublatticeQuot B S` representative into `EuclideanSpace ℝ (Fin n)`. -/
@[expose] noncomputable def SublatticeQuot.toVec {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (v : SublatticeQuot B S) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (v.1 i : ℝ))

private theorem SublatticeQuot.mem_intLattice {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (v : SublatticeQuot B S) : v.toVec ∈ intLattice B := v.2.2.1

private theorem SublatticeQuot.modParallelepiped_toVec {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (v : SublatticeQuot B S) : modParallelepiped S v.toVec = v.toVec := v.2.2.2

private theorem SublatticeQuot.ext_toVec {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    {v₁ v₂ : SublatticeQuot B S} (h : v₁.toVec = v₂.toVec) : v₁ = v₂ :=
  Subtype.ext (toVecℤ_injective h)

/-- The zero representative `0 ∈ L(B) ∩ P(S)`. -/
def SublatticeQuot.zero {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) : SublatticeQuot B S :=
  ⟨0,
   fun _ => by
     simpa only [Pi.zero_apply, abs_zero] using Finset.sum_nonneg fun _ _ => abs_nonneg _,
   by
     have hz : WithLp.toLp 2 (fun i : Fin n => (((0 : Fin n → ℤ) i : ℤ) : ℝ)) = 0 := by
       ext i; simp
     rw [hz]; exact (intLattice B).zero_mem,
   by
     have hz : WithLp.toLp 2 (fun i : Fin n => (((0 : Fin n → ℤ) i : ℤ) : ℝ)) = 0 := by
       ext i; simp
     rw [hz, modParallelepiped_zero]⟩

/-- The coordinate vector of `SublatticeQuot.zero B S` is `0`. -/
@[simp] theorem SublatticeQuot.zero_val {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) :
    (SublatticeQuot.zero B S).1 = 0 := by
  rfl

/-- `SublatticeQuot B S` is always nonempty (`0` is a representative). -/
instance {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) : Nonempty (SublatticeQuot B S) :=
  ⟨SublatticeQuot.zero B S⟩

/-- `SublatticeQuot B S` is finite via the explicit coordinate box `[-∑_j |S i j|, ∑_j |S i j|]`. -/
noncomputable instance {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) :
    Fintype (SublatticeQuot B S) := by
  let M : Fin n → ℤ := fun i => ∑ j : Fin n, |S i j|
  have : Finite (SublatticeQuot B S) := Finite.of_injective
    (fun v : SublatticeQuot B S => (fun i => ⟨v.1 i, Finset.mem_Icc.mpr (abs_le.mp (v.2.1 i))⟩ :
      ∀ i : Fin n, { x : ℤ // x ∈ Finset.Icc (-M i) (M i) }))
    fun _ _ h => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
  exact Fintype.ofFinite (SublatticeQuot B S)

instance {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) : DecidableEq (SublatticeQuot B S) :=
  inferInstanceAs (DecidableEq (Subtype _))

/-- Construct a `SublatticeQuot B S` representative from an integer coordinate vector `k`
for `B`. -/
private noncomputable def mkSublatticeQuot {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) (k : Fin n → ℤ) :
    SublatticeQuot B S := by
  have hw : modParallelepiped S (toVecℤ (B *ᵥ k)) ∈ intLattice B :=
    modParallelepiped_mem_of_le hS hSB ((mem_intLattice_iff B _).2 ⟨k, rfl⟩)
  let m := Classical.choose ((mem_intLattice_iff B _).1 hw)
  have hm : modParallelepiped S (toVecℤ (B *ᵥ k)) =
      WithLp.toLp 2 (fun i => ((B *ᵥ m) i : ℝ)) :=
    Classical.choose_spec ((mem_intLattice_iff B _).1 hw)
  refine ⟨B *ᵥ m, fun i => ?_, by rw [← hm]; exact hw,
    by rw [← hm]; exact modParallelepiped_idemp hS _⟩
  have h1 := modParallelepiped_abs_le S (toVecℤ (B *ᵥ k)) i
  rw [hm] at h1
  exact_mod_cast (by simpa [Int.cast_abs, Int.cast_sum] using h1 :
    (|(B *ᵥ m) i| : ℝ) ≤ (∑ j : Fin n, |S i j| : ℤ))

private theorem mkSublatticeQuot_toVec {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) (k : Fin n → ℤ) :
    (mkSublatticeQuot B S hS hSB k).toVec = modParallelepiped S (toVecℤ (B *ᵥ k)) :=
  (Classical.choose_spec ((mem_intLattice_iff B _).1
    (modParallelepiped_mem_of_le hS hSB ((mem_intLattice_iff B _).2 ⟨k, rfl⟩)))).symm

private noncomputable def sublatticeQuotCoord {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (v : SublatticeQuot B S) : Fin n → ℤ :=
  Classical.choose ((mem_intLattice_iff B v.toVec).1 v.mem_intLattice)

private theorem sublatticeQuotCoord_spec {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (v : SublatticeQuot B S) : v.toVec = toVecℤ (B *ᵥ sublatticeQuotCoord v) :=
  Classical.choose_spec ((mem_intLattice_iff B v.toVec).1 v.mem_intLattice)

private theorem sublatticeQuotCoord_mk {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) (k : Fin n → ℤ) :
    Submodule.Quotient.mk (p := LinearMap.range (sublatticeMat B S hSB).mulVecLin)
      (sublatticeQuotCoord (mkSublatticeQuot B S hS hSB k)) = Submodule.Quotient.mk k := by
  set v := mkSublatticeQuot B S hS hSB k
  have hdiff : toVecℤ (B *ᵥ k) - v.toVec ∈ intLattice S := by
    rw [mkSublatticeQuot_toVec]; exact sub_modParallelepiped_mem hS _
  obtain ⟨m, hm⟩ := (mem_intLattice_iff S _).1 hdiff
  rw [Submodule.Quotient.eq]
  refine ⟨-m, (mulVec_int_injective hB ?_).symm⟩
  change B *ᵥ (sublatticeQuotCoord v - k) = B *ᵥ (sublatticeMat B S hSB *ᵥ (-m))
  rw [Matrix.mulVec_mulVec, mul_sublatticeMat, Matrix.mulVec_neg, Matrix.mulVec_sub]
  have hvi : toVecℤ (B *ᵥ k - B *ᵥ sublatticeQuotCoord v) = toVecℤ (S *ᵥ m) := by
    convert hm using 1; ext i; simp [sublatticeQuotCoord_spec v]
  have hz := toVecℤ_injective hvi
  funext i; have := congrFun hz i; simp only [Pi.sub_apply, Pi.neg_apply] at this ⊢; omega

private noncomputable def sublatticeQuotEquivQuot {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    SublatticeQuot B S ≃ (Fin n → ℤ) ⧸ LinearMap.range (sublatticeMat B S hSB).mulVecLin :=
  Equiv.ofBijective
    (fun v : SublatticeQuot B S => Submodule.Quotient.mk (sublatticeQuotCoord v))
    ⟨fun v₁ v₂ h => by
      rw [Submodule.Quotient.eq] at h
      obtain ⟨m, hm⟩ := h
      have hsub : v₁.toVec - v₂.toVec ∈ intLattice S := (mem_intLattice_iff S _).2 ⟨m, by
        have hBU : B *ᵥ (sublatticeQuotCoord v₁ - sublatticeQuotCoord v₂) = S *ᵥ m := by
          rw [show sublatticeQuotCoord v₁ - sublatticeQuotCoord v₂ =
            sublatticeMat B S hSB *ᵥ m from hm.symm, Matrix.mulVec_mulVec, mul_sublatticeMat]
        ext i
        have hi := congrFun hBU i
        simp only [Matrix.mulVec_sub, Pi.sub_apply] at hi
        rw [PiLp.sub_apply, sublatticeQuotCoord_spec v₁, sublatticeQuotCoord_spec v₂]
        change ((B *ᵥ sublatticeQuotCoord v₁) i : ℝ) - ((B *ᵥ sublatticeQuotCoord v₂) i : ℝ) =
          ((S *ᵥ m) i : ℝ)
        exact_mod_cast hi⟩
      exact SublatticeQuot.ext_toVec <| by
        rw [← v₁.modParallelepiped_toVec, ← v₂.modParallelepiped_toVec]
        exact (modParallelepiped_eq_iff_sub_mem hS _ _).2 hsub,
    fun qx => Quotient.inductionOn' qx fun k =>
      ⟨mkSublatticeQuot B S hS hSB k, sublatticeQuotCoord_mk B S hB hS hSB k⟩⟩

/-- Exact cardinality `Fintype.card (SublatticeQuot B S) = |det(B⁻¹ S)|`. -/
theorem card_sublatticeQuot {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    Fintype.card (SublatticeQuot B S) = (S.det / B.det).natAbs := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (sublatticeQuotEquivQuot B S hB hS hSB),
    card_quot_range_mulVecLin _ (det_sublatticeMat_ne_zero hS hSB), det_sublatticeMat hB hSB]

/-- HNF-free quotient surjection `(ZMod D)^n → SublatticeQuot B S` with `D = |det(B⁻¹ S)|`. -/
noncomputable def quotientHom {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (x : Fin n → ZMod (S.det / B.det).natAbs) : SublatticeQuot B S :=
  mkSublatticeQuot B S hS hSB (fun j => ((x j).val : ℤ))

/-- Explicit parallelepiped characterization of `quotientHom`. -/
theorem quotientHom_toVec {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (x : Fin n → ZMod (S.det / B.det).natAbs) :
    (quotientHom B S hS hSB x).toVec =
      modParallelepiped S (WithLp.toLp 2 (fun i => ((B *ᵥ fun j => ((x j).val : ℤ)) i : ℝ))) :=
  mkSublatticeQuot_toVec B S hS hSB _

/-- Any integer vector congruent to `0` modulo `|det U|` lies in `range U.mulVecLin` (via Cramer's
rule `U * adjugate U = det U • 1`). -/
private theorem sub_mem_range_of_zmod_eq {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    {u v : Fin n → ℤ} (h : ∀ j : Fin n, (u j : ZMod U.det.natAbs) = (v j : ZMod U.det.natAbs)) :
    u - v ∈ LinearMap.range U.mulVecLin := by
  let w : Fin n → ℤ := fun j => (u j - v j) / (U.det.natAbs : ℤ)
  have heq : u - v = (U.det.natAbs : ℤ) • w := funext fun j =>
    (Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd (u j - v j) _).1
      (by rw [Int.cast_sub, h j, sub_self]))).symm
  rw [heq]
  have hmul (c : ℤ) : U *ᵥ (c • (U.adjugate *ᵥ w)) = (c * U.det) • w := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul]
  rcases abs_choice U.det with hpos | hneg
  · exact ⟨U.adjugate *ᵥ w, by simpa [hpos, Int.natCast_natAbs] using hmul 1⟩
  · exact ⟨-(U.adjugate *ᵥ w), by simpa [hneg, Int.natCast_natAbs] using hmul (-1)⟩

/-- HNF-free exact uniform sampling on `SublatticeQuot B S` via `(ZMod D)^n ↠ SublatticeQuot B S`
with `D = |det(B⁻¹ S)|` (Cramer's rule `Matrix.mul_adjugate`). -/
theorem map_quotientHom_uniform_eq_uniform_sublatticeQuot
    {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (hS : S.det ≠ 0)
    (hSB : intLattice S ≤ intLattice B) :
    letI : NeZero (S.det / B.det).natAbs :=
      ⟨by rw [← card_sublatticeQuot hB hS hSB]; exact Fintype.card_ne_zero⟩
    (PMF.uniformOfFintype (Fin n → ZMod (S.det / B.det).natAbs)).map
        (quotientHom B S hS hSB) =
      PMF.uniformOfFintype (SublatticeQuot B S) := by
  let U := sublatticeMat B S hSB
  let e := sublatticeQuotEquivQuot B S hB hS hSB
  have hD : (S.det / B.det).natAbs = U.det.natAbs :=
    congrArg Int.natAbs (det_sublatticeMat hB hSB).symm
  have : NeZero (S.det / B.det).natAbs :=
    ⟨by rw [← card_sublatticeQuot hB hS hSB]; exact Fintype.card_ne_zero⟩
  have hsub (u v : Fin n → ℤ)
      (h : ∀ j, (u j : ZMod (S.det / B.det).natAbs) = (v j : ZMod (S.det / B.det).natAbs)) :
      u - v ∈ LinearMap.range U.mulVecLin :=
    sub_mem_range_of_zmod_eq U fun j => hD ▸ h j
  have : Fintype ((Fin n → ℤ) ⧸ LinearMap.range U.mulVecLin) := Fintype.ofEquiv _ e
  let φ : (Fin n → ZMod (S.det / B.det).natAbs) →+
      ((Fin n → ℤ) ⧸ LinearMap.range U.mulVecLin) :=
    { toFun := fun x => Submodule.Quotient.mk fun j => ((x j).val : ℤ)
      map_zero' := by
        change Submodule.Quotient.mk (fun _ : Fin n => (((0 : ZMod _).val : ℤ))) = 0
        simp only [ZMod.val_zero, Nat.cast_zero]; exact Submodule.Quotient.mk_zero _
      map_add' := fun x y => by
        rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
        exact hsub _ _ fun j => by push_cast; simp }
  have hsurj : Function.Surjective φ := fun qk => Quotient.inductionOn' qk fun k =>
    ⟨fun j => (k j : ZMod _), by
      change Submodule.Quotient.mk (fun j => (((k j : ZMod _).val : ℤ))) = Submodule.Quotient.mk k
      rw [Submodule.Quotient.eq]; exact hsub _ _ fun j => by push_cast; simp⟩
  have hcomp : quotientHom B S hS hSB = e.symm ∘ φ := funext fun x =>
    e.injective <| by
      rw [Function.comp_apply, Equiv.apply_symm_apply]
      exact sublatticeQuotCoord_mk B S hB hS hSB fun j => ((x j).val : ℤ)
  rw [hcomp, ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_addHom φ hsurj,
    Cslib.Probability.PMF.uniformOfFintype_map_equiv e.symm]

/-- Discretized parallelepiped coordinate `a(w) = ⌊q · S⁻¹ w⌋ mod q` for `w ∈ GridRep S q`. -/
private noncomputable def gridRepToZMod {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (q : ℕ)
    (w : GridRep S q) : Fin n → ZMod q :=
  fun k => (Int.floor ((q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k) : ZMod q)

private theorem gridRepToZMod_val {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ} (hS : S.det ≠ 0)
    {q : ℕ} (hq : 0 < q) (w : GridRep S q) (k : Fin n) :
    ((gridRepToZMod S q w k).val : ℤ) =
      Int.floor ((q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k) := by
  have hξ : ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k =
      Int.fract (((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k) := by
    conv_lhs => rw [← w.modParallelepiped_toVec]
    exact congrFun (inv_mulVec_modParallelepiped hS w.toVec) k
  set m : ℤ := Int.floor ((q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k)
  have hm0 : 0 ≤ m := Int.floor_nonneg.mpr (by rw [hξ]; positivity)
  have hm1 : m < (q : ℤ) := Int.floor_lt.2 <| by
    rw [hξ]; simpa using mul_lt_mul_of_pos_left
      (Int.fract_lt_one (((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k)) (Nat.cast_pos.mpr hq)
  change ((m : ZMod q).val : ℤ) = m
  have hlt : m.toNat < q := by omega
  rw [show (m : ZMod q) = ((m.toNat : ℕ) : ZMod q) by rw [← Int.cast_natCast,
    Int.toNat_of_nonneg hm0], ZMod.val_natCast_of_lt hlt, Int.toNat_of_nonneg hm0]

/-- Single-column combining map `(v, c) ↦ (w, a)` where `w = (v + c) mod P(S)` and
`a = ⌊q S⁻¹ w⌋ mod q` (MR07 Lemma 5.8, p. 21). -/
noncomputable def combineColumn {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) (q : ℕ)
    (v : SublatticeQuot B S) (c : GridRep B q) : GridRep S q × (Fin n → ZMod q) :=
  if h : S.det ≠ 0 ∧ 0 < q then
    let w := mkGridRep S h.1 q h.2 (v.toVec + c.toVec)
      (Submodule.add_mem _ (intLattice_le_gridLattice h.2 B v.mem_intLattice) c.mem_gridLattice)
    (w, gridRepToZMod S q w)
  else
    (Classical.arbitrary (GridRep S q), 0)

/-- The first component of `combineColumn B S q v c` represents `(v + c) mod P(S)`. -/
theorem combineColumn_fst_toVec {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (hS : S.det ≠ 0) {q : ℕ} (hq : 0 < q) (v : SublatticeQuot B S) (c : GridRep B q) :
    (combineColumn B S q v c).1.toVec = modParallelepiped S (v.toVec + c.toVec) := by
  unfold combineColumn
  split_ifs with h
  · exact mkGridRep_toVec S h.1 q h.2 (v.toVec + c.toVec)
      (Submodule.add_mem _ (intLattice_le_gridLattice h.2 B v.mem_intLattice) c.mem_gridLattice)
  · exact (h ⟨hS, hq⟩).elim

private theorem combineColumn_snd_eq {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (hS : S.det ≠ 0) {q : ℕ} (hq : 0 < q) (v : SublatticeQuot B S) (c : GridRep B q) :
    (combineColumn B S q v c).2 = gridRepToZMod S q (combineColumn B S q v c).1 := by
  unfold combineColumn
  split_ifs with h
  · rfl
  · exact (h ⟨hS, hq⟩).elim

/-- Canonical residue value of the second component of `combineColumn`:
`((combineColumn B S q v c).2 k).val = ⌊q · (S⁻¹ w)_k⌋`, where `w = (combineColumn B S q v c).1`.
-/
theorem combineColumn_snd_val {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (hS : S.det ≠ 0) {q : ℕ} (hq : 0 < q) (v : SublatticeQuot B S) (c : GridRep B q)
    (k : Fin n) :
    (((combineColumn B S q v c).2 k).val : ℤ) =
      Int.floor ((q : ℝ) * (((S.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ
        WithLp.ofLp (combineColumn B S q v c).1.toVec) k)) := by
  rw [combineColumn_snd_eq hS hq]; exact gridRepToZMod_val hS hq _ k

/-- Query matrix `A ∈ ZMod q^{n×m}` produced by the combining procedure from `(V, C)`. -/
@[expose] noncomputable def combineMatrix {n m : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) (q : ℕ)
    (V : Fin m → SublatticeQuot B S) (C : Fin m → GridRep B q) :
    Matrix (Fin n) (Fin m) (ZMod q) :=
  fun i j => (combineColumn B S q (V j) (C j)).2 i

/-- Output vector `x = ∑_j z_j (c_j - w_j) + S * ((A_int *ᵥ z) / q)` of the combining procedure.
Using integer Euclidean division `((A_int *ᵥ z) k) / q` ensures `combineOutput ∈ L(B)` holds
unconditionally for every `z : Fin m → ℤ`, and coincides with `S * (A_int *ᵥ z / q)` whenever
`A *ᵥ z ≡ 0 (mod q)`. -/
@[expose] noncomputable def combineOutput {n m : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) (q : ℕ)
    (V : Fin m → SublatticeQuot B S) (C : Fin m → GridRep B q) (z : Fin m → ℤ) :
    EuclideanSpace ℝ (Fin n) :=
  let W := fun j => (combineColumn B S q (V j) (C j)).1
  let A_int : Matrix (Fin n) (Fin m) ℤ :=
    fun i j => (((combineColumn B S q (V j) (C j)).2 i).val : ℤ)
  (∑ j : Fin m, z j • ((C j).toVec - (W j).toVec)) +
    WithLp.toLp 2 (fun i => ((S *ᵥ fun k => ((A_int *ᵥ z) k) / (q : ℤ)) i : ℝ))

/-- Unconditional lattice membership of `combineOutput` for every `z : Fin m → ℤ`. -/
theorem combineOutput_mem_intLattice {n m : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) (q : ℕ) (hq : 0 < q)
    (V : Fin m → SublatticeQuot B S) (C : Fin m → GridRep B q) (z : Fin m → ℤ) :
    combineOutput B S q V C z ∈ intLattice B := by
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (z j) ?_)
    (hSB ((mem_intLattice_iff S _).2 ⟨_, rfl⟩))
  rw [show (C j).toVec - (combineColumn B S q (V j) (C j)).1.toVec =
    ((V j).toVec + (C j).toVec - modParallelepiped S ((V j).toVec + (C j).toVec)) -
      (V j).toVec by rw [combineColumn_fst_toVec hS hq]; abel]
  exact Submodule.sub_mem _ (hSB (sub_modParallelepiped_mem hS _)) (V j).mem_intLattice

private theorem combineColumn_fst_bijective {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (q : ℕ) (hq : 0 < q) :
    Function.Bijective
      (fun p : SublatticeQuot B S × GridRep B q => (combineColumn B S q p.1 p.2).1) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
  · rintro ⟨v₁, c₁⟩ ⟨v₂, c₂⟩ h
    dsimp only at h
    have hSdiff : (v₁.toVec + c₁.toVec) - (v₂.toVec + c₂.toVec) ∈ intLattice S :=
      (modParallelepiped_eq_iff_sub_mem hS _ _).1 <| by
        rw [← combineColumn_fst_toVec hS hq, ← combineColumn_fst_toVec hS hq, h]
    have hc_eq : c₁ = c₂ := GridRep.ext_toVec hq <| by
      rw [← c₁.modParallelepiped_toVec, ← c₂.modParallelepiped_toVec,
        modParallelepiped_eq_iff_sub_mem hB,
        show c₁.toVec - c₂.toVec = ((v₁.toVec + c₁.toVec) - (v₂.toVec + c₂.toVec)) -
          (v₁.toVec - v₂.toVec) by abel]
      exact Submodule.sub_mem _ (hSB hSdiff)
        (Submodule.sub_mem _ v₁.mem_intLattice v₂.mem_intLattice)
    subst hc_eq
    refine Prod.ext (SublatticeQuot.ext_toVec ?_) rfl
    rw [← v₁.modParallelepiped_toVec, ← v₂.modParallelepiped_toVec,
      modParallelepiped_eq_iff_sub_mem hS]
    simpa [add_sub_add_right_eq_sub] using hSdiff
  · have hdvd : B.det ∣ S.det :=
      ⟨(sublatticeMat B S hSB).det, by rw [← Matrix.det_mul, mul_sublatticeMat]⟩
    rw [Fintype.card_prod, card_sublatticeQuot hB hS hSB, card_gridRep hB hq, card_gridRep hS hq,
      mul_left_comm, ← Int.natAbs_mul, Int.ediv_mul_cancel hdvd]

/-- Grid shift vector `(1 / q) * S * b` for `b : Fin n → ZMod q`. -/
private noncomputable def zmodShiftVec {n q : ℕ} (S : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ZMod q) : EuclideanSpace ℝ (Fin n) :=
  gridVec q (S *ᵥ fun k => ((b k).val : ℤ))

private theorem zmodShiftVec_add_neg_mem {n q : ℕ} [NeZero q] (S : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ZMod q) : zmodShiftVec S b + zmodShiftVec S (-b) ∈ intLattice S := by
  have hdvd (k : Fin n) : (q : ℤ) ∣ (((b k).val : ℤ) + (((-b) k).val : ℤ)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 (by push_cast; simp)
  refine (mem_intLattice_iff S _).2
    ⟨fun k => (((b k).val : ℤ) + (((-b) k).val : ℤ)) / (q : ℤ), ?_⟩
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.pos q).ne'
  have hvec : (q : ℤ) • (S *ᵥ fun k => (((b k).val : ℤ) + (((-b) k).val : ℤ)) / (q : ℤ)) =
      S *ᵥ fun k => ((b k).val : ℤ) + (((-b) k).val : ℤ) := by
    rw [← Matrix.mulVec_smul]
    exact congrArg S.mulVec (funext fun k => Int.mul_ediv_cancel' (hdvd k))
  ext i
  have hi := congrArg (Int.cast (R := ℝ)) (congrFun hvec i)
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast] at hi
  simp only [zmodShiftVec, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ← mul_add,
    ← Int.cast_add]
  change (q : ℝ)⁻¹ * (((S *ᵥ _ + S *ᵥ _) i : ℤ) : ℝ) = _
  rw [← Matrix.mulVec_add, show (fun k => ((b k).val : ℤ)) + (fun k => (((-b) k).val : ℤ)) =
    fun k => ((b k).val : ℤ) + (((-b) k).val : ℤ) from rfl, ← hi, inv_mul_cancel_left₀ hq0]

private theorem inv_mulVec_zmodShiftVec {n q : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (hS : S.det ≠ 0)
    (b : Fin n → ZMod q) :
    (matR S)⁻¹ *ᵥ WithLp.ofLp (zmodShiftVec S b) = fun j => ((b j).val : ℝ) / q := by
  have : WithLp.ofLp (zmodShiftVec S b) = matR S *ᵥ fun j => ((b j).val : ℝ) / q := by
    change (q : ℝ)⁻¹ • WithLp.ofLp (toVecℤ (S *ᵥ _)) = _
    rw [ofLp_toVecℤ_mulVec, ← Matrix.mulVec_smul]; congr 1; funext j; simp [div_eq_inv_mul]
  rw [this, Matrix.mulVec_mulVec, matR_inv_mul hS, Matrix.one_mulVec]

private theorem map_gridRepToZMod_uniform {n q : ℕ} [NeZero q] (S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) :
    (PMF.uniformOfFintype (GridRep S q)).map (gridRepToZMod S q) =
      PMF.uniformOfFintype (Fin n → ZMod q) := by
  have hq : 0 < q := NeZero.pos q
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  let shift (b : Fin n → ZMod q) (w : GridRep S q) : GridRep S q :=
    mkGridRep S hS q hq (w.toVec + zmodShiftVec S b)
      (Submodule.add_mem _ w.mem_gridLattice ((mem_gridLattice_iff _).2 ⟨_, rfl⟩))
  have hinv (b : Fin n → ZMod q) (w : GridRep S q) : shift (-b) (shift b w) = w :=
    GridRep.ext_toVec hq <| by
      simp only [shift, mkGridRep_toVec]
      conv_rhs => rw [← w.modParallelepiped_toVec]
      rw [modParallelepiped_eq_iff_sub_mem hS,
        show modParallelepiped S (w.toVec + zmodShiftVec S b) + zmodShiftVec S (-b) - w.toVec =
          (zmodShiftVec S b + zmodShiftVec S (-b)) -
            (w.toVec + zmodShiftVec S b - modParallelepiped S (w.toVec + zmodShiftVec S b)) by
          abel]
      exact Submodule.sub_mem _ (zmodShiftVec_add_neg_mem S b) (sub_modParallelepiped_mem hS _)
  have hmap (b : Fin n → ZMod q) (w : GridRep S q) :
      gridRepToZMod S q (shift b w) = gridRepToZMod S q w + b := funext fun k => by
    have hto : (matR S)⁻¹ *ᵥ WithLp.ofLp (shift b w).toVec =
        fun j => Int.fract (((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) j + ((b j).val : ℝ) / q) := by
      rw [show (shift b w).toVec = modParallelepiped S (w.toVec + zmodShiftVec S b) from
        mkGridRep_toVec S hS q hq _ _, inv_mulVec_modParallelepiped hS]
      funext j
      change Int.fract (((matR S)⁻¹ *ᵥ (WithLp.ofLp w.toVec + WithLp.ofLp (zmodShiftVec S b))) j)
        = _
      rw [Matrix.mulVec_add, inv_mulVec_zmodShiftVec S hS b]; rfl
    simp only [gridRepToZMod, Pi.add_apply, hto, Int.fract]
    set ξ := ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k
    set m := Int.floor (ξ + ((b k).val : ℝ) / q)
    rw [show (q : ℝ) * (ξ + ((b k).val : ℝ) / q - (m : ℝ)) =
      (q : ℝ) * ξ + ((b k).val : ℤ) - ((q : ℤ) * m : ℤ) by push_cast; field_simp [hq0],
      Int.floor_sub_intCast, Int.floor_add_intCast]
    push_cast; simp
  exact Cslib.Probability.PMF.uniformOfFintype_map_of_shift fun c =>
    ⟨⟨shift c, shift (-c), hinv c, fun w => by simpa [neg_neg] using hinv (-c) w⟩, hmap c⟩

/-- Exact uniformity of the combining query matrix `A ∈ ZMod q^{n×m}` when `C` and `V` are
uniformly random (MR07 Lemma 5.8, item 1, pp. 20–21). -/
theorem idealCombine_matrix_eq_uniform
    {n m q : ℕ} [NeZero q] (B S : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    (PMF.uniformOfFintype (Fin m → GridRep B q)).bind
      (fun C => (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).map
        (fun V => combineMatrix B S q V C)) =
      PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q)) := by
  have hq : 0 < q := NeZero.pos q
  have hcol : (PMF.uniformOfFintype (SublatticeQuot B S × GridRep B q)).map
      (fun p => (combineColumn B S q p.1 p.2).2) = PMF.uniformOfFintype (Fin n → ZMod q) := by
    let e := Equiv.ofBijective _ (combineColumn_fst_bijective B S hB hS hSB q hq)
    rw [show (fun p : SublatticeQuot B S × GridRep B q => (combineColumn B S q p.1 p.2).2) =
      gridRepToZMod S q ∘ e from funext fun p => combineColumn_snd_eq hS hq p.1 p.2,
      ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_equiv e,
      map_gridRepToZMod_uniform S hS]
  let eVC : (Fin m → GridRep B q) × (Fin m → SublatticeQuot B S) ≃
      (Fin m → SublatticeQuot B S × GridRep B q) :=
    ⟨fun p j => (p.2 j, p.1 j), fun f => (fun j => (f j).2, fun j => (f j).1),
      fun ⟨_, _⟩ => rfl, fun _ => rfl⟩
  let eMat : (Fin m → Fin n → ZMod q) ≃ Matrix (Fin n) (Fin m) (ZMod q) :=
    ⟨fun cols i j => cols j i, fun A j i => A i j, fun _ => rfl, fun _ => rfl⟩
  have hlhs : (PMF.uniformOfFintype (Fin m → GridRep B q)).bind
      (fun C => (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).map
        (fun V => combineMatrix B S q V C)) =
      ((PMF.uniformOfFintype (Fin m → SublatticeQuot B S × GridRep B q)).map
        (fun f j => (combineColumn B S q (f j).1 (f j).2).2)).map eMat := by
    rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv eVC, PMF.map_comp, PMF.map_comp,
      ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
    exact congrArg (PMF.bind _) (funext fun _ => by rw [PMF.map_comp]; rfl)
  rw [hlhs, ← Cslib.Probability.PMF.pi_uniformOfFintype,
    ← Cslib.Probability.PMF.pi_map
      (p := fun _ : Fin m => PMF.uniformOfFintype (SublatticeQuot B S × GridRep B q))
      (f := fun _ (p : SublatticeQuot B S × GridRep B q) => (combineColumn B S q p.1 p.2).2)]
  simp_rw [hcol]
  rw [Cslib.Probability.PMF.pi_uniformOfFintype,
    Cslib.Probability.PMF.uniformOfFintype_map_equiv eMat]

/-- Fractional-part expansion of the discretization error `combineOutput - ∑ z_j • c_j` for a
kernel vector `z`. -/
private theorem combineOutput_sub_eq_fract
    {n m q : ℕ} (hq : 0 < q) (B S : Matrix (Fin n) (Fin n) ℤ) (hS : S.det ≠ 0)
    (V : Fin m → SublatticeQuot B S) (C : Fin m → GridRep B q) (z : Fin m → ℤ)
    (hker : InKernelLattice (combineMatrix B S q V C) z) :
    let W := fun j => (combineColumn B S q (V j) (C j)).1
    let u : Fin m → Fin n → ℝ := fun j k =>
      (q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp (W j).toVec) k
    combineOutput B S q V C z - ∑ j : Fin m, z j • (C j).toVec =
      (-((q : ℝ)⁻¹)) • ∑ k : Fin n, (∑ j : Fin m, (z j : ℝ) * Int.fract (u j k)) • intCol S k := by
  intro W u
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have : NeZero q := ⟨hq.ne'⟩
  let A_int : Matrix (Fin n) (Fin m) ℤ :=
    fun i j => (((combineColumn B S q (V j) (C j)).2 i).val : ℤ)
  have hdiv (k : Fin n) : (((A_int *ᵥ z) k / (q : ℤ) : ℤ) : ℝ) =
      (q : ℝ)⁻¹ * ∑ j : Fin m, (z j : ℝ) * (Int.floor (u j k) : ℝ) := by
    have hdvd : (q : ℤ) ∣ (A_int *ᵥ z) k := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 <| by
      simpa [A_int, combineMatrix, Matrix.mulVec, dotProduct, ZMod.natCast_zmod_val] using
        congrFun hker k
    have hA_eq (j : Fin m) : (A_int k j : ℝ) = (Int.floor (u j k) : ℝ) := by
      dsimp only [A_int, u]; rw [combineColumn_snd_eq hS hq]
      exact_mod_cast gridRepToZMod_val hS hq (W j) k
    have hcast : (q : ℝ) * (((A_int *ᵥ z) k / (q : ℤ) : ℤ) : ℝ) = ((A_int *ᵥ z) k : ℝ) := by
      exact_mod_cast Int.mul_ediv_cancel' hdvd
    rw [inv_mul_eq_div, eq_div_iff hq0, mul_comm, hcast]
    simp [Matrix.mulVec, dotProduct, hA_eq, mul_comm]
  have hW_eq (j : Fin m) : (W j).toVec = ∑ k : Fin n, ((q : ℝ)⁻¹ * u j k) • intCol S k := by
    have hinv : WithLp.ofLp (W j).toVec = matR S *ᵥ ((matR S)⁻¹ *ᵥ WithLp.ofLp (W j).toVec) := by
      rw [Matrix.mulVec_mulVec, matR_mul_inv hS, Matrix.one_mulVec]
    have heq := congrArg (WithLp.toLp 2) hinv
    rw [matR_mulVec_eq_sum_intCol] at heq
    exact heq.trans (Finset.sum_congr rfl fun k _ => by
      dsimp only [u]; rw [inv_mul_cancel_left₀ hq0])
  have hS_eq : toVecℤ (S *ᵥ fun k => (A_int *ᵥ z) k / (q : ℤ)) =
      ∑ k : Fin n, ((q : ℝ)⁻¹ * ∑ j : Fin m, (z j : ℝ) * (Int.floor (u j k) : ℝ)) •
        intCol S k := by
    rw [show toVecℤ (S *ᵥ fun k => (A_int *ᵥ z) k / (q : ℤ)) =
      WithLp.toLp 2 (matR S *ᵥ fun k => (((A_int *ᵥ z) k / (q : ℤ) : ℤ) : ℝ)) from
        congrArg (WithLp.toLp 2) (ofLp_toVecℤ_mulVec S _), matR_mulVec_eq_sum_intCol]
    simp_rw [hdiv]
  have hlhs : combineOutput B S q V C z - ∑ j : Fin m, z j • (C j).toVec =
      toVecℤ (S *ᵥ fun k => (A_int *ᵥ z) k / (q : ℤ)) - ∑ j : Fin m, (z j : ℝ) • (W j).toVec := by
    unfold combineOutput; dsimp only
    simp_rw [smul_sub, Finset.sum_sub_distrib, ← Int.cast_smul_eq_zsmul ℝ]; abel
  rw [hlhs, hS_eq]
  simp_rw [hW_eq, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, ← sub_smul]
  exact congrArg (· • intCol S k) <| by
    simp only [Int.fract, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- Combining procedure output membership and distance bound ([MicciancioRegev2007], Lemma 5.8,
items 2–3, p. 21): whenever `InKernelLattice (combineMatrix B S q V C) z`,
`combineOutput B S q V C z ∈ intLattice B` and
`‖combineOutput B S q V C z - ∑ j, z j • (C j).toVec‖ ≤ √m · n · ‖intCol S‖ · ‖z‖₂ / q`. -/
theorem combineOutput_mem_intLattice_and_norm_sub_le
    {n m q : ℕ} (hq : 0 < q) (B S : Matrix (Fin n) (Fin n) ℤ) (hS : S.det ≠ 0)
    (hSB : intLattice S ≤ intLattice B)
    (V : Fin m → SublatticeQuot B S) (C : Fin m → GridRep B q) (z : Fin m → ℤ)
    (hker : InKernelLattice (combineMatrix B S q V C) z) :
    combineOutput B S q V C z ∈ intLattice B ∧
      ‖combineOutput B S q V C z - ∑ j : Fin m, z j • (C j).toVec‖ ≤
        Real.sqrt m * n * ‖intCol S‖ * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖ / q := by
  refine ⟨combineOutput_mem_intLattice B S hS hSB q hq V C z, ?_⟩
  rw [combineOutput_sub_eq_fract hq B S hS V C z hker, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q)), inv_mul_eq_div]
  refine div_le_div_of_nonneg_right ((norm_sum_le _ _).trans ?_) (Nat.cast_nonneg q)
  calc ∑ k : Fin n, ‖(∑ j : Fin m, (z j : ℝ) * Int.fract
          ((q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp (combineColumn B S q (V j) (C j)).1.toVec) k)) •
          intCol S k‖
      ≤ ∑ _k : Fin n, (Real.sqrt m * ‖toVecℤ z‖) * ‖intCol S‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        have hcoeff : |∑ j : Fin m, (z j : ℝ) * Int.fract
            ((q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp (combineColumn B S q (V j) (C j)).1.toVec) k)| ≤
            Real.sqrt m * ‖toVecℤ z‖ :=
          (Finset.abs_sum_le_sum_abs _ _).trans <|
            (Finset.sum_le_sum fun j _ => by
              rw [abs_mul, abs_of_nonneg (Int.fract_nonneg ((q : ℝ) *
                ((matR S)⁻¹ *ᵥ WithLp.ofLp (combineColumn B S q (V j) (C j)).1.toVec) k))]
              exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le).trans
              (sum_abs_le_sqrt_mul_norm z)
        exact mul_le_mul hcoeff (norm_le_pi_norm (intCol S) k) (norm_nonneg _) (by positivity)
    _ = Real.sqrt m * n * ‖intCol S‖ * ‖toVecℤ z‖ := by simp; ring

/-! ### Part 4: Finite Single-Call `IncGDD` Reduction Step (Finite MR07 Theorem 5.9 Step) -/

/-- Nonzero integer guess `±(idx + 1)` from `(sgn, idx) : Bool × Fin K`. -/
private def guessAlpha {K : ℕ} (sgn : Bool) (idx : Fin K) : ℤ :=
  if sgn then ((idx : ℕ) + 1 : ℤ) else -((idx : ℕ) + 1 : ℤ)

private theorem guessAlpha_ne_zero {K : ℕ} (sgn : Bool) (idx : Fin K) :
    guessAlpha sgn idx ≠ 0 := by
  cases sgn <;> simp [guessAlpha] <;> omega

/-- Per-column target vector `t_i = -t / α` when `i = j`, else `0` (MR07 Theorem 5.9, p. 22). -/
private noncomputable def guessTarget {n m K : ℕ} (t : EuclideanSpace ℝ (Fin n))
    (g : Fin m × Bool × Fin K) (i : Fin m) : EuclideanSpace ℝ (Fin n) :=
  if i = g.1 then (-((guessAlpha g.2.1 g.2.2 : ℝ)⁻¹)) • t else 0

private theorem sum_smul_guessTarget_eq_neg {n m K : ℕ} (t : EuclideanSpace ℝ (Fin n))
    (g : Fin m × Bool × Fin K) (z : Fin m → ℤ) (hz : z g.1 = guessAlpha g.2.1 g.2.2) :
    ∑ i : Fin m, (z i : ℝ) • guessTarget t g i = -t := by
  rw [Finset.sum_eq_single g.1 (fun _ _ hi => by simp [guessTarget, hi])
    (fun h => (h (Finset.mem_univ g.1)).elim)]
  have hα : (guessAlpha g.2.1 g.2.2 : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (guessAlpha_ne_zero g.2.1 g.2.2)
  simp [guessTarget, hz, smul_smul, mul_inv_cancel₀ hα]

private theorem exists_guess_of_isEll2Solution {n m q : ℕ} {A : Matrix (Fin n) (Fin m) (ZMod q)}
    {β : ℝ} {z : Fin m → ℤ} (hz : SIS.IsEll2Solution A β z) :
    ∃ g : Fin m × Bool × Fin (Nat.floor β), z g.1 = guessAlpha g.2.1 g.2.2 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin m, z j ≠ 0 := by
    by_contra h; push Not at h; exact hz.1 (funext h)
  have hnat_pos : 1 ≤ (z j).natAbs := Int.natAbs_pos.mpr hj
  have hnat_le : (z j).natAbs ≤ Nat.floor β := by
    have h := hz.isSolution.2.1 j
    rw [Int.abs_eq_natAbs] at h; exact_mod_cast h
  refine ⟨(j, decide (0 < z j), ⟨(z j).natAbs - 1, by omega⟩), ?_⟩
  by_cases hpos : 0 < z j <;> simp [guessAlpha, hpos] <;> omega

/-- Single-call finite reduction step from `IncGDD` to `ℓ₂`-SIS using ideal discrete-grid samplers.
This is the finite distributional core step toward [MicciancioRegev2007], Theorem 5.9 (pp. 22–24);
strict-PPT realization and amplification are not formalized here and are tracked in
[#6861](https://github.com/cslib-community/cslib-frontier/issues/6861). -/
@[expose] noncomputable def idealIncGDDStep {n m q : ℕ} [NeZero q]
    (B S : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (β r : ℝ) (hβ : 1 ≤ β) (hr : 0 < r) (t : EuclideanSpace ℝ (Fin n))
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) :
    PMF (EuclideanSpace ℝ (Fin n)) :=
  if h : 1 ≤ n ∧ 1 ≤ m then
    have : Nonempty (Fin m) := ⟨⟨0, h.2⟩⟩
    have : Nonempty (Fin (Nat.floor β)) := ⟨⟨0, Nat.floor_pos.mpr hβ⟩⟩
    let s : ℝ := 2 * r / (β * Real.sqrt n)
    have hs : 0 < s := by
      have : (0 : ℝ) < n := Nat.cast_pos.mpr h.1
      have : (0 : ℝ) < β := lt_of_lt_of_le zero_lt_one hβ
      positivity
    (PMF.uniformOfFintype (Fin m × Bool × Fin (Nat.floor β))).bind fun ⟨j, sgn, idx⟩ =>
      let α : ℤ := if sgn then (idx.val + 1 : ℤ) else -((idx.val + 1 : ℤ))
      (Cslib.Probability.PMF.piFin fun i : Fin m =>
        idealGridSample B hB q (NeZero.pos q) s hs
          (if i = j then (-((α : ℝ)⁻¹)) • t else 0)).bind fun CY =>
          let C : Fin m → GridRep B q := fun i => (CY i).1
          let Y : Fin m → intLattice B := fun i => (CY i).2
          (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
            (ProbComp.eval (F (combineMatrix B S q V C))).map fun z =>
              combineOutput B S q V C z - ∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n))
  else
    PMF.pure 0

/-- Unconditional lattice membership on 100% of the support of `idealIncGDDStep` (including when
the SIS solver `F` fails or returns an invalid vector). -/
theorem idealIncGDDStep_support_mem_intLattice {n m q : ℕ} [NeZero q]
    (B S : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (hS : S.det ≠ 0)
    (hSB : intLattice S ≤ intLattice B)
    (β r : ℝ) (hβ : 1 ≤ β) (hr : 0 < r) (t : EuclideanSpace ℝ (Fin n))
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ))
    {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ (idealIncGDDStep B S hB β r hβ hr t F).support) :
    v ∈ intLattice B := by
  unfold idealIncGDDStep at hv
  split_ifs at hv
  · simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hv
    obtain ⟨_, _, CY, _, V, _, z, _, rfl⟩ := hv
    exact Submodule.sub_mem _
      (combineOutput_mem_intLattice B S hS hSB q (NeZero.pos q) V (fun i => (CY i).1) z)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (z i) (CY i).2.2)
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hv
    exact hv ▸ (intLattice B).zero_mem

private theorem eps_le_small {m : ℕ} {ε : ℝ}
    (hε : ε ≤ 1 / (400 * max 1 (Real.sqrt m))) : ε ≤ 1 / 400 :=
  hε.trans (one_div_le_one_div_of_le (by norm_num) (by linarith [le_max_left 1 (Real.sqrt m)]))

/-- `toMeasure` of `PMF.piFin` on a countable measurable space equals `Measure.pi`. -/
private theorem toMeasure_piFin {k : ℕ} {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] (p : Fin k → PMF α) :
    (Cslib.Probability.PMF.piFin p).toMeasure = Measure.pi (fun i => (p i).toMeasure) := by
  refine Measure.ext_of_singleton fun v => ?_
  simp [PMF.toMeasure_apply_singleton, Measure.pi_singleton, Cslib.Probability.PMF.piFin_apply]

/-- Numerical constant check from MR07 Theorem 5.9 (p. 24): for `ε ≤ 1 / (400 * max 1 √m)`,
`1 / (2π) + ε / (1 - ε) + m * (ε / (1 - ε))^2 ≤ 1 / 6`. -/
private theorem mr07_variance_const_le {m : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (400 * max 1 (Real.sqrt m))) :
    1 / (2 * Real.pi) + ε / (1 - ε) + (m : ℝ) * (ε / (1 - ε)) ^ 2 ≤ 1 / 6 := by
  have hε_small : ε ≤ 1 / 400 := eps_le_small hε
  have h1mε : (399 / 400 : ℝ) ≤ 1 - ε := by linarith
  have hmul : ε * Real.sqrt m ≤ 1 / 400 := by
    have := (le_div_iff₀ (show (0 : ℝ) < 400 * max 1 (Real.sqrt m) by
      linarith [le_max_left 1 (Real.sqrt m)])).1 hε
    nlinarith [le_max_right (1 : ℝ) (Real.sqrt m)]
  have hm_sq : (m : ℝ) * ε ^ 2 ≤ 1 / 160000 := by
    have := pow_le_pow_left₀ (by positivity) hmul 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at this; linarith
  have hterm1 : 1 / (2 * Real.pi) ≤ 1 / 6.28 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [Real.pi_gt_d2])
  have hterm2 : ε / (1 - ε) ≤ 1 / 399 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hterm3 : (m : ℝ) * (ε / (1 - ε)) ^ 2 ≤ 1 / 159201 := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - ε))]
    nlinarith [pow_le_pow_left₀ (by norm_num) h1mε 2]
  linarith

/-- Second-moment bound for independent shifted discrete Gaussians (MR07 Theorem 5.9, p. 24). -/
private theorem integral_norm_sum_smul_sq_discreteGaussian_le
    {n m : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    {β r ε : ℝ} (hβ : 1 ≤ β) (hr : 0 < r)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (400 * max 1 (Real.sqrt m)))
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B))
        (2 / (2 * r / (β * Real.sqrt n))) 0 - 1 ≤ ε)
    (centers : Fin m → EuclideanSpace ℝ (Fin n)) (z : Fin m → ℤ)
    (hz_norm : ‖toVecℤ z‖ ≤ β)
    (hs : 0 < 2 * r / (β * Real.sqrt n)) :
    let μ := (Cslib.Probability.PMF.piFin fun i : Fin m =>
      ZLattice.discreteGaussian (intLattice B) (2 * r / (β * Real.sqrt n)) hs
        (centers i)).toMeasure
    (∀ i, MemLp (fun Y : Fin m → intLattice B =>
      (Y i : EuclideanSpace ℝ (Fin n)) - centers i) 2 μ) ∧
    ∫ Y, ‖∑ i : Fin m, (z i : ℝ) • ((Y i : EuclideanSpace ℝ (Fin n)) - centers i)‖ ^ 2 ∂μ ≤
      (2 / 3 : ℝ) * r ^ 2 := by
  have := isZLattice_intLattice hB
  have hε1 : ε < 1 := by linarith [eps_le_small hε]
  set s := 2 * r / (β * Real.sqrt n)
  let p : Fin m → PMF (intLattice B) := fun i =>
    ZLattice.discreteGaussian (intLattice B) s hs (centers i)
  have hμ : (Cslib.Probability.PMF.piFin p).toMeasure = Measure.pi fun i => (p i).toMeasure :=
    toMeasure_piFin p
  have hmp (i : Fin m) : MeasurePreserving (fun Y : Fin m → intLattice B => Y i)
      (Cslib.Probability.PMF.piFin p).toMeasure (p i).toMeasure :=
    hμ ▸ measurePreserving_eval (fun j => (p j).toMeasure) i
  have hL2 (i : Fin m) : MemLp (fun Y : Fin m → intLattice B =>
      (Y i : EuclideanSpace ℝ (Fin n)) - centers i) 2
      (Cslib.Probability.PMF.piFin p).toMeasure :=
    (ZLattice.memLp_sub_discreteGaussian (intLattice B) s hs (centers i)).comp_measurePreserving
      (hmp i)
  refine ⟨hL2, ?_⟩
  have hind : iIndepFun (fun i Y => (Y i : EuclideanSpace ℝ (Fin n)) - centers i)
      (Cslib.Probability.PMF.piFin p).toMeasure := hμ ▸
    ProbabilityTheory.iIndepFun_pi (fun i =>
      (continuous_subtype_val.sub continuous_const).measurable.aemeasurable)
  have hcomp {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
      [BorelSpace F] [SecondCountableTopology F] (i : Fin m) (f : intLattice B → F)
      (hf : Continuous f) :
      ∫ Y, f (Y i) ∂(Cslib.Probability.PMF.piFin p).toMeasure = ∫ x, f x ∂(p i).toMeasure := by
    rw [← (hmp i).map_eq, integral_map (measurable_pi_apply i).aemeasurable
      hf.measurable.aestronglyMeasurable]
  have hsq (i : Fin m) : ∫ Y, ‖(Y i : EuclideanSpace ℝ (Fin n)) - centers i‖ ^ 2
      ∂(Cslib.Probability.PMF.piFin p).toMeasure ≤
      (1 / (2 * Real.pi) + ε / (1 - ε)) * s ^ 2 * n := by
    rw [hcomp i (fun x : intLattice B => ‖(x : EuclideanSpace ℝ (Fin n)) - centers i‖ ^ 2)
        ((continuous_subtype_val.sub continuous_const).norm.pow 2),
      ZLattice.integral_norm_sub_sq_discreteGaussian_eq_tsum]
    simpa [finrank_euclideanSpace_fin] using
      ZLattice.tsum_discreteGaussian_mul_norm_sub_sq_le (intLattice B) s hs (centers i) ε hε1 hdual
  have hmean (i : Fin m) : ‖∫ Y, (Y i : EuclideanSpace ℝ (Fin n)) - centers i
      ∂(Cslib.Probability.PMF.piFin p).toMeasure‖ ^ 2 ≤ (ε / (1 - ε)) ^ 2 * s ^ 2 * n := by
    rw [hcomp i (fun x : intLattice B => (x : EuclideanSpace ℝ (Fin n)) - centers i)
        (continuous_subtype_val.sub continuous_const),
      ZLattice.integral_sub_discreteGaussian_eq_tsum]
    simpa [finrank_euclideanSpace_fin] using
      ZLattice.norm_tsum_discreteGaussian_smul_sub_sq_le (intLattice B) s hs (centers i) ε hε1 hdual
  have hs2_n : s ^ 2 * n * β ^ 2 = 4 * r ^ 2 := by
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp only [s]; rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp [hn', (show β ≠ 0 by linarith)]; ring
  have hfactor : (1 / (2 * Real.pi) + ε / (1 - ε)) * s ^ 2 * n +
      (ε / (1 - ε)) ^ 2 * s ^ 2 * n * Fintype.card (Fin m) ≤ 1 / 6 * (s ^ 2 * n) := by
    have := mul_le_mul_of_nonneg_right (mr07_variance_const_le (m := m) hε0 hε)
      (by positivity : 0 ≤ s ^ 2 * n)
    simp only [Fintype.card_fin]; linarith
  have hsum_z_sq : ∑ i : Fin m, (z i : ℝ) ^ 2 ≤ β ^ 2 :=
    norm_sq_toVecℤ z ▸ pow_le_pow_left₀ (norm_nonneg _) hz_norm 2
  refine (ProbabilityTheory.integral_norm_sum_smul_sq_le_of_iIndepFun hind hL2 hsq hmean
    (fun i => (z i : ℝ))).trans <| (mul_le_mul hfactor hsum_z_sq
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)).trans_eq (by nlinarith [hs2_n])

/-- Conditional Gaussian norm bound (MR07 Theorem 5.9, pp. 23–24): for any fixed centers `c_i` and
integer coefficients `z` with `‖z‖₂ ≤ β`, independent discrete Gaussians `Y_i ~ D_{L(B), s, c_i}`
at width `s = 2r / (β √n)` satisfy `Pr[‖∑ z_i • (Y_i - c_i)‖ ≤ r] ≥ 1 / 3`. -/
private theorem cond_gaussian_sum_le_prob_ge_one_third
    {n m : ℕ} (hn : 1 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    {β r ε : ℝ} (hβ : 1 ≤ β) (hr : 0 < r)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (400 * max 1 (Real.sqrt m)))
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B))
        (2 / (2 * r / (β * Real.sqrt n))) 0 - 1 ≤ ε)
    (centers : Fin m → EuclideanSpace ℝ (Fin n)) (z : Fin m → ℤ)
    (hz_norm : ‖toVecℤ z‖ ≤ β) (hs : 0 < 2 * r / (β * Real.sqrt n)) :
    (1 / 3 : ℝ) ≤
      ((Cslib.Probability.PMF.piFin fun i : Fin m =>
          ZLattice.discreteGaussian (intLattice B) (2 * r / (β * Real.sqrt n)) hs
            (centers i)).toOuterMeasure
        {Y | ‖∑ i : Fin m, (z i : ℝ) •
          ((Y i : EuclideanSpace ℝ (Fin n)) - centers i)‖ ≤ r}).toReal := by
  have := isZLattice_intLattice hB
  let P := Cslib.Probability.PMF.piFin fun i : Fin m =>
    ZLattice.discreteGaussian (intLattice B) (2 * r / (β * Real.sqrt n)) hs (centers i)
  let S_good : Set (Fin m → intLattice B) :=
    {Y | ‖∑ i : Fin m, (z i : ℝ) • ((Y i : EuclideanSpace ℝ (Fin n)) - centers i)‖ ≤ r}
  have ⟨hL2, hE⟩ := integral_norm_sum_smul_sq_discreteGaussian_le hn B hB hβ hr hε0 hε hdual
    centers z hz_norm hs
  have hMem : MemLp (fun Y : Fin m → intLattice B => ∑ i : Fin m,
      (z i : ℝ) • ((Y i : EuclideanSpace ℝ (Fin n)) - centers i)) 2 P.toMeasure :=
    memLp_finsetSum _ fun i _ => (hL2 i).const_smul (z i : ℝ)
  have hbad := (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun Y => sq_nonneg _)
    ((memLp_two_iff_integrable_sq_norm hMem.aestronglyMeasurable).1 hMem) (r ^ 2)).trans hE
  have hbad_le : (P.toMeasure {Y | r ^ 2 ≤ ‖∑ i : Fin m, (z i : ℝ) •
      ((Y i : EuclideanSpace ℝ (Fin n)) - centers i)‖ ^ 2}).toReal ≤ 2 / 3 := by
    rw [measureReal_def] at hbad; nlinarith [sq_pos_of_pos hr]
  have hadd := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl P S_good
  have hcompl : (P.toOuterMeasure S_goodᶜ).toReal ≤ 2 / 3 := by
    have : IsProbabilityMeasure P.toMeasure := by
      rw [toMeasure_piFin]; infer_instance
    have hmeas : MeasurableSet S_goodᶜ := (Set.to_countable S_good).measurableSet.compl
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply P hmeas]
    exact (ENNReal.toReal_mono (measure_ne_top P.toMeasure _)
      (measure_mono fun Y hY => pow_le_pow_left₀ hr.le (not_le.1 hY).le 2)).trans hbad_le
  linarith

/-- Joint first-stage sample of the reduction `(gu, C, V, z)`. -/
private structure StepSample {n m q K : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) where
  guess : Fin m × Bool × Fin K
  grid : Fin m → GridRep B q
  quot : Fin m → SublatticeQuot B S
  sol : Fin m → ℤ

private theorem sisEll2Advantage_eq_pair_toReal {n m q : ℕ} [NeZero q] (β : ℝ)
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) :
    (sisEll2Advantage q β F : ℝ) =
      (((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
          (ProbComp.eval (F A)).map fun z => (A, z)).toOuterMeasure
        {p | SIS.IsEll2Solution p.1 β p.2}).toReal := by
  classical
  unfold sisEll2Advantage sisEll2Experiment Game.succProbability
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform]
  change (((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
      (ProbComp.eval (F A)).bind fun z => PMF.pure (decide (SIS.IsEll2Solution A β z))) true).toReal
    = (((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
      (ProbComp.eval (F A)).map fun z => (A, z)).toOuterMeasure
        {p | SIS.IsEll2Solution p.1 β p.2}).toReal
  congr 1
  rw [PMF.bind_apply, PMF.toOuterMeasure_bind_apply
    (p := PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q)))]
  refine tsum_congr fun A => ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply, PMF.bind_apply]
  congr 1
  refine tsum_congr fun z => by by_cases h : SIS.IsEll2Solution A β z <;> simp [h]

private theorem combineOutput_sub_sum_isSolution
    {n m q : ℕ} (hq_pos : 0 < q) (B S : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    {β g r : ℝ} (hg : 0 < g) (hq : g * n * Real.sqrt m * β ≤ (q : ℝ))
    (t : EuclideanSpace ℝ (Fin n)) (gu : Fin m × Bool × Fin (Nat.floor β))
    (C : Fin m → GridRep B q) (V : Fin m → SublatticeQuot B S) (z : Fin m → ℤ)
    (hsis : SIS.IsEll2Solution (combineMatrix B S q V C) β z)
    (hzg : z gu.1 = guessAlpha gu.2.1 gu.2.2) (Y : Fin m → intLattice B)
    (hY : ‖∑ i : Fin m, (z i : ℝ) • ((Y i : EuclideanSpace ℝ (Fin n)) -
      (guessTarget t gu i + (C i).toVec))‖ ≤ r) :
    IncGDD.IsSolution g (intLattice B) (intColCast B S hB) t r
      (combineOutput B S q V C z - ∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n))) := by
  refine ⟨Submodule.sub_mem _ (combineOutput_mem_intLattice B S hS hSB q hq_pos V C z)
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Y i).2), ?_⟩
  have hsum_eq : ∑ i : Fin m, (z i : ℝ) • ((Y i : EuclideanSpace ℝ (Fin n)) -
      (guessTarget t gu i + (C i).toVec)) =
      (∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n))) + t -
        ∑ i : Fin m, z i • (C i).toVec := by
    simp_rw [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [sum_smul_guessTarget_eq_neg t gu z hzg]
    simp_rw [Int.cast_smul_eq_zsmul]; abel
  have hcomb_le : ‖combineOutput B S q V C z - ∑ i : Fin m, z i • (C i).toVec‖ ≤
      ‖intColCast B S hB‖ / g := by
    rw [norm_intColCast]
    have h1 := (combineOutput_mem_intLattice_and_norm_sub_le hq_pos B S hS hSB V C z hsis.2.2).2
    have h2 : Real.sqrt m * n * ‖intCol S‖ * ‖toVecℤ z‖ / q ≤
        Real.sqrt m * n * ‖intCol S‖ * β / q := by gcongr; exact hsis.2.1
    refine h1.trans (h2.trans ?_)
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr hq_pos) hg]
    nlinarith [mul_le_mul_of_nonneg_right hq (norm_nonneg (intCol S))]
  calc ‖(combineOutput B S q V C z - ∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n))) - t‖
      = ‖(combineOutput B S q V C z - ∑ i : Fin m, z i • (C i).toVec) -
          ∑ i : Fin m, (z i : ℝ) • ((Y i : EuclideanSpace ℝ (Fin n)) -
            (guessTarget t gu i + (C i).toVec))‖ := by rw [hsum_eq]; congr 1; abel
    _ ≤ ‖combineOutput B S q V C z - ∑ i : Fin m, z i • (C i).toVec‖ +
          ‖∑ i : Fin m, (z i : ℝ) • ((Y i : EuclideanSpace ℝ (Fin n)) -
            (guessTarget t gu i + (C i).toVec))‖ := norm_sub_le _ _
    _ ≤ ‖intColCast B S hB‖ / g + r := add_le_add hcomb_le hY

private theorem idealIncGDDStep_eq_factor {n m q : ℕ} [NeZero q] (hn : 1 ≤ n) (hm : 1 ≤ m)
    (B S : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (β r : ℝ) (hβ : 1 ≤ β) (hr : 0 < r) (t : EuclideanSpace ℝ (Fin n))
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ))
    (hs : 0 < 2 * r / (β * Real.sqrt n)) :
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    letI : Nonempty (Fin (Nat.floor β)) := ⟨⟨0, Nat.floor_pos.mpr hβ⟩⟩
    let s := 2 * r / (β * Real.sqrt n)
    let pC := fun gu => Cslib.Probability.PMF.piFin fun i : Fin m =>
      (idealGridSample B hB q (NeZero.pos q) s hs (guessTarget t gu i)).map Prod.fst
    let pY := fun gu (C : Fin m → GridRep B q) => Cslib.Probability.PMF.piFin fun i : Fin m =>
      ZLattice.discreteGaussian (intLattice B) s hs (guessTarget t gu i + (C i).toVec)
    idealIncGDDStep B S hB β r hβ hr t F =
      ((PMF.uniformOfFintype (Fin m × Bool × Fin (Nat.floor β))).bind fun gu =>
        (pC gu).bind fun C =>
          (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
            (ProbComp.eval (F (combineMatrix B S q V C))).map fun z =>
              (⟨gu, C, V, z⟩ : StepSample B S)).bind fun x =>
        (pY x.guess x.grid).map fun Y =>
          combineOutput B S q x.quot x.grid x.sol -
            ∑ i : Fin m, x.sol i • (Y i : EuclideanSpace ℝ (Fin n)) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nonempty (Fin (Nat.floor β)) := ⟨⟨0, Nat.floor_pos.mpr hβ⟩⟩
  unfold idealIncGDDStep
  have hnm : 1 ≤ n ∧ 1 ≤ m := ⟨hn, hm⟩
  simp only [hnm, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin m × Bool × Fin (Nat.floor β))))
    (funext fun gu => ?_)
  have hpi : (Cslib.Probability.PMF.piFin fun i : Fin m =>
      idealGridSample B hB q (NeZero.pos q) _ hs (guessTarget t gu i)) =
      (Cslib.Probability.PMF.piFin fun i : Fin m =>
        (idealGridSample B hB q (NeZero.pos q) _ hs (guessTarget t gu i)).map Prod.fst).bind
          fun C => (Cslib.Probability.PMF.piFin fun i : Fin m =>
            ZLattice.discreteGaussian (intLattice B) _ hs (guessTarget t gu i + (C i).toVec)).map
              fun Y i => (C i, Y i) := by
    rw [show (fun i : Fin m => idealGridSample B hB q (NeZero.pos q) _ hs (guessTarget t gu i)) =
      fun i => ((idealGridSample B hB q (NeZero.pos q) _ hs (guessTarget t gu i)).map
        Prod.fst).bind fun c => (ZLattice.discreteGaussian (intLattice B) _ hs
          (guessTarget t gu i + c.toVec)).map fun y => (c, y) from funext fun i =>
        idealGridSample_eq_bind_discreteGaussian B hB q (NeZero.pos q) _ hs _,
      ← Cslib.Probability.PMF.piFin_bind]
    exact congrArg (PMF.bind _) (funext fun _ => Cslib.Probability.PMF.piFin_map _ _)
  change (Cslib.Probability.PMF.piFin fun i =>
    idealGridSample B hB q (NeZero.pos q) _ hs (guessTarget t gu i)).bind _ = _
  rw [hpi, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun C => ?_)
  rw [PMF.bind_map]
  change (Cslib.Probability.PMF.piFin fun i : Fin m =>
      ZLattice.discreteGaussian (intLattice B) (2 * r / (β * Real.sqrt n)) hs
        (guessTarget t gu i + (C i).toVec)).bind (fun Y =>
      (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
        (ProbComp.eval (F (combineMatrix B S q V C))).bind fun z => PMF.pure _) = _
  rw [PMF.bind_comm]
  exact congrArg (PMF.bind _) (funext fun V =>
    PMF.bind_comm _ (ProbComp.eval (F (combineMatrix B S q V C))) _)

private theorem idealJoint_good_prob_ge
    {n m q : ℕ} [NeZero q] (hm : 1 ≤ m) (B S : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    {β : ℝ} (hβ : 1 ≤ β) (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) :
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    letI : Nonempty (Fin (Nat.floor β)) := ⟨⟨0, Nat.floor_pos.mpr hβ⟩⟩
    let idealJoint : PMF (StepSample (m := m) (q := q) (K := Nat.floor β) B S) :=
      (PMF.uniformOfFintype _).bind fun gu =>
        (PMF.uniformOfFintype (Fin m → GridRep B q)).bind fun C =>
          (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
            (ProbComp.eval (F (combineMatrix B S q V C))).map fun z => ⟨gu, C, V, z⟩
    (sisEll2Advantage q β F : ℝ) / (2 * (Nat.floor β : ℝ) * m) ≤
      (idealJoint.toOuterMeasure {x | SIS.IsEll2Solution (combineMatrix B S q x.quot x.grid) β
        x.sol ∧ x.sol x.guess.1 = guessAlpha x.guess.2.1 x.guess.2.2}).toReal := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nonempty (Fin (Nat.floor β)) := ⟨⟨0, Nat.floor_pos.mpr hβ⟩⟩
  let Guess := Fin m × Bool × Fin (Nat.floor β)
  let pAZ : PMF (Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ℤ)) :=
    (PMF.uniformOfFintype _).bind fun A => (ProbComp.eval (F A)).map fun z => (A, z)
  intro idealJoint
  have hmap : idealJoint.map (fun x => (x.guess, combineMatrix B S q x.quot x.grid, x.sol)) =
      pAZ.bind fun p => (PMF.uniformOfFintype Guess).map fun gu => (gu, p.1, p.2) := by
    have hcomm : pAZ.bind (fun p => (PMF.uniformOfFintype Guess).map fun gu => (gu, p.1, p.2)) =
        (PMF.uniformOfFintype Guess).bind fun gu => pAZ.map fun p => (gu, p.1, p.2) :=
      PMF.bind_comm pAZ (PMF.uniformOfFintype Guess) fun p gu => PMF.pure (gu, p.1, p.2)
    rw [hcomm]
    simp only [idealJoint, PMF.map_bind]
    refine congrArg (PMF.bind _) (funext fun gu => ?_)
    change (PMF.uniformOfFintype (Fin m → GridRep B q)).bind _ =
      pAZ.map fun p => (gu, p.1, p.2)
    dsimp only [pAZ]
    rw [← idealCombine_matrix_eq_uniform B S hB hS hSB, PMF.map_bind, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun C => ?_)
    rw [PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun V => ?_)
    change ((ProbComp.eval _).map _).map _ = ((ProbComp.eval _).map _).map _
    rw [PMF.map_comp, PMF.map_comp]; rfl
  let E_AZ : Set (Guess × Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ℤ)) :=
    {x | SIS.IsEll2Solution x.2.1 β x.2.2 ∧ x.2.2 x.1.1 = guessAlpha x.1.2.1 x.1.2.2}
  have hcard : (Fintype.card Guess : ℝ) = 2 * (Nat.floor β : ℝ) * m := by
    simp only [Guess, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; push_cast; ring
  have hge := Cslib.Probability.PMF.toOuterMeasure_bind_ge_mul pAZ
    (fun p => (PMF.uniformOfFintype Guess).map fun gu => (gu, p.1, p.2))
    {p | SIS.IsEll2Solution p.1 β p.2} E_AZ (s₁ := (sisEll2Advantage q β F : ℝ))
    (s₂ := (Fintype.card Guess : ℝ)⁻¹) (by positivity)
    (sisEll2Advantage_eq_pair_toReal β F).le fun p _ hp => by
      obtain ⟨gu₀, hgu₀⟩ := exists_guess_of_isEll2Solution hp
      rw [PMF.toOuterMeasure_map_apply]
      have hsub : ({gu₀} : Set Guess) ⊆ (fun gu => (gu, p.1, p.2)) ⁻¹' E_AZ :=
        Set.singleton_subset_iff.mpr ⟨hp, hgu₀⟩
      simpa [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply] using
        Cslib.Probability.PMF.toOuterMeasure_toReal_mono (PMF.uniformOfFintype Guess) hsub
  rwa [← hmap, PMF.toOuterMeasure_map_apply, hcard, ← div_eq_mul_inv] at hge

/-- Product of `m` shifted discrete-grid marginals is within `m * ε / (2 * (1 - ε))` of uniform. -/
private theorem idealGridSample_piFin_closeTo_uniform {n m q : ℕ} (hq : 0 < q)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) {s ε : ℝ} (hs : 0 < s)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B)) (2 / s) 0 - 1 ≤ ε)
    (ts : Fin m → EuclideanSpace ℝ (Fin n)) :
    CloseTo (Cslib.Probability.PMF.piFin fun i : Fin m =>
        (idealGridSample B hB q hq s hs (ts i)).map Prod.fst)
      (PMF.uniformOfFintype (Fin m → GridRep B q))
      (ENNReal.ofReal (m * ε / (2 * (1 - ε)))) := by
  have := isZLattice_intLattice hB
  have := discreteTopology_dualSubmodule (intLattice B)
  have hdual_s : gaussianMass (LinearMap.BilinForm.dualSubmodule
      (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B)) (1 / s) 0 - 1 ≤ ε :=
    (sub_le_sub_right (ZLattice.gaussianMass_le_of_le _ (one_div_pos.mpr hs)
      (div_le_div_of_nonneg_right (by norm_num) hs.le) 0) 1).trans hdual
  have h1 := CloseTo.piFin (q := fun _ : Fin m => PMF.uniformOfFintype (GridRep B q))
    fun i => idealGridSample_fst_closeTo_uniform B hB q hq hs hε0 hε1 hdual_s (ts i)
  rwa [Cslib.Probability.PMF.piFin_const, Cslib.Probability.PMF.iid_uniformOfFintype,
    ← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (Nat.cast_nonneg m), ← mul_div_assoc] at h1

/-- Non-asymptotic single-call success lower bound for `idealIncGDDStep` (finite distributional
step toward [MicciancioRegev2007], Theorem 5.9, §5.2, pp. 22–24). Uses ideal discrete-grid
samplers on `G_q = (1 / q) ℤⁿ` and the dual-mass premise `ρ_{2/s}(L(B)* \ {0}) ≤ ε`; strict-PPT
realization and amplification are not formalized here and are tracked in
[#6861](https://github.com/cslib-community/cslib-frontier/issues/6861). -/
theorem idealIncGDDStep_succProb_of_sisEll2
    {n m q : ℕ} [NeZero q] (hn : 1 ≤ n) (hm : 1 ≤ m)
    (B S : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (hS : S.det ≠ 0)
    (hSB : intLattice S ≤ intLattice B)
    {β g r ε : ℝ} (hβ : 1 ≤ β) (hg : 0 < g) (hr : 0 < r)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (400 * max 1 (Real.sqrt m)))
    (hq : g * n * Real.sqrt m * β ≤ (q : ℝ))
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B))
        (2 / (2 * r / (β * Real.sqrt n))) 0 - 1 ≤ ε)
    (t : EuclideanSpace ℝ (Fin n))
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) :
    ((1 / 3 : ℝ) *
        ((sisEll2Advantage q β F : ℝ) / (2 * (Nat.floor β : ℝ) * m) -
          m * ε / (2 * (1 - ε)))) ≤
      ((idealIncGDDStep B S hB β r hβ hr t F).toOuterMeasure
        {v | IncGDD.IsSolution g (intLattice B) (intColCast B S hB) t r v}).toReal := by
  have hε1 : ε < 1 := by linarith [eps_le_small hε]
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nonempty (Fin (Nat.floor β)) := ⟨⟨0, Nat.floor_pos.mpr hβ⟩⟩
  have hs : 0 < 2 * r / (β * Real.sqrt n) := by
    have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have : (0 : ℝ) < β := lt_of_lt_of_le zero_lt_one hβ
    positivity
  let cont (gu : Fin m × Bool × Fin (Nat.floor β)) (C : Fin m → GridRep B q) :
      PMF (StepSample (m := m) (q := q) (K := Nat.floor β) B S) :=
    (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
      (ProbComp.eval (F (combineMatrix B S q V C))).map fun z => ⟨gu, C, V, z⟩
  let realJoint : PMF (StepSample (m := m) (q := q) (K := Nat.floor β) B S) :=
    (PMF.uniformOfFintype _).bind fun gu =>
      (Cslib.Probability.PMF.piFin fun i : Fin m =>
        (idealGridSample B hB q (NeZero.pos q) _ hs (guessTarget t gu i)).map Prod.fst).bind
        (cont gu)
  let idealJoint : PMF (StepSample (m := m) (q := q) (K := Nat.floor β) B S) :=
    (PMF.uniformOfFintype _).bind fun gu =>
      (PMF.uniformOfFintype (Fin m → GridRep B q)).bind (cont gu)
  let E_good : Set (StepSample (m := m) (q := q) (K := Nat.floor β) B S) :=
    {x | SIS.IsEll2Solution (combineMatrix B S q x.quot x.grid) β x.sol ∧
      x.sol x.guess.1 = guessAlpha x.guess.2.1 x.guess.2.2}
  have hclose : CloseTo realJoint idealJoint (ENNReal.ofReal (m * ε / (2 * (1 - ε)))) :=
    CloseTo.bind_right _ fun gu _ =>
      (idealGridSample_piFin_closeTo_uniform (NeZero.pos q) B hB hs hε0 hε1 hdual
        (guessTarget t gu)).bind_left (cont gu)
  have hreal_ge : (sisEll2Advantage q β F : ℝ) / (2 * (Nat.floor β : ℝ) * m) -
      m * ε / (2 * (1 - ε)) ≤ (realJoint.toOuterMeasure E_good).toReal :=
    by linarith [abs_le.1 (hclose.abs_toReal_sub_le (div_nonneg (mul_nonneg (Nat.cast_nonneg m) hε0)
      (by linarith)) E_good), idealJoint_good_prob_ge hm B S hB hS hSB hβ F]
  rw [idealIncGDDStep_eq_factor hn hm B S hB β r hβ hr t F hs, mul_comm]
  exact Cslib.Probability.PMF.toOuterMeasure_bind_ge_mul realJoint _ E_good _
    (by norm_num) hreal_ge fun x _ ⟨hsis, hzg⟩ => by
      rw [PMF.toOuterMeasure_map_apply]
      exact (cond_gaussian_sum_le_prob_ge_one_third hn B hB hβ hr hε0 hε hdual _ _
        hsis.2.1 hs).trans (Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ fun Y hY =>
          combineOutput_sub_sum_isSolution (NeZero.pos q) B S hB hS hSB hg hq t x.guess x.grid
            x.quot x.sol hsis hzg Y hY)

/-- Transfer of `idealIncGDDStep_succProb_of_sisEll2` to any approximate sampler `μ` within
`CloseTo` statistical distance `η` of `idealIncGDDStep`. -/
theorem incGDD_succProb_of_closeTo_idealIncGDDStep
    {n m q : ℕ} [NeZero q] (hn : 1 ≤ n) (hm : 1 ≤ m)
    (B S : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (hS : S.det ≠ 0)
    (hSB : intLattice S ≤ intLattice B)
    {β g r ε η : ℝ} (hβ : 1 ≤ β) (hg : 0 < g) (hr : 0 < r)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (400 * max 1 (Real.sqrt m))) (hη : 0 ≤ η)
    (hq : g * n * Real.sqrt m * β ≤ (q : ℝ))
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B))
        (2 / (2 * r / (β * Real.sqrt n))) 0 - 1 ≤ ε)
    (t : EuclideanSpace ℝ (Fin n))
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ))
    (μ : PMF (EuclideanSpace ℝ (Fin n)))
    (hclose : CloseTo μ (idealIncGDDStep B S hB β r hβ hr t F) (ENNReal.ofReal η)) :
    ((1 / 3 : ℝ) *
        ((sisEll2Advantage q β F : ℝ) / (2 * (Nat.floor β : ℝ) * m) -
          m * ε / (2 * (1 - ε)))) - η ≤
      (μ.toOuterMeasure
        {v | IncGDD.IsSolution g (intLattice B) (intColCast B S hB) t r v}).toReal := by
  have hbase := idealIncGDDStep_succProb_of_sisEll2 hn hm B S hB hS hSB hβ hg hr hε0 hε hq hdual t F
  have habs := hclose.abs_toReal_sub_le hη
    {v | IncGDD.IsSolution g (intLattice B) (intColCast B S hB) t r v}
  linarith [(abs_le.1 habs).1]

end Cslib.Crypto.SIS.MR07
