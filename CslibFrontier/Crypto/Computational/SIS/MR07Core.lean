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
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance.Product
import CslibFrontier.Probability.Uniform
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
private abbrev matR {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  B.map Int.cast

private theorem matR_det {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    (matR B).det = (B.det : ℝ) := by
  simpa [matR] using ((Int.castRingHom ℝ).map_det B).symm

private theorem matR_det_ne_zero {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0) :
    (matR B).det ≠ 0 := by
  rw [matR_det]
  exact Int.cast_ne_zero.mpr hB

private theorem isUnit_matR_det {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0) :
    IsUnit (matR B).det :=
  isUnit_iff_ne_zero.mpr (matR_det_ne_zero hB)

private theorem matR_mul_inv {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0) :
    matR B * (matR B)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv (matR B) (isUnit_matR_det hB)

private theorem matR_inv_mul {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0) :
    (matR B)⁻¹ * matR B = 1 :=
  Matrix.nonsing_inv_mul (matR B) (isUnit_matR_det hB)

/-- The columns of an invertible integer matrix `B` form an `ℝ`-basis of
`EuclideanSpace ℝ (Fin n)`. -/
private noncomputable def intColBasis {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  Basis.ofEquivFun
    { toFun := fun x => (matR B)⁻¹ *ᵥ WithLp.ofLp x
      map_add' := fun x y => by
        change (matR B)⁻¹ *ᵥ (WithLp.ofLp x + WithLp.ofLp y) = _
        rw [Matrix.mulVec_add]
      map_smul' := fun c x => by
        change (matR B)⁻¹ *ᵥ (c • WithLp.ofLp x) = _
        rw [Matrix.mulVec_smul]; rfl
      invFun := fun v => WithLp.toLp 2 (matR B *ᵥ v)
      left_inv := fun x => by
        ext i
        change (matR B *ᵥ ((matR B)⁻¹ *ᵥ WithLp.ofLp x)) i = x i
        rw [Matrix.mulVec_mulVec, matR_mul_inv hB, Matrix.one_mulVec]
      right_inv := fun v => by
        change (matR B)⁻¹ *ᵥ (matR B *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, matR_inv_mul hB, Matrix.one_mulVec] }

@[simp] private theorem coe_intColBasis {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    ⇑(intColBasis B hB) = intCol B := by
  ext j i
  simp [intColBasis, intCol, matR]

private theorem intLattice_eq_span_basis {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    intLattice B = Submodule.span ℤ (Set.range (intColBasis B hB)) := by
  rw [intLattice, coe_intColBasis]

private theorem discreteTopology_of_eq {E : Type*} [NormedAddCommGroup E]
    {L₁ L₂ : Submodule ℤ E} (h : L₁ = L₂) [DiscreteTopology L₂] :
    DiscreteTopology L₁ := by
  subst h
  exact inferInstance

private theorem isZLattice_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L₁ L₂ : Submodule ℤ E} (h : L₁ = L₂)
    [DiscreteTopology L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂] :
    IsZLattice ℝ L₁ :=
  ⟨by rw [h]; exact IsZLattice.span_top⟩

/-- Every integer lattice `intLattice B` is discrete in `EuclideanSpace ℝ (Fin n)`. -/
instance discreteTopology_intLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    DiscreteTopology (intLattice B) := by
  have hsub : (intLattice B : Set (EuclideanSpace ℝ (Fin n))) ⊆
      (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) :
        Set (EuclideanSpace ℝ (Fin n))) := by
    intro x hx
    change x ∈ Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
    refine Submodule.span_le.mpr ?_ hx
    rintro _ ⟨j, rfl⟩
    have heq : intCol B j = ∑ i : Fin n, B i j • (EuclideanSpace.basisFun (Fin n) ℝ).toBasis i := by
      ext i
      simp [intCol, EuclideanSpace.basisFun_apply, Pi.single_apply]
    rw [heq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (B i j) (Submodule.subset_span ⟨i, rfl⟩)
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range b)) := inferInstance
  exact DiscreteTopology.of_subset hdisc hsub

/-- Full-rank integer lattices are full-rank `ℤ`-lattices in `EuclideanSpace ℝ (Fin n)`. -/
theorem isZLattice_intLattice {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0) :
    IsZLattice ℝ (intLattice B) :=
  isZLattice_of_eq (intLattice_eq_span_basis B hB)

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
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    exact norm_le_pi_norm (intCol S) (Fin.cast (finrank_intLattice hB) i)
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro j
    have hj : intCol S j = intColCast B S hB (Fin.cast (finrank_intLattice hB).symm j) := by
      simp [intColCast]
    rw [hj]
    exact norm_le_pi_norm (intColCast B S hB) _

/-- The `ℝ`-basis of the fine grid `G_q = (1 / q) ℤⁿ`. -/
private noncomputable def gridBasis (n q : ℕ) (hq : 0 < q) :
    Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.unitsSMul
    (fun _ => Units.mk0 ((q : ℝ)⁻¹) (inv_ne_zero (Nat.cast_ne_zero.mpr hq.ne')))

private theorem gridLattice_eq_span_basis {n q : ℕ} (hq : 0 < q) :
    gridLattice n q = Submodule.span ℤ (Set.range (gridBasis n q hq)) := by
  unfold gridLattice gridBasis
  congr 1
  ext x
  simp [Basis.unitsSMul_apply]

/-- The fine grid `G_q = (1 / q) ℤⁿ` is discrete for every `q : ℕ`. -/
instance discreteTopology_gridLattice (n q : ℕ) : DiscreteTopology (gridLattice n q) := by
  by_cases hq : 0 < q
  · exact discreteTopology_of_eq (gridLattice_eq_span_basis hq)
  · have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
    subst hq0
    have hbot : gridLattice n 0 = ⊥ :=
      Submodule.span_eq_bot.mpr fun _ ⟨_, hj⟩ => by simpa using hj.symm
    have : Subsingleton (gridLattice n 0) := by
      rw [hbot]; infer_instance
    infer_instance

/-- The fine grid `G_q = (1 / q) ℤⁿ` is a full-rank `ℤ`-lattice for `q > 0`. -/
theorem isZLattice_gridLattice {n q : ℕ} (hq : 0 < q) :
    IsZLattice ℝ (gridLattice n q) :=
  isZLattice_of_eq (gridLattice_eq_span_basis hq)

/-- Characterization of membership in `intLattice B`. -/
theorem mem_intLattice_iff {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ intLattice B ↔ ∃ k : Fin n → ℤ, x = WithLp.toLp 2 (fun i => ((B *ᵥ k) i : ℝ)) := by
  constructor
  · intro hx
    rw [intLattice, Finsupp.mem_span_range_iff_exists_finsupp] at hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨c, ?_⟩
    ext i
    simp [Finsupp.sum_fintype, intCol, Matrix.mulVec, dotProduct, mul_comm]
  · rintro ⟨k, rfl⟩
    have heq : WithLp.toLp 2 (fun i => ((B *ᵥ k) i : ℝ)) = ∑ j : Fin n, k j • intCol B j := by
      ext i
      simp [intCol, Matrix.mulVec, dotProduct, mul_comm]
    rw [heq]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ (k j) (Submodule.subset_span ⟨j, rfl⟩)

/-- Characterization of membership in `gridLattice n q`. -/
theorem mem_gridLattice_iff {n q : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ gridLattice n q ↔
      ∃ u : Fin n → ℤ, x = ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ)) := by
  constructor
  · intro hx
    rw [gridLattice, Finsupp.mem_span_range_iff_exists_finsupp] at hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨c, ?_⟩
    ext i
    simp [Finsupp.sum_fintype, EuclideanSpace.basisFun_apply, Pi.single_apply, mul_comm]
  · rintro ⟨u, rfl⟩
    have heq : ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ)) =
        ∑ j : Fin n, u j • (((q : ℝ)⁻¹ : ℝ) • EuclideanSpace.basisFun (Fin n) ℝ j) := by
      ext i
      simp [EuclideanSpace.basisFun_apply, Pi.single_apply, mul_comm]
    rw [heq]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ (u j) (Submodule.subset_span ⟨j, rfl⟩)

/-- Every integer lattice is contained in the fine grid `G_q` for `q > 0`. -/
theorem intLattice_le_gridLattice {n q : ℕ} (hq : 0 < q) (B : Matrix (Fin n) (Fin n) ℤ) :
    intLattice B ≤ gridLattice n q := by
  intro x hx
  rw [mem_intLattice_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [mem_gridLattice_iff]
  refine ⟨fun i => (q : ℤ) * (B *ᵥ k) i, ?_⟩
  ext i
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  simp only [PiLp.smul_apply, Int.cast_mul, Int.cast_natCast, smul_eq_mul]
  field_simp [hq0]

/-- Dual-mass monotonicity from `intLattice B` to the fine grid `gridLattice n q`. -/
theorem gaussianMass_dual_gridLattice_le {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    {q : ℕ} (hq : 0 < q) {s : ℝ} (hs : 0 < s) :
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n)))
        (gridLattice n q)) (1 / s) 0 - 1 ≤
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n)))
        (intLattice B)) (1 / s) 0 - 1 := by
  have := isZLattice_intLattice hB
  have := isZLattice_gridLattice (n := n) hq
  have : DiscreteTopology
      (LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B)) :=
    discreteTopology_dualSubmodule (intLattice B)
  have : DiscreteTopology
      (LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) (gridLattice n q)) :=
    discreteTopology_dualSubmodule (gridLattice n q)
  have hsub : LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n)))
      (gridLattice n q) ≤
      LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B) := by
    intro w hw y hy
    exact hw y (intLattice_le_gridLattice hq B hy)
  have hinv : 0 < 1 / s := one_div_pos.mpr hs
  rw [gaussianMass_zero_sub_one_eq_tsum _ (1 / s) hinv,
    gaussianMass_zero_sub_one_eq_tsum _ (1 / s) hinv]
  let f : {w : LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n)))
        (gridLattice n q) | w ≠ 0} →
      {w : LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n)))
        (intLattice B) | w ≠ 0} :=
    fun w => ⟨⟨w.1.1, hsub w.1.2⟩, fun h => w.2 (Subtype.ext (congrArg (fun x => x.1) h))⟩
  have hfinj : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun x => x.1.1) h))
  have hsumD : Summable (fun w : {w : LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B) | w ≠ 0} =>
      gaussianWeight (1 / s) (w.1 : EuclideanSpace ℝ (Fin n))) :=
    ((summable_gaussianWeight _ (1 / s) hinv 0).subtype _).congr fun w => by simp
  have hsumG : Summable (fun w : {w : LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin n))) (gridLattice n q) | w ≠ 0} =>
      gaussianWeight (1 / s) (w.1 : EuclideanSpace ℝ (Fin n))) :=
    ((summable_gaussianWeight _ (1 / s) hinv 0).subtype _).congr fun w => by simp
  exact hsumG.tsum_le_tsum_of_inj f hfinj (fun _ _ => (gaussianWeight_pos _ _).le)
    (fun _ => le_rfl) hsumD

/-- Parallelepiped representative `x mod P(B) = B * frac(B⁻¹ x)` for invertible `B`. -/
@[expose] noncomputable def modParallelepiped {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  let Bℝ : Matrix (Fin n) (Fin n) ℝ := B.map Int.cast
  let ξ := Bℝ⁻¹ *ᵥ (WithLp.ofLp x)
  WithLp.toLp 2 (Bℝ *ᵥ fun k => ξ k - (Int.floor (ξ k) : ℝ))

private theorem sub_modParallelepiped_mem {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) : x - modParallelepiped B x ∈ intLattice B := by
  let ξ := (matR B)⁻¹ *ᵥ (WithLp.ofLp x)
  rw [mem_intLattice_iff]
  refine ⟨fun k => Int.floor (ξ k), ?_⟩
  ext i
  have hx : WithLp.ofLp x = matR B *ᵥ ξ := by
    simp [ξ, Matrix.mulVec_mulVec, matR_mul_inv hB]
  have hsub : WithLp.ofLp (x - modParallelepiped B x) =
      matR B *ᵥ fun k => (Int.floor (ξ k) : ℝ) := by
    change WithLp.ofLp x - matR B *ᵥ (fun k => ξ k - (Int.floor (ξ k) : ℝ)) = _
    rw [hx, ← Matrix.mulVec_sub]
    congr 1
    funext k
    simp [Pi.sub_apply]
  have hi := congrFun hsub i
  simpa [matR, Matrix.mulVec, dotProduct] using hi

private theorem modParallelepiped_add_mem {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ intLattice B) :
    modParallelepiped B (x + y) = modParallelepiped B x := by
  rw [mem_intLattice_iff] at hy
  obtain ⟨m, rfl⟩ := hy
  have hinv : (matR B)⁻¹ *ᵥ WithLp.ofLp (x + WithLp.toLp 2 (fun i => ((B *ᵥ m) i : ℝ))) =
      (matR B)⁻¹ *ᵥ WithLp.ofLp x + fun k => (m k : ℝ) := by
    have hmy : (fun i => ((B *ᵥ m) i : ℝ)) = matR B *ᵥ fun k => (m k : ℝ) := by
      funext i; simp [matR, Matrix.mulVec, dotProduct]
    change (matR B)⁻¹ *ᵥ (WithLp.ofLp x + fun i => ((B *ᵥ m) i : ℝ)) = _
    rw [Matrix.mulVec_add, hmy, Matrix.mulVec_mulVec, matR_inv_mul hB, Matrix.one_mulVec]
  unfold modParallelepiped
  dsimp only
  rw [hinv]
  congr 1
  congr 1
  funext k
  simp [Pi.add_apply, Int.floor_add_intCast]

private theorem modParallelepiped_idemp {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    modParallelepiped B (modParallelepiped B x) = modParallelepiped B x := by
  have hinv : (matR B)⁻¹ *ᵥ WithLp.ofLp (modParallelepiped B x) =
      fun k => ((matR B)⁻¹ *ᵥ WithLp.ofLp x) k -
        (Int.floor (((matR B)⁻¹ *ᵥ WithLp.ofLp x) k) : ℝ) := by
    simp [modParallelepiped, Matrix.mulVec_mulVec, matR_inv_mul hB]
  unfold modParallelepiped
  dsimp only
  change WithLp.toLp 2 (matR B *ᵥ fun k =>
    ((matR B)⁻¹ *ᵥ WithLp.ofLp (modParallelepiped B x)) k -
      (Int.floor (((matR B)⁻¹ *ᵥ WithLp.ofLp (modParallelepiped B x)) k) : ℝ)) = _
  rw [hinv]
  congr 1
  congr 1
  funext k
  have hfl : Int.floor (((matR B)⁻¹ *ᵥ WithLp.ofLp x) k -
      (Int.floor (((matR B)⁻¹ *ᵥ WithLp.ofLp x) k) : ℝ)) = 0 := by
    rw [Int.floor_sub_intCast, sub_self]
  rw [hfl, Int.cast_zero, sub_zero]

private theorem modParallelepiped_eq_iff_sub_mem {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : B.det ≠ 0) (x y : EuclideanSpace ℝ (Fin n)) :
    modParallelepiped B x = modParallelepiped B y ↔ x - y ∈ intLattice B := by
  constructor
  · intro h
    have h1 := sub_modParallelepiped_mem hB x
    have h2 := sub_modParallelepiped_mem hB y
    have heq : x - y = (x - modParallelepiped B x) - (y - modParallelepiped B y) := by
      rw [h]; abel
    rw [heq]
    exact Submodule.sub_mem _ h1 h2
  · intro h
    have hx : x = y + (x - y) := by abel
    rw [hx, modParallelepiped_add_mem hB h]

private theorem modParallelepiped_abs_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |(modParallelepiped B x) i| ≤ ∑ j : Fin n, |(B i j : ℝ)| := by
  unfold modParallelepiped
  dsimp only [WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, matR, Matrix.map_apply]
  calc |∑ j : Fin n, (B i j : ℝ) * (((matR B)⁻¹ *ᵥ WithLp.ofLp x) j -
          (Int.floor (((matR B)⁻¹ *ᵥ WithLp.ofLp x) j) : ℝ))|
      ≤ ∑ j : Fin n, |(B i j : ℝ) * (((matR B)⁻¹ *ᵥ WithLp.ofLp x) j -
          (Int.floor (((matR B)⁻¹ *ᵥ WithLp.ofLp x) j) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, |(B i j : ℝ)| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        have h0 : 0 ≤ ((matR B)⁻¹ *ᵥ WithLp.ofLp x) j -
            (Int.floor (((matR B)⁻¹ *ᵥ WithLp.ofLp x) j) : ℝ) :=
          sub_nonneg.mpr (Int.floor_le _)
        have h1 : ((matR B)⁻¹ *ᵥ WithLp.ofLp x) j -
            (Int.floor (((matR B)⁻¹ *ᵥ WithLp.ofLp x) j) : ℝ) ≤ 1 :=
          (sub_lt_iff_lt_add'.mpr (Int.lt_floor_add_one _)).le
        have habs : |((matR B)⁻¹ *ᵥ WithLp.ofLp x) j -
            (Int.floor (((matR B)⁻¹ *ᵥ WithLp.ofLp x) j) : ℝ)| ≤ 1 := by
          rw [abs_of_nonneg h0]; exact h1
        simpa using mul_le_mul_of_nonneg_left habs (abs_nonneg (B i j : ℝ))

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

/-- `GridRep B q` is always nonempty (`0` is a representative). -/
instance {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) : Nonempty (GridRep B q) := by
  refine ⟨⟨0, fun i => ?_, ?_⟩⟩
  · simp only [Pi.zero_apply, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg q) (Finset.sum_nonneg fun j _ => abs_nonneg _)
  · simp only [Pi.zero_apply]
    have hz : (((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun _ : Fin n => ((0 : ℤ) : ℝ))) = 0 := by
      ext i; simp
    rw [hz]
    ext i
    simp [modParallelepiped, Matrix.mulVec, dotProduct]

/-- `GridRep B q` is finite (explicit coordinate box). -/
noncomputable instance {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) :
    Fintype (GridRep B q) := by
  let M : Fin n → ℤ := fun i => (q : ℤ) * ∑ j : Fin n, |B i j|
  let box : Type := ∀ i : Fin n, { x : ℤ // x ∈ Finset.Icc (-M i) (M i) }
  have hinj : Function.Injective (fun c : GridRep B q =>
      (fun i => ⟨c.1 i, Finset.mem_Icc.mpr (abs_le.mp (c.2.1 i))⟩ : box)) := by
    intro a b h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have : Finite (GridRep B q) := Finite.of_injective _ hinj
  exact Fintype.ofFinite (GridRep B q)

/-- Scale an integer matrix by a natural number `q`. -/
private def scaleMat {n : ℕ} (q : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (q : ℤ) * B i j

/-- `GridRep B q` is in bijection with `(Fin n → ℤ) ⧸ range ((scaleMat q B).mulVecLin)`. -/
private noncomputable def gridRepEquivQuot {n q : ℕ} (hq : 0 < q)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    GridRep B q ≃ ((Fin n → ℤ) ⧸ LinearMap.range (scaleMat q B).mulVecLin) := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  let S := LinearMap.range (scaleMat q B).mulVecLin
  have hmemS : ∀ u : Fin n → ℤ,
      u ∈ S ↔ ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ)) ∈ intLattice B := by
    intro u
    rw [mem_intLattice_iff]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      ext i
      simp only [PiLp.smul_apply, smul_eq_mul, Matrix.mulVecLin_apply,
        scaleMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Int.cast_sum, Int.cast_mul,
        Int.cast_natCast]
      have hfactor : ∑ x : Fin n, (q : ℝ) * (B i x : ℝ) * (k x : ℝ) =
          (q : ℝ) * ∑ x : Fin n, (B i x : ℝ) * (k x : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => mul_assoc _ _ _
      rw [hfactor, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      funext i
      have hi := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hk
      simp only [PiLp.smul_apply, smul_eq_mul] at hi
      have hmul : (u i : ℝ) = (q : ℝ) * ((B *ᵥ k) i : ℝ) := by
        rw [← hi, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
      have hint : u i = (q : ℤ) * (B *ᵥ k) i := by exact_mod_cast hmul
      simpa [scaleMat, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hint.symm
  refine Equiv.ofBijective (fun c : GridRep B q => Submodule.Quotient.mk c.1) ⟨?_, ?_⟩
  · intro c₁ c₂ h
    rw [Submodule.Quotient.eq, hmemS] at h
    have hsub : c₁.toVec - c₂.toVec ∈ intLattice B := by
      convert h using 1
      ext i
      simp [GridRep.toVec, sub_eq_add_neg, mul_add]
    have hmod := (modParallelepiped_eq_iff_sub_mem hB c₁.toVec c₂.toVec).2 hsub
    rw [c₁.modParallelepiped_toVec, c₂.modParallelepiped_toVec] at hmod
    apply Subtype.ext
    funext i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hmod
    simp only [GridRep.toVec, PiLp.smul_apply, smul_eq_mul] at hi
    have hreal : (c₁.1 i : ℝ) = (c₂.1 i : ℝ) := (mul_right_inj' (inv_ne_zero hq0)).1 hi
    exact_mod_cast hreal
  · intro z
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective S z
    let x : EuclideanSpace ℝ (Fin n) := ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ))
    have hdiff : x - modParallelepiped B x ∈ intLattice B := sub_modParallelepiped_mem hB x
    obtain ⟨k, hk⟩ := (mem_intLattice_iff B _).1 hdiff
    let u' : Fin n → ℤ := fun i => u i - (q : ℤ) * (B *ᵥ k) i
    have hu'vec : ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u' i : ℝ)) =
        modParallelepiped B x := by
      ext i
      have hki := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hk
      simp only [PiLp.sub_apply, x, PiLp.smul_apply, smul_eq_mul] at hki
      have hmod : (modParallelepiped B x) i = (q : ℝ)⁻¹ * (u i : ℝ) - ((B *ᵥ k) i : ℝ) := by
        linarith
      simp only [PiLp.smul_apply, smul_eq_mul, u', Int.cast_sub, Int.cast_mul,
        Int.cast_natCast, mul_sub, hmod]
      field_simp [hq0]
    have hbox : ∀ i, |u' i| ≤ (q : ℤ) * ∑ j : Fin n, |B i j| := fun i => by
      have habs := modParallelepiped_abs_le B x i
      rw [← hu'vec] at habs
      simp only [PiLp.smul_apply, smul_eq_mul, abs_mul] at habs
      rw [abs_of_pos (inv_pos.mpr hqpos)] at habs
      have hmul : |(u' i : ℝ)| ≤ (q : ℝ) * ∑ j : Fin n, |(B i j : ℝ)| := by
        rwa [inv_mul_le_iff₀ hqpos] at habs
      exact_mod_cast hmul
    have hidemp : modParallelepiped B (((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u' i : ℝ))) =
        ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u' i : ℝ)) := by
      rw [hu'vec, modParallelepiped_idemp hB]
    refine ⟨⟨u', hbox, hidemp⟩, ?_⟩
    rw [Submodule.Quotient.eq]
    refine ⟨-k, ?_⟩
    funext i
    simp [u', scaleMat, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

private theorem mulVec_int_injective {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} (hM : M.det ≠ 0) :
    Function.Injective M.mulVec := by
  intro x y h
  have hsub : M *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
  have hdet : M.det • (x - y) = 0 := by
    calc M.det • (x - y) = (M.adjugate * M) *ᵥ (x - y) := by
            rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = M.adjugate *ᵥ (M *ᵥ (x - y)) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hsub, Matrix.mulVec_zero]
  have hxy0 : x - y = 0 := by
    funext i
    have hi := congrFun hdet i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_left hM
  exact sub_eq_zero.mp hxy0

private theorem card_quot_range_mulVecLin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.det ≠ 0) :
    Nat.card ((Fin n → ℤ) ⧸ LinearMap.range M.mulVecLin) = M.det.natAbs := by
  let N := LinearMap.range M.mulVecLin
  have hinj : Function.Injective M.mulVecLin := mulVec_int_injective hM
  let eN : (Fin n → ℤ) ≃ₗ[ℤ] N := LinearEquiv.ofInjective M.mulVecLin hinj
  let bN : Basis (Fin n) ℤ N := (Pi.basisFun ℤ (Fin n)).map eN
  rw [← Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin n)) N bN]
  congr 1
  rw [Pi.basisFun_det_apply]
  have hmat : Matrix.of (Subtype.val ∘ bN) = Mᵀ := by
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply, Matrix.transpose_apply, bN, Basis.map_apply,
      Pi.basisFun_apply, eN]
    have h1 : ((LinearEquiv.ofInjective M.mulVecLin hinj (Pi.single i 1) : N) : Fin n → ℤ) =
        M *ᵥ Pi.single i 1 := rfl
    rw [h1, Matrix.mulVec_single]
    simp
  rw [hmat, Matrix.det_transpose]

/-- Exact cardinality `Fintype.card (GridRep B q) = q^n * |det B|`. -/
theorem card_gridRep {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    {q : ℕ} (hq : 0 < q) :
    Fintype.card (GridRep B q) = q ^ n * B.det.natAbs := by
  let M : Matrix (Fin n) (Fin n) ℤ := scaleMat q B
  have hM_eq : M = (q : ℤ) • B := by ext i j; simp [M, scaleMat]
  have hMdet : M.det = (q : ℤ) ^ n * B.det := by
    rw [hM_eq, Matrix.det_smul, Fintype.card_fin]
  have hMne : M.det ≠ 0 := by
    rw [hMdet]
    exact mul_ne_zero (pow_ne_zero n (Int.natCast_ne_zero.mpr hq.ne')) hB
  calc Fintype.card (GridRep B q)
      = Nat.card (GridRep B q) := (Nat.card_eq_fintype_card).symm
    _ = Nat.card ((Fin n → ℤ) ⧸ LinearMap.range M.mulVecLin) :=
        Nat.card_congr (gridRepEquivQuot hq B hB)
    _ = M.det.natAbs := card_quot_range_mulVecLin M hMne
    _ = q ^ n * B.det.natAbs := by
        rw [hMdet, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]

/-! ### Part 2: Discrete-Grid Sampling Lemma (Finite MR07 Lemma 5.7, p. 20) -/

/-- Map a grid point `r ∈ G_q` to its parallelepiped representative
`c = (-r) mod P(B) ∈ GridRep B q`
and lattice point `y = r + c ∈ L(B)`. -/
private noncomputable def gridSplit {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (r : gridLattice n q) : GridRep B q × intLattice B := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  let u : Fin n → ℤ := Classical.choose ((mem_gridLattice_iff (-r.1)).1 (Submodule.neg_mem _ r.2))
  let c : GridRep B q := (gridRepEquivQuot hq B hB).symm (Submodule.Quotient.mk u)
  have hc_vec : c.toVec = modParallelepiped B (-r.1) := by
    have hu : (-r.1) = ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ)) :=
      Classical.choose_spec ((mem_gridLattice_iff (-r.1)).1 (Submodule.neg_mem _ r.2))
    have hq_eq : (Submodule.Quotient.mk c.1 :
        (Fin n → ℤ) ⧸ LinearMap.range (scaleMat q B).mulVecLin) = Submodule.Quotient.mk u :=
      (gridRepEquivQuot hq B hB).apply_symm_apply (Submodule.Quotient.mk u)
    rw [Submodule.Quotient.eq] at hq_eq
    obtain ⟨k, hk⟩ := hq_eq
    have hsub : c.toVec - (-r.1) ∈ intLattice B := by
      rw [hu, mem_intLattice_iff]
      refine ⟨k, ?_⟩
      ext i
      have hki := congrFun hk i
      simp only [GridRep.toVec, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.mulVecLin_apply, scaleMat, Matrix.mulVec, dotProduct, Matrix.of_apply] at hki ⊢
      have hki' : ((c.1 i - u i : ℤ) : ℝ) = (q : ℝ) * ∑ j : Fin n, (B i j : ℝ) * (k j : ℝ) := by
        have h1 : c.1 i - u i = (q : ℤ) * ∑ j : Fin n, B i j * k j := by
          simpa [Finset.mul_sum, mul_assoc] using hki.symm
        exact_mod_cast h1
      have : (q : ℝ)⁻¹ * (c.1 i : ℝ) - (q : ℝ)⁻¹ * (u i : ℝ) =
          (q : ℝ)⁻¹ * ((c.1 i - u i : ℤ) : ℝ) := by push_cast; ring
      rw [this, hki', ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
      simp
    have hmod := (modParallelepiped_eq_iff_sub_mem hB c.toVec (-r.1)).2 hsub
    exact c.modParallelepiped_toVec.symm.trans hmod
  have hy_mem : r.1 + c.toVec ∈ intLattice B := by
    have h := sub_modParallelepiped_mem hB (-r.1)
    rw [← hc_vec] at h
    have heq : r.1 + c.toVec = -(-r.1 - c.toVec) := by abel
    rw [heq]
    exact Submodule.neg_mem _ h
  exact (c, ⟨r.1 + c.toVec, hy_mem⟩)

private theorem gridSplit_snd_val {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (r : gridLattice n q) :
    ((gridSplit B hB q hq r).2 : EuclideanSpace ℝ (Fin n)) =
      r.1 + (gridSplit B hB q hq r).1.toVec := rfl

private theorem GridRep.ext_toVec {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {q : ℕ} (hq : 0 < q)
    {c₁ c₂ : GridRep B q} (h : c₁.toVec = c₂.toVec) : c₁ = c₂ := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  apply Subtype.ext
  funext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) h
  simp only [GridRep.toVec, PiLp.smul_apply, smul_eq_mul] at hi
  exact_mod_cast (mul_right_inj' (inv_ne_zero hq0)).1 hi

private theorem gridSplit_fst_toVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (r : gridLattice n q) :
    (gridSplit B hB q hq r).1.toVec = modParallelepiped B (-r.1) := by
  have hsum : r.1 + (gridSplit B hB q hq r).1.toVec ∈ intLattice B := by
    rw [← gridSplit_snd_val]
    exact (gridSplit B hB q hq r).2.2
  have hsub : (gridSplit B hB q hq r).1.toVec - (-r.1) ∈ intLattice B := by
    simpa [sub_neg_eq_add, add_comm] using hsum
  exact (gridSplit B hB q hq r).1.modParallelepiped_toVec.symm.trans
    ((modParallelepiped_eq_iff_sub_mem hB _ _).2 hsub)

private theorem gridSplit_bijective {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) : Function.Bijective (gridSplit B hB q hq) := by
  constructor
  · intro r₁ r₂ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun p => (p.2 : EuclideanSpace ℝ (Fin n))) h
    rw [gridSplit_snd_val, gridSplit_snd_val, h1] at h2
    exact Subtype.ext (add_right_cancel h2)
  · rintro ⟨c, y⟩
    have hc_mem : c.toVec ∈ gridLattice n q := (mem_gridLattice_iff _).2 ⟨c.1, rfl⟩
    have hy_mem : (y : EuclideanSpace ℝ (Fin n)) ∈ gridLattice n q :=
      intLattice_le_gridLattice hq B y.2
    let r : gridLattice n q := ⟨(y : EuclideanSpace ℝ (Fin n)) - c.toVec,
      Submodule.sub_mem _ hy_mem hc_mem⟩
    refine ⟨r, ?_⟩
    have hc_eq : (gridSplit B hB q hq r).1 = c := by
      have hvec := gridSplit_fst_toVec B hB q hq r
      have hneg : -r.1 = c.toVec + (-(y : EuclideanSpace ℝ (Fin n))) := by
        simp [r]; abel
      rw [hneg, modParallelepiped_add_mem hB (Submodule.neg_mem _ y.2),
        c.modParallelepiped_toVec] at hvec
      exact GridRep.ext_toVec hq hvec
    refine Prod.ext hc_eq ?_
    apply Subtype.ext
    rw [gridSplit_snd_val, hc_eq]
    simp [r]

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
  congr 1
  funext r
  have h1 : (gridSplit B hB q hq r).1 = (f r).1 :=
    GridRep.ext_toVec hq ((gridSplit_fst_toVec B hB q hq r).trans (hf_fst r).symm)
  refine Prod.ext h1 (Subtype.ext ?_)
  rw [gridSplit_snd_val, hf_snd, h1]

private theorem idealGridSample_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (s : ℝ) (hs : 0 < s) (t : EuclideanSpace ℝ (Fin n))
    (c : GridRep B q) (y : intLattice B) :
    idealGridSample B hB q hq s hs t (c, y) =
      ENNReal.ofReal (gaussianWeight s ((y : EuclideanSpace ℝ (Fin n)) - (t + c.toVec)) /
        gaussianMass (gridLattice n q) s t) := by
  have hbij := gridSplit_bijective B hB q hq
  let r : gridLattice n q := ⟨(y : EuclideanSpace ℝ (Fin n)) - c.toVec,
    Submodule.sub_mem _ (intLattice_le_gridLattice hq B y.2) ((mem_gridLattice_iff _).2 ⟨c.1, rfl⟩)⟩
  have hr : gridSplit B hB q hq r = (c, y) := by
    obtain ⟨r', hr'⟩ := hbij.2 (c, y)
    have hr'_eq : r' = r := by
      have h2 := congrArg (fun p => (p.2 : EuclideanSpace ℝ (Fin n))) hr'
      have h1 := congrArg (fun p => p.1.toVec) hr'
      rw [gridSplit_snd_val, h1] at h2
      exact Subtype.ext (eq_sub_of_add_eq h2)
    rwa [← hr'_eq]
  rw [idealGridSample, PMF.map_apply, tsum_eq_single r]
  · simp only [hr, ↓reduceIte]
    have hdiff : (r : EuclideanSpace ℝ (Fin n)) - t =
        (y : EuclideanSpace ℝ (Fin n)) - (t + c.toVec) := by
      simp [r]; abel
    rw [ZLattice.discreteGaussian_apply, hdiff,
      ← ENNReal.ofReal_div_of_pos (gaussianMass_pos _ s hs t)]
  · intro r' hr'
    have hne : (c, y) ≠ gridSplit B hB q hq r' := fun h => hr' (hbij.1 (h.symm.trans hr.symm))
    simp [hne]

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
    rw [PMF.map_apply]
    have htsum := (Equiv.sigmaEquivProd (GridRep B q) (intLattice B)).tsum_eq
      (fun p : GridRep B q × intLattice B =>
        if c = p.1 then idealGridSample B hB q hq s hs t p else 0)
    rw [← htsum, tsum_sigma']
    rw [tsum_eq_single c]
    · simp only [Equiv.sigmaEquivProd_apply, ↓reduceIte]
    · intro c' hc'; simp [Ne.symm hc']
  rw [hmap]
  simp_rw [idealGridSample_apply]
  have hsum : Summable (fun y : intLattice B =>
      gaussianWeight s ((y : EuclideanSpace ℝ (Fin n)) - (t + c.toVec)) /
        gaussianMass (gridLattice n q) s t) :=
    (summable_gaussianWeight (intLattice B) s hs (t + c.toVec)).div_const _
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun y => div_nonneg (gaussianWeight_pos _ _).le hZpos.le) hsum,
    ENNReal.toReal_ofReal (tsum_nonneg fun y => div_nonneg (gaussianWeight_pos _ _).le hZpos.le),
    tsum_div_const]
  rfl

/-- Exact conditional law `y | c ~ D_{L(B), s, t + c}` (MR07 Lemma 5.7, item 2). -/
theorem idealGridSample_eq_bind_discreteGaussian {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (q : ℕ) (hq : 0 < q) (s : ℝ) (hs : 0 < s)
    (t : EuclideanSpace ℝ (Fin n)) :
    idealGridSample B hB q hq s hs t =
      ((idealGridSample B hB q hq s hs t).map Prod.fst).bind fun c =>
        (ZLattice.discreteGaussian (intLattice B) s hs (t + c.toVec)).map fun y => (c, y) := by
  ext ⟨c, y⟩
  rw [PMF.bind_apply, tsum_eq_single c]
  · have hmap : ((ZLattice.discreteGaussian (intLattice B) s hs (t + c.toVec)).map
        fun y => (c, y)) (c, y) =
      ZLattice.discreteGaussian (intLattice B) s hs (t + c.toVec) y := by
      rw [PMF.map_apply, tsum_eq_single y]
      · simp
      · intro y' hy'; simp [Ne.symm hy']
    rw [hmap]
    have hfst : (idealGridSample B hB q hq s hs t).map Prod.fst c =
        ENNReal.ofReal (gaussianMass (intLattice B) s (t + c.toVec) /
          gaussianMass (gridLattice n q) s t) := by
      rw [← idealGridSample_fst_apply B hB q hq s hs t c,
        ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    rw [hfst, idealGridSample_apply, ZLattice.discreteGaussian_apply,
      ← ENNReal.ofReal_div_of_pos (gaussianMass_pos _ s hs _)]
    have hMc : 0 < gaussianMass (intLattice B) s (t + c.toVec) := gaussianMass_pos _ s hs _
    have hMq : 0 < gaussianMass (gridLattice n q) s t := gaussianMass_pos _ s hs _
    rw [← ENNReal.ofReal_mul (div_nonneg hMc.le hMq.le)]
    congr 1
    field_simp [hMc.ne', hMq.ne']
  · intro c' hc'
    have h0 : ((ZLattice.discreteGaussian (intLattice B) s hs (t + c'.toVec)).map
        fun y => (c', y)) (c, y) = 0 := by
      rw [PMF.map_apply]
      simp [Ne.symm hc']
    rw [h0, mul_zero]

/-- Elementary finite-distribution uniformity bound: if positive weights `a : α → ℝ` lie in
`[1 - ε, 1 + ε]` (`0 ≤ ε < 1`), then the normalized PMF is within `ε / (2 * (1 - ε))` of uniform
in `CloseTo` (4-line `nlinarith` proof, zero square roots). -/
private theorem closeTo_uniform_of_mem_Icc {α : Type} [Fintype α] [Nonempty α]
    (p : PMF α) {a : α → ℝ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (ha : ∀ x, 1 - ε ≤ a x ∧ a x ≤ 1 + ε)
    (hp : ∀ x, (p x).toReal = a x / ∑ y : α, a y) :
    CloseTo p (PMF.uniformOfFintype α) (ENNReal.ofReal (ε / (2 * (1 - ε)))) := by
  classical
  let N : ℝ := Fintype.card α
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr Fintype.card_pos
  let S : ℝ := ∑ y : α, a y
  let A : ℝ := S / N
  have hA_lo : 1 - ε ≤ A := by
    rw [le_div_iff₀ hNpos]
    calc (1 - ε) * N = ∑ _y : α, (1 - ε) := by simp [N]; ring
      _ ≤ ∑ y : α, a y := Finset.sum_le_sum fun y _ => (ha y).1
  have hA_hi : A ≤ 1 + ε := by
    rw [div_le_iff₀ hNpos]
    calc ∑ y : α, a y ≤ ∑ _y : α, (1 + ε) := Finset.sum_le_sum fun y _ => (ha y).2
      _ = (1 + ε) * N := by simp [N]; ring
  have hApos : 0 < A := lt_of_lt_of_le (by linarith) hA_lo
  have hSpos : 0 < S := by
    have : S = N * A := by simp [A, mul_div_cancel₀ _ hNpos.ne']
    rw [this]; positivity
  rw [closeTo_iff_tsum_tsub_le, tsum_fintype]
  have hterm : ∀ x : α, p x - PMF.uniformOfFintype α x =
      ENNReal.ofReal (max 0 ((a x - A) / S)) := fun x => by
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top p x),
      ← ENNReal.ofReal_toReal (PMF.apply_ne_top (PMF.uniformOfFintype α) x),
      ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, hp x]
    have hu : (PMF.uniformOfFintype α x).toReal = 1 / N := by
      simp [PMF.uniformOfFintype_apply, N]
    rw [hu]
    have hdiff : a x / S - 1 / N = (a x - A) / S := by
      have hSN : S = N * A := by simp [A, mul_div_cancel₀ _ hNpos.ne']
      field_simp [hSpos.ne', hNpos.ne']
      linarith
    rw [hdiff]
    by_cases h : 0 ≤ (a x - A) / S
    · rw [max_eq_right h]
    · rw [max_eq_left (le_of_not_ge h), ENNReal.ofReal_of_nonpos (le_of_not_ge h),
        ENNReal.ofReal_zero]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => le_max_left 0 _)]
  refine ENNReal.ofReal_le_ofReal ?_
  let sPos : Finset α := Finset.univ.filter fun x => A ≤ a x
  let sNeg : Finset α := Finset.univ.filter fun x => ¬ A ≤ a x
  have hV_eq : ∑ x : α, max 0 ((a x - A) / S) = (∑ x ∈ sPos, (a x - A)) / S := by
    rw [Finset.sum_div, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => A ≤ a x)]
    have h1 : ∑ x ∈ sPos, max 0 ((a x - A) / S) = ∑ x ∈ sPos, (a x - A) / S := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hAx : A ≤ a x := (Finset.mem_filter.mp hx).2
      exact max_eq_right (div_nonneg (sub_nonneg.mpr hAx) hSpos.le)
    have h2 : ∑ x ∈ sNeg, max 0 ((a x - A) / S) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hAx : a x < A := lt_of_not_ge (Finset.mem_filter.mp hx).2
      exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hAx.le) hSpos.le)
    rw [h1, h2, add_zero]
  rw [hV_eq]
  let V : ℝ := (∑ x ∈ sPos, (a x - A)) / N
  have hsum_zero : ∑ x : α, (a x - A) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hNA : N * A = S := mul_div_cancel₀ _ hNpos.ne'
    change S - N * A = 0
    linarith
  have hV_neg : V = (∑ x ∈ sNeg, (A - a x)) / N := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => A ≤ a x) (fun x => a x - A)
    rw [hsum_zero] at hsplit
    have hneg_sum : ∑ x ∈ sNeg, (A - a x) = -(∑ x ∈ sNeg, (a x - A)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    change (∑ x ∈ sPos, (a x - A)) / N = _
    rw [hneg_sum]
    have : ∑ x ∈ sPos, (a x - A) = -(∑ x ∈ sNeg, (a x - A)) := by linarith
    rw [this]
  let θ : ℝ := (sPos.card : ℝ) / N
  have hθ_comp : (sNeg.card : ℝ) / N = 1 - θ := by
    have hcards : sPos.card + sNeg.card = Fintype.card α := by
      have hdisj : Disjoint sPos sNeg :=
        Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
      rw [← Finset.card_union_of_disjoint hdisj, Finset.filter_union_filter_not_eq,
        Finset.card_univ]
    have hcardsR : (sPos.card : ℝ) + (sNeg.card : ℝ) = N := by dsimp only [N]; exact_mod_cast hcards
    simp only [θ]
    field_simp [hNpos.ne']
    linarith
  have hV1 : V ≤ θ * (1 + ε - A) := by
    have hsum_le : ∑ x ∈ sPos, (a x - A) ≤ (sPos.card : ℝ) * (1 + ε - A) := by
      calc ∑ x ∈ sPos, (a x - A) ≤ ∑ _x ∈ sPos, (1 + ε - A) :=
            Finset.sum_le_sum fun x _ => by linarith [(ha x).2]
        _ = (sPos.card : ℝ) * (1 + ε - A) := by simp; ring
    calc V = (∑ x ∈ sPos, (a x - A)) / N := rfl
      _ ≤ ((sPos.card : ℝ) * (1 + ε - A)) / N := div_le_div_of_nonneg_right hsum_le hNpos.le
      _ = θ * (1 + ε - A) := by simp [θ, mul_div_right_comm]
  have hV2 : V ≤ (1 - θ) * (A - (1 - ε)) := by
    have hsum_le : ∑ x ∈ sNeg, (A - a x) ≤ (sNeg.card : ℝ) * (A - (1 - ε)) := by
      calc ∑ x ∈ sNeg, (A - a x) ≤ ∑ _x ∈ sNeg, (A - (1 - ε)) :=
            Finset.sum_le_sum fun x _ => by linarith [(ha x).1]
        _ = (sNeg.card : ℝ) * (A - (1 - ε)) := by simp; ring
    calc V = (∑ x ∈ sNeg, (A - a x)) / N := hV_neg
      _ ≤ ((sNeg.card : ℝ) * (A - (1 - ε))) / N := div_le_div_of_nonneg_right hsum_le hNpos.le
      _ = (1 - θ) * (A - (1 - ε)) := by rw [← hθ_comp]; ring
  have hV_le : V ≤ ε / 2 := by
    by_cases hεz : ε = 0
    · subst hεz
      have hA1 : A = 1 := by linarith
      rw [hA1] at hV1
      linarith
    · have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hεz)
      have hmul1 : V * (A - (1 - ε)) ≤ θ * (1 + ε - A) * (A - (1 - ε)) := by
        have := mul_le_mul_of_nonneg_right hV1 (by linarith : 0 ≤ A - (1 - ε))
        linarith
      have hmul2 : V * (1 + ε - A) ≤ (1 - θ) * (A - (1 - ε)) * (1 + ε - A) := by
        have := mul_le_mul_of_nonneg_right hV2 (by linarith : 0 ≤ 1 + ε - A)
        linarith
      have hcomb : 2 * ε * V ≤ ε ^ 2 - (A - 1) ^ 2 := by nlinarith
      have h2 : 2 * ε * V ≤ ε ^ 2 := by nlinarith [sq_nonneg (A - 1)]
      nlinarith
  have hS_eq : (∑ x ∈ sPos, (a x - A)) / S = V / A := by
    have hSN : S = N * A := by simp [A, mul_div_cancel₀ _ hNpos.ne']
    simp only [V, hSN]
    field_simp [hNpos.ne', hApos.ne']
  rw [hS_eq]
  calc V / A ≤ (ε / 2) / (1 - ε) := by
        calc V / A ≤ (ε / 2) / A := div_le_div_of_nonneg_right hV_le hApos.le
          _ ≤ (ε / 2) / (1 - ε) := div_le_div_of_nonneg_left (by linarith) (by linarith) hA_lo
    _ = ε / (2 * (1 - ε)) := by field_simp

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
  have ha : ∀ c : GridRep B q, 1 - ε ≤ a c ∧ a c ≤ 1 + ε := fun c => by
    have hmem := gaussianMass_mem_Icc_of_dual_mass_le (intLattice B) s hs ε hdual (t + c.toVec)
    constructor
    · rw [le_div_iff₀ hMpos]; simpa [M, mul_comm] using hmem.1
    · rw [div_le_iff₀ hMpos]; simpa [M, mul_comm] using hmem.2
  have hsum_eq : ∑ c : GridRep B q, a c = gaussianMass (gridLattice n q) s t / M := by
    have htsum1 : ∑ c : GridRep B q,
        ((idealGridSample B hB q hq s hs t).map Prod.fst c).toReal = 1 := by
      have h1 := ((idealGridSample B hB q hq s hs t).map Prod.fst).tsum_coe
      rw [tsum_fintype] at h1
      have h2 := congrArg ENNReal.toReal h1
      rw [ENNReal.toReal_sum (fun c _ => PMF.apply_ne_top _ _), ENNReal.toReal_one] at h2
      exact h2
    simp_rw [idealGridSample_fst_apply B hB q hq s hs t] at htsum1
    rw [← Finset.sum_div] at htsum1
    have hZpos : 0 < gaussianMass (gridLattice n q) s t := gaussianMass_pos _ s hs t
    have hsumMass : ∑ c : GridRep B q, gaussianMass (intLattice B) s (t + c.toVec) =
        gaussianMass (gridLattice n q) s t := by
      rwa [div_eq_one_iff_eq hZpos.ne'] at htsum1
    simp only [a, ← Finset.sum_div, hsumMass]
  refine closeTo_uniform_of_mem_Icc _ hε0 hε1 ha fun c => ?_
  rw [idealGridSample_fst_apply B hB q hq s hs t c, hsum_eq]
  simp only [a]
  exact (div_div_div_cancel_right₀ (a := _) (b := _) hMpos.ne').symm

/-! ### Part 3: Sublattice Quotient & Discrete-Grid Combining Procedure (Finite MR07 Lemma 5.8) -/

/-- For `L(S) ≤ L(B)`, construct the integer transition matrix `U` satisfying `B * U = S`. -/
private noncomputable def sublatticeMat {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hSB : intLattice S ≤ intLattice B) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => Classical.choose ((mem_intLattice_iff B (intCol S j)).1
    (hSB (Submodule.subset_span ⟨j, rfl⟩))) i

private theorem mul_sublatticeMat {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hSB : intLattice S ≤ intLattice B) : B * sublatticeMat B S hSB = S := by
  ext i j
  have hj := Classical.choose_spec ((mem_intLattice_iff B (intCol S j)).1
    (hSB (Submodule.subset_span ⟨j, rfl⟩)))
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hj
  simp only [intCol, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul] at hi
  have hcast : ((S i j : ℤ) : ℝ) = (((B * sublatticeMat B S hSB) i j : ℤ) : ℝ) := by
    simp only [Matrix.mul_apply, sublatticeMat, Int.cast_sum, Int.cast_mul]
    exact hi
  exact (Int.cast_injective hcast).symm

private theorem det_sublatticeMat {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    (hSB : intLattice S ≤ intLattice B) : (sublatticeMat B S hSB).det = S.det / B.det := by
  have hdet : B.det * (sublatticeMat B S hSB).det = S.det := by
    rw [← Matrix.det_mul, mul_sublatticeMat]
  rw [← hdet, Int.mul_ediv_cancel_left _ hB]

private theorem det_sublatticeMat_ne_zero {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (_hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    (sublatticeMat B S hSB).det ≠ 0 := by
  intro h0
  have hdet : B.det * (sublatticeMat B S hSB).det = S.det := by
    rw [← Matrix.det_mul, mul_sublatticeMat]
  rw [h0, mul_zero] at hdet
  exact hS hdet.symm

private theorem natAbs_div_det_pos {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    0 < (S.det / B.det).natAbs := by
  rw [← det_sublatticeMat hB hSB]
  exact Int.natAbs_pos.mpr (det_sublatticeMat_ne_zero hB hS hSB)

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

/-- `SublatticeQuot B S` is always nonempty (`0` is a representative). -/
instance {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) : Nonempty (SublatticeQuot B S) := by
  have hz : WithLp.toLp 2 (fun i : Fin n => (((0 : Fin n → ℤ) i : ℤ) : ℝ)) = 0 := by
    ext i; simp
  refine ⟨⟨0, fun i => ?_, ?_, ?_⟩⟩
  · simp only [Pi.zero_apply, abs_zero]
    exact Finset.sum_nonneg fun j _ => abs_nonneg _
  · rw [hz]
    exact (intLattice B).zero_mem
  · rw [hz]
    ext i
    simp [modParallelepiped, Matrix.mulVec, dotProduct]

/-- `SublatticeQuot B S` is finite via the explicit coordinate box `[-∑_j |S i j|, ∑_j |S i j|]`. -/
noncomputable instance {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) :
    Fintype (SublatticeQuot B S) := by
  let M : Fin n → ℤ := fun i => ∑ j : Fin n, |S i j|
  let box : Type := ∀ i : Fin n, { x : ℤ // x ∈ Finset.Icc (-M i) (M i) }
  have hinj : Function.Injective (fun v : SublatticeQuot B S =>
      (fun i => ⟨v.1 i, Finset.mem_Icc.mpr (abs_le.mp (v.2.1 i))⟩ : box)) := by
    intro a b h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have : Finite (SublatticeQuot B S) := Finite.of_injective _ hinj
  exact Fintype.ofFinite (SublatticeQuot B S)

instance {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) : DecidableEq (SublatticeQuot B S) :=
  inferInstanceAs (DecidableEq (Subtype _))

private theorem modParallelepiped_mulVec_mem {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) (k : Fin n → ℤ) :
    modParallelepiped S (WithLp.toLp 2 (fun i => ((B *ᵥ k) i : ℝ))) ∈ intLattice B := by
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => ((B *ᵥ k) i : ℝ))
  have hx : x ∈ intLattice B := (mem_intLattice_iff B x).2 ⟨k, rfl⟩
  have hxw : x - modParallelepiped S x ∈ intLattice B := hSB (sub_modParallelepiped_mem hS x)
  have heq : modParallelepiped S x = x - (x - modParallelepiped S x) := by abel
  rw [heq]
  exact Submodule.sub_mem _ hx hxw

/-- Construct a `SublatticeQuot B S` representative from an integer coordinate vector `k`
for `B`. -/
private noncomputable def mkSublatticeQuot {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) (k : Fin n → ℤ) :
    SublatticeQuot B S := by
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => ((B *ᵥ k) i : ℝ))
  let w : EuclideanSpace ℝ (Fin n) := modParallelepiped S x
  have hw : w ∈ intLattice B := modParallelepiped_mulVec_mem B S hS hSB k
  let m : Fin n → ℤ := Classical.choose ((mem_intLattice_iff B w).1 hw)
  have hm : w = WithLp.toLp 2 (fun i => ((B *ᵥ m) i : ℝ)) :=
    Classical.choose_spec ((mem_intLattice_iff B w).1 hw)
  refine ⟨B *ᵥ m, fun i => ?_, ?_, ?_⟩
  · have h1 := modParallelepiped_abs_le S x i
    have hwi : w i = ((B *ᵥ m) i : ℝ) := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hm
    change |w i| ≤ _ at h1
    rw [hwi] at h1
    exact_mod_cast (by simpa [Int.cast_abs, Int.cast_sum] using h1 :
      (|(B *ᵥ m) i| : ℝ) ≤ ((∑ j : Fin n, |S i j| : ℤ) : ℝ))
  · rw [← hm]; exact hw
  · rw [← hm]; exact modParallelepiped_idemp hS x

private theorem mkSublatticeQuot_toVec {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) (k : Fin n → ℤ) :
    (mkSublatticeQuot B S hS hSB k).toVec =
      modParallelepiped S (WithLp.toLp 2 (fun i => ((B *ᵥ k) i : ℝ))) :=
  (Classical.choose_spec
    ((mem_intLattice_iff B _).1 (modParallelepiped_mulVec_mem B S hS hSB k))).symm

private theorem sublatticeQuotEquivQuot_mkSublatticeQuot_aux
    {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) (k : Fin n → ℤ) :
    Submodule.Quotient.mk (p := LinearMap.range (sublatticeMat B S hSB).mulVecLin)
      (Classical.choose ((mem_intLattice_iff B (mkSublatticeQuot B S hS hSB k).toVec).1
        (mkSublatticeQuot B S hS hSB k).mem_intLattice)) =
      Submodule.Quotient.mk (p := LinearMap.range (sublatticeMat B S hSB).mulVecLin) k := by
  let U := sublatticeMat B S hSB
  rw [Submodule.Quotient.eq]
  set v := mkSublatticeQuot B S hS hSB k
  set kv := Classical.choose ((mem_intLattice_iff B v.toVec).1 v.mem_intLattice)
  have hkv : v.toVec = WithLp.toLp 2 (fun i => ((B *ᵥ kv) i : ℝ)) :=
    Classical.choose_spec ((mem_intLattice_iff B v.toVec).1 v.mem_intLattice)
  have hdiff : WithLp.toLp 2 (fun i => ((B *ᵥ k) i : ℝ)) - v.toVec ∈ intLattice S := by
    rw [mkSublatticeQuot_toVec]
    exact sub_modParallelepiped_mem hS _
  obtain ⟨m, hm⟩ := (mem_intLattice_iff S _).1 hdiff
  refine ⟨-m, ?_⟩
  have hB_eq : B *ᵥ (kv - k) = B *ᵥ (U *ᵥ (-m)) := by
    rw [Matrix.mulVec_mulVec, mul_sublatticeMat, Matrix.mulVec_neg, Matrix.mulVec_sub]
    funext i
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) hm
    rw [hkv] at hi
    simp only [PiLp.sub_apply] at hi
    have hzi : (B *ᵥ k) i - (B *ᵥ kv) i = (S *ᵥ m) i := by
      exact_mod_cast hi
    simp only [Pi.sub_apply, Pi.neg_apply]
    omega
  exact (mulVec_int_injective hB hB_eq).symm

private noncomputable def sublatticeQuotEquivQuot {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    SublatticeQuot B S ≃ (Fin n → ℤ) ⧸ LinearMap.range (sublatticeMat B S hSB).mulVecLin := by
  let U := sublatticeMat B S hSB
  let N := LinearMap.range U.mulVecLin
  refine Equiv.ofBijective
    (fun v : SublatticeQuot B S =>
      Submodule.Quotient.mk (p := N)
        (Classical.choose ((mem_intLattice_iff B v.toVec).1 v.mem_intLattice)))
    ⟨?_, ?_⟩
  · intro v₁ v₂ h
    rw [Submodule.Quotient.eq] at h
    obtain ⟨m, hm⟩ := h
    set k₁ := Classical.choose ((mem_intLattice_iff B v₁.toVec).1 v₁.mem_intLattice)
    set k₂ := Classical.choose ((mem_intLattice_iff B v₂.toVec).1 v₂.mem_intLattice)
    have hk₁ : v₁.toVec = WithLp.toLp 2 (fun i => ((B *ᵥ k₁) i : ℝ)) :=
      Classical.choose_spec ((mem_intLattice_iff B v₁.toVec).1 v₁.mem_intLattice)
    have hk₂ : v₂.toVec = WithLp.toLp 2 (fun i => ((B *ᵥ k₂) i : ℝ)) :=
      Classical.choose_spec ((mem_intLattice_iff B v₂.toVec).1 v₂.mem_intLattice)
    have hsub : v₁.toVec - v₂.toVec ∈ intLattice S := by
      rw [hk₁, hk₂, mem_intLattice_iff]
      refine ⟨m, ?_⟩
      ext i
      have hBU : B *ᵥ (k₁ - k₂) = S *ᵥ m := by
        have hkm : k₁ - k₂ = U *ᵥ m := hm.symm
        rw [hkm, Matrix.mulVec_mulVec, mul_sublatticeMat]
      have hi := congrFun hBU i
      simp only [Matrix.mulVec_sub, Pi.sub_apply] at hi
      simp only [PiLp.sub_apply]
      exact_mod_cast hi
    have hmod := (modParallelepiped_eq_iff_sub_mem hS v₁.toVec v₂.toVec).2 hsub
    rw [v₁.modParallelepiped_toVec, v₂.modParallelepiped_toVec] at hmod
    apply Subtype.ext
    funext i
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) hmod
    exact Int.cast_injective hi
  · intro qx
    refine Quotient.inductionOn' qx fun k =>
      ⟨mkSublatticeQuot B S hS hSB k, sublatticeQuotEquivQuot_mkSublatticeQuot_aux B S hB hS hSB k⟩

private theorem sublatticeQuotEquivQuot_mkSublatticeQuot
    {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) (k : Fin n → ℤ) :
    sublatticeQuotEquivQuot B S hB hS hSB (mkSublatticeQuot B S hS hSB k) =
      Submodule.Quotient.mk k :=
  sublatticeQuotEquivQuot_mkSublatticeQuot_aux B S hB hS hSB k

/-- Exact cardinality `Fintype.card (SublatticeQuot B S) = |det(B⁻¹ S)|`. -/
theorem card_sublatticeQuot {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    Fintype.card (SublatticeQuot B S) = (S.det / B.det).natAbs := by
  let U := sublatticeMat B S hSB
  have hUne : U.det ≠ 0 := det_sublatticeMat_ne_zero hB hS hSB
  calc Fintype.card (SublatticeQuot B S)
      = Nat.card (SublatticeQuot B S) := (Nat.card_eq_fintype_card).symm
    _ = Nat.card ((Fin n → ℤ) ⧸ LinearMap.range U.mulVecLin) :=
        Nat.card_congr (sublatticeQuotEquivQuot B S hB hS hSB)
    _ = U.det.natAbs := card_quot_range_mulVecLin U hUne
    _ = (S.det / B.det).natAbs := by rw [det_sublatticeMat hB hSB]

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
  let D : ℕ := (S.det / B.det).natAbs
  have hDpos : 0 < D := natAbs_div_det_pos hB hS hSB
  have : NeZero D := ⟨hDpos.ne'⟩
  let U := sublatticeMat B S hSB
  let N := LinearMap.range U.mulVecLin
  have hD_mem : ∀ w : Fin n → ℤ, (D : ℤ) • w ∈ N := fun w => by
    have hDU : (D : ℤ) = U.det ∨ (D : ℤ) = -U.det := by
      have : (D : ℤ) = |U.det| := by
        simp only [D, U, ← det_sublatticeMat hB hSB, Int.natCast_natAbs]
      rcases le_or_gt 0 U.det with h | h
      · left; rwa [abs_of_nonneg h] at this
      · right; rwa [abs_of_neg h] at this
    rcases hDU with h | h
    · refine ⟨U.adjugate *ᵥ w, ?_⟩
      change U *ᵥ (U.adjugate *ᵥ w) = (D : ℤ) • w
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, h]
    · refine ⟨-(U.adjugate *ᵥ w), ?_⟩
      change U *ᵥ (-(U.adjugate *ᵥ w)) = (D : ℤ) • w
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, h, neg_smul]
  have hsub_mem_of_zmod : ∀ u v : Fin n → ℤ,
      (∀ j : Fin n, (u j : ZMod D) = (v j : ZMod D)) → u - v ∈ N := fun u v huv => by
    have hdvd : ∀ j : Fin n, (D : ℤ) ∣ (u j - v j) := fun j => by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, huv j, sub_self]
    let w : Fin n → ℤ := fun j => (u j - v j) / (D : ℤ)
    have heq : u - v = (D : ℤ) • w := by
      funext j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, w]
      exact (Int.mul_ediv_cancel' (hdvd j)).symm
    rw [heq]
    exact hD_mem w
  have : Fintype ((Fin n → ℤ) ⧸ N) :=
    Fintype.ofEquiv (SublatticeQuot B S) (sublatticeQuotEquivQuot B S hB hS hSB)
  let φ : (Fin n → ZMod D) →+ ((Fin n → ℤ) ⧸ N) := {
    toFun := fun x => Submodule.Quotient.mk (fun j => ((x j).val : ℤ))
    map_zero' := by
      change Submodule.Quotient.mk (fun j : Fin n => (((0 : Fin n → ZMod D) j).val : ℤ)) = 0
      simp only [Pi.zero_apply, ZMod.val_zero, Nat.cast_zero]
      exact Submodule.Quotient.mk_zero N
    map_add' := fun x y => by
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
      exact hsub_mem_of_zmod _ _ fun j => by push_cast; simp
  }
  have hφ_surj : Function.Surjective φ := fun qk => by
    refine Quotient.inductionOn' qk fun k => ?_
    refine ⟨fun j => (k j : ZMod D), ?_⟩
    change Submodule.Quotient.mk (fun j => (((k j : ZMod D).val : ℤ))) = Submodule.Quotient.mk k
    rw [Submodule.Quotient.eq]
    exact hsub_mem_of_zmod _ _ fun j => by push_cast; simp
  have hcomp : quotientHom B S hS hSB =
      (sublatticeQuotEquivQuot B S hB hS hSB).symm ∘ φ := by
    funext x
    apply (sublatticeQuotEquivQuot B S hB hS hSB).injective
    rw [Function.comp_apply, Equiv.apply_symm_apply]
    exact sublatticeQuotEquivQuot_mkSublatticeQuot B S hB hS hSB (fun j => ((x j).val : ℤ))
  rw [hcomp, ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_addHom φ hφ_surj]
  exact Cslib.Probability.PMF.uniformOfFintype_map_equiv
    (sublatticeQuotEquivQuot B S hB hS hSB).symm

private theorem modParallelepiped_mem_gridLattice {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) (q : ℕ) (hq : 0 < q) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ gridLattice n q) : modParallelepiped S x ∈ gridLattice n q := by
  have hxw : x - modParallelepiped S x ∈ gridLattice n q :=
    intLattice_le_gridLattice hq S (sub_modParallelepiped_mem hS x)
  have heq : modParallelepiped S x = x - (x - modParallelepiped S x) := by abel
  rw [heq]
  exact Submodule.sub_mem _ hx hxw

/-- Construct the `GridRep S q` element representing `modParallelepiped S x` for `x ∈ G_q`. -/
private noncomputable def mkGridRep {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (hS : S.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ gridLattice n q) :
    GridRep S q := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  let w : EuclideanSpace ℝ (Fin n) := modParallelepiped S x
  have hw : w ∈ gridLattice n q := modParallelepiped_mem_gridLattice S hS q hq x hx
  let u : Fin n → ℤ := Classical.choose ((mem_gridLattice_iff w).1 hw)
  have hu : w = ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ)) :=
    Classical.choose_spec ((mem_gridLattice_iff w).1 hw)
  refine ⟨u, fun i => ?_, ?_⟩
  · have h1 := modParallelepiped_abs_le S x i
    have hwi : w i = (q : ℝ)⁻¹ * (u i : ℝ) := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hu
    have hq_nonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hmul : (q : ℝ) * |w i| ≤ (q : ℝ) * ∑ j : Fin n, |(S i j : ℝ)| :=
      mul_le_mul_of_nonneg_left h1 hq_nonneg
    have hqabs : (q : ℝ) * |w i| = |(u i : ℝ)| := by
      rw [hwi, abs_mul, abs_of_nonneg (inv_nonneg.mpr hq_nonneg), ← mul_assoc,
        mul_inv_cancel₀ hq0, one_mul]
    rw [hqabs] at hmul
    exact_mod_cast (by simpa [Int.cast_abs, Int.cast_sum] using hmul :
      (|u i| : ℝ) ≤ (((q : ℤ) * ∑ j : Fin n, |S i j| : ℤ) : ℝ))
  · rw [← hu]; exact modParallelepiped_idemp hS x

private theorem mkGridRep_toVec {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (hS : S.det ≠ 0)
    (q : ℕ) (hq : 0 < q) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ gridLattice n q) :
    (mkGridRep S hS q hq x hx).toVec = modParallelepiped S x :=
  (Classical.choose_spec
    ((mem_gridLattice_iff _).1 (modParallelepiped_mem_gridLattice S hS q hq x hx))).symm

/-- Discretized parallelepiped coordinate `a(w) = ⌊q · S⁻¹ w⌋ mod q` for `w ∈ GridRep S q`. -/
private noncomputable def gridRepToZMod {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (q : ℕ)
    (w : GridRep S q) : Fin n → ZMod q :=
  fun k => (Int.floor ((q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k) : ZMod q)

private theorem gridRepToZMod_val {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ} (hS : S.det ≠ 0)
    {q : ℕ} (hq : 0 < q) (w : GridRep S q) (k : Fin n) :
    ((gridRepToZMod S q w k).val : ℤ) =
      Int.floor ((q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k) := by
  have hmod : w.toVec = modParallelepiped S w.toVec := w.modParallelepiped_toVec.symm
  have hξ : ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k =
      ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k -
        (Int.floor (((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k) : ℝ) := by
    conv_lhs => rw [hmod]
    simp [modParallelepiped, Matrix.mulVec_mulVec, matR_inv_mul hS]
  have hξ0 : 0 ≤ ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k := by
    rw [hξ]; exact sub_nonneg.mpr (Int.floor_le _)
  have hξ1 : ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k < 1 := by
    rw [hξ]; exact sub_lt_iff_lt_add'.mpr (Int.lt_floor_add_one _)
  set m : ℤ := Int.floor ((q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k)
  have hm0 : 0 ≤ m := Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg q) hξ0)
  have hm1 : m < (q : ℤ) := by
    rw [Int.floor_lt]
    calc (q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k < (q : ℝ) * 1 :=
          mul_lt_mul_of_pos_left hξ1 (Nat.cast_pos.mpr hq)
      _ = (q : ℝ) := mul_one _
  have hcast : (m : ZMod q) = ((m.toNat : ℕ) : ZMod q) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0]
  have hlt : m.toNat < q := by omega
  change ((m : ZMod q).val : ℤ) = m
  rw [hcast, ZMod.val_natCast_of_lt hlt, Int.toNat_of_nonneg hm0]

/-- Single-column combining map `(v, c) ↦ (w, a)` where `w = (v + c) mod P(S)` and
`a = ⌊q S⁻¹ w⌋ mod q` (MR07 Lemma 5.8, p. 21). -/
noncomputable def combineColumn {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) (q : ℕ)
    (v : SublatticeQuot B S) (c : GridRep B q) : GridRep S q × (Fin n → ZMod q) :=
  if h : S.det ≠ 0 ∧ 0 < q then
    let w := mkGridRep S h.1 q h.2 (v.toVec + c.toVec)
      (Submodule.add_mem _ (intLattice_le_gridLattice h.2 B v.mem_intLattice)
        ((mem_gridLattice_iff _).2 ⟨c.1, rfl⟩))
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
      (Submodule.add_mem _ (intLattice_le_gridLattice h.2 B v.mem_intLattice)
        ((mem_gridLattice_iff _).2 ⟨c.1, rfl⟩))
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
  rw [combineColumn_snd_eq hS hq]
  exact gridRepToZMod_val hS hq _ k

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
  unfold combineOutput
  dsimp only
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (z j) ?_) ?_
  · have hsub : (C j).toVec - (combineColumn B S q (V j) (C j)).1.toVec =
        ((V j).toVec + (C j).toVec - modParallelepiped S ((V j).toVec + (C j).toVec)) -
          (V j).toVec := by
      rw [combineColumn_fst_toVec hS hq]
      abel
    rw [hsub]
    exact Submodule.sub_mem _ (hSB (sub_modParallelepiped_mem hS _)) (V j).mem_intLattice
  · exact hSB ((mem_intLattice_iff S _).2 ⟨_, rfl⟩)

private theorem SublatticeQuot.ext_toVec {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    {v₁ v₂ : SublatticeQuot B S} (h : v₁.toVec = v₂.toVec) : v₁ = v₂ := by
  apply Subtype.ext
  funext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) h
  exact Int.cast_injective hi

private theorem combineColumn_fst_bijective {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (q : ℕ) (hq : 0 < q) :
    Function.Bijective
      (fun p : SublatticeQuot B S × GridRep B q => (combineColumn B S q p.1 p.2).1) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨v₁, c₁⟩ ⟨v₂, c₂⟩ h
    dsimp only at h
    have hvec : modParallelepiped S (v₁.toVec + c₁.toVec) =
        modParallelepiped S (v₂.toVec + c₂.toVec) := by
      rw [← combineColumn_fst_toVec hS hq, ← combineColumn_fst_toVec hS hq, h]
    have hSdiff : (v₁.toVec + c₁.toVec) - (v₂.toVec + c₂.toVec) ∈ intLattice S :=
      (modParallelepiped_eq_iff_sub_mem hS _ _).1 hvec
    have hc_diff : c₁.toVec - c₂.toVec ∈ intLattice B := by
      have heq : c₁.toVec - c₂.toVec =
          ((v₁.toVec + c₁.toVec) - (v₂.toVec + c₂.toVec)) - (v₁.toVec - v₂.toVec) := by abel
      rw [heq]
      exact Submodule.sub_mem _ (hSB hSdiff)
        (Submodule.sub_mem _ v₁.mem_intLattice v₂.mem_intLattice)
    have hc_eq : c₁ = c₂ := GridRep.ext_toVec hq <| by
      rw [← c₁.modParallelepiped_toVec, ← c₂.modParallelepiped_toVec]
      exact (modParallelepiped_eq_iff_sub_mem hB _ _).2 hc_diff
    subst hc_eq
    have hv_diff : v₁.toVec - v₂.toVec ∈ intLattice S := by
      simpa [add_sub_add_right_eq_sub] using hSdiff
    have hv_eq : v₁ = v₂ := SublatticeQuot.ext_toVec <| by
      rw [← v₁.modParallelepiped_toVec, ← v₂.modParallelepiped_toVec]
      exact (modParallelepiped_eq_iff_sub_mem hS _ _).2 hv_diff
    exact Prod.ext hv_eq rfl
  · rw [Fintype.card_prod, card_sublatticeQuot hB hS hSB, card_gridRep hB hq, card_gridRep hS hq]
    have hdvd : B.det ∣ S.det :=
      ⟨(sublatticeMat B S hSB).det, by rw [← Matrix.det_mul, mul_sublatticeMat]⟩
    have hmul : (S.det / B.det).natAbs * B.det.natAbs = S.det.natAbs := by
      rw [← Int.natAbs_mul, Int.ediv_mul_cancel hdvd]
    calc (S.det / B.det).natAbs * (q ^ n * B.det.natAbs)
        = q ^ n * ((S.det / B.det).natAbs * B.det.natAbs) := by ring
      _ = q ^ n * S.det.natAbs := by rw [hmul]

private theorem map_gridRepToZMod_uniform {n q : ℕ} [NeZero q] (S : Matrix (Fin n) (Fin n) ℤ)
    (hS : S.det ≠ 0) :
    (PMF.uniformOfFintype (GridRep S q)).map (gridRepToZMod S q) =
      PMF.uniformOfFintype (Fin n → ZMod q) := by
  classical
  have hq : 0 < q := NeZero.pos q
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  let shiftVec : (Fin n → ZMod q) → EuclideanSpace ℝ (Fin n) := fun b =>
    ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => ((S *ᵥ fun k => ((b k).val : ℤ)) i : ℝ))
  have hshiftVec_mem : ∀ b, shiftVec b ∈ gridLattice n q := fun b =>
    (mem_gridLattice_iff _).2 ⟨_, rfl⟩
  let shift : (Fin n → ZMod q) → GridRep S q → GridRep S q := fun b w =>
    mkGridRep S hS q hq (w.toVec + shiftVec b)
      (Submodule.add_mem _ ((mem_gridLattice_iff _).2 ⟨w.1, rfl⟩) (hshiftVec_mem b))
  have hshift_inv : ∀ b w, shift (-b) (shift b w) = w := fun b w => by
    have hvec : (shift (-b) (shift b w)).toVec = w.toVec := by
      simp only [shift, mkGridRep_toVec]
      conv_rhs => rw [← w.modParallelepiped_toVec]
      rw [modParallelepiped_eq_iff_sub_mem hS]
      have hsum_mem : shiftVec b + shiftVec (-b) ∈ intLattice S := by
        have hdvd : ∀ k : Fin n, (q : ℤ) ∣ (((b k).val : ℤ) + (((-b) k).val : ℤ)) := fun k => by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast
          simp
        rw [mem_intLattice_iff]
        refine ⟨fun k => (((b k).val : ℤ) + (((-b) k).val : ℤ)) / (q : ℤ), ?_⟩
        ext i
        have hqmul : (S *ᵥ fun k => (((b k).val : ℤ) + (((-b) k).val : ℤ))) i =
            (q : ℤ) * (S *ᵥ fun k => (((b k).val : ℤ) + (((-b) k).val : ℤ)) / (q : ℤ)) i := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← mul_left_comm, Int.mul_ediv_cancel' (hdvd k)]
        simp only [shiftVec, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        have h1 : (q : ℝ)⁻¹ * ((S *ᵥ fun k => ((b k).val : ℤ)) i : ℝ) +
            (q : ℝ)⁻¹ * ((S *ᵥ fun k => (((-b) k).val : ℤ)) i : ℝ) =
            (q : ℝ)⁻¹ * ((S *ᵥ fun k => (((b k).val : ℤ) + (((-b) k).val : ℤ))) i : ℝ) := by
          rw [← mul_add]
          congr 1
          have : (S *ᵥ fun k => ((b k).val : ℤ)) i + (S *ᵥ fun k => (((-b) k).val : ℤ)) i =
              (S *ᵥ fun k => (((b k).val : ℤ) + (((-b) k).val : ℤ))) i := by
            change ((S *ᵥ fun k => ((b k).val : ℤ)) + (S *ᵥ fun k => (((-b) k).val : ℤ))) i = _
            rw [← Matrix.mulVec_add]; rfl
          exact_mod_cast this
        rw [h1, show ((S *ᵥ fun k => (((b k).val : ℤ) + (((-b) k).val : ℤ))) i : ℝ) =
            (q : ℝ) * ((S *ᵥ fun k => (((b k).val : ℤ) + (((-b) k).val : ℤ)) / (q : ℤ)) i : ℝ) by
            exact_mod_cast hqmul]
        field_simp [hq0]
      have hdecomp : (modParallelepiped S (w.toVec + shiftVec b) + shiftVec (-b)) - w.toVec =
          (shiftVec b + shiftVec (-b)) -
            ((w.toVec + shiftVec b) - modParallelepiped S (w.toVec + shiftVec b)) := by abel
      rw [hdecomp]
      exact Submodule.sub_mem _ hsum_mem (sub_modParallelepiped_mem hS _)
    apply Subtype.ext
    funext i
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) hvec
    simp only [GridRep.toVec, PiLp.smul_apply, smul_eq_mul] at hi
    exact_mod_cast (mul_right_inj' (inv_ne_zero hq0)).1 hi
  have hshift_a : ∀ b w, gridRepToZMod S q (shift b w) = gridRepToZMod S q w + b := fun b w => by
    funext k
    have hinv_b : (matR S)⁻¹ *ᵥ WithLp.ofLp (shiftVec b) = fun j => ((b j).val : ℝ) / (q : ℝ) := by
      have hSb : WithLp.ofLp (shiftVec b) = matR S *ᵥ fun j => ((b j).val : ℝ) / (q : ℝ) := by
        funext i
        simp only [shiftVec, matR, Matrix.mulVec, dotProduct, Matrix.map_apply,
          PiLp.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hSb, Matrix.mulVec_mulVec, matR_inv_mul hS, Matrix.one_mulVec]
    have hinv_w : (matR S)⁻¹ *ᵥ WithLp.ofLp (shift b w).toVec =
        fun j => (((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) j + ((b j).val : ℝ) / (q : ℝ)) -
          (Int.floor (((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) j + ((b j).val : ℝ) / (q : ℝ)) : ℝ) := by
      have hto : (shift b w).toVec = modParallelepiped S (w.toVec + shiftVec b) :=
        mkGridRep_toVec S hS q hq _ _
      rw [hto]
      have hadd : (matR S)⁻¹ *ᵥ WithLp.ofLp (w.toVec + shiftVec b) =
          fun j => ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) j + ((b j).val : ℝ) / (q : ℝ) := by
        change (matR S)⁻¹ *ᵥ (WithLp.ofLp w.toVec + WithLp.ofLp (shiftVec b)) = _
        rw [Matrix.mulVec_add, hinv_b]
        rfl
      simp only [modParallelepiped, Matrix.mulVec_mulVec, matR_inv_mul hS, Matrix.one_mulVec, hadd]
    simp only [gridRepToZMod, Pi.add_apply, hinv_w]
    set ξ := ((matR S)⁻¹ *ᵥ WithLp.ofLp w.toVec) k
    set m := Int.floor (ξ + ((b k).val : ℝ) / (q : ℝ))
    have hmul : (q : ℝ) * (ξ + ((b k).val : ℝ) / (q : ℝ) - (m : ℝ)) =
        (q : ℝ) * ξ + ((b k).val : ℤ) - ((q : ℤ) * m : ℤ) := by
      push_cast
      field_simp [hq0]
    rw [hmul, Int.floor_sub_intCast, Int.floor_add_intCast]
    push_cast
    simp
  refine Cslib.Probability.PMF.uniformOfFintype_map_of_shift fun c =>
    ⟨{ toFun := shift c
       invFun := shift (-c)
       left_inv := hshift_inv c
       right_inv := fun w => by simpa [neg_neg] using hshift_inv (-c) w },
     hshift_a c⟩

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
    have hfun : (fun p : SublatticeQuot B S × GridRep B q => (combineColumn B S q p.1 p.2).2) =
        gridRepToZMod S q ∘ (fun p => (combineColumn B S q p.1 p.2).1) := by
      funext p
      exact combineColumn_snd_eq hS hq p.1 p.2
    rw [hfun, ← PMF.map_comp]
    let e := Equiv.ofBijective _ (combineColumn_fst_bijective B S hB hS hSB q hq)
    change ((PMF.uniformOfFintype _).map e).map (gridRepToZMod S q) = _
    rw [Cslib.Probability.PMF.uniformOfFintype_map_equiv e, map_gridRepToZMod_uniform S hS]
  let eVC : (Fin m → GridRep B q) × (Fin m → SublatticeQuot B S) ≃
      (Fin m → SublatticeQuot B S × GridRep B q) := {
    toFun := fun p j => (p.2 j, p.1 j)
    invFun := fun f => (fun j => (f j).2, fun j => (f j).1)
    left_inv := fun ⟨_, _⟩ => rfl
    right_inv := fun _ => rfl
  }
  let eMat : (Fin m → Fin n → ZMod q) ≃ Matrix (Fin n) (Fin m) (ZMod q) := {
    toFun := fun cols i j => cols j i
    invFun := fun A j i => A i j
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  have hlhs : (PMF.uniformOfFintype (Fin m → GridRep B q)).bind
      (fun C => (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).map
        (fun V => combineMatrix B S q V C)) =
      ((PMF.uniformOfFintype (Fin m → SublatticeQuot B S × GridRep B q)).map
        (fun f j => (combineColumn B S q (f j).1 (f j).2).2)).map eMat := by
    rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv eVC, PMF.map_comp, PMF.map_comp,
      ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
    refine congrArg (PMF.bind _) (funext fun C => ?_)
    rw [PMF.map_comp]
    rfl
  rw [hlhs, ← Cslib.Probability.PMF.pi_uniformOfFintype]
  have hpi : (Cslib.Probability.PMF.pi fun _ : Fin m =>
        PMF.uniformOfFintype (SublatticeQuot B S × GridRep B q)).map
      (fun f j => (combineColumn B S q (f j).1 (f j).2).2) =
      Cslib.Probability.PMF.pi fun _ : Fin m =>
        (PMF.uniformOfFintype (SublatticeQuot B S × GridRep B q)).map
          (fun p => (combineColumn B S q p.1 p.2).2) :=
    (Cslib.Probability.PMF.pi_map
      (p := fun _ : Fin m => PMF.uniformOfFintype (SublatticeQuot B S × GridRep B q))
      (f := fun _ (p : SublatticeQuot B S × GridRep B q) => (combineColumn B S q p.1 p.2).2)).symm
  rw [hpi]
  simp_rw [hcol]
  rw [Cslib.Probability.PMF.pi_uniformOfFintype,
    Cslib.Probability.PMF.uniformOfFintype_map_equiv eMat]

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
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  let W := fun j => (combineColumn B S q (V j) (C j)).1
  let A_int : Matrix (Fin n) (Fin m) ℤ :=
    fun i j => (((combineColumn B S q (V j) (C j)).2 i).val : ℤ)
  have hdvd : ∀ k : Fin n, (q : ℤ) ∣ (A_int *ᵥ z) k := fun k => by
    have : NeZero q := ⟨hq.ne'⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hk := congrFun hker k
    simpa [A_int, combineMatrix, Matrix.mulVec, dotProduct, ZMod.natCast_zmod_val] using hk
  let u : Fin m → Fin n → ℝ := fun j k =>
    (q : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp (W j).toVec) k
  let frac : Fin m → Fin n → ℝ := fun j k => u j k - (Int.floor (u j k) : ℝ)
  have hA_eq : ∀ k j, (A_int k j : ℝ) = (Int.floor (u j k) : ℝ) := fun k j => by
    dsimp only [A_int, u]
    rw [combineColumn_snd_eq hS hq]
    exact_mod_cast gridRepToZMod_val hS hq (W j) k
  have hdiff : combineOutput B S q V C z - ∑ j : Fin m, z j • (C j).toVec =
      (-((q : ℝ)⁻¹)) • ∑ k : Fin n, (∑ j : Fin m, (z j : ℝ) * frac j k) • intCol S k := by
    ext i
    have hdiv : ∀ k : Fin n, (((A_int *ᵥ z) k / (q : ℤ) : ℤ) : ℝ) =
        ((A_int *ᵥ z) k : ℝ) / (q : ℝ) := fun k => by
      have hmul : ((q : ℤ) * ((A_int *ᵥ z) k / (q : ℤ)) : ℤ) = (A_int *ᵥ z) k :=
        Int.mul_ediv_cancel' (hdvd k)
      have hmulR : (q : ℝ) * (((A_int *ᵥ z) k / (q : ℤ) : ℤ) : ℝ) = ((A_int *ᵥ z) k : ℝ) := by
        exact_mod_cast hmul
      exact eq_div_of_mul_eq hq0 (by linarith)
    have hW_repr : ∀ j : Fin m, (W j).toVec i =
        (q : ℝ)⁻¹ * ∑ k : Fin n, (S i k : ℝ) * u j k := fun j => by
      have hSinv : WithLp.ofLp (W j).toVec = matR S *ᵥ ((matR S)⁻¹ *ᵥ WithLp.ofLp (W j).toVec) := by
        rw [Matrix.mulVec_mulVec, matR_mul_inv hS, Matrix.one_mulVec]
      have hi : (W j).toVec i =
          ∑ k : Fin n, (S i k : ℝ) * ((matR S)⁻¹ *ᵥ WithLp.ofLp (W j).toVec) k :=
        congrFun hSinv i
      rw [hi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [u]
      field_simp [hq0]
    have hlhs : (combineOutput B S q V C z - ∑ j : Fin m, z j • (C j).toVec) i =
        -(∑ j : Fin m, (z j : ℝ) * (W j).toVec i) +
          ∑ k : Fin n, (S i k : ℝ) * (((A_int *ᵥ z) k : ℝ) / (q : ℝ)) := by
      unfold combineOutput
      dsimp only
      simp only [PiLp.sub_apply, PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply,
        PiLp.smul_apply, zsmul_eq_mul]
      have hterm2 : ((S *ᵥ fun k => (A_int *ᵥ z) k / (q : ℤ)) i : ℝ) =
          ∑ k : Fin n, (S i k : ℝ) * (((A_int *ᵥ z) k : ℝ) / (q : ℝ)) := by
        rw [Matrix.mulVec, dotProduct]
        simp only [Int.cast_sum, Int.cast_mul]
        refine Finset.sum_congr rfl fun k _ => by rw [hdiv k]
      change (∑ j : Fin m, (z j : ℝ) * ((C j).toVec i - (W j).toVec i)) +
          ((S *ᵥ fun k => (A_int *ᵥ z) k / (q : ℤ)) i : ℝ) -
          (∑ j : Fin m, (z j : ℝ) * (C j).toVec i) = _
      rw [hterm2]
      have hsub : (∑ j : Fin m, (z j : ℝ) * ((C j).toVec i - (W j).toVec i)) -
            (∑ j : Fin m, (z j : ℝ) * (C j).toVec i) =
            -∑ j : Fin m, (z j : ℝ) * (W j).toVec i := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      linarith
    rw [hlhs]
    simp_rw [hW_repr]
    simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, intCol, frac]
    have hA_expand : ∑ k : Fin n, (S i k : ℝ) * (((A_int *ᵥ z) k : ℝ) / (q : ℝ)) =
        (q : ℝ)⁻¹ * ∑ k : Fin n, ∑ j : Fin m,
          (S i k : ℝ) * ((z j : ℝ) * (Int.floor (u j k) : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, hA_eq]
      rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hA_expand]
    have hW_expand : ∑ j : Fin m, (z j : ℝ) * ((q : ℝ)⁻¹ * ∑ k : Fin n, (S i k : ℝ) * u j k) =
        (q : ℝ)⁻¹ * ∑ k : Fin n, ∑ j : Fin m, (S i k : ℝ) * ((z j : ℝ) * u j k) := by
      calc ∑ j : Fin m, (z j : ℝ) * ((q : ℝ)⁻¹ * ∑ k : Fin n, (S i k : ℝ) * u j k)
          = ∑ j : Fin m, ∑ k : Fin n, (q : ℝ)⁻¹ * ((S i k : ℝ) * ((z j : ℝ) * u j k)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by ring
        _ = ∑ k : Fin n, ∑ j : Fin m, (q : ℝ)⁻¹ * ((S i k : ℝ) * ((z j : ℝ) * u j k)) :=
            Finset.sum_comm
        _ = (q : ℝ)⁻¹ * ∑ k : Fin n, ∑ j : Fin m, (S i k : ℝ) * ((z j : ℝ) * u j k) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    rw [hW_expand]
    calc -((q : ℝ)⁻¹ * ∑ k : Fin n, ∑ j : Fin m, (S i k : ℝ) * ((z j : ℝ) * u j k)) +
          (q : ℝ)⁻¹ * ∑ k : Fin n, ∑ j : Fin m, (S i k : ℝ) * ((z j : ℝ) * (Int.floor (u j k) : ℝ))
        = (-(q : ℝ)⁻¹) * ((∑ k : Fin n, ∑ j : Fin m, (S i k : ℝ) * ((z j : ℝ) * u j k)) -
            (∑ k : Fin n, ∑ j : Fin m, (S i k : ℝ) * ((z j : ℝ) * (Int.floor (u j k) : ℝ)))) := by
          ring
      _ = (-(q : ℝ)⁻¹) * ∑ k : Fin n, (∑ j : Fin m, (z j : ℝ) * (u j k - (Int.floor (u j k) : ℝ))) *
            (S i k : ℝ) := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_sub_distrib, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by ring
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (inv_nonneg.mpr hqpos.le)]
  have hL1_le : ∑ j : Fin m, |(z j : ℝ)| ≤ Real.sqrt m * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖ := by
    have hsq := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun j => |(z j : ℝ)|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at hsq
    have hnorm2 : ∑ j : Fin m, (z j : ℝ) ^ 2 = ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun j _ => by simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm2] at hsq
    have hrhs_sq : (m : ℝ) * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖ ^ 2 =
        (Real.sqrt m * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    rw [hrhs_sq] at hsq
    exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hsum_le : ‖∑ k : Fin n, (∑ j : Fin m, (z j : ℝ) * frac j k) • intCol S k‖ ≤
      (n : ℝ) * (Real.sqrt m * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖) * ‖intCol S‖ := by
    calc ‖∑ k : Fin n, (∑ j : Fin m, (z j : ℝ) * frac j k) • intCol S k‖
        ≤ ∑ k : Fin n, ‖(∑ j : Fin m, (z j : ℝ) * frac j k) • intCol S k‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin n, (Real.sqrt m * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖) * ‖intCol S‖ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          have hcoeff : |∑ j : Fin m, (z j : ℝ) * frac j k| ≤
              Real.sqrt m * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖ := by
            calc |∑ j : Fin m, (z j : ℝ) * frac j k|
                ≤ ∑ j : Fin m, |(z j : ℝ) * frac j k| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ j : Fin m, |(z j : ℝ)| := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  rw [abs_mul]
                  have hf0 : 0 ≤ frac j k := sub_nonneg.mpr (Int.floor_le _)
                  have hf1 : |frac j k| ≤ 1 := by
                    rw [abs_of_nonneg hf0]
                    exact (sub_lt_iff_lt_add'.mpr (Int.lt_floor_add_one _)).le
                  simpa using mul_le_mul_of_nonneg_left hf1 (abs_nonneg (z j : ℝ))
              _ ≤ Real.sqrt m * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖ := hL1_le
          exact mul_le_mul hcoeff (norm_le_pi_norm (intCol S) k) (norm_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      _ = (n : ℝ) * (Real.sqrt m * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖) * ‖intCol S‖ := by
          simp [Finset.sum_const, nsmul_eq_mul]; ring
  calc (q : ℝ)⁻¹ * ‖∑ k : Fin n, (∑ j : Fin m, (z j : ℝ) * frac j k) • intCol S k‖
      ≤ (q : ℝ)⁻¹ * ((n : ℝ) * (Real.sqrt m * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖) * ‖intCol S‖) :=
        mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hqpos.le)
    _ = Real.sqrt m * n * ‖intCol S‖ * ‖WithLp.toLp 2 (fun j => (z j : ℝ))‖ / q := by
        field_simp [hq0]


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
  rw [Finset.sum_eq_single g.1]
  · have hα : (guessAlpha g.2.1 g.2.2 : ℝ) ≠ 0 :=
      Int.cast_ne_zero.mpr (guessAlpha_ne_zero g.2.1 g.2.2)
    simp only [guessTarget, ↓reduceIte, hz, smul_smul, mul_neg, mul_inv_cancel₀ hα, neg_one_smul]
  · intro i _ hi
    simp [guessTarget, hi]
  · intro h
    exact (h (Finset.mem_univ g.1)).elim

private theorem exists_guess_of_isEll2Solution {n m q : ℕ} {A : Matrix (Fin n) (Fin m) (ZMod q)}
    {β : ℝ} (_hβ : 1 ≤ β) {z : Fin m → ℤ} (hz : SIS.IsEll2Solution A β z) :
    ∃ g : Fin m × Bool × Fin (Nat.floor β), z g.1 = guessAlpha g.2.1 g.2.2 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin m, z j ≠ 0 := by
    by_contra h
    push Not at h
    exact hz.1 (funext h)
  have hnat_pos : 1 ≤ (z j).natAbs := Int.natAbs_pos.mpr hj
  have hnat_le : (z j).natAbs ≤ Nat.floor β := by
    have h := (hz.isSolution).2.1 j
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  let idx : Fin (Nat.floor β) := ⟨(z j).natAbs - 1, by omega⟩
  refine ⟨(j, decide (0 < z j), idx), ?_⟩
  by_cases hpos : 0 < z j
  · simp only [guessAlpha, decide_eq_true hpos, ↓reduceIte, idx]
    omega
  · simp only [guessAlpha, decide_eq_false hpos, Bool.false_eq_true, ↓reduceIte, idx]
    omega

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
  split_ifs at hv with h
  · simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hv
    obtain ⟨_, _, CY, _, V, _, z, _, rfl⟩ := hv
    exact Submodule.sub_mem _
      (combineOutput_mem_intLattice B S hS hSB q (NeZero.pos q) V (fun i => (CY i).1) z)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (z i) (CY i).2.2)
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hv
    rw [hv]
    exact (intLattice B).zero_mem

/-- Monotonicity of centered lattice Gaussian mass in the width `s`: `1 / s ≤ 2 / s` implies
`ρ_{1/s}(D \ {0}) ≤ ρ_{2/s}(D \ {0})`. -/
private theorem gaussianMass_dual_one_div_le_two_div {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (D : Submodule ℤ E) [DiscreteTopology D] {s : ℝ} (hs : 0 < s) :
    gaussianMass D (1 / s) 0 - 1 ≤ gaussianMass D (2 / s) 0 - 1 := by
  have hle := ZLattice.gaussianMass_le_of_le D (one_div_pos.mpr hs)
    (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hs.le) 0
  linarith

private theorem eps_lt_one_of_le {m : ℕ} {ε : ℝ}
    (hε : ε ≤ 1 / (400 * max 1 (Real.sqrt m))) : ε < 1 := by
  have hmax1 : (1 : ℝ) ≤ max 1 (Real.sqrt m) := le_max_left _ _
  have h400 : ε ≤ 1 / 400 :=
    hε.trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 400) (by linarith))
  linarith

/-- `toMeasure` of `PMF.piFin` on a countable measurable space equals `Measure.pi`. -/
private theorem toMeasure_piFin {k : ℕ} {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] (p : Fin k → PMF α) :
    (Cslib.Probability.PMF.piFin p).toMeasure = Measure.pi (fun i => (p i).toMeasure) := by
  apply Measure.ext_of_singleton
  intro v
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    Measure.pi_singleton, Cslib.Probability.PMF.piFin_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-- Numerical constant check from MR07 Theorem 5.9 (p. 24): for `ε ≤ 1 / (400 * max 1 √m)`,
`1 / (2π) + ε / (1 - ε) + m * (ε / (1 - ε))^2 ≤ 1 / 6`. -/
private theorem mr07_variance_const_le {m : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (400 * max 1 (Real.sqrt m))) :
    1 / (2 * Real.pi) + ε / (1 - ε) + (m : ℝ) * (ε / (1 - ε)) ^ 2 ≤ 1 / 6 := by
  have hmax1 : (1 : ℝ) ≤ max 1 (Real.sqrt m) := le_max_left _ _
  have hmax_sqrt : Real.sqrt m ≤ max 1 (Real.sqrt m) := le_max_right _ _
  have hε_small : ε ≤ 1 / 400 := by
    refine hε.trans ?_
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 400) (by linarith)
  have h1mε : (399 / 400 : ℝ) ≤ 1 - ε := by linarith
  have h1mε_pos : (0 : ℝ) < 1 - ε := by linarith
  have hterm2 : ε / (1 - ε) ≤ 1 / 399 := by
    rw [div_le_iff₀ h1mε_pos]
    linarith
  have hm_sq : (m : ℝ) * ε ^ 2 ≤ 1 / 160000 := by
    have hε_sqrt : ε * Real.sqrt m ≤ 1 / 400 := by
      have hpos : (0 : ℝ) < 400 * max 1 (Real.sqrt m) := by linarith
      have hmul : ε * (400 * max 1 (Real.sqrt m)) ≤ 1 := by
        rwa [le_div_iff₀ hpos] at hε
      have h1 : ε * Real.sqrt m ≤ ε * max 1 (Real.sqrt m) :=
        mul_le_mul_of_nonneg_left hmax_sqrt hε0
      linarith
    have hsq : (ε * Real.sqrt m) ^ 2 ≤ (1 / 400 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hε0 (Real.sqrt_nonneg _)) hε_sqrt 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at hsq
    linarith
  have hterm3 : (m : ℝ) * (ε / (1 - ε)) ^ 2 ≤ 1 / 159201 := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos h1mε_pos)]
    have hsq_lo : (399 / 400 : ℝ) ^ 2 ≤ (1 - ε) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) h1mε 2
    nlinarith
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hterm1 : 1 / (2 * Real.pi) ≤ 1 / 6.28 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

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
    (hz_norm : ‖WithLp.toLp 2 (fun i => (z i : ℝ))‖ ≤ β) :
    let s : ℝ := 2 * r / (β * Real.sqrt n)
    have hs : 0 < s := by
      have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have : (0 : ℝ) < β := lt_of_lt_of_le zero_lt_one hβ
      positivity
    (1 / 3 : ℝ) ≤
      ((Cslib.Probability.PMF.piFin fun i : Fin m =>
          ZLattice.discreteGaussian (intLattice B) s hs (centers i)).toOuterMeasure
        {Y | ‖∑ i : Fin m, (z i : ℝ) •
          ((Y i : EuclideanSpace ℝ (Fin n)) - centers i)‖ ≤ r}).toReal := by
  intro s hs
  have := isZLattice_intLattice hB
  have hε1 : ε < 1 := eps_lt_one_of_le hε
  let p : Fin m → PMF (intLattice B) :=
    fun i => ZLattice.discreteGaussian (intLattice B) s hs (centers i)
  let μ : Measure (Fin m → intLattice B) := (Cslib.Probability.PMF.piFin p).toMeasure
  have hμ_eq : μ = Measure.pi (fun i => (p i).toMeasure) := toMeasure_piFin p
  have : IsProbabilityMeasure μ := by
    rw [hμ_eq]; infer_instance
  let X : Fin m → (Fin m → intLattice B) → EuclideanSpace ℝ (Fin n) :=
    fun i Y => (Y i : EuclideanSpace ℝ (Fin n)) - centers i
  have hind : iIndepFun X μ := by
    rw [hμ_eq]
    refine ProbabilityTheory.iIndepFun_pi
      (X := fun i (x : intLattice B) => (x : EuclideanSpace ℝ (Fin n)) - centers i)
      (μ := fun i => (p i).toMeasure) (fun i => ?_)
    have hcont : Continuous (fun x : intLattice B => (x : EuclideanSpace ℝ (Fin n)) - centers i) :=
      continuous_subtype_val.sub continuous_const
    exact hcont.measurable.aemeasurable
  have hmp : ∀ i : Fin m,
      MeasurePreserving (fun Y : Fin m → intLattice B => Y i) μ (p i).toMeasure :=
    fun i => by
      rw [hμ_eq]
      exact measurePreserving_eval (fun j => (p j).toMeasure) i
  have hL2 : ∀ i : Fin m, MemLp (X i) 2 μ := fun i => by
    have hbase := ZLattice.memLp_sub_discreteGaussian (intLattice B) s hs (centers i)
    exact hbase.comp_measurePreserving (hmp i)
  let l : ℝ := (1 / (2 * Real.pi) + ε / (1 - ε)) * s ^ 2 * n
  let εm : ℝ := (ε / (1 - ε)) ^ 2 * s ^ 2 * n
  have hsq : ∀ i : Fin m, ∫ Y, ‖X i Y‖ ^ 2 ∂μ ≤ l := fun i => by
    have hcont : Continuous
        (fun x : intLattice B => ‖(x : EuclideanSpace ℝ (Fin n)) - centers i‖ ^ 2) :=
      (continuous_subtype_val.sub continuous_const).norm.pow 2
    have hcomp : ∫ Y, ‖X i Y‖ ^ 2 ∂μ =
        ∫ x : intLattice B, ‖(x : EuclideanSpace ℝ (Fin n)) - centers i‖ ^ 2 ∂(p i).toMeasure := by
      rw [← (hmp i).map_eq, integral_map (measurable_pi_apply i).aemeasurable
        hcont.measurable.aestronglyMeasurable]
    rw [hcomp, ZLattice.integral_norm_sub_sq_discreteGaussian_eq_tsum]
    simpa [l, finrank_euclideanSpace_fin] using
      ZLattice.tsum_discreteGaussian_mul_norm_sub_sq_le (intLattice B) s hs (centers i) ε hε1 hdual
  have hmean : ∀ i : Fin m, ‖∫ Y, X i Y ∂μ‖ ^ 2 ≤ εm := fun i => by
    have hcont : Continuous (fun x : intLattice B => (x : EuclideanSpace ℝ (Fin n)) - centers i) :=
      continuous_subtype_val.sub continuous_const
    have hcomp : ∫ Y, X i Y ∂μ =
        ∫ x : intLattice B, ((x : EuclideanSpace ℝ (Fin n)) - centers i) ∂(p i).toMeasure := by
      rw [← (hmp i).map_eq, integral_map (measurable_pi_apply i).aemeasurable
        hcont.measurable.aestronglyMeasurable]
    rw [hcomp, ZLattice.integral_sub_discreteGaussian_eq_tsum]
    simpa [εm, finrank_euclideanSpace_fin] using
      ZLattice.norm_tsum_discreteGaussian_smul_sub_sq_le (intLattice B) s hs (centers i) ε hε1 hdual
  have hint_bound := ProbabilityTheory.integral_norm_sum_smul_sq_le_of_iIndepFun hind hL2 hsq hmean
    (fun i => (z i : ℝ))
  have hsum_z_sq : ∑ i : Fin m, (z i : ℝ) ^ 2 ≤ β ^ 2 := by
    have hnorm2 : ∑ i : Fin m, (z i : ℝ) ^ 2 = ‖WithLp.toLp 2 (fun i => (z i : ℝ))‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => by simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm2]
    exact pow_le_pow_left₀ (norm_nonneg _) hz_norm 2
  have hconst := mr07_variance_const_le (m := m) hε0 hε
  have hE_le : ∫ Y, ‖∑ i : Fin m, (z i : ℝ) • X i Y‖ ^ 2 ∂μ ≤ (2 / 3 : ℝ) * r ^ 2 := by
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hβ_pos : (0 : ℝ) < β := lt_of_lt_of_le zero_lt_one hβ
    have hs2_n : s ^ 2 * (n : ℝ) * β ^ 2 = 4 * r ^ 2 := by
      dsimp only [s]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      field_simp [hβ_pos.ne', hn_pos.ne']
      ring
    have hfactor : l + εm * Fintype.card (Fin m) =
        (1 / (2 * Real.pi) + ε / (1 - ε) + (m : ℝ) * (ε / (1 - ε)) ^ 2) * (s ^ 2 * n) := by
      simp only [l, εm, Fintype.card_fin]
      ring
    have hcoeff_nonneg : 0 ≤ 1 / (2 * Real.pi) + ε / (1 - ε) + (m : ℝ) * (ε / (1 - ε)) ^ 2 := by
      have : 0 ≤ ε / (1 - ε) := div_nonneg hε0 (by linarith)
      positivity
    calc ∫ Y, ‖∑ i : Fin m, (z i : ℝ) • X i Y‖ ^ 2 ∂μ
        ≤ (l + εm * Fintype.card (Fin m)) * ∑ i : Fin m, (z i : ℝ) ^ 2 := hint_bound
      _ ≤ ((1 / 6 : ℝ) * (s ^ 2 * n)) * β ^ 2 := by
          rw [hfactor]
          exact mul_le_mul (mul_le_mul_of_nonneg_right hconst (by positivity)) hsum_z_sq
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = (1 / 6 : ℝ) * (s ^ 2 * (n : ℝ) * β ^ 2) := by ring
      _ = (2 / 3 : ℝ) * r ^ 2 := by rw [hs2_n]; ring
  let S_good : Set (Fin m → intLattice B) :=
    {Y | ‖∑ i : Fin m, (z i : ℝ) • X i Y‖ ≤ r}
  let S_bad : Set (Fin m → intLattice B) :=
    {Y | r ^ 2 ≤ ‖∑ i : Fin m, (z i : ℝ) • X i Y‖ ^ 2}
  have hInt_sum : Integrable (fun Y => ‖∑ i : Fin m, (z i : ℝ) • X i Y‖ ^ 2) μ := by
    have hMem : MemLp (fun Y => ∑ i : Fin m, (z i : ℝ) • X i Y) 2 μ := by
      have hfin : ∀ s : Finset (Fin m),
          MemLp (fun Y => ∑ i ∈ s, (z i : ℝ) • X i Y) 2 μ := fun s => by
        classical
        induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty]; exact MemLp.zero
        | @insert a t ha ih =>
          have heq : (fun Y => ∑ i ∈ insert a t, (z i : ℝ) • X i Y) =
              (fun Y => (z a : ℝ) • X a Y) + (fun Y => ∑ i ∈ t, (z i : ℝ) • X i Y) := by
            funext Y; simp [Finset.sum_insert ha]
          rw [heq]
          exact ((hL2 a).const_smul (z a : ℝ)).add ih
      exact hfin Finset.univ
    exact (memLp_two_iff_integrable_sq_norm hMem.aestronglyMeasurable).mp hMem
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun Y => sq_nonneg ‖∑ i : Fin m, (z i : ℝ) • X i Y‖) hInt_sum (r ^ 2)
  have hbad_le : (μ S_bad).toReal ≤ 2 / 3 := by
    have h1 : r ^ 2 * (μ S_bad).toReal ≤ (2 / 3 : ℝ) * r ^ 2 := hmarkov.trans hE_le
    nlinarith [sq_pos_of_pos hr]
  have hcompl_sub : S_goodᶜ ⊆ S_bad := fun Y hY => by
    have hgt : r < ‖∑ i : Fin m, (z i : ℝ) • X i Y‖ := not_le.mp hY
    exact (pow_le_pow_left₀ hr.le hgt.le 2)
  have hgood_meas : MeasurableSet S_good := Set.to_countable S_good |>.measurableSet
  have htoM : (Cslib.Probability.PMF.piFin p).toOuterMeasure S_good = μ S_good :=
    (PMF.toMeasure_apply_eq_toOuterMeasure_apply (Cslib.Probability.PMF.piFin p) hgood_meas).symm
  rw [htoM]
  have hadd : (μ S_good).toReal + (μ S_goodᶜ).toReal = 1 := by
    have hsum := measure_add_measure_compl hgood_meas (μ := μ)
    rw [measure_univ] at hsum
    have htoR := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), ENNReal.toReal_one] at htoR
    exact htoR
  have hcompl_le : (μ S_goodᶜ).toReal ≤ (μ S_bad).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hcompl_sub)
  linarith

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
  have := isZLattice_intLattice hB
  have hq_pos : 0 < q := NeZero.pos q
  have hqR_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq_pos
  have hε1 : ε < 1 := eps_lt_one_of_le hε
  have hK_pos : 0 < Nat.floor β := Nat.floor_pos.mpr hβ
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nonempty (Fin (Nat.floor β)) := ⟨⟨0, hK_pos⟩⟩
  let s : ℝ := 2 * r / (β * Real.sqrt n)
  have hs : 0 < s := by
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le zero_lt_one hβ
    positivity
  have hdual_s : gaussianMass (LinearMap.BilinForm.dualSubmodule
      (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B)) (1 / s) 0 - 1 ≤ ε := by
    have : DiscreteTopology
        (LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B)) :=
      discreteTopology_dualSubmodule (intLattice B)
    exact (gaussianMass_dual_one_div_le_two_div _ hs).trans hdual
  let E_sol : Set (EuclideanSpace ℝ (Fin n)) :=
    {v | IncGDD.IsSolution g (intLattice B) (intColCast B S hB) t r v}
  let Guess := Fin m × Bool × Fin (Nat.floor β)
  let pC : Guess → PMF (Fin m → GridRep B q) := fun g =>
    Cslib.Probability.PMF.piFin fun i : Fin m =>
      (idealGridSample B hB q hq_pos s hs (guessTarget t g i)).map Prod.fst
  let pY : Guess → (Fin m → GridRep B q) → PMF (Fin m → intLattice B) := fun g C =>
    Cslib.Probability.PMF.piFin fun i : Fin m =>
      ZLattice.discreteGaussian (intLattice B) s hs (guessTarget t g i + (C i).toVec)
  -- Factor `idealIncGDDStep` via `idealGridSample_eq_bind_discreteGaussian` and `piFin`
  have hstep_eq : idealIncGDDStep B S hB β r hβ hr t F =
      (PMF.uniformOfFintype Guess).bind fun gu =>
        (pC gu).bind fun C =>
          (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
            (ProbComp.eval (F (combineMatrix B S q V C))).bind fun z =>
              (pY gu C).map fun Y =>
                combineOutput B S q V C z -
                  ∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n)) := by
    unfold idealIncGDDStep
    have hnm : 1 ≤ n ∧ 1 ≤ m := ⟨hn, hm⟩
    simp only [hnm]
    refine congrArg (PMF.bind (PMF.uniformOfFintype Guess)) (funext fun gu => ?_)
    have hpi : (Cslib.Probability.PMF.piFin fun i : Fin m =>
          idealGridSample B hB q hq_pos s hs (guessTarget t gu i)) =
        (pC gu).bind fun C => (pY gu C).map fun Y i => (C i, Y i) := by
      have hcoord : (fun i : Fin m => idealGridSample B hB q hq_pos s hs (guessTarget t gu i)) =
          fun i : Fin m =>
            ((idealGridSample B hB q hq_pos s hs (guessTarget t gu i)).map Prod.fst).bind fun c =>
              (ZLattice.discreteGaussian (intLattice B) s hs (guessTarget t gu i + c.toVec)).map
                fun y => (c, y) :=
        funext fun i =>
          idealGridSample_eq_bind_discreteGaussian B hB q hq_pos s hs (guessTarget t gu i)
      rw [hcoord, ← Cslib.Probability.PMF.piFin_bind]
      refine congrArg (PMF.bind (pC gu)) (funext fun C => ?_)
      exact Cslib.Probability.PMF.piFin_map
        (fun i => ZLattice.discreteGaussian (intLattice B) s hs (guessTarget t gu i + (C i).toVec))
        (fun i y => (C i, y))
    change ((Cslib.Probability.PMF.piFin fun i : Fin m =>
        idealGridSample B hB q hq_pos s hs (guessTarget t gu i)).bind _) = _
    rw [hpi, PMF.bind_bind]
    refine congrArg (PMF.bind (pC gu)) (funext fun C => ?_)
    rw [PMF.bind_map]
    -- Commute independent draws `Y` with `(V, z)`
    change (pY gu C).bind (fun Y =>
        (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
          (ProbComp.eval (F (combineMatrix B S q V C))).bind fun z =>
            PMF.pure (combineOutput B S q V C z -
              ∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n)))) =
      (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
        (ProbComp.eval (F (combineMatrix B S q V C))).bind fun z =>
          (pY gu C).bind fun Y =>
            PMF.pure (combineOutput B S q V C z -
              ∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n)))
    rw [PMF.bind_comm (pY gu C) (PMF.uniformOfFintype (Fin m → SublatticeQuot B S))]
    refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)))
      (funext fun V => ?_)
    rw [PMF.bind_comm (pY gu C) (ProbComp.eval (F (combineMatrix B S q V C)))]
  -- Good event on `(gu, C, V, z)`
  let Good (gu : Guess) (C : Fin m → GridRep B q) (V : Fin m → SublatticeQuot B S)
      (z : Fin m → ℤ) : Prop :=
    SIS.IsEll2Solution (combineMatrix B S q V C) β z ∧ z gu.1 = guessAlpha gu.2.1 gu.2.2
  -- Conditional success probability ≥ 1/3 whenever `Good gu C V z` holds
  have hcond : ∀ gu C V z, Good gu C V z →
      ENNReal.ofReal (1 / 3 : ℝ) ≤
        ((pY gu C).map fun Y =>
          combineOutput B S q V C z -
            ∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n))).toOuterMeasure E_sol := by
    intro gu C V z ⟨hsis, hzg⟩
    rw [PMF.toOuterMeasure_map_apply]
    let S_ok : Set (Fin m → intLattice B) :=
      {Y | ‖∑ i : Fin m, (z i : ℝ) •
        ((Y i : EuclideanSpace ℝ (Fin n)) - (guessTarget t gu i + (C i).toVec))‖ ≤ r}
    have hsub : S_ok ⊆ (fun Y => combineOutput B S q V C z -
        ∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n))) ⁻¹' E_sol := by
      intro Y hY
      refine ⟨Submodule.sub_mem _
        (combineOutput_mem_intLattice B S hS hSB q hq_pos V C z)
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (z i) (Y i).2), ?_⟩
      have hcomb :=
        (combineOutput_mem_intLattice_and_norm_sub_le hq_pos B S hS hSB V C z hsis.2.2).2
      have hT : ∑ i : Fin m, (z i : ℝ) • guessTarget t gu i = -t :=
        sum_smul_guessTarget_eq_neg t gu z hzg
      have hdecomp : (combineOutput B S q V C z -
            ∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n))) - t =
          (combineOutput B S q V C z - ∑ i : Fin m, z i • (C i).toVec) -
            ∑ i : Fin m, (z i : ℝ) •
              ((Y i : EuclideanSpace ℝ (Fin n)) - (guessTarget t gu i + (C i).toVec)) := by
        have hsum_eq : ∑ i : Fin m, (z i : ℝ) •
              ((Y i : EuclideanSpace ℝ (Fin n)) - (guessTarget t gu i + (C i).toVec)) =
            (∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n))) -
              (∑ i : Fin m, (z i : ℝ) • guessTarget t gu i) -
              (∑ i : Fin m, z i • (C i).toVec) := by
          simp_rw [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Int.cast_smul_eq_zsmul]
          abel
        rw [hsum_eq, hT]
        abel
      have hcomb_le : ‖combineOutput B S q V C z - ∑ i : Fin m, z i • (C i).toVec‖ ≤
          ‖intColCast B S hB‖ / g := by
        rw [norm_intColCast]
        have h1 : Real.sqrt m * n * ‖intCol S‖ * ‖WithLp.toLp 2 (fun i => (z i : ℝ))‖ / q ≤
            Real.sqrt m * n * ‖intCol S‖ * β / q := by
          gcongr
          exact hsis.2.1
        refine hcomb.trans (h1.trans ?_)
        rw [div_le_div_iff₀ hqR_pos hg]
        have hmul : (Real.sqrt m * n * β * g) * ‖intCol S‖ ≤ (q : ℝ) * ‖intCol S‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        linarith
      calc ‖(combineOutput B S q V C z - ∑ i : Fin m, z i • (Y i : EuclideanSpace ℝ (Fin n))) - t‖
          = ‖(combineOutput B S q V C z - ∑ i : Fin m, z i • (C i).toVec) -
              ∑ i : Fin m, (z i : ℝ) •
                ((Y i : EuclideanSpace ℝ (Fin n)) - (guessTarget t gu i + (C i).toVec))‖ := by
            rw [hdecomp]
        _ ≤ ‖combineOutput B S q V C z - ∑ i : Fin m, z i • (C i).toVec‖ +
              ‖∑ i : Fin m, (z i : ℝ) •
                ((Y i : EuclideanSpace ℝ (Fin n)) - (guessTarget t gu i + (C i).toVec))‖ :=
            norm_sub_le _ _
        _ ≤ ‖intColCast B S hB‖ / g + r := add_le_add hcomb_le hY
    have hprob := cond_gaussian_sum_le_prob_ge_one_third hn B hB hβ hr hε0 hε hdual
      (fun i => guessTarget t gu i + (C i).toVec) z hsis.2.1
    have hprob_enn : ENNReal.ofReal (1 / 3 : ℝ) ≤ (pY gu C).toOuterMeasure S_ok := by
      rw [← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal hprob
    exact hprob_enn.trans ((pY gu C).toOuterMeasure.mono hsub)
  -- Lower bound on the joint real `(gu, C, V, z)` probability of `Good`
  let realJoint : PMF
      (Guess × (Fin m → GridRep B q) × (Fin m → SublatticeQuot B S) × (Fin m → ℤ)) :=
    (PMF.uniformOfFintype Guess).bind fun gu =>
      (pC gu).bind fun C =>
        (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
          (ProbComp.eval (F (combineMatrix B S q V C))).map fun z => (gu, C, V, z)
  let idealJoint : PMF
      (Guess × (Fin m → GridRep B q) × (Fin m → SublatticeQuot B S) × (Fin m → ℤ)) :=
    (PMF.uniformOfFintype Guess).bind fun gu =>
      (PMF.uniformOfFintype (Fin m → GridRep B q)).bind fun C =>
        (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
          (ProbComp.eval (F (combineMatrix B S q V C))).map fun z => (gu, C, V, z)
  let E_good : Set (Guess × (Fin m → GridRep B q) × (Fin m → SublatticeQuot B S) × (Fin m → ℤ)) :=
    {x | Good x.1 x.2.1 x.2.2.1 x.2.2.2}
  -- Step 1: `CloseTo realJoint idealJoint (m * ε / (2 * (1 - ε)))`
  have hclose_joint : CloseTo realJoint idealJoint (ENNReal.ofReal (m * ε / (2 * (1 - ε)))) := by
    have hclose_C : ∀ gu : Guess,
        CloseTo (pC gu) (PMF.uniformOfFintype (Fin m → GridRep B q))
          (ENNReal.ofReal (m * ε / (2 * (1 - ε)))) := fun gu => by
      have h1 := CloseTo.piFin (p := fun i : Fin m =>
          (idealGridSample B hB q hq_pos s hs (guessTarget t gu i)).map Prod.fst)
        (q := fun _ : Fin m => PMF.uniformOfFintype (GridRep B q))
        (fun i =>
          idealGridSample_fst_closeTo_uniform B hB q hq_pos hs hε0 hε1 hdual_s
            (guessTarget t gu i))
      have hpi_unif : Cslib.Probability.PMF.piFin
          (fun _ : Fin m => PMF.uniformOfFintype (GridRep B q)) =
          PMF.uniformOfFintype (Fin m → GridRep B q) :=
        (Cslib.Probability.PMF.piFin_const _ m).trans
          (Cslib.Probability.PMF.iid_uniformOfFintype m)
      rw [hpi_unif] at h1
      have hmul_eq : (m : ℝ≥0∞) * ENNReal.ofReal (ε / (2 * (1 - ε))) =
          ENNReal.ofReal (m * ε / (2 * (1 - ε))) := by
        rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (Nat.cast_nonneg m), mul_div_assoc]
      rwa [hmul_eq] at h1
    refine CloseTo.bind_right (PMF.uniformOfFintype Guess) fun gu _ => ?_
    exact (hclose_C gu).bind_left _
  -- Step 2: `idealJoint.toOuterMeasure E_good ≥ sisEll2Advantage / (2 * ⌊β⌋ * m)`
  have hideal_ge : (sisEll2Advantage q β F : ℝ) / (2 * (Nat.floor β : ℝ) * m) ≤
      (idealJoint.toOuterMeasure E_good).toReal := by
    let pAZ : PMF (Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ℤ)) :=
      (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
        (ProbComp.eval (F A)).map fun z => (A, z)
    have hmap_AZ : idealJoint.map (fun x => (x.1, combineMatrix B S q x.2.2.1 x.2.1, x.2.2.2)) =
        (PMF.uniformOfFintype Guess).bind fun gu => pAZ.map fun p => (gu, p.1, p.2) := by
      simp only [idealJoint, pAZ, PMF.map_bind]
      refine congrArg (PMF.bind (PMF.uniformOfFintype Guess)) (funext fun gu => ?_)
      have hcomb := idealCombine_matrix_eq_uniform (m := m) (q := q) B S hB hS hSB
      rw [← hcomb, PMF.bind_bind]
      refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin m → GridRep B q))) (funext fun C => ?_)
      rw [PMF.bind_map]
      refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)))
        (funext fun V => ?_)
      change ((ProbComp.eval (F (combineMatrix B S q V C))).map fun z => (gu, C, V, z)).map
          (fun x => (x.1, combineMatrix B S q x.2.2.1 x.2.1, x.2.2.2)) =
        ((ProbComp.eval (F (combineMatrix B S q V C))).map
          fun z => (combineMatrix B S q V C, z)).map
          fun p => (gu, p.1, p.2)
      rw [PMF.map_comp, PMF.map_comp]
      rfl
    let E_AZ : Set (Guess × Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ℤ)) :=
      {x | SIS.IsEll2Solution x.2.1 β x.2.2 ∧ x.2.2 x.1.1 = guessAlpha x.1.2.1 x.1.2.2}
    have hmeas_eq : idealJoint.toOuterMeasure E_good =
        ((PMF.uniformOfFintype Guess).bind
          fun gu => pAZ.map fun p => (gu, p.1, p.2)).toOuterMeasure E_AZ := by
      rw [← hmap_AZ, PMF.toOuterMeasure_map_apply]
      rfl
    have hcardG : (Fintype.card Guess : ℝ) = 2 * (Nat.floor β : ℝ) * m := by
      simp only [Guess, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      push_cast
      ring
    have hadv_eq : (sisEll2Advantage q β F : ℝ) =
        (pAZ.toOuterMeasure {p | SIS.IsEll2Solution p.1 β p.2}).toReal := by
      classical
      unfold sisEll2Advantage sisEll2Experiment Game.succProbability
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform]
      change (((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
          (ProbComp.eval (F A)).bind fun z =>
            PMF.pure (decide (SIS.IsEll2Solution A β z))) true).toReal =
        (pAZ.toOuterMeasure {p | SIS.IsEll2Solution p.1 β p.2}).toReal
      congr 1
      rw [PMF.toOuterMeasure_bind_apply
          (p := PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))),
        PMF.bind_apply]
      refine tsum_congr fun A => ?_
      rw [PMF.toOuterMeasure_map_apply, PMF.bind_apply, PMF.toOuterMeasure_apply]
      congr 1
      refine tsum_congr fun z => ?_
      by_cases h : SIS.IsEll2Solution A β z
      · simp [h]
      · simp [h]
    let S_p (p : Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ℤ)) : Set Guess :=
      {gu | SIS.IsEll2Solution p.1 β p.2 ∧ p.2 gu.1 = guessAlpha gu.2.1 gu.2.2}
    have hpoint : ∀ p : Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ℤ),
        SIS.IsEll2Solution p.1 β p.2 →
        (Fintype.card Guess : ℝ≥0∞)⁻¹ ≤
          (PMF.uniformOfFintype Guess).toOuterMeasure (S_p p) := by
      intro p hp
      obtain ⟨gu₀, hgu₀⟩ := exists_guess_of_isEll2Solution hβ hp
      calc (Fintype.card Guess : ℝ≥0∞)⁻¹
          = (PMF.uniformOfFintype Guess).toOuterMeasure {gu₀} := by
              rw [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
        _ ≤ _ := (PMF.uniformOfFintype Guess).toOuterMeasure.mono
              (Set.singleton_subset_iff.mpr (show gu₀ ∈ S_p p from ⟨hp, hgu₀⟩))
    have henn : (Fintype.card Guess : ℝ≥0∞)⁻¹ *
        pAZ.toOuterMeasure {p | SIS.IsEll2Solution p.1 β p.2} ≤
        idealJoint.toOuterMeasure E_good := by
      rw [hmeas_eq,
        PMF.toOuterMeasure_bind_apply (p := PMF.uniformOfFintype Guess),
        PMF.toOuterMeasure_apply (p := pAZ)]
      simp_rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
      rw [← ENNReal.tsum_mul_left]
      have hcomm : ∑' gu : Guess, PMF.uniformOfFintype Guess gu *
            ∑' p, ((fun p => (gu, p.1, p.2)) ⁻¹' E_AZ).indicator pAZ p =
          ∑' p, pAZ p * ∑' gu : Guess,
            (S_p p).indicator (PMF.uniformOfFintype Guess) gu := by
        simp_rw [← ENNReal.tsum_mul_left]
        rw [tsum_comm]
        refine tsum_congr fun p => ?_
        refine tsum_congr fun gu => ?_
        by_cases h : SIS.IsEll2Solution p.1 β p.2 ∧ p.2 gu.1 = guessAlpha gu.2.1 gu.2.2
        · simp only [Set.indicator_of_mem (show p ∈ (fun p => (gu, p.1, p.2)) ⁻¹' E_AZ from h),
            Set.indicator_of_mem (show gu ∈ S_p p from h), mul_comm]
        · simp only [Set.indicator_of_notMem (show p ∉ (fun p => (gu, p.1, p.2)) ⁻¹' E_AZ from h),
            Set.indicator_of_notMem (show gu ∉ S_p p from h), mul_zero]
      rw [hcomm]
      refine tsum_le_tsum fun p => ?_
      by_cases hp : SIS.IsEll2Solution p.1 β p.2
      · simp only [Set.indicator_of_mem (show p ∈ {p | SIS.IsEll2Solution p.1 β p.2} from hp)]
        rw [mul_comm]
        have h1 := hpoint p hp
        rw [PMF.toOuterMeasure_apply] at h1
        exact mul_le_mul_of_nonneg_left h1 zero_le
      · simp [hp]
    have htoR := ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _) henn
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← hadv_eq, hcardG,
      inv_mul_eq_div] at htoR
    exact htoR
  -- Step 3: combine `hclose_joint` and `hideal_ge` for `realJoint.toOuterMeasure E_good`
  have hreal_ge : (sisEll2Advantage q β F : ℝ) / (2 * (Nat.floor β : ℝ) * m) -
      m * ε / (2 * (1 - ε)) ≤ (realJoint.toOuterMeasure E_good).toReal := by
    have hδ_nonneg : 0 ≤ m * ε / (2 * (1 - ε)) := by
      have : 0 < 1 - ε := by linarith
      positivity
    have habs := hclose_joint.abs_toReal_sub_le hδ_nonneg E_good
    rw [abs_le] at habs
    linarith
  -- Step 4: multiply `realJoint.toOuterMeasure E_good` by `1 / 3` using `hcond`
  have hfinal_enn : ENNReal.ofReal (1 / 3 : ℝ) * realJoint.toOuterMeasure E_good ≤
      (idealIncGDDStep B S hB β r hβ hr t F).toOuterMeasure E_sol := by
    have hbind_eq : idealIncGDDStep B S hB β r hβ hr t F =
        realJoint.bind fun x =>
          (pY x.1 x.2.1).map fun Y =>
            combineOutput B S q x.2.2.1 x.2.1 x.2.2.2 -
              ∑ i : Fin m, x.2.2.2 i • (Y i : EuclideanSpace ℝ (Fin n)) := by
      rw [hstep_eq]
      simp only [realJoint, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    rw [hbind_eq,
      PMF.toOuterMeasure_bind_apply (p := realJoint),
      PMF.toOuterMeasure_apply (p := realJoint),
      ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ E_good
    · simp only [Set.indicator_of_mem hx]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hcond x.1 x.2.1 x.2.2.1 x.2.2.2 hx) zero_le
    · simp [hx]
  have hfinal_R := ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _) hfinal_enn
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 3)] at hfinal_R
  exact (mul_le_mul_of_nonneg_left hreal_ge (by norm_num : (0 : ℝ) ≤ 1 / 3)).trans hfinal_R

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
  have hbase :=
    idealIncGDDStep_succProb_of_sisEll2 hn hm B S hB hS hSB hβ hg hr hε0 hε hq hdual t F
  have habs := hclose.abs_toReal_sub_le hη
    {v | IncGDD.IsSolution g (intLattice B) (intColCast B S hB) t r v}
  rw [abs_le] at habs
  linarith

end Cslib.Crypto.SIS.MR07
