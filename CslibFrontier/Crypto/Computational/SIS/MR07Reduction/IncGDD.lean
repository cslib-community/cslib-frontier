/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.LinearAlgebra.BareissElimination
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Crypto.Computational.Lattice.GIVP
public import CslibFrontier.Crypto.Computational.SIS.Basic
public import CslibFrontier.Crypto.Computational.SIS.Ell2
public import CslibFrontier.Crypto.Computational.SIS.MR07Core
public import CslibFrontier.Crypto.Computational.SIS.MR07Reduction.Shorten
public import CslibFrontier.Crypto.Computational.SIS.MR07Samplers
public import CslibFrontier.Foundations.Data.List.DotProduct
public import CslibFrontier.Foundations.Data.Matrix.RowTable
public import CslibFrontier.Foundations.Probability.Gaussian.Int
public import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter
public import CslibFrontier.Probability.StatisticalDistance.CloseTo

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.Traverse
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.CloseTo.UniformNat
import CslibFrontier.Languages.Probabilistic.Traverse
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.StatisticalDistance.Product
import CslibFrontier.Probability.StatisticalDistance.UniformMod
import CslibFrontier.Probability.UniformNat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.List.GetD

/-!
# Strict-PPT Amplified `IncGDD` Reduction from `ℓ₂`-SIS

This module implements and analyzes the finite-parameter strict probabilistic polynomial-time
(`IsPPTOn`) reduction from the Incremental Guaranteed Distance Decoding (`IncGDD`) problem to
`ℓ₂`-SIS, providing the finite-parameter algorithmic step toward `[MicciancioRegev2007]`
Theorem 5.9 (see tracking issue #6861 for the asymptotic worst-case hardness endpoints).

## Main definitions

* `Cslib.Crypto.SIS.MR07.MR07ParamPolyTime`: polynomial-time computability of the SIS parameter
  schedules `P.n, P.m, P.β` (unary) and `P.q` (binary).
* `Cslib.Crypto.SIS.MR07.IncGDDInput`, `IncGDDInput.enc`: structured input and framing encoding
  for the amplified `IncGDD` reduction.
* `Cslib.Crypto.SIS.MR07.singleIncGDDCall`: single strict-PPT call realizing
  `MR07Core.idealIncGDDStep` via `MR07Samplers.{sampleGridGaussian, sampleQuotientModS}`,
  `sampleModNat`, `ratSolve`, `Rat.floor`, and an `ℓ₂`-SIS solver `F`.
* `Cslib.Crypto.SIS.MR07.mr07IncGDDReduction`: `OracleComp.replicate` amplification wrapper
  selecting the closest candidate via denominator-cleared pure-integer squared distance.
* `Cslib.Crypto.SIS.MR07.mr07SingleCallErr`: explicit 5-term `CloseTo` discrepancy budget for one
  `singleIncGDDCall`.

## Main results

* `Cslib.Crypto.SIS.MR07.isPPTOn_singleIncGDDCall`,
  `Cslib.Crypto.SIS.MR07.isPPTOn_mr07IncGDDReduction`: unconditional strict-PPT certificates.
* `Cslib.Crypto.SIS.MR07.mem_support_singleIncGDDCall_mem_intLattice`,
  `Cslib.Crypto.SIS.MR07.mem_support_mr07IncGDDReduction_mem_intLattice`: unconditional lattice
  membership on 100% of the output support regardless of SIS solver behavior.
* `Cslib.Crypto.SIS.MR07.closeTo_eval_singleIncGDDCall_idealIncGDDStep`: full 4-stage `CloseTo`
  bridge from `singleIncGDDCall` to `MR07Core.idealIncGDDStep`.
* `Cslib.Crypto.SIS.MR07.mr07IncGDDReduction_succProb_ge`: finite-parameter amplified `IncGDD`
  failure bound `(1 - pSingle)^trials` toward `[MicciancioRegev2007]` Theorem 5.9.
-/

public section

namespace Cslib.Crypto.SIS.MR07

open Cslib Cslib.Crypto Cslib.Crypto.SIS Cslib.LinearAlgebra Cslib.Probability Cslib.ProbComp
open Mathlib.Tactic.Matrix ProbabilityTheory ZLattice
open Turing.MultiTapeTM ComputableInPolyTime
open scoped IntTable RatTable LinearSystemInput LinearSolveResult
  GridSampleInput QuotientSampleInput BigOperators ENNReal NNReal RealInnerProductSpace
  _root_.Matrix

attribute [local irreducible] encRat encIntBin encNat IntTable.enc RatTable.enc
  GridSampleInput.enc QuotientSampleInput.enc

/-! ### 1. Parameter Family, Input Structure & Euclidean Conversion Helpers -/

/-- Efficiency predicate for a SIS parameter family `P` used by the MR07 strict-PPT reduction:
`n, m, β` computable in unary and `q` in binary (`encNat`). -/
structure MR07ParamPolyTime (P : SISParams) : Prop where
  /-- Dimension schedule `P.n` is polytime in unary. -/
  hn : ComputableInPolyTime P.n encUnary encUnary
  /-- Column-count schedule `P.m` is polytime in unary. -/
  hm : ComputableInPolyTime P.m encUnary encUnary
  /-- Norm-bound schedule `P.β` is polytime in unary. -/
  hβ : ComputableInPolyTime P.β encUnary encUnary
  /-- Modulus schedule `P.q` is polytime in binary (`encNat`). -/
  hq : ComputableInPolyTime P.q encUnary encNat

/-- Input to the strict-PPT amplified `IncGDD` reduction (finite step toward
`[MicciancioRegev2007]` Theorem 5.9). `basisB` and `basisS` are row-major `IntTable`s whose
columns are the lattice basis vectors (`MR07.intCol`). -/
structure IncGDDInput where
  /-- Security parameter (encoded in unary). -/
  secParam : ℕ
  /-- Row-major integer basis of the outer lattice `L(B)`. -/
  basisB : IntTable
  /-- Row-major integer basis of the sublattice `L(S) ⊆ L(B)`. -/
  basisS : IntTable
  /-- Rational target vector `t ∈ ℚ^n`. -/
  target : List ℚ
  /-- Exact rational squared radius `r² > 0`. -/
  rSq : ℚ
  /-- Unary number of independent `singleIncGDDCall` amplification trials. -/
  trials : ℕ
  /-- Unary tail-cutoff multiplier passed to `sampleGridGaussian`. -/
  tail : ℕ
  /-- Unary dyadic acceptance-coin precision passed to `sampleGridGaussian`. -/
  prec : ℕ
  /-- Unary rejection-trial cap passed to `sampleGridGaussian`. -/
  maxTrials : ℕ
  /-- Unary extra random bits for modular guess and quotient samplers. -/
  extraBits : ℕ
  deriving DecidableEq, Repr

namespace IncGDDInput

/-- Framing encoding of `IncGDDInput`. -/
enc_structure enc : IncGDDInput where
  secParam : encUnary,
  basisB : IntTable.enc,
  basisS : IntTable.enc,
  target : (encList encRat),
  rSq : encRat,
  trials : encUnary,
  tail : encUnary,
  prec : encUnary,
  maxTrials : encUnary,
  extraBits : encUnary

end IncGDDInput

attribute [local irreducible] IncGDDInput.enc
open scoped IncGDDInput

/-- Convert a list of integers to `EuclideanSpace ℝ (Fin n)` (zero-padded). -/
@[expose] noncomputable def listToEuclidean (n : ℕ) (v : List ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i : Fin n => (v.getD i.val 0 : ℝ)

/-- Convert a list of rationals to `EuclideanSpace ℝ (Fin n)` (zero-padded). -/
@[expose] noncomputable def ratListToEuclidean (n : ℕ) (t : List ℚ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i : Fin n => (t.getD i.val 0 : ℝ)

/-- Explicit 5-term `CloseTo` discrepancy budget for one `singleIncGDDCall` (two modular guesses
`j ∈ Fin m` and `idx ∈ Fin β`, `m` columns × `n` coordinates of `sampleGridGaussian`, and `m`
columns of `sampleQuotientModS`). -/
@[expose] noncomputable def mr07SingleCallErr (n m tail prec maxTrials extraBits : ℕ) (ε : ℝ) :
    ℝ :=
  2 * (2 : ℝ) ^ (-(extraBits : ℤ)) +
    (m : ℝ) * ((n : ℝ) *
      ((1 - 1 / (16 * (2 * (tail : ℝ) + 6))) ^ maxTrials
        + (8 * (tail : ℝ) + 24) / (2 : ℝ) ^ prec
        + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (tail : ℝ) ^ 2)))) +
    (m : ℝ) * ((n : ℝ) / (2 : ℝ) ^ extraBits)

/-! ### 2. Integer-Lattice Geometry & Dual-Mass Bridges (PR 2.3 ↔ PR 2.5) -/

/-- Every vector in an integer lattice `intLattice B` has integer coordinates, so `Int.floor` is
lossless on it. -/
theorem intLattice_coord_eq_floor {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ intLattice B) (i : Fin n) :
    ((Int.floor (WithLp.ofLp y i) : ℤ) : ℝ) = WithLp.ofLp y i := by
  have hex : ∃ z : ℤ, WithLp.ofLp y i = (z : ℝ) := by
    refine Submodule.span_induction ?_ ⟨0, by simp⟩ ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      exact ⟨B i j, rfl⟩
    · rintro u v _ _ ⟨zu, hzu⟩ ⟨zv, hzv⟩
      exact ⟨zu + zv, by simp [hzu, hzv]⟩
    · rintro c u _ ⟨zu, hzu⟩
      exact ⟨c * zu, by simp [hzu]⟩
  obtain ⟨z, hz⟩ := hex
  rw [hz, Int.floor_intCast]

/-- Any full-rank integer lattice `intLattice B` satisfies `ℤ^n ⊆ (intLattice B)*`, so
`gaussianMass (intLattice B)* (2 / s) 0 - 1 ≤ ε ≤ 1 / 2` forces `1 ≤ s`, and hence `1 ≤ q * s`
for every `q ≥ 1`. -/
theorem one_le_q_mul_s_of_dualMass {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    {s ε : ℝ} (hs : 0 < s) (hε : ε ≤ 1 / 2)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule
      (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B)) (2 / s) 0 - 1 ≤ ε) :
    1 ≤ (q : ℝ) * s := by
  have : IsZLattice ℝ (intLattice B) := isZLattice_intLattice hB
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B)
  have : DiscreteTopology D := ZLattice.discreteTopology_dualSubmodule (intLattice B)
  let e0 : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)
  have he0_mem : e0 ∈ D := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    have hinner : innerₗ (EuclideanSpace ℝ (Fin n)) e0 y = WithLp.ofLp y ⟨0, hn⟩ := by
      change ⟪e0, y⟫ = WithLp.ofLp y ⟨0, hn⟩
      rw [EuclideanSpace.inner_single_left]
      simp
    rw [hinner, Submodule.mem_one]
    exact ⟨Int.floor (WithLp.ofLp y ⟨0, hn⟩), intLattice_coord_eq_floor B hy ⟨0, hn⟩⟩
  let vPos : D := ⟨e0, he0_mem⟩
  let vNeg : D := ⟨-e0, D.neg_mem he0_mem⟩
  have hvPos_ne : vPos ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : D => WithLp.ofLp (v : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩) h0
    simp [vPos, e0] at h1
  have hvNeg_ne : vNeg ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : D => WithLp.ofLp (v : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩) h0
    simp [vNeg, e0] at h1
  have hvPos_ne_neg : vPos ≠ vNeg := by
    intro h0
    have h1 := congrArg (fun v : D => WithLp.ofLp (v : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩) h0
    simp [vPos, vNeg, e0] at h1
    linarith
  have he0_norm : ‖e0‖ = 1 := by simp [e0]
  have h2s_pos : 0 < 2 / s := div_pos (by norm_num) hs
  have hsumm :
      Summable fun v : D => gaussianWeight (2 / s) ((v : EuclideanSpace ℝ (Fin n)) - 0) :=
    ZLattice.summable_gaussianWeight D (2 / s) h2s_pos 0
  have hge_terms : 2 * gaussianWeight (2 / s) e0 ≤ gaussianMass D (2 / s) 0 - 1 := by
    have hfin : ({(0 : D), vPos, vNeg} : Finset D).sum
        (fun v => gaussianWeight (2 / s) ((v : EuclideanSpace ℝ (Fin n)) - 0)) ≤
        gaussianMass D (2 / s) 0 :=
      hsumm.sum_le_tsum _ fun v _ => (gaussianWeight_pos (2 / s) _).le
    have hnot1 : (0 : D) ∉ ({vPos, vNeg} : Finset D) := by
      simp [hvPos_ne.symm, hvNeg_ne.symm]
    rw [Finset.sum_insert hnot1, Finset.sum_pair hvPos_ne_neg] at hfin
    have h0 : gaussianWeight (2 / s) (((0 : D) : EuclideanSpace ℝ (Fin n)) - 0) = 1 := by
      simp [gaussianWeight]
    have hneg : gaussianWeight (2 / s) ((vNeg : EuclideanSpace ℝ (Fin n)) - 0) =
        gaussianWeight (2 / s) e0 := by
      simp [vNeg, gaussianWeight]
    have hpos : gaussianWeight (2 / s) ((vPos : EuclideanSpace ℝ (Fin n)) - 0) =
        gaussianWeight (2 / s) e0 := by
      simp [vPos]
    linarith
  have hgw : gaussianWeight (2 / s) e0 = Real.exp (-Real.pi * (s / 2) ^ 2) := by
    simp only [gaussianWeight, he0_norm, one_pow]
    congr 1; field_simp
  have hexp_le : Real.exp (-Real.pi * (s / 2) ^ 2) ≤ 1 / 4 := by linarith
  have h1_le_s : 1 ≤ s := by
    by_contra hlt
    push Not at hlt
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hsq : (s / 2) ^ 2 < 1 / 4 := by nlinarith
    have harg : -1 < -Real.pi * (s / 2) ^ 2 := by nlinarith
    have hexp1 : Real.exp (-1 : ℝ) < Real.exp (-Real.pi * (s / 2) ^ 2) :=
      Real.exp_lt_exp.mpr harg
    have he_lt4 : Real.exp (1 : ℝ) < 4 := by linarith [Real.exp_one_lt_d9]
    have h14_lt : (1 / 4 : ℝ) < Real.exp (-1 : ℝ) := by
      rw [Real.exp_neg, one_div]
      exact inv_strictAnti₀ (Real.exp_pos 1) he_lt4
    linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  nlinarith

private theorem mem_dual_intLatticeReal_iff (w : ℝ) :
    w ∈ LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal ↔ ∃ k : ℤ, w = (k : ℝ) := by
  constructor
  · intro hw
    have h1 : (1 : ℝ) ∈ intLatticeReal := (mem_intLatticeReal_iff 1).mpr ⟨1, by simp⟩
    obtain ⟨k, hk⟩ := Submodule.mem_one.mp (hw 1 h1)
    refine ⟨k, ?_⟩
    simpa [innerₗ_apply_apply] using hk.symm
  · rintro ⟨k, rfl⟩ x hx
    obtain ⟨m, rfl⟩ := (mem_intLatticeReal_iff x).mp hx
    rw [Submodule.mem_one]
    refine ⟨m * k, ?_⟩
    simp [innerₗ_apply_apply]

/-- Dual-mass bridge connecting `MR07Core`'s `2 / s` hypothesis on `(intLattice B)*` to
`MR07Samplers`'s `1 / (q * s)` hypothesis on `intLatticeReal*`. -/
theorem gaussianMass_dual_intReal_le_of_intLattice_two_div
    {n q : ℕ} (hn : 1 ≤ n) (hq : 0 < q)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    {s : ℝ} (hs : 0 < s) :
    ZLattice.gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal)
        (1 / ((q : ℝ) * s)) 0 - 1 ≤
      ZLattice.gaussianMass
        (LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B))
        (2 / s) 0 - 1 := by
  let D1 := LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal
  let Dg := LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) (gridLattice n q)
  let DL := LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) (intLattice B)
  have : IsZLattice ℝ (gridLattice n q) := isZLattice_gridLattice hq
  have : IsZLattice ℝ (intLattice B) := isZLattice_intLattice hB
  have : DiscreteTopology Dg := ZLattice.discreteTopology_dualSubmodule (gridLattice n q)
  have : DiscreteTopology DL := ZLattice.discreteTopology_dualSubmodule (intLattice B)
  have h1s_pos : 0 < 1 / s := one_div_pos.mpr hs
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  let i0 : Fin n := ⟨0, hn⟩
  let e0 : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ i0
  have he0_norm : ‖e0‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i0
  have hmem_Dg : ∀ w : D1, ((q : ℝ) * (w : ℝ)) • e0 ∈ Dg := by
    intro w x hx
    obtain ⟨k, hk⟩ := (mem_dual_intLatticeReal_iff (w : ℝ)).mp w.property
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩
      rw [Submodule.mem_one]
      by_cases hj : j = i0
      · subst hj
        refine ⟨k, ?_⟩
        have hself : inner ℝ e0 e0 = 1 := by rw [real_inner_self_eq_norm_sq, he0_norm, one_pow]
        simp only [innerₗ_apply_apply, real_inner_smul_left, real_inner_smul_right, e0, hk,
          algebraMap_int_eq, eq_intCast]
        rw [show inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i0)
            (EuclideanSpace.basisFun (Fin n) ℝ i0) = 1 from hself]
        field_simp [hqR.ne']
      · refine ⟨0, ?_⟩
        have horth : inner ℝ e0 (EuclideanSpace.basisFun (Fin n) ℝ j) = 0 :=
          (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.2 (Ne.symm hj)
        simp only [innerₗ_apply_apply, real_inner_smul_left, real_inner_smul_right, horth,
          mul_zero, map_zero]
    · simp
    · intro a b _ _ ha hb; simpa [map_add] using Submodule.add_mem _ ha hb
    · intro a b _ hb
      have : innerₗ (EuclideanSpace ℝ (Fin n)) (((q : ℝ) * (w : ℝ)) • e0) (a • b) =
          a • innerₗ (EuclideanSpace ℝ (Fin n)) (((q : ℝ) * (w : ℝ)) • e0) b := by
        simp [innerₗ_apply_apply, ← Int.cast_smul_eq_zsmul ℝ]
      rw [this]
      exact Submodule.smul_mem _ a hb
  let f : D1 → Dg := fun w => ⟨((q : ℝ) * (w : ℝ)) • e0, hmem_Dg w⟩
  have hf_inj : Function.Injective f := by
    intro w₁ w₂ h
    have hv := congrArg (fun u : Dg => inner ℝ (u : EuclideanSpace ℝ (Fin n)) e0) h
    have hself : inner ℝ e0 e0 = 1 := by rw [real_inner_self_eq_norm_sq, he0_norm, one_pow]
    simp only [f, real_inner_smul_left, hself, mul_one] at hv
    exact Subtype.ext (mul_left_cancel₀ hqR.ne' hv)
  have hf_weight : ∀ w : D1,
      gaussianWeight (1 / ((q : ℝ) * s)) ((w : ℝ) - 0) =
        gaussianWeight (1 / s) ((f w : EuclideanSpace ℝ (Fin n)) - 0) := by
    intro w
    simp only [sub_zero, gaussianWeight, f, norm_smul, Real.norm_eq_abs, he0_norm, mul_one,
      abs_mul, abs_of_pos hqR]
    congr 1
    field_simp [hqR.ne', hs.ne']
  have hsumDg :
      Summable fun u : Dg => gaussianWeight (1 / s) ((u : EuclideanSpace ℝ (Fin n)) - 0) :=
    ZLattice.summable_gaussianWeight Dg (1 / s) h1s_pos 0
  have hsumD1 : Summable fun w : D1 => gaussianWeight (1 / ((q : ℝ) * s)) ((w : ℝ) - 0) := by
    simp_rw [hf_weight]
    exact hsumDg.comp_injective hf_inj
  have hle_grid : ZLattice.gaussianMass D1 (1 / ((q : ℝ) * s)) 0 ≤
      ZLattice.gaussianMass Dg (1 / s) 0 := by
    unfold ZLattice.gaussianMass
    exact hsumD1.tsum_le_tsum_of_inj f hf_inj (fun _ _ => (gaussianWeight_pos _ _).le)
      (fun w => (hf_weight w).le) hsumDg
  have hgrid_le_L := gaussianMass_dual_gridLattice_le hB hq hs
  have h1s_le_2s : ZLattice.gaussianMass DL (1 / s) 0 ≤ ZLattice.gaussianMass DL (2 / s) 0 := by
    have h2s_pos : 0 < 2 / s := div_pos (by norm_num) hs
    unfold ZLattice.gaussianMass
    refine (ZLattice.summable_gaussianWeight DL (1 / s) h1s_pos 0).tsum_le_tsum ?_
      (ZLattice.summable_gaussianWeight DL (2 / s) h2s_pos 0)
    intro v
    simp only [sub_zero, gaussianWeight]
    apply Real.exp_le_exp.mpr
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    have hsq : 0 ≤ ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 := sq_nonneg _
    have hinv : (1 / s) ^ 2 ≤ (2 / s) ^ 2 :=
      pow_le_pow_left₀ h1s_pos.le (div_le_div_of_nonneg_right (by norm_num) hs.le) 2
    have hdiv : ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (2 / s) ^ 2 ≤
        ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (1 / s) ^ 2 :=
      div_le_div_of_nonneg_left hsq (sq_pos_of_pos h1s_pos) hinv
    rw [mul_div_assoc, mul_div_assoc]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hpi]
  linarith

/-! ### 3. Shared Linear-Algebra, SIS-Solver, and Combining Helpers -/

private def intTableToRatTable (B : IntTable) : RatTable :=
  ⟨B.numRows, B.numCols, B.rows.map fun row => row.map (Int.cast : ℤ → ℚ)⟩

private theorem computableInPolyTime_intTableToRatTable :
    ComputableInPolyTime intTableToRatTable IntTable.enc RatTable.enc := by
  have hcast : ComputableInPolyTime (fun p : List ℤ × ℤ => (p.2 : ℚ))
      (encPair (encList encIntBin) encIntBin) encRat :=
    (snd (encList encIntBin) encIntBin).trans rat_intCast
  have hrow : ComputableInPolyTime (fun row : List ℤ => row.map (Int.cast : ℤ → ℚ))
      (encList encIntBin) (encList encRat) :=
    mapWithInput (f := fun _ (z : ℤ) => (z : ℚ)) (id' (encIn := encList encIntBin)) hcast
  have hBrows : ComputableInPolyTime (RowTable.rows : IntTable → _) IntTable.enc
      (encList (encList encIntBin)) := by
    fun_prop
  have hrows : ComputableInPolyTime
      (fun B : IntTable => B.rows.map fun row => row.map (Int.cast : ℤ → ℚ))
      IntTable.enc (encList (encList encRat)) :=
    mapWithInput (f := fun _ (row : List ℤ) => row.map (Int.cast : ℤ → ℚ)) hBrows
      ((snd IntTable.enc (encList encIntBin)).trans hrow)
  have heq : intTableToRatTable = fun B =>
      RowTable.mk (α := ℚ) B.numRows B.numCols
        (B.rows.map fun row => row.map (Int.cast : ℤ → ℚ)) := rfl
  rw [heq]
  fun_prop

private def intTableMulVec (B : IntTable) (v : List ℤ) : List ℤ :=
  (List.range B.numRows).map fun r =>
    ListMatrix.dotProduct B.numCols (B.rows.getD r []) v

private theorem computableInPolyTime_intTableMulVec :
    ComputableInPolyTime (fun p : IntTable × List ℤ => intTableMulVec p.1 p.2)
      (encPair IntTable.enc (encList encIntBin)) (encList encIntBin) := by
  unfold intTableMulVec
  let encIn := encPair IntTable.enc (encList encIntBin)
  have hrows : ComputableInPolyTime (fun p : IntTable × List ℤ => List.range p.1.numRows)
      encIn (encList encUnary) :=
    unary_range' (by fun_prop)
  have hrowStep : ComputableInPolyTime
      (fun q : (IntTable × List ℤ) × ℕ =>
        ListMatrix.dotProduct q.1.1.numCols (q.1.1.rows.getD q.2 []) q.1.2)
      (encPair encIn encUnary) encIntBin := by
    let encQ := encPair encIn encUnary
    have hnc : ComputableInPolyTime (fun q : (IntTable × List ℤ) × ℕ => q.1.1.numCols)
        encQ encUnary := by fun_prop
    have hrowL : ComputableInPolyTime
        (fun q : (IntTable × List ℤ) × ℕ => q.1.1.rows.getD q.2 [])
        encQ (encList encIntBin) := by
      have hr : ComputableInPolyTime (fun q : (IntTable × List ℤ) × ℕ => q.1.1.rows)
          encQ (encList (encList encIntBin)) := by fun_prop
      exact listGetDWithInput hr (snd encIn encUnary) []
    have hv : ComputableInPolyTime (fun q : (IntTable × List ℤ) × ℕ => q.1.2)
        encQ (encList encIntBin) := by fun_prop
    exact listDotProduct.comp (hnc.prod (hrowL.prod hv))
  exact mapWithInput hrows hrowStep

private theorem rat_floor_divInt_eq_ediv (a : ℤ) {q : ℕ} (hq : 0 < q) :
    (Rat.divInt a (q : ℤ)).floor = a / (q : ℤ) := by
  change Int.floor (Rat.divInt a (q : ℤ)) = a / (q : ℤ)
  rw [Int.floor_eq_iff, Rat.divInt_eq_div]
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hmod_ge : 0 ≤ a % (q : ℤ) := Int.emod_nonneg a hqZ.ne'
  have hmod_lt : a % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos a hqZ
  have hdiv_add : a % (q : ℤ) + (q : ℤ) * (a / (q : ℤ)) = a := Int.emod_add_mul_ediv a (q : ℤ)
  have hlo_z : (a / (q : ℤ)) * (q : ℤ) ≤ a := by linarith
  have hhi_z : a < (a / (q : ℤ) + 1) * (q : ℤ) := by linarith
  have hlo_q : ((a / (q : ℤ) : ℤ) : ℚ) * (q : ℚ) ≤ (a : ℚ) := by exact_mod_cast hlo_z
  have hhi_q : (a : ℚ) < (((a / (q : ℤ) : ℤ) : ℚ) + 1) * (q : ℚ) := by exact_mod_cast hhi_z
  rw [Int.cast_natCast]
  exact ⟨(le_div_iff₀ hqQ).mpr hlo_q, (div_lt_iff₀ hqQ).mpr hhi_q⟩

/-- Pack a row-major `List (List ℕ)` of residues into `P.Input` at security parameter `κ`. -/
private def makeSISInput (P : SISParams) (κ : ℕ) (rows : List (List ℕ)) : P.Input :=
  ⟨κ, Matrix.of fun i j => ((rows.getD i.1 []).getD j.1 0 : ZMod (P.q κ))⟩

private theorem list_ofFn_eq_map_range {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.ofFn fun i : Fin n => f i.1) = (List.range n).map f := by
  apply List.ext_getElem <;> simp

private theorem makeSISInput_polytime {P : SISParams} (hP : MR07ParamPolyTime P) :
    ComputableInPolyTime (fun p : ℕ × List (List ℕ) => makeSISInput P p.1 p.2)
      (encPair encUnary (encList (encList encNat))) P.encInput := by
  let encRows := encList (encList encNat)
  let encIn := encPair encUnary encRows
  have hκ : ComputableInPolyTime (fun p : ℕ × List (List ℕ) => p.1) encIn encUnary :=
    fst encUnary encRows
  have hq : ComputableInPolyTime (fun p : ℕ × List (List ℕ) => P.q p.1) encIn encNat :=
    hP.hq.comp hκ
  have hrow : ComputableInPolyTime
      (fun q : (ℕ × List (List ℕ)) × ℕ =>
        (List.range (P.m q.1.1)).map fun j => ((q.1.2.getD q.2 []).getD j 0) % P.q q.1.1)
      (encPair encIn encUnary) (encList encNat) := by
    have hidx := unary_range' ((hP.hm.comp hκ).comp (fst encIn encUnary))
    have hent : ComputableInPolyTime
        (fun r : ((ℕ × List (List ℕ)) × ℕ) × ℕ =>
          ((r.1.1.2.getD r.1.2 []).getD r.2 0) % P.q r.1.1.1)
        (encPair (encPair encIn encUnary) encUnary) encNat :=
      binary_mod' (by fun_prop)
        (hq.comp ((fst encIn encUnary).comp (fst (encPair encIn encUnary) encUnary)))
    exact mapWithInput hidx hent
  have hmat : ComputableInPolyTime
      (fun p : ℕ × List (List ℕ) =>
        (List.range (P.n p.1)).map fun i =>
          (List.range (P.m p.1)).map fun j => ((p.2.getD i []).getD j 0) % P.q p.1)
      encIn encRows :=
    mapWithInput (unary_range' (hP.hn.comp hκ)) hrow
  refine (hκ.prod hmat).of_enc_eq fun p => ?_
  rw [SISParams.encInput_apply, SIS.encodeMatrix]
  have hof :
      (List.ofFn fun i : Fin (P.n p.1) => List.ofFn fun j : Fin (P.m p.1) =>
        ((makeSISInput P p.1 p.2).matrix i j).val) =
      (List.range (P.n p.1)).map fun i =>
        (List.range (P.m p.1)).map fun j => ((p.2.getD i []).getD j 0) % P.q p.1 := by
    have hinner : ∀ i : Fin (P.n p.1),
        (List.ofFn fun j : Fin (P.m p.1) => ((makeSISInput P p.1 p.2).matrix i j).val) =
        (List.range (P.m p.1)).map fun j => ((p.2.getD i.1 []).getD j 0) % P.q p.1 := fun i => by
      simpa [makeSISInput, ZMod.val_natCast] using
        list_ofFn_eq_map_range (P.m p.1) (fun j => ((p.2.getD i.1 []).getD j 0) % P.q p.1)
    simp_rw [hinner]
    exact list_ofFn_eq_map_range (P.n p.1)
      (fun i => (List.range (P.m p.1)).map fun j => ((p.2.getD i []).getD j 0) % P.q p.1)
  change frame (encUnary p.1) ++
      encList (encList encNat)
        (List.ofFn fun i : Fin (P.n p.1) => List.ofFn fun j : Fin (P.m p.1) =>
          ((makeSISInput P p.1 p.2).matrix i j).val) =
    encPair encUnary encRows
      (p.1, (List.range (P.n p.1)).map fun i =>
        (List.range (P.m p.1)).map fun j => ((p.2.getD i []).getD j 0) % P.q p.1)
  rw [hof]
  rfl

/-- Invoke a SIS solver `F` on a row-major residue matrix and return its output as `List ℤ`. -/
private noncomputable def callSISSolver (P : SISParams) (F : P.Solver) (κ : ℕ)
    (rows : List (List ℕ)) :
    ProbComp (List ℤ) :=
  List.ofFn <$> F κ (makeSISInput P κ rows).matrix

private theorem isPPTOn_callSISSolver {P : SISParams} (hP : MR07ParamPolyTime P)
    {F : P.Solver} (hF : F.IsPPT) :
    IsPPTOn (encPair encUnary (encList (encList encNat))) (encList encIntBin)
      (fun p => callSISSolver P F p.1 p.2) := by
  have hF_list : IsPPTOn P.encInput (encList encIntBin)
      (fun x => List.ofFn <$> F x.secParam x.matrix) := by
    obtain ⟨k, State, hfin, tm, c, d, hrun⟩ := hF
    refine ⟨k, State, hfin, tm, c, d, fun x => ?_⟩
    simpa only [SIS.encodeVec, encBits, Function.Embedding.refl_apply,
      ProbComp.eval_map, PMF.map_comp, Function.comp_def] using hrun x
  exact (hF_list.preprocess (makeSISInput_polytime hP)).congr fun _ => rfl

private structure CombineColArg where
  dim : ℕ
  modulus : ℕ
  sublattice : IntTable
  v : List ℤ
  u : List ℤ
  deriving DecidableEq, Repr

private enc_structure CombineColArg.enc : CombineColArg where
  dim : encUnary,
  modulus : encNat,
  sublattice : IntTable.enc,
  v : (encList encIntBin),
  u : (encList encIntBin)

attribute [local irreducible] CombineColArg.enc
open scoped CombineColArg

/-- Exact single-column combiner realizing `MR07Core.combineColumn`: solves `S *ᵥ ξ = v + u / q`,
sets `k = ⌊ξ⌋`, `sk = S *ᵥ k`, and `a_r = ⌊q * (ξ_r - k_r)⌋ % q`. -/
private def combineColInt (dim q : ℕ) (S : IntTable) (v u : List ℤ) : List ℤ × List ℕ :=
  let rhs : List ℚ := (List.range dim).map fun r =>
    Rat.divInt ((q : ℤ) * v.getD r 0 + u.getD r 0) (q : ℤ)
  let sol : List ℚ := (ratSolve ⟨intTableToRatTable S, rhs⟩).solution.getD (List.replicate dim 0)
  let k : List ℤ := (List.range dim).map fun r => (sol.getD r 0).floor
  let sk : List ℤ := intTableMulVec S k
  let a : List ℕ := (List.range dim).map fun r =>
    (((q : ℚ) * (sol.getD r 0 - (k.getD r 0 : ℚ))).floor).toNat % q
  (sk, a)

private theorem computableInPolyTime_combineColInt :
    ComputableInPolyTime
      (fun p : CombineColArg => combineColInt p.dim p.modulus p.sublattice p.v p.u)
      CombineColArg.enc (encPair (encList encIntBin) (encList encNat)) := by
  have hdim : ComputableInPolyTime CombineColArg.dim CombineColArg.enc encUnary := by fun_prop
  have hq : ComputableInPolyTime CombineColArg.modulus CombineColArg.enc encNat := by fun_prop
  have hS : ComputableInPolyTime CombineColArg.sublattice CombineColArg.enc IntTable.enc := by
    fun_prop
  have hv : ComputableInPolyTime CombineColArg.v CombineColArg.enc (encList encIntBin) := by
    fun_prop
  have hu : ComputableInPolyTime CombineColArg.u CombineColArg.enc (encList encIntBin) := by
    fun_prop
  have hrng : ComputableInPolyTime (fun p : CombineColArg => List.range p.dim)
      CombineColArg.enc (encList encUnary) := unary_range' hdim
  have hrhs : ComputableInPolyTime
      (fun p : CombineColArg => (List.range p.dim).map fun r =>
        Rat.divInt ((p.modulus : ℤ) * p.v.getD r 0 + p.u.getD r 0) (p.modulus : ℤ))
      CombineColArg.enc (encList encRat) := by
    have hqz := intBin_natCast.comp (hq.comp (fst CombineColArg.enc encUnary))
    have hvr := listGetDWithInput (hv.comp (fst CombineColArg.enc encUnary))
      (snd CombineColArg.enc encUnary) 0
    have hur := listGetDWithInput (hu.comp (fst CombineColArg.enc encUnary))
      (snd CombineColArg.enc encUnary) 0
    exact mapWithInput hrng (rat_divInt' (intBin_add' (intBin_mul' hqz hvr) hur) hqz)
  have hsys : ComputableInPolyTime
      (fun p : CombineColArg => LinearSystemInput.mk (intTableToRatTable p.sublattice)
        ((List.range p.dim).map fun r =>
          Rat.divInt ((p.modulus : ℤ) * p.v.getD r 0 + p.u.getD r 0) (p.modulus : ℤ)))
      CombineColArg.enc LinearSystemInput.enc := by
    have hSrat := computableInPolyTime_intTableToRatTable.comp hS
    fun_prop
  have hopt : ComputableInPolyTime
      (fun p : CombineColArg => (ratSolve ⟨intTableToRatTable p.sublattice,
        (List.range p.dim).map fun r =>
          Rat.divInt ((p.modulus : ℤ) * p.v.getD r 0 + p.u.getD r 0) (p.modulus : ℤ)⟩).solution)
      CombineColArg.enc (encOption (encList encRat)) :=
    (by fun_prop : ComputableInPolyTime LinearSolveResult.solution LinearSolveResult.enc
      (encOption (encList encRat))).comp (ratSolve_computableInPolyTime.comp hsys)
  have hsol := optionGetDWithInput hopt (by fun_prop :
    ComputableInPolyTime (fun p : CombineColArg => List.replicate p.dim (0 : ℚ))
      CombineColArg.enc (encList encRat))
  have hk : ComputableInPolyTime
      (fun p : CombineColArg => (List.range p.dim).map fun r =>
        (((ratSolve ⟨intTableToRatTable p.sublattice,
          (List.range p.dim).map fun r =>
            Rat.divInt ((p.modulus : ℤ) * p.v.getD r 0 + p.u.getD r 0)
              (p.modulus : ℤ)⟩).solution.getD
          (List.replicate p.dim 0)).getD r 0).floor)
      CombineColArg.enc (encList encIntBin) :=
    mapWithInput hrng
      (rat_floor.comp
        (listGetDWithInput (hsol.comp (fst CombineColArg.enc encUnary))
          (snd CombineColArg.enc encUnary) 0))
  have hsk := computableInPolyTime_intTableMulVec.comp (hS.prod hk)
  have ha : ComputableInPolyTime
      (fun p : CombineColArg => (List.range p.dim).map fun r =>
        (((p.modulus : ℚ) *
          (((ratSolve ⟨intTableToRatTable p.sublattice,
            (List.range p.dim).map fun r =>
              Rat.divInt ((p.modulus : ℤ) * p.v.getD r 0 + p.u.getD r 0)
                (p.modulus : ℤ)⟩).solution.getD
            (List.replicate p.dim 0)).getD r 0 -
          ((((List.range p.dim).map fun r =>
            (((ratSolve ⟨intTableToRatTable p.sublattice,
              (List.range p.dim).map fun r =>
                Rat.divInt ((p.modulus : ℤ) * p.v.getD r 0 + p.u.getD r 0)
                  (p.modulus : ℤ)⟩).solution.getD
              (List.replicate p.dim 0)).getD r 0).floor).getD r 0 : ℤ) : ℚ))).floor).toNat %
          p.modulus)
      CombineColArg.enc (encList encNat) := by
    have hq_r : ComputableInPolyTime (fun x : CombineColArg × ℕ => (x.1.modulus : ℚ))
        (encPair CombineColArg.enc encUnary) encRat :=
      rat_intCast.comp (intBin_natCast.comp (hq.comp (fst CombineColArg.enc encUnary)))
    have hsolr := listGetDWithInput (hsol.comp (fst CombineColArg.enc encUnary))
      (snd CombineColArg.enc encUnary) 0
    have hkr := rat_intCast.comp
      (listGetDWithInput (hk.comp (fst CombineColArg.enc encUnary))
        (snd CombineColArg.enc encUnary) 0)
    have hfl := rat_floor.comp (rat_mul' hq_r (rat_sub' hsolr hkr))
    exact mapWithInput hrng
      (binary_mod' (intBin_toNat.comp hfl) (hq.comp (fst CombineColArg.enc encUnary)))
  exact hsk.prod ha

private structure CombineRowsArg where
  n : ℕ
  m : ℕ
  cols : List (List ℤ × List ℕ)
  deriving DecidableEq, Repr

private enc_structure CombineRowsArg.enc : CombineRowsArg where
  n : encUnary,
  m : encUnary,
  cols : (encList (encPair (encList encIntBin) (encList encNat)))

attribute [local irreducible] CombineRowsArg.enc
open scoped CombineRowsArg

/-- Transpose the `m` column residue vectors produced by `combineColInt` into `n` matrix rows. -/
private def combineMatrixRowsInt (n m : ℕ) (cols : List (List ℤ × List ℕ)) : List (List ℕ) :=
  (List.range n).map fun r =>
    (List.range m).map fun c => (cols.getD c ([], [])).2.getD r 0

private theorem computableInPolyTime_combineMatrixRowsInt :
    ComputableInPolyTime (fun p : CombineRowsArg => combineMatrixRowsInt p.n p.m p.cols)
      CombineRowsArg.enc (encList (encList encNat)) := by
  have hn : ComputableInPolyTime CombineRowsArg.n CombineRowsArg.enc encUnary := by fun_prop
  have hm : ComputableInPolyTime CombineRowsArg.m CombineRowsArg.enc encUnary := by fun_prop
  have hcols : ComputableInPolyTime CombineRowsArg.cols CombineRowsArg.enc
      (encList (encPair (encList encIntBin) (encList encNat))) := by fun_prop
  have hrow : ComputableInPolyTime
      (fun q : CombineRowsArg × ℕ =>
        (List.range q.1.m).map fun c => (q.1.cols.getD c ([], [])).2.getD q.2 0)
      (encPair CombineRowsArg.enc encUnary) (encList encNat) := by
    let encQ := encPair CombineRowsArg.enc encUnary
    have hcol : ComputableInPolyTime
        (fun t : (CombineRowsArg × ℕ) × ℕ => (t.1.1.cols.getD t.2 ([], [])).2)
        (encPair encQ encUnary) (encList encNat) :=
      (snd (encList encIntBin) (encList encNat)).comp
        (listGetDWithInput (hcols.comp ((fst CombineRowsArg.enc encUnary).comp (fst encQ encUnary)))
          (snd encQ encUnary) ([], []))
    have hent : ComputableInPolyTime
        (fun t : (CombineRowsArg × ℕ) × ℕ => (t.1.1.cols.getD t.2 ([], [])).2.getD t.1.2 0)
        (encPair encQ encUnary) encNat :=
      listGetDWithInput hcol ((snd CombineRowsArg.enc encUnary).comp (fst encQ encUnary)) 0
    exact mapWithInput (unary_range' (hm.comp (fst CombineRowsArg.enc encUnary))) hent
  exact mapWithInput (unary_range' hn) hrow

private structure CombineOutArg where
  n : ℕ
  m : ℕ
  q : ℕ
  sublattice : IntTable
  cols : List (List ℤ × List ℕ)
  vs : List (List ℤ)
  ys : List (List ℤ)
  z : List ℤ
  deriving DecidableEq, Repr

private enc_structure CombineOutArg.enc : CombineOutArg where
  n : encUnary,
  m : encUnary,
  q : encNat,
  sublattice : IntTable.enc,
  cols : (encList (encPair (encList encIntBin) (encList encNat))),
  vs : (encList (encList encIntBin)),
  ys : (encList (encList encIntBin)),
  z : (encList encIntBin)

attribute [local irreducible] CombineOutArg.enc
open scoped CombineOutArg

/-- Exact integer recombination realizing `combineOutput B S q V C z - ∑ z_i • Y_i` using
`Rat.floor (Rat.divInt _ q)` for exact integer division by `q`. -/
private def combineOutputInt (n m q : ℕ) (S : IntTable)
    (cols : List (List ℤ × List ℕ)) (vs ys : List (List ℤ)) (z : List ℤ) : List ℤ :=
  let azDivQ : List ℤ := (List.range n).map fun r =>
    (Rat.divInt (((List.range m).map fun c =>
      (((cols.getD c ([], [])).2.getD r 0 : ℕ) : ℤ) * z.getD c 0).sum) (q : ℤ)).floor
  let sAzDivQ : List ℤ := intTableMulVec S azDivQ
  (List.range n).map fun r =>
    (((List.range m).map fun c =>
      z.getD c 0 * ((cols.getD c ([], [])).1.getD r 0 -
        (vs.getD c []).getD r 0 - (ys.getD c []).getD r 0)).sum) + sAzDivQ.getD r 0

private theorem computableInPolyTime_combineOutputInt :
    ComputableInPolyTime
      (fun p : CombineOutArg => combineOutputInt p.n p.m p.q p.sublattice p.cols p.vs p.ys p.z)
      CombineOutArg.enc (encList encIntBin) := by
  have hn : ComputableInPolyTime CombineOutArg.n CombineOutArg.enc encUnary := by fun_prop
  have hm : ComputableInPolyTime CombineOutArg.m CombineOutArg.enc encUnary := by fun_prop
  have hq : ComputableInPolyTime CombineOutArg.q CombineOutArg.enc encNat := by fun_prop
  have hS : ComputableInPolyTime CombineOutArg.sublattice CombineOutArg.enc IntTable.enc := by
    fun_prop
  have hcols : ComputableInPolyTime CombineOutArg.cols CombineOutArg.enc
      (encList (encPair (encList encIntBin) (encList encNat))) := by fun_prop
  have hvs : ComputableInPolyTime CombineOutArg.vs CombineOutArg.enc
      (encList (encList encIntBin)) := by fun_prop
  have hys : ComputableInPolyTime CombineOutArg.ys CombineOutArg.enc
      (encList (encList encIntBin)) := by fun_prop
  have hz : ComputableInPolyTime CombineOutArg.z CombineOutArg.enc (encList encIntBin) := by
    fun_prop
  have hrngN := unary_range' hn
  let encQ := encPair CombineOutArg.enc encUnary
  have hp1 := (fst CombineOutArg.enc encUnary).comp (fst encQ encUnary)
  have hr := (snd CombineOutArg.enc encUnary).comp (fst encQ encUnary)
  have hc := snd encQ encUnary
  have hz_c := listGetDWithInput (hz.comp hp1) hc 0
  have hazDivQ : ComputableInPolyTime
      (fun p : CombineOutArg => (List.range p.n).map fun r =>
        (Rat.divInt (((List.range p.m).map fun c =>
          (((p.cols.getD c ([], [])).2.getD r 0 : ℕ) : ℤ) * p.z.getD c 0).sum)
          (p.q : ℤ)).floor)
      CombineOutArg.enc (encList encIntBin) := by
    have hsum : ComputableInPolyTime
        (fun q : CombineOutArg × ℕ => ((List.range q.1.m).map fun c =>
          (((q.1.cols.getD c ([], [])).2.getD q.2 0 : ℕ) : ℤ) * q.1.z.getD c 0).sum)
        encQ encIntBin := by
      have hcol : ComputableInPolyTime
          (fun t : (CombineOutArg × ℕ) × ℕ => (t.1.1.cols.getD t.2 ([], [])).2)
          (encPair encQ encUnary) (encList encNat) :=
        (snd (encList encIntBin) (encList encNat)).comp
          (listGetDWithInput (hcols.comp hp1) hc ([], []))
      have ha_rc := intBin_natCast.comp (listGetDWithInput hcol hr 0)
      exact (mapWithInput (unary_range' (hm.comp (fst CombineOutArg.enc encUnary)))
        (intBin_mul' ha_rc hz_c)).trans intBin_sum
    have hqZ := intBin_natCast.comp (hq.comp (fst CombineOutArg.enc encUnary))
    exact mapWithInput hrngN (rat_floor.comp (rat_divInt' hsum hqZ))
  have hsAz := computableInPolyTime_intTableMulVec.comp (hS.prod hazDivQ)
  have hsum2 : ComputableInPolyTime
      (fun q : CombineOutArg × ℕ => ((List.range q.1.m).map fun c =>
        q.1.z.getD c 0 * ((q.1.cols.getD c ([], [])).1.getD q.2 0 -
          (q.1.vs.getD c []).getD q.2 0 - (q.1.ys.getD c []).getD q.2 0)).sum)
      encQ encIntBin := by
    have hsk_c : ComputableInPolyTime
        (fun t : (CombineOutArg × ℕ) × ℕ => (t.1.1.cols.getD t.2 ([], [])).1)
        (encPair encQ encUnary) (encList encIntBin) :=
      (fst (encList encIntBin) (encList encNat)).comp
        (listGetDWithInput (hcols.comp hp1) hc ([], []))
    have hsk_rc := listGetDWithInput hsk_c hr 0
    have hv_rc := listGetDWithInput (listGetDWithInput (hvs.comp hp1) hc []) hr 0
    have hy_rc := listGetDWithInput (listGetDWithInput (hys.comp hp1) hc []) hr 0
    exact (mapWithInput (unary_range' (hm.comp (fst CombineOutArg.enc encUnary)))
      (intBin_mul' hz_c (intBin_sub' (intBin_sub' hsk_rc hv_rc) hy_rc))).trans intBin_sum
  have hsAz_r := listGetDWithInput (hsAz.comp (fst CombineOutArg.enc encUnary))
    (snd CombineOutArg.enc encUnary) 0
  exact mapWithInput hrngN (intBin_add' hsum2 hsAz_r)

/-! ### 4. Single Strict-PPT `IncGDD` Call (`singleIncGDDCall`) -/

private structure IncGDDState1 where
  inp : IncGDDInput
  j : ℕ
  sgn : Bool
  idx : ℕ
  deriving DecidableEq, Repr

private enc_structure IncGDDState1.enc : IncGDDState1 where
  inp : IncGDDInput.enc,
  j : encNat,
  sgn : encBool,
  idx : encNat

attribute [local irreducible] IncGDDState1.enc
open scoped IncGDDState1

private structure IncGDDState2 where
  inp : IncGDDInput
  cys : List (List ℤ × List ℤ)
  vs : List (List ℤ)
  deriving DecidableEq, Repr

private enc_structure IncGDDState2.enc : IncGDDState2 where
  inp : IncGDDInput.enc,
  cys : (encList (encPair (encList encIntBin) (encList encIntBin))),
  vs : (encList (encList encIntBin))

attribute [local irreducible] IncGDDState2.enc
open scoped IncGDDState2

/-- Single strict-PPT `IncGDD` call realizing `MR07Core.idealIncGDDStep` via `MR07Samplers`'s
`sampleGridGaussian` and `sampleQuotientModS`, `sampleModNat`, `ratSolve`, and `F`. -/
noncomputable def singleIncGDDCall (P : SISParams) (F : P.Solver) (inp : IncGDDInput) :
    ProbComp (List ℤ) :=
  let κ := inp.secParam
  let n := P.n κ
  let m := P.m κ
  let q := P.q κ
  let β := P.β κ
  if n = 0 ∨ m = 0 ∨ β = 0 then
    pure (List.replicate n 0)
  else do
    let j ← sampleModNat (Nat.clog 2 m + inp.extraBits) m
    let sgn ← ProbComp.uniform Bool
    let idx ← sampleModNat (Nat.clog 2 β + inp.extraBits) β
    let α : ℤ := if sgn then (idx + 1 : ℤ) else -((idx + 1 : ℤ))
    let sSq : ℚ := inp.rSq * Rat.divInt 4 ((β * β * n : ℕ) : ℤ)
    let scaledTarget : List ℚ := inp.target.map fun x => Rat.divInt (-1) α * x
    let cys ← (List.range m).mapM fun i =>
      sampleGridGaussian
        ⟨n, q, inp.basisB, sSq,
          if i = j then scaledTarget else List.replicate n 0,
          inp.tail, inp.prec, inp.maxTrials⟩
    let vs ← (List.range m).mapM fun _ =>
      sampleQuotientModS ⟨n, inp.basisB, inp.basisS, inp.extraBits⟩
    let cols := (List.range m).map fun c =>
      combineColInt n q inp.basisS (vs.getD c []) (cys.getD c ([], [])).1
    let rows := combineMatrixRowsInt n m cols
    let z ← callSISSolver P F κ rows
    let ys := cys.map Prod.snd
    pure (combineOutputInt n m q inp.basisS cols vs ys z)

private noncomputable def stageSampleGuess (P : SISParams) (inp : IncGDDInput) :
    ProbComp IncGDDState1 := do
  let m := P.m inp.secParam
  let β := P.β inp.secParam
  let j ← sampleModNat (Nat.clog 2 m + inp.extraBits) m
  let sgn ← ProbComp.uniform Bool
  let idx ← sampleModNat (Nat.clog 2 β + inp.extraBits) β
  pure ⟨inp, j, sgn, idx⟩

private theorem isPPTOn_stageSampleGuess {P : SISParams} (hP : MR07ParamPolyTime P) :
    IsPPTOn IncGDDInput.enc IncGDDState1.enc (stageSampleGuess P) := by
  have hκ : ComputableInPolyTime IncGDDInput.secParam IncGDDInput.enc encUnary := by fun_prop
  have hextra : ComputableInPolyTime IncGDDInput.extraBits IncGDDInput.enc encUnary := by fun_prop
  have hm := hP.hm.comp hκ
  have hβ := hP.hβ.comp hκ
  have hj : IsPPTOn IncGDDInput.enc encNat
      (fun inp => sampleModNat (Nat.clog 2 (P.m inp.secParam) + inp.extraBits)
        (P.m inp.secParam)) :=
    isPPTOn_sampleModNat
      (unary_add' (binary_clog_two.comp (unary_to_binary.comp hm)) hextra)
      (unary_to_binary.comp hm)
  have hsgn : IsPPTOn (encPair IncGDDInput.enc encNat) encBool (fun _ => ProbComp.uniform Bool) :=
    isPPTOn_uniform_bool _
  have hidx : IsPPTOn (encPair (encPair IncGDDInput.enc encNat) encBool) encNat
      (fun p : (IncGDDInput × ℕ) × Bool =>
        sampleModNat (Nat.clog 2 (P.β p.1.1.secParam) + p.1.1.extraBits)
          (P.β p.1.1.secParam)) := by
    have hp := (fst IncGDDInput.enc encNat).comp (fst (encPair IncGDDInput.enc encNat) encBool)
    exact isPPTOn_sampleModNat
      (unary_add' (binary_clog_two.comp (unary_to_binary.comp (hβ.comp hp))) (hextra.comp hp))
      (unary_to_binary.comp (hβ.comp hp))
  have hpack : ComputableInPolyTime
      (fun p : ((IncGDDInput × ℕ) × Bool) × ℕ => IncGDDState1.mk p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair IncGDDInput.enc encNat) encBool) encNat) IncGDDState1.enc := by
    let enc1 := encPair IncGDDInput.enc encNat
    let enc2 := encPair enc1 encBool
    have hp1 := fst enc2 encNat
    have hp11 := (fst enc1 encBool).comp hp1
    exact IncGDDState1.enc_mk_polyTime
      ((fst IncGDDInput.enc encNat).comp hp11)
      ((snd IncGDDInput.enc encNat).comp hp11)
      ((snd enc1 encBool).comp hp1)
      (snd enc2 encNat)
  have h := hj.keep_input.bind (hsgn.keep_input.bind (hidx.keep_input.map hpack))
  refine h.congr fun inp => ?_
  simp only [stageSampleGuess, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

private noncomputable def stageSampleLattices (P : SISParams) (st : IncGDDState1) :
    ProbComp IncGDDState2 := do
  let inp := st.inp
  let κ := inp.secParam
  let n := P.n κ
  let m := P.m κ
  let q := P.q κ
  let β := P.β κ
  let α : ℤ := if st.sgn then (st.idx + 1 : ℤ) else -((st.idx + 1 : ℤ))
  let sSq : ℚ := inp.rSq * Rat.divInt 4 ((β * β * n : ℕ) : ℤ)
  let scaledTarget : List ℚ := inp.target.map fun x => Rat.divInt (-1) α * x
  let cys ← (List.range m).mapM fun i =>
    sampleGridGaussian
      ⟨n, q, inp.basisB, sSq,
        if i = st.j then scaledTarget else List.replicate n 0,
        inp.tail, inp.prec, inp.maxTrials⟩
  let vs ← (List.range m).mapM fun _ =>
    sampleQuotientModS ⟨n, inp.basisB, inp.basisS, inp.extraBits⟩
  pure ⟨inp, cys, vs⟩

private theorem isPPTOn_stageSampleLattices {P : SISParams} (hP : MR07ParamPolyTime P) :
    IsPPTOn IncGDDState1.enc IncGDDState2.enc (stageSampleLattices P) := by
  have hinp : ComputableInPolyTime IncGDDState1.inp IncGDDState1.enc IncGDDInput.enc := by fun_prop
  have hj : ComputableInPolyTime IncGDDState1.j IncGDDState1.enc encNat := by fun_prop
  have hsgn : ComputableInPolyTime IncGDDState1.sgn IncGDDState1.enc encBool := by fun_prop
  have hidx : ComputableInPolyTime IncGDDState1.idx IncGDDState1.enc encNat := by fun_prop
  have hκ : ComputableInPolyTime (fun st : IncGDDState1 => st.inp.secParam)
      IncGDDState1.enc encUnary := by fun_prop
  have hn := hP.hn.comp hκ
  have hm := hP.hm.comp hκ
  have hq := hP.hq.comp hκ
  have hβ := hP.hβ.comp hκ
  have hα : ComputableInPolyTime
      (fun st : IncGDDState1 => if st.sgn then (st.idx + 1 : ℤ) else -((st.idx + 1 : ℤ)))
      IncGDDState1.enc encIntBin := by
    have hpos := intBin_natCast.comp (binary_add' hidx (const 1))
    exact hsgn.ite' hpos (intBin_neg.comp hpos)
  have hsSq : ComputableInPolyTime
      (fun st : IncGDDState1 => st.inp.rSq * Rat.divInt 4
        ((P.β st.inp.secParam * P.β st.inp.secParam * P.n st.inp.secParam : ℕ) : ℤ))
      IncGDDState1.enc encRat := by
    have hrSq : ComputableInPolyTime (fun st : IncGDDState1 => st.inp.rSq)
        IncGDDState1.enc encRat := by fun_prop
    have hden := intBin_natCast.comp (unary_to_binary.comp (unary_mul' (unary_mul' hβ hβ) hn))
    exact rat_mul' hrSq (rat_divInt' (const 4) hden)
  have hscaled : ComputableInPolyTime
      (fun st : IncGDDState1 => st.inp.target.map fun x =>
        Rat.divInt (-1) (if st.sgn then (st.idx + 1 : ℤ) else -((st.idx + 1 : ℤ))) * x)
      IncGDDState1.enc (encList encRat) :=
    mapWithInput (by fun_prop : ComputableInPolyTime (fun st : IncGDDState1 => st.inp.target)
      IncGDDState1.enc (encList encRat))
      (rat_mul' (rat_divInt' (const (-1)) (hα.comp (fst IncGDDState1.enc encRat)))
        (snd IncGDDState1.enc encRat))
  have hcys : IsPPTOn IncGDDState1.enc
      (encList (encPair (encList encIntBin) (encList encIntBin)))
      (fun st : IncGDDState1 =>
        let inp := st.inp
        let α : ℤ := if st.sgn then (st.idx + 1 : ℤ) else -((st.idx + 1 : ℤ))
        let sSq : ℚ := inp.rSq * Rat.divInt 4
          ((P.β inp.secParam * P.β inp.secParam * P.n inp.secParam : ℕ) : ℤ)
        let scaledTarget : List ℚ := inp.target.map fun x => Rat.divInt (-1) α * x
        (List.range (P.m inp.secParam)).mapM fun i =>
          sampleGridGaussian
            ⟨P.n inp.secParam, P.q inp.secParam, inp.basisB, sSq,
              if i = st.j then scaledTarget else List.replicate (P.n inp.secParam) 0,
              inp.tail, inp.prec, inp.maxTrials⟩) := by
    have hgridInp : ComputableInPolyTime
        (fun q : IncGDDState1 × ℕ =>
          let inp := q.1.inp
          let α : ℤ := if q.1.sgn then (q.1.idx + 1 : ℤ) else -((q.1.idx + 1 : ℤ))
          let sSq : ℚ := inp.rSq * Rat.divInt 4
            ((P.β inp.secParam * P.β inp.secParam * P.n inp.secParam : ℕ) : ℤ)
          let scaledTarget : List ℚ := inp.target.map fun x => Rat.divInt (-1) α * x
          GridSampleInput.mk (P.n inp.secParam) (P.q inp.secParam) inp.basisB sSq
            (if q.2 = q.1.j then scaledTarget else List.replicate (P.n inp.secParam) 0)
            inp.tail inp.prec inp.maxTrials)
        (encPair IncGDDState1.enc encUnary) GridSampleInput.enc := by
      have hq1 := fst IncGDDState1.enc encUnary
      have hq2 := snd IncGDDState1.enc encUnary
      have hinp' := hinp.comp hq1
      have hcond := decide_eq' (unary_to_binary.comp hq2) (hj.comp hq1)
      have hn' := hn.comp hq1
      have hq' := hq.comp hq1
      have hB' : ComputableInPolyTime (fun q : IncGDDState1 × ℕ => q.1.inp.basisB)
          (encPair IncGDDState1.enc encUnary) IntTable.enc :=
        (by fun_prop : ComputableInPolyTime IncGDDInput.basisB IncGDDInput.enc IntTable.enc).comp
          hinp'
      have hrep : ComputableInPolyTime
          (fun q : IncGDDState1 × ℕ => List.replicate (P.n q.1.inp.secParam) (0 : ℚ))
          (encPair IncGDDState1.enc encUnary) (encList encRat) :=
        ComputableInPolyTime.replicate hn' (.const (0 : ℚ))
      have htarget := ite_decide hcond (hscaled.comp hq1) hrep
      have hsSq' := hsSq.comp hq1
      have htail' : ComputableInPolyTime (fun q : IncGDDState1 × ℕ => q.1.inp.tail)
          (encPair IncGDDState1.enc encUnary) encUnary :=
        (by fun_prop : ComputableInPolyTime IncGDDInput.tail IncGDDInput.enc encUnary).comp hinp'
      have hprec' : ComputableInPolyTime (fun q : IncGDDState1 × ℕ => q.1.inp.prec)
          (encPair IncGDDState1.enc encUnary) encUnary :=
        (by fun_prop : ComputableInPolyTime IncGDDInput.prec IncGDDInput.enc encUnary).comp hinp'
      have hmaxT' : ComputableInPolyTime (fun q : IncGDDState1 × ℕ => q.1.inp.maxTrials)
          (encPair IncGDDState1.enc encUnary) encUnary :=
        (by fun_prop : ComputableInPolyTime IncGDDInput.maxTrials IncGDDInput.enc encUnary).comp
          hinp'
      exact GridSampleInput.enc_mk_polyTime hn' hq' hB' hsSq' htarget htail' hprec' hmaxT'
    exact IsPPTOn.mapMWith (isPPTOn_sampleGridGaussian.preprocess hgridInp) (unary_range' hm)
  let encCY := encList (encPair (encList encIntBin) (encList encIntBin))
  have hvs : IsPPTOn (encPair IncGDDState1.enc encCY) (encList (encList encIntBin))
      (fun p : IncGDDState1 × List (List ℤ × List ℤ) =>
        (List.range (P.m p.1.inp.secParam)).mapM fun _ =>
          sampleQuotientModS
            ⟨P.n p.1.inp.secParam, p.1.inp.basisB, p.1.inp.basisS, p.1.inp.extraBits⟩) := by
    have hp1 := fst IncGDDState1.enc encCY
    have hqInp : ComputableInPolyTime
        (fun q : (IncGDDState1 × List (List ℤ × List ℤ)) × ℕ =>
          QuotientSampleInput.mk (P.n q.1.1.inp.secParam) q.1.1.inp.basisB
            q.1.1.inp.basisS q.1.1.inp.extraBits)
        (encPair (encPair IncGDDState1.enc encCY) encUnary) QuotientSampleInput.enc := by
      have hst := hp1.comp (fst (encPair IncGDDState1.enc encCY) encUnary)
      have hinp' := hinp.comp hst
      exact QuotientSampleInput.enc_mk_polyTime (hn.comp hst)
        ((by fun_prop : ComputableInPolyTime IncGDDInput.basisB IncGDDInput.enc IntTable.enc).comp
          hinp')
        ((by fun_prop : ComputableInPolyTime IncGDDInput.basisS IncGDDInput.enc IntTable.enc).comp
          hinp')
        ((by fun_prop : ComputableInPolyTime IncGDDInput.extraBits IncGDDInput.enc encUnary).comp
          hinp')
    exact IsPPTOn.mapMWith (isPPTOn_sampleQuotientModS.preprocess hqInp)
      (unary_range' (hm.comp hp1))
  have hpack : ComputableInPolyTime
      (fun p : (IncGDDState1 × List (List ℤ × List ℤ)) × List (List ℤ) =>
        IncGDDState2.mk p.1.1.inp p.1.2 p.2)
      (encPair (encPair IncGDDState1.enc encCY) (encList (encList encIntBin)))
      IncGDDState2.enc := by
    have hp1 := fst (encPair IncGDDState1.enc encCY) (encList (encList encIntBin))
    exact IncGDDState2.enc_mk_polyTime
      (hinp.comp ((fst IncGDDState1.enc encCY).comp hp1))
      ((snd IncGDDState1.enc encCY).comp hp1)
      (snd (encPair IncGDDState1.enc encCY) (encList (encList encIntBin)))
  have h := hcys.keep_input.bind (hvs.keep_input.map hpack)
  refine h.congr fun st => ?_
  simp only [stageSampleLattices, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]

private def stageCols (P : SISParams) (st : IncGDDState2) : List (List ℤ × List ℕ) :=
  (List.range (P.m st.inp.secParam)).map fun c =>
    combineColInt (P.n st.inp.secParam) (P.q st.inp.secParam) st.inp.basisS
      (st.vs.getD c []) (st.cys.getD c ([], [])).1

private noncomputable def stageSolveAndCombine (P : SISParams) (F : P.Solver) (st : IncGDDState2) :
    ProbComp (List ℤ) := do
  let inp := st.inp
  let κ := inp.secParam
  let n := P.n κ
  let m := P.m κ
  let q := P.q κ
  let cols := stageCols P st
  let rows := combineMatrixRowsInt n m cols
  let z ← callSISSolver P F κ rows
  let ys := st.cys.map Prod.snd
  pure (combineOutputInt n m q inp.basisS cols st.vs ys z)

private theorem isPPTOn_stageSolveAndCombine {P : SISParams} (hP : MR07ParamPolyTime P)
    {F : P.Solver} (hF : F.IsPPT) :
    IsPPTOn IncGDDState2.enc (encList encIntBin) (stageSolveAndCombine P F) := by
  have hκ : ComputableInPolyTime (fun st : IncGDDState2 => st.inp.secParam)
      IncGDDState2.enc encUnary := by fun_prop
  have hn := hP.hn.comp hκ
  have hm := hP.hm.comp hκ
  have hq := hP.hq.comp hκ
  have hcols : ComputableInPolyTime (stageCols P)
      IncGDDState2.enc (encList (encPair (encList encIntBin) (encList encNat))) := by
    unfold stageCols
    have harg : ComputableInPolyTime
        (fun q : IncGDDState2 × ℕ =>
          CombineColArg.mk (P.n q.1.inp.secParam) (P.q q.1.inp.secParam) q.1.inp.basisS
            (q.1.vs.getD q.2 []) (q.1.cys.getD q.2 ([], [])).1)
        (encPair IncGDDState2.enc encUnary) CombineColArg.enc := by
      have hq1 := fst IncGDDState2.enc encUnary
      have hq2 := snd IncGDDState2.enc encUnary
      have hinp2 : ComputableInPolyTime IncGDDState2.inp IncGDDState2.enc IncGDDInput.enc := by
        fun_prop
      have hS' : ComputableInPolyTime (fun q : IncGDDState2 × ℕ => q.1.inp.basisS)
          (encPair IncGDDState2.enc encUnary) IntTable.enc :=
        (by fun_prop : ComputableInPolyTime IncGDDInput.basisS IncGDDInput.enc IntTable.enc).comp
          (hinp2.comp hq1)
      have hvs2 : ComputableInPolyTime IncGDDState2.vs IncGDDState2.enc
          (encList (encList encIntBin)) := by fun_prop
      have hcys2 : ComputableInPolyTime IncGDDState2.cys IncGDDState2.enc
          (encList (encPair (encList encIntBin) (encList encIntBin))) := by fun_prop
      have hvs' := listGetDWithInput (hvs2.comp hq1) hq2 []
      have hu' := (fst (encList encIntBin) (encList encIntBin)).comp
        (listGetDWithInput (hcys2.comp hq1) hq2 ([], []))
      exact CombineColArg.enc_mk_polyTime (hn.comp hq1) (hq.comp hq1) hS' hvs' hu'
    exact mapWithInput (unary_range' hm) (computableInPolyTime_combineColInt.comp harg)
  have hrows : ComputableInPolyTime
      (fun st : IncGDDState2 =>
        combineMatrixRowsInt (P.n st.inp.secParam) (P.m st.inp.secParam) (stageCols P st))
      IncGDDState2.enc (encList (encList encNat)) :=
    computableInPolyTime_combineMatrixRowsInt.comp (CombineRowsArg.enc_mk_polyTime hn hm hcols)
  have hz : IsPPTOn IncGDDState2.enc (encList encIntBin)
      (fun st : IncGDDState2 =>
        callSISSolver P F st.inp.secParam
          (combineMatrixRowsInt (P.n st.inp.secParam) (P.m st.inp.secParam) (stageCols P st))) :=
    (isPPTOn_callSISSolver hP hF).preprocess (hκ.prod hrows)
  have harg : ComputableInPolyTime
      (fun p : IncGDDState2 × List ℤ =>
        CombineOutArg.mk (P.n p.1.inp.secParam) (P.m p.1.inp.secParam) (P.q p.1.inp.secParam)
          p.1.inp.basisS (stageCols P p.1) p.1.vs (p.1.cys.map Prod.snd) p.2)
      (encPair IncGDDState2.enc (encList encIntBin)) CombineOutArg.enc := by
    have hp1 := fst IncGDDState2.enc (encList encIntBin)
    have hinp2 : ComputableInPolyTime IncGDDState2.inp IncGDDState2.enc IncGDDInput.enc := by
      fun_prop
    have hS' : ComputableInPolyTime (fun p : IncGDDState2 × List ℤ => p.1.inp.basisS)
        (encPair IncGDDState2.enc (encList encIntBin)) IntTable.enc :=
      (by fun_prop : ComputableInPolyTime IncGDDInput.basisS IncGDDInput.enc IntTable.enc).comp
        (hinp2.comp hp1)
    have hvs2 : ComputableInPolyTime IncGDDState2.vs IncGDDState2.enc
        (encList (encList encIntBin)) := by fun_prop
    have hcys2 : ComputableInPolyTime IncGDDState2.cys IncGDDState2.enc
        (encList (encPair (encList encIntBin) (encList encIntBin))) := by fun_prop
    have hys' := (ComputableInPolyTime.map (snd (encList encIntBin) (encList encIntBin))).comp
      (hcys2.comp hp1)
    exact CombineOutArg.enc_mk_polyTime (hn.comp hp1) (hm.comp hp1) (hq.comp hp1) hS'
      (hcols.comp hp1) (hvs2.comp hp1) hys' (snd IncGDDState2.enc (encList encIntBin))
  have hout := computableInPolyTime_combineOutputInt.comp harg
  have h := hz.keep_input.map hout
  refine h.congr fun st => ?_
  simp only [stageSolveAndCombine, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]

/-- Unconditional strict-PPT certificate for `singleIncGDDCall`. -/
theorem isPPTOn_singleIncGDDCall {P : SISParams} (hP : MR07ParamPolyTime P)
    {F : P.Solver} (hF : F.IsPPT) :
    IsPPTOn IncGDDInput.enc (encList encIntBin) (singleIncGDDCall P F) := by
  have hκ : ComputableInPolyTime IncGDDInput.secParam IncGDDInput.enc encUnary := by fun_prop
  have hn := hP.hn.comp hκ
  have hm := hP.hm.comp hκ
  have hβ := hP.hβ.comp hκ
  have hguard : ComputableInPolyTime
      (fun inp : IncGDDInput =>
        decide (P.n inp.secParam = 0 ∨ P.m inp.secParam = 0 ∨ P.β inp.secParam = 0))
      IncGDDInput.enc encBool :=
    (bool_or' (decide_eq' hn (const 0))
      (bool_or' (decide_eq' hm (const 0)) (decide_eq' hβ (const 0)))).of_enc_eq fun _ => by simp
  have hfallback : IsPPTOn IncGDDInput.enc (encList encIntBin)
      (fun inp => pure (List.replicate (P.n inp.secParam) (0 : ℤ))) :=
    (by fun_prop : ComputableInPolyTime
      (fun inp : IncGDDInput => List.replicate (P.n inp.secParam) (0 : ℤ))
      IncGDDInput.enc (encList encIntBin)).isPPTOn
  have hmain : IsPPTOn IncGDDInput.enc (encList encIntBin)
      (fun inp => stageSampleGuess P inp >>= fun st1 =>
        stageSampleLattices P st1 >>= stageSolveAndCombine P F) :=
    (isPPTOn_stageSampleGuess hP).bind
      ((isPPTOn_stageSampleLattices hP).bind (isPPTOn_stageSolveAndCombine hP hF))
  have hcomb := IsPPTOn.ite hguard hfallback hmain
  refine hcomb.congr fun inp => ?_
  unfold singleIncGDDCall stageSampleGuess stageSampleLattices stageSolveAndCombine stageCols
  by_cases h : P.n inp.secParam = 0 ∨ P.m inp.secParam = 0 ∨ P.β inp.secParam = 0
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, bind_assoc, pure_bind]

/-! ### 5. Exact Algebraic & Sampler-List Bridges -/

private theorem intTableToRatTable_toMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    (intTableToRatTable (RowTable.ofMatrix M)).toMatrix = M.map (Int.cast : ℤ → ℚ) := by
  ext i j
  simp [intTableToRatTable, RowTable.toMatrix, RowTable.entry, RowTable.ofMatrix,
    List.getD_eq_getElem?_getD]
  rfl

private theorem intTableMulVec_getD {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (v : List ℤ) (r : Fin n) :
    (intTableMulVec (RowTable.ofMatrix M) v).getD r.1 0 =
      (M *ᵥ fun c : Fin n => v.getD c.1 0) r := by
  have hr : r.val < (intTableMulVec (RowTable.ofMatrix M) v).length := by
    simp [intTableMulVec, r.isLt]
  rw [List.getD_eq_getElem _ _ hr]
  simp only [intTableMulVec, RowTable.numRows_ofMatrix, RowTable.numCols_ofMatrix,
    List.getElem_map, List.getElem_range, ListMatrix.dotProduct_eq, Matrix.mulVec, dotProduct,
    ofList_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hent : ((RowTable.ofMatrix M).rows.getD r.val []).getD c.val 0 = M r c :=
    RowTable.entry_ofMatrix_of_lt M r.isLt c.isLt
  rw [hent]

private theorem matrix_map_intCast_det_ne_zero {n : ℕ} {R : Type*} [CommRing R] [CharZero R]
    {M : Matrix (Fin n) (Fin n) ℤ} (hM : M.det ≠ 0) :
    (M.map (Int.cast : ℤ → R)).det ≠ 0 := by
  have hdet : (M.map (Int.cast : ℤ → R)).det = (M.det : R) :=
    (RingHom.map_det (Int.castRingHom R) M).symm
  rw [hdet]
  exact Int.cast_ne_zero.mpr hM

private theorem ratSolve_intMatrix_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} (hM : M.det ≠ 0)
    (rhs : List ℚ) :
    let sol := (ratSolve ⟨intTableToRatTable (RowTable.ofMatrix M), rhs⟩).solution.getD
      (List.replicate n 0)
    ∀ i : Fin n,
      (sol.getD i.1 0 : ℝ) =
        ((M.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ fun r : Fin n => (rhs.getD r.1 0 : ℝ)) i := by
  intro sol
  let MQ : Matrix (Fin n) (Fin n) ℚ := M.map (Int.cast : ℤ → ℚ)
  let MR : Matrix (Fin n) (Fin n) ℝ := M.map (Int.cast : ℤ → ℝ)
  have hMQ_unit : IsUnit MQ.det := isUnit_iff_ne_zero.mpr (matrix_map_intCast_det_ne_zero hM)
  have hMR_unit : IsUnit MR.det := isUnit_iff_ne_zero.mpr (matrix_map_intCast_det_ne_zero hM)
  let bQ : Fin n → ℚ := fun r => rhs.getD r.1 0
  have hex : ∃ x : Fin n → ℚ, MQ *ᵥ x = bQ :=
    ⟨MQ⁻¹ *ᵥ bQ,
      by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv MQ hMQ_unit, Matrix.one_mulVec]⟩
  have hspec := ratSolve_spec ⟨intTableToRatTable (RowTable.ofMatrix M), rhs⟩
  dsimp only at hspec
  have hmat : (intTableToRatTable (RowTable.ofMatrix M)).toMatrix = MQ :=
    intTableToRatTable_toMatrix M
  have hne_none :
      (ratSolve ⟨intTableToRatTable (RowTable.ofMatrix M), rhs⟩).solution ≠ none := by
    intro hnone
    exact (hspec.2.mp hnone) (by rwa [hmat])
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne_none
  have hsol_eq : sol = x := by simp [sol, hx]
  have hx_mul : MQ *ᵥ (fun j : Fin n => x.getD j.1 0) = bQ := by
    have h := (hspec.1 x hx).2
    rwa [hmat] at h
  have hR_mul : MR *ᵥ (fun j : Fin n => (sol.getD j.1 0 : ℝ)) =
      fun r : Fin n => (rhs.getD r.1 0 : ℝ) := by
    funext r
    have hr := congrFun hx_mul r
    have hcast := congrArg (Rat.cast : ℚ → ℝ) hr
    simp only [MQ, Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul,
      Rat.cast_intCast, bQ] at hcast
    simpa [MR, Matrix.mulVec, dotProduct, hsol_eq] using hcast
  have hR_inv : (fun j : Fin n => (sol.getD j.1 0 : ℝ)) =
      MR⁻¹ *ᵥ fun r : Fin n => (rhs.getD r.1 0 : ℝ) := by
    calc (fun j : Fin n => (sol.getD j.1 0 : ℝ))
        = (MR⁻¹ * MR) *ᵥ fun j : Fin n => (sol.getD j.1 0 : ℝ) := by
          rw [Matrix.nonsing_inv_mul MR hMR_unit, Matrix.one_mulVec]
      _ = MR⁻¹ *ᵥ (MR *ᵥ fun j : Fin n => (sol.getD j.1 0 : ℝ)) :=
          (Matrix.mulVec_mulVec _ _ _).symm
      _ = MR⁻¹ *ᵥ fun r : Fin n => (rhs.getD r.1 0 : ℝ) := by rw [hR_mul]
  intro i
  exact congrFun hR_inv i

private theorem combineColInt_eq_combineColumn {n q : ℕ} (hq : 0 < q)
    (B S : Matrix (Fin n) (Fin n) ℤ) (hS : S.det ≠ 0)
    (v_rep : SublatticeQuot B S) (c_rep : GridRep B q) (v u : List ℤ)
    (hv : ∀ r : Fin n, (v.getD r.1 0 : ℝ) = WithLp.ofLp v_rep.toVec r)
    (hu : ∀ r : Fin n, (u.getD r.1 0 : ℝ) / (q : ℝ) = WithLp.ofLp c_rep.toVec r) :
    let res := combineColInt n q (RowTable.ofMatrix S) v u
    (∀ r : Fin n, (res.1.getD r.1 0 : ℝ) - WithLp.ofLp v_rep.toVec r =
        WithLp.ofLp (c_rep.toVec - (combineColumn B S q v_rep c_rep).1.toVec) r) ∧
    (∀ r : Fin n, res.2.getD r.1 0 = ((combineColumn B S q v_rep c_rep).2 r).val) := by
  intro res
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hSR_unit : IsUnit (S.map (Int.cast : ℤ → ℝ)).det :=
    isUnit_iff_ne_zero.mpr (matrix_map_intCast_det_ne_zero hS)
  let rhs : List ℚ := (List.range n).map fun r =>
    Rat.divInt ((q : ℤ) * v.getD r 0 + u.getD r 0) (q : ℤ)
  have hrhs_R : ∀ r : Fin n, (rhs.getD r.1 0 : ℝ) =
      WithLp.ofLp (v_rep.toVec + c_rep.toVec) r := by
    intro r
    have hr : rhs.getD r.1 0 = Rat.divInt ((q : ℤ) * v.getD r.1 0 + u.getD r.1 0) (q : ℤ) := by
      simp [rhs, List.getD_eq_getElem?_getD, r.isLt]
    rw [hr, Rat.divInt_eq_div]
    push_cast
    rw [PiLp.add_apply, ← hv r, ← hu r]
    field_simp [hqR]
  let sol : List ℚ := (ratSolve ⟨intTableToRatTable (RowTable.ofMatrix S), rhs⟩).solution.getD
    (List.replicate n 0)
  have hsolR : ∀ j : Fin n, (sol.getD j.1 0 : ℝ) =
      ((S.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ WithLp.ofLp (v_rep.toVec + c_rep.toVec)) j := by
    intro j
    rw [ratSolve_intMatrix_eq hS rhs j]
    congr 1; funext r; exact hrhs_R r
  let k : List ℤ := (List.range n).map fun r => (sol.getD r 0).floor
  have hk_eq : ∀ j : Fin n, (k.getD j.1 0 : ℝ) =
      (Int.floor (((S.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ
        WithLp.ofLp (v_rep.toVec + c_rep.toVec)) j) : ℝ) := by
    intro j
    have hj : k.getD j.1 0 = Int.floor (sol.getD j.1 0) := by
      simp [k, List.getD_eq_getElem?_getD, j.isLt]; rfl
    rw [hj, ← hsolR j, Rat.floor_cast]
  let sk : List ℤ := intTableMulVec (RowTable.ofMatrix S) k
  have hsk_eq : ∀ r : Fin n, (sk.getD r.1 0 : ℝ) =
      ((S.map (Int.cast : ℤ → ℝ)) *ᵥ fun j : Fin n => (k.getD j.1 0 : ℝ)) r := by
    intro r
    have hr := intTableMulVec_getD S k r
    have hcast := congrArg (Int.cast : ℤ → ℝ) hr
    simpa [sk, Matrix.mulVec, dotProduct] using hcast
  have hw_eq : ∀ r : Fin n,
      WithLp.ofLp (combineColumn B S q v_rep c_rep).1.toVec r =
        WithLp.ofLp v_rep.toVec r + WithLp.ofLp c_rep.toVec r - (sk.getD r.1 0 : ℝ) := by
    intro r
    rw [combineColumn_fst_toVec hS hq]
    unfold modParallelepiped
    dsimp only
    change ((S.map (Int.cast : ℤ → ℝ)) *ᵥ
      (((S.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ WithLp.ofLp (v_rep.toVec + c_rep.toVec)) -
        fun j => (Int.floor (((S.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ
          WithLp.ofLp (v_rep.toVec + c_rep.toVec)) j) : ℝ))) r = _
    rw [Matrix.mulVec_sub, Pi.sub_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hSR_unit, Matrix.one_mulVec]
    have h2 : ((S.map (Int.cast : ℤ → ℝ)) *ᵥ fun j =>
        (Int.floor (((S.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ
          WithLp.ofLp (v_rep.toVec + c_rep.toVec)) j) : ℝ)) r = (sk.getD r.1 0 : ℝ) := by
      rw [hsk_eq r]; congr 1; funext j; rw [hk_eq j]
    rw [h2]
    rfl
  constructor
  · intro r
    rw [PiLp.sub_apply, hw_eq r]
    change (sk.getD r.1 0 : ℝ) - _ = _
    ring
  · intro r
    have hSinv_w :
        ((S.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ
          WithLp.ofLp (combineColumn B S q v_rep c_rep).1.toVec) r =
        ((sol.getD r.1 0 - (k.getD r.1 0 : ℚ) : ℚ) : ℝ) := by
      rw [combineColumn_fst_toVec hS hq]
      unfold modParallelepiped
      dsimp only
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hSR_unit, Matrix.one_mulVec]
      push_cast
      rw [hsolR r, hk_eq r]
    have hsnd := combineColumn_snd_val hS hq v_rep c_rep r
    rw [hSinv_w] at hsnd
    have hq_prod :
        (q : ℝ) * ((sol.getD r.1 0 - (k.getD r.1 0 : ℚ) : ℚ) : ℝ) =
        (((q : ℚ) * (sol.getD r.1 0 - (k.getD r.1 0 : ℚ)) : ℚ) : ℝ) := by
      push_cast; rfl
    rw [hq_prod, Rat.floor_cast] at hsnd
    have hki : k.getD r.1 0 = Int.floor (sol.getD r.1 0) := by
      simp [k, List.getD_eq_getElem?_getD, r.isLt]; rfl
    have hfrac_nonneg : (0 : ℚ) ≤ sol.getD r.1 0 - (k.getD r.1 0 : ℚ) := by
      rw [hki, sub_nonneg]; exact Int.floor_le _
    have hfrac_lt : sol.getD r.1 0 - (k.getD r.1 0 : ℚ) < 1 := by
      rw [hki, sub_lt_iff_lt_add']; exact Int.lt_floor_add_one _
    have hprod_nonneg : (0 : ℚ) ≤ (q : ℚ) * (sol.getD r.1 0 - (k.getD r.1 0 : ℚ)) :=
      mul_nonneg (Nat.cast_nonneg q) hfrac_nonneg
    have hprod_lt : (q : ℚ) * (sol.getD r.1 0 - (k.getD r.1 0 : ℚ)) < (q : ℚ) := by
      calc (q : ℚ) * (sol.getD r.1 0 - (k.getD r.1 0 : ℚ))
          < (q : ℚ) * 1 := mul_lt_mul_of_pos_left hfrac_lt (by exact_mod_cast hq)
        _ = (q : ℚ) := mul_one _
    have hfl_nonneg : 0 ≤ Int.floor ((q : ℚ) * (sol.getD r.1 0 - (k.getD r.1 0 : ℚ))) :=
      Int.floor_nonneg.mpr hprod_nonneg
    have hfl_lt : Int.floor ((q : ℚ) * (sol.getD r.1 0 - (k.getD r.1 0 : ℚ))) < (q : ℤ) :=
      Int.floor_lt.mpr (by exact_mod_cast hprod_lt)
    have htoNat_lt :
        (Int.floor ((q : ℚ) * (sol.getD r.1 0 - (k.getD r.1 0 : ℚ)))).toNat < q := by
      omega
    have hres_r : res.2.getD r.1 0 =
        (Int.floor ((q : ℚ) * (sol.getD r.1 0 - (k.getD r.1 0 : ℚ)))).toNat % q := by
      simp [res, combineColInt, rhs, sol, k, List.getD_eq_getElem?_getD, r.isLt]; rfl
    rw [hres_r, Nat.mod_eq_of_lt htoNat_lt]
    have hcast_eq :
        ((((Int.floor ((q : ℚ) * (sol.getD r.1 0 - (k.getD r.1 0 : ℚ)))).toNat : ℕ) : ℤ)) =
        (((combineColumn B S q v_rep c_rep).2 r).val : ℤ) := by
      rw [Int.toNat_of_nonneg hfl_nonneg]
      exact hsnd.symm
    exact_mod_cast hcast_eq

private theorem makeSISInput_combineMatrix_eq {P : SISParams} {κ : ℕ}
    (B S : Matrix (Fin (P.n κ)) (Fin (P.n κ)) ℤ) (hS : S.det ≠ 0)
    (V : Fin (P.m κ) → SublatticeQuot B S) (C : Fin (P.m κ) → GridRep B (P.q κ))
    (vs us : List (List ℤ))
    (hvs : ∀ (c : Fin (P.m κ)) (r : Fin (P.n κ)),
      ((vs.getD c.1 []).getD r.1 0 : ℝ) = WithLp.ofLp (V c).toVec r)
    (hus : ∀ (c : Fin (P.m κ)) (r : Fin (P.n κ)),
      ((us.getD c.1 []).getD r.1 0 : ℝ) / (P.q κ : ℝ) = WithLp.ofLp (C c).toVec r) :
    let cols := (List.range (P.m κ)).map fun c =>
      combineColInt (P.n κ) (P.q κ) (RowTable.ofMatrix S) (vs.getD c []) (us.getD c [])
    (makeSISInput P κ (combineMatrixRowsInt (P.n κ) (P.m κ) cols)).matrix =
      combineMatrix B S (P.q κ) V C := by
  intro cols
  have hq : 0 < P.q κ := NeZero.pos (P.q κ)
  change Matrix.of (fun i j : Fin _ =>
      (((combineMatrixRowsInt (P.n κ) (P.m κ) cols).getD i.1 []).getD j.1 0 : ZMod (P.q κ))) =
    combineMatrix B S (P.q κ) V C
  ext r c
  have hc : cols.getD c.1 ([], []) =
      combineColInt (P.n κ) (P.q κ) (RowTable.ofMatrix S) (vs.getD c.1 []) (us.getD c.1 []) := by
    simp [cols, List.getD_eq_getElem?_getD, c.isLt]
  have hcol2 := (combineColInt_eq_combineColumn hq B S hS (V c) (C c) _ _ (hvs c) (hus c)).2 r
  have hrow : ((combineMatrixRowsInt (P.n κ) (P.m κ) cols).getD r.1 []).getD c.1 0 =
      (cols.getD c.1 ([], [])).2.getD r.1 0 := by
    simp [combineMatrixRowsInt, List.getD_eq_getElem?_getD, r.isLt, c.isLt]
  simp only [Matrix.of_apply, hrow, hc, hcol2, ZMod.natCast_zmod_val]
  rfl

private theorem combineOutputInt_eq_combineOutput_sub {n m q : ℕ} (hq : 0 < q)
    (B S : Matrix (Fin n) (Fin n) ℤ) (hS : S.det ≠ 0)
    (V : Fin m → SublatticeQuot B S) (C : Fin m → GridRep B q) (Y : Fin m → intLattice B)
    (vs us ys : List (List ℤ))
    (hvs : ∀ (c : Fin m) (r : Fin n),
      ((vs.getD c.1 []).getD r.1 0 : ℝ) = WithLp.ofLp (V c).toVec r)
    (hus : ∀ (c : Fin m) (r : Fin n),
      ((us.getD c.1 []).getD r.1 0 : ℝ) / (q : ℝ) = WithLp.ofLp (C c).toVec r)
    (hys : ∀ (c : Fin m) (r : Fin n),
      ((ys.getD c.1 []).getD r.1 0 : ℝ) = WithLp.ofLp (Y c : EuclideanSpace ℝ (Fin n)) r)
    (z : Fin m → ℤ) :
    let cols := (List.range m).map fun c =>
      combineColInt n q (RowTable.ofMatrix S) (vs.getD c []) (us.getD c [])
    let out := combineOutputInt n m q (RowTable.ofMatrix S) cols vs ys (List.ofFn z)
    listToEuclidean n out =
      combineOutput B S q V C z - ∑ c : Fin m, z c • (Y c : EuclideanSpace ℝ (Fin n)) := by
  intro cols out
  have hcol_spec : ∀ c : Fin m,
      (∀ r : Fin n,
        ((cols.getD c.1 ([], [])).1.getD r.1 0 : ℝ) - WithLp.ofLp (V c).toVec r =
          WithLp.ofLp ((C c).toVec - (combineColumn B S q (V c) (C c)).1.toVec) r) ∧
      (∀ r : Fin n,
        (cols.getD c.1 ([], [])).2.getD r.1 0 = ((combineColumn B S q (V c) (C c)).2 r).val) := by
    intro c
    have hc : cols.getD c.1 ([], []) =
        combineColInt n q (RowTable.ofMatrix S) (vs.getD c.1 []) (us.getD c.1 []) := by
      simp [cols, List.getD_eq_getElem?_getD, c.isLt]
    rw [hc]
    exact combineColInt_eq_combineColumn hq B S hS (V c) (C c) _ _ (hvs c) (hus c)
  set azDivQ : List ℤ := (List.range n).map fun r =>
    (Rat.divInt (((List.range m).map fun c =>
      (((cols.getD c ([], [])).2.getD r 0 : ℕ) : ℤ) * (List.ofFn z).getD c 0).sum) (q : ℤ)).floor
  have haz_eq : ∀ r : Fin n,
      azDivQ.getD r.1 0 =
        (((fun i j => (((combineColumn B S q (V j) (C j)).2 i).val : ℤ) :
          Matrix (Fin n) (Fin m) ℤ) *ᵥ z) r) / (q : ℤ) := by
    intro r
    have hr : azDivQ.getD r.1 0 =
        (((List.range m).map fun c =>
          (((cols.getD c ([], [])).2.getD r.1 0 : ℕ) : ℤ) * (List.ofFn z).getD c 0).sum) /
          (q : ℤ) := by
      simp only [azDivQ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range r.isLt,
        Option.map_some, Option.getD_some, rat_floor_divInt_eq_ediv _ hq]
    rw [hr]
    congr 1
    unfold Matrix.mulVec dotProduct
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem
    · simp
    · intro c hc1 hc2
      have hlt : c < m := by simpa using hc1
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
        List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
      simpa only [List.getD_eq_getElem?_getD] using
        congrArg (fun a : ℕ => (a : ℤ) * z ⟨c, hlt⟩) ((hcol_spec ⟨c, hlt⟩).2 r)
  ext r
  have hout_r : out.getD r.1 0 =
      (((List.range m).map fun c =>
        (List.ofFn z).getD c 0 * ((cols.getD c ([], [])).1.getD r.1 0 -
          (vs.getD c []).getD r.1 0 - (ys.getD c []).getD r.1 0)).sum) +
        (intTableMulVec (RowTable.ofMatrix S) azDivQ).getD r.1 0 := by
    simp [out, combineOutputInt, azDivQ, List.getD_eq_getElem?_getD, r.isLt]
  have hsAz_r : (intTableMulVec (RowTable.ofMatrix S) azDivQ).getD r.1 0 =
      (S *ᵥ fun k =>
        (((fun i j => (((combineColumn B S q (V j) (C j)).2 i).val : ℤ) :
          Matrix (Fin n) (Fin m) ℤ) *ᵥ z) k) / (q : ℤ)) r := by
    rw [intTableMulVec_getD S azDivQ r]
    congr 1; funext k; exact haz_eq k
  have hsum_eq :
      ((((List.range m).map fun c =>
          (List.ofFn z).getD c 0 * ((cols.getD c ([], [])).1.getD r.1 0 -
            (vs.getD c []).getD r.1 0 - (ys.getD c []).getD r.1 0)).sum : ℤ) : ℝ) =
      WithLp.ofLp ((∑ c : Fin m, z c • ((C c).toVec - (combineColumn B S q (V c) (C c)).1.toVec)) -
        ∑ c : Fin m, z c • (Y c : EuclideanSpace ℝ (Fin n))) r := by
    have hlist :
        ((List.range m).map fun c =>
          (List.ofFn z).getD c 0 * ((cols.getD c ([], [])).1.getD r.1 0 -
            (vs.getD c []).getD r.1 0 - (ys.getD c []).getD r.1 0)).sum =
        ∑ c : Fin m, z c * ((cols.getD c.1 ([], [])).1.getD r.1 0 -
          (vs.getD c.1 []).getD r.1 0 - (ys.getD c.1 []).getD r.1 0) := by
      rw [← List.sum_ofFn]
      congr 1
      apply List.ext_getElem
      · simp
      · intro c hc1 hc2
        have hlt : c < m := by simpa using hc1
        simp [List.getD_eq_getElem?_getD, hlt]
    rw [hlist, PiLp.sub_apply, WithLp.ofLp_sum, WithLp.ofLp_sum, Finset.sum_apply,
      Finset.sum_apply, ← Finset.sum_sub_distrib]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, PiLp.smul_apply, zsmul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hvs c r, hys c r, (hcol_spec c).1 r]
    ring
  change (out.getD r.1 0 : ℝ) = _
  rw [hout_r, Int.cast_add, hsum_eq, hsAz_r]
  unfold combineOutput
  simp only [PiLp.sub_apply, PiLp.add_apply]
  ring

/-! #### Coordinatewise specs of `gridPairToLists` and `sublatticeQuotToList` -/

private theorem modParallelepiped_sub_mem {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ intLattice B) :
    modParallelepiped B (x - y) = modParallelepiped B x := by
  obtain ⟨m, hm⟩ := (mem_intLattice_iff B y).1 hy
  let BR : Matrix (Fin n) (Fin n) ℝ := B.map Int.cast
  have hunit : IsUnit BR.det := isUnit_iff_ne_zero.mpr (matrix_map_intCast_det_ne_zero hB)
  have hy_vec : WithLp.ofLp y = BR *ᵥ fun j => (m j : ℝ) := by
    rw [hm]; funext i; simp [BR, Matrix.mulVec, dotProduct]
  have hinv : BR⁻¹ *ᵥ WithLp.ofLp (x - y) = BR⁻¹ *ᵥ WithLp.ofLp x + fun k => (-m k : ℝ) := by
    change BR⁻¹ *ᵥ (WithLp.ofLp x - WithLp.ofLp y) = _
    rw [Matrix.mulVec_sub, hy_vec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul BR hunit,
      Matrix.one_mulVec]
    funext k; simp [sub_eq_add_neg]
  unfold modParallelepiped
  dsimp only
  change WithLp.toLp 2 (BR *ᵥ fun k =>
    (BR⁻¹ *ᵥ WithLp.ofLp (x - y)) k - (Int.floor ((BR⁻¹ *ᵥ WithLp.ofLp (x - y)) k) : ℝ)) = _
  rw [hinv]
  congr 2; funext k
  have hfl : Int.floor ((BR⁻¹ *ᵥ WithLp.ofLp x) k + ((-m k : ℤ) : ℝ)) =
      Int.floor ((BR⁻¹ *ᵥ WithLp.ofLp x) k) + (-m k) := Int.floor_add_intCast _ _
  have hfl' : Int.floor ((BR⁻¹ *ᵥ WithLp.ofLp x) k + (-m k : ℝ)) =
      Int.floor ((BR⁻¹ *ᵥ WithLp.ofLp x) k) + (-m k) := by simpa using hfl
  rw [Pi.add_apply, hfl']
  push_cast
  ring

private theorem gridPairToLists_spec {n q : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : B.det ≠ 0) (hq : 0 < q) (gy : GridRep B q × intLattice B) (r : Fin n) :
    ((gridPairToLists gy).1.getD r.1 0 : ℝ) / (q : ℝ) = WithLp.ofLp gy.1.toVec r ∧
    ((gridPairToLists gy).2.getD r.1 0 : ℝ) =
      WithLp.ofLp (gy.2 : EuclideanSpace ℝ (Fin n)) r := by
  rcases gy with ⟨g, y⟩
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  let r' : List ℤ :=
    List.ofFn fun i : Fin n => (q : ℤ) * Int.floor (WithLp.ofLp y.1 i) - g.1 i
  have hr'_vec :
      ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i : Fin n => (r'.getD i.val 0 : ℝ)) =
        y.1 - g.toVec := by
    ext i
    have hi : r'.getD i.val 0 = (q : ℤ) * Int.floor (WithLp.ofLp y.1 i) - g.1 i := by
      simp [r', List.getD_eq_getElem?_getD, i.isLt]
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, GridRep.toVec, hi, Int.cast_sub,
      Int.cast_mul, Int.cast_natCast, intLattice_coord_eq_floor B y.2 i]
    field_simp [hqR.ne']
  obtain ⟨gy', hlist, hfst, hsnd⟩ :=
    gridReduceInt_exists_gridRep (RowTable.ofMatrix B) B rfl rfl
      (fun i j => RowTable.entry_ofMatrix_of_lt B i.isLt j.isLt) hB hq r'
  rw [hr'_vec] at hfst hsnd
  have hg'_vec : gy'.1.toVec = g.toVec := by
    rw [hfst, neg_sub, modParallelepiped_sub_mem hB y.2]
    exact g.2.2
  have hg'_eq : gy'.1 = g := by
    apply Subtype.ext; funext i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hg'_vec
    simp only [GridRep.toVec, PiLp.smul_apply, smul_eq_mul] at hi
    exact Int.cast_injective (mul_left_cancel₀ (inv_ne_zero hqR.ne') hi)
  have hy'_eq : gy'.2 = y := by
    apply Subtype.ext
    rw [hsnd, hg'_vec, sub_add_cancel]
  have hgy'_eq : gy' = (g, y) := Prod.ext hg'_eq hy'_eq
  rw [hgy'_eq] at hlist
  obtain ⟨_, _, hu_spec, hy_spec, _⟩ :=
    gridReduceInt_spec (RowTable.ofMatrix B) B rfl rfl
      (fun i j => RowTable.entry_ofMatrix_of_lt B i.isLt j.isLt) hB hq r'
  dsimp only at hu_spec hy_spec
  have hg_idemp : modParallelepiped B g.toVec = g.toVec := g.2.2
  rw [hr'_vec, neg_sub, modParallelepiped_sub_mem hB y.2, hg_idemp] at hu_spec
  rw [hr'_vec, hu_spec, sub_add_cancel] at hy_spec
  rw [← hlist]
  constructor
  · have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v r) hu_spec
    simp only [PiLp.smul_apply, smul_eq_mul] at h1
    rw [div_eq_inv_mul]
    exact h1
  · exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v r) hy_spec

private theorem sublatticeQuotToList_spec {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (qv : SublatticeQuot B S) (r : Fin n) :
    ((sublatticeQuotToList qv).getD r.1 0 : ℝ) = WithLp.ofLp qv.toVec r := by
  have hDpos : 0 < (S.det / B.det).natAbs := by
    rw [← quotientIndex_eq_natAbs_div_det (RowTable.ofMatrix B) (RowTable.ofMatrix S) B S
      (RowTable.wellFormed_ofMatrix B) (RowTable.wellFormed_ofMatrix S) rfl
      (fun i j => RowTable.entry_ofMatrix_of_lt B i.isLt j.isLt) rfl
      (fun i j => RowTable.entry_ofMatrix_of_lt S i.isLt j.isLt) hB hSB]
    exact quotientIndex_pos (RowTable.ofMatrix B) (RowTable.ofMatrix S) B S
      (RowTable.wellFormed_ofMatrix B) (RowTable.wellFormed_ofMatrix S) rfl
      (fun i j => RowTable.entry_ofMatrix_of_lt B i.isLt j.isLt) rfl
      (fun i j => RowTable.entry_ofMatrix_of_lt S i.isLt j.isLt) hB hS hSB
  have : NeZero (S.det / B.det).natAbs := ⟨hDpos.ne'⟩
  have hmem : qv ∈ ((PMF.uniformOfFintype (Fin n → ZMod (S.det / B.det).natAbs)).map
      (quotientHom B S hS hSB)).support := by
    rw [map_quotientHom_uniform_eq_uniform_sublatticeQuot B S hB hS hSB]
    simp
  obtain ⟨z, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  rw [← quotientReduceInt_eq_quotientHom (RowTable.ofMatrix B) (RowTable.ofMatrix S) B S
    rfl rfl (fun i j => RowTable.entry_ofMatrix_of_lt B i.isLt j.isLt)
    rfl rfl (fun i j => RowTable.entry_ofMatrix_of_lt S i.isLt j.isLt) hS hSB z]
  obtain ⟨_, hv_vec⟩ :=
    quotientReduceInt_spec (RowTable.ofMatrix B) (RowTable.ofMatrix S) B S
      rfl rfl (fun i j => RowTable.entry_ofMatrix_of_lt B i.isLt j.isLt)
      rfl rfl (fun i j => RowTable.entry_ofMatrix_of_lt S i.isLt j.isLt) hS
      (List.ofFn fun i : Fin n => (z i).val)
  have hx_eq : (fun j : Fin n => ((List.ofFn fun i : Fin n => (z i).val).getD j.val 0 : ℤ)) =
      fun j => ((z j).val : ℤ) := by
    funext j; simp [List.getD_eq_getElem?_getD, j.isLt]
  rw [hx_eq, ← quotientHom_toVec B S hS hSB z] at hv_vec
  exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v r) hv_vec

/-! ### 6. Unconditional Support & 4-Stage `CloseTo` Bridge for `singleIncGDDCall` -/

private theorem closeTo_eval_sampleModNat_clog_add (extraBits M : ℕ) [NeZero M] :
    CloseTo (ProbComp.eval (sampleModNat (Nat.clog 2 M + extraBits) M))
      ((PMF.uniformOfFintype (Fin M)).map Fin.val)
      (ENNReal.ofReal ((2 : ℝ) ^ (-(extraBits : ℤ)))) := by
  have hMpos : 0 < M := NeZero.pos M
  have hc := (closeTo_uniform_sampleModNat (Nat.clog 2 M + extraBits) M).symm.map ZMod.val
  have hlhs :
      ((ProbComp.eval (sampleModNat (Nat.clog 2 M + extraBits) M)).map
        (Nat.cast : ℕ → ZMod M)).map ZMod.val =
      ProbComp.eval (sampleModNat (Nat.clog 2 M + extraBits) M) := by
    rw [PMF.map_comp]
    conv_rhs => rw [← PMF.map_id (ProbComp.eval (sampleModNat (Nat.clog 2 M + extraBits) M))]
    refine PMF.map_congr_on_support _ _ _ fun x hx => ?_
    unfold sampleModNat at hx
    rw [ProbComp.eval_map] at hx
    obtain ⟨n, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact ZMod.val_natCast_of_lt (Nat.mod_lt n hMpos)
  have hrhs :
      (PMF.uniformOfFintype (ZMod M)).map ZMod.val =
      (PMF.uniformOfFintype (Fin M)).map Fin.val :=
    (Probability.PMF.uniformOfFintype_fin_bind M PMF.pure).symm
  rw [hlhs, hrhs] at hc
  refine hc.mono ?_
  have hMle : (M : ℝ≥0∞) ≤ 2 ^ Nat.clog 2 M := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) M
  rw [pow_add]
  calc (M : ℝ≥0∞) / (2 ^ Nat.clog 2 M * 2 ^ extraBits)
      ≤ (2 ^ Nat.clog 2 M) / (2 ^ Nat.clog 2 M * 2 ^ extraBits) :=
        ENNReal.div_le_div_right hMle _
    _ = 1 / 2 ^ extraBits := by
        conv_lhs => arg 1; rw [← mul_one ((2 : ℝ≥0∞) ^ Nat.clog 2 M)]
        rw [ENNReal.mul_div_mul_left 1 (2 ^ extraBits) (by positivity) (by simp)]
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-(extraBits : ℤ))) := by
        rw [zpow_neg, zpow_natCast, one_div, ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

private theorem closeTo_eval_mapM_range {β : Type} {k : ℕ}
    {f : ℕ → ProbComp β} {g : Fin k → PMF β} {δ : ℝ≥0∞}
    (h : ∀ i : Fin k, CloseTo (ProbComp.eval (f i.val)) (g i) δ) :
    CloseTo (ProbComp.eval ((List.range k).mapM f))
      ((PMF.piFin g).map List.ofFn) ((k : ℝ≥0∞) * δ) := by
  rw [ProbComp.eval_mapM_range]
  exact (CloseTo.piFin h).map List.ofFn

private theorem mem_support_mapM_range_getD {β : Type} {k : ℕ} {f : ℕ → ProbComp β}
    {xs : List β} (hxs : xs ∈ (ProbComp.eval ((List.range k).mapM f)).support) (d : β) :
    xs.length = k ∧ ∀ i : Fin k, xs.getD i.val d ∈ (ProbComp.eval (f i.val)).support := by
  rw [ProbComp.eval_mapM_range, PMF.mem_support_map_iff] at hxs
  obtain ⟨g, hg, rfl⟩ := hxs
  refine ⟨List.length_ofFn, fun i => ?_⟩
  rw [PMF.mem_support_piFin_iff] at hg
  have hget : (List.ofFn g).getD i.val d = g i := by
    simp [List.getD_eq_getElem?_getD, i.isLt]
  rw [hget]
  exact hg i

/-- Unconditional lattice membership on 100% of the support of `singleIncGDDCall` (even when the
SIS solver `F` fails or returns arbitrary vectors). -/
theorem mem_support_singleIncGDDCall_mem_intLattice
    (P : SISParams) (F : P.Solver) (inp : IncGDDInput)
    (B S : Matrix (Fin (P.n inp.secParam)) (Fin (P.n inp.secParam)) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (hB_eq : inp.basisB = RowTable.ofMatrix B) (hS_eq : inp.basisS = RowTable.ofMatrix S)
    {v : List ℤ} (hv : v ∈ (ProbComp.eval (singleIncGDDCall P F inp)).support) :
    v.length = P.n inp.secParam ∧ listToEuclidean (P.n inp.secParam) v ∈ intLattice B := by
  unfold singleIncGDDCall at hv
  dsimp only at hv
  split_ifs at hv with hzero
  · rw [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hv
    subst hv
    refine ⟨by simp, ?_⟩
    have h0 : listToEuclidean (P.n inp.secParam) (List.replicate (P.n inp.secParam) 0) = 0 := by
      ext r; simp [listToEuclidean, List.getD_eq_getElem?_getD]
    rw [h0]
    exact (intLattice B).zero_mem
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hv
    obtain ⟨j, _, sgn, _, idx, _, cys, hcys, vs, hvs, zL, hzL, rfl⟩ := hv
    have hq : 0 < P.q inp.secParam := NeZero.pos (P.q inp.secParam)
    obtain ⟨hcys_len, hcys_get⟩ := mem_support_mapM_range_getD hcys ([], [])
    obtain ⟨hvs_len, hvs_get⟩ := mem_support_mapM_range_getD hvs []
    have hcy_ex : ∀ c : Fin (P.m inp.secParam),
        ∃ cy : GridRep B (P.q inp.secParam) × intLattice B,
          (∀ r : Fin (P.n inp.secParam),
            ((cys.getD c.1 ([], [])).1.getD r.1 0 : ℝ) / (P.q inp.secParam : ℝ) =
              WithLp.ofLp cy.1.toVec r) ∧
          (∀ r : Fin (P.n inp.secParam),
            ((cys.getD c.1 ([], [])).2.getD r.1 0 : ℝ) =
              WithLp.ofLp (cy.2 : EuclideanSpace ℝ (Fin (P.n inp.secParam))) r) := fun c => by
      have h := hcys_get c
      rw [hB_eq] at h
      obtain ⟨cy, hlist, _⟩ :=
        mem_support_sampleGridGaussian_exists_gridRep _ B rfl rfl
          (fun i j => RowTable.entry_ofMatrix_of_lt B i.isLt j.isLt) hB hq h
      exact ⟨cy, fun r => (hlist ▸ gridPairToLists_spec hB hq cy r).1,
        fun r => (hlist ▸ gridPairToLists_spec hB hq cy r).2⟩
    have hv_ex : ∀ c : Fin (P.m inp.secParam),
        ∃ vr : SublatticeQuot B S,
          ∀ r : Fin (P.n inp.secParam),
            ((vs.getD c.1 []).getD r.1 0 : ℝ) = WithLp.ofLp vr.toVec r := fun c => by
      have h := hvs_get c
      rw [hB_eq, hS_eq] at h
      obtain ⟨vr, hlist, _⟩ :=
        mem_support_sampleQuotientModS_exists_sublatticeQuot _ B S
          rfl rfl (fun i j => RowTable.entry_ofMatrix_of_lt B i.isLt j.isLt)
          rfl rfl (fun i j => RowTable.entry_ofMatrix_of_lt S i.isLt j.isLt) hS hSB h
      exact ⟨vr, fun r => hlist ▸ sublatticeQuotToList_spec hB hS hSB vr r⟩
    choose CY hCY_u hCY_y using hcy_ex
    choose V hV using hv_ex
    unfold callSISSolver at hzL
    rw [ProbComp.eval_map, PMF.mem_support_map_iff] at hzL
    obtain ⟨z, _, rfl⟩ := hzL
    have hus : ∀ c : Fin (P.m inp.secParam), ∀ r : Fin (P.n inp.secParam),
        (((cys.map Prod.fst).getD c.1 []).getD r.1 0 : ℝ) / (P.q inp.secParam : ℝ) =
          WithLp.ofLp (CY c).1.toVec r := fun c r => by
      have hfst : (cys.map Prod.fst).getD c.1 [] = (cys.getD c.1 ([], [])).1 := by
        simp [List.getD_eq_getElem?_getD, hcys_len, c.isLt]
      rw [hfst]; exact hCY_u c r
    have hys : ∀ c : Fin (P.m inp.secParam), ∀ r : Fin (P.n inp.secParam),
        (((cys.map Prod.snd).getD c.1 []).getD r.1 0 : ℝ) =
          WithLp.ofLp ((CY c).2 : EuclideanSpace ℝ (Fin (P.n inp.secParam))) r := fun c r => by
      have hsnd : (cys.map Prod.snd).getD c.1 [] = (cys.getD c.1 ([], [])).2 := by
        simp [List.getD_eq_getElem?_getD, hcys_len, c.isLt]
      rw [hsnd]; exact hCY_y c r
    have hcols_eq :
        ((List.range (P.m inp.secParam)).map fun c =>
          combineColInt (P.n inp.secParam) (P.q inp.secParam) inp.basisS (vs.getD c [])
            (cys.getD c ([], [])).1) =
        ((List.range (P.m inp.secParam)).map fun c =>
          combineColInt (P.n inp.secParam) (P.q inp.secParam) (RowTable.ofMatrix S) (vs.getD c [])
            ((cys.map Prod.fst).getD c [])) := by
      refine List.map_congr_left fun c hc => ?_
      have hcm : c < P.m inp.secParam := List.mem_range.mp hc
      have hfst : (cys.map Prod.fst).getD c [] = (cys.getD c ([], [])).1 := by
        simp [List.getD_eq_getElem?_getD, hcys_len, hcm]
      rw [hS_eq, hfst]
    refine ⟨by simp [combineOutputInt], ?_⟩
    rw [hcols_eq, hS_eq]
    rw [combineOutputInt_eq_combineOutput_sub hq B S hS V (fun c => (CY c).1) (fun c => (CY c).2)
      vs (cys.map Prod.fst) (cys.map Prod.snd) hV hus hys z]
    exact Submodule.sub_mem _
      (combineOutput_mem_intLattice B S hS hSB (P.q inp.secParam) hq V (fun c => (CY c).1) z)
      (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ (z c) (CY c).2.2)

private lemma closeTo_eval_singleIncGDDCall_inner
    (P : SISParams) (F : P.Solver) (inp : IncGDDInput)
    (B S : Matrix (Fin (P.n inp.secParam)) (Fin (P.n inp.secParam)) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (hB_eq : inp.basisB = RowTable.ofMatrix B) (hS_eq : inp.basisS = RowTable.ofMatrix S)
    {sSq : ℚ} (hsSq_pos : 0 < sSq) {s : ℝ} (hs_pos : 0 < s) (hs_eq : s = Real.sqrt (sSq : ℝ))
    (hqs1 : 1 ≤ (P.q inp.secParam : ℝ) * s)
    (htail : 1 ≤ inp.tail) (hprec : 8 * (2 * inp.tail + 6) ≤ 2 ^ inp.prec)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε_half : ε ≤ 1 / 2)
    (hdual_int : ZLattice.gaussianMass
      (LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal)
      (1 / ((P.q inp.secParam : ℝ) * s)) 0 - 1 ≤ ε)
    (j : Fin (P.m inp.secParam)) (sgn : Bool) (idx : Fin (P.β inp.secParam)) :
    let κ := inp.secParam
    let n := P.n κ
    let m := P.m κ
    let q := P.q κ
    let hq : 0 < q := NeZero.pos q
    let α : ℤ := if sgn then (idx.val + 1 : ℤ) else -((idx.val + 1 : ℤ))
    let scaledTarget : List ℚ := inp.target.map fun x => Rat.divInt (-1) α * x
    let δg : ℝ := (n : ℝ) *
      ((1 - 1 / (16 * (2 * (inp.tail : ℝ) + 6))) ^ inp.maxTrials
        + (8 * (inp.tail : ℝ) + 24) / (2 : ℝ) ^ inp.prec
        + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2)))
    let δq : ℝ := (n : ℝ) / (2 : ℝ) ^ inp.extraBits
    CloseTo
      ((ProbComp.eval ((List.range m).mapM fun i =>
        sampleGridGaussian
          ⟨n, q, inp.basisB, sSq,
            if i = j.val then scaledTarget else List.replicate n 0,
            inp.tail, inp.prec, inp.maxTrials⟩)).bind fun cys =>
        (ProbComp.eval ((List.range m).mapM fun _ =>
          sampleQuotientModS ⟨n, inp.basisB, inp.basisS, inp.extraBits⟩)).bind fun vs =>
          let cols := (List.range m).map fun c =>
            combineColInt n q inp.basisS (vs.getD c []) (cys.getD c ([], [])).1
          let rows := combineMatrixRowsInt n m cols
          (ProbComp.eval (callSISSolver P F κ rows)).map fun z =>
            listToEuclidean n (combineOutputInt n m q inp.basisS cols vs (cys.map Prod.snd) z))
      ((PMF.piFin fun i : Fin m =>
        idealGridSample B hB q hq s hs_pos
          (if i = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0)).bind fun CY =>
        (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
          (ProbComp.eval (F κ (combineMatrix B S q V (fun i => (CY i).1)))).map fun z =>
            combineOutput B S q V (fun i => (CY i).1) z -
              ∑ i : Fin m, z i • ((CY i).2 : EuclideanSpace ℝ (Fin n)))
      (ENNReal.ofReal ((m : ℝ) * δg + (m : ℝ) * δq)) := by
  intro κ n m q hq α scaledTarget δg δq
  have h1me : 0 < 1 - ε := by linarith
  have hbase_nn : 0 ≤ 1 - 1 / (16 * (2 * (inp.tail : ℝ) + 6)) := by
    have hden : (1 : ℝ) ≤ 16 * (2 * (inp.tail : ℝ) + 6) := by
      linarith [Nat.cast_nonneg (α := ℝ) inp.tail]
    have hinv : 1 / (16 * (2 * (inp.tail : ℝ) + 6)) ≤ 1 := div_le_one_of_le₀ hden (by positivity)
    linarith
  have hδg0 : 0 ≤ δg := by dsimp only [δg]; positivity
  have hδq0 : 0 ≤ δq := by dsimp only [δq]; positivity
  have htarget_eq : ∀ i : Fin m,
      ratListToEuclidean n (if i.val = j.val then scaledTarget else List.replicate n 0) =
        if i = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      ext r
      have hget : scaledTarget.getD r.1 0 = Rat.divInt (-1) α * inp.target.getD r.1 0 := by
        by_cases hr : r.1 < inp.target.length
        · have hr' : r.1 < scaledTarget.length := by simp [scaledTarget, hr]
          rw [List.getD_eq_getElem _ _ hr', List.getD_eq_getElem _ _ hr]
          simp [scaledTarget]
        · have hr' : scaledTarget.length ≤ r.1 := by simp [scaledTarget]; omega
          rw [List.getD_eq_default _ _ hr', List.getD_eq_default _ _ (by omega)]
          simp
      change (scaledTarget.getD r.1 0 : ℝ) = _
      rw [hget, Rat.divInt_eq_div]
      simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_intCast,
        PiLp.smul_apply, smul_eq_mul, ratListToEuclidean]
      ring
    · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp only [hij, hne, ↓reduceIte]
      ext r
      simp [ratListToEuclidean, List.getD_eq_getElem?_getD]
  have hgrid_mapM :
      CloseTo
        (ProbComp.eval ((List.range m).mapM fun i =>
          sampleGridGaussian
            ⟨n, q, inp.basisB, sSq,
              if i = j.val then scaledTarget else List.replicate n 0,
              inp.tail, inp.prec, inp.maxTrials⟩))
        ((PMF.piFin fun i : Fin m =>
          idealGridSample B hB q hq s hs_pos
            (if i = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0)).map
            fun CY => List.ofFn fun i => gridPairToLists (CY i))
        (ENNReal.ofReal ((m : ℝ) * δg)) := by
    have hpi := closeTo_eval_mapM_range (k := m)
      (f := fun i => sampleGridGaussian
        ⟨n, q, inp.basisB, sSq,
          if i = j.val then scaledTarget else List.replicate n 0,
          inp.tail, inp.prec, inp.maxTrials⟩)
      (g := fun i : Fin m => (idealGridSample B hB q hq s hs_pos
        (if i = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0)).map
          gridPairToLists)
      (δ := ENNReal.ofReal δg)
      fun i => by
        rw [hB_eq, ← htarget_eq i]
        have h1 := closeTo_eval_sampleGridGaussian_pi
          ⟨n, q, RowTable.ofMatrix B, sSq,
            if i.val = j.val then scaledTarget else List.replicate n 0,
            inp.tail, inp.prec, inp.maxTrials⟩
          hsSq_pos hq (hs_eq ▸ hqs1) htail hε0 hε_half (hs_eq ▸ hdual_int) hprec
        have hmap := map_gridReduceInt_piFin_eq_map_idealGridSample
          (RowTable.ofMatrix B) B rfl rfl
          (fun a b => RowTable.entry_ofMatrix_of_lt B a.isLt b.isLt) hB hq s hs_pos
          (ratListToEuclidean n (if i.val = j.val then scaledTarget else List.replicate n 0))
        dsimp only at h1 hmap
        have hdg :
            (PMF.piFin fun k : Fin n =>
              discreteGaussianInt ((q : ℝ) * Real.sqrt (sSq : ℝ)) (by positivity)
                ((q : ℝ) * ((if i.val = j.val then scaledTarget else List.replicate n 0).getD
                  k.val 0 : ℝ))) =
            (PMF.piFin fun k : Fin n =>
              discreteGaussianInt ((q : ℝ) * s) (by positivity)
                ((q : ℝ) * (ratListToEuclidean n
                  (if i.val = j.val then scaledTarget else List.replicate n 0)) k)) := by
          congr 1; funext k; congr 1
          rw [hs_eq]
        rw [hdg, hmap] at h1
        exact h1
    rw [PMF.piFin_map, PMF.map_comp] at hpi
    have herr : (m : ℝ≥0∞) * ENNReal.ofReal δg = ENNReal.ofReal ((m : ℝ) * δg) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
    simpa only [herr, Function.comp_def] using hpi
  have hpi_unif : (PMF.piFin fun _ : Fin m => PMF.uniformOfFintype (SublatticeQuot B S)) =
      PMF.uniformOfFintype (Fin m → SublatticeQuot B S) :=
    (PMF.piFin_const _ m).trans (PMF.iid_uniformOfFintype m)
  have hquot_mapM :
      CloseTo
        (ProbComp.eval ((List.range m).mapM fun _ =>
          sampleQuotientModS ⟨n, inp.basisB, inp.basisS, inp.extraBits⟩))
        ((PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).map
          fun V => List.ofFn fun i => sublatticeQuotToList (V i))
        (ENNReal.ofReal ((m : ℝ) * δq)) := by
    have hpi := closeTo_eval_mapM_range (k := m)
      (f := fun _ => sampleQuotientModS ⟨n, inp.basisB, inp.basisS, inp.extraBits⟩)
      (g := fun _ : Fin m => (PMF.uniformOfFintype (SublatticeQuot B S)).map
        sublatticeQuotToList)
      (δ := ENNReal.ofReal δq)
      fun _ => by
        rw [hB_eq, hS_eq]
        have hDpos := quotientIndex_pos (RowTable.ofMatrix B) (RowTable.ofMatrix S) B S
          (RowTable.wellFormed_ofMatrix B) (RowTable.wellFormed_ofMatrix S) rfl
          (fun a b => RowTable.entry_ofMatrix_of_lt B a.isLt b.isLt) rfl
          (fun a b => RowTable.entry_ofMatrix_of_lt S a.isLt b.isLt) hB hS hSB
        have h1 := closeTo_eval_sampleQuotientModS_pi
          ⟨n, RowTable.ofMatrix B, RowTable.ofMatrix S, inp.extraBits⟩ hDpos
        have hmap := map_quotientReduceInt_piFin_eq_map_uniform
          (RowTable.ofMatrix B) (RowTable.ofMatrix S) B S
          (RowTable.wellFormed_ofMatrix B) (RowTable.wellFormed_ofMatrix S)
          rfl rfl (fun a b => RowTable.entry_ofMatrix_of_lt B a.isLt b.isLt)
          rfl rfl (fun a b => RowTable.entry_ofMatrix_of_lt S a.isLt b.isLt) hB hS hSB
        dsimp only at h1 hmap
        rw [hmap] at h1
        have hδq_eq : ((n : ℝ≥0∞) / 2 ^ inp.extraBits) = ENNReal.ofReal δq := by
          dsimp only [δq]
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        rwa [hδq_eq] at h1
    rw [PMF.piFin_map, PMF.map_comp, hpi_unif] at hpi
    have herr : (m : ℝ≥0∞) * ENNReal.ofReal δq = ENNReal.ofReal ((m : ℝ) * δq) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
    simpa only [herr, Function.comp_def] using hpi
  let cont : List (List ℤ × List ℤ) → List (List ℤ) → PMF (EuclideanSpace ℝ (Fin n)) :=
    fun cys vs =>
      let cols := (List.range m).map fun c =>
        combineColInt n q inp.basisS (vs.getD c []) (cys.getD c ([], [])).1
      let rows := combineMatrixRowsInt n m cols
      (ProbComp.eval (callSISSolver P F κ rows)).map fun z =>
        listToEuclidean n (combineOutputInt n m q inp.basisS cols vs (cys.map Prod.snd) z)
  have hbind1 :
      CloseTo
        ((ProbComp.eval ((List.range m).mapM fun i =>
          sampleGridGaussian
            ⟨n, q, inp.basisB, sSq,
              if i = j.val then scaledTarget else List.replicate n 0,
              inp.tail, inp.prec, inp.maxTrials⟩)).bind fun cys =>
          (ProbComp.eval ((List.range m).mapM fun _ =>
            sampleQuotientModS ⟨n, inp.basisB, inp.basisS, inp.extraBits⟩)).bind (cont cys))
        (((PMF.piFin fun i : Fin m =>
          idealGridSample B hB q hq s hs_pos
            (if i = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0)).map
            fun CY => List.ofFn fun i => gridPairToLists (CY i)).bind fun cys =>
          ((PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).map
            fun V => List.ofFn fun i => sublatticeQuotToList (V i)).bind (cont cys))
        (ENNReal.ofReal ((m : ℝ) * δg) + ENNReal.ofReal ((m : ℝ) * δq)) :=
    hgrid_mapM.bind fun cys _ => hquot_mapM.bind_left (cont cys)
  have hrhs_eq :
      (((PMF.piFin fun i : Fin m =>
        idealGridSample B hB q hq s hs_pos
          (if i = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0)).map
          fun CY => List.ofFn fun i => gridPairToLists (CY i)).bind fun cys =>
        ((PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).map
          fun V => List.ofFn fun i => sublatticeQuotToList (V i)).bind (cont cys)) =
      ((PMF.piFin fun i : Fin m =>
        idealGridSample B hB q hq s hs_pos
          (if i = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0)).bind fun CY =>
        (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
          (ProbComp.eval (F κ (combineMatrix B S q V (fun i => (CY i).1)))).map fun z =>
            combineOutput B S q V (fun i => (CY i).1) z -
              ∑ i : Fin m, z i • ((CY i).2 : EuclideanSpace ℝ (Fin n))) := by
    rw [PMF.bind_map]
    congr 1; funext CY
    dsimp only [Function.comp_apply]
    rw [PMF.bind_map]
    congr 1; funext V
    simp only [Function.comp_apply]
    let cys : List (List ℤ × List ℤ) := List.ofFn fun i => gridPairToLists (CY i)
    let vs : List (List ℤ) := List.ofFn fun i => sublatticeQuotToList (V i)
    let us : List (List ℤ) := cys.map Prod.fst
    let ys : List (List ℤ) := cys.map Prod.snd
    have hvs : ∀ (c : Fin m) (r : Fin n),
        ((vs.getD c.1 []).getD r.1 0 : ℝ) = WithLp.ofLp (V c).toVec r := fun c r => by
      have hvc : vs.getD c.1 [] = sublatticeQuotToList (V c) := by
        simp [vs, List.getD_eq_getElem?_getD, c.isLt]
      rw [hvc]; exact sublatticeQuotToList_spec hB hS hSB (V c) r
    have hus : ∀ (c : Fin m) (r : Fin n),
        ((us.getD c.1 []).getD r.1 0 : ℝ) / (q : ℝ) = WithLp.ofLp (CY c).1.toVec r := fun c r => by
      have huc : us.getD c.1 [] = (gridPairToLists (CY c)).1 := by
        simp [us, cys, List.getD_eq_getElem?_getD, c.isLt]
      rw [huc]; exact (gridPairToLists_spec hB hq (CY c) r).1
    have hys : ∀ (c : Fin m) (r : Fin n),
        ((ys.getD c.1 []).getD r.1 0 : ℝ) =
          WithLp.ofLp ((CY c).2 : EuclideanSpace ℝ (Fin n)) r := fun c r => by
      have hyc : ys.getD c.1 [] = (gridPairToLists (CY c)).2 := by
        simp [ys, cys, List.getD_eq_getElem?_getD, c.isLt]
      rw [hyc]; exact (gridPairToLists_spec hB hq (CY c) r).2
    have hcols_eq :
        ((List.range m).map fun c =>
          combineColInt n q inp.basisS (vs.getD c []) (cys.getD c ([], [])).1) =
        ((List.range m).map fun c =>
          combineColInt n q (RowTable.ofMatrix S) (vs.getD c []) (us.getD c [])) := by
      refine List.map_congr_left fun c hc => ?_
      have hcm : c < m := List.mem_range.mp hc
      have hfst : us.getD c [] = (cys.getD c ([], [])).1 := by
        simp [us, cys, List.getD_eq_getElem?_getD, hcm]
      rw [hS_eq, hfst]
    change (ProbComp.eval (callSISSolver P F κ (combineMatrixRowsInt n m
      ((List.range m).map fun c =>
        combineColInt n q inp.basisS (vs.getD c []) (cys.getD c ([], [])).1)))).map
      (fun z => listToEuclidean n (combineOutputInt n m q inp.basisS
        ((List.range m).map fun c =>
          combineColInt n q inp.basisS (vs.getD c []) (cys.getD c ([], [])).1) vs ys z)) = _
    rw [hcols_eq, hS_eq]
    unfold callSISSolver
    rw [ProbComp.eval_map, PMF.map_comp,
      makeSISInput_combineMatrix_eq B S hS V (fun i => (CY i).1) vs us hvs hus]
    congr 1; funext z
    simp only [Function.comp_apply]
    exact combineOutputInt_eq_combineOutput_sub hq B S hS V (fun i => (CY i).1)
      (fun i => (CY i).2) vs us ys hvs hus hys z
  rw [hrhs_eq, ← ENNReal.ofReal_add (by positivity) (by positivity)] at hbind1
  exact hbind1

/-- Full 4-stage `CloseTo` bridge from concrete `singleIncGDDCall` to `MR07Core.idealIncGDDStep`,
discharging both `1 ≤ q * s` and the 1-D dual-mass bound automatically from `hdual`. -/
theorem closeTo_eval_singleIncGDDCall_idealIncGDDStep
    (P : SISParams) (F : P.Solver) (inp : IncGDDInput)
    (hn : 1 ≤ P.n inp.secParam) (hm : 1 ≤ P.m inp.secParam) (hβ : 1 ≤ P.β inp.secParam)
    (hrSq : 0 < inp.rSq) (htail : 1 ≤ inp.tail)
    (hprec : 8 * (2 * inp.tail + 6) ≤ 2 ^ inp.prec)
    (B S : Matrix (Fin (P.n inp.secParam)) (Fin (P.n inp.secParam)) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (hB_eq : inp.basisB = RowTable.ofMatrix B) (hS_eq : inp.basisS = RowTable.ofMatrix S)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε_half : ε ≤ 1 / 2)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin (P.n inp.secParam)))) (intLattice B))
        (2 / (2 * Real.sqrt (inp.rSq : ℝ) /
          ((P.β inp.secParam : ℝ) * Real.sqrt (P.n inp.secParam)))) 0 - 1 ≤ ε) :
    let κ := inp.secParam
    let n := P.n κ
    let m := P.m κ
    let β := P.β κ
    let r : ℝ := Real.sqrt (inp.rSq : ℝ)
    have hβR : (1 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβ
    have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hrSq)
    CloseTo
      ((ProbComp.eval (singleIncGDDCall P F inp)).map (listToEuclidean n))
      (idealIncGDDStep B S hB (β : ℝ) r hβR hr (ratListToEuclidean n inp.target) (F κ))
      (ENNReal.ofReal (mr07SingleCallErr n m inp.tail inp.prec inp.maxTrials inp.extraBits ε)) := by
  intro κ n m β r hβR hr
  set q := P.q κ
  have hq : 0 < q := NeZero.pos q
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hβ0 : β ≠ 0 := Nat.pos_iff_ne_zero.mp hβ
  have : NeZero m := ⟨hm0⟩
  have : NeZero β := ⟨hβ0⟩
  set sSq : ℚ := inp.rSq * Rat.divInt 4 ((β * β * n : ℕ) : ℤ)
  have hsSq_pos : 0 < sSq := by
    dsimp only [sSq]
    rw [Rat.divInt_eq_div]
    have hden_pos : (0 : ℚ) < ((β * β * n : ℕ) : ℚ) := by
      exact_mod_cast (by positivity : 0 < β * β * n)
    exact mul_pos hrSq (div_pos (by norm_num) hden_pos)
  set s : ℝ := 2 * r / ((β : ℝ) * Real.sqrt n)
  have hs_pos : 0 < s := by
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hβR0 : (0 : ℝ) < β := Nat.cast_pos.mpr hβ
    positivity
  have hs_eq : s = Real.sqrt (sSq : ℝ) := by
    have hsSq_R : (sSq : ℝ) = s ^ 2 := by
      dsimp only [sSq, s, r]
      rw [Rat.divInt_eq_div]
      push_cast
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by exact_mod_cast hrSq.le),
        Real.sq_sqrt (Nat.cast_nonneg n)]
      have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      have hβR0 : (β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hβ0
      field_simp [hnR, hβR0]
      ring
    rw [hsSq_R, Real.sqrt_sq hs_pos.le]
  have hqs1 : 1 ≤ (q : ℝ) * s :=
    one_le_q_mul_s_of_dualMass hn hq B hB hs_pos hε_half hdual
  have hdual_int : ZLattice.gaussianMass
      (LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal)
      (1 / ((q : ℝ) * s)) 0 - 1 ≤ ε :=
    (gaussianMass_dual_intReal_le_of_intLattice_two_div hn hq B hB hs_pos).trans hdual
  have hfloor : Nat.floor (β : ℝ) = β := Nat.floor_natCast β
  have hnotzero : ¬ (n = 0 ∨ m = 0 ∨ β = 0) := by simp [hn0, hm0, hβ0]
  have hbind_map_pure : ∀ (p : PMF (List ℤ)) (g : List ℤ → List ℤ),
      (p.bind fun a => PMF.pure (g a)).map (listToEuclidean n) =
        p.map fun a => listToEuclidean n (g a) := fun p g => by
    rw [PMF.map_bind]
    change p.bind (fun a => (PMF.pure (g a)).bind (PMF.pure ∘ listToEuclidean n)) =
      p.bind (PMF.pure ∘ fun a => listToEuclidean n (g a))
    simp only [PMF.pure_bind, Function.comp_apply]
    rfl
  have hreal_unfold :
      (ProbComp.eval (singleIncGDDCall P F inp)).map (listToEuclidean n) =
      (ProbComp.eval (sampleModNat (Nat.clog 2 m + inp.extraBits) m)).bind fun j =>
        (PMF.uniformOfFintype Bool).bind fun sgn =>
          (ProbComp.eval (sampleModNat (Nat.clog 2 β + inp.extraBits) β)).bind fun idx =>
            let α : ℤ := if sgn then (idx + 1 : ℤ) else -((idx + 1 : ℤ))
            let scaledTarget : List ℚ := inp.target.map fun x => Rat.divInt (-1) α * x
            (ProbComp.eval ((List.range m).mapM fun i =>
              sampleGridGaussian
                ⟨n, q, inp.basisB, sSq,
                  if i = j then scaledTarget else List.replicate n 0,
                  inp.tail, inp.prec, inp.maxTrials⟩)).bind fun cys =>
              (ProbComp.eval ((List.range m).mapM fun _ =>
                sampleQuotientModS ⟨n, inp.basisB, inp.basisS, inp.extraBits⟩)).bind fun vs =>
                let cols := (List.range m).map fun c =>
                  combineColInt n q inp.basisS (vs.getD c []) (cys.getD c ([], [])).1
                let rows := combineMatrixRowsInt n m cols
                (ProbComp.eval (callSISSolver P F κ rows)).map fun z =>
                  listToEuclidean n
                    (combineOutputInt n m q inp.basisS cols vs (cys.map Prod.snd) z) := by
    unfold singleIncGDDCall
    dsimp only [κ, n, m, q, β, sSq]
    rw [ite_eq_right hnotzero]
    rw [ProbComp.eval_bind, PMF.map_bind]
    congr 1; funext j
    rw [ProbComp.eval_bind, ProbComp.eval_uniform, PMF.map_bind]
    congr 1; funext sgn
    rw [ProbComp.eval_bind, PMF.map_bind]
    congr 1; funext idx
    rw [ProbComp.eval_bind, PMF.map_bind]
    congr 1; funext cys
    rw [ProbComp.eval_bind, PMF.map_bind]
    congr 1; funext vs
    rw [ProbComp.eval_bind]
    simp only [ProbComp.eval_pure]
    exact hbind_map_pure _ _
  let eGuess : (Fin m × Bool × Fin β) ≃ (Fin m × Bool × Fin (Nat.floor (β : ℝ))) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (finCongr hfloor.symm))
  have hideal_unfold :
      idealIncGDDStep B S hB (β : ℝ) r hβR hr (ratListToEuclidean n inp.target) (F κ) =
      (PMF.uniformOfFintype (Fin m)).bind fun j =>
        (PMF.uniformOfFintype Bool).bind fun sgn =>
          (PMF.uniformOfFintype (Fin β)).bind fun idx =>
            let α : ℤ := if sgn then (idx.val + 1 : ℤ) else -((idx.val + 1 : ℤ))
            (PMF.piFin fun i : Fin m =>
              idealGridSample B hB q hq s hs_pos
                (if i = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0)).bind
              fun CY =>
              (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
                (ProbComp.eval (F κ (combineMatrix B S q V (fun i => (CY i).1)))).map fun z =>
                  combineOutput B S q V (fun i => (CY i).1) z -
                    ∑ i : Fin m, z i • ((CY i).2 : EuclideanSpace ℝ (Fin n)) := by
    unfold idealIncGDDStep
    have hnm : 1 ≤ n ∧ 1 ≤ m := ⟨hn, hm⟩
    rw [dite_eq_left hnm]
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have : Nonempty (Fin β) := ⟨⟨0, hβ⟩⟩
    have : Nonempty (Fin (Nat.floor (β : ℝ))) := ⟨⟨0, Nat.floor_pos.mpr hβR⟩⟩
    change (PMF.uniformOfFintype (Fin m × Bool × Fin ⌊(β : ℝ)⌋₊)).bind (fun x =>
      match x with
      | (j, sgn, idx) =>
        let α : ℤ := if sgn then (idx.val + 1 : ℤ) else -((idx.val + 1 : ℤ))
        (PMF.piFin fun i : Fin m =>
          idealGridSample B hB q hq s hs_pos
            (if i = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0)).bind
          fun CY =>
          (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
            (ProbComp.eval (F κ (combineMatrix B S q V (fun i => (CY i).1)))).map fun z =>
              combineOutput B S q V (fun i => (CY i).1) z -
                ∑ i : Fin m, z i • ((CY i).2 : EuclideanSpace ℝ (Fin n))) = _
    rw [← PMF.uniformOfFintype_map_equiv eGuess, PMF.bind_map]
    rw [← PMF.uniformOfFintype_prod, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun j => ?_)
    rw [PMF.bind_map, ← PMF.uniformOfFintype_prod, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun sgn => ?_)
    rw [PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun idx => ?_)
    have hidx_val : (finCongr hfloor.symm idx).val = idx.val := rfl
    simp only [eGuess, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map_apply, hidx_val,
      Function.comp_apply]
  rw [hreal_unfold, hideal_unfold]
  let δg : ℝ := (n : ℝ) *
    ((1 - 1 / (16 * (2 * (inp.tail : ℝ) + 6))) ^ inp.maxTrials
      + (8 * (inp.tail : ℝ) + 24) / (2 : ℝ) ^ inp.prec
      + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2)))
  let δq : ℝ := (n : ℝ) / (2 : ℝ) ^ inp.extraBits
  let δm : ℝ := (2 : ℝ) ^ (-(inp.extraBits : ℤ))
  have h1me : 0 < 1 - ε := by linarith
  have hbase_nn : 0 ≤ 1 - 1 / (16 * (2 * (inp.tail : ℝ) + 6)) := by
    have hden : (1 : ℝ) ≤ 16 * (2 * (inp.tail : ℝ) + 6) := by
      linarith [Nat.cast_nonneg (α := ℝ) inp.tail]
    have hinv : 1 / (16 * (2 * (inp.tail : ℝ) + 6)) ≤ 1 := div_le_one_of_le₀ hden (by positivity)
    linarith
  have hδg0 : 0 ≤ δg := by dsimp only [δg]; positivity
  have hδq0 : 0 ≤ δq := by dsimp only [δq]; positivity
  have hδm0 : 0 ≤ δm := by positivity
  let realBody : ℕ → Bool → ℕ → PMF (EuclideanSpace ℝ (Fin n)) := fun j sgn idx =>
    let α : ℤ := if sgn then (idx + 1 : ℤ) else -((idx + 1 : ℤ))
    let scaledTarget : List ℚ := inp.target.map fun x => Rat.divInt (-1) α * x
    (ProbComp.eval ((List.range m).mapM fun i =>
      sampleGridGaussian
        ⟨n, q, inp.basisB, sSq,
          if i = j then scaledTarget else List.replicate n 0,
          inp.tail, inp.prec, inp.maxTrials⟩)).bind fun cys =>
      (ProbComp.eval ((List.range m).mapM fun _ =>
        sampleQuotientModS ⟨n, inp.basisB, inp.basisS, inp.extraBits⟩)).bind fun vs =>
        let cols := (List.range m).map fun c =>
          combineColInt n q inp.basisS (vs.getD c []) (cys.getD c ([], [])).1
        let rows := combineMatrixRowsInt n m cols
        (ProbComp.eval (callSISSolver P F κ rows)).map fun z =>
          listToEuclidean n (combineOutputInt n m q inp.basisS cols vs (cys.map Prod.snd) z)
  let idealBody : ℕ → Bool → ℕ → PMF (EuclideanSpace ℝ (Fin n)) := fun j sgn idx =>
    let α : ℤ := if sgn then (idx + 1 : ℤ) else -((idx + 1 : ℤ))
    (PMF.piFin fun i : Fin m =>
      idealGridSample B hB q hq s hs_pos
        (if i.val = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0)).bind fun CY =>
      (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
        (ProbComp.eval (F κ (combineMatrix B S q V (fun i => (CY i).1)))).map fun z =>
          combineOutput B S q V (fun i => (CY i).1) z -
            ∑ i : Fin m, z i • ((CY i).2 : EuclideanSpace ℝ (Fin n))
  have hinner : ∀ (j : Fin m) (sgn : Bool) (idx : Fin β),
      CloseTo (realBody j.val sgn idx.val) (idealBody j.val sgn idx.val)
        (ENNReal.ofReal ((m : ℝ) * δg + (m : ℝ) * δq)) := fun j sgn idx => by
    have h := closeTo_eval_singleIncGDDCall_inner P F inp B S hB hS hSB hB_eq hS_eq
      hsSq_pos hs_pos hs_eq hqs1 htail hprec hε0 hε_half hdual_int j sgn idx
    simpa only [realBody, idealBody, Fin.ext_iff] using h
  have hj_close := closeTo_eval_sampleModNat_clog_add inp.extraBits m
  have hidx_close := closeTo_eval_sampleModNat_clog_add inp.extraBits β
  have hstep_j :
      CloseTo
        ((ProbComp.eval (sampleModNat (Nat.clog 2 m + inp.extraBits) m)).bind fun j =>
          (PMF.uniformOfFintype Bool).bind fun sgn =>
            (ProbComp.eval (sampleModNat (Nat.clog 2 β + inp.extraBits) β)).bind fun idx =>
              realBody j sgn idx)
        (((PMF.uniformOfFintype (Fin m)).map Fin.val).bind fun j =>
          (PMF.uniformOfFintype Bool).bind fun sgn =>
            ((PMF.uniformOfFintype (Fin β)).map Fin.val).bind fun idx =>
              idealBody j sgn idx)
        (ENNReal.ofReal δm +
          (ENNReal.ofReal δm + ENNReal.ofReal ((m : ℝ) * δg + (m : ℝ) * δq))) :=
    hj_close.bind fun jVal hj_mem => by
      rw [PMF.mem_support_map_iff] at hj_mem
      obtain ⟨j, _, rfl⟩ := hj_mem
      exact CloseTo.bind_right _ fun sgn _ =>
        hidx_close.bind fun idxVal hidx_mem => by
          rw [PMF.mem_support_map_iff] at hidx_mem
          obtain ⟨idx, _, rfl⟩ := hidx_mem
          exact hinner j sgn idx
  have herr_sum :
      ENNReal.ofReal δm + (ENNReal.ofReal δm + ENNReal.ofReal ((m : ℝ) * δg + (m : ℝ) * δq)) =
      ENNReal.ofReal (mr07SingleCallErr n m inp.tail inp.prec inp.maxTrials inp.extraBits ε) := by
    rw [← ENNReal.ofReal_add hδm0 (by positivity), ← ENNReal.ofReal_add hδm0 (by positivity)]
    congr 1
    dsimp only [mr07SingleCallErr, δm, δg, δq]
    ring
  have hrhs_fin :
      (((PMF.uniformOfFintype (Fin m)).map Fin.val).bind fun j =>
        (PMF.uniformOfFintype Bool).bind fun sgn =>
          ((PMF.uniformOfFintype (Fin β)).map Fin.val).bind fun idx =>
            idealBody j sgn idx) =
      ((PMF.uniformOfFintype (Fin m)).bind fun j =>
        (PMF.uniformOfFintype Bool).bind fun sgn =>
          (PMF.uniformOfFintype (Fin β)).bind fun idx =>
            let α : ℤ := if sgn then (idx.val + 1 : ℤ) else -((idx.val + 1 : ℤ))
            (PMF.piFin fun i : Fin m =>
              idealGridSample B hB q hq s hs_pos
                (if i = j then (-((α : ℝ)⁻¹)) • ratListToEuclidean n inp.target else 0)).bind
              fun CY =>
              (PMF.uniformOfFintype (Fin m → SublatticeQuot B S)).bind fun V =>
                (ProbComp.eval (F κ (combineMatrix B S q V (fun i => (CY i).1)))).map fun z =>
                  combineOutput B S q V (fun i => (CY i).1) z -
                    ∑ i : Fin m, z i • ((CY i).2 : EuclideanSpace ℝ (Fin n))) := by
    rw [PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun j => ?_)
    dsimp only [Function.comp_apply]
    refine congrArg (PMF.bind _) (funext fun sgn => ?_)
    rw [PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun idx => ?_)
    simp only [Function.comp_apply, idealBody, Fin.ext_iff]
  rw [hrhs_fin, herr_sum] at hstep_j
  exact hstep_j

/-! ### 7. Denominator-Cleared Minimizer & Amplified `mr07IncGDDReduction` -/

/-- Pure-integer scaled squared Euclidean distance `‖D • v - tNum‖²` (zero rational arithmetic
inside the candidate comparison loop). -/
private def scaledSqDist (n D : ℕ) (tNum v : List ℤ) : ℕ :=
  let diff := (List.range n).map fun i => (D : ℤ) * v.getD i 0 - tNum.getD i 0
  (ListMatrix.dotProduct n diff diff).natAbs

/-- Deterministic exact rational squared-distance minimizer over `cands : List (List ℤ)`,
defaulting to `List.replicate n 0` (which is `0 ∈ intLattice B`), reusing
`BareissElimination.{rowDenomProd, clearRow}`. -/
private def closestRatCand (n : ℕ) (t : List ℚ) (cands : List (List ℤ)) : List ℤ :=
  let D := rowDenomProd t
  let tNum := clearRow t
  cands.foldl
    (fun best v =>
      if scaledSqDist n D tNum v < scaledSqDist n D tNum best then v else best)
    (List.replicate n 0)

private theorem scaledSqDist_cast_eq (n : ℕ) (t : List ℚ) (v : List ℤ) :
    ((scaledSqDist n (rowDenomProd t) (clearRow t) v : ℕ) : ℝ) =
      ((rowDenomProd t : ℝ) ^ 2) * ‖listToEuclidean n v - ratListToEuclidean n t‖ ^ 2 := by
  set D := rowDenomProd t
  dsimp only [scaledSqDist]
  rw [ListMatrix.dotProduct_eq_sum_map_range, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  let diff := (List.range n).map fun i => (D : ℤ) * v.getD i 0 - (clearRow t).getD i 0
  have hnn : 0 ≤ ((List.range n).map fun i => diff.getD i 0 * diff.getD i 0).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact mul_self_nonneg _
  have hcast : ((((List.range n).map fun i => diff.getD i 0 * diff.getD i 0).sum).natAbs : ℝ) =
      ((((List.range n).map fun i => diff.getD i 0 * diff.getD i 0).sum : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hnn]
  have hsum_fin : ((List.range n).map fun i => diff.getD i 0 * diff.getD i 0).sum =
      ∑ i : Fin n, diff.getD i.1 0 * diff.getD i.1 0 := by
    rw [Fin.sum_univ_def]
    congr 1
    exact List.ext_getElem (by simp) fun i h₁ h₂ => by simp
  rw [hcast, hsum_fin, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdi : diff.getD i.1 0 = (D : ℤ) * v.getD i.1 0 - (clearRow t).getD i.1 0 := by
    simp [diff, List.getD_eq_getElem?_getD, i.isLt]
  have ht_clear : (((clearRow t).getD i.1 0 : ℤ) : ℝ) = (D : ℝ) * (t.getD i.1 0 : ℝ) := by
    by_cases hi : i.1 < t.length
    · have hi' : i.1 < (clearRow t).length := by simp [clearRow, hi]
      rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi]
      have hq := cast_clearRow_mem (List.getElem_mem hi)
      have hcastR := congrArg (Rat.cast : ℚ → ℝ) hq
      simp only [clearRow, List.getElem_map, Rat.cast_intCast, Rat.cast_mul,
        Rat.cast_natCast] at hcastR ⊢
      exact hcastR
    · have hi' : (clearRow t).length ≤ i.1 := by simp [clearRow]; omega
      rw [List.getD_eq_default _ _ hi', List.getD_eq_default _ _ (by omega)]
      simp
  rw [hdi]
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, ht_clear, PiLp.sub_apply,
    listToEuclidean, ratListToEuclidean, Real.norm_eq_abs, sq_abs]
  ring

private theorem closestRatCand_foldl_props (n D : ℕ) (tNum : List ℤ)
    (init : List ℤ) (cands : List (List ℤ)) :
    let step := fun best v =>
      if scaledSqDist n D tNum v < scaledSqDist n D tNum best then v else best
    let res := cands.foldl step init
    (res = init ∨ res ∈ cands) ∧
    scaledSqDist n D tNum res ≤ scaledSqDist n D tNum init ∧
    (∀ v ∈ cands, scaledSqDist n D tNum res ≤ scaledSqDist n D tNum v) := by
  induction cands generalizing init with
  | nil => simp
  | cons a rest ih =>
    intro step
    simp only [List.foldl_cons]
    set next := step init a
    obtain ⟨hmem, hle_next, hle_rest⟩ := ih next
    have hnext_mem : next = init ∨ next = a := by
      dsimp only [next, step]; split_ifs <;> simp
    have hnext_le_init : scaledSqDist n D tNum next ≤ scaledSqDist n D tNum init := by
      dsimp only [next, step]; split_ifs with h <;> omega
    have hnext_le_a : scaledSqDist n D tNum next ≤ scaledSqDist n D tNum a := by
      dsimp only [next, step]; split_ifs with h <;> omega
    refine ⟨?_, hle_next.trans hnext_le_init, ?_⟩
    · rcases hmem with h | h
      · rcases hnext_mem with h1 | h1
        · exact Or.inl (h.trans h1)
        · exact Or.inr (by rw [h, h1]; exact List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem a h)
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact hle_next.trans hnext_le_a
      · exact hle_rest v hv'

private theorem closestRatCand_mem_or_zero (n : ℕ) (t : List ℚ) (cands : List (List ℤ)) :
    closestRatCand n t cands = List.replicate n 0 ∨ closestRatCand n t cands ∈ cands :=
  (closestRatCand_foldl_props n (rowDenomProd t) (clearRow t) (List.replicate n 0) cands).1

private theorem closestRatCand_norm_le (n : ℕ) (t : List ℚ) {cands : List (List ℤ)}
    {v : List ℤ} (hv : v ∈ cands) :
    ‖listToEuclidean n (closestRatCand n t cands) - ratListToEuclidean n t‖ ≤
      ‖listToEuclidean n v - ratListToEuclidean n t‖ := by
  have hDpos : (0 : ℝ) < (rowDenomProd t : ℝ) := Nat.cast_pos.mpr (rowDenomProd_pos t)
  have hscaled : scaledSqDist n (rowDenomProd t) (clearRow t) (closestRatCand n t cands) ≤
      scaledSqDist n (rowDenomProd t) (clearRow t) v :=
    (closestRatCand_foldl_props n (rowDenomProd t) (clearRow t) (List.replicate n 0) cands).2.2 v hv
  have hR : ((scaledSqDist n (rowDenomProd t) (clearRow t) (closestRatCand n t cands) : ℕ) : ℝ) ≤
      ((scaledSqDist n (rowDenomProd t) (clearRow t) v : ℕ) : ℝ) := by exact_mod_cast hscaled
  rw [scaledSqDist_cast_eq, scaledSqDist_cast_eq] at hR
  have hsq : ‖listToEuclidean n (closestRatCand n t cands) - ratListToEuclidean n t‖ ^ 2 ≤
      ‖listToEuclidean n v - ratListToEuclidean n t‖ ^ 2 :=
    le_of_mul_le_mul_left hR (sq_pos_of_pos hDpos)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem computableInPolyTime_scaledSqDist :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ × List ℤ) × List ℤ => scaledSqDist p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair encUnary (encPair encNat (encList encIntBin))) (encList encIntBin))
      encNat := by
  unfold scaledSqDist
  let encP := encPair (encPair encUnary (encPair encNat (encList encIntBin))) (encList encIntBin)
  have hdiff : ComputableInPolyTime
      (fun p : (ℕ × ℕ × List ℤ) × List ℤ =>
        (List.range p.1.1).map fun k => (p.1.2.1 : ℤ) * p.2.getD k 0 - p.1.2.2.getD k 0)
      encP (encList encIntBin) := by
    have hrange : ComputableInPolyTime
        (fun p : (ℕ × ℕ × List ℤ) × List ℤ => List.range p.1.1) encP (encList encUnary) := by
      fun_prop
    have hbody : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × List ℤ) × List ℤ) × ℕ =>
          (q.1.1.2.1 : ℤ) * q.1.2.getD q.2 0 - q.1.1.2.2.getD q.2 0)
        (encPair encP encUnary) encIntBin := by fun_prop
    exact mapWithInput hrange hbody
  have hn : ComputableInPolyTime (fun p : (ℕ × ℕ × List ℤ) × List ℤ => p.1.1) encP encUnary := by
    fun_prop
  exact intBin_natAbs.comp (listDotProduct.comp (hn.prod (hdiff.prod hdiff)))

private theorem computableInPolyTime_closestRatCand :
    ComputableInPolyTime
      (fun p : (ℕ × List ℚ) × List (List ℤ) => closestRatCand p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList encRat)) (encList (encList encIntBin)))
      (encList encIntBin) := by
  let encIn := encPair (encPair encUnary (encList encRat)) (encList (encList encIntBin))
  let encPar := encPair encUnary (encPair encNat (encList encIntBin))
  let encVec := encList encIntBin
  let par : (ℕ × List ℚ) × List (List ℤ) → ℕ × ℕ × List ℤ :=
    fun p => (p.1.1, (rowDenomProd p.1.2, clearRow p.1.2))
  let init : (ℕ × List ℚ) × List (List ℤ) → List ℤ := fun p => List.replicate p.1.1 0
  let step : (ℕ × ℕ × List ℤ) → List ℤ → List ℤ → List ℤ :=
    fun par best v =>
      if scaledSqDist par.1 par.2.1 par.2.2 v < scaledSqDist par.1 par.2.1 par.2.2 best
      then v else best
  have ht : ComputableInPolyTime (fun p : (ℕ × List ℚ) × List (List ℤ) => p.1.2)
      encIn (encList encRat) :=
    (snd encUnary (encList encRat)).comp (fst _ _)
  have hpar : ComputableInPolyTime par encIn encPar :=
    ((fst encUnary (encList encRat)).comp (fst _ _)).prod
      ((computableInPolyTime_rowDenomProd.comp ht).prod (computableInPolyTime_clearRow.comp ht))
  have hlist : ComputableInPolyTime (fun p : (ℕ × List ℚ) × List (List ℤ) => p.2)
      encIn (encList encVec) := snd _ _
  have hinit : ComputableInPolyTime init encIn encVec := by
    dsimp only [init, encIn, encVec]
    have hn : ComputableInPolyTime (fun p : (ℕ × List ℚ) × List (List ℤ) => p.1.1)
        (encPair (encPair encUnary (encList encRat)) (encList (encList encIntBin))) encUnary := by
      fun_prop
    exact ComputableInPolyTime.replicate hn (.const (0 : ℤ))
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ × List ℤ) × List ℤ) × List ℤ => step q.1.1 q.1.2 q.2)
      (encPair (encPair encPar encVec) encVec) encVec := by
    dsimp only [step]
    have hv : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × List ℤ) × List ℤ) × List ℤ =>
          scaledSqDist q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.2)
        (encPair (encPair encPar encVec) encVec) encNat :=
      computableInPolyTime_scaledSqDist.comp
        (((fst encPar encVec).comp (fst _ _)).prod (snd _ _))
    have hbest : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × List ℤ) × List ℤ) × List ℤ =>
          scaledSqDist q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2)
        (encPair (encPair encPar encVec) encVec) encNat :=
      computableInPolyTime_scaledSqDist.comp
        (((fst encPar encVec).comp (fst _ _)).prod ((snd encPar encVec).comp (fst _ _)))
    exact (binary_lt' hv hbest).ite_decide (snd _ _) ((snd encPar encVec).comp (fst _ _))
  obtain ⟨cI, dI, hcI⟩ := hinit.polyBounded_length.exists_le
  let B : (ℕ × List ℚ) × List (List ℤ) → ℕ := fun p =>
    cI * ((encIn p).length + 1) ^ dI + (encIn p).length
  have hB : PolyBounded (fun p => (encIn p).length) B :=
    (PolyBounded.of_forall_le cI dI fun _ => le_rfl).add
      (PolyBounded.of_forall_le 1 1 fun p => by simp)
  exact ComputableInPolyTime.foldlWith (encA := encVec) (encB := encVec)
    (encL := encList encVec) (encP := encPar)
    hpar hlist hinit hstep (B := B) hB fun p i _ => by
      have hmem := (closestRatCand_foldl_props p.1.1 (rowDenomProd p.1.2)
        (clearRow p.1.2) (init p) (p.2.take i)).1
      rcases hmem with heq | hmem_take
      · rw [heq]
        exact (hcI p).trans (Nat.le_add_right _ _)
      · have hmem_p2 : ((p.2.take i).foldl (step (par p)) (init p)) ∈ p.2 :=
          List.mem_of_mem_take hmem_take
        have hlen1 : (encVec ((p.2.take i).foldl (step (par p)) (init p))).length ≤
            (encList encVec p.2).length :=
          SizedListEncoding.length_elem_le p.2 _ hmem_p2
        have hlen2 : (encList encVec p.2).length ≤ (encIn p).length := by
          simp only [encIn, encVec, length_encPair]
          omega
        exact (hlen1.trans hlen2).trans (Nat.le_add_left _ _)

/-- Amplified strict-PPT `IncGDD` reduction: runs `inp.trials` independent calls to
`singleIncGDDCall P F inp` via `OracleComp.replicate` and outputs the closest lattice vector to
`inp.target`. -/
noncomputable def mr07IncGDDReduction (P : SISParams) (F : P.Solver) (inp : IncGDDInput) :
    ProbComp (List ℤ) := do
  let cands ← OracleComp.replicate inp.trials (singleIncGDDCall P F inp)
  pure (closestRatCand (P.n inp.secParam) inp.target cands)

/-- Strict-PPT efficiency certificate for `mr07IncGDDReduction` (finite step toward
`[MicciancioRegev2007]` Theorem 5.9). -/
theorem isPPTOn_mr07IncGDDReduction {P : SISParams} (hP : MR07ParamPolyTime P)
    {F : P.Solver} (hF : F.IsPPT) :
    IsPPTOn IncGDDInput.enc (encList encIntBin) (mr07IncGDDReduction P F) := by
  have htrials : ComputableInPolyTime IncGDDInput.trials IncGDDInput.enc encUnary := by fun_prop
  have hdim : ComputableInPolyTime (fun inp : IncGDDInput => P.n inp.secParam)
      IncGDDInput.enc encUnary :=
    hP.hn.comp (by fun_prop : ComputableInPolyTime IncGDDInput.secParam IncGDDInput.enc encUnary)
  have htarget : ComputableInPolyTime IncGDDInput.target IncGDDInput.enc (encList encRat) := by
    fun_prop
  have hrep : IsPPTOn IncGDDInput.enc (encList (encList encIntBin))
      (fun inp => OracleComp.replicate inp.trials (singleIncGDDCall P F inp)) :=
    (isPPTOn_singleIncGDDCall hP hF).replicate htrials
  have hpost : ComputableInPolyTime
      (fun p : IncGDDInput × List (List ℤ) => closestRatCand (P.n p.1.secParam) p.1.target p.2)
      (encPair IncGDDInput.enc (encList (encList encIntBin))) (encList encIntBin) :=
    computableInPolyTime_closestRatCand.comp
      (((hdim.comp (fst IncGDDInput.enc _)).prod (htarget.comp (fst IncGDDInput.enc _))).prod
        (snd IncGDDInput.enc _))
  refine (hrep.map_with (f := fun inp cands => closestRatCand (P.n inp.secParam) inp.target cands)
    hpost).congr fun inp => ?_
  simp only [mr07IncGDDReduction, bind_pure_comp]

/-- Unconditional lattice membership on 100% of the support of `mr07IncGDDReduction`. -/
theorem mem_support_mr07IncGDDReduction_mem_intLattice
    (P : SISParams) (F : P.Solver) (inp : IncGDDInput)
    (B S : Matrix (Fin (P.n inp.secParam)) (Fin (P.n inp.secParam)) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (hB_eq : inp.basisB = RowTable.ofMatrix B) (hS_eq : inp.basisS = RowTable.ofMatrix S)
    {v : List ℤ} (hv : v ∈ (ProbComp.eval (mr07IncGDDReduction P F inp)).support) :
    v.length = P.n inp.secParam ∧ listToEuclidean (P.n inp.secParam) v ∈ intLattice B := by
  unfold mr07IncGDDReduction at hv
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hv
  obtain ⟨cands, hcands, rfl⟩ := hv
  rw [ProbComp.mem_support_replicate_iff] at hcands
  rcases closestRatCand_mem_or_zero (P.n inp.secParam) inp.target cands with heq | hmem
  · rw [heq]
    refine ⟨by simp, ?_⟩
    have h0 : listToEuclidean (P.n inp.secParam) (List.replicate (P.n inp.secParam) 0) = 0 := by
      ext r; simp [listToEuclidean, List.getD_eq_getElem?_getD]
    rw [h0]
    exact (intLattice B).zero_mem
  · exact mem_support_singleIncGDDCall_mem_intLattice P F inp B S hB hS hSB hB_eq hS_eq
      (hcands.2 _ hmem)

/-- Finite-parameter amplified `IncGDD` failure bound (step toward `[MicciancioRegev2007]`
Theorem 5.9, §5.2, pp. 22–24): combining `closeTo_eval_singleIncGDDCall_idealIncGDDStep`,
`MR07Core.incGDD_succProb_of_closeTo_idealIncGDDStep`, and independent amplification via
`OracleComp.replicate`. -/
theorem mr07IncGDDReduction_succProb_ge
    (P : SISParams) (F : P.Solver) (inp : IncGDDInput)
    (hn : 1 ≤ P.n inp.secParam) (hm : 1 ≤ P.m inp.secParam) (hβ : 1 ≤ P.β inp.secParam)
    (hrSq : 0 < inp.rSq) (htail : 1 ≤ inp.tail)
    (hprec : 8 * (2 * inp.tail + 6) ≤ 2 ^ inp.prec)
    (B S : Matrix (Fin (P.n inp.secParam)) (Fin (P.n inp.secParam)) ℤ)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (hB_eq : inp.basisB = RowTable.ofMatrix B) (hS_eq : inp.basisS = RowTable.ofMatrix S)
    {g ε pSingle : ℝ} (hg : 0 < g) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (400 * max 1 (Real.sqrt (P.m inp.secParam))))
    (hq : g * (P.n inp.secParam : ℝ) * Real.sqrt (P.m inp.secParam) * (P.β inp.secParam : ℝ) ≤
      (P.q inp.secParam : ℝ))
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin (P.n inp.secParam)))) (intLattice B))
        (2 / (2 * Real.sqrt (inp.rSq : ℝ) /
          ((P.β inp.secParam : ℝ) * Real.sqrt (P.n inp.secParam)))) 0 - 1 ≤ ε)
    (hp_le :
      pSingle ≤
        (1 / 3 : ℝ) *
          ((sisEll2Advantage (P.q inp.secParam) (P.β inp.secParam : ℝ) (F inp.secParam) : ℝ) /
              (2 * (P.β inp.secParam : ℝ) * (P.m inp.secParam : ℝ)) -
            (P.m inp.secParam : ℝ) * ε / (2 * (1 - ε))) -
        mr07SingleCallErr (P.n inp.secParam) (P.m inp.secParam)
          inp.tail inp.prec inp.maxTrials inp.extraBits ε) :
    let κ := inp.secParam
    let n := P.n κ
    let r : ℝ := Real.sqrt (inp.rSq : ℝ)
    let t := ratListToEuclidean n inp.target
    ((ProbComp.eval (mr07IncGDDReduction P F inp)).toOuterMeasure
      {v | ¬ (v.length = n ∧ IncGDD.IsSolution g (intLattice B) (intColCast B S hB) t r
        (listToEuclidean n v))}).toReal ≤
      (1 - pSingle) ^ inp.trials := by
  intro κ n r t
  set m := P.m κ
  set β := P.β κ
  have hε_half : ε ≤ 1 / 2 := by
    have hmax : (1 : ℝ) ≤ max 1 (Real.sqrt m) := le_max_left _ _
    have h400 : ε ≤ 1 / 400 :=
      hε.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith))
    linarith
  have h1me : 0 < 1 - ε := by linarith
  have hbase_nn : 0 ≤ 1 - 1 / (16 * (2 * (inp.tail : ℝ) + 6)) := by
    have hden : (1 : ℝ) ≤ 16 * (2 * (inp.tail : ℝ) + 6) := by
      linarith [Nat.cast_nonneg (α := ℝ) inp.tail]
    have hinv : 1 / (16 * (2 * (inp.tail : ℝ) + 6)) ≤ 1 := div_le_one_of_le₀ hden (by positivity)
    linarith
  have hη0 : 0 ≤ mr07SingleCallErr n m inp.tail inp.prec inp.maxTrials inp.extraBits ε := by
    dsimp only [mr07SingleCallErr]; positivity
  have hβR : (1 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβ
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hrSq)
  have hclose := closeTo_eval_singleIncGDDCall_idealIncGDDStep P F inp hn hm hβ hrSq htail hprec
    B S hB hS hSB hB_eq hS_eq hε0 hε_half hdual
  have hsucc := incGDD_succProb_of_closeTo_idealIncGDDStep hn hm B S hB hS hSB hβR hg hr
    hε0 hε hη0 hq hdual t (F κ) _ hclose
  rw [Nat.floor_natCast] at hsucc
  let Good : Set (List ℤ) := {v | IncGDD.IsSolution g (intLattice B) (intColCast B S hB) t r
    (listToEuclidean n v)}
  have hsingle_good :
      pSingle ≤ ((ProbComp.eval (singleIncGDDCall P F inp)).toOuterMeasure Good).toReal := by
    have heq : ((ProbComp.eval (singleIncGDDCall P F inp)).map (listToEuclidean n)).toOuterMeasure
        {u | IncGDD.IsSolution g (intLattice B) (intColCast B S hB) t r u} =
        (ProbComp.eval (singleIncGDDCall P F inp)).toOuterMeasure Good := by
      rw [PMF.toOuterMeasure_map_apply]; rfl
    rw [heq] at hsucc
    exact hp_le.trans hsucc
  have hsingle_fail :
      ((ProbComp.eval (singleIncGDDCall P F inp)).toOuterMeasure Goodᶜ).toReal ≤ 1 - pSingle := by
    have hcompl := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl
      (ProbComp.eval (singleIncGDDCall P F inp)) Good
    linarith
  let FailOut : Set (List ℤ) := {v | ¬ (v.length = n ∧ IncGDD.IsSolution g (intLattice B)
    (intColCast B S hB) t r (listToEuclidean n v))}
  let isBad : List ℤ → Bool := fun v => by classical exact decide (v ∈ Goodᶜ)
  have hisBad_eq : {v | isBad v = true} = Goodᶜ := by
    ext v; simp [isBad]
  have hmeas_le :
      (ProbComp.eval (mr07IncGDDReduction P F inp)).toOuterMeasure FailOut ≤
      (ProbComp.eval (OracleComp.replicate inp.trials (singleIncGDDCall P F inp))).toOuterMeasure
        {cands | ∀ c ∈ cands, isBad c = true} := by
    have hmap : ProbComp.eval (mr07IncGDDReduction P F inp) =
        (ProbComp.eval (OracleComp.replicate inp.trials (singleIncGDDCall P F inp))).map
          (closestRatCand n inp.target) := by
      dsimp only [mr07IncGDDReduction]
      rw [ProbComp.eval_bind]
      simp only [ProbComp.eval_pure]
      rfl
    rw [hmap, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun cands => ?_
    by_cases hsupp : cands ∈ (ProbComp.eval (OracleComp.replicate inp.trials
        (singleIncGDDCall P F inp))).support
    · by_cases hfail : cands ∈ closestRatCand n inp.target ⁻¹' FailOut
      · have hall_bad :
            cands ∈ ({cands | ∀ c ∈ cands, isBad c = true} : Set (List (List ℤ))) := by
          intro c hc
          have hc' : c ∈ Goodᶜ := by
            intro hgood
            apply hfail
            have hbest : (closestRatCand n inp.target cands).length = n ∧
                listToEuclidean n (closestRatCand n inp.target cands) ∈ intLattice B := by
              rcases closestRatCand_mem_or_zero n inp.target cands with heq | hmem
              · rw [heq]
                refine ⟨by simp, ?_⟩
                have h0 : listToEuclidean n (List.replicate n 0) = 0 := by
                  ext i; simp [listToEuclidean, List.getD_eq_getElem?_getD]
                rw [h0]
                exact (intLattice B).zero_mem
              · exact mem_support_singleIncGDDCall_mem_intLattice P F inp B S hB hS hSB hB_eq hS_eq
                  (((ProbComp.mem_support_replicate_iff _ _ _).mp hsupp).2 _ hmem)
            refine ⟨hbest.1, hbest.2, ?_⟩
            exact (closestRatCand_norm_le n inp.target hc).trans hgood.dist_le
          simpa [isBad] using hc'
        rw [Set.indicator_of_mem hfail, Set.indicator_of_mem hall_bad]
      · rw [Set.indicator_of_notMem hfail]
        exact zero_le
    · have h0 : ProbComp.eval (OracleComp.replicate inp.trials (singleIncGDDCall P F inp)) cands =
          0 := by
        simpa [PMF.mem_support_iff] using hsupp
      simp only [Set.indicator_apply]
      split_ifs <;> simp [h0]
  have hrep := ProbComp.toOuterMeasure_replicate_forall (singleIncGDDCall P F inp) isBad inp.trials
  have hle_enn :
      (ProbComp.eval (mr07IncGDDReduction P F inp)).toOuterMeasure FailOut ≤
      ((ProbComp.eval (singleIncGDDCall P F inp)).toOuterMeasure Goodᶜ) ^ inp.trials := by
    rw [← hisBad_eq, ← hrep]
    exact hmeas_le
  have htoR := ENNReal.toReal_mono
    (ENNReal.pow_ne_top (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)) hle_enn
  rw [ENNReal.toReal_pow] at htoR
  exact htoR.trans (pow_le_pow_left₀ ENNReal.toReal_nonneg hsingle_fail inp.trials)

end Cslib.Crypto.SIS.MR07
