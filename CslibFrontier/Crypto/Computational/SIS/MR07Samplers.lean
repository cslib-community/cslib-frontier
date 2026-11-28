/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Rational.Runtime.Determinant
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
public import CslibFrontier.Computability.Probabilistic.DiscreteGaussian1D
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Crypto.Computational.SIS.MR07Core
public import CslibFrontier.Foundations.Data.List.DotProduct
public import CslibFrontier.Foundations.Probability.Gaussian.Int
public import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter
public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
public import Mathlib.Data.ZMod.Basic

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Traverse
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.CloseTo.UniformNat
import CslibFrontier.Languages.Probabilistic.Traverse
import CslibFrontier.Probability.StatisticalDistance.Product
import CslibFrontier.Probability.UniformNat
import Mathlib.Data.List.GetD

/-!
# Strict-PPT discrete-grid Gaussian and HNF-free quotient samplers

This module constructs the two lattice-specific strict probabilistic polynomial-time (`IsPPTOn`)
samplers supporting the Micciancio–Regev `IncGDD` to `ℓ₂`-SIS reduction (`MR07Core`):

1. `Cslib.Crypto.SIS.MR07.sampleGridGaussian`: draws `dim` independent 1-D discrete Gaussian
   coordinates via `sampleZ` at width `q · √(sSq)` and center `q · t_i`, then reduces into the
   fundamental parallelepiped via `gridReduceInt` (built on `solveFloorMul`, `ratSolve`,
   `Rat.floor`, and `ListMatrix.dotProduct`).
2. `Cslib.Crypto.SIS.MR07.sampleQuotientModS`: computes the quotient index
   `D = |det S| / |det B|` via staged Bird determinants (`quotientIndex`), samples `dim`
   near-uniform coordinates in `ZMod D` via `sampleModNat`, and reduces modulo `P(S)` via
   `quotientReduceInt` (built on `solveFloorMul` and `ListMatrix.dotProduct`).

In addition to unconditional strict-PPT and product-pushforward `CloseTo` certificates, this module
proves exact matrix specifications (`solveFloorMul_spec`, `quotientIndex_eq_natAbs_div_det`,
`gridReduceInt_spec`, `quotientReduceInt_spec`) and typed-law bridges connecting the executable
list samplers directly to `idealGridSample` on `GridRep B q × intLattice B` (via
`gridPairToLists` / `decodeGridPair`) and to `PMF.uniformOfFintype (SublatticeQuot B S)` (via
`sublatticeQuotToList` / `decodeSublatticeQuot`).

## Main definitions

* `Cslib.Crypto.SIS.MR07.solveFloorMul`: shared polynomial-time rational solve, `Rat.floor`, and
  integer multiply-back helper (`ListMatrix.dotProduct`).
* `Cslib.Crypto.SIS.MR07.GridSampleInput`, `gridReduceInt`, `sampleGridGaussian`: discrete-grid
  Gaussian sampler and input encoding.
* `Cslib.Crypto.SIS.MR07.QuotientSampleInput`, `quotientIndex`, `quotientReduceInt`,
  `sampleQuotientModS`: HNF-free quotient sampler and input encoding.
* `Cslib.Crypto.SIS.MR07.gridEmbed`, `gridPairToLists`, `decodeGridPair`,
  `sublatticeQuotToList`, `decodeSublatticeQuot`: canonical injective list encodings and
  left-inverse decoders between list outputs and `MR07Core`'s typed lattice interfaces.

## Main results

* `Cslib.Crypto.SIS.MR07.isPPTOn_sampleGridGaussian`,
  `Cslib.Crypto.SIS.MR07.closeTo_eval_sampleGridGaussian_pi`,
  `Cslib.Crypto.SIS.MR07.closeTo_eval_sampleGridGaussian_pi_of_smoothingParameter_le`,
  `Cslib.Crypto.SIS.MR07.mem_support_sampleGridGaussian`: strict-PPT, product-pushforward
  `CloseTo`, and support certificates for `sampleGridGaussian`.
* `Cslib.Crypto.SIS.MR07.isPPTOn_sampleQuotientModS`,
  `Cslib.Crypto.SIS.MR07.closeTo_eval_sampleQuotientModS_pi`,
  `Cslib.Crypto.SIS.MR07.mem_support_sampleQuotientModS`: strict-PPT, product-pushforward
  `CloseTo`, and support certificates for `sampleQuotientModS`.
* `Cslib.Crypto.SIS.MR07.solveFloorMul_spec`,
  `Cslib.Crypto.SIS.MR07.quotientIndex_eq_natAbs_div_det`,
  `Cslib.Crypto.SIS.MR07.gridReduceInt_spec`,
  `Cslib.Crypto.SIS.MR07.quotientReduceInt_spec`: exact `IntTable` / `WellFormed`
  specifications connecting executable list reductions to `MR07Core` lattice geometry.
* `Cslib.Crypto.SIS.MR07.piFin_discreteGaussianInt_map_gridEmbed`,
  `Cslib.Crypto.SIS.MR07.map_gridReduceInt_piFin_eq_map_idealGridSample`,
  `Cslib.Crypto.SIS.MR07.closeTo_eval_sampleGridGaussian_idealGridSample`,
  `Cslib.Crypto.SIS.MR07.closeTo_eval_sampleGridGaussian_idealGridSample_of_smoothingParameter_le`,
  `Cslib.Crypto.SIS.MR07.mem_support_sampleGridGaussian_exists_gridRep`: typed-law bridge and
  lossless support recovery from `sampleGridGaussian` to `idealGridSample`.
* `Cslib.Crypto.SIS.MR07.quotientReduceInt_eq_quotientHom`,
  `Cslib.Crypto.SIS.MR07.map_quotientReduceInt_piFin_eq_map_uniform`,
  `Cslib.Crypto.SIS.MR07.closeTo_eval_sampleQuotientModS_uniform`,
  `Cslib.Crypto.SIS.MR07.mem_support_sampleQuotientModS_exists_sublatticeQuot`: typed-law bridge
  and lossless support recovery from `sampleQuotientModS` to
  `PMF.uniformOfFintype (SublatticeQuot B S)`.

## References

* [D. Micciancio and O. Regev, *Worst-Case to Average-Case Reductions Based on Gaussian
  Measures*][MicciancioRegev2007], §2 (p. 8) and §5.2 (Lemmas 5.7–5.8, pp. 20–21 of the
  December 27, 2005 author's copy).
-/

public section

namespace Cslib.Crypto.SIS.MR07

open Turing.MultiTapeTM ComputableInPolyTime Cslib.LinearAlgebra Cslib.Probability Cslib.ProbComp
open Mathlib.Tactic.Matrix ZLattice
open scoped IntTable RatTable LinearSystemInput LinearSolveResult SampleZInput
open scoped ENNReal RealInnerProductSpace _root_.Matrix

attribute [local irreducible] SampleZInput.enc IntTable.enc RatTable.enc
  LinearSystemInput.enc LinearSolveResult.enc encRat encIntBin encNat encUnary

/-! ### 1. Shared linear-algebra helpers (`ListMatrix.dotProduct`, `Rat.floor`, `solveFloorMul`) -/

/-- Convert an `IntTable` to a `RatTable` by casting each entry to `ℚ`. -/
private def intTableToRatTable (B : IntTable) : RatTable :=
  ⟨B.numRows, B.numCols, B.rows.map fun row => row.map (Int.cast : ℤ → ℚ)⟩

private theorem computableInPolyTime_intTableToRatTable :
    ComputableInPolyTime intTableToRatTable IntTable.enc RatTable.enc := by
  fun_prop [intTableToRatTable]

/-- Row-wise integer matrix-vector multiplication via `ListMatrix.dotProduct`. -/
private theorem computableInPolyTime_intTableMulVec :
    ComputableInPolyTime
      (fun p : IntTable × List ℤ =>
        (List.range p.1.numRows).map fun r =>
          ListMatrix.dotProduct p.1.numCols (p.1.rows.getD r []) p.2)
      (encPair IntTable.enc (encList encIntBin)) (encList encIntBin) := by
  let encIn := encPair IntTable.enc (encList encIntBin)
  have hrows : ComputableInPolyTime (fun p : IntTable × List ℤ => List.range p.1.numRows)
      encIn (encList encUnary) := by
    have hnr : ComputableInPolyTime (fun p : IntTable × List ℤ => p.1.numRows)
        encIn encUnary := by fun_prop
    exact unary_range' hnr
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

/-- Shared exact rational-solve, coordinatewise `Rat.floor`, and integer multiply-back helper:
solves `mat *ᵥ ξ = rhs`, sets `k = ⌊ξ⌋`, and returns `mat *ᵥ k` via `ListMatrix.dotProduct`. -/
def solveFloorMul (dim : ℕ) (mat : IntTable) (rhs : List ℚ) : List ℤ :=
  let matRat : RatTable :=
    ⟨mat.numRows, mat.numCols, mat.rows.map fun row => row.map (Int.cast : ℤ → ℚ)⟩
  let sol := (ratSolve ⟨matRat, rhs⟩).solution.getD (List.replicate dim 0)
  let k := (List.range dim).map fun i => (sol.getD i 0).floor
  (List.range mat.numRows).map fun r =>
    ListMatrix.dotProduct mat.numCols (mat.rows.getD r []) k

private theorem computableInPolyTime_solveFloorMul {α : Type} {encIn : α ↪ List Bool}
    {dim : α → ℕ} {mat : α → IntTable} {rhs : α → List ℚ}
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hmat : ComputableInPolyTime mat encIn IntTable.enc)
    (hrhs : ComputableInPolyTime rhs encIn (encList encRat)) :
    ComputableInPolyTime (fun a => solveFloorMul (dim a) (mat a) (rhs a))
      encIn (encList encIntBin) := by
  have hmatRat : ComputableInPolyTime (fun a => intTableToRatTable (mat a))
      encIn RatTable.enc := computableInPolyTime_intTableToRatTable.comp hmat
  have hsys : ComputableInPolyTime
      (fun a => LinearSystemInput.mk (intTableToRatTable (mat a)) (rhs a))
      encIn LinearSystemInput.enc := by fun_prop
  have hres := ratSolve_computableInPolyTime.comp hsys
  have hsol : ComputableInPolyTime
      (fun a => (ratSolve ⟨intTableToRatTable (mat a), rhs a⟩).solution.getD
        (List.replicate (dim a) 0))
      encIn (encList encRat) :=
    optionGetDWithInput (by fun_prop) (by fun_prop)
  have hk : ComputableInPolyTime
      (fun a => (List.range (dim a)).map fun i =>
        (((ratSolve ⟨intTableToRatTable (mat a), rhs a⟩).solution.getD
          (List.replicate (dim a) 0)).getD i 0).floor)
      encIn (encList encIntBin) := by
    have := hsol.comp (fst encIn encUnary)
    exact mapWithInput (unary_range' hdim) (by fun_prop)
  dsimp only [solveFloorMul, intTableToRatTable] at hk ⊢
  exact (hmat.prod hk).trans computableInPolyTime_intTableMulVec

private theorem computableInPolyTime_gridRhs {α : Type} {encIn : α ↪ List Bool}
    {dim : α → ℕ} {q : α → ℤ} {r' : α → List ℤ}
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hq : ComputableInPolyTime q encIn encIntBin)
    (hr' : ComputableInPolyTime r' encIn (encList encIntBin)) :
    ComputableInPolyTime
      (fun a => (List.range (dim a)).map fun i => Rat.divInt (-((r' a).getD i 0)) (q a))
      encIn (encList encRat) := by
  fun_prop

private theorem computableInPolyTime_gridPost {α : Type} {encIn : α ↪ List Bool}
    {dim : α → ℕ} {q : α → ℤ} {r' bk : α → List ℤ}
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hq : ComputableInPolyTime q encIn encIntBin)
    (hr' : ComputableInPolyTime r' encIn (encList encIntBin))
    (hbk : ComputableInPolyTime bk encIn (encList encIntBin)) :
    ComputableInPolyTime
      (fun a =>
        ((List.range (dim a)).map fun i => -((r' a).getD i 0) - q a * (bk a).getD i 0,
         (List.range (dim a)).map fun i => -((bk a).getD i 0)))
      encIn (encPair (encList encIntBin) (encList encIntBin)) := by
  fun_prop

private theorem computableInPolyTime_vecIntToRat {α : Type} {encIn : α ↪ List Bool}
    {dim : α → ℕ} {v : α → List ℤ}
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hv : ComputableInPolyTime v encIn (encList encIntBin)) :
    ComputableInPolyTime
      (fun a => (List.range (dim a)).map fun i => ((v a).getD i 0 : ℚ))
      encIn (encList encRat) := by
  fun_prop

private theorem computableInPolyTime_vecSub {α : Type} {encIn : α ↪ List Bool}
    {dim : α → ℕ} {u v : α → List ℤ}
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hu : ComputableInPolyTime u encIn (encList encIntBin))
    (hv : ComputableInPolyTime v encIn (encList encIntBin)) :
    ComputableInPolyTime
      (fun a => (List.range (dim a)).map fun i => (u a).getD i 0 - (v a).getD i 0)
      encIn (encList encIntBin) := by
  fun_prop

/-! ### 2. Strict-PPT discrete-grid Gaussian sampler (`sampleGridGaussian`) -/

/-- Input specification for the discrete-grid Gaussian sampler `sampleGridGaussian`
([MicciancioRegev2007], Lemma 5.7, p. 20). -/
structure GridSampleInput where
  /-- Ambient lattice dimension `n`. -/
  dim : ℕ
  /-- Integer grid modulus `q > 0`. -/
  modulus : ℕ
  /-- Basis matrix `B` of the lattice `L(B)` (columns are basis vectors). -/
  basis : IntTable
  /-- Rational squared Gaussian width `s² > 0`. -/
  sSq : ℚ
  /-- Target center `t ∈ ℚ^n`. -/
  target : List ℚ
  /-- Unary tail-cutoff multiplier `t_tail` passed to `sampleZ`. -/
  tail : ℕ
  /-- Unary dyadic acceptance-coin precision `prec` passed to `sampleZ`. -/
  prec : ℕ
  /-- Unary rejection-trial cap `maxTrials` passed to `sampleZ`. -/
  maxTrials : ℕ
  deriving DecidableEq, Repr

namespace GridSampleInput

/-- Framing encoding of `GridSampleInput` (binary `modulus` to permit super-polynomial `q`). -/
enc_structure enc : GridSampleInput where
  dim : encUnary, modulus : encNat, basis : IntTable.enc, sSq : encRat,
  target : (encList encRat), tail : encUnary, prec : encUnary, maxTrials : encUnary

end GridSampleInput

open scoped GridSampleInput
attribute [local irreducible] GridSampleInput.enc

/-- Exact integer grid reduction: given `r' ∈ ℤ^dim`, computes `bk = solveFloorMul dim B (-r' / q)`
and returns `(u, y) = (-r' - q • bk, -bk)`. -/
def gridReduceInt (dim q : ℕ) (B : IntTable) (r' : List ℤ) : List ℤ × List ℤ :=
  let rhs : List ℚ := (List.range dim).map fun i => Rat.divInt (-(r'.getD i 0)) (q : ℤ)
  let bk : List ℤ := solveFloorMul dim B rhs
  ((List.range dim).map fun i => -(r'.getD i 0) - (q : ℤ) * bk.getD i 0,
   (List.range dim).map fun i => -(bk.getD i 0))

/-- Coordinate `i` 1-D input for `sampleGridGaussian`. -/
private def gridCoordInput (inp : GridSampleInput) (i : ℕ) : SampleZInput :=
  ⟨((inp.modulus : ℚ) ^ 2) * inp.sSq, (inp.modulus : ℚ) * inp.target.getD i 0,
    inp.tail, inp.prec, inp.maxTrials⟩

/-- Strict-PPT discrete-grid Gaussian sampler (`r' ~ D_{ℤ^dim, q*s, q*t}` followed by exact
`gridReduceInt`). -/
noncomputable def sampleGridGaussian (inp : GridSampleInput) : ProbComp (List ℤ × List ℤ) := do
  let r' ← (List.range inp.dim).mapM fun i => sampleZ (gridCoordInput inp i)
  pure (gridReduceInt inp.dim inp.modulus inp.basis r')

private theorem computableInPolyTime_gridReduceInt :
    ComputableInPolyTime
      (fun p : GridSampleInput × List ℤ => gridReduceInt p.1.dim p.1.modulus p.1.basis p.2)
      (encPair GridSampleInput.enc (encList encIntBin))
      (encPair (encList encIntBin) (encList encIntBin)) := by
  have hrhs := computableInPolyTime_gridRhs
    (dim := fun p : GridSampleInput × List ℤ => p.1.dim)
    (q := fun p => (p.1.modulus : ℤ)) (r' := Prod.snd)
    (by fun_prop) (by fun_prop) (snd _ _)
  have hbk := computableInPolyTime_solveFloorMul
    (dim := fun p : GridSampleInput × List ℤ => p.1.dim)
    (mat := fun p => p.1.basis) (by fun_prop) (by fun_prop) hrhs
  exact computableInPolyTime_gridPost
    (dim := fun p : GridSampleInput × List ℤ => p.1.dim)
    (q := fun p => (p.1.modulus : ℤ)) (r' := Prod.snd)
    (by fun_prop) (by fun_prop) (snd _ _) hbk

/-- Strict-PPT certificate for `sampleGridGaussian`. -/
theorem isPPTOn_sampleGridGaussian :
    IsPPTOn GridSampleInput.enc (encPair (encList encIntBin) (encList encIntBin))
      sampleGridGaussian := by
  have hcoord : ComputableInPolyTime (fun p : GridSampleInput × ℕ => gridCoordInput p.1 p.2)
      (encPair GridSampleInput.enc encUnary) SampleZInput.enc := by
    fun_prop [gridCoordInput]
  have htrav : IsPPTOn GridSampleInput.enc (encList encIntBin)
      (fun inp => (List.range inp.dim).mapM fun i => sampleZ (gridCoordInput inp i)) :=
    IsPPTOn.mapMWith (isPPTOn_sampleZ.preprocess hcoord) (by fun_prop)
  have hres := htrav.map_with
    (f := fun inp r' => gridReduceInt inp.dim inp.modulus inp.basis r')
    computableInPolyTime_gridReduceInt
  refine hres.congr fun inp => ?_
  simp only [sampleGridGaussian, bind_pure_comp]

/-- `CloseTo` bound for `sampleGridGaussian` against `PMF.piFin` of 1-D discrete Gaussians at
width `q * √sSq` and centers `q * t_i`, pushed forward by `gridReduceInt`. -/
theorem closeTo_eval_sampleGridGaussian_pi
    (inp : GridSampleInput) (hsSq : 0 < inp.sSq) (hq : 0 < inp.modulus)
    (hqs1 : 1 ≤ (inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ)) (ht : 1 ≤ inp.tail)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hdual : ZLattice.gaussianMass
      (LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal)
      (1 / ((inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ))) 0 - 1 ≤ ε)
    (hprec : 8 * (2 * inp.tail + 6) ≤ 2 ^ inp.prec) :
    CloseTo (ProbComp.eval (sampleGridGaussian inp))
      ((PMF.piFin fun i : Fin inp.dim =>
          discreteGaussianInt ((inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ))
            (by positivity) ((inp.modulus : ℝ) * (inp.target.getD i.val 0 : ℝ))).map
        fun r => gridReduceInt inp.dim inp.modulus inp.basis (List.ofFn r))
      (ENNReal.ofReal ((inp.dim : ℝ) *
        ((1 - 1 / (16 * (2 * inp.tail + 6 : ℝ))) ^ inp.maxTrials
          + (8 * inp.tail + 24 : ℝ) / (2 : ℝ) ^ inp.prec
          + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2))))) := by
  set s := Real.sqrt (inp.sSq : ℝ)
  set qs := (inp.modulus : ℝ) * s
  have hqs_pos : 0 < qs := by positivity
  set Δ := (1 - 1 / (16 * (2 * (inp.tail : ℝ) + 6))) ^ inp.maxTrials
      + (8 * (inp.tail : ℝ) + 24) / (2 : ℝ) ^ inp.prec
      + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2))
  have hcoord (i : Fin inp.dim) :
      CloseTo (ProbComp.eval (sampleZ (gridCoordInput inp i.val)))
        (discreteGaussianInt qs hqs_pos
          ((inp.modulus : ℝ) * (inp.target.getD i.val 0 : ℝ)))
        (ENNReal.ofReal Δ) := by
    have hq_pos_q : (0 : ℚ) < (inp.modulus : ℚ) := by exact_mod_cast hq
    have hsSq' : 0 < (gridCoordInput inp i.val).sSq := by
      dsimp only [gridCoordInput]
      exact mul_pos (sq_pos_of_pos hq_pos_q) hsSq
    have hsqrt_eq : Real.sqrt (((gridCoordInput inp i.val).sSq : ℚ) : ℝ) = qs := by
      dsimp only [gridCoordInput, qs, s]
      push_cast
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
    have hcenter_eq : ((gridCoordInput inp i.val).center : ℝ) =
        (inp.modulus : ℝ) * (inp.target.getD i.val 0 : ℝ) := by
      dsimp only [gridCoordInput]; push_cast; rfl
    have h := closeTo_eval_sampleZ_discreteGaussian (gridCoordInput inp i.val) hsSq'
      (by rwa [hsqrt_eq]) ht hε0 hε (by rwa [hsqrt_eq]) hprec
    have hdgInt_eq :
        discreteGaussianInt (Real.sqrt (((gridCoordInput inp i.val).sSq : ℚ) : ℝ))
          (by positivity) ((gridCoordInput inp i.val).center : ℝ) =
        discreteGaussianInt qs hqs_pos
          ((inp.modulus : ℝ) * (inp.target.getD i.val 0 : ℝ)) := by
      congr 1
    rwa [hdgInt_eq] at h
  have hpi := CloseTo.piFin hcoord
  have hmul_eq : (inp.dim : ℝ≥0∞) * ENNReal.ofReal Δ = ENNReal.ofReal ((inp.dim : ℝ) * Δ) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hmul_eq] at hpi
  have heval : ProbComp.eval (sampleGridGaussian inp) =
      (PMF.piFin fun i : Fin inp.dim =>
        ProbComp.eval (sampleZ (gridCoordInput inp i.val))).map
        fun r => gridReduceInt inp.dim inp.modulus inp.basis (List.ofFn r) := by
    unfold sampleGridGaussian
    rw [bind_pure_comp, ProbComp.eval_map, ProbComp.eval_mapM_range, PMF.map_comp]
    rfl
  rw [heval]
  exact hpi.map _

/-- Smoothing-parameter (`η_ε(ℤ) ≤ q · √sSq`) form of `closeTo_eval_sampleGridGaussian_pi`. -/
theorem closeTo_eval_sampleGridGaussian_pi_of_smoothingParameter_le
    (inp : GridSampleInput) (hsSq : 0 < inp.sSq) (hq : 0 < inp.modulus)
    (hqs1 : 1 ≤ (inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ)) (ht : 1 ≤ inp.tail)
    {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1 / 2)
    (hη : ZLattice.smoothingParameter intLatticeReal ε ≤
      (inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ))
    (hprec : 8 * (2 * inp.tail + 6) ≤ 2 ^ inp.prec) :
    CloseTo (ProbComp.eval (sampleGridGaussian inp))
      ((PMF.piFin fun i : Fin inp.dim =>
          discreteGaussianInt ((inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ))
            (by positivity) ((inp.modulus : ℝ) * (inp.target.getD i.val 0 : ℝ))).map
        fun r => gridReduceInt inp.dim inp.modulus inp.basis (List.ofFn r))
      (ENNReal.ofReal ((inp.dim : ℝ) *
        ((1 - 1 / (16 * (2 * inp.tail + 6 : ℝ))) ^ inp.maxTrials
          + (8 * inp.tail + 24 : ℝ) / (2 : ℝ) ^ inp.prec
          + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2))))) :=
  closeTo_eval_sampleGridGaussian_pi inp hsSq hq hqs1 ht hε.le hε_le
    ((ZLattice.smoothingParameter_le_iff intLatticeReal (by positivity) hε).mp hη) hprec

/-- Every output pair in the support of `sampleGridGaussian inp` is the exact `gridReduceInt`
image of some length-`inp.dim` integer vector. -/
theorem mem_support_sampleGridGaussian (inp : GridSampleInput) {p : List ℤ × List ℤ}
    (hp : p ∈ (ProbComp.eval (sampleGridGaussian inp)).support) :
    ∃ r' : List ℤ, r'.length = inp.dim ∧
      p = gridReduceInt inp.dim inp.modulus inp.basis r' := by
  unfold sampleGridGaussian at hp
  rw [bind_pure_comp, ProbComp.eval_map, ProbComp.eval_mapM_range, PMF.map_comp] at hp
  obtain ⟨r, _, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  exact ⟨List.ofFn r, List.length_ofFn, hr.symm⟩

/-! ### 3. Strict-PPT HNF-free quotient sampler (`sampleQuotientModS`) -/

/-- Input specification for the HNF-free quotient sampler `sampleQuotientModS`. -/
structure QuotientSampleInput where
  /-- Ambient lattice dimension `n`. -/
  dim : ℕ
  /-- Basis matrix `B` of the outer lattice `L(B)`. -/
  basis : IntTable
  /-- Basis matrix `S` of the sublattice `L(S) ⊆ L(B)`. -/
  sublattice : IntTable
  /-- Extra random bits per coordinate above `Nat.clog 2 D`. -/
  extraBits : ℕ
  deriving DecidableEq, Repr

namespace QuotientSampleInput

/-- Framing encoding of `QuotientSampleInput`. -/
enc_structure enc : QuotientSampleInput where
  dim : encUnary, basis : IntTable.enc, sublattice : IntTable.enc, extraBits : encUnary

end QuotientSampleInput

open scoped QuotientSampleInput
attribute [local irreducible] QuotientSampleInput.enc

/-- Integer quotient index `D = |det S| / |det B|` computed via staged Bird determinants. -/
def quotientIndex (B S : IntTable) : ℕ :=
  (Cslib.Circuits.Rational.detRows S.rows).natAbs /
    (Cslib.Circuits.Rational.detRows B.rows).natAbs

@[local fun_prop]
private theorem computableInPolyTime_intTableRows :
    ComputableInPolyTime (Cslib.RowTable.rows : IntTable → _) IntTable.enc Cslib.encIntTable := by
  change ComputableInPolyTime (Cslib.RowTable.rows : IntTable → _) IntTable.enc
    (encList (encList encIntBin))
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_quotientIndex :
    ComputableInPolyTime (fun p : IntTable × IntTable => quotientIndex p.1 p.2)
      (encPair IntTable.enc IntTable.enc) encNat := by
  have := Cslib.Circuits.Rational.detRows_polytime
  fun_prop [quotientIndex]

/-- Exact integer quotient representative reduction: given `x ∈ ℕ^dim`, computes `v0 = B *ᵥ x` via
`ListMatrix.dotProduct`, `sk = solveFloorMul dim S v0`, and returns `v0 - sk`. -/
def quotientReduceInt (dim : ℕ) (B S : IntTable) (x : List ℕ) : List ℤ :=
  let v0 : List ℤ := (List.range B.numRows).map fun r =>
    ListMatrix.dotProduct B.numCols (B.rows.getD r []) (x.map (Nat.cast : ℕ → ℤ))
  let rhs : List ℚ := (List.range dim).map fun i => (v0.getD i 0 : ℚ)
  let sk : List ℤ := solveFloorMul dim S rhs
  (List.range dim).map fun i => v0.getD i 0 - sk.getD i 0

/-- HNF-free strict-PPT quotient sampler for `L(B) ∩ P(S)`. Returns `0` if `D = 0`. -/
noncomputable def sampleQuotientModS (inp : QuotientSampleInput) : ProbComp (List ℤ) :=
  let D := quotientIndex inp.basis inp.sublattice
  let width := if D = 0 then 0 else Nat.clog 2 D + inp.extraBits
  do
    let coords ← (List.range inp.dim).mapM fun _ => sampleModNat width D
    pure (if D = 0 then List.replicate inp.dim 0
      else quotientReduceInt inp.dim inp.basis inp.sublattice coords)

private theorem computableInPolyTime_quotientReduceInt :
    ComputableInPolyTime
      (fun p : QuotientSampleInput × List ℕ =>
        quotientReduceInt p.1.dim p.1.basis p.1.sublattice p.2)
      (encPair QuotientSampleInput.enc (encList encNat)) (encList encIntBin) := by
  let encIn := encPair QuotientSampleInput.enc (encList encNat)
  have hdim : ComputableInPolyTime (fun p : QuotientSampleInput × List ℕ => p.1.dim)
      encIn encUnary := by fun_prop
  have hB : ComputableInPolyTime (fun p : QuotientSampleInput × List ℕ => p.1.basis)
      encIn IntTable.enc := by fun_prop
  have hS : ComputableInPolyTime (fun p : QuotientSampleInput × List ℕ => p.1.sublattice)
      encIn IntTable.enc := by fun_prop
  have hxInt : ComputableInPolyTime
      (fun p : QuotientSampleInput × List ℕ => p.2.map (Nat.cast : ℕ → ℤ))
      encIn (encList encIntBin) := by fun_prop
  have hv0 := (hB.prod hxInt).trans computableInPolyTime_intTableMulVec
  have hrhs := computableInPolyTime_vecIntToRat hdim hv0
  have hsk := computableInPolyTime_solveFloorMul hdim hS hrhs
  exact computableInPolyTime_vecSub hdim hv0 hsk

/-- Strict-PPT certificate for `sampleQuotientModS`. -/
theorem isPPTOn_sampleQuotientModS :
    IsPPTOn QuotientSampleInput.enc (encList encIntBin) sampleQuotientModS := by
  have hcoord : IsPPTOn (encPair QuotientSampleInput.enc encUnary) encNat
      (fun p : QuotientSampleInput × ℕ =>
        sampleModNat
          (if quotientIndex p.1.basis p.1.sublattice = 0 then 0
            else Nat.clog 2 (quotientIndex p.1.basis p.1.sublattice) + p.1.extraBits)
          (quotientIndex p.1.basis p.1.sublattice)) :=
    isPPTOn_sampleModNat (by fun_prop) (by fun_prop)
  have htrav : IsPPTOn QuotientSampleInput.enc (encList encNat)
      (fun inp => (List.range inp.dim).mapM fun _ =>
        sampleModNat
          (if quotientIndex inp.basis inp.sublattice = 0 then 0
            else Nat.clog 2 (quotientIndex inp.basis inp.sublattice) + inp.extraBits)
          (quotientIndex inp.basis inp.sublattice)) :=
    IsPPTOn.mapMWith hcoord (by fun_prop)
  have hres := htrav.map_with
    (f := fun inp coords =>
      if quotientIndex inp.basis inp.sublattice = 0 then List.replicate inp.dim (0 : ℤ)
      else quotientReduceInt inp.dim inp.basis inp.sublattice coords)
    (ite_decide (by fun_prop) (by fun_prop) computableInPolyTime_quotientReduceInt)
  refine hres.congr fun inp => ?_
  simp only [sampleQuotientModS, bind_pure_comp]

/-- `CloseTo` bound for `sampleQuotientModS` against `PMF.piFin` of `uniformOfFintype (ZMod D)`
pushed forward by `quotientReduceInt`. -/
theorem closeTo_eval_sampleQuotientModS_pi (inp : QuotientSampleInput)
    (hDpos : 0 < quotientIndex inp.basis inp.sublattice) :
    let D := quotientIndex inp.basis inp.sublattice
    letI : NeZero D := ⟨hDpos.ne'⟩
    CloseTo (ProbComp.eval (sampleQuotientModS inp))
      ((PMF.piFin fun _ : Fin inp.dim => PMF.uniformOfFintype (ZMod D)).map
        fun z => quotientReduceInt inp.dim inp.basis inp.sublattice
          (List.ofFn fun i => (z i).val))
      ((inp.dim : ℝ≥0∞) / 2 ^ inp.extraBits) := by
  dsimp only
  set D := quotientIndex inp.basis inp.sublattice
  have : NeZero D := ⟨hDpos.ne'⟩
  have hDne : D ≠ 0 := hDpos.ne'
  set width := Nat.clog 2 D + inp.extraBits
  have hcoord : CloseTo
      ((ProbComp.eval (sampleModNat width D)).map (Nat.cast : ℕ → ZMod D))
      (PMF.uniformOfFintype (ZMod D))
      (1 / 2 ^ inp.extraBits) := by
    refine (closeTo_uniform_sampleModNat width D).symm.mono ?_
    have hDle : (D : ℝ≥0∞) ≤ 2 ^ Nat.clog 2 D := by
      exact_mod_cast Nat.le_pow_clog (by omega) D
    rw [show (2 : ℝ≥0∞) ^ width = 2 ^ Nat.clog 2 D * 2 ^ inp.extraBits by
      dsimp only [width]; rw [pow_add]]
    calc
      (D : ℝ≥0∞) / (2 ^ Nat.clog 2 D * 2 ^ inp.extraBits) ≤
          (2 ^ Nat.clog 2 D) / (2 ^ Nat.clog 2 D * 2 ^ inp.extraBits) :=
        ENNReal.div_le_div_right hDle _
      _ = 1 / 2 ^ inp.extraBits := by
        conv_lhs => arg 1; rw [← mul_one ((2 : ℝ≥0∞) ^ Nat.clog 2 D)]
        rw [ENNReal.mul_div_mul_left 1 (2 ^ inp.extraBits) (by positivity) (by simp)]
  have hpi : CloseTo
      (PMF.piFin fun _ : Fin inp.dim =>
        (ProbComp.eval (sampleModNat width D)).map (Nat.cast : ℕ → ZMod D))
      (PMF.piFin fun _ : Fin inp.dim => PMF.uniformOfFintype (ZMod D))
      ((inp.dim : ℝ≥0∞) / 2 ^ inp.extraBits) := by
    have h := CloseTo.piFin (fun _ : Fin inp.dim => hcoord)
    rwa [mul_one_div] at h
  have heval : ProbComp.eval (sampleQuotientModS inp) =
      (PMF.piFin fun _ : Fin inp.dim =>
        (ProbComp.eval (sampleModNat width D)).map (Nat.cast : ℕ → ZMod D)).map
        fun z => quotientReduceInt inp.dim inp.basis inp.sublattice
          (List.ofFn fun i => (z i).val) := by
    rw [PMF.piFin_map (p := fun _ : Fin inp.dim => ProbComp.eval (sampleModNat width D))
      (g := fun _ => (Nat.cast : ℕ → ZMod D)), PMF.map_comp]
    have hprog : sampleQuotientModS inp =
        (do
          let coords ← (List.range inp.dim).mapM fun _ => sampleModNat width D
          pure (quotientReduceInt inp.dim inp.basis inp.sublattice coords)) := by
      unfold sampleQuotientModS
      dsimp only
      change (do
        let coords ← (List.range inp.dim).mapM fun _ =>
          sampleModNat (if D = 0 then 0 else Nat.clog 2 D + inp.extraBits) D
        pure (if D = 0 then List.replicate inp.dim 0
          else quotientReduceInt inp.dim inp.basis inp.sublattice coords)) = _
      simp only [hDne, ↓reduceIte]
      rfl
    rw [hprog, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_mapM_range, PMF.map_comp]
    apply PMF.map_congr_on_support
    intro r hr
    simp only [Function.comp_apply]
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_ofFn]
    have hri : r ⟨i, by simpa using hi⟩ ∈ (ProbComp.eval (sampleModNat width D)).support :=
      (PMF.mem_support_piFin_iff _ _).mp hr ⟨i, by simpa using hi⟩
    have hlt : r ⟨i, by simpa using hi⟩ < D := by
      unfold sampleModNat at hri
      rw [ProbComp.eval_map] at hri
      obtain ⟨n, _, hn⟩ := (PMF.mem_support_map_iff _ _ _).mp hri
      rw [← hn]
      exact Nat.mod_lt n hDpos
    exact (ZMod.val_natCast_of_lt hlt).symm
  rw [heval]
  exact hpi.map _

/-- Every vector in the support of `sampleQuotientModS inp` is either the zero fallback (when
`quotientIndex = 0`) or the exact `quotientReduceInt` image of some length-`inp.dim` list. -/
theorem mem_support_sampleQuotientModS (inp : QuotientSampleInput) {v : List ℤ}
    (hv : v ∈ (ProbComp.eval (sampleQuotientModS inp)).support) :
    v = List.replicate inp.dim 0 ∨
      ∃ x : List ℕ, x.length = inp.dim ∧
        v = quotientReduceInt inp.dim inp.basis inp.sublattice x := by
  unfold sampleQuotientModS at hv
  dsimp only at hv
  rw [bind_pure_comp, ProbComp.eval_map, ProbComp.eval_mapM_range, PMF.map_comp] at hv
  obtain ⟨r, _, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
  by_cases hD : quotientIndex inp.basis inp.sublattice = 0
  · left; simpa [hD] using hr.symm
  · right; exact ⟨List.ofFn r, List.length_ofFn, by simpa [hD] using hr.symm⟩

/-! ### 4. Exact `IntTable.toMatrix` / `WellFormed` specifications -/

private theorem intTableToRatTable_entry (T : IntTable) (i j : ℕ) :
    (intTableToRatTable T).entry i j = (T.entry i j : ℚ) := by
  unfold intTableToRatTable Cslib.RowTable.entry
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hrow : T.rows[i]? with
  | none => simp
  | some row =>
    simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    cases hcol : row[j]? with
    | none => simp
    | some v => simp

private theorem intTableMulVec_getD {n : ℕ} (T : IntTable) (B : Matrix (Fin n) (Fin n) ℤ)
    (hrows : T.numRows = n) (hcols : T.numCols = n)
    (hmat : ∀ (i j : Fin n), T.entry i.val j.val = B i j)
    (v : List ℤ) (i : Fin n) :
    (((List.range T.numRows).map fun r =>
      ListMatrix.dotProduct T.numCols (T.rows.getD r []) v)).getD i.val 0 =
      (B *ᵥ fun j : Fin n => v.getD j.val 0) i := by
  have hi : i.val < ((List.range T.numRows).map fun r =>
      ListMatrix.dotProduct T.numCols (T.rows.getD r []) v).length := by
    simp only [List.length_map, List.length_range, hrows]
    exact i.isLt
  rw [List.getD_eq_getElem _ _ hi, List.getElem_map, List.getElem_range, hcols,
    ListMatrix.dotProduct_eq]
  simp only [Matrix.mulVec, dotProduct, ofList_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hentry : (T.rows.getD i.val []).getD j.val 0 = B i j := hmat i j
  rw [hentry]

/-- Exact matrix specification of `solveFloorMul`: for any square invertible `IntTable` `T`
representing `B : Matrix (Fin n) (Fin n) ℤ`, `solveFloorMul n T rhs` equals
`B *ᵥ ⌊(B_ℝ)⁻¹ *ᵥ rhs⌋` coordinatewise. -/
theorem solveFloorMul_spec {n : ℕ} (T : IntTable) (B : Matrix (Fin n) (Fin n) ℤ)
    (hrows : T.numRows = n) (hcols : T.numCols = n)
    (hmat : ∀ (i j : Fin n), T.entry i.val j.val = B i j)
    (hB : B.det ≠ 0) (rhs : List ℚ) (i : Fin n) :
    (solveFloorMul n T rhs).getD i.val 0 =
      (B *ᵥ fun j : Fin n =>
        Int.floor (((B.map Int.cast : Matrix (Fin n) (Fin n) ℝ)⁻¹ *ᵥ
          fun k : Fin n => (rhs.getD k.val 0 : ℝ)) j)) i := by
  cases T with
  | mk nr nc rows =>
    dsimp only at hrows hcols
    cases hrows
    cases hcols
    let T : IntTable := ⟨n, n, rows⟩
    let M : RatTable := intTableToRatTable T
    let sys : LinearSystemInput := ⟨M, rhs⟩
    let BQ : Matrix (Fin n) (Fin n) ℚ := B.map Int.cast
    let BR : Matrix (Fin n) (Fin n) ℝ := B.map Int.cast
    have hM_eq : M.toMatrix = BQ := by
      ext r j
      rw [Cslib.RowTable.toMatrix_apply, intTableToRatTable_entry]
      exact congrArg (Int.cast : ℤ → ℚ) (hmat r j)
    have hBQ_det : BQ.det ≠ 0 := by
      have hdet : BQ.det = (B.det : ℚ) := by
        simpa [BQ] using ((Int.castRingHom ℚ).map_det B).symm
      rw [hdet]
      exact Int.cast_ne_zero.mpr hB
    have hBQ_inv : BQ * BQ⁻¹ = 1 := Matrix.mul_nonsing_inv BQ (isUnit_iff_ne_zero.mpr hBQ_det)
    have hBR_inv : BR⁻¹ * BR = 1 := matR_inv_mul hB
    let bQ : Fin n → ℚ := fun k => rhs.getD k.val 0
    let ξQ : Fin n → ℚ := BQ⁻¹ *ᵥ bQ
    have hcons : ∃ x : Fin M.numCols → ℚ,
        M.toMatrix *ᵥ x = fun r : Fin M.numRows => rhs.getD r.val 0 := by
      refine ⟨ξQ, ?_⟩
      have h1 : BQ *ᵥ ξQ = bQ := by
        dsimp only [ξQ]
        rw [Matrix.mulVec_mulVec, hBQ_inv, Matrix.one_mulVec]
      change M.toMatrix *ᵥ ξQ = bQ
      rw [hM_eq]
      exact h1
    have hspec := ratSolve_spec sys
    have hne_none : (ratSolve sys).solution ≠ none := by
      intro hnone
      exact (hspec.2.mp hnone) hcons
    obtain ⟨sol, hsol⟩ := Option.ne_none_iff_exists'.mp hne_none
    have ⟨_, hsol_eq⟩ := hspec.1 sol hsol
    have hsol_real : ∀ j : Fin n,
        (sol.getD j.val 0 : ℝ) = (BR⁻¹ *ᵥ fun k : Fin n => (rhs.getD k.val 0 : ℝ)) j := by
      have hmul_eq : BR *ᵥ (fun j : Fin n => (sol.getD j.val 0 : ℝ)) =
          fun k : Fin n => (rhs.getD k.val 0 : ℝ) := by
        ext k
        have hk_q := congrFun hsol_eq k
        change (M.toMatrix *ᵥ fun j : Fin n => sol.getD j.val 0) k = rhs.getD k.val 0 at hk_q
        rw [hM_eq] at hk_q
        have hcast := congrArg (Rat.cast : ℚ → ℝ) hk_q
        simp only [BQ, BR, Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum,
          Rat.cast_mul] at hcast ⊢
        exact hcast
      intro j
      have h1 := congrFun (congrArg (BR⁻¹ *ᵥ ·) hmul_eq) j
      rwa [Matrix.mulVec_mulVec, hBR_inv, Matrix.one_mulVec] at h1
    unfold solveFloorMul
    dsimp only
    change (((List.range T.numRows).map fun r =>
      ListMatrix.dotProduct T.numCols (T.rows.getD r [])
        ((List.range n).map fun j =>
          (((ratSolve sys).solution.getD (List.replicate n 0)).getD j 0).floor))).getD i.val 0 = _
    rw [hsol, Option.getD_some]
    rw [intTableMulVec_getD T B rfl rfl hmat _ i]
    congr 1
    funext j
    have hj : j.val < ((List.range n).map fun k => (sol.getD k 0).floor).length := by
      simp [j.isLt]
    rw [List.getD_eq_getElem _ _ hj, List.getElem_map, List.getElem_range]
    have hfl : (sol.getD j.val 0).floor = Int.floor (sol.getD j.val 0 : ℝ) := by
      rw [show (sol.getD j.val 0).floor = Int.floor (sol.getD j.val 0) from rfl,
        ← Rat.floor_cast (α := ℝ)]
    rw [hfl, hsol_real j]

/-- Exact determinant-index specification of `quotientIndex`: for well-formed square `IntTable`s
representing `B, S : Matrix (Fin n) (Fin n) ℤ` with `B.det ≠ 0` and `intLattice S ≤ intLattice B`,
`quotientIndex TB TS = (S.det / B.det).natAbs`. -/
theorem quotientIndex_eq_natAbs_div_det {n : ℕ} (TB TS : IntTable)
    (B S : Matrix (Fin n) (Fin n) ℤ)
    (hBwf : TB.WellFormed) (hSwf : TS.WellFormed)
    (hBrows : TB.numRows = n) (hBmat : ∀ (i j : Fin n), TB.entry i.val j.val = B i j)
    (hSrows : TS.numRows = n) (hSmat : ∀ (i j : Fin n), TS.entry i.val j.val = S i j)
    (hB : B.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    quotientIndex TB TS = (S.det / B.det).natAbs := by
  have hdetB : Cslib.Circuits.Rational.detRows TB.rows = B.det :=
    Cslib.Circuits.Rational.detRows_eq_det_of_rowEntry B (hBwf.1.trans hBrows) hBmat
  have hdetS : Cslib.Circuits.Rational.detRows TS.rows = S.det :=
    Cslib.Circuits.Rational.detRows_eq_det_of_rowEntry S (hSwf.1.trans hSrows) hSmat
  have hdet_mul : S.det = B.det * (sublatticeMat B S hSB).det := by
    rw [← Matrix.det_mul, mul_sublatticeMat]
  unfold quotientIndex
  rw [hdetB, hdetS, hdet_mul, Int.natAbs_mul,
    Nat.mul_div_cancel_left _ (Int.natAbs_pos.mpr hB),
    Int.mul_ediv_cancel_left _ hB]

/-- Exact geometric specification of `gridReduceInt` against `modParallelepiped` and
`intLattice`: for invertible `B` and `0 < q`, `(u, y)` from `gridReduceInt n q T r'` satisfies
`u / q = (-r' / q) mod P(B)` and `y = r' / q + u / q ∈ intLattice B`. -/
theorem gridReduceInt_spec {n q : ℕ} (T : IntTable) (B : Matrix (Fin n) (Fin n) ℤ)
    (hrows : T.numRows = n) (hcols : T.numCols = n)
    (hmat : ∀ (i j : Fin n), T.entry i.val j.val = B i j)
    (hB : B.det ≠ 0) (hq : 0 < q) (r' : List ℤ) :
    let p := gridReduceInt n q T r'
    let rVec : EuclideanSpace ℝ (Fin n) :=
      ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i : Fin n => (r'.getD i.val 0 : ℝ))
    let uVec : EuclideanSpace ℝ (Fin n) :=
      ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i : Fin n => (p.1.getD i.val 0 : ℝ))
    let yVec : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i : Fin n => (p.2.getD i.val 0 : ℝ))
    p.1.length = n ∧ p.2.length = n ∧
      uVec = modParallelepiped B (-rVec) ∧
      yVec = rVec + uVec ∧
      yVec ∈ intLattice B := by
  intro p rVec uVec yVec
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  let rhs : List ℚ := (List.range n).map fun i => Rat.divInt (-(r'.getD i 0)) (q : ℤ)
  have hrhs_real : ∀ k : Fin n, (rhs.getD k.val 0 : ℝ) = (-rVec) k := by
    intro k
    have hk : k.val < rhs.length := by simp [rhs, k.isLt]
    rw [List.getD_eq_getElem _ _ hk]
    dsimp only [rhs]
    rw [List.getElem_map, List.getElem_range]
    have hdiv : (Rat.divInt (-(r'.getD k.val 0)) (q : ℤ) : ℝ) =
        (-(r'.getD k.val 0 : ℝ)) / (q : ℝ) := by
      rw [Rat.divInt_eq_div]
      push_cast
      rfl
    rw [hdiv]
    change -(r'.getD k.val 0 : ℝ) / (q : ℝ) = -((q : ℝ)⁻¹ * (r'.getD k.val 0 : ℝ))
    ring
  have hbk := fun i : Fin n => solveFloorMul_spec T B hrows hcols hmat hB rhs i
  have hp1_len : p.1.length = n := by simp [p, gridReduceInt]
  have hp2_len : p.2.length = n := by simp [p, gridReduceInt]
  have hu_coord : ∀ i : Fin n, p.1.getD i.val 0 =
      -(r'.getD i.val 0) - (q : ℤ) * (solveFloorMul n T rhs).getD i.val 0 := by
    intro i
    have hi : i.val < p.1.length := by rw [hp1_len]; exact i.isLt
    rw [List.getD_eq_getElem _ _ hi]
    simp [p, gridReduceInt, rhs]
  have hy_coord : ∀ i : Fin n, p.2.getD i.val 0 = -((solveFloorMul n T rhs).getD i.val 0) := by
    intro i
    have hi : i.val < p.2.length := by rw [hp2_len]; exact i.isLt
    rw [List.getD_eq_getElem _ _ hi]
    simp [p, gridReduceInt, rhs]
  let BR : Matrix (Fin n) (Fin n) ℝ := B.map Int.cast
  have hBR_mul : BR * BR⁻¹ = 1 := matR_mul_inv hB
  have hu_eq : uVec = modParallelepiped B (-rVec) := by
    ext i
    have hbi := hbk i
    have hrhs_fun : (fun k : Fin n => (rhs.getD k.val 0 : ℝ)) = WithLp.ofLp (-rVec) :=
      funext hrhs_real
    have hbk_real : ((solveFloorMul n T rhs).getD i.val 0 : ℝ) =
        (BR *ᵥ fun j : Fin n =>
          (Int.floor ((BR⁻¹ *ᵥ WithLp.ofLp (-rVec)) j) : ℝ)) i := by
      rw [hbi, hrhs_fun]
      simp [BR, Matrix.mulVec, dotProduct]
    have hneg_r : (-rVec) i = (BR *ᵥ (BR⁻¹ *ᵥ WithLp.ofLp (-rVec))) i := by
      rw [Matrix.mulVec_mulVec, hBR_mul, Matrix.one_mulVec]
    change (q : ℝ)⁻¹ * (p.1.getD i.val 0 : ℝ) =
      (BR *ᵥ fun j => (BR⁻¹ *ᵥ WithLp.ofLp (-rVec)) j -
        (Int.floor ((BR⁻¹ *ᵥ WithLp.ofLp (-rVec)) j) : ℝ)) i
    rw [hu_coord i]
    push_cast
    rw [hbk_real]
    have hsub : (BR *ᵥ fun j => (BR⁻¹ *ᵥ WithLp.ofLp (-rVec)) j -
        (Int.floor ((BR⁻¹ *ᵥ WithLp.ofLp (-rVec)) j) : ℝ)) i =
        (-rVec) i - (BR *ᵥ fun j => (Int.floor ((BR⁻¹ *ᵥ WithLp.ofLp (-rVec)) j) : ℝ)) i := by
      change (BR *ᵥ ((BR⁻¹ *ᵥ WithLp.ofLp (-rVec)) -
        fun j => (Int.floor ((BR⁻¹ *ᵥ WithLp.ofLp (-rVec)) j) : ℝ))) i = _
      rw [Matrix.mulVec_sub, Pi.sub_apply, ← hneg_r]
    rw [hsub]
    change (q : ℝ)⁻¹ * (-(r'.getD i.val 0 : ℝ) - (q : ℝ) * _) =
      -((q : ℝ)⁻¹ * (r'.getD i.val 0 : ℝ)) - _
    field_simp [hq0]
  have hy_eq : yVec = rVec + uVec := by
    ext i
    change (p.2.getD i.val 0 : ℝ) =
      (q : ℝ)⁻¹ * (r'.getD i.val 0 : ℝ) + (q : ℝ)⁻¹ * (p.1.getD i.val 0 : ℝ)
    rw [hy_coord i, hu_coord i]
    push_cast
    field_simp [hq0]
    ring
  have hy_mem : yVec ∈ intLattice B := by
    rw [mem_intLattice_iff]
    refine ⟨fun j => -(Int.floor ((BR⁻¹ *ᵥ fun k : Fin n => (rhs.getD k.val 0 : ℝ)) j)), ?_⟩
    ext i
    change (p.2.getD i.val 0 : ℝ) = _
    rw [hy_coord i, hbk i]
    simp [BR, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
  exact ⟨hp1_len, hp2_len, hu_eq, hy_eq, hy_mem⟩

/-- Exact geometric specification of `quotientReduceInt` against `MR07Core.modParallelepiped`:
for `B = TB.toMatrix` and invertible `S = TS.toMatrix`, `v = quotientReduceInt n TB TS x`
has length `n` and equals `modParallelepiped S (B *ᵥ x)`. -/
theorem quotientReduceInt_spec {n : ℕ} (TB TS : IntTable) (B S : Matrix (Fin n) (Fin n) ℤ)
    (hBrows : TB.numRows = n) (hBcols : TB.numCols = n)
    (hBmat : ∀ (i j : Fin n), TB.entry i.val j.val = B i j)
    (hSrows : TS.numRows = n) (hScols : TS.numCols = n)
    (hSmat : ∀ (i j : Fin n), TS.entry i.val j.val = S i j)
    (hS : S.det ≠ 0) (x : List ℕ) :
    let v := quotientReduceInt n TB TS x
    v.length = n ∧
      WithLp.toLp 2 (fun i : Fin n => (v.getD i.val 0 : ℝ)) =
        modParallelepiped S
          (WithLp.toLp 2 (fun i : Fin n =>
            ((B *ᵥ fun j : Fin n => (x.getD j.val 0 : ℤ)) i : ℝ))) := by
  intro v
  have hv_len : v.length = n := by simp [v, quotientReduceInt]
  let v0 : List ℤ := (List.range TB.numRows).map fun r =>
    ListMatrix.dotProduct TB.numCols (TB.rows.getD r []) (x.map (Nat.cast : ℕ → ℤ))
  have hv0_coord : ∀ i : Fin n,
      v0.getD i.val 0 = (B *ᵥ fun j : Fin n => (x.getD j.val 0 : ℤ)) i := by
    intro i
    rw [intTableMulVec_getD TB B hBrows hBcols hBmat _ i]
    congr 1
    funext j
    by_cases hj : j.val < x.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_none (Nat.not_lt.mp hj), Option.map_none, Option.getD_none, Nat.cast_zero]
  let rhs : List ℚ := (List.range n).map fun i => (v0.getD i 0 : ℚ)
  let xVec : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i : Fin n => ((B *ᵥ fun j : Fin n => (x.getD j.val 0 : ℤ)) i : ℝ))
  have hrhs_real : ∀ k : Fin n, (rhs.getD k.val 0 : ℝ) = xVec k := by
    intro k
    have hk : k.val < rhs.length := by simp [rhs, k.isLt]
    rw [List.getD_eq_getElem _ _ hk]
    dsimp only [rhs, xVec]
    rw [List.getElem_map, List.getElem_range]
    simpa only [Rat.cast_intCast] using congrArg (Int.cast : ℤ → ℝ) (hv0_coord k)
  let SR : Matrix (Fin n) (Fin n) ℝ := S.map Int.cast
  have hSR_mul : SR * SR⁻¹ = 1 := matR_mul_inv hS
  refine ⟨hv_len, ?_⟩
  ext i
  have hi : i.val < v.length := by rw [hv_len]; exact i.isLt
  have hv_i : v.getD i.val 0 = v0.getD i.val 0 - (solveFloorMul n TS rhs).getD i.val 0 := by
    rw [List.getD_eq_getElem _ _ hi]
    simp [v, quotientReduceInt, v0, rhs]
  have hsk := solveFloorMul_spec TS S hSrows hScols hSmat hS rhs i
  have hrhs_fun : (fun k : Fin n => (rhs.getD k.val 0 : ℝ)) = WithLp.ofLp xVec :=
    funext hrhs_real
  have hsk_real : ((solveFloorMul n TS rhs).getD i.val 0 : ℝ) =
      (SR *ᵥ fun j : Fin n => (Int.floor ((SR⁻¹ *ᵥ WithLp.ofLp xVec) j) : ℝ)) i := by
    rw [hsk, hrhs_fun]
    simp [SR, Matrix.mulVec, dotProduct]
  have hx_eq : xVec i = (SR *ᵥ (SR⁻¹ *ᵥ WithLp.ofLp xVec)) i := by
    rw [Matrix.mulVec_mulVec, hSR_mul, Matrix.one_mulVec]
  change (v.getD i.val 0 : ℝ) =
    (SR *ᵥ ((SR⁻¹ *ᵥ WithLp.ofLp xVec) -
      fun j => (Int.floor ((SR⁻¹ *ᵥ WithLp.ofLp xVec) j) : ℝ))) i
  rw [hv_i, Int.cast_sub, hv0_coord i, hsk_real, Matrix.mulVec_sub, Pi.sub_apply, ← hx_eq]

/-! ### 5. Typed-law bridges to `MR07Core.idealGridSample` and `SublatticeQuot` -/

private theorem getD_ofFn_eq {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (i : Fin n) :
    (List.ofFn f).getD i.val d = f i := by
  have hi : i.val < (List.ofFn f).length := by simp [i.isLt]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getElem_ofFn]

private theorem list_ofFn_getD_eq {α : Type*} {n : ℕ} {l : List α} (hl : l.length = n) (d : α) :
    List.ofFn (fun i : Fin n => l.getD i.val d) = l := by
  apply List.ext_getElem (by simp [hl])
  intro i hi _
  have hi' : i < l.length := by simpa [hl] using hi
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
    Option.getD_some]

/-! #### 5.1 Discrete-grid Gaussian sampler ↔ `MR07.idealGridSample` -/

/-- Bijection identifying `Fin n → ℤ` with the fine grid lattice `G_q = (1 / q) ℤⁿ`. -/
noncomputable def gridEmbed (n q : ℕ) (hq : 0 < q) : (Fin n → ℤ) ≃ gridLattice n q :=
  Equiv.ofBijective
    (fun r' => ⟨((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (r' i : ℝ)),
      (mem_gridLattice_iff _).2 ⟨r', rfl⟩⟩)
    ⟨by
      intro a b hab
      have hqR : ((q : ℝ)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hq.ne')
      have hvec : WithLp.toLp 2 (fun i => (a i : ℝ)) = WithLp.toLp 2 (fun i => (b i : ℝ)) :=
        smul_right_injective _ hqR (congrArg Subtype.val hab)
      funext i
      exact Int.cast_injective (congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hvec),
     by
      intro x
      obtain ⟨r', hr'⟩ := (mem_gridLattice_iff x.1).1 x.2
      exact ⟨r', Subtype.ext hr'.symm⟩⟩

/-- Canonical injective encoding of a typed `GridRep B q × intLattice B` sample into
`List ℤ × List ℤ`. -/
noncomputable def gridPairToLists {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {q : ℕ} :
    GridRep B q × intLattice B → List ℤ × List ℤ
  | (g, y) => (List.ofFn g.1, List.ofFn fun i => Int.floor ((y : EuclideanSpace ℝ (Fin n)) i))

/-- `gridPairToLists` is injective on `GridRep B q × intLattice B`. -/
theorem gridPairToLists_injective {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {q : ℕ} :
    Function.Injective (gridPairToLists (B := B) (q := q)) := by
  intro ⟨c₁, y₁⟩ ⟨c₂, y₂⟩ h
  simp only [gridPairToLists, Prod.mk.injEq] at h
  have hc : c₁ = c₂ := by
    apply Subtype.ext; funext i
    have hi := congrArg (fun l : List ℤ => l.getD i.val 0) h.1
    simpa [getD_ofFn_eq] using hi
  have hy : y₁ = y₂ := by
    obtain ⟨m₁, hm₁⟩ := (mem_intLattice_iff B y₁.1).1 y₁.2
    obtain ⟨m₂, hm₂⟩ := (mem_intLattice_iff B y₂.1).1 y₂.2
    apply Subtype.ext; ext i
    have hi := congrArg (fun l : List ℤ => l.getD i.val 0) h.2
    have hfl : Int.floor (y₁.1 i) = Int.floor (y₂.1 i) := by
      simpa [getD_ofFn_eq] using hi
    have h1 : y₁.1 i = ((B *ᵥ m₁) i : ℝ) := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hm₁
    have h2 : y₂.1 i = ((B *ᵥ m₂) i : ℝ) := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hm₂
    rw [h1, h2, Int.floor_intCast, Int.floor_intCast] at hfl
    rw [h1, h2, hfl]
  exact Prod.ext hc hy

/-- Left-inverse decoder from `List ℤ × List ℤ` to `GridRep B q × intLattice B`. -/
noncomputable def decodeGridPair {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) :
    List ℤ × List ℤ → GridRep B q × intLattice B :=
  Function.invFun (gridPairToLists (B := B) (q := q))

/-- `decodeGridPair` is a left inverse to `gridPairToLists`. -/
theorem decodeGridPair_gridPairToLists {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {q : ℕ}
    (p : GridRep B q × intLattice B) :
    decodeGridPair B q (gridPairToLists p) = p :=
  Function.leftInverse_invFun gridPairToLists_injective p

/-- Exact product factorization: `PMF.piFin` of 1-D integer discrete Gaussians at `(q · s, q · t_i)`
pushed through `gridEmbed` equals `ZLattice.discreteGaussian (gridLattice n q) s hs t`. -/
theorem piFin_discreteGaussianInt_map_gridEmbed {n q : ℕ} (hq : 0 < q)
    (s : ℝ) (hs : 0 < s) (t : EuclideanSpace ℝ (Fin n)) :
    let hqs : 0 < (q : ℝ) * s := mul_pos (Nat.cast_pos.mpr hq) hs
    (PMF.piFin fun i : Fin n => discreteGaussianInt ((q : ℝ) * s) hqs ((q : ℝ) * t i)).map
        (gridEmbed n q hq) =
      ZLattice.discreteGaussian (gridLattice n q) s hs t := by
  classical
  intro hqs
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hweight : ∀ r' : Fin n → ℤ,
      ∏ i : Fin n, ProbabilityTheory.gaussianWeight ((q : ℝ) * s) ((r' i : ℝ) - (q : ℝ) * t i) =
        ProbabilityTheory.gaussianWeight s ((gridEmbed n q hq r').1 - t) := by
    intro r'
    simp only [ProbabilityTheory.gaussianWeight, ← Real.exp_sum]
    congr 1
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoord : ((gridEmbed n q hq r').1 - t) i =
        ((r' i : ℝ) - (q : ℝ) * t i) / (q : ℝ) := by
      change (q : ℝ)⁻¹ * (r' i : ℝ) - t i = _
      field_simp [hqR.ne']
    rw [hcoord, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    field_simp [hqR.ne', hs.ne']
  let Zprod : ℝ := ∏ i : Fin n, ZLattice.gaussianMass intLatticeReal ((q : ℝ) * s) ((q : ℝ) * t i)
  let Zgrid : ℝ := ZLattice.gaussianMass (gridLattice n q) s t
  have hZprod_pos : 0 < Zprod :=
    Finset.prod_pos fun i _ => ZLattice.gaussianMass_pos intLatticeReal _ hqs _
  have hZgrid_pos : 0 < Zgrid := ZLattice.gaussianMass_pos (gridLattice n q) s hs t
  have hLHS_apply : ∀ x : gridLattice n q,
      ((PMF.piFin fun i : Fin n => discreteGaussianInt ((q : ℝ) * s) hqs ((q : ℝ) * t i)).map
          (gridEmbed n q hq)) x =
        ENNReal.ofReal (ProbabilityTheory.gaussianWeight s (x.1 - t)) / ENNReal.ofReal Zprod := by
    intro x
    set r' := (gridEmbed n q hq).symm x
    rw [PMF.map_apply, tsum_eq_single r']
    · have hxr : x = gridEmbed n q hq r' := ((gridEmbed n q hq).apply_symm_apply x).symm
      simp only [hxr, ↓reduceIte, PMF.piFin_apply]
      simp_rw [discreteGaussianInt_apply]
      have hdiv : ∀ i : Fin n,
          ENNReal.ofReal (ProbabilityTheory.gaussianWeight ((q : ℝ) * s)
              ((r' i : ℝ) - (q : ℝ) * t i)) /
            ENNReal.ofReal (ZLattice.gaussianMass intLatticeReal ((q : ℝ) * s) ((q : ℝ) * t i)) =
          ENNReal.ofReal (ProbabilityTheory.gaussianWeight ((q : ℝ) * s)
              ((r' i : ℝ) - (q : ℝ) * t i) /
            ZLattice.gaussianMass intLatticeReal ((q : ℝ) * s) ((q : ℝ) * t i)) :=
        fun i => (ENNReal.ofReal_div_of_pos (ZLattice.gaussianMass_pos _ _ hqs _)).symm
      simp_rw [hdiv]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ =>
        div_nonneg (ProbabilityTheory.gaussianWeight_pos _ _).le
          (ZLattice.gaussianMass_pos _ _ hqs _).le),
        Finset.prod_div_distrib, hweight r', ENNReal.ofReal_div_of_pos hZprod_pos]
    · intro r'' hr''
      have hne : x ≠ gridEmbed n q hq r'' := fun heq =>
        hr'' ((gridEmbed n q hq).symm_apply_eq.mpr heq).symm
      simp [hne]
  have hZ_eq : ENNReal.ofReal Zprod = ENNReal.ofReal Zgrid := by
    have hsum1 : ∑' x : gridLattice n q,
        ENNReal.ofReal (ProbabilityTheory.gaussianWeight s (x.1 - t)) /
          ENNReal.ofReal Zprod = 1 := by
      simp_rw [← hLHS_apply]; exact PMF.tsum_coe _
    have hsum2 : ∑' x : gridLattice n q,
        ENNReal.ofReal (ProbabilityTheory.gaussianWeight s (x.1 - t)) /
          ENNReal.ofReal Zgrid = 1 := by
      have : ∀ x : gridLattice n q,
          ZLattice.discreteGaussian (gridLattice n q) s hs t x =
            ENNReal.ofReal (ProbabilityTheory.gaussianWeight s (x.1 - t)) /
              ENNReal.ofReal Zgrid :=
        fun x => ZLattice.discreteGaussian_apply _ s hs t x
      simp_rw [← this]; exact PMF.tsum_coe _
    simp_rw [div_eq_mul_inv] at hsum1 hsum2
    rw [ENNReal.tsum_mul_right] at hsum1 hsum2
    have hcancel : ∀ {Z : ℝ}, 0 < Z →
        (∑' x : gridLattice n q, ENNReal.ofReal (ProbabilityTheory.gaussianWeight s (x.1 - t))) *
          (ENNReal.ofReal Z)⁻¹ = 1 →
        ∑' x : gridLattice n q, ENNReal.ofReal (ProbabilityTheory.gaussianWeight s (x.1 - t)) =
          ENNReal.ofReal Z := fun {Z} hZ h => by
      have h' := congrArg (· * ENNReal.ofReal Z) h
      rwa [mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hZ).ne'
        ENNReal.ofReal_ne_top, mul_one, one_mul] at h'
    exact (hcancel hZprod_pos hsum1).symm.trans (hcancel hZgrid_pos hsum2)
  ext x
  rw [hLHS_apply x, hZ_eq, ZLattice.discreteGaussian_apply]

/-- Build the typed `GridRep B q × intLattice B` witness from `gridReduceInt_spec` on any
`r' : List ℤ` (zero decoding loss). -/
theorem gridReduceInt_exists_gridRep {n q : ℕ} (T : IntTable) (B : Matrix (Fin n) (Fin n) ℤ)
    (hrows : T.numRows = n) (hcols : T.numCols = n)
    (hmat : ∀ (i j : Fin n), T.entry i.val j.val = B i j)
    (hB : B.det ≠ 0) (hq : 0 < q) (r' : List ℤ) :
    let rVec : EuclideanSpace ℝ (Fin n) :=
      ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i : Fin n => (r'.getD i.val 0 : ℝ))
    ∃ gy : GridRep B q × intLattice B,
      gridReduceInt n q T r' = gridPairToLists gy ∧
        gy.1.toVec = modParallelepiped B (-rVec) ∧
        (gy.2 : EuclideanSpace ℝ (Fin n)) = rVec + gy.1.toVec := by
  intro rVec
  obtain ⟨hp1_len, hp2_len, hu_eq, hy_eq, hy_mem⟩ :=
    gridReduceInt_spec T B hrows hcols hmat hB hq r'
  set p := gridReduceInt n q T r'
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  let u : Fin n → ℤ := fun i => p.1.getD i.val 0
  have hu_bound : ∀ i : Fin n, |u i| ≤ (q : ℤ) * ∑ j : Fin n, |B i j| := by
    intro i
    have h1 := modParallelepiped_abs_le B (-rVec) i
    have h2 : modParallelepiped B (-rVec) i = (q : ℝ)⁻¹ * (u i : ℝ) := by
      rw [← hu_eq]; rfl
    rw [h2, abs_mul, abs_inv, abs_of_pos hqR, inv_mul_le_iff₀ hqR] at h1
    exact_mod_cast (by simpa [Int.cast_abs, Int.cast_sum, Int.cast_mul] using h1 :
      (|u i| : ℝ) ≤ ((q : ℤ) * ∑ j : Fin n, |B i j| : ℤ))
  have hu_idemp : modParallelepiped B (((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ))) =
      ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2 (fun i => (u i : ℝ)) := by
    rw [hu_eq]; exact modParallelepiped_idemp hB (-rVec)
  let g : GridRep B q := ⟨u, hu_bound, hu_idemp⟩
  let y : intLattice B := ⟨WithLp.toLp 2 (fun i : Fin n => (p.2.getD i.val 0 : ℝ)), hy_mem⟩
  refine ⟨(g, y), ?_, hu_eq, hy_eq⟩
  refine Prod.ext (list_ofFn_getD_eq hp1_len 0).symm ?_
  have hy_list : List.ofFn (fun i : Fin n => Int.floor ((y : EuclideanSpace ℝ (Fin n)) i)) =
      List.ofFn (fun i : Fin n => p.2.getD i.val 0) := by
    congr 1; funext i; exact Int.floor_intCast (p.2.getD i.val 0)
  exact (hy_list.trans (list_ofFn_getD_eq hp2_len 0)).symm

/-- Every output pair in the support of `sampleGridGaussian inp` encodes a valid
`GridRep B inp.modulus × intLattice B` recovered losslessly by `decodeGridPair`. -/
theorem mem_support_sampleGridGaussian_exists_gridRep (inp : GridSampleInput)
    (B : Matrix (Fin inp.dim) (Fin inp.dim) ℤ)
    (hrows : inp.basis.numRows = inp.dim) (hcols : inp.basis.numCols = inp.dim)
    (hmat : ∀ (i j : Fin inp.dim), inp.basis.entry i.val j.val = B i j)
    (hB : B.det ≠ 0) (hq : 0 < inp.modulus) {p : List ℤ × List ℤ}
    (hp : p ∈ (ProbComp.eval (sampleGridGaussian inp)).support) :
    ∃ gy : GridRep B inp.modulus × intLattice B,
      p = gridPairToLists gy ∧ decodeGridPair B inp.modulus p = gy := by
  obtain ⟨r', _, rfl⟩ := mem_support_sampleGridGaussian inp hp
  obtain ⟨gy, hlist, _, _⟩ :=
    gridReduceInt_exists_gridRep inp.basis B hrows hcols hmat hB hq r'
  exact ⟨gy, hlist, hlist ▸ decodeGridPair_gridPairToLists gy⟩

/-- Exact target-law equality connecting `sampleGridGaussian`'s product-pushforward `PMF` to
`MR07Core.idealGridSample` pushed through `gridPairToLists`. -/
theorem map_gridReduceInt_piFin_eq_map_idealGridSample {n q : ℕ}
    (T : IntTable) (B : Matrix (Fin n) (Fin n) ℤ)
    (hrows : T.numRows = n) (hcols : T.numCols = n)
    (hmat : ∀ (i j : Fin n), T.entry i.val j.val = B i j)
    (hB : B.det ≠ 0) (hq : 0 < q) (s : ℝ) (hs : 0 < s) (t : EuclideanSpace ℝ (Fin n)) :
    let hqs : 0 < (q : ℝ) * s := mul_pos (Nat.cast_pos.mpr hq) hs
    (PMF.piFin fun i : Fin n => discreteGaussianInt ((q : ℝ) * s) hqs ((q : ℝ) * t i)).map
        (fun r => gridReduceInt n q T (List.ofFn r)) =
      (idealGridSample B hB q hq s hs t).map gridPairToLists := by
  classical
  intro hqs
  have hEx : ∀ r : gridLattice n q, ∃ gy : GridRep B q × intLattice B,
      gridReduceInt n q T (List.ofFn ((gridEmbed n q hq).symm r)) = gridPairToLists gy ∧
        gy.1.toVec = modParallelepiped B (-r.1) ∧
        (gy.2 : EuclideanSpace ℝ (Fin n)) = r.1 + gy.1.toVec := by
    intro r
    have hr_eq : ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2
        (fun i : Fin n => ((List.ofFn ((gridEmbed n q hq).symm r)).getD i.val 0 : ℝ)) = r.1 := by
      have h := (gridEmbed n q hq).apply_symm_apply r
      have h1 : ((q : ℝ)⁻¹ : ℝ) • WithLp.toLp 2
          (fun i : Fin n => (((gridEmbed n q hq).symm r) i : ℝ)) = r.1 :=
        congrArg Subtype.val h
      convert h1 using 3
      ext i; exact congrArg Int.cast (getD_ofFn_eq _ 0 i)
    obtain ⟨gy, hlist, hfst, hsnd⟩ := gridReduceInt_exists_gridRep T B hrows hcols hmat hB hq
      (List.ofFn ((gridEmbed n q hq).symm r))
    rw [hr_eq] at hfst hsnd
    exact ⟨gy, hlist, hfst, hsnd⟩
  choose f hf_list hf_fst hf_snd using hEx
  rw [idealGridSample_eq_map B hB q hq s hs t f hf_fst hf_snd,
    ← piFin_discreteGaussianInt_map_gridEmbed hq s hs t, PMF.map_comp, PMF.map_comp]
  congr 1; funext r'
  simpa [Equiv.symm_apply_apply] using hf_list (gridEmbed n q hq r')

private theorem closeTo_decodeGridPair_idealGridSample {n q : ℕ}
    (T : IntTable) (B : Matrix (Fin n) (Fin n) ℤ)
    (hrows : T.numRows = n) (hcols : T.numCols = n)
    (hmat : ∀ (i j : Fin n), T.entry i.val j.val = B i j)
    (hB : B.det ≠ 0) (hq : 0 < q) (s : ℝ) (hs : 0 < s) (t : EuclideanSpace ℝ (Fin n))
    (μ : PMF (List ℤ × List ℤ)) {δ : ℝ≥0∞}
    (hclose :
      let hqs : 0 < (q : ℝ) * s := mul_pos (Nat.cast_pos.mpr hq) hs
      CloseTo μ
        ((PMF.piFin fun i : Fin n => discreteGaussianInt ((q : ℝ) * s) hqs ((q : ℝ) * t i)).map
          fun r => gridReduceInt n q T (List.ofFn r)) δ) :
    CloseTo (μ.map (decodeGridPair B q)) (idealGridSample B hB q hq s hs t) δ := by
  have h1 := hclose.map (decodeGridPair B q)
  rw [map_gridReduceInt_piFin_eq_map_idealGridSample T B hrows hcols hmat hB hq s hs t,
    PMF.map_comp] at h1
  have hid : (decodeGridPair B q ∘ gridPairToLists (B := B) (q := q)) = id :=
    funext decodeGridPair_gridPairToLists
  rwa [hid, PMF.map_id] at h1

/-- `CloseTo` guarantee for `sampleGridGaussian` decoded into the typed
`GridRep B inp.modulus × intLattice B` law `idealGridSample`. -/
theorem closeTo_eval_sampleGridGaussian_idealGridSample
    (inp : GridSampleInput) (B : Matrix (Fin inp.dim) (Fin inp.dim) ℤ)
    (hrows : inp.basis.numRows = inp.dim) (hcols : inp.basis.numCols = inp.dim)
    (hmat : ∀ (i j : Fin inp.dim), inp.basis.entry i.val j.val = B i j)
    (hB : B.det ≠ 0) (hsSq : 0 < inp.sSq) (hq : 0 < inp.modulus)
    (hqs1 : 1 ≤ (inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ)) (ht : 1 ≤ inp.tail)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hdual : ZLattice.gaussianMass
      (LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal)
      (1 / ((inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ))) 0 - 1 ≤ ε)
    (hprec : 8 * (2 * inp.tail + 6) ≤ 2 ^ inp.prec) :
    let tVec : EuclideanSpace ℝ (Fin inp.dim) :=
      WithLp.toLp 2 fun i : Fin inp.dim => (inp.target.getD i.val 0 : ℝ)
    CloseTo ((ProbComp.eval (sampleGridGaussian inp)).map (decodeGridPair B inp.modulus))
      (idealGridSample B hB inp.modulus hq (Real.sqrt (inp.sSq : ℝ)) (by positivity) tVec)
      (ENNReal.ofReal ((inp.dim : ℝ) *
        ((1 - 1 / (16 * (2 * inp.tail + 6 : ℝ))) ^ inp.maxTrials
          + (8 * inp.tail + 24 : ℝ) / (2 : ℝ) ^ inp.prec
          + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2))))) :=
  closeTo_decodeGridPair_idealGridSample inp.basis B hrows hcols hmat hB hq
    (Real.sqrt (inp.sSq : ℝ)) (by positivity)
    (WithLp.toLp 2 fun i : Fin inp.dim => (inp.target.getD i.val 0 : ℝ))
    (ProbComp.eval (sampleGridGaussian inp))
    (closeTo_eval_sampleGridGaussian_pi inp hsSq hq hqs1 ht hε0 hε hdual hprec)

/-- Smoothing-parameter (`η_ε(ℤ) ≤ q · √sSq`) form of
`closeTo_eval_sampleGridGaussian_idealGridSample`. -/
theorem closeTo_eval_sampleGridGaussian_idealGridSample_of_smoothingParameter_le
    (inp : GridSampleInput) (B : Matrix (Fin inp.dim) (Fin inp.dim) ℤ)
    (hrows : inp.basis.numRows = inp.dim) (hcols : inp.basis.numCols = inp.dim)
    (hmat : ∀ (i j : Fin inp.dim), inp.basis.entry i.val j.val = B i j)
    (hB : B.det ≠ 0) (hsSq : 0 < inp.sSq) (hq : 0 < inp.modulus)
    (hqs1 : 1 ≤ (inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ)) (ht : 1 ≤ inp.tail)
    {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1 / 2)
    (hη : ZLattice.smoothingParameter intLatticeReal ε ≤
      (inp.modulus : ℝ) * Real.sqrt (inp.sSq : ℝ))
    (hprec : 8 * (2 * inp.tail + 6) ≤ 2 ^ inp.prec) :
    let tVec : EuclideanSpace ℝ (Fin inp.dim) :=
      WithLp.toLp 2 fun i : Fin inp.dim => (inp.target.getD i.val 0 : ℝ)
    CloseTo ((ProbComp.eval (sampleGridGaussian inp)).map (decodeGridPair B inp.modulus))
      (idealGridSample B hB inp.modulus hq (Real.sqrt (inp.sSq : ℝ)) (by positivity) tVec)
      (ENNReal.ofReal ((inp.dim : ℝ) *
        ((1 - 1 / (16 * (2 * inp.tail + 6 : ℝ))) ^ inp.maxTrials
          + (8 * inp.tail + 24 : ℝ) / (2 : ℝ) ^ inp.prec
          + (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * (inp.tail : ℝ) ^ 2))))) :=
  closeTo_eval_sampleGridGaussian_idealGridSample inp B hrows hcols hmat hB hsSq hq hqs1 ht
    hε.le hε_le ((ZLattice.smoothingParameter_le_iff intLatticeReal (by positivity) hε).mp hη) hprec

/-! #### 5.2 HNF-free quotient sampler ↔ `PMF.uniformOfFintype (SublatticeQuot B S)` -/

/-- Canonical injective encoding of a typed `SublatticeQuot B S` element into `List ℤ`. -/
def sublatticeQuotToList {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (q : SublatticeQuot B S) : List ℤ :=
  List.ofFn q.1

/-- `sublatticeQuotToList` is injective on `SublatticeQuot B S`. -/
theorem sublatticeQuotToList_injective {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ} :
    Function.Injective (sublatticeQuotToList (B := B) (S := S)) := by
  intro q₁ q₂ h
  apply Subtype.ext; funext i
  have hi := congrArg (fun l : List ℤ => l.getD i.val 0) h
  simpa [sublatticeQuotToList, getD_ofFn_eq] using hi

/-- Left-inverse decoder from `List ℤ` to `SublatticeQuot B S`. -/
noncomputable def decodeSublatticeQuot {n : ℕ} (B S : Matrix (Fin n) (Fin n) ℤ) :
    List ℤ → SublatticeQuot B S :=
  Function.invFun (sublatticeQuotToList (B := B) (S := S))

/-- `decodeSublatticeQuot` is a left inverse to `sublatticeQuotToList`. -/
theorem decodeSublatticeQuot_sublatticeQuotToList {n : ℕ} {B S : Matrix (Fin n) (Fin n) ℤ}
    (q : SublatticeQuot B S) :
    decodeSublatticeQuot B S (sublatticeQuotToList q) = q :=
  Function.leftInverse_invFun sublatticeQuotToList_injective q

/-- Positivity of `quotientIndex TB TS` for invertible `B, S` with `intLattice S ≤ intLattice B`. -/
theorem quotientIndex_pos {n : ℕ} (TB TS : IntTable) (B S : Matrix (Fin n) (Fin n) ℤ)
    (hBwf : TB.WellFormed) (hSwf : TS.WellFormed)
    (hBrows : TB.numRows = n) (hBmat : ∀ (i j : Fin n), TB.entry i.val j.val = B i j)
    (hSrows : TS.numRows = n) (hSmat : ∀ (i j : Fin n), TS.entry i.val j.val = S i j)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    0 < quotientIndex TB TS := by
  rw [quotientIndex_eq_natAbs_div_det TB TS B S hBwf hSwf hBrows hBmat hSrows hSmat hB hSB,
    ← det_sublatticeMat hB hSB]
  exact Int.natAbs_pos.mpr (det_sublatticeMat_ne_zero hS hSB)

/-- Every `quotientReduceInt n TB TS x` output is the exact `sublatticeQuotToList` image of a
typed `SublatticeQuot B S` representative (zero decoding loss). -/
theorem quotientReduceInt_exists_sublatticeQuot {n : ℕ} (TB TS : IntTable)
    (B S : Matrix (Fin n) (Fin n) ℤ)
    (hBrows : TB.numRows = n) (hBcols : TB.numCols = n)
    (hBmat : ∀ (i j : Fin n), TB.entry i.val j.val = B i j)
    (hSrows : TS.numRows = n) (hScols : TS.numCols = n)
    (hSmat : ∀ (i j : Fin n), TS.entry i.val j.val = S i j)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) (x : List ℕ) :
    ∃ qv : SublatticeQuot B S, quotientReduceInt n TB TS x = sublatticeQuotToList qv := by
  obtain ⟨hv_len, hv_vec⟩ :=
    quotientReduceInt_spec TB TS B S hBrows hBcols hBmat hSrows hScols hSmat hS x
  set v := quotientReduceInt n TB TS x
  let xZ : Fin n → ℤ := fun j => (x.getD j.val 0 : ℤ)
  let xE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i : Fin n => ((B *ᵥ xZ) i : ℝ))
  let c : Fin n → ℤ := fun i => v.getD i.val 0
  have hv_bound : ∀ i : Fin n, |c i| ≤ ∑ j : Fin n, |S i j| := by
    intro i
    have h1 := modParallelepiped_abs_le S xE i
    have h2 : modParallelepiped S xE i = (c i : ℝ) := by
      simpa [c, xE, xZ] using (congrArg (fun w : EuclideanSpace ℝ (Fin n) => w i) hv_vec).symm
    rw [h2] at h1
    exact_mod_cast (by simpa [Int.cast_abs, Int.cast_sum] using h1 :
      (|c i| : ℝ) ≤ ((∑ j : Fin n, |S i j| : ℤ) : ℝ))
  have hv_mem : WithLp.toLp 2 (fun i => (c i : ℝ)) ∈ intLattice B := by
    rw [hv_vec]
    exact modParallelepiped_mem_of_le hS hSB ((mem_intLattice_iff B xE).2 ⟨xZ, rfl⟩)
  have hv_idemp : modParallelepiped S (WithLp.toLp 2 (fun i => (c i : ℝ))) =
      WithLp.toLp 2 (fun i => (c i : ℝ)) := by
    rw [hv_vec]; exact modParallelepiped_idemp hS xE
  exact ⟨⟨c, hv_bound, hv_mem, hv_idemp⟩, (list_ofFn_getD_eq hv_len 0).symm⟩

/-- Every output in the support of `sampleQuotientModS inp` encodes a valid `SublatticeQuot B S`
representative recovered losslessly by `decodeSublatticeQuot B S`. -/
theorem mem_support_sampleQuotientModS_exists_sublatticeQuot (inp : QuotientSampleInput)
    (B S : Matrix (Fin inp.dim) (Fin inp.dim) ℤ)
    (hBrows : inp.basis.numRows = inp.dim) (hBcols : inp.basis.numCols = inp.dim)
    (hBmat : ∀ (i j : Fin inp.dim), inp.basis.entry i.val j.val = B i j)
    (hSrows : inp.sublattice.numRows = inp.dim) (hScols : inp.sublattice.numCols = inp.dim)
    (hSmat : ∀ (i j : Fin inp.dim), inp.sublattice.entry i.val j.val = S i j)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) {v : List ℤ}
    (hv : v ∈ (ProbComp.eval (sampleQuotientModS inp)).support) :
    ∃ qv : SublatticeQuot B S,
      v = sublatticeQuotToList qv ∧ decodeSublatticeQuot B S v = qv := by
  rcases mem_support_sampleQuotientModS inp hv with rfl | ⟨x, _, rfl⟩
  · have hlist : List.replicate inp.dim (0 : ℤ) =
        sublatticeQuotToList (SublatticeQuot.zero B S) := by
      apply List.ext_getElem (by simp [sublatticeQuotToList])
      intro i hi _; simp [sublatticeQuotToList]
    exact ⟨SublatticeQuot.zero B S, hlist,
      hlist ▸ decodeSublatticeQuot_sublatticeQuotToList (SublatticeQuot.zero B S)⟩
  · obtain ⟨qv, hqv⟩ :=
      quotientReduceInt_exists_sublatticeQuot inp.basis inp.sublattice B S
        hBrows hBcols hBmat hSrows hScols hSmat hS hSB x
    exact ⟨qv, hqv, hqv ▸ decodeSublatticeQuot_sublatticeQuotToList qv⟩

/-- Pointwise identity: `quotientReduceInt` on `z : Fin n → ZMod (S.det / B.det).natAbs` equals
`sublatticeQuotToList (MR07Core.quotientHom B S hS hSB z)`. -/
theorem quotientReduceInt_eq_quotientHom {n : ℕ} (TB TS : IntTable)
    (B S : Matrix (Fin n) (Fin n) ℤ)
    (hBrows : TB.numRows = n) (hBcols : TB.numCols = n)
    (hBmat : ∀ (i j : Fin n), TB.entry i.val j.val = B i j)
    (hSrows : TS.numRows = n) (hScols : TS.numCols = n)
    (hSmat : ∀ (i j : Fin n), TS.entry i.val j.val = S i j)
    (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (z : Fin n → ZMod (S.det / B.det).natAbs) :
    quotientReduceInt n TB TS (List.ofFn fun i => (z i).val) =
      sublatticeQuotToList (quotientHom B S hS hSB z) := by
  set xNat := List.ofFn fun i : Fin n => (z i).val
  obtain ⟨hv_len, hv_vec⟩ :=
    quotientReduceInt_spec TB TS B S hBrows hBcols hBmat hSrows hScols hSmat hS xNat
  have hx_fun : (fun j : Fin n => (xNat.getD j.val 0 : ℤ)) = fun j => ((z j).val : ℤ) := by
    funext j; exact congrArg Nat.cast (getD_ofFn_eq (fun i => (z i).val) 0 j)
  have hvec_eq :
      WithLp.toLp 2 (fun i : Fin n => ((quotientReduceInt n TB TS xNat).getD i.val 0 : ℝ)) =
        (quotientHom B S hS hSB z).toVec := by
    rw [hv_vec, hx_fun, quotientHom_toVec]
  apply List.ext_getElem (by simp [hv_len, sublatticeQuotToList])
  intro i hi _
  have hi' : i < n := by simpa [hv_len] using hi
  have hi_v := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w ⟨i, hi'⟩) hvec_eq
  simp only [SublatticeQuot.toVec, WithLp.ofLp_toLp] at hi_v
  have hZ : (quotientReduceInt n TB TS xNat).getD i 0 =
      (quotientHom B S hS hSB z).1 ⟨i, hi'⟩ := Int.cast_injective hi_v
  have hi_len : i < (quotientReduceInt n TB TS xNat).length := hv_len.symm ▸ hi'
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_len, Option.getD_some] at hZ
  simpa [sublatticeQuotToList] using hZ

private theorem map_quotientReduceInt_piFin_eq_map_uniform_aux {n : ℕ}
    (TB TS : IntTable) (B S : Matrix (Fin n) (Fin n) ℤ)
    (hBrows : TB.numRows = n) (hBcols : TB.numCols = n)
    (hBmat : ∀ (i j : Fin n), TB.entry i.val j.val = B i j)
    (hSrows : TS.numRows = n) (hScols : TS.numCols = n)
    (hSmat : ∀ (i j : Fin n), TS.entry i.val j.val = S i j)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (D : ℕ) [NeZero D] (hD : D = (S.det / B.det).natAbs) :
    (PMF.piFin fun _ : Fin n => PMF.uniformOfFintype (ZMod D)).map
        (fun z => quotientReduceInt n TB TS (List.ofFn fun i => (z i).val)) =
      (PMF.uniformOfFintype (SublatticeQuot B S)).map sublatticeQuotToList := by
  subst hD
  rw [(PMF.piFin_const _ n).trans (PMF.iid_uniformOfFintype n),
    ← map_quotientHom_uniform_eq_uniform_sublatticeQuot B S hB hS hSB, PMF.map_comp]
  congr 1; funext z
  exact quotientReduceInt_eq_quotientHom TB TS B S hBrows hBcols hBmat hSrows hScols hSmat
    hS hSB z

/-- Exact target-law equality connecting `sampleQuotientModS`'s product-pushforward `PMF` to
`PMF.uniformOfFintype (SublatticeQuot B S)` pushed through `sublatticeQuotToList`. -/
theorem map_quotientReduceInt_piFin_eq_map_uniform {n : ℕ}
    (TB TS : IntTable) (B S : Matrix (Fin n) (Fin n) ℤ)
    (hBwf : TB.WellFormed) (hSwf : TS.WellFormed)
    (hBrows : TB.numRows = n) (hBcols : TB.numCols = n)
    (hBmat : ∀ (i j : Fin n), TB.entry i.val j.val = B i j)
    (hSrows : TS.numRows = n) (hScols : TS.numCols = n)
    (hSmat : ∀ (i j : Fin n), TS.entry i.val j.val = S i j)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    let D := quotientIndex TB TS
    letI : NeZero D :=
      ⟨(quotientIndex_pos TB TS B S hBwf hSwf hBrows hBmat hSrows hSmat hB hS hSB).ne'⟩
    (PMF.piFin fun _ : Fin n => PMF.uniformOfFintype (ZMod D)).map
        (fun z => quotientReduceInt n TB TS (List.ofFn fun i => (z i).val)) =
      (PMF.uniformOfFintype (SublatticeQuot B S)).map sublatticeQuotToList := by
  have : NeZero (quotientIndex TB TS) :=
    ⟨(quotientIndex_pos TB TS B S hBwf hSwf hBrows hBmat hSrows hSmat hB hS hSB).ne'⟩
  exact map_quotientReduceInt_piFin_eq_map_uniform_aux TB TS B S hBrows hBcols hBmat
    hSrows hScols hSmat hB hS hSB (quotientIndex TB TS)
    (quotientIndex_eq_natAbs_div_det TB TS B S hBwf hSwf hBrows hBmat hSrows hSmat hB hSB)

private theorem closeTo_decodeSublatticeQuot_uniform {n : ℕ}
    (TB TS : IntTable) (B S : Matrix (Fin n) (Fin n) ℤ)
    (hBwf : TB.WellFormed) (hSwf : TS.WellFormed)
    (hBrows : TB.numRows = n) (hBcols : TB.numCols = n)
    (hBmat : ∀ (i j : Fin n), TB.entry i.val j.val = B i j)
    (hSrows : TS.numRows = n) (hScols : TS.numCols = n)
    (hSmat : ∀ (i j : Fin n), TS.entry i.val j.val = S i j)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B)
    (μ : PMF (List ℤ)) {δ : ℝ≥0∞}
    (hclose :
      let D := quotientIndex TB TS
      letI : NeZero D :=
        ⟨(quotientIndex_pos TB TS B S hBwf hSwf hBrows hBmat hSrows hSmat hB hS hSB).ne'⟩
      CloseTo μ
        ((PMF.piFin fun _ : Fin n => PMF.uniformOfFintype (ZMod D)).map
          fun z => quotientReduceInt n TB TS (List.ofFn fun i => (z i).val)) δ) :
    CloseTo (μ.map (decodeSublatticeQuot B S)) (PMF.uniformOfFintype (SublatticeQuot B S)) δ := by
  have h1 := hclose.map (decodeSublatticeQuot B S)
  rw [map_quotientReduceInt_piFin_eq_map_uniform TB TS B S hBwf hSwf hBrows hBcols hBmat
    hSrows hScols hSmat hB hS hSB, PMF.map_comp] at h1
  have hid : (decodeSublatticeQuot B S ∘ sublatticeQuotToList (B := B) (S := S)) = id :=
    funext decodeSublatticeQuot_sublatticeQuotToList
  rwa [hid, PMF.map_id] at h1

/-- `CloseTo` guarantee for `sampleQuotientModS` decoded into the typed uniform law
`PMF.uniformOfFintype (SublatticeQuot B S)`. -/
theorem closeTo_eval_sampleQuotientModS_uniform
    (inp : QuotientSampleInput) (B S : Matrix (Fin inp.dim) (Fin inp.dim) ℤ)
    (hBwf : inp.basis.WellFormed) (hSwf : inp.sublattice.WellFormed)
    (hBrows : inp.basis.numRows = inp.dim) (hBcols : inp.basis.numCols = inp.dim)
    (hBmat : ∀ (i j : Fin inp.dim), inp.basis.entry i.val j.val = B i j)
    (hSrows : inp.sublattice.numRows = inp.dim) (hScols : inp.sublattice.numCols = inp.dim)
    (hSmat : ∀ (i j : Fin inp.dim), inp.sublattice.entry i.val j.val = S i j)
    (hB : B.det ≠ 0) (hS : S.det ≠ 0) (hSB : intLattice S ≤ intLattice B) :
    CloseTo ((ProbComp.eval (sampleQuotientModS inp)).map (decodeSublatticeQuot B S))
      (PMF.uniformOfFintype (SublatticeQuot B S))
      ((inp.dim : ℝ≥0∞) / 2 ^ inp.extraBits) :=
  closeTo_decodeSublatticeQuot_uniform inp.basis inp.sublattice B S hBwf hSwf
    hBrows hBcols hBmat hSrows hScols hSmat hB hS hSB
    (ProbComp.eval (sampleQuotientModS inp))
    (closeTo_eval_sampleQuotientModS_pi inp
      (quotientIndex_pos inp.basis inp.sublattice B S hBwf hSwf
        hBrows hBmat hSrows hSmat hB hS hSB))

end Cslib.Crypto.SIS.MR07
