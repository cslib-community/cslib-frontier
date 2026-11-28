/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.BinarySearch
public import CslibFrontier.Computability.Complexity.FineGrained.MaxSAT.Histogram
public import CslibFrontier.Computability.Complexity.FineGrained.Reduction
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Logics.Propositional.CSP.MaxCSPSampling
import CslibFrontier.Computability.Circuit.FanIn
import CslibFrontier.Computability.Complexity.FineGrained.BruteForce
import CslibFrontier.Computability.Complexity.FineGrained.CircuitCounting
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform

/-!
# MAX-SAT / Max-CSP structures, subsampling specializations, and fixed-width SAT solver reductions

This module connects `MaxSAT` (`MaxSAT.thresholdCircuit`, `MaxSAT.optimum`) and general `Max-CSP`
(`MaxCSPInstance`, `MaxCSPSampling`) to supplied fixed-width `k`-SAT solvers (`3 ≤ k`):

1. **Structured encodings:** `enc_structure` encodes `StructInstance`, `ThresholdQuery`,
   `StructSolution`, and the parameterized `MaxCSPInstance Rel ℕ`. They connect to
   `MaxSAT.Instance`, `MaxCSPInstance.ofCNF`, and the `2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`
   (and `1 - η` sample-size) subsampling concentration and optimality-loss theorems.
2. **Threshold compilation (`thresholdToCNF`):** compiles a `ThresholdQuery` in polynomial time via
   `MaxSAT.thresholdCircuit` and `Compiler.toSatCNF` to a 3-CNF formula (`KSAT k` for every `3 ≤ k`)
   with at most `thresholdVarBudget workSize = 957 * workSize + 957` variables, satisfiable iff
   `cutoff ≤ optimum`.
3. **Resource transfer from a supplied fixed-width SAT solver:**
   * *Decision transfer:* `DecidableInExpTime`, `DecidableInSubexpTime`, and `P` membership transfer
     from `KSAT k` (`3 ≤ k`) to `ThresholdLanguage` (measured by `workSize`, and by `numVars` on
     sparse fixed-width instances).
   * *Exact native optimization and witness recovery
     (`FixedWidthSATSolver.exists_optimum_algorithm`, `computableInPolyTime_optimum_of_KSAT`,
     `computableInPolyTime_optimizeWith`,
     `exists_computableInPolyTime_optimize_of_KSAT_mem_P`,
     `computableInPolyTime_maxCSPOptimizeBounded`):* any native `k`-SAT solver (`3 ≤ k`)
     with monotone variable-count factor `timeRate` and polynomial workspace (witnessed at
     `timeRate n = 2 ^ n` by `FixedWidthSATSolver.exists_bruteForce`) computes exact `MaxSAT`
     optima at `timeRate (thresholdVarBudget workSize) * poly(L)` in polynomial space, and any
     polynomial-time `k`-SAT decider (`KSAT k ∈ P encCNF`) computes both the exact optimum and an
     optimal `F.numVars`-bit assignment for `MaxSAT` and bounded-arity Boolean `Max-CSP` in native
     multi-tape polynomial time.
   * *Query-model binary search and witness recovery (`SATQuery`, `optimumByBinarySearchQ`,
     `optimizeByBinarySearchQ`, `optimumMaxCSPByBinarySearchQ`):* bisection via
     `Cslib.Query.lowerBoundBy` followed by unit-clause prefix pinning recovers both the exact
     optimum and an optimal assignment (`StructSolution`) in `FreeM SATQuery` using at most
     `⌊log₂ m⌋ + 1` SAT queries for the value and `⌊log₂ m⌋ + 1 + n` SAT queries (all 3-CNFs of at
     most `thresholdVarBudget (workSize + 2 * n)` variables) for witness recovery, and on an
     `s`-clause subsample of a width-`w` instance queries `k`-SAT only on formulas of at most
     `thresholdVarBudget ((w + 1) * s + 2 * n)` variables while returning an assignment with at most
     `2 * δ * m` optimality loss with probability at least `1 - 2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`
     (and `≥ 1 - η` under the `η` sample-size bound).

## Main definitions

* `Cslib.Complexity.MaxSAT.StructInstance`, `ThresholdQuery`, `StructSolution`:
  structured MAX-SAT instances, threshold queries, and exact optimization outputs.
* `Cslib.Complexity.MaxSAT.thresholdToCNF`, `thresholdVarBudget`: polynomial-time 3-CNF threshold
  compilation and variable-count bound.
* `Cslib.Complexity.MaxSAT.FixedWidthSATSolver`: supplied native `k`-SAT solver bundle.
* `Cslib.Complexity.MaxSAT.optimizeWith`, `maxCSPOptimizeBounded`: native value and witness
  optimization from a supplied SAT decider.
* `Cslib.Complexity.MaxSAT.SATQuery`, `optimumByBinarySearch`, `optimumByBinarySearchQ`,
  `optimizeByBinarySearch`, `optimizeByBinarySearchQ`, `optimumMaxCSPByBinarySearch`,
  `optimumMaxCSPByBinarySearchQ`: pure and `FreeM SATQuery` binary-search solvers.

## Main results

* `Cslib.Complexity.MaxSAT.computableInPolyTime_thresholdToCNF`,
  `polyTimeReducible_thresholdLanguage_KSAT`: polynomial-time reduction to `KSAT k` (`3 ≤ k`).
* `Cslib.Complexity.MaxSAT.FixedWidthSATSolver.exists_optimum_algorithm`,
  `computableInPolyTime_optimum_of_KSAT`: native value optimization from `k`-SAT solvers.
* `Cslib.Complexity.MaxSAT.optimizeWith_spec`, `computableInPolyTime_optimizeWith`,
  `exists_computableInPolyTime_optimize_of_KSAT_mem_P`, `maxCSPOptimizeBounded_spec`,
  `computableInPolyTime_maxCSPOptimizeBounded`: native multi-tape polynomial-time value and
  optimal assignment recovery.
* `Cslib.Complexity.MaxSAT.optimumByBinarySearch_eq_optimum`,
  `countQueries_optimumByBinarySearchQ_le`, `cost_optimumByBinarySearchQ_le`,
  `optimizeByBinarySearch_spec`, `countQueries_optimizeByBinarySearchQ_le`,
  `cost_optimizeByBinarySearchQ_le`, `sample_optimumByBinarySearch_spec`,
  `sample_optimizeByBinarySearch_spec`, `sample_optimizeByBinarySearch_spec_of_sample_size`,
  `optimumMaxCSPByBinarySearch_eq_optimum`, `countQueries_optimumMaxCSPByBinarySearchQ_le`,
  `cost_optimumMaxCSPByBinarySearchQ_le`:
  correctness, `FreeM` query-count/cost bounds, and subsampling transfer theorems.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
-/

public section

namespace Cslib.Complexity.MaxSAT

open Cslib.Algorithms.Lean Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Frontier
  Cslib.Logic.PL Cslib.Query Turing.MultiTapeTM ComputableInPolyTime

/-! ### `#4391`-compliant `MaxSAT` structures, encodings, and `Max-CSP` bridges -/

/-- A MAX-SAT instance packaged as a structure with named `numVars` and `clauses` fields. -/
@[ext]
structure StructInstance where
  /-- Number of declared Boolean variables (`0, …, numVars - 1`). -/
  numVars : ℕ
  /-- Clause list counted with multiplicity. -/
  clauses : CNF ℕ
  deriving DecidableEq, Repr

/-- Unary declared variable count followed by `encCNF`, matching `MaxSAT.encInstance`. -/
enc_structure encStructInstance : StructInstance where
  numVars : encUnary, clauses : encCNF

attribute [fun_prop] encStructInstance_numVars_polyTime encStructInstance_clauses_polyTime
  encStructInstance_mk_polyTime

/-- A MAX-SAT threshold decision query packaged as a structure. -/
@[ext]
structure ThresholdQuery where
  /-- Underlying MAX-SAT instance. -/
  inst : StructInstance
  /-- Requested minimum number of satisfied clauses. -/
  cutoff : ℕ
  deriving DecidableEq, Repr

/-- Structured threshold query encoding, matching `MaxSAT.encQuery` bit-for-bit. -/
enc_structure encThresholdQuery : ThresholdQuery where
  inst : encStructInstance, cutoff : encUnary

attribute [fun_prop] encThresholdQuery_inst_polyTime encThresholdQuery_cutoff_polyTime
  encThresholdQuery_mk_polyTime

/-- Exact optimization output for a `StructInstance` or `MaxCSPInstance`: optimal objective value
paired with truth-value bits for variables `0, …, numVars - 1`. -/
@[ext]
structure StructSolution where
  /-- Optimal objective value. -/
  optValue : ℕ
  /-- Truth values for variables `0, …, numVars - 1`. -/
  assignmentBits : List Bool
  deriving DecidableEq, Repr

/-- Binary optimum value followed by raw assignment bits (`encPair encNat encBits`). -/
enc_structure encStructSolution : StructSolution where
  optValue : encNat, assignmentBits : encBits

attribute [fun_prop] encStructSolution_optValue_polyTime
  encStructSolution_assignmentBits_polyTime encStructSolution_mk_polyTime

namespace StructInstance

/-- Underlying pair representation `MaxSAT.Instance`. -/
@[expose] def toPair (F : StructInstance) : Instance :=
  (F.numVars, F.clauses)

/-- Wrap a pair `MaxSAT.Instance` as a `StructInstance`. -/
@[expose] def ofPair (F : Instance) : StructInstance :=
  ⟨F.1, F.2⟩

/-- View a `StructInstance` as a Boolean `MaxCSPInstance (List Bool) ℕ`. -/
@[expose] def toMaxCSP (F : StructInstance) : MaxCSPInstance (List Bool) ℕ :=
  MaxCSPInstance.ofCNF F.numVars F.clauses

/-- Clause-satisfaction score of `x : BitString F.numVars`. -/
@[expose] def score (F : StructInstance) (x : BitString F.numVars) : ℕ :=
  MaxSAT.score F.toPair x

/-- Number of declared assignments achieving score at least `q`. -/
@[expose] def thresholdCount (F : StructInstance) (q : ℕ) : ℕ :=
  MaxSAT.thresholdCount F.toPair q

/-- Maximum number of simultaneously satisfied clauses. -/
@[expose] def optimum (F : StructInstance) : ℕ :=
  MaxSAT.optimum F.toPair

/-- Structural size: literal occurrences plus clauses. -/
@[expose] def workSize (F : StructInstance) : ℕ :=
  MaxSAT.workSize F.toPair

@[simp]
theorem score_toMaxCSP (F : StructInstance) (x : BitString F.numVars) :
    F.toMaxCSP.score MaxCSP.clauseSem x = F.score x :=
  MaxCSPInstance.score_ofCNF F.numVars F.clauses x

@[simp]
theorem thresholdCount_toMaxCSP (F : StructInstance) (q : ℕ) :
    F.toMaxCSP.thresholdCount MaxCSP.clauseSem q = F.thresholdCount q :=
  MaxCSPInstance.thresholdCount_ofCNF F.numVars F.clauses q

@[simp]
theorem optimum_toMaxCSP (F : StructInstance) :
    F.toMaxCSP.optimum MaxCSP.clauseSem = F.optimum :=
  MaxCSPInstance.optimum_ofCNF F.numVars F.clauses

@[simp]
theorem workSize_toMaxCSP (F : StructInstance) :
    F.toMaxCSP.workSize = F.workSize :=
  MaxCSPInstance.workSize_ofCNF F.numVars F.clauses

/-! #### Subsampling specializations for `StructInstance` -/

/-- Subsampled `s`-clause `StructInstance` indexed by `ω : Fin s → Fin F.clauses.length`. -/
@[expose] def sample (F : StructInstance) {s : ℕ} (ω : Fin s → Fin F.clauses.length) :
    StructInstance :=
  ⟨F.numVars, List.ofFn fun j => F.clauses[ω j]⟩

/-- Uniform distribution over `s`-clause subsamples of a nonempty `StructInstance`. -/
@[expose] noncomputable def samplePMF (F : StructInstance) (hm : 0 < F.clauses.length) (s : ℕ) :
    _root_.PMF (Fin s → Fin F.clauses.length) :=
  MaxCSP.uniformSamplePMF F.clauses.length hm s

private def castSampleIdx (F : StructInstance) {s : ℕ} (ω : Fin s → Fin F.clauses.length) :
    Fin s → Fin F.toMaxCSP.constraints.length :=
  fun j => ⟨(ω j).val, by simp only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF, (ω j).isLt]⟩

private theorem toMaxCSP_sample (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) :
    (F.sample ω).toMaxCSP = F.toMaxCSP.sample (F.castSampleIdx ω) := by
  refine MaxCSPInstance.ext rfl ?_
  simp only [MaxCSPInstance.sample, Fin.getElem_fin, castSampleIdx]
  simp only [toMaxCSP, sample, MaxCSPInstance.ofCNF, List.map_ofFn, Function.comp_def,
    Fin.getElem_fin, List.getElem_map]

private theorem score_toMaxCSP_sample (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) (x : BitString F.numVars) :
    (F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x = (F.sample ω).score x := by
  have hcon : (F.toMaxCSP.sample (F.castSampleIdx ω)).constraints =
      (F.sample ω).toMaxCSP.constraints :=
    congrArg MaxCSPInstance.constraints (F.toMaxCSP_sample ω).symm
  rw [← (F.sample ω).score_toMaxCSP x]
  simp only [MaxCSPInstance.score, MaxCSPInstance.evalCount, hcon]
  rfl

private theorem optimum_toMaxCSP_sample (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) :
    (F.toMaxCSP.sample (F.castSampleIdx ω)).optimum MaxCSP.clauseSem = (F.sample ω).optimum :=
  Finset.sup_congr rfl fun x _ => F.score_toMaxCSP_sample ω x

theorem workSize_sample_le_of_width {w : ℕ} {F : StructInstance}
    (hw : ∀ c ∈ F.clauses, c.length ≤ w) {s : ℕ} (ω : Fin s → Fin F.clauses.length) :
    (F.sample ω).workSize ≤ (w + 1) * s := by
  rw [← workSize_toMaxCSP, toMaxCSP_sample]
  refine MaxCSPInstance.workSize_sample_le_of_width (fun c hc => ?_) _
  simp only [toMaxCSP, MaxCSPInstance.ofCNF, List.mem_map] at hc
  obtain ⟨cl, hcl, rfl⟩ := hc
  simpa only [Constraint.ofClause, List.length_map] using hw cl hcl

/-- **Uniform clause-subsampling concentration for MAX-SAT (`2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`).**
-/
theorem exists_sample_score_abs_sub_ge_le (F : StructInstance) (hm : 0 < F.clauses.length)
    (s : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | ∃ x : BitString F.numVars,
        δ * (F.clauses.length : ℝ) ≤
          |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) -
            (F.score x : ℝ)|}).toReal ≤
      2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
  have hm' : 0 < F.toMaxCSP.constraints.length := by
    simpa only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF] using hm
  let e : (Fin s → Fin F.clauses.length) ≃ (Fin s → Fin F.toMaxCSP.constraints.length) :=
    Equiv.piCongrRight fun _ =>
      finCongr (MaxCSPInstance.length_constraints_ofCNF F.numVars F.clauses).symm
  have hpmf : (F.samplePMF hm s).map e = F.toMaxCSP.samplePMF hm' s := by
    have : Nonempty (Fin F.clauses.length) := ⟨⟨0, hm⟩⟩
    have : Nonempty (Fin F.toMaxCSP.constraints.length) := ⟨⟨0, hm'⟩⟩
    exact Cslib.Probability.PMF.uniformOfFintype_map_equiv e
  have h := F.toMaxCSP.boolean_exists_sample_score_abs_sub_ge_le MaxCSP.clauseSem hm' s hδ
  rw [← hpmf, _root_.PMF.toOuterMeasure_map_apply] at h
  refine (le_of_eq ?_).trans h
  congr 2; ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, toMaxCSP,
    MaxCSPInstance.length_constraints_ofCNF]
  refine exists_congr fun x => ?_
  have hsc : (F.toMaxCSP.sample (e ω)).score MaxCSP.clauseSem x = (F.sample ω).score x :=
    F.score_toMaxCSP_sample ω x
  have hfull : F.toMaxCSP.score MaxCSP.clauseSem x = F.score x := F.score_toMaxCSP x
  change _ ↔ δ * (F.clauses.length : ℝ) ≤
    |(F.clauses.length : ℝ) / (s : ℝ) *
      (((F.toMaxCSP.sample (e ω)).score MaxCSP.clauseSem x : ℕ) : ℝ) -
      ((F.toMaxCSP.score MaxCSP.clauseSem x : ℕ) : ℝ)|
  rw [hsc, hfull]

private theorem hunif_toMaxCSP (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) {ε : ℝ}
    (hunif : ∀ x : BitString F.numVars,
      |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) - (F.score x : ℝ)| ≤ ε) :
    ∀ x : BitString F.toMaxCSP.numVars,
      |(F.toMaxCSP.constraints.length : ℝ) / (s : ℝ) *
          ((F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x : ℝ) -
        (F.toMaxCSP.score MaxCSP.clauseSem x : ℝ)| ≤ ε := fun x => by
  let x' : BitString F.numVars := x
  change |(F.toMaxCSP.constraints.length : ℝ) / (s : ℝ) *
      (((F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x' : ℕ) : ℝ) -
    ((F.toMaxCSP.score MaxCSP.clauseSem x' : ℕ) : ℝ)| ≤ ε
  rw [F.score_toMaxCSP_sample ω x', F.score_toMaxCSP x']
  simpa only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF] using hunif x'

/-- **The `2 * δ * m` optimality loss bound for MAX-SAT.** -/
theorem optimum_sub_score_le_two_mul (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) {δ : ℝ}
    (hunif : ∀ x : BitString F.numVars,
      |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) - (F.score x : ℝ)| ≤
        δ * (F.clauses.length : ℝ))
    {xHat : BitString F.numVars}
    (hmax : ∀ x : BitString F.numVars, (F.sample ω).score x ≤ (F.sample ω).score xHat) :
    (F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * (F.clauses.length : ℝ) := by
  have hunif' : ∀ x : BitString F.toMaxCSP.numVars,
      |(F.toMaxCSP.constraints.length : ℝ) / (s : ℝ) *
          ((F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x : ℝ) -
        (F.toMaxCSP.score MaxCSP.clauseSem x : ℝ)| ≤
        δ * (F.toMaxCSP.constraints.length : ℝ) := by
    simpa only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF] using F.hunif_toMaxCSP ω hunif
  have hmax' : ∀ x : BitString F.toMaxCSP.numVars,
      (F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x ≤
        (F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem xHat := fun x => by
    let x' : BitString F.numVars := x
    change (F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x' ≤
      (F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem xHat
    rw [F.score_toMaxCSP_sample ω x', F.score_toMaxCSP_sample ω xHat]
    exact hmax x'
  have h := F.toMaxCSP.optimum_sub_score_le_two_mul MaxCSP.clauseSem (F.castSampleIdx ω)
    hunif' hmax'
  rw [F.optimum_toMaxCSP, F.score_toMaxCSP xHat] at h
  simpa only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF] using h

/-- **Deterministic rescaled sample optimum bound for MAX-SAT.** -/
theorem abs_rescaled_optimum_sub_le (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) {ε : ℝ}
    (hunif : ∀ x : BitString F.numVars,
      |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) - (F.score x : ℝ)| ≤ ε) :
    |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum : ℝ) - (F.optimum : ℝ)| ≤ ε := by
  have h := F.toMaxCSP.abs_rescaled_optimum_sub_le MaxCSP.clauseSem (F.castSampleIdx ω)
    (F.hunif_toMaxCSP ω hunif)
  rw [F.optimum_toMaxCSP_sample ω, F.optimum_toMaxCSP] at h
  simpa only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF] using h

/-- **Success probability (`≥ 1 - 2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`) for MAX-SAT subsampling.** -/
theorem one_sub_le_sample_good (F : StructInstance) (hm : 0 < F.clauses.length) (s : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - 2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (∀ xHat : BitString F.numVars,
            (∀ x, (F.sample ω).score x ≤ (F.sample ω).score xHat) →
              (F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * (F.clauses.length : ℝ)) ∧
          |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum : ℝ) -
            (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}).toReal := by
  set good : Set (Fin s → Fin F.clauses.length) :=
    {ω | (∀ xHat : BitString F.numVars,
        (∀ x, (F.sample ω).score x ≤ (F.sample ω).score xHat) →
          (F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * (F.clauses.length : ℝ)) ∧
      |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum : ℝ) -
        (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}
  have hsum := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl (F.samplePMF hm s) good
  have hcompl :
      ((F.samplePMF hm s).toOuterMeasure goodᶜ).toReal ≤
        2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
    refine (Cslib.Probability.PMF.toOuterMeasure_toReal_mono (F.samplePMF hm s) ?_).trans
      (F.exists_sample_score_abs_sub_ge_le hm s hδ)
    intro ω hω
    by_contra hnb
    simp only [Set.mem_ofPred_eq, not_exists, not_le] at hnb
    have hunif : ∀ x : BitString F.numVars,
        |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) - (F.score x : ℝ)| ≤
          δ * (F.clauses.length : ℝ) := fun x => (hnb x).le
    exact hω ⟨fun _ hmax => F.optimum_sub_score_le_two_mul ω hunif hmax,
      F.abs_rescaled_optimum_sub_le ω hunif⟩
  linarith

/-- **Success probability `≥ 1 - η` for MAX-SAT subsampling under
`(n + 1) * log 2 + log (1 / η) ≤ 2 * s * δ ^ 2`.** -/
theorem one_sub_le_sample_good_of_sample_size (F : StructInstance) (hm : 0 < F.clauses.length)
    {s : ℕ} {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η)
    (hs : (F.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    1 - η ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (∀ xHat : BitString F.numVars,
            (∀ x, (F.sample ω).score x ≤ (F.sample ω).score xHat) →
              (F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * (F.clauses.length : ℝ)) ∧
          |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum : ℝ) -
            (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}).toReal := by
  have h1 := MaxCSP.two_pow_succ_mul_exp_le_eta hη hs
  have h2 := F.one_sub_le_sample_good hm s hδ
  linarith

end StructInstance

/-! ### Parameterized encoding for `MaxCSPInstance` -/

variable {Rel : Type} in
/-- The framed unary variable count followed by the constraints encoded by `encCSP`. -/
enc_structure encMaxCSPInstance (encRel : Rel ↪ List Bool) : MaxCSPInstance Rel ℕ where
  numVars : encUnary, constraints : (encCSP encRel encNat)

attribute [fun_prop] encMaxCSPInstance_numVars_polyTime encMaxCSPInstance_constraints_polyTime

/-- Width-guarded compilation of a Boolean `MaxCSPInstance Rel ℕ` to a `StructInstance` via
forbidden-pattern `CSP.toCNFBounded`. -/
@[expose] def maxCSPToStruct {Rel : Type} (w : ℕ) (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) : StructInstance :=
  ⟨F.numVars, F.constraints.toCNFBounded w sem⟩

@[fun_prop]
theorem computableInPolyTime_maxCSPToStruct {Rel : Type} [Finite Rel] (encRel : Rel ↪ List Bool)
    (w : ℕ) (sem : Rel → List Bool → Bool) :
    ComputableInPolyTime (maxCSPToStruct w sem) (encMaxCSPInstance encRel) encStructInstance :=
  encStructInstance_mk_polyTime (encMaxCSPInstance_numVars_polyTime encRel .id')
    ((CSP.computableInPolyTime_toCNFBounded_of_finite encRel encNat w sem).comp
      (encMaxCSPInstance_constraints_polyTime encRel .id'))

theorem optimum_maxCSPToStruct_add_length {Rel : Type} {w : ℕ} (sem : Rel → List Bool → Bool)
    {F : MaxCSPInstance Rel ℕ} (hw : ∀ c ∈ F.constraints, c.scope.length ≤ w) :
    (maxCSPToStruct w sem F).optimum + F.constraints.length =
      (maxCSPToStruct w sem F).clauses.length + F.optimum sem := by
  dsimp only [maxCSPToStruct]
  rw [← StructInstance.optimum_toMaxCSP]
  dsimp only [StructInstance.toMaxCSP]
  rw [CSP.toCNFBounded_eq_toCNF hw]
  exact F.optimum_ofCNF_toCNF_add_length sem

theorem score_maxCSPToStruct_add_length {Rel : Type} {w : ℕ} (sem : Rel → List Bool → Bool)
    {F : MaxCSPInstance Rel ℕ} (hw : ∀ c ∈ F.constraints, c.scope.length ≤ w)
    (x : BitString F.numVars) :
    (maxCSPToStruct w sem F).score x + F.constraints.length =
      (maxCSPToStruct w sem F).clauses.length + F.score sem x := by
  dsimp only [maxCSPToStruct]
  rw [← StructInstance.score_toMaxCSP]
  dsimp only [StructInstance.toMaxCSP]
  rw [CSP.toCNFBounded_eq_toCNF hw]
  exact F.score_ofCNF_toCNF_add_length sem x

/-! ### Polynomial-time threshold reduction to fixed-width `k`-SAT (`3 ≤ k`) -/

/-- The MAX-SAT threshold decision language: queries `q` whose cutoff is achievable. -/
@[expose] def ThresholdLanguage : Set ThresholdQuery :=
  {q | q.cutoff ≤ q.inst.optimum}

/-- Work-size parameter of a threshold query (`workSize` of its underlying instance). -/
@[expose] def ThresholdQuery.workSize (q : ThresholdQuery) : ℕ :=
  q.inst.workSize

/-- Compile a `ThresholdQuery` to a 3-CNF formula via `MaxSAT.thresholdCircuit` and
`Compiler.toSatCNF`. -/
@[expose] def thresholdToCNF (q : ThresholdQuery) : CNF ℕ :=
  Compiler.toSatCNF (thresholdCircuit q.inst.toPair q.cutoff) Boolean.interpretation

/-- Every clause of `thresholdToCNF q` has length at most `3`. -/
theorem length_clause_mem_thresholdToCNF (q : ThresholdQuery) {cl : Clause ℕ}
    (hcl : cl ∈ thresholdToCNF q) : cl.length ≤ 3 :=
  Compiler.length_le_of_mem_toCNF Boolean.interpretation (fun _ b => b)
    (Circuit.fanInAtMost_of_arity_le Boolean.arity_le_two _) hcl

/-- `thresholdToCNF q` is satisfiable iff `q.cutoff ≤ q.inst.optimum`. -/
theorem satisfiable_thresholdToCNF_iff (q : ThresholdQuery) :
    (thresholdToCNF q).Satisfiable ↔ q.cutoff ≤ q.inst.optimum := by
  rw [thresholdToCNF, Compiler.satisfiable_toSatCNF_iff, mem_SignatureCircuitSAT]
  simp only [eval_thresholdCircuit, decide_eq_true_eq]
  rw [← thresholdCount_pos_iff, thresholdCount_pos_iff_le_optimum]
  rfl

/-- For every fixed width `k ≥ 3`, `thresholdToCNF q` belongs to `KSAT k` iff `q` belongs to
`ThresholdLanguage`. -/
theorem thresholdToCNF_mem_KSAT_iff {k : ℕ} (hk : 3 ≤ k) (q : ThresholdQuery) :
    thresholdToCNF q ∈ KSAT k ↔ q ∈ ThresholdLanguage := by
  simp only [KSAT, ThresholdLanguage, Set.mem_ofPred_eq, satisfiable_thresholdToCNF_iff]
  exact ⟨fun h => h.2, fun h => ⟨fun _ hcl => (length_clause_mem_thresholdToCNF q hcl).trans hk, h⟩⟩

/-- The variable budget of `thresholdToCNF` on work size `w`: the compiled 3-CNF of a query of
work size `w` has at most `thresholdVarBudget w = 957 * w + 957` variables
(`numVars_thresholdToCNF_le`). -/
@[expose] def thresholdVarBudget (w : ℕ) : ℕ := 957 * w + 957

/-- A larger work size has a larger variable budget. -/
theorem thresholdVarBudget_mono : Monotone thresholdVarBudget := fun _ _ h => by
  unfold thresholdVarBudget
  omega

/-- `thresholdToCNF q` uses at most `thresholdVarBudget q.workSize` distinct variables. -/
theorem numVars_thresholdToCNF_le (q : ThresholdQuery) :
    (thresholdToCNF q).numVars ≤ thresholdVarBudget q.workSize := by
  have hnum := Compiler.numVars_toCNF_le (c := thresholdCircuit q.inst.toPair q.cutoff)
    Boolean.interpretation (fun _ b => b) (Circuit.fanInAtMost_of_arity_le Boolean.arity_le_two _)
  have hsize := size_thresholdCircuit_le q.inst.toPair q.cutoff
  dsimp only [thresholdToCNF, Compiler.toSatCNF, thresholdVarBudget, ThresholdQuery.workSize,
    StructInstance.workSize] at hnum ⊢
  omega

/-- On an instance whose clauses all have width at most `w`, `thresholdToCNF q` uses at most
`thresholdVarBudget ((w + 1) * m)` distinct variables (`m = q.inst.clauses.length`). -/
theorem numVars_thresholdToCNF_le_of_width {w : ℕ} (q : ThresholdQuery)
    (hw : ∀ c ∈ q.inst.clauses, c.length ≤ w) :
    (thresholdToCNF q).numVars ≤ thresholdVarBudget ((w + 1) * q.inst.clauses.length) :=
  (numVars_thresholdToCNF_le q).trans
    (thresholdVarBudget_mono (workSize_le_of_width w q.inst.toPair hw))

/-- `thresholdToCNF q` has at most `8 * (numVars + 1)` clauses. -/
theorem length_thresholdToCNF_le (q : ThresholdQuery) :
    (thresholdToCNF q).length ≤ 8 * ((thresholdToCNF q).numVars + 1) := by
  have h := Compiler.length_toCNF_le_numVars Boolean.interpretation (fun _ b => b)
    (Circuit.fanInAtMost_of_arity_le Boolean.arity_le_two (thresholdCircuit q.inst.toPair q.cutoff))
  simpa only [thresholdToCNF, Compiler.toSatCNF, Nat.reduceAdd, Nat.reducePow] using h

/-- `thresholdToCNF` is computable in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_thresholdToCNF :
    ComputableInPolyTime thresholdToCNF encThresholdQuery encCNF := by
  have hinst := encThresholdQuery_inst_polyTime ComputableInPolyTime.id'
  have htoQuery : ComputableInPolyTime (fun q : ThresholdQuery => (q.inst.toPair, q.cutoff))
      encThresholdQuery encQuery :=
    ((encStructInstance_numVars_polyTime hinst).prod
      (encStructInstance_clauses_polyTime hinst)).prod
      (encThresholdQuery_cutoff_polyTime ComputableInPolyTime.id')
  have hsat : ComputableInPolyTime
      (fun p : Query => Compiler.toSatCNF (thresholdCircuit p.1 p.2) Boolean.interpretation)
      encQuery encCNF :=
    ((CircuitCounting.computableInPolyTime_toSatCNF (σ := Boolean.signature) Boolean.encOp
      Boolean.interpretation).comp computableInPolyTime_thresholdCircuit).of_enc_eq fun _ => rfl
  exact (hsat.comp htoQuery).of_enc_eq fun _ => rfl

/-- `ThresholdLanguage` reduces in polynomial time to `KSAT k` for every `k ≥ 3`. -/
theorem polyTimeReducible_thresholdLanguage_KSAT {k : ℕ} (hk : 3 ≤ k) :
    PolyTimeReducible encThresholdQuery encCNF ThresholdLanguage (KSAT k) :=
  ⟨thresholdToCNF, computableInPolyTime_thresholdToCNF,
    fun q => (thresholdToCNF_mem_KSAT_iff hk q).symm⟩

/-- `ThresholdLanguage` reduces in polynomial time to `ThreeSAT`. -/
theorem polyTimeReducible_thresholdLanguage_ThreeSAT :
    PolyTimeReducible encThresholdQuery encCNF ThresholdLanguage ThreeSAT :=
  polyTimeReducible_thresholdLanguage_KSAT le_rfl

/-! ### Resource transfer from a supplied fixed-width SAT solver -/

/-- **Exponential-time decision transfer:** a `2 ^ (δ * n)` decider for `KSAT k` (`3 ≤ k`) gives a
`2 ^ (957 * δ * workSize)` decider for `ThresholdLanguage`. -/
theorem decidableInExpTime_thresholdLanguage_of_KSAT {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 ≤ δ)
    (hKSAT : DecidableInExpTime (KSAT k) encCNF CNF.numVars δ) :
    DecidableInExpTime ThresholdLanguage encThresholdQuery ThresholdQuery.workSize (957 * δ) :=
  hKSAT.of_reduction computableInPolyTime_thresholdToCNF
    (fun q => (thresholdToCNF_mem_KSAT_iff hk q).symm) numVars_thresholdToCNF_le hδ

/-- **Subexponential-time decision transfer:** subexponential decidability of `KSAT k` (`3 ≤ k`) in
`CNF.numVars` transfers to `ThresholdLanguage` in `ThresholdQuery.workSize`. -/
theorem decidableInSubexpTime_thresholdLanguage_of_KSAT {k : ℕ} (hk : 3 ≤ k)
    (hKSAT : DecidableInSubexpTime (KSAT k) encCNF CNF.numVars) :
    DecidableInSubexpTime ThresholdLanguage encThresholdQuery ThresholdQuery.workSize :=
  hKSAT.of_reduction computableInPolyTime_thresholdToCNF
    (fun q => (thresholdToCNF_mem_KSAT_iff hk q).symm) numVars_thresholdToCNF_le

/-- **Polynomial-time decision transfer:** if `KSAT k ∈ P encCNF` (`3 ≤ k`), then
`ThresholdLanguage ∈ P encThresholdQuery`. -/
theorem mem_P_thresholdLanguage_of_KSAT {k : ℕ} (hk : 3 ≤ k) (hKSAT : KSAT k ∈ P encCNF) :
    ThresholdLanguage ∈ P encThresholdQuery :=
  (polyTimeReducible_thresholdLanguage_KSAT hk).mem_P hKSAT

/-- A supplied native deterministic solver for `k`-SAT with a monotone parameter time factor
`timeRate` in `CNF.numVars` and polynomial workspace in the encoded formula length. -/
structure FixedWidthSATSolver (k : ℕ) where
  /-- Boolean decision procedure on CNF formulas. -/
  solve : CNF ℕ → Bool
  /-- Monotone parameter factor as a function of `CNF.numVars`. -/
  timeRate : ℕ → ℕ
  /-- Polynomial exponent in the time bound. -/
  timeExp : ℕ
  /-- Polynomial exponent in the workspace bound. -/
  spaceExp : ℕ
  /-- Correctness on all formulas of clause width at most `k`. -/
  correct : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable)
  /-- Non-vanishing rate factor (`1 ≤ timeRate n`). -/
  one_le_timeRate : ∀ n, 1 ≤ timeRate n
  /-- Monotonicity of `timeRate` in `CNF.numVars`. -/
  mono_timeRate : Monotone timeRate
  /-- Native machine certificate for `solve`. -/
  computable : ComputableInO solve encCNF encBool
    (fun φ => timeRate φ.numVars * ((encCNF φ).length + 1) ^ timeExp)
    (fun φ => ((encCNF φ).length + 1) ^ spaceExp)

/-- **Classical `2 ^ n` exhaustive-search `FixedWidthSATSolver k`:** `BruteForce.search` yields a
native polynomial-space `FixedWidthSATSolver k` with `timeRate n = 2 ^ n` for every `k`. -/
theorem FixedWidthSATSolver.exists_bruteForce (k : ℕ) :
    ∃ solver : FixedWidthSATSolver k,
      solver.solve = BruteForce.search ∧ solver.timeRate = fun n => 2 ^ n := by
  let BfState := (CNF ℕ × ℕ) × Bool
  let encBf : BfState ↪ List Bool := encPair (encPair encCNF encNat) encBool
  let bfInit (φ : CNF ℕ) : BfState := ((φ, 0), false)
  let bfStep (s : BfState) : BfState :=
    ((s.1.1, s.1.2 + 1), s.2 || s.1.1.eval (bitsAssignment s.1.1.distinctVars s.1.2))
  let bfRounds (φ : CNF ℕ) : ℕ := 2 ^ φ.numVars
  have hiter : ∀ (φ : CNF ℕ) (m : ℕ), bfStep^[m] (bfInit φ) =
      ((φ, m), (List.range m).any fun i => φ.eval (bitsAssignment φ.distinctVars i)) := by
    intro φ m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, List.range_succ, List.any_append, List.any_cons,
        List.any_nil, Bool.or_false]
  have hrounds_poly : ComputableInPolyTime bfRounds encCNF encNat :=
    ComputableInPolyTime.binary_two_pow.comp SAT.computableInPolyTime_numVars
  have hinit_poly : ComputableInPolyTime bfInit encCNF encBf :=
    (ComputableInPolyTime.id'.prod (const 0)).prod (const false)
  have hstep_poly : ComputableInPolyTime bfStep encBf encBf := by
    have hφ : ComputableInPolyTime (fun s : BfState => s.1.1) encBf encCNF :=
      (fst encCNF encNat).comp (fst _ _)
    have hi : ComputableInPolyTime (fun s : BfState => s.1.2) encBf encNat :=
      (snd encCNF encNat).comp (fst _ _)
    exact (hφ.prod (binary_add' hi (const 1))).prod
      (bool_or.comp ((snd _ _).prod (computableInPolyTime_eval_bitsAssignment.comp
        ((hφ.prod (SAT.computableInPolyTime_distinctVars.comp hφ)).prod hi))))
  obtain ⟨dn, _, hdn⟩ := hrounds_poly.exists_degree
  obtain ⟨di, _, hdi⟩ := hinit_poly.exists_degree
  obtain ⟨ds, _, hds⟩ := hstep_poly.exists_degree
  obtain ⟨cn, en, hnum_le⟩ := SAT.computableInPolyTime_numVars.polyBounded_length.exists_le
  have hrounds_len (φ : CNF ℕ) : (encNat (bfRounds φ)).length = φ.numVars + 1 := by
    dsimp only [bfRounds]; rw [length_encNat_two_pow]
  let B (φ : CNF ℕ) : ℕ :=
    2 * (2 * (encCNF φ).length + (cn * ((encCNF φ).length + 1) ^ en + 1) + 2) + 4
  have hstate (φ : CNF ℕ) (m : ℕ) (hm : m ≤ bfRounds φ) :
      (encBf (bfStep^[m] (bfInit φ))).length ≤ B φ := by
    have hm_len : (encNat m).length ≤ φ.numVars + 1 :=
      (length_encNat_mono hm).trans_eq (hrounds_len φ)
    have hnv : φ.numVars ≤ cn * ((encCNF φ).length + 1) ^ en := by
      simpa only [encUnary_apply, List.length_replicate] using hnum_le φ
    rw [hiter]
    dsimp only [encBf, B]
    rw [length_encPair, length_encPair, encBool_apply, List.length_singleton]
    dsimp only; omega
  have hloop := ComputableInO.iterate hdn.inO hdi.inO hds.inO
    (R := fun φ => (B φ + 1) ^ ds) (Q := fun φ => (B φ + 1) ^ ds) (B := B)
    (fun φ m hm => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate φ m hm) 1) ds)
    (fun φ m hm => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate φ m hm) 1) ds)
    hstate
  have hL : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) (fun φ => (encCNF φ).length) := .self
  have hL1 := hL.add (.const 1)
  have hnvP : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) CNF.numVars :=
    SAT.computableInPolyTime_numVars.polyBounded_length.mono fun φ => by
      simp only [encUnary_apply, List.length_replicate, le_rfl]
  have hB_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) B :=
    ((PolyBounded.const 2).mul (((PolyBounded.const 2).mul hL).add
      (((PolyBounded.const cn).mul (hL1.pow en)).add (.const 1)) |>.add (.const 2))).add (.const 4)
  have hU_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
      (fun φ => ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
        2 * ((B φ + 1) ^ ds + B φ + (φ.numVars + 2) ^ 2)) :=
    ((hL1.pow dn).add (hL1.pow di)).add ((PolyBounded.const 2).mul
      ((((hB_poly.add (.const 1)).pow ds).add hB_poly).add ((hnvP.add (.const 2)).pow 2)))
  have hV_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
      (fun φ => ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
        (B φ + 1) ^ ds + B φ + (φ.numVars + 1)) :=
    ((((hL1.pow dn).add (hL1.pow di)).add ((hB_poly.add (.const 1)).pow ds)).add hB_poly).add
      (hnvP.add (.const 1))
  obtain ⟨cU, dU, hU⟩ := hU_poly.exists_le
  obtain ⟨cV, dV, hV⟩ := hV_poly.exists_le
  have hloop_std : ComputableInO (fun φ => bfStep^[bfRounds φ] (bfInit φ)) encCNF encBf
      (fun φ => 2 ^ φ.numVars * ((encCNF φ).length + 1) ^ dU)
      (fun φ => ((encCNF φ).length + 1) ^ dV) := by
    refine hloop.mono (cU + cV + 1) (fun φ => ?_) (fun φ => ?_)
    · have hN1 : 1 ≤ 2 ^ φ.numVars := Nat.one_le_two_pow
      have h2N : bfRounds φ + 1 ≤ 2 * 2 ^ φ.numVars := by dsimp only [bfRounds]; omega
      calc ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
            (bfRounds φ + 1) * ((B φ + 1) ^ ds + B φ + ((encNat (bfRounds φ)).length + 1) ^ 2)
          ≤ 2 ^ φ.numVars * (((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
              2 * ((B φ + 1) ^ ds + B φ + (φ.numVars + 2) ^ 2)) := by
            rw [hrounds_len]
            exact (Nat.add_le_add (Nat.le_mul_of_pos_left _ hN1)
              (Nat.mul_le_mul_right _ h2N)).trans_eq (by ring)
        _ ≤ 2 ^ φ.numVars * (cU * ((encCNF φ).length + 1) ^ dU) :=
            Nat.mul_le_mul_left _ (hU φ)
        _ = cU * (2 ^ φ.numVars * ((encCNF φ).length + 1) ^ dU) := by ring
        _ ≤ (cU + cV + 1) * (2 ^ φ.numVars * ((encCNF φ).length + 1) ^ dU + 1) :=
            Nat.mul_le_mul (by omega) (Nat.le_succ _)
    · calc ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
            (B φ + 1) ^ ds + B φ + (encNat (bfRounds φ)).length
          = ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
              (B φ + 1) ^ ds + B φ + (φ.numVars + 1) := by rw [hrounds_len]
        _ ≤ cV * ((encCNF φ).length + 1) ^ dV := hV φ
        _ ≤ (cU + cV + 1) * (((encCNF φ).length + 1) ^ dV + 1) :=
            Nat.mul_le_mul (by omega) (Nat.le_succ _)
  obtain ⟨d, hsearch_inO⟩ := hloop_std.polynomial_postprocessing
    (snd (encPair encCNF encNat) encBool) (fun _ => Nat.one_le_two_pow)
  have hsearch_eq : BruteForce.search =
      Prod.snd ∘ fun φ : CNF ℕ => bfStep^[bfRounds φ] (bfInit φ) := by
    funext φ
    simp only [Function.comp_apply, hiter, BruteForce.search, bfRounds, CNF.length_distinctVars]
  refine ⟨⟨BruteForce.search, fun n => 2 ^ n, d, d, fun φ _ => BruteForce.search_eq_true_iff φ,
    fun _ => Nat.one_le_two_pow, fun _ _ => Nat.pow_le_pow_right (by decide),
    hsearch_inO.of_enc_eq fun φ => by rw [hsearch_eq]⟩, rfl, rfl⟩

/-- Recover the optimum from the list of feasibility booleans at cutoffs `0, …, m + 1`. -/
@[expose] def optimumFromDecisions (decisions : List Bool) : ℕ :=
  decisions.countP id - 1

theorem optimumFromDecisions_threshold (F : StructInstance) :
    optimumFromDecisions
      ((List.range (F.clauses.length + 2)).map fun q => decide (q ≤ F.optimum)) =
      F.optimum := by
  have hopt : F.optimum ≤ F.clauses.length := optimum_le (F.numVars, F.clauses)
  simp only [optimumFromDecisions, List.countP_map, Function.comp_def, id_eq]
  rw [countP_range_le, Nat.min_eq_right (by omega)]
  omega

@[fun_prop]
theorem computableInPolyTime_optimumFromDecisions :
    ComputableInPolyTime optimumFromDecisions (encList encBool) encNat := by
  have hcnt : ComputableInPolyTime (fun bs : List Bool => bs.countP id)
      (encList encBool) encUnary :=
    countPWithInput (encA := encBool) ComputableInPolyTime.id' (snd (encList encBool) encBool)
  exact unary_to_binary.comp (unary_sub' hcnt (const 1))

private theorem computableInPolyTime_structWorkSize :
    ComputableInPolyTime StructInstance.workSize encStructInstance encUnary := by
  have hcl := encStructInstance_clauses_polyTime ComputableInPolyTime.id'
  have hflat : ComputableInPolyTime (fun F : StructInstance => F.clauses.flatten)
      encStructInstance (encList (encPair encNat encBool)) := by
    simpa only [List.flatten_eq_flatMap] using flatMapWithInput hcl (snd _ _)
  have hvars_len : ComputableInPolyTime (fun F : StructInstance => F.clauses.vars.length)
      encStructInstance encUnary :=
    ((length_list (encPair encNat encBool)).comp hflat).of_enc_eq fun F => by
      simp only [Function.comp_apply, CNF.vars, List.length_map]
  exact unary_add' hvars_len ((length_list (encList (encPair encNat encBool))).comp hcl)

private theorem computableInPolyTime_thresholdQueries :
    ComputableInPolyTime
      (fun F : StructInstance =>
        (List.range (F.clauses.length + 2)).map fun q => thresholdToCNF ⟨F, q⟩)
      encStructInstance (encList encCNF) := by
  fun_prop

private theorem map_thresholdToCNF_eq {f : CNF ℕ → Bool} (F : StructInstance)
    (hf : ∀ q, f (thresholdToCNF ⟨F, q⟩) = true ↔ (thresholdToCNF ⟨F, q⟩).Satisfiable) :
    ((List.range (F.clauses.length + 2)).map fun q => thresholdToCNF ⟨F, q⟩).map f =
      (List.range (F.clauses.length + 2)).map fun q => decide (q ≤ F.optimum) := by
  rw [List.map_map]
  exact List.map_congr_left fun q _ => by
    rw [Function.comp_apply, Bool.eq_iff_iff, hf q, satisfiable_thresholdToCNF_iff,
      decide_eq_true_eq]

/-- **Native MAX-SAT optimization from a supplied fixed-width SAT solver (`3 ≤ k`).** -/
theorem FixedWidthSATSolver.exists_optimum_algorithm {k : ℕ} (hk : 3 ≤ k)
    (solver : FixedWidthSATSolver k) :
    ∃ d : ℕ, ComputableInO StructInstance.optimum encStructInstance encNat
      (fun F => solver.timeRate (thresholdVarBudget F.workSize) *
        ((encStructInstance F).length + 1) ^ d)
      (fun F => ((encStructInstance F).length + 1) ^ d) := by
  let encP := encPair encStructInstance encCNF
  let guard (p : StructInstance × CNF ℕ) : Bool :=
    decide (p.2.numVars ≤ thresholdVarBudget p.1.workSize)
  have hguard : ComputableInPolyTime guard encP encBool :=
    unary_le' (SAT.computableInPolyTime_numVars.comp (snd encStructInstance encCNF))
      (unary_add' (unary_mul' (const 957)
        (computableInPolyTime_structWorkSize.comp (fst encStructInstance encCNF))) (const 957))
  obtain ⟨dg, _, hguard_deg⟩ := hguard.exists_degree
  have hsolve_snd :=
    solver.computable.comp (ComputableInDegree.snd encStructInstance encCNF).inO_one
  have hite := hguard_deg.inO.ite hsolve_snd (ComputableInO.const false)
  let eMax := max dg (max solver.timeExp 1)
  let bMax := max dg (max solver.spaceExp 1)
  have henc_pow (p : StructInstance × CNF ℕ) (exp : ℕ) (hexp : exp ≤ max exp 1) :
      ((encCNF p.2).length + 1) ^ exp ≤ ((encP p).length + 1) ^ max dg (max exp 1) :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right (length_le_encPair_right _ _ p) 1) _).trans
      (Nat.pow_le_pow_right (Nat.le_add_left 1 _) (hexp.trans (le_max_right dg _)))
  have hle (p : StructInstance × CNF ℕ) (R exp : ℕ) (hR : 1 ≤ R) :
      ((encP p).length + 1) ^ dg ≤ R * ((encP p).length + 1) ^ max dg (max exp 1) ∧
        (encP p).length ≤ R * ((encP p).length + 1) ^ max dg (max exp 1) := by
    set L := (encP p).length
    have hL1 : 1 ≤ L + 1 := Nat.le_add_left 1 L
    refine ⟨(Nat.pow_le_pow_right hL1 (le_max_left _ _)).trans (Nat.le_mul_of_pos_left _ hR), ?_⟩
    have h2 := (Nat.pow_le_pow_right hL1 ((le_max_right exp 1).trans (le_max_right dg _))).trans
      (Nat.le_mul_of_pos_left _ hR)
    rw [pow_one] at h2
    omega
  have hanswer : ComputableInO
      (fun p : StructInstance × CNF ℕ => if guard p then solver.solve p.2 else false)
      encP encBool
      (fun p => solver.timeRate (thresholdVarBudget p.1.workSize) * ((encP p).length + 1) ^ eMax)
      (fun p => ((encP p).length + 1) ^ bMax) := by
    refine hite.mono 3 (fun p => ?_) (fun p => ?_)
    · obtain ⟨hdg, hL⟩ := hle p (solver.timeRate (thresholdVarBudget p.1.workSize))
        solver.timeExp (solver.one_le_timeRate _)
      dsimp only [encP, eMax] at hdg hL ⊢
      split_ifs with hg_true
      · have hmul := Nat.mul_le_mul (solver.mono_timeRate (of_decide_eq_true hg_true))
          (henc_pow p solver.timeExp (le_max_left _ 1))
        dsimp only [encP, eMax] at hmul
        omega
      · omega
    · obtain ⟨hdg, hL⟩ := hle p 1 solver.spaceExp le_rfl
      rw [one_mul] at hdg hL
      dsimp only [encP, bMax] at hdg hL ⊢
      split_ifs
      · have hpow := henc_pow p solver.spaceExp (le_max_left _ 1)
        dsimp only [encP, bMax] at hpow
        omega
      · omega
  obtain ⟨d₁, hlist⟩ := ComputableInO.polynomial_queries
    (T := fun F : StructInstance => solver.timeRate (thresholdVarBudget F.workSize))
    hanswer computableInPolyTime_thresholdQueries (fun _ => solver.one_le_timeRate _)
  obtain ⟨d₂, hpost⟩ := hlist.polynomial_postprocessing
    computableInPolyTime_optimumFromDecisions (fun _ => solver.one_le_timeRate _)
  refine ⟨d₂, hpost.of_enc_eq fun F => ?_⟩
  have hmap_eq :=
    map_thresholdToCNF_eq (f := fun φ => if guard (F, φ) then solver.solve φ else false)
      F fun q => by
      have hgq : guard (F, thresholdToCNF ⟨F, q⟩) = true :=
        decide_eq_true (numVars_thresholdToCNF_le ⟨F, q⟩)
      simp only [hgq, ↓reduceIte]
      exact solver.correct _ fun _ hcl => (length_clause_mem_thresholdToCNF ⟨F, q⟩ hcl).trans hk
  simp only [Function.comp_apply, hmap_eq, optimumFromDecisions_threshold]

/-- **Polynomial-time exact MAX-SAT optimization from a polynomial-time `k`-SAT decider (`3 ≤ k`).**
-/
theorem computableInPolyTime_optimum_of_KSAT {k : ℕ} (hk : 3 ≤ k) {solveKSAT : CNF ℕ → Bool}
    (hpoly : ComputableInPolyTime solveKSAT encCNF encBool)
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solveKSAT φ = true ↔ φ.Satisfiable)) :
    ComputableInPolyTime StructInstance.optimum encStructInstance encNat := by
  have hmap := (ComputableInPolyTime.map hpoly).comp computableInPolyTime_thresholdQueries
  refine (computableInPolyTime_optimumFromDecisions.comp hmap).of_enc_eq fun F => ?_
  have hdec := map_thresholdToCNF_eq (f := solveKSAT) F fun q =>
    hspec _ fun _ hcl => (length_clause_mem_thresholdToCNF ⟨F, q⟩ hcl).trans hk
  simp only [Function.comp_apply, hdec, optimumFromDecisions_threshold]

/-- **Class-level corollary:** if `KSAT k ∈ P encCNF` (`3 ≤ k`), then `StructInstance.optimum` is
computable in polynomial time. -/
theorem computableInPolyTime_optimum_of_KSAT_mem_P {k : ℕ} (hk : 3 ≤ k)
    (hKSAT : KSAT k ∈ P encCNF) :
    ComputableInPolyTime StructInstance.optimum encStructInstance encNat := by
  obtain ⟨solveKSAT, hpoly, hmem⟩ := hKSAT
  exact computableInPolyTime_optimum_of_KSAT hk hpoly fun φ hcl =>
    (hmem φ).symm.trans ⟨fun h => h.2, fun h => ⟨hcl, h⟩⟩

/-! ### Witness recovery by unit-clause prefix pinning and native polynomial-time optimization -/

private theorem eval_unit_clause_iff {n : ℕ} (x : BitString n) {j : ℕ} (hj : j < n) (bit : Bool) :
    Clause.eval (assignment n x) [(j, bit)] = true ↔ x ⟨j, hj⟩ = bit := by
  simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Literal.eval_mk, assignment,
    hj, ↓reduceDIte, beq_iff_eq]

private theorem le_optimum_append_iff (F : StructInstance) (acc : CNF ℕ) :
    acc.length + F.optimum ≤ (StructInstance.mk F.numVars (acc ++ F.clauses)).optimum ↔
      ∃ x : BitString F.numVars, F.score x = F.optimum ∧
        ∀ c ∈ acc, Clause.eval (assignment F.numVars x) c = true := by
  change _ ≤ optimum (F.numVars, acc ++ F.clauses) ↔ _
  rw [← thresholdCount_pos_iff_le_optimum, thresholdCount_pos_iff]
  refine exists_congr fun x => ?_
  have hscore : score (F.numVars, acc ++ F.clauses) x =
      acc.countP (Clause.eval (assignment F.numVars x)) + F.score x := by
    simp only [StructInstance.score, score, StructInstance.toPair, List.countP_append]
  have hle_acc : acc.countP (Clause.eval (assignment F.numVars x)) ≤ acc.length :=
    List.countP_le_length
  have hle_opt : F.score x ≤ F.optimum := score_le_optimum F.toPair x
  rw [hscore]
  exact ⟨fun h => ⟨by omega, List.countP_eq_length.mp (by omega)⟩,
    fun ⟨hopt, hall⟩ => by rw [List.countP_eq_length.mpr hall, hopt]⟩

/-- Unit-clause list pinning variables `0, …, bits.length - 1` to the entries of `bits`. -/
private def pinnedClauses (bits : List Bool) : CNF ℕ :=
  bits.zipIdx.map fun p => [(p.2, p.1)]

private theorem length_pinnedClauses (bits : List Bool) :
    (pinnedClauses bits).length = bits.length := by
  simp [pinnedClauses]

attribute [local simp] length_pinnedClauses

private theorem length_vars_pinnedClauses (bits : List Bool) :
    (pinnedClauses bits).vars.length = bits.length := by
  simp [pinnedClauses, CNF.vars, Function.comp_def]

private theorem eval_pinnedClauses_iff {n : ℕ} (x : BitString n) {bits : List Bool}
    (hbits : bits.length ≤ n) :
    (∀ c ∈ pinnedClauses bits, Clause.eval (assignment n x) c = true) ↔
      ∀ j (hj : j < bits.length), x ⟨j, hj.trans_le hbits⟩ = bits[j] := by
  constructor
  · intro hall j hj
    have hlen : j < (pinnedClauses bits).length := by simpa using hj
    have hmem : (pinnedClauses bits)[j] ∈ pinnedClauses bits := List.getElem_mem hlen
    have heq : (pinnedClauses bits)[j] = [(j, bits[j])] := by simp [pinnedClauses]
    exact (eval_unit_clause_iff x (hj.trans_le hbits) bits[j]).mp (heq ▸ hall _ hmem)
  · intro hx c hc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    have hj' : j < bits.length := by simpa using hj
    have heq : (pinnedClauses bits)[j] = [(j, bits[j])] := by simp [pinnedClauses]
    rw [heq]
    exact (eval_unit_clause_iff x (hj'.trans_le hbits) bits[j]).mpr (hx j hj')

private theorem eval_pinnedClauses_append_singleton {n : ℕ} (x : BitString n)
    {bits : List Bool} (bit : Bool) (hbits : bits.length < n) :
    (∀ c ∈ pinnedClauses (bits ++ [bit]), Clause.eval (assignment n x) c = true) ↔
      (∀ c ∈ pinnedClauses bits, Clause.eval (assignment n x) c = true) ∧
        x ⟨bits.length, hbits⟩ = bit := by
  rw [eval_pinnedClauses_iff x (by simp; omega), eval_pinnedClauses_iff x hbits.le]
  constructor
  · intro hall
    refine ⟨fun j hj => ?_, ?_⟩
    · have h := hall j (by simp; omega)
      simpa [List.getElem_append_left hj] using h
    · have h := hall bits.length (by simp)
      simpa [List.getElem_append_right (le_refl bits.length)] using h
  · rintro ⟨hprev, hlast⟩ j hj
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
    · simpa [List.getElem_append_left hlt] using hprev j hlt
    · simpa [List.getElem_append_right (le_refl bits.length)] using hlast

/-- Single step of unit-clause prefix pinning on `(F, opt)`: extend `bits` at variable
`bits.length` with `true` if `thresholdToCNF` remains satisfiable at cutoff
`(bits.length + 1) + opt`, and `false` otherwise. -/
private def StructInstance.recoverStep (F : StructInstance) (solve : CNF ℕ → Bool) (opt : ℕ)
    (bits : List Bool) : List Bool :=
  let cand := pinnedClauses (bits ++ [true])
  let b := solve (thresholdToCNF ⟨⟨F.numVars, cand ++ F.clauses⟩, cand.length + opt⟩)
  bits ++ [b]

/-- Recover `F.numVars` assignment bits at target optimum `opt` using `solve`. -/
private def StructInstance.recoverBits (F : StructInstance) (solve : CNF ℕ → Bool) (opt : ℕ) :
    List Bool :=
  (F.recoverStep solve opt)^[F.numVars] []

private theorem StructInstance.length_iterate_recoverStep (F : StructInstance)
    (solve : CNF ℕ → Bool) (opt i : ℕ) (bits : List Bool) :
    ((F.recoverStep solve opt)^[i] bits).length = bits.length + i := by
  induction i generalizing bits with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [StructInstance.recoverStep, List.length_append, List.length_singleton]
    omega

private theorem StructInstance.length_recoverBits (F : StructInstance) (solve : CNF ℕ → Bool)
    (opt : ℕ) :
    (F.recoverBits solve opt).length = F.numVars := by
  simp [StructInstance.recoverBits, StructInstance.length_iterate_recoverStep]

/-- Correctness of `StructInstance.recoverBits`: at `opt = F.optimum`, `F.recoverBits solve opt`
returns an `F.numVars`-bit list achieving `F.score (BitString.ofList F.numVars ...) = F.optimum`
for any `k`-SAT decider (`3 ≤ k`). -/
private theorem StructInstance.recoverBits_score_eq_optimum {k : ℕ} (hk : 3 ≤ k)
    {solve : CNF ℕ → Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable))
    (F : StructInstance) :
    F.score (BitString.ofList F.numVars (F.recoverBits solve F.optimum)) = F.optimum := by
  have hstep_inv : ∀ (bits : List Bool), bits.length < F.numVars →
      (∃ x : BitString F.numVars, F.score x = F.optimum ∧
        ∀ c ∈ pinnedClauses bits, Clause.eval (assignment F.numVars x) c = true) →
      ∃ x : BitString F.numVars, F.score x = F.optimum ∧
        ∀ c ∈ pinnedClauses (F.recoverStep solve F.optimum bits),
          Clause.eval (assignment F.numVars x) c = true := by
    intro bits hlt hinv
    let cand := pinnedClauses (bits ++ [true])
    have hprobe : solve (thresholdToCNF ⟨⟨F.numVars, cand ++ F.clauses⟩, cand.length + F.optimum⟩) =
        true ↔ ∃ x : BitString F.numVars, F.score x = F.optimum ∧
          ∀ c ∈ cand, Clause.eval (assignment F.numVars x) c = true := by
      rw [hspec _ (fun _ hcl => (length_clause_mem_thresholdToCNF _ hcl).trans hk),
        satisfiable_thresholdToCNF_iff]
      exact le_optimum_append_iff F cand
    simp only [StructInstance.recoverStep]
    set b := solve (thresholdToCNF ⟨⟨F.numVars, cand ++ F.clauses⟩, cand.length + F.optimum⟩)
    cases hb : b
    · obtain ⟨x, hx_opt, hx_bits⟩ := hinv
      have hfalse : x ⟨bits.length, hlt⟩ = false :=
        Bool.eq_false_iff.mpr fun hx_true =>
          Bool.noConfusion (hb.symm.trans (hprobe.mpr ⟨x, hx_opt,
            (eval_pinnedClauses_append_singleton x true hlt).mpr ⟨hx_bits, hx_true⟩⟩))
      exact ⟨x, hx_opt, (eval_pinnedClauses_append_singleton x false hlt).mpr ⟨hx_bits, hfalse⟩⟩
    · exact hprobe.mp hb
  have hiter_inv : ∀ i ≤ F.numVars,
      ∃ x : BitString F.numVars, F.score x = F.optimum ∧
        ∀ c ∈ pinnedClauses ((F.recoverStep solve F.optimum)^[i] []),
          Clause.eval (assignment F.numVars x) c = true := by
    intro i hi
    induction i with
    | zero =>
      obtain ⟨xStar, hxStar⟩ := exists_score_eq_optimum F.toPair
      exact ⟨xStar, hxStar, fun _ hc => by simp [pinnedClauses] at hc⟩
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact hstep_inv _ (by simp [StructInstance.length_iterate_recoverStep]; omega) (ih (by omega))
  obtain ⟨x, hx_opt, hx_all⟩ := hiter_inv F.numVars le_rfl
  have hlen : (F.recoverBits solve F.optimum).length = F.numVars :=
    F.length_recoverBits solve F.optimum
  have hall := (eval_pinnedClauses_iff x hlen.le).mp hx_all
  have hxeq : BitString.ofList F.numVars (F.recoverBits solve F.optimum) = x := by
    funext j
    have hj : j.val < (F.recoverBits solve F.optimum).length := by rw [hlen]; exact j.isLt
    simp only [BitString.ofList, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj, Option.getD_some]
    simpa using (hall j.val hj).symm
  rw [hxeq, hx_opt]

/-- Native MAX-SAT optimization with witness recovery from a supplied SAT decider `solve`: computes
`opt` from the `m + 2` threshold queries and recovers `F.numVars` assignment bits by unit-clause
prefix pinning. -/
def optimizeWith (solve : CNF ℕ → Bool) (F : StructInstance) : StructSolution :=
  let opt := optimumFromDecisions
    (((List.range (F.clauses.length + 2)).map fun q => thresholdToCNF ⟨F, q⟩).map solve)
  ⟨opt, F.recoverBits solve opt⟩

/-- **Correctness of `optimizeWith`:** for any `k`-SAT decider (`3 ≤ k`), `optimizeWith solve F`
returns `optValue = F.optimum` and an `F.numVars`-bit list scoring `F.optimum`. -/
theorem optimizeWith_spec {k : ℕ} (hk : 3 ≤ k) {solve : CNF ℕ → Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable))
    (F : StructInstance) :
    (optimizeWith solve F).optValue = F.optimum ∧
      (optimizeWith solve F).assignmentBits.length = F.numVars ∧
      F.score (BitString.ofList F.numVars (optimizeWith solve F).assignmentBits) = F.optimum := by
  have hdec := map_thresholdToCNF_eq (f := solve) F fun q =>
    hspec _ fun _ hcl => (length_clause_mem_thresholdToCNF ⟨F, q⟩ hcl).trans hk
  have hopt : optimumFromDecisions
      (((List.range (F.clauses.length + 2)).map fun q => thresholdToCNF ⟨F, q⟩).map solve) =
      F.optimum := by
    rw [hdec, optimumFromDecisions_threshold]
  simp only [optimizeWith, hopt, StructInstance.length_recoverBits, true_and]
  exact F.recoverBits_score_eq_optimum hk hspec

@[fun_prop]
private theorem computableInPolyTime_pinnedClauses :
    ComputableInPolyTime pinnedClauses encBits encCNF :=
  (ComputableInPolyTime.map
    (by fun_prop : ComputableInPolyTime (fun p : Bool × ℕ => ([(p.2, p.1)] : Clause ℕ))
      (encPair encBool encUnary) (encList (encPair encNat encBool)))).comp
    ((zipIdx encBool).comp (bits_encList_polyTime encBool).1)

private theorem computableInPolyTime_structRecoverStep {solve : CNF ℕ → Bool}
    (hpoly : ComputableInPolyTime solve encCNF encBool) :
    ComputableInPolyTime
      (fun p : (StructInstance × ℕ) × List Bool => p.1.1.recoverStep solve p.1.2 p.2)
      (encPair (encPair encStructInstance encUnary) encBits) encBits := by
  let encPar := encPair encStructInstance encUnary
  have hF := (fst encStructInstance encUnary).comp (fst encPar encBits)
  have hopt := (snd encStructInstance encUnary).comp (fst encPar encBits)
  have hbits := snd encPar encBits
  have hcand := computableInPolyTime_pinnedClauses.comp (bitsAppend hbits (const [true]))
  have hq := computableInPolyTime_thresholdToCNF.comp (encThresholdQuery_mk_polyTime
    (encStructInstance_mk_polyTime (encStructInstance_numVars_polyTime hF)
      (listAppend' hcand (encStructInstance_clauses_polyTime hF)))
    (unary_add' ((length_list (encList (encPair encNat encBool))).comp hcand) hopt))
  exact bitsAppend hbits
    ((of_finite (fun bit : Bool => [bit]) (encIn := encBool) (encOut := encBits)).comp
      (hpoly.comp hq))

/-- **Polynomial-time closure for `optimizeWith`:** for any polynomial-time procedure `solve`,
`optimizeWith solve` runs in polynomial time on multi-tape Turing machines (and when `solve`
decides `k`-SAT for `3 ≤ k`, `optimizeWith_spec` certifies exact optimality of both the returned
value and witness assignment). -/
theorem computableInPolyTime_optimizeWith {solve : CNF ℕ → Bool}
    (hpoly : ComputableInPolyTime solve encCNF encBool) :
    ComputableInPolyTime (optimizeWith solve) encStructInstance encStructSolution := by
  let optFn (F : StructInstance) : ℕ :=
    optimumFromDecisions
      (((List.range (F.clauses.length + 2)).map fun q => thresholdToCNF ⟨F, q⟩).map solve)
  have hmap := (ComputableInPolyTime.map hpoly).comp computableInPolyTime_thresholdQueries
  have hcnt : ComputableInPolyTime (fun bs : List Bool => bs.countP id)
      (encList encBool) encUnary :=
    countPWithInput (encA := encBool) ComputableInPolyTime.id' (snd (encList encBool) encBool)
  have hoptU : ComputableInPolyTime optFn encStructInstance encUnary :=
    (unary_sub' hcnt (const 1)).comp hmap
  have hnv : ComputableInPolyTime StructInstance.numVars encStructInstance encUnary :=
    encStructInstance_numVars_polyTime ComputableInPolyTime.id'
  have hrec : ComputableInPolyTime (fun F : StructInstance => F.recoverBits solve (optFn F))
      encStructInstance encBits :=
    iterateWith (par := fun F : StructInstance => (F, optFn F))
      (count := StructInstance.numVars) (init := fun _ => ([] : List Bool))
      (step := fun p bits => p.1.recoverStep solve p.2 bits)
      (ComputableInPolyTime.id'.prod hoptU) hnv (const [])
      (computableInPolyTime_structRecoverStep hpoly) hnv.polyBounded
      (fun F i hi => by simp [encBits_apply, StructInstance.length_iterate_recoverStep, hi])
  exact encStructSolution_mk_polyTime (unary_to_binary.comp hoptU) hrec

/-- **Class-level MAX-SAT witness optimization:** if `KSAT k ∈ P encCNF` (`3 ≤ k`), then both the
exact MAX-SAT optimum and an optimal `F.numVars`-bit assignment are computable in polynomial time
on multi-tape Turing machines. -/
theorem exists_computableInPolyTime_optimize_of_KSAT_mem_P {k : ℕ} (hk : 3 ≤ k)
    (hKSAT : KSAT k ∈ P encCNF) :
    ∃ solveOpt : StructInstance → StructSolution,
      ComputableInPolyTime solveOpt encStructInstance encStructSolution ∧
      ∀ F : StructInstance,
        (solveOpt F).optValue = F.optimum ∧
        (solveOpt F).assignmentBits.length = F.numVars ∧
        F.score (BitString.ofList F.numVars (solveOpt F).assignmentBits) = F.optimum := by
  obtain ⟨solveKSAT, hpoly, hmem⟩ := hKSAT
  have hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solveKSAT φ = true ↔ φ.Satisfiable) :=
    fun φ hcl => (hmem φ).symm.trans ⟨fun h => h.2, fun h => ⟨hcl, h⟩⟩
  exact ⟨optimizeWith solveKSAT, computableInPolyTime_optimizeWith hpoly,
    optimizeWith_spec hk hspec⟩

/-! ### `O(log m)`-query `FreeM SATQuery` binary search and sparse-subsampling transfer -/

/-- Query signature for a supplied propositional SAT oracle on `CNF ℕ`. -/
inductive SATQuery : Type → Type where
  /-- Test satisfiability of `φ : CNF ℕ`. -/
  | sat (φ : CNF ℕ) : SATQuery Bool

/-- Lift `SATQuery.sat φ` into `FreeM SATQuery Bool`. -/
abbrev SATQuery.ask (φ : CNF ℕ) : FreeM SATQuery Bool :=
  FreeM.lift (.sat φ)

@[simp]
theorem SATQuery.eval_ask (oracle : {ι : Type} → SATQuery ι → ι) (φ : CNF ℕ) :
    (SATQuery.ask φ).eval oracle = oracle (.sat φ) := rfl

/-- Build a `SATQuery` oracle from a pure solver `CNF ℕ → Bool`. -/
@[expose] def SATQuery.oracleOf (solve : CNF ℕ → Bool) :
    {ι : Type} → SATQuery ι → ι
  | _, .sat φ => solve φ

@[simp]
theorem SATQuery.oracleOf_sat (solve : CNF ℕ → Bool) (φ : CNF ℕ) :
    SATQuery.oracleOf solve (.sat φ) = solve φ := rfl

/-- Pure exact MAX-SAT optimization by binary search on `[1, m + 1)` using a supplied `k`-SAT
solver `solve : CNF ℕ → Bool`. -/
def optimumByBinarySearch (solve : CNF ℕ → Bool) (F : StructInstance) : ℕ :=
  lowerBound (fun q => solve (thresholdToCNF ⟨F, q⟩)) 1 (F.clauses.length + 1) - 1

/-- `FreeM SATQuery` binary-search program finding `F.optimum` on `[1, m + 1)`. -/
def optimumByBinarySearchQ (F : StructInstance) : FreeM SATQuery ℕ := do
  let k ← lowerBoundBy (fun q => SATQuery.ask (thresholdToCNF ⟨F, q⟩)) 1 (F.clauses.length + 1)
  pure (k - 1)

@[simp]
theorem eval_optimumByBinarySearchQ (oracle : {ι : Type} → SATQuery ι → ι) (F : StructInstance) :
    (optimumByBinarySearchQ F).eval oracle =
      optimumByBinarySearch (fun φ => oracle (.sat φ)) F := by
  simp [optimumByBinarySearchQ, optimumByBinarySearch]

/-- **Correctness of binary-search optimization:** for any `k`-SAT solver (`3 ≤ k`),
`optimumByBinarySearch solve F = F.optimum`. -/
theorem optimumByBinarySearch_eq_optimum {k : ℕ} (hk : 3 ≤ k) {solve : CNF ℕ → Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable))
    (F : StructInstance) :
    optimumByBinarySearch solve F = F.optimum := by
  let probe (q : ℕ) : Bool := solve (thresholdToCNF ⟨F, q⟩)
  have hprobe (q : ℕ) : probe q = true ↔ q ≤ F.optimum := by
    rw [hspec _ (fun _ hcl => (length_clause_mem_thresholdToCNF ⟨F, q⟩ hcl).trans hk),
      satisfiable_thresholdToCNF_iff]
  have hmono : ∀ m m', 1 ≤ m → m ≤ m' → m' < F.clauses.length + 1 →
      probe m' = true → probe m = true := by
    intro m m' _ hmm' _ hm'
    exact (hprobe m).mpr (hmm'.trans ((hprobe m').mp hm'))
  obtain ⟨hlo, hhi, htrue, hfalse⟩ :=
    lowerBound_spec probe (lo := 1) (hi := F.clauses.length + 1) hmono
  have hopt_le : F.optimum ≤ F.clauses.length := optimum_le (F.numVars, F.clauses)
  dsimp only [optimumByBinarySearch]
  set r := lowerBound probe 1 (F.clauses.length + 1)
  have hnot_of_false {q : ℕ} (hqr : r ≤ q) (hqm : q < F.clauses.length + 1) : ¬ q ≤ F.optimum :=
    fun h => by
      have hf := hfalse q hqr hqm
      rw [(hprobe q).mpr h] at hf
      exact Bool.noConfusion hf
  by_cases hr1 : r = 1
  · rcases Nat.eq_zero_or_pos F.clauses.length with hm0 | hmpos
    · omega
    · have := hnot_of_false (q := 1) (by omega) (by omega); omega
  · have hge : r - 1 ≤ F.optimum := (hprobe (r - 1)).mp (htrue (r - 1) (by omega) (by omega))
    by_cases hrm : r = F.clauses.length + 1
    · omega
    · have := hnot_of_false (q := r) le_rfl (by omega); omega

/-- **Weighted query-cost bound for `optimumByBinarySearchQ`:** if every 3-CNF of at most
`thresholdVarBudget F.workSize` variables has weight at most `C`, then `optimumByBinarySearchQ F`
incurs cost at most `C * (Nat.log 2 F.clauses.length + 1)`. -/
theorem cost_optimumByBinarySearchQ_le (oracle : {ι : Type} → SATQuery ι → ι)
    (weight : {ι : Type} → SATQuery ι → ℕ) (F : StructInstance) {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) → φ.numVars ≤ thresholdVarBudget F.workSize →
      weight (.sat φ) ≤ C) :
    (optimumByBinarySearchQ F).cost oracle weight ≤ C * (Nat.log 2 F.clauses.length + 1) := by
  simp only [optimumByBinarySearchQ, FreeM.cost_bind, FreeM.cost_pure, add_zero]
  have h := cost_lowerBoundBy_le oracle weight (fun q => SATQuery.ask (thresholdToCNF ⟨F, q⟩))
    (c := C) (lo := 1) (hi := F.clauses.length + 1) fun q _ _ => by
      simpa only [FreeM.cost_lift] using
        hcost _ (fun _ hcl => length_clause_mem_thresholdToCNF ⟨F, q⟩ hcl)
          (numVars_thresholdToCNF_le ⟨F, q⟩)
  simpa only [Nat.add_sub_cancel_right] using h

/-- **Query-count bound for `optimumByBinarySearchQ`:** makes at most
`Nat.log 2 F.clauses.length + 1` SAT queries against any oracle (`0` when `F.clauses = []`). -/
theorem countQueries_optimumByBinarySearchQ_le (oracle : {ι : Type} → SATQuery ι → ι)
    (F : StructInstance) :
    (optimumByBinarySearchQ F).countQueries oracle ≤ Nat.log 2 F.clauses.length + 1 := by
  simpa only [FreeM.countQueries_eq_cost_one, one_mul] using
    cost_optimumByBinarySearchQ_le oracle (fun _ => 1) F (C := 1) fun _ _ _ => le_rfl

/-- On an instance with no clauses, `optimumByBinarySearchQ` makes zero SAT queries. -/
theorem countQueries_optimumByBinarySearchQ_of_clauses_eq_nil
    (oracle : {ι : Type} → SATQuery ι → ι) {F : StructInstance} (hF : F.clauses = []) :
    (optimumByBinarySearchQ F).countQueries oracle = 0 := by
  simp only [optimumByBinarySearchQ, hF, List.length_nil, FreeM.countQueries_eq_cost_one,
    FreeM.cost_bind, FreeM.cost_pure, add_zero]
  exact cost_lowerBoundBy_of_le oracle (fun _ => 1) _ le_rfl

/-- **End-to-end subsampled sparse MAX-`w`-SAT optimization via a supplied fixed-width SAT oracle.**
Drawing `s` clauses uniformly from `F` (`0 < F.clauses.length`, clause width `≤ w`) and running
`optimumByBinarySearchQ (F.sample ω)` against `SATQuery.oracleOf solve` (`3 ≤ k`):
1. queries `solve` only on 3-CNFs of at most `thresholdVarBudget ((w + 1) * s)` variables, within
   weighted query cost `C * (Nat.log 2 s + 1)` whenever `weight (.sat φ) ≤ C` on such formulas; and
2. with probability at least `1 - 2 ^ (F.numVars + 1) * exp (-2 * s * δ ^ 2)`, estimates `F.optimum`
   within `δ * m` after `(m / s)` rescaling and certifies `2 * δ * m` optimality loss for every
   sampled maximizer. -/
theorem sample_optimumByBinarySearch_spec {k w : ℕ} (hk : 3 ≤ k)
    {solve : CNF ℕ → Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable))
    {F : StructInstance} (hm : 0 < F.clauses.length) (hw : ∀ c ∈ F.clauses, c.length ≤ w)
    (s : ℕ) {weight : {ι : Type} → SATQuery ι → ℕ} {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget ((w + 1) * s) → weight (.sat φ) ≤ C)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ ω : Fin s → Fin F.clauses.length,
      (optimumByBinarySearchQ (F.sample ω)).cost (SATQuery.oracleOf solve) weight ≤
        C * (Nat.log 2 s + 1)) ∧
    1 - 2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (∀ xHat : BitString F.numVars,
            (∀ x, (F.sample ω).score x ≤ (F.sample ω).score xHat) →
              (F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * (F.clauses.length : ℝ)) ∧
          |(F.clauses.length : ℝ) / (s : ℝ) *
              (optimumByBinarySearch solve (F.sample ω) : ℝ) -
            (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}).toReal := by
  refine ⟨fun ω => ?_, ?_⟩
  · simpa only [StructInstance.sample, List.length_ofFn] using
      cost_optimumByBinarySearchQ_le (SATQuery.oracleOf solve) weight (F.sample ω) (C := C)
        fun φ h3 hvars =>
          hcost φ h3 (hvars.trans (thresholdVarBudget_mono (F.workSize_sample_le_of_width hw ω)))
  · simp_rw [fun ω : Fin s → Fin F.clauses.length =>
      optimumByBinarySearch_eq_optimum hk hspec (F.sample ω)]
    exact F.one_sub_le_sample_good hm s hδ

/-- `FreeM SATQuery` loop executing `rem` steps of unit-clause prefix pinning from `bits`. -/
private def recoverLoopQ (F : StructInstance) (opt : ℕ) :
    ℕ → List Bool → FreeM SATQuery (List Bool)
  | 0, bits => pure bits
  | rem + 1, bits => do
    let cand := pinnedClauses (bits ++ [true])
    let b ← SATQuery.ask (thresholdToCNF ⟨⟨F.numVars, cand ++ F.clauses⟩, cand.length + opt⟩)
    recoverLoopQ F opt rem (bits ++ [b])

private theorem eval_recoverLoopQ (oracle : {ι : Type} → SATQuery ι → ι) (F : StructInstance)
    (opt rem : ℕ) (bits : List Bool) :
    (recoverLoopQ F opt rem bits).eval oracle =
      (F.recoverStep (fun φ => oracle (.sat φ)) opt)^[rem] bits := by
  induction rem generalizing bits with
  | zero => rfl
  | succ rem ih =>
    simp only [recoverLoopQ, FreeM.eval_bind, SATQuery.eval_ask, ih,
      Function.iterate_succ_apply, StructInstance.recoverStep]

private theorem cost_recoverLoopQ_le (oracle : {ι : Type} → SATQuery ι → ι)
    (weight : {ι : Type} → SATQuery ι → ℕ) (F : StructInstance) (opt : ℕ) {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget (F.workSize + 2 * F.numVars) → weight (.sat φ) ≤ C)
    {rem : ℕ} (bits : List Bool) (hrem : bits.length + rem ≤ F.numVars) :
    (recoverLoopQ F opt rem bits).cost oracle weight ≤ C * rem := by
  induction rem generalizing bits with
  | zero => simp [recoverLoopQ]
  | succ rem ih =>
    let cand := pinnedClauses (bits ++ [true])
    let q : ThresholdQuery := ⟨⟨F.numVars, cand ++ F.clauses⟩, cand.length + opt⟩
    have hcand_len : cand.length = bits.length + 1 := by simp [cand]
    have hcand_vars : cand.vars.length = bits.length + 1 := by
      simpa [cand] using length_vars_pinnedClauses (bits ++ [true])
    have hws_q : q.workSize ≤ F.workSize + 2 * F.numVars := by
      simp only [ThresholdQuery.workSize, StructInstance.workSize, MaxSAT.workSize,
        StructInstance.toPair, CNF.vars, List.flatten_append, List.map_append,
        List.length_append, q] at hcand_len hcand_vars ⊢
      omega
    have hstep : weight (.sat (thresholdToCNF q)) ≤ C :=
      hcost _ (fun _ hcl => length_clause_mem_thresholdToCNF q hcl)
        ((numVars_thresholdToCNF_le q).trans (thresholdVarBudget_mono hws_q))
    dsimp only [q, cand] at hstep
    simp only [recoverLoopQ, FreeM.cost_bind, FreeM.cost_lift, SATQuery.eval_ask]
    set b := oracle (.sat (thresholdToCNF
      ⟨⟨F.numVars, (pinnedClauses (bits ++ [true])) ++ F.clauses⟩,
        (pinnedClauses (bits ++ [true])).length + opt⟩))
    have hrec := ih (bits ++ [b]) (by simp; omega)
    rw [Nat.mul_succ]
    omega

/-- Pure exact MAX-SAT optimization with witness recovery: finds `opt = F.optimum` by bisection and
constructs an `F.numVars`-bit assignment achieving `F.score ... = F.optimum` by unit-clause prefix
pinning. -/
def optimizeByBinarySearch (solve : CNF ℕ → Bool) (F : StructInstance) : StructSolution :=
  let opt := optimumByBinarySearch solve F
  ⟨opt, F.recoverBits solve opt⟩

/-- `FreeM SATQuery` program finding `F.optimum` and an optimal `F.numVars`-bit assignment
(`StructSolution`) using at most `⌊log₂ m⌋ + 1 + n` SAT queries. -/
def optimizeByBinarySearchQ (F : StructInstance) : FreeM SATQuery StructSolution := do
  let opt ← optimumByBinarySearchQ F
  let bits ← recoverLoopQ F opt F.numVars []
  pure ⟨opt, bits⟩

@[simp]
theorem eval_optimizeByBinarySearchQ (oracle : {ι : Type} → SATQuery ι → ι) (F : StructInstance) :
    (optimizeByBinarySearchQ F).eval oracle =
      optimizeByBinarySearch (fun φ => oracle (.sat φ)) F := by
  simp [optimizeByBinarySearchQ, optimizeByBinarySearch, eval_recoverLoopQ,
    StructInstance.recoverBits]

/-- **Correctness of `optimizeByBinarySearch`:** returns `optValue = F.optimum` and an
`F.numVars`-bit list scoring `F.optimum` (`3 ≤ k`). -/
theorem optimizeByBinarySearch_spec {k : ℕ} (hk : 3 ≤ k) {solve : CNF ℕ → Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable))
    (F : StructInstance) :
    (optimizeByBinarySearch solve F).optValue = F.optimum ∧
      (optimizeByBinarySearch solve F).assignmentBits.length = F.numVars ∧
      F.score (BitString.ofList F.numVars (optimizeByBinarySearch solve F).assignmentBits) =
        F.optimum := by
  simp only [optimizeByBinarySearch, optimumByBinarySearch_eq_optimum hk hspec F,
    StructInstance.length_recoverBits, true_and]
  exact F.recoverBits_score_eq_optimum hk hspec

/-- **Weighted query-cost bound for `optimizeByBinarySearchQ`:** at most
`C * (Nat.log 2 F.clauses.length + 1 + F.numVars)` cost when every 3-CNF of at most
`thresholdVarBudget (F.workSize + 2 * F.numVars)` variables has weight at most `C`. -/
theorem cost_optimizeByBinarySearchQ_le (oracle : {ι : Type} → SATQuery ι → ι)
    (weight : {ι : Type} → SATQuery ι → ℕ) (F : StructInstance) {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget (F.workSize + 2 * F.numVars) → weight (.sat φ) ≤ C) :
    (optimizeByBinarySearchQ F).cost oracle weight ≤
      C * (Nat.log 2 F.clauses.length + 1 + F.numVars) := by
  simp only [optimizeByBinarySearchQ, FreeM.cost_bind, FreeM.cost_pure, add_zero]
  have ht1 := cost_optimumByBinarySearchQ_le oracle weight F (C := C) fun φ h3 hnv =>
    hcost φ h3 (hnv.trans (thresholdVarBudget_mono (Nat.le_add_right _ _)))
  have ht2 := cost_recoverLoopQ_le oracle weight F ((optimumByBinarySearchQ F).eval oracle) hcost
    (rem := F.numVars) [] (by simp)
  rw [Nat.mul_add]
  omega

/-- **Query-count bound for `optimizeByBinarySearchQ`:** makes at most
`Nat.log 2 F.clauses.length + 1 + F.numVars` SAT queries against any oracle. -/
theorem countQueries_optimizeByBinarySearchQ_le (oracle : {ι : Type} → SATQuery ι → ι)
    (F : StructInstance) :
    (optimizeByBinarySearchQ F).countQueries oracle ≤
      Nat.log 2 F.clauses.length + 1 + F.numVars := by
  simpa only [FreeM.countQueries_eq_cost_one, one_mul] using
    cost_optimizeByBinarySearchQ_le oracle (fun _ => 1) F (C := 1) fun _ _ _ => le_rfl

/-- **Sample-optimization reduction with witness recovery (`3 ≤ k`):** on an `s`-clause subsample of
a width-`w` instance `F`, `optimizeByBinarySearchQ (F.sample ω)` queries `solve` only on 3-CNFs of
at most `thresholdVarBudget ((w + 1) * s + 2 * F.numVars)` variables within weighted cost
`C * (Nat.log 2 s + 1 + F.numVars)` (and `≤ Nat.log 2 s + 1 + F.numVars` queries), and with
probability at least `1 - 2 ^ (F.numVars + 1) * exp (-2 * s * δ ^ 2)` the returned witness
`sol := optimizeByBinarySearch solve (F.sample ω)` estimates `F.optimum` within `δ * m` (after
`(m / s)` rescaling) and satisfies
`(F.optimum : ℝ) - (F.score (BitString.ofList F.numVars sol.assignmentBits) : ℝ) ≤ 2 * δ * m`. -/
theorem sample_optimizeByBinarySearch_spec {k w : ℕ} (hk : 3 ≤ k)
    {solve : CNF ℕ → Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable))
    {F : StructInstance} (hm : 0 < F.clauses.length) (hw : ∀ c ∈ F.clauses, c.length ≤ w)
    (s : ℕ) {weight : {ι : Type} → SATQuery ι → ℕ} {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget ((w + 1) * s + 2 * F.numVars) → weight (.sat φ) ≤ C)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ ω : Fin s → Fin F.clauses.length,
      (optimizeByBinarySearchQ (F.sample ω)).cost (SATQuery.oracleOf solve) weight ≤
        C * (Nat.log 2 s + 1 + F.numVars)) ∧
    1 - 2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (F.optimum : ℝ) -
              (F.score (BitString.ofList F.numVars
                (optimizeByBinarySearch solve (F.sample ω)).assignmentBits) : ℝ) ≤
              2 * δ * (F.clauses.length : ℝ) ∧
          |(F.clauses.length : ℝ) / (s : ℝ) *
              ((optimizeByBinarySearch solve (F.sample ω)).optValue : ℝ) -
            (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}).toReal := by
  refine ⟨fun ω => ?_, (F.one_sub_le_sample_good hm s hδ).trans
    (Cslib.Probability.PMF.toOuterMeasure_toReal_mono (F.samplePMF hm s) fun ω hω => ?_)⟩
  · simpa only [StructInstance.sample, List.length_ofFn] using
      cost_optimizeByBinarySearchQ_le (SATQuery.oracleOf solve) weight (F.sample ω) (C := C)
        fun φ h3 hnv => hcost φ h3 <| hnv.trans
          (thresholdVarBudget_mono (Nat.add_le_add_right (F.workSize_sample_le_of_width hw ω) _))
  · obtain ⟨hopt_ret, _, hscore_ret⟩ := optimizeByBinarySearch_spec hk hspec (F.sample ω)
    refine ⟨hω.1 _ fun x => ?_, ?_⟩
    · change (F.sample ω).score x ≤
        (F.sample ω).score
          (BitString.ofList (F.sample ω).numVars
            (optimizeByBinarySearch solve (F.sample ω)).assignmentBits)
      rw [hscore_ret]; exact score_le_optimum (F.sample ω).toPair x
    · rw [hopt_ret]; exact hω.2

/-- **Sample-optimization reduction with witness recovery under the `η` sample-size condition:**
when `0 < η` and `(F.numVars + 1) * log 2 + log (1 / η) ≤ 2 * s * δ ^ 2`,
`optimizeByBinarySearch solve (F.sample ω)` succeeds with probability at least `1 - η`. -/
theorem sample_optimizeByBinarySearch_spec_of_sample_size {k w : ℕ} (hk : 3 ≤ k)
    {solve : CNF ℕ → Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable))
    {F : StructInstance} (hm : 0 < F.clauses.length) (hw : ∀ c ∈ F.clauses, c.length ≤ w)
    {s : ℕ} {weight : {ι : Type} → SATQuery ι → ℕ} {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget ((w + 1) * s + 2 * F.numVars) → weight (.sat φ) ≤ C)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η)
    (hs : (F.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    (∀ ω : Fin s → Fin F.clauses.length,
      (optimizeByBinarySearchQ (F.sample ω)).cost (SATQuery.oracleOf solve) weight ≤
        C * (Nat.log 2 s + 1 + F.numVars)) ∧
    1 - η ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (F.optimum : ℝ) -
              (F.score (BitString.ofList F.numVars
                (optimizeByBinarySearch solve (F.sample ω)).assignmentBits) : ℝ) ≤
              2 * δ * (F.clauses.length : ℝ) ∧
          |(F.clauses.length : ℝ) / (s : ℝ) *
              ((optimizeByBinarySearch solve (F.sample ω)).optValue : ℝ) -
            (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}).toReal := by
  obtain ⟨ht, hprob⟩ := sample_optimizeByBinarySearch_spec hk hspec hm hw s hcost hδ
  have heta := MaxCSP.two_pow_succ_mul_exp_le_eta hη hs
  exact ⟨ht, by linarith⟩

/-! ### Bounded-arity Boolean `Max-CSP` optimization and witness recovery -/

/-- Width-guarded exact Boolean `Max-CSP` optimum recovered via `maxCSPToStruct`. -/
@[expose] def maxCSPOptimumBounded {Rel : Type} (w : ℕ) (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) : ℕ :=
  (maxCSPToStruct w sem F).optimum + F.constraints.length - (maxCSPToStruct w sem F).clauses.length

/-- When every constraint has scope length at most `w`, `maxCSPOptimumBounded w sem F` equals
`F.optimum sem`. -/
theorem maxCSPOptimumBounded_eq_optimum {Rel : Type} {w : ℕ} (sem : Rel → List Bool → Bool)
    {F : MaxCSPInstance Rel ℕ} (hw : ∀ c ∈ F.constraints, c.scope.length ≤ w) :
    maxCSPOptimumBounded w sem F = F.optimum sem := by
  have h := optimum_maxCSPToStruct_add_length sem hw
  dsimp only [maxCSPOptimumBounded]
  omega

/-- **Polynomial-time exact bounded-arity Boolean `Max-CSP` optimization from a polynomial-time
`k`-SAT decider (`3 ≤ k`).** -/
theorem computableInPolyTime_maxCSPOptimumBounded_of_KSAT {Rel : Type} [Finite Rel]
    (encRel : Rel ↪ List Bool) (w : ℕ) (sem : Rel → List Bool → Bool) {k : ℕ} (hk : 3 ≤ k)
    {solveKSAT : CNF ℕ → Bool} (hpoly : ComputableInPolyTime solveKSAT encCNF encBool)
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solveKSAT φ = true ↔ φ.Satisfiable)) :
    ComputableInPolyTime (maxCSPOptimumBounded w sem) (encMaxCSPInstance encRel) encNat := by
  have hstruct := computableInPolyTime_maxCSPToStruct encRel w sem
  exact binary_sub'
    (binary_add' ((computableInPolyTime_optimum_of_KSAT hk hpoly hspec).comp hstruct)
      (unary_to_binary.comp ((length_list (encConstraint encRel encNat)).comp
        (encMaxCSPInstance_constraints_polyTime encRel .id'))))
    (unary_to_binary.comp ((length_list (encList (encPair encNat encBool))).comp
      (encStructInstance_clauses_polyTime hstruct)))

/-- Width-guarded exact Boolean `Max-CSP` value and witness optimization via `maxCSPToStruct` and
`optimizeWith`. -/
def maxCSPOptimizeBounded {Rel : Type} (w : ℕ) (sem : Rel → List Bool → Bool)
    (solve : CNF ℕ → Bool) (F : MaxCSPInstance Rel ℕ) : StructSolution :=
  let sol := optimizeWith solve (maxCSPToStruct w sem F)
  ⟨sol.optValue + F.constraints.length - (maxCSPToStruct w sem F).clauses.length,
    sol.assignmentBits⟩

/-- **Correctness of `maxCSPOptimizeBounded`:** on any width-`≤ w` Boolean `MaxCSPInstance`, returns
`F.optimum sem` and an `F.numVars`-bit assignment achieving `F.score sem ... = F.optimum sem`
(`3 ≤ k`). -/
theorem maxCSPOptimizeBounded_spec {Rel : Type} {w k : ℕ} (hk : 3 ≤ k)
    (sem : Rel → List Bool → Bool) {solve : CNF ℕ → Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable))
    {F : MaxCSPInstance Rel ℕ} (hw : ∀ c ∈ F.constraints, c.scope.length ≤ w) :
    (maxCSPOptimizeBounded w sem solve F).optValue = F.optimum sem ∧
      (maxCSPOptimizeBounded w sem solve F).assignmentBits.length = F.numVars ∧
      F.score sem
        (BitString.ofList F.numVars (maxCSPOptimizeBounded w sem solve F).assignmentBits) =
        F.optimum sem := by
  obtain ⟨hopt, hlen, hsc⟩ := optimizeWith_spec hk hspec (maxCSPToStruct w sem F)
  have hopt_shift := optimum_maxCSPToStruct_add_length sem hw
  have hsc_shift := score_maxCSPToStruct_add_length sem hw
    (BitString.ofList F.numVars (optimizeWith solve (maxCSPToStruct w sem F)).assignmentBits)
  change (maxCSPToStruct w sem F).score
    (BitString.ofList F.numVars (optimizeWith solve (maxCSPToStruct w sem F)).assignmentBits) =
    (maxCSPToStruct w sem F).optimum at hsc
  dsimp only [maxCSPOptimizeBounded]
  exact ⟨by omega, hlen, by omega⟩

/-- **Polynomial-time closure for `maxCSPOptimizeBounded`:** for any polynomial-time procedure
`solve`, `maxCSPOptimizeBounded w sem solve` runs in polynomial time on multi-tape Turing machines
(and when `solve` decides `k`-SAT for `3 ≤ k`, `maxCSPOptimizeBounded_spec` certifies exact
optimality of both the returned value and witness assignment on width-`≤ w` instances). -/
theorem computableInPolyTime_maxCSPOptimizeBounded {Rel : Type} [Finite Rel]
    (encRel : Rel ↪ List Bool) (w : ℕ) (sem : Rel → List Bool → Bool) {solve : CNF ℕ → Bool}
    (hpoly : ComputableInPolyTime solve encCNF encBool) :
    ComputableInPolyTime (maxCSPOptimizeBounded w sem solve)
      (encMaxCSPInstance encRel) encStructSolution := by
  have hstruct := computableInPolyTime_maxCSPToStruct encRel w sem
  have hsol := (computableInPolyTime_optimizeWith hpoly).comp hstruct
  exact encStructSolution_mk_polyTime
    (binary_sub'
      (binary_add' (encStructSolution_optValue_polyTime hsol)
        (unary_to_binary.comp ((length_list (encConstraint encRel encNat)).comp
          (computableInPolyTime_maxCSP_constraints ComputableInPolyTime.id'))))
      (unary_to_binary.comp ((length_list (encList (encPair encNat encBool))).comp
        (encStructInstance_clauses_polyTime hstruct))))
    (encStructSolution_assignmentBits_polyTime hsol)

/-- Pure exact bounded-arity Boolean `Max-CSP` optimization by binary search via `maxCSPToStruct`.
-/
def optimumMaxCSPByBinarySearch {Rel : Type} (w : ℕ) (sem : Rel → List Bool → Bool)
    (solve : CNF ℕ → Bool) (F : MaxCSPInstance Rel ℕ) : ℕ :=
  optimumByBinarySearch solve (maxCSPToStruct w sem F) + F.constraints.length -
    (maxCSPToStruct w sem F).clauses.length

/-- `FreeM SATQuery` binary-search program computing the bounded-arity Boolean `Max-CSP` optimum via
`maxCSPToStruct`. -/
def optimumMaxCSPByBinarySearchQ {Rel : Type} (w : ℕ) (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) : FreeM SATQuery ℕ := do
  let optCNF ← optimumByBinarySearchQ (maxCSPToStruct w sem F)
  pure (optCNF + F.constraints.length - (maxCSPToStruct w sem F).clauses.length)

@[simp]
theorem eval_optimumMaxCSPByBinarySearchQ {Rel : Type} (oracle : {ι : Type} → SATQuery ι → ι)
    (w : ℕ) (sem : Rel → List Bool → Bool) (F : MaxCSPInstance Rel ℕ) :
    (optimumMaxCSPByBinarySearchQ w sem F).eval oracle =
      optimumMaxCSPByBinarySearch w sem (fun φ => oracle (.sat φ)) F := by
  simp [optimumMaxCSPByBinarySearchQ, optimumMaxCSPByBinarySearch]

/-- **Correctness of `Max-CSP` binary-search optimization:** on any width-`≤ w` Boolean
`MaxCSPInstance`, `optimumMaxCSPByBinarySearch` returns `F.optimum sem` (`3 ≤ k`). -/
theorem optimumMaxCSPByBinarySearch_eq_optimum {Rel : Type} {w k : ℕ} (hk : 3 ≤ k)
    (sem : Rel → List Bool → Bool) {solve : CNF ℕ → Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable))
    {F : MaxCSPInstance Rel ℕ} (hw : ∀ c ∈ F.constraints, c.scope.length ≤ w) :
    optimumMaxCSPByBinarySearch w sem solve F = F.optimum sem := by
  simp only [optimumMaxCSPByBinarySearch, optimumByBinarySearch_eq_optimum hk hspec]
  exact maxCSPOptimumBounded_eq_optimum sem hw

/-- **Weighted query-cost bound for `optimumMaxCSPByBinarySearchQ`.** -/
theorem cost_optimumMaxCSPByBinarySearchQ_le {Rel : Type} (oracle : {ι : Type} → SATQuery ι → ι)
    (weight : {ι : Type} → SATQuery ι → ℕ) (w : ℕ) (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget (maxCSPToStruct w sem F).workSize → weight (.sat φ) ≤ C) :
    (optimumMaxCSPByBinarySearchQ w sem F).cost oracle weight ≤
      C * (Nat.log 2 (maxCSPToStruct w sem F).clauses.length + 1) := by
  simp only [optimumMaxCSPByBinarySearchQ, FreeM.cost_bind, FreeM.cost_pure, add_zero]
  exact cost_optimumByBinarySearchQ_le oracle weight (maxCSPToStruct w sem F) hcost

/-- **Query-count bound for `optimumMaxCSPByBinarySearchQ`.** -/
theorem countQueries_optimumMaxCSPByBinarySearchQ_le {Rel : Type}
    (oracle : {ι : Type} → SATQuery ι → ι) (w : ℕ) (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) :
    (optimumMaxCSPByBinarySearchQ w sem F).countQueries oracle ≤
      Nat.log 2 (maxCSPToStruct w sem F).clauses.length + 1 := by
  simpa only [FreeM.countQueries_eq_cost_one, one_mul] using
    cost_optimumMaxCSPByBinarySearchQ_le oracle (fun _ => 1) w sem F (C := 1) fun _ _ _ => le_rfl

end Cslib.Complexity.MaxSAT
