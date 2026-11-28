/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.FineGrained.BruteForce
import CslibFrontier.Computability.Complexity.FineGrained.MaxSAT.Reduction
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Verification tests for `Max-CSP`, constraint subsampling, and fixed-width SAT reductions

Exercises `MaxCSP`, `MaxCSPSampling`, and `MaxSAT.Reduction` across the strict `module` boundary:
* finite-domain (`Fin 3`) and Boolean unweighted/weighted `Max-CSP` scores, optima, and clamped
  binary compilation (`toClampedBoolean`);
* exact affine score and optimum shifts under forbidden-pattern `CSP.toCNF` compilation;
* nonvacuous instantiations of the `2 ^ (n + 1) * exp (-2 * s * δ ^ 2)` and
  `|D| ^ n * 2 * exp (-2 * s * δ ^ 2)` subsampling bounds, existence of sparse approximators, and
  tightness of the `2 * δ * m` optimality-loss bound;
* concrete `thresholdToCNF` compilation, `O(log m)`-query `FreeM SATQuery` binary-search
  optimization and witness recovery (`optimumByBinarySearchQ`, `optimizeByBinarySearchQ`,
  `optimumMaxCSPByBinarySearchQ`), and native resource transfer (`FixedWidthSATSolver`,
  `optimizeWith`, `maxCSPOptimizeBounded`, `exists_computableInPolyTime_optimize_of_KSAT_mem_P`).
-/

set_option linter.privateModule false

namespace Cslib.Tests.MaxCSPSamplingAndReduction

open Cslib.Algorithms.Lean Cslib.Complexity Cslib.Complexity.MaxSAT Cslib.Logic.PL Cslib.Query
  Turing.MultiTapeTM

/-! ### 1. Finite-domain `Max-CSP` (`Fin 3` 3-coloring on `K₃` and `K₄`) and clamped compilation -/

/-- Disequality relation on `Fin 3` for proper 3-coloring edges. -/
def neqFin3 (_ : Unit) : List (Fin 3) → Bool
  | [u, v] => decide (u ≠ v)
  | _ => false

/-- Triangle `K₃` has 3 edges and is 3-colorable (`optimum = 3`). -/
def k3ColorCSP : MaxCSPInstance Unit ℕ where
  numVars := 3
  constraints := [⟨(), [0, 1]⟩, ⟨(), [1, 2]⟩, ⟨(), [0, 2]⟩]

/-- Equality (`true`) or disequality (`false`) relation on `Fin 3`. -/
def eqOrNeqFin3 (wantEq : Bool) : List (Fin 3) → Bool
  | [u, v] => if wantEq then decide (u = v) else decide (u ≠ v)
  | _ => false

/-- Unsatisfiable `Fin 3` triangle `x₀ = x₁`, `x₁ = x₂`, `x₀ ≠ x₂` (`3` constraints, `optimum = 2`).
-/
def frustratedFin3CSP : MaxCSPInstance Bool ℕ where
  numVars := 3
  constraints := [⟨true, [0, 1]⟩, ⟨true, [1, 2]⟩, ⟨false, [0, 2]⟩]

/-- Complete graph `K₄` on `Fin 3` (`4` variables, `6` edges). -/
def k4ColorCSP : MaxCSPInstance Unit ℕ where
  numVars := 4
  constraints :=
    [⟨(), [0, 1]⟩, ⟨(), [0, 2]⟩, ⟨(), [0, 3]⟩, ⟨(), [1, 2]⟩, ⟨(), [1, 3]⟩, ⟨(), [2, 3]⟩]

example : k3ColorCSP.optimum neqFin3 = 3 := by decide
example : frustratedFin3CSP.optimum eqOrNeqFin3 = 2 := by decide

/-- Clamped Boolean compilation of `frustratedFin3CSP` on `3 * 2 = 6` Boolean variables preserves
the exact optimum `2` without penalty weights. -/
theorem frustratedFin3_clampedBoolean_optimum :
    (frustratedFin3CSP.toClampedBoolean 3).optimum
      (MaxCSP.clampedSem 3 (by decide) eqOrNeqFin3) = 2 := by
  rw [frustratedFin3CSP.optimum_toClampedBoolean (by decide) eqOrNeqFin3 (by decide)]
  decide

/-! ### 2. Weighted `Max-CSP`, zero-variable & repeated-scope edge cases -/

/-- Concrete weighted `Max-CSP` over `ℕ` with asymmetric weights `3, 5, 7`. -/
def asymWeightedCSP : WeightedMaxCSP Bool ℕ ℕ where
  numVars := 1
  constraints := [⟨true, [0], 3⟩, ⟨false, [0], 5⟩, ⟨false, [0], 7⟩]

def litSem (pol : Bool) : List Bool → Bool
  | [b] => pol == b
  | _ => false

/-- Setting `x₀ = false` earns `5 + 7 = 12`, beating `x₀ = true` (`3`). -/
example : asymWeightedCSP.optimum litSem = 12 := by decide

/-- Zero-variable (`numVars = 0`) edge case with a nullary true constraint and a repeated-variable
scope `[0, 0]` reading the default `false` value outside `Fin 0`. -/
def zeroVarCSP : MaxCSPInstance Bool ℕ where
  numVars := 0
  constraints := [⟨true, []⟩, ⟨false, [0, 0]⟩]

def eqAllSem (target : Bool) (bs : List Bool) : Bool :=
  bs.all (· == target)

example : zeroVarCSP.optimum eqAllSem = 2 := by decide

/-! ### 3. Forbidden-pattern `CSP.toCNF` exact affine score and optimum shift -/

/-- Concrete unsatisfiable XOR cycle `x₀ ≠ x₁`, `x₁ ≠ x₂`, `x₀ ≠ x₂` (`3` constraints,
`optimum = 2`). -/
def xorCycleCSP : MaxCSPInstance Unit ℕ where
  numVars := 3
  constraints := [⟨(), [0, 1]⟩, ⟨(), [1, 2]⟩, ⟨(), [0, 2]⟩]

def xor2Sem (_ : Unit) : List Bool → Bool
  | [a, b] => a != b
  | _ => false

example : xorCycleCSP.optimum xor2Sem = 2 := by decide
example : (maxCSPToStruct 2 xor2Sem xorCycleCSP).clauses.length = 6 := by decide
example : (maxCSPToStruct 2 xor2Sem xorCycleCSP).optimum = 5 := by decide

/-- Verifies `5 + 3 = 6 + 2` via `optimum_maxCSPToStruct_add_length`. -/
theorem xorCycle_affine_shift :
    (maxCSPToStruct 2 xor2Sem xorCycleCSP).optimum + xorCycleCSP.constraints.length =
      (maxCSPToStruct 2 xor2Sem xorCycleCSP).clauses.length + xorCycleCSP.optimum xor2Sem :=
  optimum_maxCSPToStruct_add_length xor2Sem (by decide)

/-! ### 4. Tightness of the `2 * δ * m` optimality loss and nonvacuous subsampling bounds -/

/-- Instance on `1` variable with `4` clauses: `x₀` three times and `¬x₀` once (`m = 4`,
`optimum = 3` at `x₀ = true`, while `x₀ = false` has score `1`, losing `2 = 2 * (1 / 4) * 4` when a
`2`-sample picks `[x₀, ¬x₀]`). -/
abbrev tightLossInst : StructInstance :=
  ⟨1, [[(0, true)], [(0, true)], [(0, true)], [(0, false)]]⟩

example : tightLossInst.optimum = 3 := by decide

/-- Sample `ω = ![0, 3]` selects `x₀` and `¬x₀` (`s = 2`, `m = 4`). Rescaled score `(4 / 2) * 1 = 2`
is within `δ * m = (1 / 4) * 4 = 1` of the true scores `3` and `1` on *both* assignments, and the
sampled maximizer `xHat = fun _ => false` achieves true score `1 = 3 - 2 * (1 / 4) * 4`, attaining
the `2 * δ * m` loss bound with exact equality! -/
def tightSample : Fin 2 → Fin tightLossInst.clauses.length
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨3, by decide⟩

abbrev falseAssign : BitString 1 := fun _ => false
abbrev trueAssign : BitString 1 := fun _ => true

theorem tight_two_delta_m_attained :
    (tightLossInst.optimum : ℝ) - (tightLossInst.score falseAssign : ℝ) =
      2 * (1 / 4 : ℝ) * (tightLossInst.clauses.length : ℝ) ∧
    (∀ x : BitString tightLossInst.numVars,
      |(tightLossInst.clauses.length : ℝ) / (2 : ℝ) *
          ((tightLossInst.sample tightSample).score x : ℝ) -
        (tightLossInst.score x : ℝ)| ≤
      (1 / 4 : ℝ) * (tightLossInst.clauses.length : ℝ)) ∧
    (∀ x : BitString tightLossInst.numVars,
      (tightLossInst.sample tightSample).score x ≤
        (tightLossInst.sample tightSample).score falseAssign) := by
  have hopt : tightLossInst.optimum = 3 := by decide
  have hfalse_full : tightLossInst.score falseAssign = 1 := by decide
  have hfalse_samp : (tightLossInst.sample tightSample).score falseAssign = 1 := by decide
  have htrue_full : tightLossInst.score trueAssign = 3 := by decide
  have htrue_samp : (tightLossInst.sample tightSample).score trueAssign = 1 := by decide
  have hlen : tightLossInst.clauses.length = 4 := rfl
  refine ⟨by rw [hopt, hfalse_full, hlen]; norm_num, fun x => ?_, fun x => ?_⟩
  · by_cases hx : x 0 = true
    · have hxeq : x = trueAssign := funext fun i => by fin_cases i; exact hx
      rw [hxeq, htrue_samp, htrue_full, hlen]
      norm_num
    · have hxeq : x = falseAssign := funext fun i => by
        fin_cases i
        exact Bool.eq_false_iff.mpr hx
      rw [hxeq, hfalse_samp, hfalse_full, hlen]
      norm_num
  · by_cases hx : x 0 = true
    · have hxeq : x = trueAssign := funext fun i => by fin_cases i; exact hx
      rw [hxeq, htrue_samp, hfalse_samp]
    · have hxeq : x = falseAssign := funext fun i => by
        fin_cases i
        exact Bool.eq_false_iff.mpr hx
      rw [hxeq]

/-- Nonvacuous instantiation of `exists_boolean_sample_approx` on `xorCycleCSP` (`n = 3`,
`δ = 1 / 2`, `s = 6`: `(3 + 1) * log 2 < 4 * 0.7 = 2.8 < 3 = 2 * 6 * (1 / 2) ^ 2`). -/
theorem nonvacuous_exists_boolean_sample :
    ∃ ω : Fin 6 → Fin xorCycleCSP.constraints.length,
      (∀ xHat : BitString xorCycleCSP.numVars,
        (∀ x, (xorCycleCSP.sample ω).score xor2Sem x ≤
          (xorCycleCSP.sample ω).score xor2Sem xHat) →
        (xorCycleCSP.optimum xor2Sem : ℝ) - (xorCycleCSP.score xor2Sem xHat : ℝ) ≤
          2 * (1 / 2 : ℝ) * (xorCycleCSP.constraints.length : ℝ)) := by
  have hlog : (xorCycleCSP.numVars + 1 : ℝ) * Real.log 2 < 2 * (6 : ℝ) * (1 / 2 : ℝ) ^ 2 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hn : (xorCycleCSP.numVars : ℝ) = 3 := rfl
    rw [hn]
    linarith
  obtain ⟨ω, -, hloss, -⟩ :=
    xorCycleCSP.exists_boolean_sample_approx xor2Sem (by decide) (by norm_num) hlog
  exact ⟨ω, hloss⟩

/-- Nonvacuous instantiation of `[0, 1]`-weighted subsampling concentration over `Fin 3`. -/
theorem nonvacuous_fin3_weighted_sampling :
    let F : WeightedMaxCSP Unit ℕ ℝ := k4ColorCSP.toRealWeighted
    ((F.samplePMF (by decide) 20).toOuterMeasure
      {ω | ∃ x : Fin F.numVars → Fin 3,
        (1 / 2 : ℝ) * (F.constraints.length : ℝ) ≤
          |(F.constraints.length : ℝ) / (20 : ℝ) * (F.sample ω).score neqFin3 x -
            F.score neqFin3 x|}).toReal ≤
      (3 : ℝ) ^ 4 * 2 * Real.exp (-2 * (20 : ℝ) * (1 / 2 : ℝ) ^ 2) := by
  intro F
  have hw : ∀ c ∈ F.constraints, c.weight ∈ Set.Icc (0 : ℝ) 1 := by
    intro c hc
    simp only [F, MaxCSPInstance.toRealWeighted, List.mem_map] at hc
    obtain ⟨_, _, rfl⟩ := hc
    exact ⟨zero_le_one, le_rfl⟩
  have hnv : F.numVars = 4 := rfl
  simpa only [Fintype.card_fin, hnv, Nat.cast_ofNat] using
    F.exists_sample_score_abs_sub_ge_le neqFin3 (by decide) 20 hw (by norm_num)

/-! ### 5. Encoded words of constraints and `Max-CSP` instances

`Constraint` is a structure and `MaxCSPInstance` stores a `CSP`, but the encodings still write
the same words as the pair encodings they replaced (`encMaxConstraint` encoded `(c.rel, c.scope)`
with `encPair encRel (encList encNat)`). -/

example {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (c : Constraint Rel V) :
    encConstraint encRel encV c = encPair encRel (encList encV) (c.rel, c.scope) := rfl

example {Rel : Type} (encRel : Rel ↪ List Bool) (F : MaxCSPInstance Rel ℕ) :
    encMaxCSPInstance encRel F =
      encPair encUnary (encCSP encRel encNat) (F.numVars, F.constraints) := rfl

example {Rel : Type} (encRel : Rel ↪ List Bool) (F : MaxCSPInstance Rel ℕ) :
    encMaxCSPInstance encRel F =
      encPair encUnary (encList (encPair encRel (encList encNat)))
        (F.numVars, F.constraints.map fun c => (c.rel, c.scope)) := by
  simp only [encMaxCSPInstance_apply, encPair_apply, encList, Function.Embedding.coeFn_mk,
    List.flatMap_map, Function.comp_def, encConstraint_apply]

example : encMaxCSPInstance encUnit xorCycleCSP =
    encPair encUnary (encList (encPair encUnit (encList encNat)))
      (3, [((), [0, 1]), ((), [1, 2]), ((), [0, 2])]) := rfl

/-! ### 6. Fixed-width SAT reduction, `FreeM` binary search, and native witness transfer -/

/-- Unsatisfiable 4-clause 2-CNF instance (`optimum = 3`). -/
def fourClauseInst : StructInstance where
  numVars := 2
  clauses := [[(0, true)], [(0, false)], [(0, true), (1, true)], [(0, false), (1, false)]]

example : fourClauseInst.optimum = 3 := by decide

theorem bruteForce_spec (φ : CNF ℕ) (_ : ∀ c ∈ φ, c.length ≤ 3) :
    BruteForce.search φ = true ↔ φ.Satisfiable :=
  BruteForce.search_eq_true_iff φ

/-- `SATQuery` oracle backed by `BruteForce.search`. -/
def bruteOracle : {ι : Type} → SATQuery ι → ι :=
  SATQuery.oracleOf BruteForce.search

/-- `optimumByBinarySearch` / `optimumByBinarySearchQ` find the exact optimum `3` of
`fourClauseInst` in at most `⌊log₂ 4⌋ + 1 = 3` SAT queries, and make `0` queries on an empty
formula. -/
example : (optimumByBinarySearchQ fourClauseInst).eval bruteOracle = 3 := by
  rw [eval_optimumByBinarySearchQ]
  exact (optimumByBinarySearch_eq_optimum (k := 3) le_rfl bruteForce_spec fourClauseInst).trans
    (by decide)

example : (optimumByBinarySearchQ fourClauseInst).countQueries bruteOracle ≤ 3 := by
  have h := countQueries_optimumByBinarySearchQ_le bruteOracle fourClauseInst
  have hlog : Nat.log 2 fourClauseInst.clauses.length + 1 = 3 := by decide
  exact h.trans_eq hlog

example : optimumByBinarySearch BruteForce.search ⟨2, []⟩ = 0 :=
  (optimumByBinarySearch_eq_optimum (k := 3) le_rfl bruteForce_spec ⟨2, []⟩).trans (by decide)

example : (optimumByBinarySearchQ ⟨2, []⟩).countQueries bruteOracle = 0 :=
  countQueries_optimumByBinarySearchQ_of_clauses_eq_nil bruteOracle rfl

/-- Nonvacuous instantiation of the `η = 1 / 4` failure-probability sample-size bound on
`xorCycleCSP` (`n = 3`, `δ = 1 / 2`, `s = 9`: `(3 + 1) * log 2 + log 4 = 6 * log 2 < 4.2 ≤ 4.5`). -/
theorem nonvacuous_sample_size_eta :
    (3 / 4 : ℝ) ≤
      ((xorCycleCSP.samplePMF (by decide) 9).toOuterMeasure
        {ω | (∀ xHat : BitString xorCycleCSP.numVars,
            (∀ x, (xorCycleCSP.sample ω).score xor2Sem x ≤
              (xorCycleCSP.sample ω).score xor2Sem xHat) →
              (xorCycleCSP.optimum xor2Sem : ℝ) -
                (xorCycleCSP.score xor2Sem xHat : ℝ) ≤
                2 * (1 / 2 : ℝ) * (xorCycleCSP.constraints.length : ℝ)) ∧
          |(xorCycleCSP.constraints.length : ℝ) / (9 : ℝ) *
              ((xorCycleCSP.sample ω).optimum xor2Sem : ℝ) -
            (xorCycleCSP.optimum xor2Sem : ℝ)| ≤
              (1 / 2 : ℝ) * (xorCycleCSP.constraints.length : ℝ)}).toReal := by
  have hs : (xorCycleCSP.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / (1 / 4 : ℝ)) ≤
      2 * (9 : ℝ) * (1 / 2 : ℝ) ^ 2 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hn : (xorCycleCSP.numVars : ℝ) = 3 := rfl
    have h4 : (1 : ℝ) / (1 / 4 : ℝ) = 2 ^ 2 := by norm_num
    rw [hn, h4, Real.log_pow]
    push_cast
    linarith
  have h := xorCycleCSP.one_sub_le_boolean_sample_good_of_sample_size xor2Sem (by decide)
    (s := 9) (by norm_num) (by norm_num) hs
  linarith

/-- Witness recovery (`optimizeByBinarySearch` / `optimizeByBinarySearchQ`) finds both `optimum = 3`
and a 2-bit assignment scoring `3` on `fourClauseInst` within `⌊log₂ 4⌋ + 1 + 2 = 5` SAT queries. -/
theorem fourClause_optimize_witness :
    (optimizeByBinarySearch BruteForce.search fourClauseInst).optValue = 3 ∧
      (optimizeByBinarySearch BruteForce.search fourClauseInst).assignmentBits.length = 2 ∧
      fourClauseInst.score
        (BitString.ofList fourClauseInst.numVars
          (optimizeByBinarySearch BruteForce.search fourClauseInst).assignmentBits) = 3 ∧
      (optimizeByBinarySearchQ fourClauseInst).eval bruteOracle =
        optimizeByBinarySearch BruteForce.search fourClauseInst ∧
      (optimizeByBinarySearchQ fourClauseInst).countQueries bruteOracle ≤ 5 := by
  obtain ⟨hopt, hlen, hscore⟩ :=
    optimizeByBinarySearch_spec (k := 3) le_rfl bruteForce_spec fourClauseInst
  have h3 : fourClauseInst.optimum = 3 := by decide
  have ht := countQueries_optimizeByBinarySearchQ_le bruteOracle fourClauseInst
  have h5 : Nat.log 2 fourClauseInst.clauses.length + 1 + fourClauseInst.numVars = 5 := by decide
  exact ⟨hopt.trans h3, hlen, hscore.trans h3,
    eval_optimizeByBinarySearchQ bruteOracle fourClauseInst, ht.trans_eq h5⟩

/-- End-to-end subsampled witness-recovery guarantee under the `η = 1 / 2` sample-size bound on
`fourClauseInst` (`n = 2`, `w = 2`, `δ = 1 / 2`, `s = 8`: `4 * log 2 < 2.8 ≤ 4`). -/
theorem fourClause_sample_optimize_eta_spec :
    (∀ ω : Fin 8 → Fin fourClauseInst.clauses.length,
      (optimizeByBinarySearchQ (fourClauseInst.sample ω)).countQueries bruteOracle ≤ 6) ∧
    (1 / 2 : ℝ) ≤
      ((fourClauseInst.samplePMF (by decide) 8).toOuterMeasure
        {ω | (fourClauseInst.optimum : ℝ) -
              (fourClauseInst.score
                (BitString.ofList fourClauseInst.numVars
                  (optimizeByBinarySearch BruteForce.search
                    (fourClauseInst.sample ω)).assignmentBits) : ℝ) ≤
              2 * (1 / 2 : ℝ) * (fourClauseInst.clauses.length : ℝ) ∧
          |(fourClauseInst.clauses.length : ℝ) / (8 : ℝ) *
              ((optimizeByBinarySearch BruteForce.search (fourClauseInst.sample ω)).optValue : ℝ) -
            (fourClauseInst.optimum : ℝ)| ≤
              (1 / 2 : ℝ) * (fourClauseInst.clauses.length : ℝ)}).toReal := by
  have hs : (fourClauseInst.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / (1 / 2 : ℝ)) ≤
      2 * (8 : ℝ) * (1 / 2 : ℝ) ^ 2 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hn : (fourClauseInst.numVars : ℝ) = 2 := rfl
    have hdiv : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
    rw [hn, hdiv]
    linarith
  obtain ⟨ht, hprob⟩ := sample_optimizeByBinarySearch_spec_of_sample_size (k := 3) (w := 2)
    le_rfl bruteForce_spec (F := fourClauseInst) (by decide) (by decide) (s := 8)
    (weight := fun _ => 1) (C := 1) (fun _ _ _ => le_rfl) (by norm_num) (η := 1 / 2)
    (by norm_num) hs
  have h6 : Nat.log 2 8 + 1 + fourClauseInst.numVars = 6 := by decide
  refine ⟨fun ω => ?_, by linarith⟩
  rw [FreeM.countQueries_eq_cost_one]
  exact (ht ω).trans_eq (by rw [one_mul, h6])

/-- Exponential-time decision transfer instantiated from `KSAT_decidableInExpTime_one 3`. -/
theorem thresholdLanguage_expTime_bruteForce :
    DecidableInExpTime ThresholdLanguage encThresholdQuery ThresholdQuery.workSize 957 := by
  simpa only [mul_one] using
    decidableInExpTime_thresholdLanguage_of_KSAT (k := 3) le_rfl zero_le_one
      (KSAT_decidableInExpTime_one 3)

/-- Native `FixedWidthSATSolver 3` instantiated via `FixedWidthSATSolver.exists_bruteForce` to
verify `FixedWidthSATSolver.exists_optimum_algorithm` end-to-end in
`2 ^ thresholdVarBudget workSize` time and polynomial space. -/
theorem exists_bruteForce_optimum_from_solver :
    ∃ d : ℕ,
      ComputableInO StructInstance.optimum encStructInstance encNat
        (fun F => 2 ^ thresholdVarBudget F.workSize * ((encStructInstance F).length + 1) ^ d)
        (fun F => ((encStructInstance F).length + 1) ^ d) := by
  obtain ⟨solver, -, hrate⟩ := FixedWidthSATSolver.exists_bruteForce 3
  obtain ⟨d, hinO⟩ := solver.exists_optimum_algorithm (k := 3) le_rfl
  rw [hrate] at hinO
  exact ⟨d, hinO⟩

/-- Native witness optimization (`optimizeWith` and `maxCSPOptimizeBounded`) checked on
`fourClauseInst` (`optimum = 3`) and `xorCycleCSP` (`optimum = 2`), plus class-level transfer when
`ThreeSAT ∈ P encCNF`. -/
theorem native_optimizeWith_fourClause :
    (optimizeWith BruteForce.search fourClauseInst).optValue = 3 ∧
      (optimizeWith BruteForce.search fourClauseInst).assignmentBits.length = 2 ∧
      fourClauseInst.score
        (BitString.ofList fourClauseInst.numVars
          (optimizeWith BruteForce.search fourClauseInst).assignmentBits) = 3 := by
  obtain ⟨hopt, hlen, hsc⟩ := optimizeWith_spec (k := 3) le_rfl bruteForce_spec fourClauseInst
  have h3 : fourClauseInst.optimum = 3 := by decide
  exact ⟨hopt.trans h3, hlen, hsc.trans h3⟩

theorem native_maxCSPOptimize_xorCycle :
    (maxCSPOptimizeBounded 2 xor2Sem BruteForce.search xorCycleCSP).optValue = 2 ∧
      (maxCSPOptimizeBounded 2 xor2Sem BruteForce.search xorCycleCSP).assignmentBits.length = 3 ∧
      xorCycleCSP.score xor2Sem
        (BitString.ofList xorCycleCSP.numVars
          (maxCSPOptimizeBounded 2 xor2Sem BruteForce.search xorCycleCSP).assignmentBits) = 2 := by
  obtain ⟨hopt, hlen, hsc⟩ :=
    maxCSPOptimizeBounded_spec (w := 2) (k := 3) le_rfl xor2Sem bruteForce_spec
      (F := xorCycleCSP) (by decide)
  have h2 : xorCycleCSP.optimum xor2Sem = 2 := by decide
  exact ⟨hopt.trans h2, hlen, hsc.trans h2⟩

theorem polyTime_optimize_if_ThreeSAT_mem_P (hP : ThreeSAT ∈ P encCNF) :
    ∃ solveOpt : StructInstance → StructSolution,
      ComputableInPolyTime solveOpt encStructInstance encStructSolution ∧
      ∀ F : StructInstance,
        (solveOpt F).optValue = F.optimum ∧
        (solveOpt F).assignmentBits.length = F.numVars ∧
        F.score (BitString.ofList F.numVars (solveOpt F).assignmentBits) = F.optimum :=
  exists_computableInPolyTime_optimize_of_KSAT_mem_P (k := 3) le_rfl hP

/-- Binary-search `Max-CSP` optimization instantiated on `xorCycleCSP` (`optimum = 2`). -/
example : optimumMaxCSPByBinarySearch 2 xor2Sem BruteForce.search xorCycleCSP = 2 :=
  (optimumMaxCSPByBinarySearch_eq_optimum (w := 2) (k := 3) le_rfl xor2Sem bruteForce_spec
    (by decide)).trans (by decide)

example : (optimumMaxCSPByBinarySearchQ 2 xor2Sem xorCycleCSP).countQueries bruteOracle ≤
    Nat.log 2 (maxCSPToStruct 2 xor2Sem xorCycleCSP).clauses.length + 1 :=
  countQueries_optimumMaxCSPByBinarySearchQ_le bruteOracle 2 xor2Sem xorCycleCSP

end Cslib.Tests.MaxCSPSamplingAndReduction
