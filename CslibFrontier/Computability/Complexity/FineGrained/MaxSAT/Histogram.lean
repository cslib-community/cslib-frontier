/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.MaxSAT.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialQueries
public import CslibFrontier.Logics.Propositional.MaxSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Foundations.Data.Nat.SqrtLog.Shifted
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Exact MAX-SAT score distributions and optimum

The threshold counter gives the number of assignments satisfying at least `q` clauses. Querying
all cutoffs from `0` through `m + 1`, for `m` clauses, gives the exact score distribution by
adjacent differences. The number of positive threshold counts, minus one, is the exact optimum.
Repeated and empty clauses retain their original contribution to the score.

Both outputs have native algorithms using
`2 ^ O(N / √log N) poly(L)` time and polynomial space, where `N` is literal occurrences plus
clauses and `L` is the complete encoded input length. The generic native query and postprocessing
theorems preserve the threshold counter's exponential factor. A bound in the declared variable
count requires a density hypothesis; this module does not discard clauses or multiplicities.
For the general propositional weighted partial MaxSAT definition and its bridge to `optimum`, see
`Cslib.Logic.PL.MaxSAT` (`toLogicMaxSAT`, `optimum_eq_logic_maxSatisfiedWeight`).

## Main results

* `MaxSAT.histogramFromCounts_thresholdCounts`: adjacent differences recover every exact count.
* `MaxSAT.optimumFromCounts_thresholdCounts`: positive threshold counts recover the optimum.
* `MaxSAT.exists_histogram_algorithm`, `MaxSAT.exists_optimum_algorithm`: native resource bounds.
* `MaxSAT.exists_sparse_histogram_algorithm`, `MaxSAT.exists_sparse_optimum_algorithm`:
  the rate in declared variables under fixed width and density bounds.
-/

@[expose] public section

namespace Cslib.Complexity.MaxSAT

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Number of assignments satisfying exactly `q` clauses. -/
def exactCount (F : Instance) (q : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : BitString F.1 => score F x = q)).card

/-- The complete score distribution, including the zero-score coefficient. -/
def histogram (F : Instance) : List ℕ :=
  (List.range (F.2.length + 1)).map (exactCount F)

/-- Maximum number of simultaneously satisfied clauses. -/
def optimum (F : Instance) : ℕ := Finset.univ.sup (score F)

/-- Threshold counts with one trailing zero at cutoff `m + 1`. -/
def thresholdCounts (F : Instance) : List ℕ :=
  (List.range (F.2.length + 2)).map (thresholdCount F)

/-- Adjacent differences of a threshold-count list. -/
def histogramFromCounts (counts : List ℕ) : List ℕ :=
  (counts.zip counts.tail).map (fun p => p.1 - p.2)

/-- The number of feasible score cutoffs, minus the always-feasible zero cutoff. -/
def optimumFromCounts (counts : List ℕ) : ℕ :=
  counts.countP (fun n => decide (0 < n)) - 1

/-- Differences of consecutive tail counts give the exact score count. -/
theorem thresholdCount_sub (F : Instance) (q : ℕ) :
    thresholdCount F q - thresholdCount F (q + 1) = exactCount F q := by
  have hsub : (Finset.univ.filter (fun x : BitString F.1 => q + 1 ≤ score F x)) ⊆
      Finset.univ.filter (fun x : BitString F.1 => q ≤ score F x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    omega
  have heq : (Finset.univ.filter (fun x : BitString F.1 => q ≤ score F x)) \
      (Finset.univ.filter (fun x : BitString F.1 => q + 1 ≤ score F x)) =
      Finset.univ.filter (fun x : BitString F.1 => score F x = q) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  simpa only [thresholdCount, exactCount, heq] using
    (Finset.card_sdiff_of_subset hsub).symm

/-- Adjacent differences preserve the increasing order of score indices. -/
theorem histogramFromCounts_range (f : ℕ → ℕ) (m : ℕ) :
    histogramFromCounts ((List.range (m + 1)).map f) =
      (List.range m).map (fun q => f q - f (q + 1)) := by
  apply List.ext_getElem
  · simp [histogramFromCounts]
  · intro i hi hj
    simp [histogramFromCounts]

/-- The returned histogram contains every exact assignment count. -/
theorem histogramFromCounts_thresholdCounts (F : Instance) :
    histogramFromCounts (thresholdCounts F) = histogram F := by
  simpa only [thresholdCounts, histogram, Nat.add_assoc, thresholdCount_sub] using
    histogramFromCounts_range (thresholdCount F) (F.2.length + 1)

/-- Every score is at most the optimum. -/
theorem score_le_optimum (F : Instance) (x : BitString F.1) : score F x ≤ optimum F :=
  Finset.le_sup (Finset.mem_univ x)

/-- The optimum is attained by an assignment, including when there are no variables. -/
theorem exists_score_eq_optimum (F : Instance) : ∃ x : BitString F.1, score F x = optimum F :=
  let ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (score F)
  ⟨x, hx.symm⟩

/-- The optimum is at most the number of clauses. -/
theorem optimum_le (F : Instance) : optimum F ≤ F.2.length :=
  Finset.sup_le (fun x _ => score_le F x)

/-- The feasible thresholds are exactly the integers from zero through the optimum. -/
theorem thresholdCount_pos_iff_le_optimum (F : Instance) (q : ℕ) :
    0 < thresholdCount F q ↔ q ≤ optimum F := by
  rw [thresholdCount_pos_iff]
  exact ⟨fun ⟨x, hx⟩ => hx.trans (score_le_optimum F x),
    fun hq => (exists_score_eq_optimum F).elim fun x hx => ⟨x, hx ▸ hq⟩⟩

/-- Number of naturals below `m` that are at most `q`. -/
theorem countP_range_le (m q : ℕ) :
    (List.range m).countP (fun j => decide (j ≤ q)) = min m (q + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : m ≤ q <;> simp [h] <;> omega

/-- Counting positive threshold counts returns the exact maximum score. -/
theorem optimumFromCounts_thresholdCounts (F : Instance) :
    optimumFromCounts (thresholdCounts F) = optimum F := by
  simp only [optimumFromCounts, thresholdCounts, List.countP_map, Function.comp_def,
    thresholdCount_pos_iff_le_optimum]
  rw [countP_range_le, Nat.min_eq_right (by have := optimum_le F; omega)]
  omega

/-- Differences are polynomial-time on binary counts. -/
theorem histogramFromCounts_polyTime :
    ComputableInPolyTime histogramFromCounts (encList encNat) (encList encNat) := by
  polytime [histogramFromCounts]

/-- Recovering the optimum is polynomial-time in the list of binary counts. -/
theorem optimumFromCounts_polyTime :
    ComputableInPolyTime optimumFromCounts (encList encNat) encNat := by
  polytime [optimumFromCounts]

/-! ### Native runtime bounds -/

/-- The complete threshold list is computed at the same contraction rate. The number of queries
and the materialized answer list contribute only polynomial factors. -/
theorem exists_thresholdCounts_algorithm :
    ∃ A d : ℕ, ComputableInO thresholdCounts encInstance (encList encNat)
      (fun F => 2 ^ (A * (workSize F + 1) / Nat.sqrt (Nat.log 2 (workSize F + 2))) *
        ((encInstance F).length + 1) ^ d)
      (fun F => ((encInstance F).length + 1) ^ d) := by
  obtain ⟨count, A, e, b, hcount, hc⟩ := exists_thresholdCounter
  rw [funext hcount] at hc
  obtain ⟨d, hd⟩ := ComputableInO.polynomial_queries
    (T := fun F => 2 ^ (A * (workSize F + 1) / Nat.sqrt (Nat.log 2 (workSize F + 2))))
    (e := e) (b := b) hc
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.unary_add'
      ((ComputableInPolyTime.length_list (encList (encPair encNat encBool))).comp
        (ComputableInPolyTime.snd encUnary encCNF)) (.const 2)))
    (fun _ => Nat.one_le_two_pow)
  exact ⟨A, d, hd⟩

/-- A native algorithm returns all exact score counts, in increasing order from `0` through `m`,
within the threshold counter's exponential rate and polynomial space. -/
theorem exists_histogram_algorithm :
    ∃ A d : ℕ, ComputableInO histogram encInstance (encList encNat)
      (fun F => 2 ^ (A * (workSize F + 1) / Nat.sqrt (Nat.log 2 (workSize F + 2))) *
        ((encInstance F).length + 1) ^ d)
      (fun F => ((encInstance F).length + 1) ^ d) := by
  obtain ⟨A, d, hd⟩ := exists_thresholdCounts_algorithm
  obtain ⟨e, he⟩ := hd.polynomial_postprocessing histogramFromCounts_polyTime
    (fun _ => Nat.one_le_two_pow)
  refine ⟨A, e, he.of_enc_eq fun F => ?_⟩
  rw [Function.comp_apply, histogramFromCounts_thresholdCounts]

/-- A native algorithm returns the exact MAX-SAT optimum at the contraction rate, with
polynomial space. This is uniform in clause width and in the input's declared variable count. -/
theorem exists_optimum_algorithm :
    ∃ A d : ℕ, ComputableInO optimum encInstance encNat
      (fun F => 2 ^ (A * (workSize F + 1) / Nat.sqrt (Nat.log 2 (workSize F + 2))) *
        ((encInstance F).length + 1) ^ d)
      (fun F => ((encInstance F).length + 1) ^ d) := by
  obtain ⟨A, d, hd⟩ := exists_thresholdCounts_algorithm
  obtain ⟨e, he⟩ := hd.polynomial_postprocessing optimumFromCounts_polyTime
    (fun _ => Nat.one_le_two_pow)
  refine ⟨A, e, he.of_enc_eq fun F => ?_⟩
  rw [Function.comp_apply, optimumFromCounts_thresholdCounts]

/-! ### Sparse fixed-width instances -/

/-- Width at most `k` and at most `c (n+1)` clauses on `n` declared variables. References retain
the total evaluation convention of `Instance`; well-formed instances have all references below
`n`. Both resource parameters are fixed before the input. -/
abbrev SparseInstance (k c : ℕ) :=
  {F : Instance // (∀ clause ∈ F.2, clause.length ≤ k) ∧ F.2.length ≤ c * (F.1 + 1)}

/-- The declared variable count of a sparse instance. -/
abbrev SparseInstance.numVars {k c : ℕ} : SparseInstance k c → ℕ
  | ⟨(numVars, _), _⟩ => numVars

/-- Sparse instances use the same complete encoding as their underlying formulas. -/
def encSparseInstance (k c : ℕ) : SparseInstance k c ↪ List Bool :=
  (Function.Embedding.subtype _).trans encInstance

/-- Width and density give an explicit linear bound on the parameter in the exponent. -/
theorem sparse_workSize_le {k c : ℕ} (F : SparseInstance k c) :
    workSize F.1 ≤ (k + 1) * c * F.numVars + (k + 1) * c := by
  calc workSize F.1 ≤ (k + 1) * F.1.2.length := workSize_le_of_width k F.1 F.2.1
    _ ≤ (k + 1) * (c * (F.1.1 + 1)) := Nat.mul_le_mul_left _ F.2.2
    _ = (k + 1) * c * F.1.1 + (k + 1) * c := by ring

private theorem sparse_algorithm {β : Type} {enc : β ↪ List Bool} {f : Instance → β}
    {A d : ℕ} (k c : ℕ)
    (hf : ComputableInO f encInstance enc
      (fun F => 2 ^ (A * (workSize F + 1) / Nat.sqrt (Nat.log 2 (workSize F + 2))) *
        ((encInstance F).length + 1) ^ d)
      (fun F => ((encInstance F).length + 1) ^ d)) :
    ComputableInO (fun F : SparseInstance k c => f F.1) (encSparseInstance k c) enc
      (fun F => 2 ^ (A * (8 * ((k + 1) * c) + 14) * (F.numVars + 1) /
        Nat.sqrt (Nat.log 2 (F.numVars + 2))) * ((encSparseInstance k c F).length + 1) ^ d)
      (fun F => ((encSparseInstance k c F).length + 1) ^ d) :=
  (hf.of_encIn_eq Subtype.val fun _ => rfl).mono_le
    (fun F => Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_succ_div_sqrt_log_two_le (sparse_workSize_le F))))
    (fun _ => le_rfl)

/-- Exact score distributions for sparse MAX-`k`-SAT in `2 ^ O(n / √log n) poly(L)` time and
polynomial space, for fixed width `k` and density `c`. Every one of the `2^n` canonical declared
assignments is counted, including assignments to unused variables. -/
theorem exists_sparse_histogram_algorithm (k c : ℕ) :
    ∃ A d : ℕ, ComputableInO (fun F : SparseInstance k c => histogram F.1)
      (encSparseInstance k c) (encList encNat)
      (fun F => 2 ^ (A * (F.numVars + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
        ((encSparseInstance k c F).length + 1) ^ d)
      (fun F => ((encSparseInstance k c F).length + 1) ^ d) := by
  obtain ⟨A, d, h⟩ := exists_histogram_algorithm
  exact ⟨A * (8 * ((k + 1) * c) + 14), d, sparse_algorithm k c h⟩

/-- The exact ordinary clause-count optimum for sparse MAX-`k`-SAT has the same native rate and
polynomial workspace. The input may contain duplicate and empty clauses. -/
theorem exists_sparse_optimum_algorithm (k c : ℕ) :
    ∃ A d : ℕ, ComputableInO (fun F : SparseInstance k c => optimum F.1)
      (encSparseInstance k c) encNat
      (fun F => 2 ^ (A * (F.numVars + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
        ((encSparseInstance k c F).length + 1) ^ d)
      (fun F => ((encSparseInstance k c F).length + 1) ^ d) := by
  obtain ⟨A, d, h⟩ := exists_optimum_algorithm
  exact ⟨A * (8 * ((k + 1) * c) + 14), d, sparse_algorithm k c h⟩

/-! ### Bridge to propositional MaxSAT -/

/-- Propositional weighted partial MaxSAT counterpart of `F : Instance`: variable references at
or above `F.1` are constrained to `false` by hard unit clauses, matching `assignment F.1 x`, and
every clause of `F.2` has soft weight `1`. -/
def toLogicMaxSAT (F : Instance) : Cslib.Logic.PL.MaxSAT ℕ where
  hard := (F.2.vars.filter fun v => decide (F.1 ≤ v)).map fun v => [(v, false)]
  soft := F.2.map (·, 1)

theorem toLogicMaxSAT_eq_unweighted (F : Instance) (hF : ∀ v ∈ F.2.vars, v < F.1) :
    toLogicMaxSAT F = Cslib.Logic.PL.MaxSAT.unweighted F.2 := by
  have hnil : F.2.vars.filter (fun v => decide (F.1 ≤ v)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro v hv
    simp [Nat.not_le.2 (hF v hv)]
  simp [toLogicMaxSAT, Cslib.Logic.PL.MaxSAT.unweighted, hnil]

@[simp]
theorem totalWeight_toLogicMaxSAT (F : Instance) :
    (toLogicMaxSAT F).totalWeight = F.2.length := by
  simp [toLogicMaxSAT, Cslib.Logic.PL.MaxSAT.totalWeight, List.map_map, Function.comp_def]

theorem feasible_toLogicMaxSAT_assignment (F : Instance) (x : BitString F.1) :
    (toLogicMaxSAT F).feasible (assignment F.1 x) := by
  simp only [Cslib.Logic.PL.MaxSAT.feasible, toLogicMaxSAT, CNF.eval_eq_true_iff, List.mem_map,
    List.mem_filter, decide_eq_true_eq]
  rintro c ⟨v, ⟨_, hv⟩, rfl⟩
  have hfalse : assignment F.1 x v = false := by simp [assignment, Nat.not_lt.2 hv]
  simp [Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, hfalse]

theorem satisfiedWeight_toLogicMaxSAT_assignment (F : Instance) (x : BitString F.1) :
    (toLogicMaxSAT F).satisfiedWeight (assignment F.1 x) = score F x := by
  change (Cslib.Logic.PL.MaxSAT.unweighted F.2).satisfiedWeight (assignment F.1 x) = score F x
  rw [Cslib.Logic.PL.MaxSAT.satisfiedWeight_unweighted]
  rfl

private theorem satisfiedWeight_toLogicMaxSAT_eq_score (F : Instance) {σ : ℕ → Bool}
    (hσ : (toLogicMaxSAT F).feasible σ) :
    (toLogicMaxSAT F).satisfiedWeight σ = score F (fun i => σ i.1) := by
  have hagree : ∀ v ∈ F.2.vars, σ v = assignment F.1 (fun i => σ i.1) v := by
    intro v hv
    by_cases hlt : v < F.1
    · simp [assignment, hlt]
    · have hle : F.1 ≤ v := Nat.le_of_not_lt hlt
      have hunit : Clause.eval σ [(v, false)] = true := by
        refine (CNF.eval_eq_true_iff σ (toLogicMaxSAT F).hard).1 hσ [(v, false)] ?_
        exact List.mem_map.2 ⟨v, List.mem_filter.2 ⟨hv, decide_eq_true hle⟩, rfl⟩
      have hfalse : σ v = false := by
        simpa [Clause.eval_cons, Literal.eval_mk, Clause.eval_nil] using hunit
      simp [assignment, hlt, hfalse]
  change (Cslib.Logic.PL.MaxSAT.unweighted F.2).satisfiedWeight σ = score F (fun i => σ i.1)
  rw [Cslib.Logic.PL.MaxSAT.satisfiedWeight_unweighted, CNF.countP_eval_congr hagree]
  rfl

theorem feasible_toLogicMaxSAT_nonempty (F : Instance) : (toLogicMaxSAT F).hard.Satisfiable :=
  ⟨assignment F.1 (fun _ => false), feasible_toLogicMaxSAT_assignment F (fun _ => false)⟩

/-- `MaxSAT.optimum F` coincides with the maximum satisfied weight of `toLogicMaxSAT F`. -/
theorem optimum_eq_toLogicMaxSAT_maxSatisfiedWeight (F : Instance) :
    (optimum F : WithBot ℕ) = (toLogicMaxSAT F).maxSatisfiedWeight := by
  symm
  refine (Cslib.Logic.PL.MaxSAT.maxSatisfiedWeight_eq_coe_iff (t := optimum F)).2 ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := exists_score_eq_optimum F
    exact ⟨assignment F.1 x, feasible_toLogicMaxSAT_assignment F x,
      (satisfiedWeight_toLogicMaxSAT_assignment F x).trans hx⟩
  · intro σ hσ
    rw [satisfiedWeight_toLogicMaxSAT_eq_score F hσ]
    exact score_le_optimum F _

/-- The propositional MaxSAT cost optimum of `toLogicMaxSAT F` is `F.2.length - optimum F`. -/
theorem toLogicMaxSAT_optimum_eq (F : Instance) :
    (toLogicMaxSAT F).optimum = ((F.2.length - optimum F : ℕ) : WithTop ℕ) := by
  obtain ⟨opt, maxSat, hopt, hmax, hsum⟩ :=
    Cslib.Logic.PL.MaxSAT.optimum_add_maxSatisfiedWeight (feasible_toLogicMaxSAT_nonempty F)
  have hmaxEq : maxSat = optimum F := by
    apply WithBot.coe_injective
    exact hmax.symm.trans (optimum_eq_toLogicMaxSAT_maxSatisfiedWeight F).symm
  rw [totalWeight_toLogicMaxSAT] at hsum
  rw [hopt]
  exact congrArg ((↑) : ℕ → WithTop ℕ) (by omega)

/-- For well-formed instances (all variables `< F.1`), `MaxSAT.optimum F` equals the maximum
satisfied weight of `Cslib.Logic.PL.MaxSAT.unweighted F.2`. -/
theorem optimum_eq_logic_maxSatisfiedWeight (F : Instance) (hF : ∀ v ∈ F.2.vars, v < F.1) :
    (optimum F : WithBot ℕ) = (Cslib.Logic.PL.MaxSAT.unweighted F.2).maxSatisfiedWeight := by
  rw [← toLogicMaxSAT_eq_unweighted F hF]
  exact optimum_eq_toLogicMaxSAT_maxSatisfiedWeight F

/-- For well-formed instances (all variables `< F.1`), the propositional unweighted MaxSAT cost
optimum of `F.2` is `F.2.length - optimum F`. -/
theorem logic_optimum_unweighted_eq (F : Instance) (hF : ∀ v ∈ F.2.vars, v < F.1) :
    (Cslib.Logic.PL.MaxSAT.unweighted F.2).optimum =
      ((F.2.length - optimum F : ℕ) : WithTop ℕ) := by
  rw [← toLogicMaxSAT_eq_unweighted F hF]
  exact toLogicMaxSAT_optimum_eq F

end Cslib.Complexity.MaxSAT
