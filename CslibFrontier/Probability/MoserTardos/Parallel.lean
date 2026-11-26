/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MoserTardos.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Parallel Moser–Tardos algorithm

This module formalizes the parallel resampling algorithm for the variable-model Lovász Local
Lemma ([MoserTardos2010, Algorithm 1.2, Section 4, Theorem 1.3]).

In each parallel round, an admissible selection rule `psel` inspects the current assignment
`current vbl T w` and selects a **maximal independent set** of occurring bad events:
1. every selected event occurs at `current vbl T w` (`IsValidParallelRule.mem`);
2. selected events are pairwise non-adjacent (`¬Adj vbl i j`), i.e., distinct and defined on
   disjoint variable sets (`IsValidParallelRule.pairwise`);
3. every occurring event shares at least one variable with (or equals) some selected event
   (`IsValidParallelRule.max`).

In particular, `psel T w = []` holds if and only if no bad event occurs at `current vbl T w`.
Resampling all events in the chosen batch in sequence appends them onto the cumulative log `w`
(`parallelRun`), preserving `IsLog`. Any event resampled in round `k` yields a witness structure
of depth `k` and size at least `k + 1` ([MoserTardos2010, Lemma 4.1]). Summing the resulting
tail bounds `Pr[parallelRounds ≥ k + 1] ≤ min 1 ((1 - ε)^(k+1) * ∑ i, x i / (1 - x i))` yields
the logarithmic expected round bound `((max 0 (Real.log M) + 1) / ε)` of Theorem 1.3.

Termination needs no slack. Every prefix of the parallel run is a valid log, so the bound of
Theorem 1.2 for all valid logs (`lintegral_iSup_count_le`) applies to it. Under the plain
hypothesis `Pr[A i] ≤ x i * ∏ j ∈ Γ i, (1 - x j)`, almost surely every admissible rule reaches an
empty batch, and the whole run performs at most `∑ i, x i / (1 - x i)` resamplings in
expectation. The slack `ε` is needed only for the round bound.

## Main definitions

* `Cslib.Probability.MoserTardos.IsValidParallelRule`: admissibility predicate for a parallel
  selection rule choosing a maximal independent set of occurring events.
* `Cslib.Probability.MoserTardos.parallelRun`: the cumulative log after `n` parallel rounds.
* `Cslib.Probability.MoserTardos.parallelRounds`: the number of non-empty parallel rounds
  (`ℝ≥0∞`, equal to `⊤` if no terminating round is reached).
* `Cslib.Probability.MoserTardos.greedyIndependentSubset`,
  `Cslib.Probability.MoserTardos.greedyParallelList`,
  `Cslib.Probability.MoserTardos.greedyParallel`: greedy maximal independent set selection rules.

## Main results

* `Cslib.Probability.MoserTardos.isLog_parallelRun`: parallel execution produces a valid log.
* `Cslib.Probability.MoserTardos.parallel_witness_depth`: [MoserTardos2010, Lemma 4.1] (witness
  structure of depth `k` and cardinality at least `k + 1` for every event resampled in round `k`).
* `Cslib.Probability.MoserTardos.table_succ_le_parallelRounds_le` and
  `Cslib.Probability.MoserTardos.lintegral_parallelRounds_le`: [MoserTardos2010, Theorem 1.3] tail
  and expected round bounds under `Pr[A i] ≤ (1 - ε) * x i * ∏ j ∈ Γ i, (1 - x j)`.
* `Cslib.Probability.MoserTardos.ae_exists_parallelRun_eq_nil`,
  `Cslib.Probability.MoserTardos.ae_exists_forall_notMem_parallelRun`: almost sure termination at
  an assignment avoiding every event, under `Pr[A i] ≤ x i * ∏ j ∈ Γ i, (1 - x j)` with no slack;
  `ae_exists_parallelRun_eq_nil_of_bound` is the generic form and
  `ae_exists_forall_notMem_parallelRun_symmetric` the symmetric case `e * q * (d + 1) ≤ 1`.
* `Cslib.Probability.MoserTardos.lintegral_iSup_length_parallelRun_le`: the expected total number
  of resamplings of the parallel run is at most `∑ i, x i / (1 - x i)`, with no slack, as a
  consequence of `lintegral_iSup_count_le` through a measurable majorant.
* `Cslib.Probability.MoserTardos.lintegral_parallelRounds_le_symmetric`,
  `Cslib.Probability.MoserTardos.lintegral_parallelRounds_le_symmetric_of_pos`: symmetric
  specializations of the round bound under `e * q * (d + 1) ≤ 1 - ε`.
* `Cslib.Probability.MoserTardos.lintegral_parallelRounds_le_pmfPi` and
  `Cslib.Probability.MoserTardos.lintegral_parallelRounds_le_pmfPi_symmetric`: `PMF.pi` bridges.

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010]
-/

public section

open Finset MeasureTheory ENNReal

namespace Cslib.Probability.MoserTardos

section ParallelExecution

variable {V ι : Type*} {α : V → Type*}

/-- A parallel selection rule for the Moser–Tardos algorithm chooses, from the table `T` and the
current log `w`, a maximal independent subset of the events occurring at `current vbl T w`.
Returning `[]` indicates that no bad event occurs. -/
structure IsValidParallelRule [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι) : Prop where
  /-- Every chosen event occurs in the current assignment. -/
  mem : ∀ T w i, i ∈ psel T w → current vbl T w ∈ A i
  /-- Distinct steps in a batch have disjoint variable sets (in particular, no duplicates). -/
  pairwise : ∀ T w, (psel T w).Pairwise fun i j => ¬Adj vbl i j
  /-- Every occurring event shares at least one variable with some chosen event. -/
  max : ∀ T w i, current vbl T w ∈ A i → ∃ j ∈ psel T w, Adj vbl i j

/-- A valid parallel rule returns `[]` if and only if no bad event occurs in the current
assignment. -/
theorem IsValidParallelRule.eq_nil_iff [DecidableEq V] {vbl : ι → Finset V}
    {A : ι → Set (∀ v, α v)} {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (h : IsValidParallelRule vbl A psel) (T : ∀ p : V × ℕ, α p.1) (w : List ι) :
    psel T w = [] ↔ ∀ i, current vbl T w ∉ A i := by
  refine ⟨fun hnil i hi => ?_,
    fun hnone => List.eq_nil_iff_forall_not_mem.2 fun i hi => hnone i (h.mem T w i hi)⟩
  obtain ⟨j, hj, -⟩ := h.max T w i hi
  simp [hnil] at hj

/-- The cumulative resampling log (latest step first) after `n` rounds of the parallel algorithm
using selection rule `psel` on table `T`. -/
@[expose] def parallelRun (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) : ℕ → List ι
  | 0 => []
  | n + 1 => psel T (parallelRun psel T n) ++ parallelRun psel T n

@[simp]
theorem parallelRun_zero (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) :
    parallelRun psel T 0 = [] :=
  rfl

theorem parallelRun_succ (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) (n : ℕ) :
    parallelRun psel T (n + 1) = psel T (parallelRun psel T n) ++ parallelRun psel T n :=
  rfl

/-- Once a round returns `[]`, all subsequent logs remain unchanged. -/
theorem parallelRun_eq_of_eq_nil {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    {T : ∀ p : V × ℕ, α p.1} {n : ℕ} (hn : psel T (parallelRun psel T n) = []) :
    ∀ {m : ℕ}, n ≤ m → parallelRun psel T m = parallelRun psel T n := by
  intro m hm
  induction hm with
  | refl => rfl
  | step _ ih => rw [parallelRun_succ, ih, hn, List.nil_append]

/-- Once a round returns `[]`, all subsequent rounds return `[]`. -/
theorem psel_parallelRun_eq_nil_of_le {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    {T : ∀ p : V × ℕ, α p.1} {n m : ℕ} (hn : psel T (parallelRun psel T n) = [])
    (hnm : n ≤ m) :
    psel T (parallelRun psel T m) = [] := by
  rw [parallelRun_eq_of_eq_nil hn hnm, hn]

private theorem uses_append_eq_of_forall_notMem [DecidableEq V] (vbl : ι → Finset V)
    (b w : List ι) {v : V} (hv : ∀ j ∈ b, v ∉ vbl j) :
    uses vbl (b ++ w) v = uses vbl w v := by
  induction b with
  | nil => simp
  | cons j b ih =>
    simp [uses_cons, hv j List.mem_cons_self, ih fun x hx => hv x (List.mem_cons_of_mem _ hx)]

private theorem isLog_append_of_pairwise [DecidableEq V] (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (T : ∀ p : V × ℕ, α p.1) {w b : List ι} (hw : IsLog vbl A T w)
    (hmem : ∀ i ∈ b, current vbl T w ∈ A i)
    (hpw : b.Pairwise fun i j => ¬Adj vbl i j) :
    IsLog vbl A T (b ++ w) := by
  induction b with
  | nil => simpa using hw
  | cons i b ih =>
    rw [List.pairwise_cons] at hpw
    have ih' := ih (fun j hj => hmem j (List.mem_cons_of_mem _ hj)) hpw.2
    rw [List.cons_append, isLog_cons]
    refine ⟨?_, ih'⟩
    have hiw : current vbl T w ∈ A i := hmem i List.mem_cons_self
    refine (hA i (fun v hv => ?_)).mp hiw
    rw [current_apply, current_apply, uses_append_eq_of_forall_notMem vbl b w fun j hj hvj => ?_]
    exact (hpw.1 j hj) (adj_of_mem vbl hv hvj)

/-- Every finite prefix `parallelRun psel T n` produced by a valid parallel selection rule is a
valid log. -/
theorem isLog_parallelRun [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel)
    (T : ∀ p : V × ℕ, α p.1) (n : ℕ) :
    IsLog vbl A T (parallelRun psel T n) := by
  induction n with
  | zero => exact isLog_nil vbl A T
  | succ n ih =>
    exact isLog_append_of_pairwise vbl A hA T ih
      (fun i hi => hrule.mem T _ i hi) (hrule.pairwise T _)

/-- The number of non-empty parallel resampling rounds performed by `psel` on `T` (`⊤` if no
round ever returns `[]`). -/
noncomputable def parallelRounds (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (_ : psel T (parallelRun psel T n) ≠ []), ((n : ℝ≥0∞) + 1)

/-- If round `n` returns `[]`, at most `n` rounds are non-empty. -/
theorem parallelRounds_le_of_eq_nil {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    {T : ∀ p : V × ℕ, α p.1} {n : ℕ} (hn : psel T (parallelRun psel T n) = []) :
    parallelRounds psel T ≤ n := by
  refine iSup₂_le fun m hm => mod_cast Nat.succ_le_of_lt (by_contra fun hge =>
    hm (psel_parallelRun_eq_nil_of_le hn (Nat.le_of_not_lt hge)))

theorem succ_le_parallelRounds_iff (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) (k : ℕ) :
    ((k : ℝ≥0∞) + 1 ≤ parallelRounds psel T) ↔ psel T (parallelRun psel T k) ≠ [] :=
  ⟨fun hle hnil => not_lt_of_ge (hle.trans (parallelRounds_le_of_eq_nil hnil))
    (by exact_mod_cast Nat.lt_succ_self k),
   fun hne =>
    le_iSup₂ (f := fun n (_ : psel T (parallelRun psel T n) ≠ []) => ((n : ℝ≥0∞) + 1)) k hne⟩

theorem exists_eq_nil_of_parallelRounds_ne_top (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    {T : ∀ p : V × ℕ, α p.1} (hfin : parallelRounds psel T ≠ ⊤) :
    ∃ n : ℕ, psel T (parallelRun psel T n) = [] := by
  by_contra! hne
  refine hfin (eq_top_iff.mpr <| le_of_forall_lt fun c hc => ?_)
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hc.ne_top
  exact hn.trans_le (le_self_add.trans ((succ_le_parallelRounds_iff psel T n).2 (hne n)))

theorem parallelRounds_eq_tsum (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) :
    parallelRounds psel T =
      ∑' k : ℕ, if psel T (parallelRun psel T k) ≠ [] then (1 : ℝ≥0∞) else 0 := by
  classical
  by_cases hterm : ∃ n, psel T (parallelRun psel T n) = []
  · let n₀ := Nat.find hterm
    have hn₀ : psel T (parallelRun psel T n₀) = [] := Nat.find_spec hterm
    rw [tsum_eq_sum (s := Finset.range n₀) fun k hk => by
        simp [psel_parallelRun_eq_nil_of_le hn₀ (not_lt.1 (Finset.mem_range.not.1 hk))],
      Finset.sum_congr (g := fun _ => (1 : ℝ≥0∞)) rfl fun k hk => by
        simp [Nat.find_min hterm (Finset.mem_range.1 hk)]]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    refine le_antisymm (parallelRounds_le_of_eq_nil hn₀) ?_
    cases hn₀_eq : n₀ with
    | zero => simp
    | succ m =>
      exact_mod_cast (succ_le_parallelRounds_iff psel T m).2 (Nat.find_min hterm (by omega))
  · push Not at hterm
    simp only [ne_eq, hterm, not_false_eq_true, ↓reduceIte,
      ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
    exact not_ne_iff.mp fun hfin => (exists_eq_nil_of_parallelRounds_ne_top psel hfin).elim hterm

/-- A run whose rounds are never empty resamples at least one event per round. -/
private theorem le_length_parallelRun_of_forall
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι} {T : ∀ p : V × ℕ, α p.1}
    (h : ∀ n, psel T (parallelRun psel T n) ≠ []) :
    ∀ n, n ≤ (parallelRun psel T n).length
  | 0 => Nat.zero_le _
  | n + 1 => by
    rw [parallelRun_succ, List.length_append]
    linarith [List.length_pos_of_ne_nil (h n), le_length_parallelRun_of_forall h n]

end ParallelExecution

section GreedyMIS

variable {V ι : Type*} {α : V → Type*} [DecidableEq V] [DecidableEq ι]

/-- Greedy maximal independent subset of candidates `cand` satisfying Boolean predicate `P`,
scanning right-to-left and accepting each candidate that satisfies `P` and is distinct from and
variable-disjoint from all already-selected elements. -/
@[expose] def greedyIndependentSubset (vbl : ι → Finset V) (P : ι → Bool) : List ι → List ι
  | [] => []
  | i :: is =>
      let rest := greedyIndependentSubset vbl P is
      if P i && rest.all (fun j => decide (i ≠ j) && decide (Disjoint (vbl i) (vbl j))) then
        i :: rest
      else
        rest

private theorem greedyIndependentSubset_mem (vbl : ι → Finset V) (P : ι → Bool)
    (cand : List ι) {i : ι} (hi : i ∈ greedyIndependentSubset vbl P cand) :
    i ∈ cand ∧ P i = true := by
  induction cand with
  | nil => simp [greedyIndependentSubset] at hi
  | cons x xs ih =>
    simp only [greedyIndependentSubset] at hi
    split_ifs at hi with hcond
    · rcases List.mem_cons.1 hi with rfl | hxs
      · exact ⟨List.mem_cons_self, (Eq.mp (Bool.and_eq_true _ _) hcond).1⟩
      · exact (ih hxs).imp_left (List.mem_cons_of_mem _)
    · exact (ih hi).imp_left (List.mem_cons_of_mem _)

private theorem greedyIndependentSubset_pairwise (vbl : ι → Finset V) (P : ι → Bool)
    (cand : List ι) :
    (greedyIndependentSubset vbl P cand).Pairwise fun i j => ¬Adj vbl i j := by
  induction cand with
  | nil => simp [greedyIndependentSubset]
  | cons x xs ih =>
    simp only [greedyIndependentSubset]
    split_ifs with hcond
    · rw [Bool.and_eq_true, List.all_eq_true] at hcond
      refine List.pairwise_cons.mpr ⟨fun j hj => ?_, ih⟩
      simpa [adj_iff, not_or] using hcond.2 j hj
    · exact ih

private theorem greedyIndependentSubset_max (vbl : ι → Finset V) (P : ι → Bool)
    (cand : List ι) {i : ι} (hic : i ∈ cand) (hiP : P i = true) :
    ∃ j ∈ greedyIndependentSubset vbl P cand, Adj vbl i j := by
  induction cand with
  | nil => simp at hic
  | cons x xs ih =>
    simp only [greedyIndependentSubset]
    rcases List.mem_cons.1 hic with rfl | hixs
    · split_ifs with hcond
      · exact ⟨i, List.mem_cons_self, adj_refl vbl i⟩
      · by_contra hno
        refine hcond ?_
        simp only [hiP, Bool.true_and, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact fun j hj => by simpa [adj_iff, not_or] using fun h => hno ⟨j, hj, h⟩
    · obtain ⟨j, hj, hadj⟩ := ih hixs
      split_ifs <;> exact ⟨j, by simp [hj], hadj⟩

/-- Computable greedy maximal independent set parallel selection rule over an explicit candidate
list `cand` and Boolean event detector `occur`. -/
@[expose] def greedyParallelList (vbl : ι → Finset V) (cand : List ι)
    (occur : (∀ v, α v) → ι → Bool) (T : ∀ p : V × ℕ, α p.1) (w : List ι) : List ι :=
  greedyIndependentSubset vbl (fun i => occur (current vbl T w) i) cand

theorem isValidParallelRule_greedyParallelList (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (cand : List ι) (hcand : ∀ i, i ∈ cand) (occur : (∀ v, α v) → ι → Bool)
    (hoccur : ∀ a i, occur a i = true ↔ a ∈ A i) :
    IsValidParallelRule vbl A (greedyParallelList vbl cand occur) where
  mem _ _ i hi := (hoccur _ i).1 (greedyIndependentSubset_mem vbl _ cand hi).2
  pairwise _ _ := greedyIndependentSubset_pairwise vbl _ cand
  max _ _ i hi := greedyIndependentSubset_max vbl _ cand (hcand i) ((hoccur _ i).2 hi)

/-- Noncomputable canonical greedy maximal independent set parallel selection rule for finite
event index types `ι`. -/
noncomputable def greedyParallel [Fintype ι] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (T : ∀ p : V × ℕ, α p.1) (w : List ι) : List ι :=
  open Classical in
  greedyParallelList vbl (Finset.univ : Finset ι).toList (fun a i => decide (a ∈ A i)) T w

theorem isValidParallelRule_greedyParallel [Fintype ι] (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) :
    IsValidParallelRule vbl A (greedyParallel vbl A) := by
  classical
  exact isValidParallelRule_greedyParallelList vbl A (Finset.univ : Finset ι).toList
    (fun i => Finset.mem_toList.2 (Finset.mem_univ i))
    (fun a i => decide (a ∈ A i)) (fun _ _ => decide_eq_true_iff)

end GreedyMIS

section WitnessDepth

variable {V ι : Type*} {α : V → Type*}

private def pushList (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    (b : List ι) (S : Finset (ι × ℕ)) : Finset (ι × ℕ) :=
  b.foldl (fun S' j => pushRel R j S') S

private theorem subset_pushRel (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    (j : ι) (S : Finset (ι × ℕ)) :
    S ⊆ pushRel R j S := by
  by_cases hj : levelRel R j S = 0
  · rw [pushRel_of_eq_zero hj]
  · exact pushRel_of_ne_zero hj ▸ subset_insert _ _

private theorem subset_pushList (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    (b : List ι) (S : Finset (ι × ℕ)) :
    S ⊆ pushList R b S := by
  induction b generalizing S with
  | nil => exact Subset.rfl
  | cons j b ih =>
    exact (subset_pushRel R j S).trans (ih _)

private theorem pushList_append (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    (a b : List ι) (S : Finset (ι × ℕ)) :
    pushList R (a ++ b) S = pushList R b (pushList R a S) :=
  List.foldl_append

private theorem levelRel_pushRel_of_not_rel (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    {x y : ι} (hxy : ¬R x y) (S : Finset (ι × ℕ)) :
    levelRel R y (pushRel R x S) = levelRel R y S := by
  by_cases hx : levelRel R x S = 0
  · rw [pushRel_of_eq_zero hx]
  · rw [pushRel_of_ne_zero hx, levelRel_insert_of_not_rel hxy]

private theorem mem_pushList_spec (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    {b : List ι} (hpw : b.Pairwise fun x y => ¬R x y) (S : Finset (ι × ℕ)) :
    (∀ p ∈ pushList R b S,
        p ∈ S ∨ ∃ j ∈ b, levelRel R j S ≠ 0 ∧ p = (j, levelRel R j S)) ∧
      (∀ j ∈ b, levelRel R j S ≠ 0 → (j, levelRel R j S) ∈ pushList R b S) := by
  induction b generalizing S with
  | nil => simp [pushList]
  | cons x b ih =>
    rw [List.pairwise_cons] at hpw
    have ih' := ih hpw.2 (pushRel R x S)
    have hlev : ∀ y ∈ b, levelRel R y (pushRel R x S) = levelRel R y S := fun y hy =>
      levelRel_pushRel_of_not_rel R (hpw.1 y hy) S
    constructor
    · intro p hp
      rcases ih'.1 p hp with hp1 | ⟨j, hjb, hne, rfl⟩
      · by_cases hx : levelRel R x S = 0
        · exact Or.inl (pushRel_of_eq_zero hx ▸ hp1)
        · rcases mem_insert.1 (pushRel_of_ne_zero hx ▸ hp1) with rfl | hpS
          · exact Or.inr ⟨x, List.mem_cons_self, hx, rfl⟩
          · exact Or.inl hpS
      · rw [hlev j hjb] at hne ⊢
        exact Or.inr ⟨j, List.mem_cons_of_mem _ hjb, hne, rfl⟩
    · intro j hj hne
      rcases List.mem_cons.1 hj with rfl | hjb
      · exact subset_pushList R b (pushRel R j S)
          ((pushRel_of_ne_zero hne).symm ▸ mem_insert_self _ _)
      · rw [← hlev j hjb] at hne ⊢
        exact ih'.2 j hjb hne

private theorem witnessRel_prefix_eq_singleton (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    {i : ι} {suff : List ι} (hsuff : ∀ j ∈ suff, ¬R i j) :
    witnessRel R i suff = {(i, 0)} := by
  induction suff with
  | nil => exact witnessRel_nil R i
  | cons j suff ih =>
    rw [witnessRel_cons_of_not_rel R (hsuff j List.mem_cons_self)]
    exact ih fun x hx => hsuff x (List.mem_cons_of_mem _ hx)

private theorem witnessRel_append_eq_pushList (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    {i : ι} {suff : List ι} (hsuff : ∀ j ∈ suff, ¬R i j) (w : List ι) :
    witnessRel R i (suff ++ w) = pushList R w {(i, 0)} := by
  induction w using List.reverseRecOn with
  | nil =>
    rw [List.append_nil, pushList, List.foldl_nil, witnessRel_prefix_eq_singleton R hsuff]
  | append_singleton w j ih =>
    rw [← List.append_assoc, witnessRel_append_singleton, ih, pushList_append]
    simp [pushList]

private theorem parallel_step_adj [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) (T : ∀ p : V × ℕ, α p.1) (m : ℕ)
    {i : ι} (hi : i ∈ psel T (parallelRun psel T (m + 1))) :
    ∃ j ∈ psel T (parallelRun psel T m), Adj vbl i j := by
  have hi_occ : current vbl T (parallelRun psel T (m + 1)) ∈ A i :=
    hrule.mem T (parallelRun psel T (m + 1)) i hi
  by_cases hm_occ : current vbl T (parallelRun psel T m) ∈ A i
  · exact hrule.max T (parallelRun psel T m) i hm_occ
  · by_contra! hdisj
    refine hm_occ ((hA i fun v hv => ?_).mp hi_occ)
    rw [parallelRun_succ, current_apply, current_apply,
      uses_append_eq_of_forall_notMem vbl _ _ fun j hj hvj => hdisj j hj (adj_of_mem vbl hv hvj)]

private def batchSlice (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) (r : ℕ) : ℕ → List ι
  | 0 => []
  | d + 1 => psel T (parallelRun psel T (r + d)) ++ batchSlice psel T r d

private theorem batchSlice_zero_eq_parallelRun
    (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι) (T : ∀ p : V × ℕ, α p.1) (k : ℕ) :
    batchSlice psel T 0 k = parallelRun psel T k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [batchSlice, zero_add, ih, parallelRun_succ]

private theorem batchSlice_succ_right
    (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι) (T : ∀ p : V × ℕ, α p.1) (r d : ℕ) :
    batchSlice psel T r (d + 1) =
      batchSlice psel T (r + 1) d ++ psel T (parallelRun psel T r) := by
  induction d generalizing r with
  | zero => simp [batchSlice]
  | succ d ih =>
    rw [batchSlice, ← Nat.add_assoc, Nat.add_right_comm r d 1, ih r, ← List.append_assoc]; rfl

private theorem pushList_batchSlice_depth [DecidableEq V] [DecidableEq ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) (T : ∀ p : V × ℕ, α p.1) :
    ∀ (d r t : ℕ) (S : Finset (ι × ℕ)),
      (∀ p ∈ S, p.2 ≤ t) →
      (∃ p ∈ S, p.2 = t ∧ p.1 ∈ psel T (parallelRun psel T (r + d))) →
      (∀ p ∈ pushList (Adj vbl) (batchSlice psel T r d) S, p.2 ≤ t + d) ∧
        (∃ p ∈ pushList (Adj vbl) (batchSlice psel T r d) S,
          p.2 = t + d ∧ p.1 ∈ psel T (parallelRun psel T r)) := by
  intro d
  induction d with
  | zero => exact fun _ _ _ hle hex => ⟨hle, hex⟩
  | succ d ih =>
    intro r t S hle hex
    rw [batchSlice_succ_right, pushList_append]
    obtain ⟨hle', ⟨p, hpS', hpt, hp_in⟩⟩ := ih (r + 1) t S hle
      (by rwa [← Nat.add_assoc, Nat.add_right_comm] at hex)
    obtain ⟨j, hj, hadj⟩ := parallel_step_adj vbl A hA hrule T r hp_in
    set S' := pushList (Adj vbl) (batchSlice psel T (r + 1) d) S
    have hspec := mem_pushList_spec (Adj vbl) (hrule.pairwise T (parallelRun psel T r)) S'
    have hj_bound (x : ι) : levelRel (Adj vbl) x S' ≤ t + d + 1 := by
      by_cases hl0 : levelRel (Adj vbl) x S' = 0
      · omega
      · obtain ⟨q, hq, hql, -⟩ := exists_of_levelRel_ne_zero hl0
        linarith [hle' q hq]
    have hjeq : levelRel (Adj vbl) j S' = t + d + 1 :=
      le_antisymm (hj_bound j) (hpt ▸ lt_levelRel hpS' hadj)
    refine ⟨fun q hq => ?_, (j, t + (d + 1)), hjeq ▸ hspec.2 j hj (by omega), rfl, hj⟩
    rcases hspec.1 q hq with hq' | ⟨x, -, -, rfl⟩
    · exact (hle' q hq').trans (by omega)
    · exact (hj_bound x).trans (by omega)

/-- **Parallel witness-tree depth lemma** [MoserTardos2010, Lemma 4.1]: if round `k` selects a
non-empty batch containing `i` (with suffix `suff` after `i` in that batch), then the witness
structure `witness vbl i (suff ++ parallelRun psel T k)` lies in `shapes vbl i k`, is proper,
passes its check on `T`, and contains a vertex at depth `k` (hence has cardinality `≥ k + 1`). -/
theorem parallel_witness_depth [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) (T : ∀ p : V × ℕ, α p.1) (k : ℕ)
    {i : ι} {pref suff : List ι}
    (hsplit : psel T (parallelRun psel T k) = pref ++ i :: suff) :
    let S := witness vbl i (suff ++ parallelRun psel T k)
    S ∈ shapes vbl i k ∧ Proper vbl S ∧ Check vbl A S T ∧ (∃ p ∈ S, p.2 = k) ∧ k + 1 ≤ #S := by
  intro S
  have hpw : (psel T (parallelRun psel T k)).Pairwise fun x y => ¬Adj vbl x y :=
    hrule.pairwise T (parallelRun psel T k)
  rw [hsplit, List.pairwise_append] at hpw
  have hi_suff : ∀ j ∈ suff, ¬Adj vbl i j := (List.pairwise_cons.1 hpw.2.1).1
  have hS_eq : S = pushList (Adj vbl) (batchSlice psel T 0 k) {(i, 0)} := by
    change witness vbl i (suff ++ parallelRun psel T k) = _
    rw [witness_eq_witnessRel, witnessRel_append_eq_pushList (Adj vbl) hi_suff,
      batchSlice_zero_eq_parallelRun]
  have hdepth := pushList_batchSlice_depth vbl A hA hrule T k 0 0 {(i, 0)}
    (fun p hp => by simp [mem_singleton.1 hp])
    ⟨(i, 0), mem_singleton_self _, rfl, by rw [zero_add, hsplit]; simp⟩
  rw [zero_add, ← hS_eq] at hdepth
  have hroot : RootedRel (Adj vbl) i S := by
    dsimp only [S]
    exact witness_eq_witnessRel (vbl := vbl) i _ ▸ rooted_witnessRel (Adj vbl) i _
  have hshape : S ∈ shapes vbl i k :=
    shapes_eq_shapesRel (vbl := vbl) i k ▸ mem_shapesRel (Adj vbl) k hroot hdepth.1
  have hprop : Proper vbl S := proper_witness vbl i _
  have hchk : Check vbl A S T := check_witness vbl A hA i _ T <| by
    simpa using isLog_append_of_pairwise vbl A hA T (isLog_parallelRun vbl A hA hrule T k)
      (fun x hx => hrule.mem T _ x (hsplit ▸ List.mem_append_right _ hx)) hpw.2.1
  obtain ⟨p, hp, hpk, -⟩ := hdepth.2
  have hlevels (t : ℕ) : ∀ q ∈ S, q.2 = t → ∀ d ≤ t, ∃ q ∈ S, q.2 = d := by
    induction t with
    | zero => exact fun q hqS _ _ _ => ⟨q, hqS, by omega⟩
    | succ t iht =>
      intro q hqS hqt d hdt
      rcases Nat.eq_or_lt_of_le hdt with rfl | hlt
      · exact ⟨q, hqS, hqt⟩
      · obtain ⟨r, hrS, hrt, -⟩ := hroot.parent q hqS (by omega)
        exact iht r hrS (by omega) d (by omega)
  have hcard : k + 1 ≤ #S :=
    calc k + 1 = #(Finset.range (k + 1)) := (card_range (k + 1)).symm
      _ ≤ #(S.image Prod.snd) := card_le_card fun d hd => by
          obtain ⟨q, hqS, rfl⟩ := hlevels k p hp hpk d (Nat.lt_succ_iff.1 (mem_range.1 hd))
          exact mem_image_of_mem Prod.snd hqS
      _ ≤ #S := card_image_le
  exact ⟨hshape, hprop, hchk, ⟨p, hp, hpk⟩, hcard⟩

end WitnessDepth

section Expectation

variable {V ι : Type*} {α : V → Type*} [∀ v, MeasurableSpace (α v)]

private def parallelEvent [DecidableEq V] [DecidableEq ι] [Fintype ι] (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) (k : ℕ) : Set (∀ p : V × ℕ, α p.1) :=
  {T | ∃ i : ι, ∃ S ∈ shapes vbl i k, Proper vbl S ∧ k + 1 ≤ #S ∧ Check vbl A S T}

private theorem measurableSet_parallelEvent [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i)) (k : ℕ) :
    MeasurableSet (parallelEvent vbl A k) := by
  convert MeasurableSet.iUnion fun i => MeasurableSet.biUnion (shapes vbl i k).countable_toSet
    fun S _ => MeasurableSet.iUnion fun (_ : Proper vbl S) =>
      MeasurableSet.iUnion fun (_ : k + 1 ≤ #S) => measurableSet_check vbl A hAm S using 1
  ext T
  simp only [parallelEvent, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]; tauto

omit [∀ v, MeasurableSpace (α v)] in
private theorem mem_parallelEvent_of_psel_ne_nil [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) {T : ∀ p : V × ℕ, α p.1} {k : ℕ}
    (hne : psel T (parallelRun psel T k) ≠ []) :
    T ∈ parallelEvent vbl A k := by
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨pref, suff, hsplit⟩ := List.append_of_mem hi
  obtain ⟨hshape, hprop, hchk, -, hcard⟩ := parallel_witness_depth vbl A hA hrule T k hsplit
  exact ⟨i, witness vbl i (suff ++ parallelRun psel T k), hshape, hprop, hcard, hchk⟩

private theorem table_parallelEvent_le [Fintype V] [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    (k : ℕ) :
    table μ (parallelEvent vbl A k) ≤
      ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∑ i : ι, x i / (1 - x i)) := by
  classical
  have h1e0 : 0 ≤ 1 - ε := sub_nonneg.2 hε.2
  have hy0 : ∀ i, 0 ≤ x i * ∏ j ∈ Γ i, (1 - x j) := fun i =>
    mul_nonneg (hx i).1 (Finset.prod_nonneg fun j _ => sub_nonneg.2 (hx j).2.le)
  have hterm : ∀ S : Finset (ι × ℕ),
      0 ≤ (1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j)) := fun S =>
    mul_nonneg (pow_nonneg h1e0 _) (Finset.prod_nonneg fun _ _ => hy0 _)
  have hsub : parallelEvent vbl A k ⊆
      ⋃ i : ι, ⋃ S ∈ (shapes vbl i k).filter (fun S => Proper vbl S ∧ k + 1 ≤ #S),
        {T | Check vbl A S T} := by
    intro T ⟨i, S, hS, hprop, hcard, hchk⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_biUnion (mem_filter.2 ⟨hS, hprop, hcard⟩) hchk⟩
  calc table μ (parallelEvent vbl A k)
      ≤ ∑ i : ι, ∑ S ∈ (shapes vbl i k).filter (fun S => Proper vbl S ∧ k + 1 ≤ #S),
          table μ {T | Check vbl A S T} :=
        (measure_mono hsub).trans <| (measure_iUnion_fintype_le _ _).trans <|
          Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ i : ι, ∑ S ∈ shapes vbl i k,
          ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j))) := by
        refine Finset.sum_le_sum fun i _ => (Finset.sum_le_sum fun S hS => ?_).trans
          (Finset.sum_le_sum_of_subset (filter_subset _ _))
        obtain ⟨-, hprop, hcard⟩ := mem_filter.1 hS
        rw [measure_check_eq_prod μ vbl A hAm hA hprop,
          ← Finset.prod_congr rfl fun p _ => ofReal_measureReal,
          ← ENNReal.ofReal_prod_of_nonneg fun _ _ => measureReal_nonneg]
        refine ENNReal.ofReal_le_ofReal ((Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg)
          fun p _ => hP p.1).trans ?_)
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one h1e0 (by linarith [hε.1]) hcard)
          (Finset.prod_nonneg fun p _ => hy0 p.1)
    _ ≤ ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∑ i : ι, x i / (1 - x i)) := by
        have hinner : ∀ i : ι, ∑ S ∈ shapes vbl i k,
            ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j))) =
            ENNReal.ofReal (∑ S ∈ shapes vbl i k,
              (1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j))) := fun i =>
          (ENNReal.ofReal_sum_of_nonneg fun S _ => hterm S).symm
        simp_rw [hinner]
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hterm _]
        refine ENNReal.ofReal_le_ofReal ?_
        simp_rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
          sum_prod_shapes_le vbl Γ hΓ hx hy0 (fun _ => le_rfl) i k) (pow_nonneg h1e0 _)

/-- **Parallel Moser–Tardos tail bound** ([MoserTardos2010, Section 4]): under
`Pr[A i] ≤ (1 - ε) * x i * ∏ j ∈ Γ i, (1 - x j)` with `ε ∈ (0, 1]`, for every admissible
parallel selection rule `psel`, the probability that the algorithm performs at least `k + 1`
parallel rounds is at most `(1 - ε) ^ (k + 1) * ∑ i, x i / (1 - x i)`. -/
theorem table_succ_le_parallelRounds_le [Fintype V] [DecidableEq V] [Fintype ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) (k : ℕ) :
    table μ {T | (k : ℝ≥0∞) + 1 ≤ parallelRounds psel T} ≤
      ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∑ i : ι, x i / (1 - x i)) := by
  classical
  refine (measure_mono fun T hT => ?_).trans
    (table_parallelEvent_le μ vbl A hAm hA Γ hΓ hx hε hP k)
  exact mem_parallelEvent_of_psel_ne_nil vbl A hA hrule
    ((succ_le_parallelRounds_iff psel T k).1 hT)

private theorem tsum_min_one_split_bound {ε M : ℝ} (hr0 : 0 ≤ 1 - ε)
    (hr1 : 1 - ε < 1) (N : ℕ) (hrN : (1 - ε) ^ (N + 1) * M ≤ 1) :
    (∑' k : ℕ, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (k + 1) * M))) ≤
      (N : ℝ≥0∞) + ENNReal.ofReal (1 / ε) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  by_cases hn : n ≤ N
  · calc ∑ _k ∈ Finset.range n, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (_k + 1) * M))
        ≤ ∑ _k ∈ Finset.range n, (1 : ℝ≥0∞) := Finset.sum_le_sum fun _ _ => min_le_left _ _
      _ = (n : ℝ≥0∞) := by simp
      _ ≤ (N : ℝ≥0∞) := Nat.cast_le.mpr hn
      _ ≤ (N : ℝ≥0∞) + ENNReal.ofReal (1 / ε) := le_self_add
  · have hNn : N ≤ n := Nat.le_of_not_le hn
    rw [← Nat.add_sub_cancel' hNn, Finset.sum_range_add]
    refine add_le_add ?_ ?_
    · calc ∑ _k ∈ Finset.range N, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (_k + 1) * M))
          ≤ ∑ _k ∈ Finset.range N, (1 : ℝ≥0∞) := Finset.sum_le_sum fun _ _ => min_le_left _ _
        _ = (N : ℝ≥0∞) := by simp
    · have htail : ∀ m : ℕ,
          min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (N + m + 1) * M)) ≤
            ENNReal.ofReal ((1 - ε) ^ m) := fun m => by
        refine (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal ?_)
        calc (1 - ε) ^ (N + m + 1) * M
            = ((1 - ε) ^ (N + 1) * M) * (1 - ε) ^ m := by
              rw [Nat.add_right_comm N m 1, pow_add]; ring
          _ ≤ 1 * (1 - ε) ^ m := mul_le_mul_of_nonneg_right hrN (pow_nonneg hr0 _)
          _ = (1 - ε) ^ m := one_mul _
      calc ∑ m ∈ Finset.range (n - N),
              min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (N + m + 1) * M))
          ≤ ∑ m ∈ Finset.range (n - N), ENNReal.ofReal ((1 - ε) ^ m) :=
            Finset.sum_le_sum fun m _ => htail m
        _ = ENNReal.ofReal (∑ m ∈ Finset.range (n - N), (1 - ε) ^ m) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun m _ => pow_nonneg hr0 m]
        _ ≤ ENNReal.ofReal (∑' m : ℕ, (1 - ε) ^ m) :=
            ENNReal.ofReal_le_ofReal ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum
              (Finset.range (n - N)) fun m _ => pow_nonneg hr0 m)
        _ = ENNReal.ofReal (1 / ε) := by
            rw [tsum_geometric_of_lt_one hr0 hr1, sub_sub_self, one_div]

private theorem tsum_min_one_ofReal_pow_mul_le {ε M : ℝ} (hε : ε ∈ Set.Ioc 0 1) (hM : 0 ≤ M) :
    (∑' k : ℕ, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (k + 1) * M))) ≤
      ENNReal.ofReal ((max 0 (Real.log M) + 1) / ε) := by
  have h1e0 : 0 ≤ 1 - ε := sub_nonneg.2 hε.2
  rcases eq_or_lt_of_le hε.2 with rfl | hε_lt
  · simp
  have hr_pos : 0 < 1 - ε := sub_pos.2 hε_lt
  have hr_lt : 1 - ε < 1 := sub_lt_self _ hε.1
  rcases le_or_gt M 1 with hM1 | hM1
  · rw [max_eq_left (Real.log_nonpos hM hM1), zero_add]
    simpa using tsum_min_one_split_bound h1e0 hr_lt 0
      (by rw [zero_add, pow_one]; nlinarith [hε.1])
  have hMpos : 0 < M := zero_lt_one.trans hM1
  have hlog_pos : 0 < Real.log M := Real.log_pos hM1
  rw [max_eq_right hlog_pos.le]
  let a := -Real.log (1 - ε)
  have ha_ge : ε ≤ a := by linarith [Real.log_le_sub_one_of_pos hr_pos]
  have ha_pos : 0 < a := hε.1.trans_le ha_ge
  obtain ⟨N, hN_le_a, hN_lt⟩ :
      ∃ N : ℕ, (N : ℝ) ≤ Real.log M / a ∧ Real.log M / a < (N : ℝ) + 1 :=
    ⟨_, Nat.floor_le (div_nonneg hlog_pos.le ha_pos.le), Nat.lt_floor_add_one _⟩
  have hrN_le : (1 - ε) ^ (N + 1) * M ≤ 1 := by
    have hlt_mul : Real.log M < ((N : ℝ) + 1) * a := (div_lt_iff₀ ha_pos).1 hN_lt
    refine ((Real.log_neg_iff (mul_pos (pow_pos hr_pos _) hMpos)).1 ?_).le
    rw [Real.log_mul (pow_pos hr_pos _).ne' hMpos.ne', Real.log_pow]
    push_cast
    linarith
  calc (∑' k : ℕ, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (k + 1) * M)))
      ≤ ENNReal.ofReal (N : ℝ) + ENNReal.ofReal (1 / ε) := by
        simpa using tsum_min_one_split_bound h1e0 hr_lt N hrN_le
    _ ≤ ENNReal.ofReal ((Real.log M + 1) / ε) := by
        rw [← ENNReal.ofReal_add (Nat.cast_nonneg N) (div_nonneg zero_le_one hε.1.le), add_div]
        exact ENNReal.ofReal_le_ofReal (add_le_add_left
          (hN_le_a.trans (div_le_div_of_nonneg_left hlog_pos.le hε.1 ha_ge)) _)

private noncomputable def parallelEventSum [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (T : ∀ p : V × ℕ, α p.1) : ℝ≥0∞ :=
  ∑' k : ℕ, (parallelEvent vbl A k).indicator (fun _ => (1 : ℝ≥0∞)) T

private theorem measurable_parallelEventSum [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i)) :
    Measurable (parallelEventSum vbl A) :=
  Measurable.tsum fun k =>
    measurable_const.indicator (measurableSet_parallelEvent vbl A hAm k)

omit [∀ v, MeasurableSpace (α v)] in
private theorem parallelRounds_le_parallelEventSum [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) (T : ∀ p : V × ℕ, α p.1) :
    parallelRounds psel T ≤ parallelEventSum vbl A T := by
  rw [parallelRounds_eq_tsum, parallelEventSum]
  refine tsum_le_tsum fun k => ?_
  split_ifs with hne
  · rw [Set.indicator_of_mem (mem_parallelEvent_of_psel_ne_nil vbl A hA hrule hne)]
  · exact zero_le

private theorem lintegral_parallelEventSum_eq [DecidableEq V] [DecidableEq ι]
    [Fintype ι] (μ : ∀ v, Measure (α v))
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i)) :
    ∫⁻ T, parallelEventSum vbl A T ∂table μ = ∑' k : ℕ, table μ (parallelEvent vbl A k) := by
  unfold parallelEventSum
  rw [lintegral_tsum fun k =>
    (measurable_const.indicator (measurableSet_parallelEvent vbl A hAm k)).aemeasurable]
  refine tsum_congr fun k => ?_
  rw [lintegral_indicator (measurableSet_parallelEvent vbl A hAm k), setLIntegral_one]

private theorem lintegral_parallelEventSum_le [Fintype V] [DecidableEq V] [DecidableEq ι]
    [Fintype ι] (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j))) :
    ∫⁻ T, parallelEventSum vbl A T ∂table μ ≤
      ENNReal.ofReal ((max 0 (Real.log (∑ i : ι, x i / (1 - x i))) + 1) / ε) := by
  rw [lintegral_parallelEventSum_eq μ vbl A hAm]
  exact (tsum_le_tsum fun k => le_min ((measure_mono (Set.subset_univ _)).trans (by simp))
      (table_parallelEvent_le μ vbl A hAm hA Γ hΓ hx hε hP k)).trans
    (tsum_min_one_ofReal_pow_mul_le hε <|
      Finset.sum_nonneg fun i _ => div_nonneg (hx i).1 (sub_pos.2 (hx i).2).le)

/-- **Parallel Moser–Tardos theorem** [MoserTardos2010, Theorem 1.3]: under
`Pr[A i] ≤ (1 - ε) * x i * ∏ j ∈ Γ i, (1 - x j)` with `ε ∈ (0, 1]`, any admissible parallel
selection rule terminates in at most `(max 0 (Real.log (∑ i, x i / (1 - x i))) + 1) / ε`
expected parallel rounds.

The rule is not assumed measurable, so `∫⁻` is the lower Lebesgue integral. As in the sequential
theorem, `exists_measurable_ge_parallelRounds` dominates `parallelRounds psel` for every valid
parallel rule by a single measurable function of the table with the same expected bound. -/
theorem lintegral_parallelRounds_le [Fintype V] [DecidableEq V] [Fintype ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table μ ≤
      ENNReal.ofReal ((max 0 (Real.log (∑ i : ι, x i / (1 - x i))) + 1) / ε) := by
  classical
  exact (lintegral_mono (parallelRounds_le_parallelEventSum vbl A hA hrule)).trans
    (lintegral_parallelEventSum_le μ vbl A hAm hA Γ hΓ hx hε hP)

/-- **Theorem 1.3 for the outer expectation** [MoserTardos2010]: under the slack local-lemma
hypothesis there is a measurable function `g` of the table, with
`∫⁻ g ≤ (max 0 (Real.log (∑ i, x i / (1 - x i))) + 1) / ε`, that bounds `parallelRounds psel`
for every valid parallel selection rule `psel`. So the bound holds for the upper (outer)
expectation of the number of rounds as well, whether or not the rule is measurable. -/
theorem exists_measurable_ge_parallelRounds [Fintype V] [DecidableEq V] [Fintype ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j))) :
    ∃ g : (∀ p : V × ℕ, α p.1) → ℝ≥0∞, Measurable g ∧
      ∫⁻ T, g T ∂table μ ≤
        ENNReal.ofReal ((max 0 (Real.log (∑ i : ι, x i / (1 - x i))) + 1) / ε) ∧
      ∀ psel : (∀ p : V × ℕ, α p.1) → List ι → List ι,
        IsValidParallelRule vbl A psel → ∀ T, parallelRounds psel T ≤ g T := by
  classical
  exact ⟨parallelEventSum vbl A, measurable_parallelEventSum vbl A hAm,
    lintegral_parallelEventSum_le μ vbl A hAm hA Γ hΓ hx hε hP,
    fun _ hrule T => parallelRounds_le_parallelEventSum vbl A hA hrule T⟩

/-- **Termination of the parallel algorithm, generic form.** If every event's largest count in a
valid log has finite expectation, then almost surely every admissible parallel rule reaches an
empty batch after finitely many rounds. No slack is needed: the run's logs are valid
(`isLog_parallelRun`) and grow in every non-empty round, while
`ae_exists_forall_isLog_length_le_of_bound` bounds the length of every valid log. -/
theorem ae_exists_parallelRun_eq_nil_of_bound [DecidableEq V] [Finite ι]
    (μ : ∀ v, Measure (α v)) (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (hc : ∀ [DecidableEq ι] (i : ι),
      ∫⁻ T, ⨆ (w : List ι) (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞) ∂table μ ≠ ⊤)
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table μ, ∃ n : ℕ, psel T (parallelRun psel T n) = [] := by
  filter_upwards [ae_exists_forall_isLog_length_le_of_bound μ vbl A hAm hc] with T ⟨N, hN⟩
  by_contra! hne
  exact Nat.not_succ_le_self N ((le_length_parallelRun_of_forall hne (N + 1)).trans
    (hN _ (isLog_parallelRun vbl A hA hrule T (N + 1))))

/-- Under the local-lemma hypothesis `Pr[A i] ≤ x i * ∏ j ∈ Γ i, (1 - x j)` of Theorem 1.2,
without the slack `1 - ε` that Theorem 1.3 needs for its round bound, almost surely every
admissible parallel rule reaches an empty batch after finitely many rounds. This is a consequence
of the valid-log bound `lintegral_iSup_count_le` through `ae_exists_parallelRun_eq_nil_of_bound`.
Moser and Tardos make the same observation when they introduce Algorithm 1.2
[MoserTardos2010, Section 1]: the parallel algorithm "can be considered a special case of the
sequential algorithm, so the statement of Theorem 1.2 applies to the parallel version too". -/
theorem ae_exists_parallelRun_eq_nil [Fintype V] [DecidableEq V] [Finite ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table μ, ∃ n : ℕ, psel T (parallelRun psel T n) = [] :=
  ae_exists_parallelRun_eq_nil_of_bound μ vbl A hAm hA
    (fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i))
    hrule

/-- Under the local-lemma hypothesis of Theorem 1.2 (no slack), `parallelRounds psel T < ⊤` almost
surely for every admissible parallel rule `psel`. -/
theorem ae_parallelRounds_ne_top [Fintype V] [DecidableEq V] [Finite ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table μ, parallelRounds psel T ≠ ⊤ :=
  (ae_exists_parallelRun_eq_nil μ vbl A hAm hA Γ hΓ hx hP hrule).mono fun _ ⟨n, hn⟩ =>
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (parallelRounds_le_of_eq_nil hn)

/-- Under the local-lemma hypothesis of Theorem 1.2 (no slack), almost surely every admissible
parallel rule reaches an assignment avoiding all bad events in finitely many parallel rounds. -/
theorem ae_exists_forall_notMem_parallelRun [Fintype V] [DecidableEq V] [Finite ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table μ, ∃ n : ℕ, ∀ i, current vbl T (parallelRun psel T n) ∉ A i :=
  (ae_exists_parallelRun_eq_nil μ vbl A hAm hA Γ hΓ hx hP hrule).mono
    fun T ⟨n, hn⟩ => ⟨n, (hrule.eq_nil_iff T _).1 hn⟩

/-- Under the local-lemma hypothesis of Theorem 1.2 (no slack), every admissible parallel rule
performs at most `∑ i, x i / (1 - x i)` resamplings in expectation over the whole run. This is a
consequence of the valid-log bound `lintegral_iSup_count_le`: each prefix of the parallel run is a
valid log (`isLog_parallelRun`), so its length is at most the measurable majorant
`∑ i, ⨆ (w valid), w.count i` (`length_le_sum_iSup_count`), whose integral
`lintegral_sum_iSup_count_le_of_bound` bounds. Moser and Tardos note after introducing
Algorithm 1.2 that Theorem 1.2 applies to the parallel version [MoserTardos2010, Section 1].

As for `lintegral_parallelRounds_le`, the rule is not assumed measurable and `∫⁻` is the lower
Lebesgue integral. The theorem bounds that lower integral through the majorant; it does not
identify it with the integral of the majorant. -/
theorem lintegral_iSup_length_parallelRun_le [Fintype V] [DecidableEq V] [Fintype ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, ⨆ n, ((parallelRun psel T n).length : ℝ≥0∞) ∂table μ ≤
      ∑ i, ENNReal.ofReal (x i / (1 - x i)) := by
  classical
  exact (lintegral_mono fun T => iSup_le fun n =>
      length_le_sum_iSup_count vbl A (isLog_parallelRun vbl A hA hrule T n)).trans
    (lintegral_sum_iSup_count_le_of_bound μ vbl A hAm
      fun i => lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i)

end Expectation

section SymmetricAndPMF

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι] [Fintype ι]
  {α : V → Type*} [∀ v, MeasurableSpace (α v)]

private theorem ofReal_max_log_mono {a b ε : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hε : 0 < ε) :
    ENNReal.ofReal ((max 0 (Real.log a) + 1) / ε) ≤
      ENNReal.ofReal ((max 0 (Real.log b) + 1) / ε) := by
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hε.le)
  refine add_le_add ?_ le_rfl
  rcases eq_or_lt_of_le ha with rfl | hapos
  · simp
  · exact max_le_max_left 0 (Real.log_le_log hapos hab)

/-- Symmetric parallel Moser–Tardos theorem (`1 ≤ d`): under `e * q * (d + 1) ≤ 1 - ε` with
`ε ∈ (0, 1]`, any admissible parallel selection rule terminates in at most
`(max 0 (Real.log (card ι / d)) + 1) / ε` expected parallel rounds. -/
theorem lintegral_parallelRounds_le_symmetric_of_pos [Fintype V]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hdpos : 1 ≤ d)
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q ε : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q) (hε : ε ∈ Set.Ioc 0 1)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1 - ε)
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table μ ≤
      ENNReal.ofReal ((max 0 (Real.log ((Fintype.card ι : ℝ) / d)) + 1) / ε) := by
  obtain ⟨Γ, x, hΓ, hx, hP, hsum, -⟩ := exists_slack_weights_of_symmetric vbl hd
    (fun _ => measureReal_nonneg) hq hε hlll
  have hM0 : 0 ≤ ∑ i : ι, x i / (1 - x i) :=
    Finset.sum_nonneg fun i _ => div_nonneg (hx i).1 (sub_pos.2 (hx i).2).le
  exact (lintegral_parallelRounds_le μ vbl A hAm hA Γ hΓ hx hε hP hrule).trans
    (ofReal_max_log_mono hM0 (hsum hdpos) hε.1)

/-- Symmetric parallel Moser–Tardos theorem (all `d : ℕ`): under `e * q * (d + 1) ≤ 1 - ε`
with `ε ∈ (0, 1]`, any admissible parallel selection rule terminates in at most
`(max 0 (Real.log (card ι)) + 1) / ε` expected parallel rounds. -/
theorem lintegral_parallelRounds_le_symmetric [Fintype V]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q ε : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q) (hε : ε ∈ Set.Ioc 0 1)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1 - ε)
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table μ ≤
      ENNReal.ofReal ((max 0 (Real.log (Fintype.card ι : ℝ)) + 1) / ε) := by
  obtain ⟨Γ, x, hΓ, hx, hP, -, hsum⟩ := exists_slack_weights_of_symmetric vbl hd
    (fun _ => measureReal_nonneg) hq hε hlll
  have hM0 : 0 ≤ ∑ i : ι, x i / (1 - x i) :=
    Finset.sum_nonneg fun i _ => div_nonneg (hx i).1 (sub_pos.2 (hx i).2).le
  exact (lintegral_parallelRounds_le μ vbl A hAm hA Γ hΓ hx hε hP hrule).trans
    (ofReal_max_log_mono hM0 hsum hε.1)

/-- Almost sure termination and avoidance under the symmetric local-lemma hypothesis
`e * q * (d + 1) ≤ 1`, with no slack, for every `d : ℕ`. -/
theorem ae_exists_forall_notMem_parallelRun_symmetric [Fintype V]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table μ, ∃ n : ℕ, ∀ i, current vbl T (parallelRun psel T n) ∉ A i :=
  -- The generic theorem quantifies over the `DecidableEq ι` instance used by `List.count`, while
  -- `hd` fixes the section's; `convert` identifies the two.
  have hc := lintegral_iSup_count_ne_top_symmetric μ vbl A hAm hA hd hq hlll
  (ae_exists_parallelRun_eq_nil_of_bound μ vbl A hAm hA (fun i => by convert hc i) hrule).mono
    fun T ⟨n, hn⟩ => ⟨n, (hrule.eq_nil_iff T _).1 hn⟩

omit [DecidableEq ι] in
/-- `PMF.pi` bridge for parallel Moser–Tardos expected rounds under the general asymmetric slack
LLL hypothesis. -/
theorem lintegral_parallelRounds_le_pmfPi [Fintype V] [∀ v, Finite (α v)]
    [∀ v, MeasurableSingletonClass (α v)] (p : ∀ v, PMF (α v)) (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hAx : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤
      (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ q : V × ℕ, α q.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table (fun v => (p v).toMeasure) ≤
      ENNReal.ofReal ((max 0 (Real.log (∑ i : ι, x i / (1 - x i))) + 1) / ε) :=
  lintegral_parallelRounds_le (fun v => (p v).toMeasure) vbl A hAm hA Γ hΓ hx hε
    (fun i => toReal_toOuterMeasure_pi_eq_measureReal p (hAm i) ▸ hAx i) hrule

omit [DecidableEq ι] [Fintype ι] in
/-- `PMF.pi` bridge for almost-sure parallel Moser–Tardos termination and avoidance under the
general asymmetric local-lemma hypothesis, with no slack. -/
theorem ae_exists_forall_notMem_parallelRun_pmfPi [Fintype V] [Finite ι]
    [∀ v, Finite (α v)] [∀ v, MeasurableSingletonClass (α v)]
    (p : ∀ v, PMF (α v)) (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hAx : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤
      x i * ∏ j ∈ Γ i, (1 - x j))
    {psel : (∀ q : V × ℕ, α q.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table (fun v => (p v).toMeasure),
      ∃ n : ℕ, ∀ i, current vbl T (parallelRun psel T n) ∉ A i :=
  ae_exists_forall_notMem_parallelRun (fun v => (p v).toMeasure) vbl A hAm hA Γ hΓ hx
    (fun i => toReal_toOuterMeasure_pi_eq_measureReal p (hAm i) ▸ hAx i) hrule

/-- `PMF.pi` bridge for symmetric parallel Moser–Tardos expected rounds (all `d : ℕ`). -/
theorem lintegral_parallelRounds_le_pmfPi_symmetric [Fintype V] [∀ v, Finite (α v)]
    [∀ v, MeasurableSingletonClass (α v)] (p : ∀ v, PMF (α v))
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q ε : ℝ} (hq : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤ q)
    (hε : ε ∈ Set.Ioc 0 1) (hlll : Real.exp 1 * q * (d + 1) ≤ 1 - ε)
    {psel : (∀ q' : V × ℕ, α q'.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table (fun v => (p v).toMeasure) ≤
      ENNReal.ofReal ((max 0 (Real.log (Fintype.card ι : ℝ)) + 1) / ε) :=
  lintegral_parallelRounds_le_symmetric (fun v => (p v).toMeasure) vbl A hAm hA hd
    (fun i => toReal_toOuterMeasure_pi_eq_measureReal p (hAm i) ▸ hq i) hε hlll hrule

end SymmetricAndPMF

end Cslib.Probability.MoserTardos
