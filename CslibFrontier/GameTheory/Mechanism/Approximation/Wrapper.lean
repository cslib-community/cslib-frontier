/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Undominated-Strategy Implementation and Iterative Wrapper Mechanisms

This module formalizes Section 12.5 of [Lavi2007] (pp. 321–327, based on Babaioff, Lavi, and
Pavlov 2006): the iterative ascending wrapper mechanism, implementation in undominated strategies,
the known single-minded (`KSM-PROC`) warm-up, and the multi-minded single-value subprocedure
(`1-CA-PROC`).

## Scope and model

We formalize the exact game-theoretic dominance, iteration-count, and social-welfare approximation
guarantees of [Lavi2007] §12.5 over finite player sets `N` and finite item sets `M` with arbitrary
full-history adaptive deterministic strategies:

* **Single-value players** ([Lavi2007], p. 322): a player `(v̄ᵢ, S̄ᵢ)` has scalar value `v̄ᵢ ≥ 1`
  and a nonempty, upward-closed (free-disposal), normalized (`∅ ∉ S̄ᵢ`) collection of desired
  bundles `S̄ᵢ : Set (Finset M)`.
* **Iterative wrapper & proper procedures** (Definitions 12.36–12.37, Lemma 12.38, pp. 322–323):
  every player starts at bid `vᵢ⁰ = 1` and tentative bundle `sᵢ⁰`; each iteration invokes `PROC`,
  and active nonwinners choose to double (`vᵢ^{j+1} = 2 · vᵢ^j`) or permanently retire
  (`vᵢ^{j+1} = 0`). Under any proper procedure (feasible, Pareto maximal, shrinking-sets), if bids
  never exceed `v_max ≥ 1`, the wrapper terminates in at most `2 ⌊log₂ v_max⌋ + 1` iterations
  (`WrapperProc.termRound_le_of_isProperOn`). Non-terminating profiles (when an out-of-`D` player
  doubles indefinitely) yield the empty zero-payment outcome (`utility = 0`).
* **Local approximation & global reduction** (Definitions 12.39 & 12.42, Claim 12.44, pp. 323–324):
  combining improvement (`∑_{i ∈ W_j} v_i^j ≤ ∑_{i ∈ W_{j+1}} v_i^j`) with `c`-local algorithmic
  approximation and value bounds bounds the optimal welfare of the retired restricted instance `R̄`
  by `2 · J · c · ∑_{i ∈ W_J} v̄ᵢ ≤ 2 · (2 ⌊log₂ v_max⌋ + 1) · c · ∑_{i ∈ W_J} v̄ᵢ`.
* **Known single-minded players (`KSM-PROC`)** (Definition 12.40, Proposition 12.41, Claim 12.43,
  Theorem 12.45, pp. 323–324): wrapping any `c`-approximation algorithm for KSM players yields a
  **dominant-strategy implementation** achieving welfare approximation
  `1 + 2 · (2 ⌊log₂ v_max⌋ + 1) · c = O(log(v_max) · c)`.
* **Single-value players (`1-CA-PROC`)** (Definitions 12.46 & 12.48, Lemmas 12.47 & 12.49,
  Claim 12.50, Theorem 12.51, pp. 325–327): `1-CA-PROC` is a `(3 + 2 √m)`-local-approximation
  satisfying first-time shrink with respect to an explicitly weakly dominant strategy class `D`
  (`oneCaStrategyClass`), yielding an **implementation in undominated strategies** achieving
  welfare approximation
  `1 + 2 · (2 ⌊log₂ v_max⌋ + 1) · (2 ⌊log₂ v_max⌋ + 2) · (3 + 2 √m) = O(log²(v_max) · √m)`.

No machine-model polynomial running-time or demand-oracle query complexity claim is formalized
here; the polynomial-time execution and dominance-transition clauses of Definition 12.35 (p. 321)
remain open under issue #7789.

## Precision notes on the printed source

1. **Iteration index in Definition 12.42 (p. 324):** The displayed inequality writes
   `OPT(R_j(v^j, S̄)) ≤ c · ∑_{i ∈ W_j} v_i^j`, which vanishes at `j = 0` since `W_0 = ∅`. The proof
   of Lemma 12.47 (p. 325) uses the intended `W_{j+1}` (the winners produced by `PROC` at iteration
   `j`, before players in `R_j` retire); this module uses `W_{j+1}`.
2. **Boundary `v_max = 1` in Claim 12.44 (p. 324):** The printed bound `5 · log(v_max) · c`
   vanishes at `v_max = 1`, whereas `J ≤ 2 ⌊log₂ v_max⌋ + 1` gives the exact all-`v_max ≥ 1`
   factor `2 · (2 ⌊log₂ v_max⌋ + 1) · c` (which is at most `5 · log₂(v_max) · c` for `v_max ≥ 4`).
3. **Power-of-two ties in Proposition 12.41 (p. 323):** Both "double iff `2 vᵢ^j < v̄ᵢ`"
   (`ksmDominantStrategy`) and "double iff `2 vᵢ^j ≤ v̄ᵢ`" are dominant strategies in `KSM-PROC`
   (yielding utility `0` either way at `2 vᵢ^j = v̄ᵢ`), and both satisfy `v̄ᵢ / 2 ≤ vᵢ^j ≤ v̄ᵢ` upon
   retiring. The biconditional in Proposition 12.41 holds literally for `ksmDominantStrategy`.
4. **Loser-if-silent condition and empty shrinks in `1-CA-PROC` (p. 325):** At `j = 0`, `W_0 = ∅`,
   so a player with `|sᵢ⁰| = m > √m` still loses if silent even though `sᵢ⁰ ∩ (⋃_{k ∈ W_0} s_k) = ∅`
   vacuously. Moreover, a player who already shrank (`|sᵢ^j| ≤ √m`) enters `GREEDY_j` if disjoint
   from `GREEDY_j`. `IsLoserIfSilent` captures the exact condition under which staying silent
   prevents `i` from entering any of `W_cur, M_cur, GREEDY_j`: `v̄ᵢ / 2 ≤ vᵢ^j`,
   `i ∉ W_cur ∪ M_cur ∪ G_cur`, and either `|sᵢ^j| > √m` or `sᵢ^j` intersects all three current
   allocations. Likewise,
   `1-CA-PROC` requires shrunk bundles to be nonempty (`1 ≤ |b| ≤ √m`), ensuring Pareto holds even
   for out-of-`D` strategies; and `D` requires `sᵢ^j ∈ S̄ᵢ` at every iteration (matching p. 327's
   statement that `sᵢ^J` contains a desired bundle, needed in Claim 12.50 when a player first
   shrinks and retires in the same iteration).
5. **Typo in Theorem 12.51 (p. 327):** The printed theorem writes `O(log²(v_max) · c)` instead of
   `O(log²(v_max) · √m)`; our theorem `oneCaProc_isUndominatedImpl` states the explicit
   `O(log²(v_max) · √m)` factor from Lemma 12.47 (`c = 3 + 2 √m`) and Lemma 12.49.

## Main definitions

* `SingleValuePlayer`, `SingleValuePlayer.eval`, `SingleValuePlayer.singleMinded`: single-value
  valuations `(v̄ᵢ, S̄ᵢ)` ([Lavi2007], p. 322).
* `IsFeasibleAlloc`, `welfareOn`, `optWelfareOn`, `optWelfare`: feasible allocations and optimal
  social welfare for single-value instances.
* `WrapperState`, `WrapperProc`, `wrapperState`, `Terminates`, `termRound`, `WrapperProc.alloc`,
  `WrapperProc.payment`, `WrapperProc.utility`, `WrapperProc.socialWelfare`: the iterative wrapper
  (Definition 12.36, p. 322).
* `WrapperProc.WeaklyDominates`, `WrapperProc.IsDominantStrategy`,
  `WrapperProc.IsUndominatedImpl`, `WrapperProc.IsDominantStrategyImpl`: game-theoretic
  implementation in undominated / dominant strategies (Definition 12.35, p. 321).
* `WrapperProc.IsProperOn`, `WrapperProc.HasImprovementOn`, `WrapperProc.IsLocalApproxOn`,
  `WrapperProc.HasFirstTimeShrinkOn`: structural wrapper properties (Definitions 12.37, 12.39,
  12.42, 12.48).
* `KsmStrategy`, `ksmProc`, `ksmDominantStrategy`, `ksmDominantSet`: the KSM subprocedure and
  dominant strategy (Definition 12.40, Proposition 12.41, p. 323).
* `OneCaShrinkView`, `OneCaStrategy`, `oneCaProc`, `IsLoserIfSilent`, `oneCaStrategyClass`,
  `dominateOneCaStrategy`: the `1-CA-PROC` subprocedure, strategy set `D`, and explicit weak
  dominance transformation (Definition 12.46, p. 325).

## Main results

* `WrapperProc.termRound_le_of_isProperOn`: **Lemma 12.38** ([Lavi2007], p. 323) — `2 ⌊log₂ v_max⌋
  + 1` iteration bound for any proper procedure.
* `WrapperProc.optWelfare_rBar_le`: **Claim 12.44** ([Lavi2007], p. 324) — `2 · J · c` bound on
  `OPT(R̄)` for any `c`-local-approximation.
* `ksmDominantStrategy_isDominant`, `ksmDominantStrategy_retire_iff`: **Proposition 12.41**
  ([Lavi2007], p. 323).
* `ksmProc_isLocalApproxOn`: **Claim 12.43** ([Lavi2007], p. 324).
* `ksmProc_isDominantStrategyImpl`: **Theorem 12.45** ([Lavi2007], p. 324) — dominant-strategy
  `O(log(v_max) · c)`-approximation for KSM players.
* `dominateOneCaStrategy_mem`, `dominateOneCaStrategy_weaklyDominates`: explicit weak dominance of
  `oneCaStrategyClass` (`D`) in `Wrapper + 1-CA-PROC` ([Lavi2007], p. 325).
* `oneCaProc_isLocalApproxOn`: **Lemma 12.47** ([Lavi2007], pp. 325–326) — `(3 + 2 √m)`-local
  approximation for `1-CA-PROC`.
* `WrapperProc.optWelfare_shrunkLosers_le`: **Claim 12.50** ([Lavi2007], p. 326) —
  `OPT(P) ≤ J · OPT(R̄)`.
* `WrapperProc.optWelfare_le_of_firstTimeShrink`: **Lemma 12.49**
  ([Lavi2007], pp. 326–327) — `O(log²(v_max) · c)` global approximation under first-time shrink.
* `oneCaProc_isUndominatedImpl`: **Theorem 12.51** ([Lavi2007], p. 327) — implementation in
  undominated strategies achieving `O(log²(v_max) · √m)` welfare approximation for single-value
  players.

## References

* [R. Lavi, *Computationally Efficient Approximation Mechanisms*, Chapter 12, §12.5,
  pp. 321–327][Lavi2007]
-/

public section

namespace Cslib.GameTheory.Mechanism.Wrapper

open Finset

/-! ### Single-Value Players and Optimal Social Welfare -/

section SingleValue

/-- A single-value player `(v̄ᵢ, S̄ᵢ)` over item set `M` ([Lavi2007], §12.5, p. 322):
the player assigns value `value ≥ 1` to every bundle in the upward-closed (free-disposal),
normalized (`∅ ∉ desired`), nonempty collection `desired`, and `0` to all other bundles. -/
structure SingleValuePlayer (M : Type*) where
  /-- Scalar value `v̄ᵢ ≥ 1` obtained from any desired bundle. -/
  value : ℝ
  /-- Collection `S̄ᵢ` of desired bundles. -/
  desired : Set (Finset M)
  /-- Value lower bound `v̄ᵢ ≥ 1` ([Lavi2007], p. 322). -/
  one_le_value : 1 ≤ value
  /-- Free disposal / monotonicity: any superset of a desired bundle is desired. -/
  upward_closed : ∀ ⦃s t : Finset M⦄, s ∈ desired → s ⊆ t → t ∈ desired
  /-- Normalization: the empty bundle is not desired (`vᵢ(∅) = 0`). -/
  empty_not_mem : ∅ ∉ desired
  /-- At least one bundle is desired (so `Finset.univ ∈ desired` when `M` is finite). -/
  desired_nonempty : desired.Nonempty

namespace SingleValuePlayer

variable {M : Type*}

private theorem value_pos (p : SingleValuePlayer M) : 0 < p.value :=
  lt_of_lt_of_le zero_lt_one p.one_le_value

theorem nonempty_of_mem {p : SingleValuePlayer M} {s : Finset M} (hs : s ∈ p.desired) :
    s.Nonempty :=
  Finset.nonempty_iff_ne_empty.2 fun h => p.empty_not_mem (h ▸ hs)

theorem univ_mem [Fintype M] (p : SingleValuePlayer M) : Finset.univ ∈ p.desired := by
  obtain ⟨s, hs⟩ := p.desired_nonempty
  exact p.upward_closed hs (Finset.subset_univ s)

/-- Valuation `vᵢ(s) ∈ {0, v̄ᵢ}` induced by a single-value player. -/
@[expose] noncomputable def eval (p : SingleValuePlayer M) (s : Finset M) : ℝ := by
  classical exact if s ∈ p.desired then p.value else 0

theorem eval_of_mem {p : SingleValuePlayer M} {s : Finset M} (hs : s ∈ p.desired) :
    p.eval s = p.value := by
  classical simp only [eval, hs, ↓reduceIte]

theorem eval_of_not_mem {p : SingleValuePlayer M} {s : Finset M} (hs : s ∉ p.desired) :
    p.eval s = 0 := by
  classical simp only [eval, hs, ↓reduceIte]

@[simp]
theorem eval_empty (p : SingleValuePlayer M) : p.eval ∅ = 0 :=
  eval_of_not_mem p.empty_not_mem

theorem eval_nonneg (p : SingleValuePlayer M) (s : Finset M) : 0 ≤ p.eval s := by
  classical
  simp only [eval]
  split_ifs
  · exact p.value_pos.le
  · exact le_rfl

theorem eval_le_value (p : SingleValuePlayer M) (s : Finset M) : p.eval s ≤ p.value := by
  classical
  simp only [eval]
  split_ifs
  · exact le_rfl
  · exact p.value_pos.le

/-- Construct a single-value player representing a single-minded bidder desiring `bundle`
(nonempty) at value `value ≥ 1`. -/
@[expose] def singleMinded (bundle : Finset M) (hbundle : bundle.Nonempty)
    (value : ℝ) (hval : 1 ≤ value) : SingleValuePlayer M where
  value := value
  desired := {s | bundle ⊆ s}
  one_le_value := hval
  upward_closed _ _ hs hst := hs.trans hst
  empty_not_mem h := hbundle.ne_empty (Finset.subset_empty.1 h)
  desired_nonempty := ⟨bundle, Subset.rfl⟩

end SingleValuePlayer

/-- An allocation `alloc : N → Finset M` is feasible if distinct players receive pairwise disjoint
bundles. -/
@[expose] def IsFeasibleAlloc {N M : Type*} (alloc : N → Finset M) : Prop :=
  Pairwise fun i j => Disjoint (alloc i) (alloc j)

/-- Social welfare of allocation `alloc` on player subset `X`, given scalar values `val` and
desired-bundle collections `des`. -/
@[expose] noncomputable def welfareOn {N M : Type*} (X : Finset N) (val : N → ℝ)
    (des : N → Set (Finset M)) (alloc : N → Finset M) : ℝ := by
  classical exact ∑ i ∈ X, if alloc i ∈ des i then val i else 0

private noncomputable def feasibleAllocs (N M : Type*) [Fintype N] [Fintype M] :
    Finset (N → Finset M) := by
  classical exact Finset.univ.filter IsFeasibleAlloc

private theorem feasibleAllocs_nonempty (N M : Type*) [Fintype N] [Fintype M] :
    (feasibleAllocs N M).Nonempty := by
  classical
  refine ⟨fun _ => ∅, Finset.mem_filter.2
    ⟨Finset.mem_univ _, fun _ _ _ => Finset.disjoint_empty_left _⟩⟩

/-- Optimal social welfare `OPT(X, val, des)` over all feasible allocations on player subset `X`
([Lavi2007], §12.5, p. 324). Works uniformly for true players and restricted virtual instances
`R_j(v, S)`. -/
noncomputable def optWelfareOn {N M : Type*} [Fintype N] [Fintype M]
    (X : Finset N) (val : N → ℝ) (des : N → Set (Finset M)) : ℝ :=
  (feasibleAllocs N M).sup' (feasibleAllocs_nonempty N M) (welfareOn X val des)

/-- Optimal social welfare `OPT` for a profile of single-value players. -/
@[expose] noncomputable def optWelfare {N M : Type*} [Fintype N] [Fintype M]
    (players : N → SingleValuePlayer M) : ℝ :=
  optWelfareOn Finset.univ (fun i => (players i).value) (fun i => (players i).desired)

section OptLemmas

variable {N M : Type*} [Fintype N] [Fintype M]

theorem welfareOn_le_optWelfareOn (X : Finset N) (val : N → ℝ) (des : N → Set (Finset M))
    {alloc : N → Finset M} (hfeas : IsFeasibleAlloc alloc) :
    welfareOn X val des alloc ≤ optWelfareOn X val des := by
  classical
  exact Finset.le_sup' (welfareOn X val des)
    (show alloc ∈ feasibleAllocs N M from Finset.mem_filter.2 ⟨Finset.mem_univ alloc, hfeas⟩)

theorem exists_feasibleAlloc_eq_optWelfareOn (X : Finset N) (val : N → ℝ)
    (des : N → Set (Finset M)) :
    ∃ alloc : N → Finset M, IsFeasibleAlloc alloc ∧
      welfareOn X val des alloc = optWelfareOn X val des := by
  classical
  obtain ⟨alloc, halloc, hEq⟩ :=
    Finset.exists_mem_eq_sup' (feasibleAllocs_nonempty N M) (welfareOn X val des)
  have hfeas : IsFeasibleAlloc alloc := by
    simp only [feasibleAllocs, Finset.mem_filter] at halloc
    exact halloc.2
  exact ⟨alloc, hfeas, hEq.symm⟩

private theorem optWelfareOn_nonneg {X : Finset N} {val : N → ℝ} {des : N → Set (Finset M)}
    (hval : ∀ i ∈ X, 0 ≤ val i) : 0 ≤ optWelfareOn X val des := by
  classical
  calc (0 : ℝ)
    _ ≤ welfareOn X val des (fun _ => ∅) :=
        Finset.sum_nonneg fun i hi => by
          split_ifs
          · exact hval i hi
          · exact le_rfl
    _ ≤ optWelfareOn X val des :=
        welfareOn_le_optWelfareOn X val des fun _ _ _ => Finset.disjoint_empty_left _

private theorem optWelfareOn_mono_val {X : Finset N} {val₁ val₂ : N → ℝ}
    {des : N → Set (Finset M)} (hval : ∀ i ∈ X, val₁ i ≤ val₂ i) :
    optWelfareOn X val₁ des ≤ optWelfareOn X val₂ des := by
  classical
  obtain ⟨alloc, hfeas, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn X val₁ des
  rw [← hEq]
  refine (Finset.sum_le_sum fun i hi => ?_).trans (welfareOn_le_optWelfareOn X val₂ des hfeas)
  split_ifs
  · exact hval i hi
  · exact le_rfl

private theorem optWelfareOn_mono_des {X : Finset N} {val : N → ℝ}
    {des₁ des₂ : N → Set (Finset M)} (hval : ∀ i ∈ X, 0 ≤ val i)
    (hdes : ∀ i ∈ X, des₁ i ⊆ des₂ i) :
    optWelfareOn X val des₁ ≤ optWelfareOn X val des₂ := by
  classical
  obtain ⟨alloc, hfeas, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn X val des₁
  rw [← hEq]
  refine (Finset.sum_le_sum fun i hi => ?_).trans (welfareOn_le_optWelfareOn X val des₂ hfeas)
  by_cases h1 : alloc i ∈ des₁ i
  · simp only [h1, hdes i hi h1, ↓reduceIte, le_refl]
  · simp only [h1, ↓reduceIte]
    split_ifs
    · exact hval i hi
    · exact le_rfl

private theorem optWelfareOn_smul {X : Finset N} {val : N → ℝ} {des : N → Set (Finset M)}
    {α : ℝ} (hα : 0 ≤ α) :
    optWelfareOn X (fun i => α * val i) des ≤ α * optWelfareOn X val des := by
  classical
  obtain ⟨alloc, hfeas, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn X (fun i => α * val i) des
  rw [← hEq]
  have hrew : welfareOn X (fun i => α * val i) des alloc = α * welfareOn X val des alloc := by
    simp only [welfareOn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  rw [hrew]
  exact mul_le_mul_of_nonneg_left (welfareOn_le_optWelfareOn X val des hfeas) hα

private theorem optWelfareOn_subset_le {X Y : Finset N} {val : N → ℝ} {des : N → Set (Finset M)}
    (hXY : X ⊆ Y) (hval : ∀ i ∈ Y, 0 ≤ val i) :
    optWelfareOn X val des ≤ optWelfareOn Y val des := by
  classical
  obtain ⟨alloc, hfeas, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn X val des
  rw [← hEq]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hXY fun i hi _ => ?_).trans
    (welfareOn_le_optWelfareOn Y val des hfeas)
  split_ifs
  · exact hval i hi
  · exact le_rfl

private theorem sum_union_le {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ s ∪ t, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hinter : 0 ≤ ∑ x ∈ s ∩ t, f x :=
    Finset.sum_nonneg fun x hx => hf x (Finset.mem_union_left _ (Finset.mem_inter.1 hx).1)
  linarith

private theorem optWelfareOn_union_le [DecidableEq N] {X Y : Finset N} {val : N → ℝ}
    {des : N → Set (Finset M)} (hval : ∀ i ∈ X ∪ Y, 0 ≤ val i) :
    optWelfareOn (X ∪ Y) val des ≤ optWelfareOn X val des + optWelfareOn Y val des := by
  classical
  obtain ⟨alloc, hfeas, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn (X ∪ Y) val des
  rw [← hEq]
  have hsum : welfareOn (X ∪ Y) val des alloc ≤
      welfareOn X val des alloc + welfareOn Y val des alloc := by
    simp only [welfareOn]
    exact sum_union_le fun i hi => by
      split_ifs
      · exact hval i hi
      · exact le_rfl
  exact hsum.trans (add_le_add (welfareOn_le_optWelfareOn X val des hfeas)
    (welfareOn_le_optWelfareOn Y val des hfeas))

private theorem optWelfareOn_biUnion_le {ι : Type*} [DecidableEq N] (I : Finset ι)
    (f : ι → Finset N) {val : N → ℝ} {des : N → Set (Finset M)}
    (hval : ∀ t ∈ I, ∀ i ∈ f t, 0 ≤ val i) :
    optWelfareOn (I.biUnion f) val des ≤ ∑ t ∈ I, optWelfareOn (f t) val des := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.sum_empty]
    obtain ⟨alloc, _, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn (∅ : Finset N) val des
    simp only [welfareOn, Finset.sum_empty] at hEq
    linarith
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hval' : ∀ i ∈ f a ∪ s.biUnion f, 0 ≤ val i := by
      intro i hi
      rcases Finset.mem_union.1 hi with hfa | hbi
      · exact hval a (Finset.mem_insert_self a s) i hfa
      · obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.1 hbi
        exact hval t (Finset.mem_insert_of_mem ht) i hit
    exact (optWelfareOn_union_le hval').trans
      (add_le_add le_rfl (ih fun t ht i hi => hval t (Finset.mem_insert_of_mem ht) i hi))

private theorem optWelfareOn_le_sum {X : Finset N} {val : N → ℝ} {des : N → Set (Finset M)}
    (hval : ∀ i ∈ X, 0 ≤ val i) :
    optWelfareOn X val des ≤ ∑ i ∈ X, val i := by
  classical
  obtain ⟨alloc, _, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn X val des
  rw [← hEq]
  refine Finset.sum_le_sum fun i hi => ?_
  split_ifs
  · exact le_rfl
  · exact hval i hi

private theorem optWelfareOn_congr_des {X : Finset N} {val : N → ℝ}
    {des₁ des₂ : N → Set (Finset M)} (h : ∀ i ∈ X, des₁ i = des₂ i) :
    optWelfareOn X val des₁ = optWelfareOn X val des₂ := by
  classical
  refine le_antisymm ?_ ?_
  · obtain ⟨alloc, hfeas, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn X val des₁
    rw [← hEq]
    have hcongr : welfareOn X val des₁ alloc = welfareOn X val des₂ alloc :=
      Finset.sum_congr rfl fun i hi => by rw [h i hi]
    rw [hcongr]
    exact welfareOn_le_optWelfareOn X val des₂ hfeas
  · obtain ⟨alloc, hfeas, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn X val des₂
    rw [← hEq]
    have hcongr : welfareOn X val des₂ alloc = welfareOn X val des₁ alloc :=
      Finset.sum_congr rfl fun i hi => by rw [h i hi]
    rw [hcongr]
    exact welfareOn_le_optWelfareOn X val des₁ hfeas

end OptLemmas

end SingleValue

/-! ### The Iterative Wrapper and Implementation in Undominated Strategies -/

section WrapperCore

/-- State of the iterative wrapper at iteration `j` ([Lavi2007], Definition 12.36, p. 322).
Bids `val i` are natural numbers (`0` for retired players, powers of `2` for active players). -/
@[ext]
structure WrapperState (N M : Type*) where
  /-- Current bid `v_i^j` (`0` if retired, `2^k` if active). -/
  val : N → ℕ
  /-- Current tentative winning bundle `s_i^j`. -/
  bundle : N → Finset M
  /-- Current tentative winner set `W_j`. -/
  winners : Finset N
  /-- Current permanently retired set `L_j`. -/
  losers : Finset N

/-- A subprocedure plugged into the iterative wrapper ([Lavi2007], Definition 12.36, p. 322),
parameterized by the players' strategy type `Strat`. -/
structure WrapperProc (N M Strat : Type*) where
  /-- Initial tentative bundle `s_i^0` for each player `i`. -/
  initBundle : N → Finset M
  /-- Subprocedure `PROC(v^j, s^j, W_j)`: given the strategy profile `σ`, the list of strictly
  earlier states `past`, and the current state `st`, outputs `(W_{j+1}, s^{j+1})`. -/
  proc : (N → Strat) → List (WrapperState N M) → WrapperState N M → Finset N × (N → Finset M)
  /-- Step-2 doubling decision for player `i` when `i ∉ W_{j+1} ∪ L_j`: `true` doubles `v_i^j`,
  `false` permanently retires `i` (`v_i^{j+1} = 0`). -/
  chooseDouble : Strat → List (WrapperState N M) → WrapperState N M → Finset N →
    (N → Finset M) → Bool

variable {N M Strat : Type*}

/-- Initial wrapper state at `j = 0`: `W_0 = L_0 = ∅`, `v_i^0 = 1`, `s_i^0 = initBundle i`. -/
@[expose] def initState (initBundle : N → Finset M) : WrapperState N M where
  val := fun _ => 1
  bundle := initBundle
  winners := ∅
  losers := ∅

/-- One step of the iterative wrapper (Definition 12.36, p. 322). Once `W_j ∪ L_j = univ`, the
state remains stationary. -/
@[expose] def wrapperNext [Fintype N] [DecidableEq N] (P : WrapperProc N M Strat)
    (σ : N → Strat) (past : List (WrapperState N M)) (st : WrapperState N M) :
    WrapperState N M :=
  if st.winners ∪ st.losers = Finset.univ then st
  else
    let res := P.proc σ past st
    let W' := res.1
    let s' := res.2
    let v' : N → ℕ := fun i =>
      if i ∈ W' ∪ st.losers then st.val i
      else if P.chooseDouble (σ i) past st W' s' then 2 * st.val i else 0
    let L' : Finset N := Finset.univ.filter fun i => v' i = 0
    ⟨v', s', W', L'⟩

/-- Execute `j` iterations of the wrapper, returning `(state_j, past_states)`. -/
@[expose] def wrapperRunHist [Fintype N] [DecidableEq N] (P : WrapperProc N M Strat)
    (σ : N → Strat) : ℕ → WrapperState N M × List (WrapperState N M)
  | 0 => (initState P.initBundle, [])
  | j + 1 =>
    let cur := wrapperRunHist P σ j
    (wrapperNext P σ cur.2 cur.1, cur.1 :: cur.2)

/-- Wrapper state at iteration `j`. -/
@[expose] def wrapperState [Fintype N] [DecidableEq N] (P : WrapperProc N M Strat)
    (σ : N → Strat) (j : ℕ) : WrapperState N M :=
  (wrapperRunHist P σ j).1

/-- The wrapper has terminated by iteration `j`: `W_j ∪ L_j = univ`. -/
@[expose] def TerminatedAt [Fintype N] [DecidableEq N] (P : WrapperProc N M Strat)
    (σ : N → Strat) (j : ℕ) : Prop :=
  (wrapperState P σ j).winners ∪ (wrapperState P σ j).losers = Finset.univ

/-- The wrapper terminates in finitely many iterations under strategy profile `σ`. -/
@[expose] def Terminates [Fintype N] [DecidableEq N] (P : WrapperProc N M Strat)
    (σ : N → Strat) : Prop :=
  ∃ j, TerminatedAt P σ j

/-- The first termination iteration `J` (or `0` if the wrapper does not terminate). -/
@[expose] noncomputable def termRound [Fintype N] [DecidableEq N] (P : WrapperProc N M Strat)
    (σ : N → Strat) : ℕ := by
  classical exact if h : Terminates P σ then Nat.find h else 0

namespace WrapperProc

variable [Fintype N] [DecidableEq N]

/-- Final bundle allocation produced by the wrapper (Definition 12.36, p. 322): winners `i ∈ W_J`
receive `s_i^J`, all others receive `∅`; non-terminating profiles yield `∅`. -/
@[expose] noncomputable def alloc (P : WrapperProc N M Strat) (σ : N → Strat) (i : N) : Finset M :=
  by
    classical
    exact if Terminates P σ then
      let stJ := wrapperState P σ (termRound P σ)
      if i ∈ stJ.winners then stJ.bundle i else ∅
    else ∅

/-- Final payment charged by the wrapper (Definition 12.36, p. 322): winners `i ∈ W_J` pay `v_i^J`,
all others pay `0`; non-terminating profiles charge `0`. -/
@[expose] noncomputable def payment (P : WrapperProc N M Strat) (σ : N → Strat) (i : N) : ℝ :=
  by
    classical
    exact if Terminates P σ then
      let stJ := wrapperState P σ (termRound P σ)
      if i ∈ stJ.winners then (stJ.val i : ℝ) else 0
    else 0

/-- Quasilinear utility of player `i` with true single-value valuation `p` under profile `σ`. -/
@[expose] noncomputable def utility (P : WrapperProc N M Strat) (σ : N → Strat)
    (p : SingleValuePlayer M) (i : N) : ℝ :=
  p.eval (P.alloc σ i) - P.payment σ i

/-- Total realized social welfare `∑ i, v_i(alloc i)` under profile `σ`. -/
@[expose] noncomputable def socialWelfare (P : WrapperProc N M Strat) (σ : N → Strat)
    (players : N → SingleValuePlayer M) : ℝ :=
  ∑ i : N, (players i).eval (P.alloc σ i)

/-- Strategy `st'` *weakly dominates* `st` for player `i` with true valuation `p`: against every
opponent strategy profile `σ`, `st'` yields at least as much utility as `st`. -/
@[expose] def WeaklyDominates (P : WrapperProc N M Strat) (p : SingleValuePlayer M)
    (i : N) (st' st : Strat) : Prop :=
  ∀ σ : N → Strat, P.utility (Function.update σ i st) p i ≤
    P.utility (Function.update σ i st') p i

/-- Strategy `stStar` is a *dominant strategy* for player `i` with valuation `p`. -/
@[expose] def IsDominantStrategy (P : WrapperProc N M Strat) (p : SingleValuePlayer M)
    (i : N) (stStar : Strat) : Prop :=
  ∀ st : Strat, P.WeaklyDominates p i stStar st

/-- **Game-theoretic implementation of a `c`-approximation in undominated strategies**
([Lavi2007], Definition 12.35, p. 321): there exists a strategy family `D` such that
(i) every profile in `D` terminates in a feasible allocation attaining a `c`-approximation to
`optWelfare`, and (ii) every strategy of player `i` is weakly dominated by some strategy in `D i`.
Machine-model polynomial time is outside this predicate and tracked under `#7789`. -/
@[expose] def IsUndominatedImpl [Fintype M] (P : WrapperProc N M Strat)
    (players : N → SingleValuePlayer M) (D : N → Set Strat) (c : ℝ) : Prop :=
  (∀ σ : N → Strat, (∀ i, σ i ∈ D i) →
    Terminates P σ ∧ IsFeasibleAlloc (P.alloc σ) ∧
      optWelfare players ≤ c * P.socialWelfare σ players) ∧
  (∀ (i : N) (st : Strat), ∃ st' ∈ D i, P.WeaklyDominates (players i) i st' st)

/-- **Game-theoretic dominant-strategy implementation of a `c`-approximation**
([Lavi2007], Theorem 12.45, p. 324): `σStar i` is a dominant strategy for every player `i`, and
the profile `σStar` terminates in a feasible allocation attaining a `c`-approximation to
`optWelfare`. -/
@[expose] def IsDominantStrategyImpl [Fintype M] (P : WrapperProc N M Strat)
    (players : N → SingleValuePlayer M) (σStar : N → Strat) (c : ℝ) : Prop :=
  (∀ i, P.IsDominantStrategy (players i) i (σStar i)) ∧
  Terminates P σStar ∧
  IsFeasibleAlloc (P.alloc σStar) ∧
  optWelfare players ≤ c * P.socialWelfare σStar players

/-- **Proper procedure** along strategy profile `σ` ([Lavi2007], Definition 12.37, p. 322):
at every active iteration `j` (`¬ TerminatedAt P σ j`), `PROC` outputs a feasible winner set
`W_{j+1}` disjoint from `L_j` satisfying (1) Pareto maximality and (2) shrinking-sets. -/
@[expose] def IsProperOn (P : WrapperProc N M Strat) (σ : N → Strat) : Prop :=
  ∀ j : ℕ, ¬ TerminatedAt P σ j →
    let cur := wrapperRunHist P σ j
    let res := P.proc σ cur.2 cur.1
    (res.1 : Set N).PairwiseDisjoint res.2 ∧
    Disjoint res.1 cur.1.losers ∧
    (∀ i, i ∉ res.1 ∪ cur.1.losers → ∃ l ∈ res.1, ¬ Disjoint (res.2 i) (res.2 l)) ∧
    (∀ i, res.2 i ⊆ cur.1.bundle i)

/-- **Improvement property** along strategy profile `σ` ([Lavi2007], Definition 12.39, p. 323):
`∑_{i ∈ W_j} v_i^j ≤ ∑_{i ∈ W_{j+1}} v_i^j` at every active iteration `j`. -/
@[expose] def HasImprovementOn (P : WrapperProc N M Strat) (σ : N → Strat) : Prop :=
  ∀ j : ℕ, ¬ TerminatedAt P σ j →
    let cur := wrapperRunHist P σ j
    ∑ i ∈ cur.1.winners, cur.1.val i ≤ ∑ i ∈ (P.proc σ cur.2 cur.1).1, cur.1.val i

/-- **First-time shrink property** along strategy profile `σ` ([Lavi2007], Definition 12.48,
p. 326): any two distinct players who shrink from size `m` to `< m` in the same iteration `j`
have disjoint new bundles `s_{i₁}^{j+1}` and `s_{i₂}^{j+1}`. -/
@[expose] def HasFirstTimeShrinkOn [Fintype M] (P : WrapperProc N M Strat)
    (σ : N → Strat) : Prop :=
  ∀ j : ℕ, ¬ TerminatedAt P σ j →
    ∀ ⦃i₁ i₂ : N⦄, i₁ ≠ i₂ →
      ((wrapperState P σ j).bundle i₁).card = Fintype.card M →
      ((wrapperState P σ (j + 1)).bundle i₁).card < Fintype.card M →
      ((wrapperState P σ j).bundle i₂).card = Fintype.card M →
      ((wrapperState P σ (j + 1)).bundle i₂).card < Fintype.card M →
      Disjoint ((wrapperState P σ (j + 1)).bundle i₁) ((wrapperState P σ (j + 1)).bundle i₂)

end WrapperProc

end WrapperCore

variable {N M Strat : Type*}

/-! ### Basic Wrapper Invariants and Lemma 12.38 -/

section WrapperInvariants

variable [Fintype N] [DecidableEq N]

private theorem wrapperState_zero (P : WrapperProc N M Strat) (σ : N → Strat) :
    wrapperState P σ 0 = initState P.initBundle := rfl

private theorem wrapperState_succ_of_terminatedAt {P : WrapperProc N M Strat} {σ : N → Strat}
    {j : ℕ} (h : TerminatedAt P σ j) :
    wrapperState P σ (j + 1) = wrapperState P σ j := by
  simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at h ⊢
  simp only [h, ↓reduceIte]

private theorem wrapperState_succ_winners {P : WrapperProc N M Strat} {σ : N → Strat} {j : ℕ}
    (hnotT : ¬ TerminatedAt P σ j) :
    (wrapperState P σ (j + 1)).winners =
      (P.proc σ (wrapperRunHist P σ j).2 (wrapperRunHist P σ j).1).1 := by
  simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at hnotT ⊢
  simp only [hnotT, ↓reduceIte]

private theorem wrapperState_succ_bundle {P : WrapperProc N M Strat} {σ : N → Strat} {j : ℕ}
    (hnotT : ¬ TerminatedAt P σ j) :
    (wrapperState P σ (j + 1)).bundle =
      (P.proc σ (wrapperRunHist P σ j).2 (wrapperRunHist P σ j).1).2 := by
  simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at hnotT ⊢
  simp only [hnotT, ↓reduceIte]

private theorem wrapperState_succ_val {P : WrapperProc N M Strat} {σ : N → Strat} {j : ℕ}
    (hnotT : ¬ TerminatedAt P σ j) (i : N) :
    let cur := wrapperRunHist P σ j
    let res := P.proc σ cur.2 cur.1
    (wrapperState P σ (j + 1)).val i =
      if i ∈ res.1 ∪ cur.1.losers then cur.1.val i
      else if P.chooseDouble (σ i) cur.2 cur.1 res.1 res.2 then 2 * cur.1.val i else 0 := by
  simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at hnotT ⊢
  simp only [hnotT, ↓reduceIte]

private theorem wrapperNext_congr {P : WrapperProc N M Strat} {σ₁ σ₂ : N → Strat}
    {past : List (WrapperState N M)} {st : WrapperState N M}
    (hproc : P.proc σ₁ past st = P.proc σ₂ past st)
    (hch : ∀ k, k ∉ (P.proc σ₁ past st).1 ∪ st.losers →
      P.chooseDouble (σ₁ k) past st (P.proc σ₁ past st).1 (P.proc σ₁ past st).2 =
      P.chooseDouble (σ₂ k) past st (P.proc σ₂ past st).1 (P.proc σ₂ past st).2) :
    wrapperNext P σ₁ past st = wrapperNext P σ₂ past st := by
  simp only [wrapperNext]
  by_cases ht : st.winners ∪ st.losers = Finset.univ
  · simp only [ht, ↓reduceIte]
  · simp only [ht, ↓reduceIte]
    have hv : ∀ k,
        (if k ∈ (P.proc σ₁ past st).1 ∪ st.losers then st.val k
         else if P.chooseDouble (σ₁ k) past st (P.proc σ₁ past st).1 (P.proc σ₁ past st).2
           then 2 * st.val k else 0) =
        (if k ∈ (P.proc σ₂ past st).1 ∪ st.losers then st.val k
         else if P.chooseDouble (σ₂ k) past st (P.proc σ₂ past st).1 (P.proc σ₂ past st).2
           then 2 * st.val k else 0) := by
      intro k
      by_cases hm : k ∈ (P.proc σ₁ past st).1 ∪ st.losers
      · have hm₂ : k ∈ (P.proc σ₂ past st).1 ∪ st.losers := hproc ▸ hm
        simp only [hm, hm₂, ↓reduceIte]
      · simp only [hm, ↓reduceIte, ← hproc, hch k hm]
    simp only [hv]
    rw [hproc]

private theorem wrapperState_eq_of_terminatedAt_le {P : WrapperProc N M Strat} {σ : N → Strat}
    {j k : ℕ} (h : TerminatedAt P σ j) (hjk : j ≤ k) :
    wrapperState P σ k = wrapperState P σ j := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [wrapperState_succ_of_terminatedAt (by simpa only [TerminatedAt, ih] using h), ih]

private theorem terminatedAt_mono {P : WrapperProc N M Strat} {σ : N → Strat} {j k : ℕ}
    (h : TerminatedAt P σ j) (hjk : j ≤ k) : TerminatedAt P σ k := by
  simp only [TerminatedAt, wrapperState_eq_of_terminatedAt_le h hjk]
  exact h

theorem termRound_spec {P : WrapperProc N M Strat} {σ : N → Strat} (h : Terminates P σ) :
    TerminatedAt P σ (termRound P σ) := by
  classical
  simp only [termRound, h, ↓reduceDIte]
  exact Nat.find_spec h

theorem termRound_le_of_terminatedAt {P : WrapperProc N M Strat} {σ : N → Strat} {j : ℕ}
    (h : TerminatedAt P σ j) : termRound P σ ≤ j := by
  classical
  have hT : Terminates P σ := ⟨j, h⟩
  simp only [termRound, hT, ↓reduceDIte]
  exact Nat.find_min' hT h

private theorem not_terminatedAt_of_lt_termRound {P : WrapperProc N M Strat} {σ : N → Strat}
    {j : ℕ} (h : j < termRound P σ) : ¬ TerminatedAt P σ j := fun ht =>
  not_le_of_gt h (termRound_le_of_terminatedAt ht)

theorem wrapperState_termRound_eq {P : WrapperProc N M Strat} {σ : N → Strat} {K : ℕ}
    (h : TerminatedAt P σ K) :
    wrapperState P σ (termRound P σ) = wrapperState P σ K :=
  (wrapperState_eq_of_terminatedAt_le (termRound_spec ⟨K, h⟩)
    (termRound_le_of_terminatedAt h)).symm

private theorem mem_losers_iff_val_eq_zero (P : WrapperProc N M Strat) (σ : N → Strat)
    (j : ℕ) (i : N) :
    i ∈ (wrapperState P σ j).losers ↔ (wrapperState P σ j).val i = 0 := by
  induction j with
  | zero =>
    simp only [wrapperState_zero, initState, Finset.notMem_empty, one_ne_zero]
  | succ j ih =>
    by_cases ht : TerminatedAt P σ j
    · rw [wrapperState_succ_of_terminatedAt ht]
      exact ih
    · simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at ht ⊢
      simp only [ht, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem losers_subset_succ (P : WrapperProc N M Strat) (σ : N → Strat) (j : ℕ) :
    (wrapperState P σ j).losers ⊆ (wrapperState P σ (j + 1)).losers := by
  intro i hi
  by_cases ht : TerminatedAt P σ j
  · rwa [wrapperState_succ_of_terminatedAt ht]
  · rw [mem_losers_iff_val_eq_zero] at hi ⊢
    simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at ht hi ⊢
    simp only [ht, ↓reduceIte, hi]
    split_ifs <;> rfl

private theorem losers_mono (P : WrapperProc N M Strat) (σ : N → Strat) {j k : ℕ} (hjk : j ≤ k) :
    (wrapperState P σ j).losers ⊆ (wrapperState P σ k).losers := by
  induction k, hjk using Nat.le_induction with
  | base => exact Subset.rfl
  | succ m _ ih => exact ih.trans (losers_subset_succ P σ m)

private theorem val_mono_of_not_mem_losers (P : WrapperProc N M Strat) (σ : N → Strat)
    {j k : ℕ} (hjk : j ≤ k) {i : N} (hi : i ∉ (wrapperState P σ k).losers) :
    (wrapperState P σ j).val i ≤ (wrapperState P σ k).val i := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    have him : i ∉ (wrapperState P σ m).losers := fun h => hi (losers_subset_succ P σ m h)
    refine (ih him).trans ?_
    by_cases ht : TerminatedAt P σ m
    · rw [wrapperState_succ_of_terminatedAt ht]
    · have hnz : (wrapperState P σ (m + 1)).val i ≠ 0 :=
        mt (mem_losers_iff_val_eq_zero P σ (m + 1) i).2 hi
      simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at ht hnz ⊢
      simp only [ht, ↓reduceIte] at hnz ⊢
      split_ifs at hnz ⊢ with h1 h2
      · exact le_rfl
      · omega
      · exact absurd rfl hnz

private theorem bundle_subset_succ_of_isProperOn {P : WrapperProc N M Strat} {σ : N → Strat}
    (hproper : P.IsProperOn σ) (j : ℕ) (i : N) :
    (wrapperState P σ (j + 1)).bundle i ⊆ (wrapperState P σ j).bundle i := by
  by_cases ht : TerminatedAt P σ j
  · rw [wrapperState_succ_of_terminatedAt ht]
  · have h := (hproper j ht).2.2.2 i
    simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at ht ⊢
    simpa only [ht, ↓reduceIte] using h

private theorem bundle_subset_of_isProperOn {P : WrapperProc N M Strat} {σ : N → Strat}
    (hproper : P.IsProperOn σ) {j k : ℕ} (hjk : j ≤ k) (i : N) :
    (wrapperState P σ k).bundle i ⊆ (wrapperState P σ j).bundle i := by
  induction k, hjk using Nat.le_induction with
  | base => exact Subset.rfl
  | succ m _ ih => exact (bundle_subset_succ_of_isProperOn hproper m i).trans ih

private theorem disjoint_winners_losers_of_isProperOn {P : WrapperProc N M Strat} {σ : N → Strat}
    (hproper : P.IsProperOn σ) (j : ℕ) :
    Disjoint (wrapperState P σ j).winners (wrapperState P σ j).losers := by
  induction j with
  | zero =>
    simp only [wrapperState_zero, initState, Finset.disjoint_empty_left]
  | succ j ih =>
    by_cases ht : TerminatedAt P σ j
    · rwa [wrapperState_succ_of_terminatedAt ht]
    · have hdisj := (hproper j ht).2.1
      rw [Finset.disjoint_left]
      intro i hiW hiL
      rw [mem_losers_iff_val_eq_zero] at hiL
      simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at ht hiW hiL
      simp only [ht, ↓reduceIte] at hiW hiL
      have hnotL : i ∉ (wrapperRunHist P σ j).1.losers := Finset.disjoint_left.1 hdisj hiW
      have hnz : (wrapperRunHist P σ j).1.val i ≠ 0 :=
        mt (mem_losers_iff_val_eq_zero P σ j i).2 hnotL
      simp only [Finset.mem_union, hiW, true_or, ↓reduceIte] at hiL
      exact hnz hiL

private theorem winners_pairwiseDisjoint_of_isProperOn {P : WrapperProc N M Strat} {σ : N → Strat}
    (hproper : P.IsProperOn σ) (j : ℕ) :
    ((wrapperState P σ j).winners : Set N).PairwiseDisjoint (wrapperState P σ j).bundle := by
  cases j with
  | zero =>
    simp only [wrapperState_zero, initState, Finset.coe_empty, Set.pairwiseDisjoint_empty]
  | succ j =>
    by_cases ht : TerminatedAt P σ j
    · rw [wrapperState_succ_of_terminatedAt ht]
      exact winners_pairwiseDisjoint_of_isProperOn hproper j
    · have hp := (hproper j ht).1
      simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at ht ⊢
      simpa only [ht, ↓reduceIte] using hp

theorem WrapperProc.isFeasibleAlloc_of_isProperOn {P : WrapperProc N M Strat} {σ : N → Strat}
    (hproper : P.IsProperOn σ) : IsFeasibleAlloc (P.alloc σ) := by
  classical
  intro i₁ i₂ hne
  simp only [WrapperProc.alloc]
  split_ifs with hT h1 h2
  · exact winners_pairwiseDisjoint_of_isProperOn hproper (termRound P σ) h1 h2 hne
  · exact Finset.disjoint_empty_right _
  · exact Finset.disjoint_empty_left _
  · exact Finset.disjoint_empty_left _
  · exact Finset.disjoint_empty_left _

/-- Whether player `i` doubled in iteration `j` (active nonwinner choosing `true`). -/
private def doubledAt (P : WrapperProc N M Strat) (σ : N → Strat) (i : N) (j : ℕ) : Bool :=
  let cur := wrapperRunHist P σ j
  if cur.1.winners ∪ cur.1.losers = Finset.univ then false
  else
    let res := P.proc σ cur.2 cur.1
    if i ∈ res.1 ∪ cur.1.losers then false
    else P.chooseDouble (σ i) cur.2 cur.1 res.1 res.2

/-- Total number of times player `i` doubled before iteration `j`. -/
private def doublingCount (P : WrapperProc N M Strat) (σ : N → Strat) (i : N) (j : ℕ) : ℕ :=
  ((Finset.range j).filter fun t => doubledAt P σ i t = true).card

private theorem val_eq_two_pow_doublingCount (P : WrapperProc N M Strat) (σ : N → Strat)
    (j : ℕ) {i : N} (hi : i ∉ (wrapperState P σ j).losers) :
    (wrapperState P σ j).val i = 2 ^ doublingCount P σ i j := by
  induction j with
  | zero =>
    simp only [wrapperState_zero, initState, doublingCount, Finset.range_zero,
      Finset.filter_empty, Finset.card_empty, pow_zero]
  | succ j ih =>
    have hij : i ∉ (wrapperState P σ j).losers := fun h => hi (losers_subset_succ P σ j h)
    have hprev := ih hij
    have hcount : doublingCount P σ i (j + 1) =
        doublingCount P σ i j + if doubledAt P σ i j = true then 1 else 0 := by
      simp only [doublingCount, Finset.range_add_one, Finset.filter_insert]
      split_ifs with hd
      · rw [Finset.card_insert_of_notMem]
        simp only [Finset.mem_filter, Finset.mem_range, lt_self_iff_false, false_and,
          not_false_eq_true]
      · simp only [add_zero]
    by_cases ht : TerminatedAt P σ j
    · have hdf : doubledAt P σ i j = false := by
        simp only [doubledAt, TerminatedAt, wrapperState] at ht ⊢
        simp only [ht, ↓reduceIte]
      rw [wrapperState_succ_of_terminatedAt ht, hcount, hdf]
      simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using hprev
    · have hnz : (wrapperState P σ (j + 1)).val i ≠ 0 :=
        mt (mem_losers_iff_val_eq_zero P σ (j + 1) i).2 hi
      rw [hcount]
      simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt, doubledAt]
        at ht hprev hnz ⊢
      simp only [ht, ↓reduceIte] at hnz ⊢
      by_cases hmem : i ∈ (P.proc σ (wrapperRunHist P σ j).2 (wrapperRunHist P σ j).1).1 ∪
          (wrapperRunHist P σ j).1.losers
      · simp only [hmem, ↓reduceIte, Bool.false_eq_true, add_zero]
        exact hprev
      · simp only [hmem, ↓reduceIte] at hnz ⊢
        cases hch : P.chooseDouble (σ i) (wrapperRunHist P σ j).2 (wrapperRunHist P σ j).1
            (P.proc σ (wrapperRunHist P σ j).2 (wrapperRunHist P σ j).1).1
            (P.proc σ (wrapperRunHist P σ j).2 (wrapperRunHist P σ j).1).2
        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hnz
          exact absurd rfl hnz
        · simp only [↓reduceIte, hprev, pow_succ, mul_comm]

private theorem doublingCount_le_of_val_lt {P : WrapperProc N M Strat} {σ : N → Strat} {B : ℕ}
    (hbound : ∀ j i, (wrapperState P σ j).val i < 2 ^ (B + 1)) (i : N) (j : ℕ) :
    doublingCount P σ i j ≤ B := by
  induction j with
  | zero =>
    simp only [doublingCount, Finset.range_zero, Finset.filter_empty, Finset.card_empty,
      Nat.zero_le]
  | succ j ih =>
    by_cases hd : doubledAt P σ i j = true
    · have hnotL : i ∉ (wrapperState P σ (j + 1)).losers := by
        rw [mem_losers_iff_val_eq_zero]
        have hnotT : ¬ TerminatedAt P σ j := by
          intro ht
          simp only [doubledAt, TerminatedAt, wrapperState] at ht hd
          simp only [ht, ↓reduceIte, Bool.false_eq_true] at hd
        simp only [doubledAt, TerminatedAt, wrapperState] at hnotT hd
        simp only [hnotT, ↓reduceIte] at hd
        have hnotMem : i ∉ (P.proc σ (wrapperRunHist P σ j).2 (wrapperRunHist P σ j).1).1 ∪
            (wrapperRunHist P σ j).1.losers := by
          intro hm
          simp only [hm, ↓reduceIte, Bool.false_eq_true] at hd
        have hnotLj : i ∉ (wrapperState P σ j).losers := fun h =>
          hnotMem (Finset.mem_union_right _ h)
        have hpos : 0 < (wrapperState P σ j).val i :=
          Nat.pos_of_ne_zero (mt (mem_losers_iff_val_eq_zero P σ j i).2 hnotLj)
        simp only [hnotMem, ↓reduceIte] at hd
        simp only [wrapperState, wrapperRunHist, wrapperNext, hnotT, ↓reduceIte, hnotMem, hd]
        exact mul_ne_zero two_ne_zero hpos.ne'
      have hpow : 2 ^ doublingCount P σ i (j + 1) < 2 ^ (B + 1) := by
        rw [← val_eq_two_pow_doublingCount P σ (j + 1) hnotL]
        exact hbound (j + 1) i
      exact Nat.lt_succ_iff.1 ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hpow)
    · have heq : doublingCount P σ i (j + 1) = doublingCount P σ i j := by
        simp only [doublingCount, Finset.range_add_one, Finset.filter_insert, hd,
          Bool.false_eq_true, ↓reduceIte]
      rw [heq]
      exact ih

/-- **Lemma 12.38** ([Lavi2007], §12.5, p. 323): if `P` is proper along `σ` and every player's bid
never exceeds `v_max`, then the iterative wrapper terminates in at most
`2 * Nat.log 2 ⌊v_max⌋₊ + 1` iterations. -/
theorem WrapperProc.termRound_le_of_isProperOn {P : WrapperProc N M Strat} {σ : N → Strat}
    {v_max : ℝ} (hproper : P.IsProperOn σ)
    (hbound : ∀ j i, ((wrapperState P σ j).val i : ℝ) ≤ v_max) :
    Terminates P σ ∧ termRound P σ ≤ 2 * Nat.log 2 ⌊v_max⌋₊ + 1 := by
  set B := Nat.log 2 ⌊v_max⌋₊
  have hlt_pow : ∀ j i, (wrapperState P σ j).val i < 2 ^ (B + 1) := by
    intro j i
    have h1 : ⌊v_max⌋₊ < 2 ^ (B + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊v_max⌋₊
    have h2 : v_max < ((2 ^ (B + 1) : ℕ) : ℝ) := by
      have hfloor : v_max < (⌊v_max⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one v_max
      have hle : (⌊v_max⌋₊ + 1 : ℕ) ≤ 2 ^ (B + 1) := h1
      have hleR : ((⌊v_max⌋₊ : ℝ) + 1) ≤ ((2 ^ (B + 1) : ℕ) : ℝ) := by exact_mod_cast hle
      linarith
    exact_mod_cast (hbound j i).trans_lt h2
  have hterm : TerminatedAt P σ (2 * B + 1) := by
    by_contra hnotT
    have hnotT_prev : ¬ TerminatedAt P σ (2 * B) := fun h =>
      hnotT (terminatedAt_mono h (Nat.le_succ _))
    have hne : (wrapperState P σ (2 * B + 1)).winners ∪ (wrapperState P σ (2 * B + 1)).losers ≠
        Finset.univ := hnotT
    have hex : ∃ i₁ : N, i₁ ∉ (wrapperState P σ (2 * B + 1)).winners ∪
        (wrapperState P σ (2 * B + 1)).losers := by
      by_contra hall
      push Not at hall
      exact hne (Finset.eq_univ_iff_forall.2 hall)
    obtain ⟨i₁, hi₁⟩ := hex
    rw [Finset.mem_union, not_or] at hi₁
    obtain ⟨hi₁W, hi₁L⟩ := hi₁
    have hi₁L_prev : i₁ ∉ (wrapperState P σ (2 * B)).losers := fun h =>
      hi₁L (losers_subset_succ P σ (2 * B) h)
    have hi₁_not_mem : i₁ ∉ (P.proc σ (wrapperRunHist P σ (2 * B)).2
        (wrapperRunHist P σ (2 * B)).1).1 ∪ (wrapperRunHist P σ (2 * B)).1.losers := by
      rw [wrapperState_succ_winners hnotT_prev] at hi₁W
      exact Finset.notMem_union.2 ⟨hi₁W, hi₁L_prev⟩
    have hi₁_doubled : doubledAt P σ i₁ (2 * B) = true := by
      have hnz : (wrapperState P σ (2 * B + 1)).val i₁ ≠ 0 :=
        mt (mem_losers_iff_val_eq_zero P σ (2 * B + 1) i₁).2 hi₁L
      rw [wrapperState_succ_val hnotT_prev i₁] at hnz
      simp only [doubledAt, wrapperState, TerminatedAt] at hnotT_prev ⊢
      simp only [hnotT_prev, ↓reduceIte, hi₁_not_mem] at hnz ⊢
      cases hch : P.chooseDouble (σ i₁)
          (wrapperRunHist P σ (2 * B)).2 (wrapperRunHist P σ (2 * B)).1
          (P.proc σ (wrapperRunHist P σ (2 * B)).2 (wrapperRunHist P σ (2 * B)).1).1
          (P.proc σ (wrapperRunHist P σ (2 * B)).2 (wrapperRunHist P σ (2 * B)).1).2
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hnz
        exact absurd rfl hnz
      · rfl
    obtain ⟨i₂, hi₂W, hnotDisj⟩ := (hproper (2 * B) hnotT_prev).2.2.1 i₁ hi₁_not_mem
    have hne12 : i₁ ≠ i₂ := fun h => hi₁_not_mem (Finset.mem_union_left _ (h ▸ hi₂W))
    have hi₂W' : i₂ ∈ (wrapperState P σ (2 * B + 1)).winners := by
      simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at hnotT_prev ⊢
      simpa only [hnotT_prev, ↓reduceIte] using hi₂W
    have hi₂L : i₂ ∉ (wrapperState P σ (2 * B + 1)).losers :=
      Finset.disjoint_left.1 (disjoint_winners_losers_of_isProperOn hproper (2 * B + 1)) hi₂W'
    have hnotDisj' : ¬ Disjoint ((wrapperState P σ (2 * B + 1)).bundle i₁)
        ((wrapperState P σ (2 * B + 1)).bundle i₂) := by
      simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at hnotT_prev ⊢
      simpa only [hnotT_prev, ↓reduceIte] using hnotDisj
    -- At every earlier iteration `t < 2 * B`, at least one of `{i₁, i₂}` doubled.
    have hcover : ∀ t ∈ Finset.range (2 * B),
        doubledAt P σ i₁ t = true ∨ doubledAt P σ i₂ t = true := by
      intro t ht
      rw [Finset.mem_range] at ht
      have hnotTt : ¬ TerminatedAt P σ t := fun h =>
        hnotT_prev (terminatedAt_mono h (Nat.le_of_lt ht))
      have hnotDisj_t : ¬ Disjoint ((wrapperState P σ (t + 1)).bundle i₁)
          ((wrapperState P σ (t + 1)).bundle i₂) := fun hd =>
        hnotDisj' (hd.mono (bundle_subset_of_isProperOn hproper (Nat.succ_le_succ ht.le) i₁)
          (bundle_subset_of_isProperOn hproper (Nat.succ_le_succ ht.le) i₂))
      have hnotBothW : ¬ (i₁ ∈ (wrapperState P σ (t + 1)).winners ∧
          i₂ ∈ (wrapperState P σ (t + 1)).winners) := fun ⟨h1, h2⟩ =>
        hnotDisj_t (winners_pairwiseDisjoint_of_isProperOn hproper (t + 1) h1 h2 hne12)
      have helper : ∀ k, k ∉ (wrapperState P σ (t + 1)).winners →
          k ∉ (wrapperState P σ (2 * B + 1)).losers → doubledAt P σ k t = true := by
        intro k hkW hkL
        have hkLt1 : k ∉ (wrapperState P σ (t + 1)).losers := fun h =>
          hkL (losers_mono P σ (Nat.succ_le_succ ht.le) h)
        have hkLt : k ∉ (wrapperState P σ t).losers := fun h =>
          hkLt1 (losers_subset_succ P σ t h)
        have hnz : (wrapperState P σ (t + 1)).val k ≠ 0 :=
          mt (mem_losers_iff_val_eq_zero P σ (t + 1) k).2 hkLt1
        rw [wrapperState_succ_winners hnotTt] at hkW
        rw [wrapperState_succ_val hnotTt k] at hnz
        have hnm : k ∉ (P.proc σ (wrapperRunHist P σ t).2 (wrapperRunHist P σ t).1).1 ∪
            (wrapperRunHist P σ t).1.losers := Finset.notMem_union.2 ⟨hkW, hkLt⟩
        simp only [doubledAt, wrapperState, TerminatedAt] at hnotTt ⊢
        simp only [hnotTt, ↓reduceIte, hnm] at hnz ⊢
        cases hch : P.chooseDouble (σ k) (wrapperRunHist P σ t).2 (wrapperRunHist P σ t).1
            (P.proc σ (wrapperRunHist P σ t).2 (wrapperRunHist P σ t).1).1
            (P.proc σ (wrapperRunHist P σ t).2 (wrapperRunHist P σ t).1).2
        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hnz
          exact absurd rfl hnz
        · rfl
      by_cases h1 : i₁ ∈ (wrapperState P σ (t + 1)).winners
      · exact Or.inr (helper i₂ (fun h2 => hnotBothW ⟨h1, h2⟩) hi₂L)
      · exact Or.inl (helper i₁ h1 hi₁L)
    have hsum_prev : 2 * B ≤ doublingCount P σ i₁ (2 * B) + doublingCount P σ i₂ (2 * B) := by
      have hsub : Finset.range (2 * B) ⊆
          ((Finset.range (2 * B)).filter fun t => doubledAt P σ i₁ t = true) ∪
          ((Finset.range (2 * B)).filter fun t => doubledAt P σ i₂ t = true) := by
        intro t ht
        rcases hcover t ht with h1 | h2
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨ht, h1⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ht, h2⟩)
      calc 2 * B = (Finset.range (2 * B)).card := (Finset.card_range _).symm
        _ ≤ _ := Finset.card_le_card hsub
        _ ≤ doublingCount P σ i₁ (2 * B) + doublingCount P σ i₂ (2 * B) :=
            Finset.card_union_le _ _
    have hstep1 : doublingCount P σ i₁ (2 * B + 1) = doublingCount P σ i₁ (2 * B) + 1 := by
      simp only [doublingCount, Finset.range_add_one, Finset.filter_insert, hi₁_doubled, ↓reduceIte]
      rw [Finset.card_insert_of_notMem]
      simp only [Finset.mem_filter, Finset.mem_range, lt_self_iff_false, false_and,
        not_false_eq_true]
    have hstep2 : doublingCount P σ i₂ (2 * B) ≤ doublingCount P σ i₂ (2 * B + 1) := by
      refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
      exact Finset.range_mono (Nat.le_succ _)
    have hle1 : doublingCount P σ i₁ (2 * B + 1) ≤ B :=
      doublingCount_le_of_val_lt hlt_pow i₁ (2 * B + 1)
    have hle2 : doublingCount P σ i₂ (2 * B + 1) ≤ B :=
      doublingCount_le_of_val_lt hlt_pow i₂ (2 * B + 1)
    omega
  exact ⟨⟨2 * B + 1, hterm⟩, termRound_le_of_terminatedAt hterm⟩

end WrapperInvariants

/-! ### Local Approximation and Claim 12.44 -/

section LocalApprox

variable [Fintype N] [DecidableEq N]

/-- Players who retire at iteration `j`: `L_{j+1} \ L_j`. -/
@[expose] def retiredAt (P : WrapperProc N M Strat) (σ : N → Strat) (j : ℕ) : Finset N :=
  (wrapperState P σ (j + 1)).losers \ (wrapperState P σ j).losers

/-- Desired bundles of player `i` restricted to subsets of `s i` ([Lavi2007], eq. (12.14),
p. 323): `S_i|_{s_i} = {b ∈ S_i | b ⊆ s_i}`. -/
@[expose] def restrictedDesired (des : N → Set (Finset M)) (s : N → Finset M) (i : N) :
    Set (Finset M) :=
  {b ∈ des i | b ⊆ s i}

/-- The iteration at which player `i` retires (or `0` if `i` never retires). -/
@[expose] noncomputable def retireRound (P : WrapperProc N M Strat) (σ : N → Strat) (i : N) : ℕ :=
  by
    classical
    exact if h : ∃ j, i ∈ (wrapperState P σ (j + 1)).losers then Nat.find h else 0

/-- Desired-bundle collection of the union retired virtual instance `R̄ = ⋃_{j < J} R_j(v̄, S̄)`
([Lavi2007], p. 324): each retired player `i` keeps desired bundles contained in `s_i^{r_i}`
where `r_i` is the iteration at which `i` retired. -/
@[expose] noncomputable def rBarDesired (P : WrapperProc N M Strat) (σ : N → Strat)
    (players : N → SingleValuePlayer M) (i : N) : Set (Finset M) :=
  restrictedDesired (fun k => (players k).desired)
    (wrapperState P σ (retireRound P σ i)).bundle i

private theorem retireRound_eq_of_mem_retiredAt {P : WrapperProc N M Strat} {σ : N → Strat}
    {j : ℕ} {i : N} (hi : i ∈ retiredAt P σ j) : retireRound P σ i = j := by
  classical
  rw [retiredAt, Finset.mem_sdiff] at hi
  have hex : ∃ k, i ∈ (wrapperState P σ (k + 1)).losers := ⟨j, hi.1⟩
  simp only [retireRound, hex, ↓reduceDIte]
  refine le_antisymm (Nat.find_min' hex hi.1) ?_
  by_contra hlt
  push Not at hlt
  exact hi.2 (losers_mono P σ (Nat.succ_le_of_lt hlt) (Nat.find_spec hex))

private theorem biUnion_retiredAt_eq_losers (P : WrapperProc N M Strat) (σ : N → Strat) (J : ℕ) :
    (Finset.range J).biUnion (retiredAt P σ) = (wrapperState P σ J).losers := by
  induction J with
  | zero =>
    simp only [Finset.range_zero, Finset.biUnion_empty, wrapperState_zero, initState]
  | succ J ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, ih, retiredAt,
      Finset.sdiff_union_of_subset (losers_subset_succ P σ J)]

private theorem mem_retiredAt_retireRound {P : WrapperProc N M Strat} {σ : N → Strat} {J : ℕ}
    {i : N} (hi : i ∈ (wrapperState P σ J).losers) :
    retireRound P σ i < J ∧ i ∈ retiredAt P σ (retireRound P σ i) := by
  rw [← biUnion_retiredAt_eq_losers P σ J, Finset.mem_biUnion] at hi
  obtain ⟨j, hj, hij⟩ := hi
  rw [Finset.mem_range] at hj
  rw [retireRound_eq_of_mem_retiredAt hij]
  exact ⟨hj, hij⟩

/-- **Local approximation** ([Lavi2007], Definition 12.42, p. 324, with the winner index `W_{j+1}`
matching Lemma 12.47, p. 325): `P` is a `c`-local-approximation w.r.t. strategy family `D` if for
every profile `σ` in `D`, `P` is proper, satisfies improvement, achieves `c`-algorithmic
approximation on each `R_j(v^j, S̄)` against `∑_{i ∈ W_{j+1}} v_i^j`, and maintains the value
bounds (`s_i^j ∈ S̄_i`, `v_i^j ≤ v̄_i`, and `v̄_i / 2 ≤ v_i^j` upon retirement). -/
@[expose] def WrapperProc.IsLocalApproxOn [Fintype M] (P : WrapperProc N M Strat)
    (players : N → SingleValuePlayer M) (D : N → Set Strat) (c : ℝ) : Prop :=
  ∀ σ : N → Strat, (∀ i, σ i ∈ D i) →
    P.IsProperOn σ ∧
    P.HasImprovementOn σ ∧
    (∀ j : ℕ, ¬ TerminatedAt P σ j →
      optWelfareOn (retiredAt P σ j)
        (fun i => ((wrapperState P σ j).val i : ℝ))
        (restrictedDesired (fun i => (players i).desired) (wrapperState P σ j).bundle) ≤
      c * ∑ i ∈ (wrapperState P σ (j + 1)).winners, ((wrapperState P σ j).val i : ℝ)) ∧
    (∀ j i, (wrapperState P σ j).bundle i ∈ (players i).desired) ∧
    (∀ j i, ((wrapperState P σ j).val i : ℝ) ≤ (players i).value) ∧
    (∀ j i, i ∈ retiredAt P σ j → (players i).value / 2 ≤ ((wrapperState P σ j).val i : ℝ))

private theorem sum_winners_val_succ_eq {P : WrapperProc N M Strat} {σ : N → Strat} {j : ℕ}
    (hnotT : ¬ TerminatedAt P σ j) :
    ∑ i ∈ (wrapperState P σ (j + 1)).winners, ((wrapperState P σ j).val i : ℝ) =
      ∑ i ∈ (wrapperState P σ (j + 1)).winners, ((wrapperState P σ (j + 1)).val i : ℝ) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at hnotT hi ⊢
  simp only [hnotT, ↓reduceIte] at hi ⊢
  simp only [Finset.mem_union, hi, true_or, ↓reduceIte]

private theorem sum_winners_val_mono {P : WrapperProc N M Strat} {σ : N → Strat}
    (himp : P.HasImprovementOn σ) {j k : ℕ} (hjk : j ≤ k) :
    ∑ i ∈ (wrapperState P σ j).winners, ((wrapperState P σ j).val i : ℝ) ≤
      ∑ i ∈ (wrapperState P σ k).winners, ((wrapperState P σ k).val i : ℝ) := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    refine ih.trans ?_
    by_cases ht : TerminatedAt P σ m
    · rw [wrapperState_succ_of_terminatedAt ht]
    · rw [← sum_winners_val_succ_eq ht]
      have hnat := himp m ht
      have hW : (wrapperState P σ (m + 1)).winners =
          (P.proc σ (wrapperRunHist P σ m).2 (wrapperRunHist P σ m).1).1 := by
        simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt] at ht ⊢
        simp only [ht, ↓reduceIte]
      rw [hW]
      exact_mod_cast hnat

private theorem socialWelfare_eq_sum_winners {P : WrapperProc N M Strat} {σ : N → Strat}
    {players : N → SingleValuePlayer M} (hT : Terminates P σ)
    (hdes : ∀ i ∈ (wrapperState P σ (termRound P σ)).winners,
      (wrapperState P σ (termRound P σ)).bundle i ∈ (players i).desired) :
    P.socialWelfare σ players =
      ∑ i ∈ (wrapperState P σ (termRound P σ)).winners, (players i).value := by
  classical
  simp only [WrapperProc.socialWelfare, WrapperProc.alloc, hT, ↓reduceIte]
  rw [← Finset.sum_subset (Finset.subset_univ (wrapperState P σ (termRound P σ)).winners)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hi, ↓reduceIte, SingleValuePlayer.eval_of_mem (hdes i hi)]
  · intro i _ hi
    simp only [hi, ↓reduceIte, SingleValuePlayer.eval_empty]

/-- **Claim 12.44** ([Lavi2007], §12.5, p. 324): under any `c`-local-approximation with `0 ≤ c`
and `1 ≤ v_max` bounding all player values, the optimal welfare of the retired restricted instance
`R̄` satisfies both the exact `termRound` bound `2 * J * c * SW` and the explicit all-`v_max ≥ 1`
bound `2 * (2 * Nat.log 2 ⌊v_max⌋₊ + 1) * c * SW`. -/
theorem WrapperProc.optWelfare_rBar_le [Fintype M] {P : WrapperProc N M Strat}
    {players : N → SingleValuePlayer M} {D : N → Set Strat} {c v_max : ℝ} {σ : N → Strat}
    (hloc : P.IsLocalApproxOn players D c) (hc : 0 ≤ c)
    (hval_le : ∀ i, (players i).value ≤ v_max) (hσ : ∀ i, σ i ∈ D i) :
    let J := termRound P σ
    Terminates P σ ∧
    J ≤ 2 * Nat.log 2 ⌊v_max⌋₊ + 1 ∧
    optWelfareOn (wrapperState P σ J).losers (fun i => (players i).value)
        (rBarDesired P σ players) ≤
      2 * (J : ℝ) * c * P.socialWelfare σ players ∧
    optWelfareOn (wrapperState P σ J).losers (fun i => (players i).value)
        (rBarDesired P σ players) ≤
      2 * (2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 1) * c * P.socialWelfare σ players := by
  obtain ⟨hproper, himp, halg, hdes, hvalB, hretB⟩ := hloc σ hσ
  obtain ⟨hT, hJle⟩ := P.termRound_le_of_isProperOn hproper fun j i =>
    (hvalB j i).trans (hval_le i)
  set J := termRound P σ
  have hSW : P.socialWelfare σ players = ∑ i ∈ (wrapperState P σ J).winners, (players i).value :=
    socialWelfare_eq_sum_winners hT fun i _ => hdes J i
  have hSW_nonneg : 0 ≤ P.socialWelfare σ players := by
    rw [hSW]
    exact Finset.sum_nonneg fun i _ => (players i).value_pos.le
  have hper_round : ∀ j ∈ Finset.range J,
      optWelfareOn (retiredAt P σ j) (fun i => (players i).value) (rBarDesired P σ players) ≤
        2 * c * P.socialWelfare σ players := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hnotT : ¬ TerminatedAt P σ j := not_terminatedAt_of_lt_termRound hj
    have hcongr : optWelfareOn (retiredAt P σ j) (fun i => (players i).value)
        (rBarDesired P σ players) =
        optWelfareOn (retiredAt P σ j) (fun i => (players i).value)
          (restrictedDesired (fun k => (players k).desired) (wrapperState P σ j).bundle) :=
      optWelfareOn_congr_des fun i hi => by
        simp only [rBarDesired, retireRound_eq_of_mem_retiredAt hi]
    rw [hcongr]
    have h1 : optWelfareOn (retiredAt P σ j) (fun i => (players i).value)
        (restrictedDesired (fun k => (players k).desired) (wrapperState P σ j).bundle) ≤
        2 * optWelfareOn (retiredAt P σ j) (fun i => ((wrapperState P σ j).val i : ℝ))
          (restrictedDesired (fun k => (players k).desired) (wrapperState P σ j).bundle) := by
      refine (optWelfareOn_mono_val (val₂ := fun i => 2 * ((wrapperState P σ j).val i : ℝ))
        fun i hi => by linarith [hretB j i hi]).trans (optWelfareOn_smul (by norm_num))
    have h2 := halg j hnotT
    have h3 : ∑ i ∈ (wrapperState P σ (j + 1)).winners, ((wrapperState P σ j).val i : ℝ) ≤
        P.socialWelfare σ players := by
      rw [sum_winners_val_succ_eq hnotT, hSW]
      exact (sum_winners_val_mono himp (Nat.succ_le_of_lt hj)).trans
        (Finset.sum_le_sum fun i _ => hvalB J i)
    calc optWelfareOn (retiredAt P σ j) (fun i => (players i).value)
          (restrictedDesired (fun k => (players k).desired) (wrapperState P σ j).bundle)
      _ ≤ 2 * (c * ∑ i ∈ (wrapperState P σ (j + 1)).winners,
            ((wrapperState P σ j).val i : ℝ)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = 2 * c * ∑ i ∈ (wrapperState P σ (j + 1)).winners,
            ((wrapperState P σ j).val i : ℝ) := by ring
      _ ≤ 2 * c * P.socialWelfare σ players :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hboundJ : optWelfareOn (wrapperState P σ J).losers (fun i => (players i).value)
      (rBarDesired P σ players) ≤ 2 * (J : ℝ) * c * P.socialWelfare σ players := by
    rw [← biUnion_retiredAt_eq_losers P σ J]
    calc optWelfareOn ((Finset.range J).biUnion (retiredAt P σ)) (fun i => (players i).value)
          (rBarDesired P σ players)
      _ ≤ ∑ j ∈ Finset.range J, optWelfareOn (retiredAt P σ j) (fun i => (players i).value)
            (rBarDesired P σ players) :=
          optWelfareOn_biUnion_le _ _ fun _ _ i _ => (players i).value_pos.le
      _ ≤ ∑ _j ∈ Finset.range J, (2 * c * P.socialWelfare σ players) :=
          Finset.sum_le_sum hper_round
      _ = (J : ℝ) * (2 * c * P.socialWelfare σ players) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = 2 * (J : ℝ) * c * P.socialWelfare σ players := by ring
  have hJleR : (J : ℝ) ≤ 2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 1 := by exact_mod_cast hJle
  refine ⟨hT, hJle, hboundJ, hboundJ.trans ?_⟩
  have hmul : 0 ≤ c * P.socialWelfare σ players := mul_nonneg hc hSW_nonneg
  nlinarith

end LocalApprox

/-! ### Known Single-Minded Players (`KSM-PROC`, Theorem 12.45) -/

section KsmProc

variable [Fintype N] [LinearOrder N] [DecidableEq M]

/-- Full-history strategy for the KSM wrapper: given past states, current state, and round output
`(W_{j+1}, s^{j+1})`, returns `true` to double or `false` to permanently retire. -/
abbrev KsmStrategy (N M : Type*) :=
  List (WrapperState N M) → WrapperState N M → Finset N → (N → Finset M) → Bool

/-- Greedy Pareto-maximizing extension for KSM players ([Lavi2007], p. 323): visits all players in
deterministic linear order and inserts each active player whose bundle is disjoint from the
current winner set. -/
@[expose] def ksmExtendPareto (bundle : N → Finset M) (L W : Finset N) : Finset N :=
  (Finset.univ.sort (· ≤ ·)).foldl
    (fun acc i =>
      if i ∉ L ∧ i ∉ acc ∧ ∀ k ∈ acc, Disjoint (bundle i) (bundle k) then insert i acc else acc)
    W

private theorem ksmExtendPareto_props (bundle : N → Finset M) (L W : Finset N)
    (hdisj : Disjoint W L) (hpw : (W : Set N).PairwiseDisjoint bundle) :
    W ⊆ ksmExtendPareto bundle L W ∧
    Disjoint (ksmExtendPareto bundle L W) L ∧
    ((ksmExtendPareto bundle L W : Set N).PairwiseDisjoint bundle) ∧
    (∀ i, i ∉ ksmExtendPareto bundle L W ∪ L →
      ∃ l ∈ ksmExtendPareto bundle L W, ¬ Disjoint (bundle i) (bundle l)) := by
  let step : Finset N → N → Finset N := fun acc i =>
    if i ∉ L ∧ i ∉ acc ∧ ∀ k ∈ acc, Disjoint (bundle i) (bundle k) then insert i acc else acc
  have hfold : ∀ (xs : List N) (acc : Finset N),
      Disjoint acc L → (acc : Set N).PairwiseDisjoint bundle →
      acc ⊆ xs.foldl step acc ∧
      Disjoint (xs.foldl step acc) L ∧
      (((xs.foldl step acc : Finset N) : Set N).PairwiseDisjoint bundle) ∧
      (∀ i ∈ xs, i ∉ xs.foldl step acc ∪ L →
        ∃ l ∈ xs.foldl step acc, ¬ Disjoint (bundle i) (bundle l)) := by
    intro xs
    induction xs with
    | nil =>
      intro acc hd hp
      exact ⟨Subset.rfl, hd, hp, fun _ h => absurd h List.not_mem_nil⟩
    | cons a tl ih =>
      intro acc hd hp
      have hacc_sub : acc ⊆ step acc a := by
        simp only [step]
        split_ifs
        · exact Finset.subset_insert a acc
        · exact Subset.rfl
      have hd' : Disjoint (step acc a) L := by
        simp only [step]
        split_ifs with h
        · exact Finset.disjoint_insert_left.2 ⟨h.1, hd⟩
        · exact hd
      have hp' : ((step acc a : Set N).PairwiseDisjoint bundle) := by
        simp only [step]
        split_ifs with h
        · rw [Finset.coe_insert]
          exact hp.insert fun k hk _ => h.2.2 k hk
        · exact hp
      obtain ⟨hsub_tl, hd_tl, hp_tl, hpar_tl⟩ := ih (step acc a) hd' hp'
      refine ⟨hacc_sub.trans hsub_tl, hd_tl, hp_tl, fun i hi hnot => ?_⟩
      rcases List.mem_cons.1 hi with rfl | htl
      · rw [Finset.mem_union, not_or] at hnot
        have hnot_step : i ∉ step acc i := fun h => hnot.1 (hsub_tl h)
        have hnot_cond : ¬ (i ∉ L ∧ i ∉ acc ∧ ∀ k ∈ acc, Disjoint (bundle i) (bundle k)) := by
          intro hc
          apply hnot_step
          simp only [step]
          rw [ite_eq_left_iff.2 fun h => absurd hc h]
          exact Finset.mem_insert_self i acc
        push Not at hnot_cond
        obtain ⟨k, hk, hnd⟩ := hnot_cond hnot.2 (fun h => hnot_step (hacc_sub h))
        exact ⟨k, hsub_tl (hacc_sub hk), hnd⟩
      · exact hpar_tl i htl hnot
  obtain ⟨h1, h2, h3, h4⟩ := hfold (Finset.univ.sort (· ≤ ·)) W hdisj hpw
  exact ⟨h1, h2, h3, fun i hi => h4 i ((Finset.mem_sort (· ≤ ·)).2 (Finset.mem_univ i)) hi⟩

/-- **The `KSM-PROC` subprocedure** ([Lavi2007], Definition 12.40, p. 323): given public desired
bundles `bundle` and a KSM approximation algorithm `alg : (N → ℝ) → Finset N`, invokes `alg` on
current bids `v^j`, enforces Improvement against `W_j`, and greedily extends the winner set to
satisfy Pareto maximality while keeping `s^{j+1} = s^j = bundle`. -/
@[expose] def ksmProc (bundle : N → Finset M) (alg : (N → ℝ) → Finset N) :
    WrapperProc N M (KsmStrategy N M) where
  initBundle := bundle
  proc _ _ st :=
    let wAlg := (alg fun i => (st.val i : ℝ)).filter fun i => 0 < st.val i
    let wBase := if ∑ i ∈ st.winners, st.val i ≤ ∑ i ∈ wAlg, st.val i then wAlg else st.winners
    (ksmExtendPareto bundle st.losers wBase, st.bundle)
  chooseDouble s past st W' s' := s past st W' s'

/-- Canonical dominant strategy for a KSM player with true value `v` ([Lavi2007], Proposition
12.41, p. 323): double iff `2 * v_i^j < v`, else permanently retire. -/
@[expose] noncomputable def ksmDominantStrategy (i : N) (v : ℝ) : KsmStrategy N M :=
  fun _ st _ _ => by classical exact decide (2 * (st.val i : ℝ) < v)

/-- The set of all undominated value-respecting KSM strategies for player `i` with value `v`: never
double above `v` and never retire strictly below `v / 2`. Contains both `2 v_i^j < v` and
`2 v_i^j ≤ v`. -/
@[expose] def ksmDominantSet (i : N) (v : ℝ) : Set (KsmStrategy N M) :=
  {s | ∀ past st W' s',
    (v < 2 * (st.val i : ℝ) → s past st W' s' = false) ∧
    (2 * (st.val i : ℝ) < v → s past st W' s' = true)}

omit [Fintype N] [LinearOrder N] [DecidableEq M] in
theorem ksmDominantStrategy_mem (i : N) (v : ℝ) :
    ksmDominantStrategy (M := M) i v ∈ ksmDominantSet i v := by
  intro past st W' s'
  classical
  simp only [ksmDominantStrategy, decide_eq_false_iff_not, decide_eq_true_eq]
  exact ⟨fun h => not_lt.2 h.le, fun h => h⟩

private theorem ksmProc_bundle_eq (bundle : N → Finset M) (alg : (N → ℝ) → Finset N)
    (σ : N → KsmStrategy N M) (j : ℕ) :
    (wrapperState (ksmProc bundle alg) σ j).bundle = bundle := by
  induction j with
  | zero => rfl
  | succ j ih =>
    by_cases ht : TerminatedAt (ksmProc bundle alg) σ j
    · rw [wrapperState_succ_of_terminatedAt ht, ih]
    · simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt, ksmProc] at ht ih ⊢
      simpa only [ht, ↓reduceIte] using ih

private theorem ksmProc_isProperOn_and_hasImprovementOn (bundle : N → Finset M)
    {alg : (N → ℝ) → Finset N}
    (halg_feas : ∀ v : N → ℝ, (∀ i, 0 ≤ v i) → (alg v : Set N).PairwiseDisjoint bundle)
    (σ : N → KsmStrategy N M) :
    (ksmProc bundle alg).IsProperOn σ ∧ (ksmProc bundle alg).HasImprovementOn σ := by
  set P := ksmProc bundle alg
  have hproc_eq : ∀ (past : List (WrapperState N M)) (st : WrapperState N M),
      P.proc σ past st =
        let wAlg := (alg fun i => (st.val i : ℝ)).filter fun i => 0 < st.val i
        let wBase := if ∑ i ∈ st.winners, st.val i ≤ ∑ i ∈ wAlg, st.val i then wAlg else st.winners
        (ksmExtendPareto bundle st.losers wBase, st.bundle) := fun _ _ => rfl
  have hinv : ∀ j : ℕ,
      Disjoint (wrapperState P σ j).winners (wrapperState P σ j).losers ∧
      ((wrapperState P σ j).winners : Set N).PairwiseDisjoint bundle := by
    intro j
    induction j with
    | zero =>
      simp only [wrapperState_zero, initState, Finset.disjoint_empty_left, Finset.coe_empty,
        Set.pairwiseDisjoint_empty, and_self]
    | succ j ih =>
      by_cases ht : TerminatedAt P σ j
      · rwa [wrapperState_succ_of_terminatedAt ht]
      · set st := wrapperState P σ j
        let wAlg := (alg fun i => (st.val i : ℝ)).filter fun i => 0 < st.val i
        have hwAlg_disj : Disjoint wAlg st.losers := by
          rw [Finset.disjoint_left]
          intro i hi hiL
          rw [mem_losers_iff_val_eq_zero] at hiL
          exact (Finset.mem_filter.1 hi).2.ne' hiL
        have hwAlg_pw : (wAlg : Set N).PairwiseDisjoint bundle :=
          (halg_feas _ fun _ => Nat.cast_nonneg _).subset
            (by exact_mod_cast Finset.filter_subset _ _)
        let wBase := if ∑ i ∈ st.winners, st.val i ≤ ∑ i ∈ wAlg, st.val i then wAlg else st.winners
        have hwBase_disj : Disjoint wBase st.losers := by
          simp only [wBase]; split_ifs <;> [exact hwAlg_disj; exact ih.1]
        have hwBase_pw : (wBase : Set N).PairwiseDisjoint bundle := by
          simp only [wBase]; split_ifs <;> [exact hwAlg_pw; exact ih.2]
        obtain ⟨_, hd_ext, hp_ext, _⟩ := ksmExtendPareto_props bundle st.losers wBase
          hwBase_disj hwBase_pw
        have hW' : (wrapperState P σ (j + 1)).winners =
            ksmExtendPareto bundle st.losers wBase :=
          wrapperState_succ_winners ht
        refine ⟨?_, hW' ▸ hp_ext⟩
        rw [Finset.disjoint_left]
        intro i hiW hiL
        rw [mem_losers_iff_val_eq_zero] at hiL
        rw [hW'] at hiW
        have hnotL : i ∉ st.losers := Finset.disjoint_left.1 hd_ext hiW
        have hnz : st.val i ≠ 0 := mt (mem_losers_iff_val_eq_zero P σ j i).2 hnotL
        have hval_eq : (wrapperState P σ (j + 1)).val i = st.val i := by
          rw [wrapperState_succ_val ht i]
          have hmem : i ∈ (P.proc σ (wrapperRunHist P σ j).2 (wrapperRunHist P σ j).1).1 ∪
              (wrapperRunHist P σ j).1.losers := Finset.mem_union_left _ hiW
          simp only [hmem, ↓reduceIte]
          rfl
        exact hnz (hval_eq.symm.trans hiL)
  constructor
  · intro j _
    set st := wrapperState P σ j
    have hbun : st.bundle = bundle := ksmProc_bundle_eq bundle alg σ j
    let wAlg := (alg fun i => (st.val i : ℝ)).filter fun i => 0 < st.val i
    have hwAlg_disj : Disjoint wAlg st.losers := by
      rw [Finset.disjoint_left]
      intro i hi hiL
      rw [mem_losers_iff_val_eq_zero] at hiL
      exact (Finset.mem_filter.1 hi).2.ne' hiL
    have hwAlg_pw : (wAlg : Set N).PairwiseDisjoint bundle :=
      (halg_feas _ fun _ => Nat.cast_nonneg _).subset (by exact_mod_cast Finset.filter_subset _ _)
    let wBase := if ∑ i ∈ st.winners, st.val i ≤ ∑ i ∈ wAlg, st.val i then wAlg else st.winners
    have hwBase_disj : Disjoint wBase st.losers := by
      simp only [wBase]; split_ifs <;> [exact hwAlg_disj; exact (hinv j).1]
    have hwBase_pw : (wBase : Set N).PairwiseDisjoint bundle := by
      simp only [wBase]; split_ifs <;> [exact hwAlg_pw; exact (hinv j).2]
    obtain ⟨_, hd_ext, hp_ext, hpar_ext⟩ :=
      ksmExtendPareto_props bundle st.losers wBase hwBase_disj hwBase_pw
    change (ksmExtendPareto bundle st.losers wBase : Set N).PairwiseDisjoint st.bundle ∧
      Disjoint (ksmExtendPareto bundle st.losers wBase) st.losers ∧
      (∀ i, i ∉ ksmExtendPareto bundle st.losers wBase ∪ st.losers →
        ∃ l ∈ ksmExtendPareto bundle st.losers wBase, ¬ Disjoint (st.bundle i) (st.bundle l)) ∧
      (∀ i, st.bundle i ⊆ st.bundle i)
    rw [hbun]
    exact ⟨hp_ext, hd_ext, hpar_ext, fun _ => Subset.rfl⟩
  · intro j _
    set st := wrapperState P σ j
    let wAlg := (alg fun i => (st.val i : ℝ)).filter fun i => 0 < st.val i
    let wBase := if ∑ i ∈ st.winners, st.val i ≤ ∑ i ∈ wAlg, st.val i then wAlg else st.winners
    have hle_base : ∑ i ∈ st.winners, st.val i ≤ ∑ i ∈ wBase, st.val i := by
      simp only [wBase]; split_ifs with h <;> [exact h; exact le_rfl]
    have hsub : wBase ⊆ ksmExtendPareto bundle st.losers wBase := by
      have hwAlg_disj : Disjoint wAlg st.losers := by
        rw [Finset.disjoint_left]
        intro i hi hiL
        rw [mem_losers_iff_val_eq_zero] at hiL
        exact (Finset.mem_filter.1 hi).2.ne' hiL
      have hwAlg_pw : (wAlg : Set N).PairwiseDisjoint bundle :=
        (halg_feas _ fun _ => Nat.cast_nonneg _).subset (by exact_mod_cast Finset.filter_subset _ _)
      have hwBase_disj : Disjoint wBase st.losers := by
        simp only [wBase]; split_ifs <;> [exact hwAlg_disj; exact (hinv j).1]
      have hwBase_pw : (wBase : Set N).PairwiseDisjoint bundle := by
        simp only [wBase]; split_ifs <;> [exact hwAlg_pw; exact (hinv j).2]
      exact (ksmExtendPareto_props bundle st.losers wBase hwBase_disj hwBase_pw).1
    exact hle_base.trans (Finset.sum_le_sum_of_subset hsub)

private theorem ksmDominantSet_val_le {bundle : N → Finset M} {alg : (N → ℝ) → Finset N}
    {σ : N → KsmStrategy N M} {i : N} {v : ℝ} (hv : 1 ≤ v)
    (hs : σ i ∈ ksmDominantSet i v) (j : ℕ) :
    ((wrapperState (ksmProc bundle alg) σ j).val i : ℝ) ≤ v := by
  set P := ksmProc bundle alg
  induction j with
  | zero =>
    simpa only [wrapperState_zero, initState, Nat.cast_one] using hv
  | succ j ih =>
    by_cases ht : TerminatedAt P σ j
    · rwa [wrapperState_succ_of_terminatedAt ht]
    · set cur := wrapperRunHist P σ j
      set res := P.proc σ cur.2 cur.1
      have hval_succ : (wrapperState P σ (j + 1)).val i =
          if i ∈ res.1 ∪ cur.1.losers then cur.1.val i
          else if σ i cur.2 cur.1 res.1 res.2 then 2 * cur.1.val i else 0 :=
        wrapperState_succ_val ht i
      rw [hval_succ]
      split_ifs with h1 h2
      · exact ih
      · by_contra hgt
        push Not at hgt
        have hgt' : v < 2 * (cur.1.val i : ℝ) := by
          have : ((2 * cur.1.val i : ℕ) : ℝ) = 2 * (cur.1.val i : ℝ) := by
            rw [Nat.cast_mul, Nat.cast_ofNat]
          linarith
        have hfalse := (hs cur.2 cur.1 res.1 res.2).1 hgt'
        exact Bool.false_ne_true (hfalse.symm.trans h2)
      · simp only [Nat.cast_zero]
        linarith

private theorem ksmDominantSet_retire_ge {bundle : N → Finset M} {alg : (N → ℝ) → Finset N}
    {σ : N → KsmStrategy N M} {i : N} {v : ℝ} (hs : σ i ∈ ksmDominantSet i v)
    {j : ℕ} (hi : i ∈ retiredAt (ksmProc bundle alg) σ j) :
    v / 2 ≤ ((wrapperState (ksmProc bundle alg) σ j).val i : ℝ) := by
  set P := ksmProc bundle alg
  rw [retiredAt, Finset.mem_sdiff] at hi
  obtain ⟨hi1, hi0⟩ := hi
  have hnotT : ¬ TerminatedAt P σ j := fun ht =>
    hi0 (by rwa [wrapperState_succ_of_terminatedAt ht] at hi1)
  rw [mem_losers_iff_val_eq_zero] at hi1
  set cur := wrapperRunHist P σ j
  set res := P.proc σ cur.2 cur.1
  have hnz : cur.1.val i ≠ 0 := mt (mem_losers_iff_val_eq_zero P σ j i).2 hi0
  have hval_succ : (wrapperState P σ (j + 1)).val i =
      if i ∈ res.1 ∪ cur.1.losers then cur.1.val i
      else if σ i cur.2 cur.1 res.1 res.2 then 2 * cur.1.val i else 0 :=
    wrapperState_succ_val hnotT i
  rw [hval_succ] at hi1
  by_contra hlt
  push Not at hlt
  have hlt' : 2 * (cur.1.val i : ℝ) < v := by
    have : (cur.1.val i : ℝ) = ((wrapperState P σ j).val i : ℝ) := rfl
    linarith
  have htrue : σ i cur.2 cur.1 res.1 res.2 = true := (hs cur.2 cur.1 res.1 res.2).2 hlt'
  rw [htrue] at hi1
  simp only [↓reduceIte] at hi1
  split_ifs at hi1
  · exact hnz hi1
  · exact mul_ne_zero two_ne_zero hnz hi1

omit [Fintype N] [LinearOrder N] [DecidableEq M] in
/-- **Proposition 12.41 (retirement threshold)** ([Lavi2007], §12.5, p. 323): under the canonical
dominant strategy `ksmDominantStrategy i v`, at any non-overbidding bid `v_i^j ≤ v`, player `i`
chooses to retire (`false`) iff `v / 2 ≤ v_i^j ≤ v`. -/
theorem ksmDominantStrategy_retire_iff (i : N) {v : ℝ} (past : List (WrapperState N M))
    (st : WrapperState N M) (W' : Finset N) (s' : N → Finset M)
    (hle : (st.val i : ℝ) ≤ v) :
    ksmDominantStrategy i v past st W' s' = false ↔
      v / 2 ≤ (st.val i : ℝ) ∧ (st.val i : ℝ) ≤ v := by
  classical
  simp only [ksmDominantStrategy, decide_eq_false_iff_not, not_lt]
  constructor
  · intro h; exact ⟨by linarith, hle⟩
  · intro ⟨h, _⟩; linarith

/-- **Proposition 12.41 (dominant strategy)** ([Lavi2007], §12.5, p. 323): for any player `i`
desiring `bundle i`, `ksmDominantStrategy i p.value` is a dominant strategy in `Wrapper + KSM-PROC`
against all opponent full-history strategies. -/
theorem ksmDominantStrategy_isDominant (bundle : N → Finset M) (alg : (N → ℝ) → Finset N)
    {halg_feas : ∀ v : N → ℝ, (∀ i, 0 ≤ v i) → (alg v : Set N).PairwiseDisjoint bundle}
    (i : N) (p : SingleValuePlayer M) (hb : bundle i ∈ p.desired) :
    (ksmProc bundle alg).IsDominantStrategy p i (ksmDominantStrategy i p.value) := by
  intro st σ
  set P := ksmProc bundle alg
  set σ₁ := Function.update σ i st
  set σ₂ := Function.update σ i (ksmDominantStrategy i p.value)
  have hutil₂_nonneg : 0 ≤ P.utility σ₂ p i := by
    classical
    simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment]
    split_ifs with hT hW
    · have hbun : (wrapperState P σ₂ (termRound P σ₂)).bundle i = bundle i := by
        rw [ksmProc_bundle_eq]
      rw [hbun, p.eval_of_mem hb]
      have hσ₂i : σ₂ i ∈ ksmDominantSet i p.value := by
        simpa only [σ₂, Function.update_self] using ksmDominantStrategy_mem (M := M) i p.value
      have hle := ksmDominantSet_val_le (bundle := bundle) (alg := alg) p.one_le_value hσ₂i
        (termRound P σ₂)
      linarith
    · simp only [SingleValuePlayer.eval_empty, sub_zero, le_refl]
    · simp only [SingleValuePlayer.eval_empty, sub_zero, le_refl]
  by_cases heq : ∀ j, wrapperRunHist P σ₁ j = wrapperRunHist P σ₂ j
  · have hstEq : ∀ j, wrapperState P σ₁ j = wrapperState P σ₂ j := fun j =>
      congrArg Prod.fst (heq j)
    have hTeq : Terminates P σ₁ ↔ Terminates P σ₂ := by
      simp only [Terminates, TerminatedAt, hstEq]
    have hreq : termRound P σ₁ = termRound P σ₂ := by
      classical
      simp only [termRound, hTeq]
      split_ifs with hT₂
      · refine le_antisymm ?_ ?_
        · exact Nat.find_min' (hTeq.2 hT₂)
            (by simpa only [TerminatedAt, hstEq] using Nat.find_spec hT₂)
        · exact Nat.find_min' hT₂
            (by simpa only [TerminatedAt, ← hstEq] using Nat.find_spec (hTeq.2 hT₂))
      · rfl
    have haeq : P.alloc σ₁ i = P.alloc σ₂ i := by
      classical simp only [WrapperProc.alloc, hTeq, hreq, hstEq]
    have hpeq : P.payment σ₁ i = P.payment σ₂ i := by
      classical simp only [WrapperProc.payment, hTeq, hreq, hstEq]
    simp only [WrapperProc.utility, haeq, hpeq, le_refl]
  · -- First iteration where the two runs diverge.
    classical
    push Not at heq
    set m := Nat.find heq
    have hm_ne : wrapperRunHist P σ₁ m ≠ wrapperRunHist P σ₂ m := Nat.find_spec heq
    have hm_pos : 0 < m := by
      by_contra h0
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos h0
      exact hm_ne (by simp only [hm0, wrapperRunHist])
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm_pos.ne'
    rw [hj] at hm_ne
    have hj_eq : wrapperRunHist P σ₁ j = wrapperRunHist P σ₂ j := by
      by_contra hne
      exact Nat.find_min heq (by omega : j < m) hne
    have hnotT₁ : ¬ TerminatedAt P σ₁ j := by
      intro ht
      have ht₂ : TerminatedAt P σ₂ j := by
        simpa only [TerminatedAt, wrapperState, hj_eq] using ht
      apply hm_ne
      simp only [wrapperRunHist, wrapperNext, TerminatedAt, wrapperState] at ht ht₂ ⊢
      simp only [hj_eq, ht₂, ↓reduceIte]
    have hst_eq : wrapperState P σ₁ j = wrapperState P σ₂ j := congrArg Prod.fst hj_eq
    -- `P.proc` ignores strategies, so `(W', s')` is identical for `σ₁` and `σ₂` at iteration `j`.
    set cur := wrapperRunHist P σ₁ j
    set res := P.proc σ₁ cur.2 cur.1
    have hproc_eq : P.proc σ₁ cur.2 cur.1 = P.proc σ₂ cur.2 cur.1 := rfl
    have hnotMem : i ∉ res.1 ∪ cur.1.losers := by
      intro hm
      apply hm_ne
      simp only [wrapperRunHist]
      refine Prod.ext ?_ (by
        change (wrapperRunHist P σ₁ j).1 :: (wrapperRunHist P σ₁ j).2 =
          (wrapperRunHist P σ₂ j).1 :: (wrapperRunHist P σ₂ j).2
        rw [← hj_eq])
      rw [← hj_eq]
      exact wrapperNext_congr hproc_eq fun k hk => by
        have hki : k ≠ i := fun h => hk (h ▸ hm)
        have hσk : σ₁ k = σ₂ k := by simp only [σ₁, σ₂, Function.update_of_ne hki]
        simp only [hσk]
        rfl
    have hch_ne : σ₁ i cur.2 cur.1 res.1 res.2 ≠ σ₂ i cur.2 cur.1 res.1 res.2 := by
      intro hch
      apply hm_ne
      simp only [wrapperRunHist]
      refine Prod.ext ?_ (by
        change (wrapperRunHist P σ₁ j).1 :: (wrapperRunHist P σ₁ j).2 =
          (wrapperRunHist P σ₂ j).1 :: (wrapperRunHist P σ₂ j).2
        rw [← hj_eq])
      rw [← hj_eq]
      exact wrapperNext_congr hproc_eq fun k _ => by
        by_cases hk : k = i
        · subst hk; exact hch
        · have hσk : σ₁ k = σ₂ k := by simp only [σ₁, σ₂, Function.update_of_ne hk]
          simp only [hσk]
          rfl
    -- Because `chooseDouble` differs for `i ∉ W' ∪ L_j`, `st` chose opposite to the dominant move.
    have hutil₁_le_zero : P.utility σ₁ p i ≤ 0 := by
      have hproper₁ := (ksmProc_isProperOn_and_hasImprovementOn bundle halg_feas σ₁).1
      by_cases hT₁ : Terminates P σ₁
      · have hJ_ge : j + 1 ≤ termRound P σ₁ := by
          by_contra hlt
          push Not at hlt
          exact hnotT₁ (terminatedAt_mono (termRound_spec hT₁) (Nat.le_of_lt_succ hlt))
        have hval_j1 : (wrapperState P σ₁ (j + 1)).val i =
            if σ₁ i cur.2 cur.1 res.1 res.2 then 2 * cur.1.val i else 0 := by
          rw [wrapperState_succ_val hnotT₁ i]
          change (if i ∈ res.1 ∪ cur.1.losers then cur.1.val i
            else if σ₁ i cur.2 cur.1 res.1 res.2 then 2 * cur.1.val i else 0) = _
          simp only [hnotMem, ↓reduceIte]
        cases hst_ch : σ₁ i cur.2 cur.1 res.1 res.2
        · -- `st` retired at iteration `j`, so `i ∈ L_J`, hence `i ∉ W_J` and utility is `0`.
          have hret₁ : (wrapperState P σ₁ (j + 1)).val i = 0 := by
            simp only [hval_j1, hst_ch, Bool.false_eq_true, ↓reduceIte]
          have hiL : i ∈ (wrapperState P σ₁ (termRound P σ₁)).losers :=
            losers_mono P σ₁ hJ_ge ((mem_losers_iff_val_eq_zero P σ₁ (j + 1) i).2 hret₁)
          have hiNotW : i ∉ (wrapperState P σ₁ (termRound P σ₁)).winners :=
            Finset.disjoint_right.1 (disjoint_winners_losers_of_isProperOn hproper₁ _) hiL
          simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment, hT₁, ↓reduceIte,
            hiNotW, SingleValuePlayer.eval_empty, sub_zero, le_refl]
        · -- `st` doubled while `ksmDominantStrategy` retired, so `2 * v_i^j ≥ p.value`.
          have hdom_false :
              ksmDominantStrategy (M := M) i p.value cur.2 cur.1 res.1 res.2 = false := by
            have hσ₂i : σ₂ i = ksmDominantStrategy i p.value := Function.update_self i _ σ
            rw [hst_ch, hσ₂i] at hch_ne
            cases h2 : ksmDominantStrategy (M := M) i p.value cur.2 cur.1 res.1 res.2
            · rfl
            · exact absurd h2.symm hch_ne
          have hge_val : p.value ≤ ((wrapperState P σ₁ (j + 1)).val i : ℝ) := by
            simp only [hval_j1, hst_ch, ↓reduceIte, Nat.cast_mul, Nat.cast_ofNat]
            simp only [ksmDominantStrategy, decide_eq_false_iff_not, not_lt] at hdom_false
            exact hdom_false
          simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment, hT₁, ↓reduceIte]
          split_ifs with hW
          · have hiNotL : i ∉ (wrapperState P σ₁ (termRound P σ₁)).losers :=
              Finset.disjoint_left.1 (disjoint_winners_losers_of_isProperOn hproper₁ _) hW
            have hmono : ((wrapperState P σ₁ (j + 1)).val i : ℝ) ≤
                ((wrapperState P σ₁ (termRound P σ₁)).val i : ℝ) := by
              exact_mod_cast val_mono_of_not_mem_losers P σ₁ hJ_ge hiNotL
            linarith [p.eval_le_value ((wrapperState P σ₁ (termRound P σ₁)).bundle i)]
          · simp only [SingleValuePlayer.eval_empty, sub_zero, le_refl]
      · simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment, hT₁, ↓reduceIte,
          SingleValuePlayer.eval_empty, sub_zero, le_refl]
    exact hutil₁_le_zero.trans hutil₂_nonneg

/-- **Claim 12.43** ([Lavi2007], §12.5, p. 324): given any feasible `c`-approximation algorithm
`alg` for KSM players with public bundles `bundle`, `ksmProc bundle alg` is a
`c`-local-approximation with respect to `ksmDominantSet`. -/
theorem ksmProc_isLocalApproxOn [Fintype M] (bundle : N → Finset M)
    (hbundle : ∀ i, (bundle i).Nonempty) (v : N → ℝ) (hv : ∀ i, 1 ≤ v i)
    {alg : (N → ℝ) → Finset N} {c : ℝ} (hc : 0 ≤ c)
    (halg_feas : ∀ w : N → ℝ, (∀ i, 0 ≤ w i) → (alg w : Set N).PairwiseDisjoint bundle)
    (halg_approx : ∀ (w : N → ℝ), (∀ i, 0 ≤ w i) → ∀ W : Finset N,
      (W : Set N).PairwiseDisjoint bundle → ∑ i ∈ W, w i ≤ c * ∑ i ∈ alg w, w i) :
    let players := fun i => SingleValuePlayer.singleMinded (bundle i) (hbundle i) (v i) (hv i)
    (ksmProc bundle alg).IsLocalApproxOn players (fun i => ksmDominantSet i (v i)) c := by
  intro players σ hσ
  obtain ⟨hproper, himp⟩ := ksmProc_isProperOn_and_hasImprovementOn bundle halg_feas σ
  refine ⟨hproper, himp, ?_, ?_, ?_, ?_⟩
  · intro j hnotT
    classical
    set st := wrapperState (ksmProc bundle alg) σ j
    obtain ⟨alloc, hfeas, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn
      (retiredAt (ksmProc bundle alg) σ j) (fun i => (st.val i : ℝ))
      (restrictedDesired (fun i => (players i).desired) st.bundle)
    rw [← hEq]
    let Wopt : Finset N := (retiredAt (ksmProc bundle alg) σ j).filter fun i =>
      alloc i ∈ restrictedDesired (fun k => (players k).desired) st.bundle i
    have hWopt_pw : (Wopt : Set N).PairwiseDisjoint bundle := by
      intro i₁ h1 i₂ h2 hne
      have hb1 : bundle i₁ ⊆ alloc i₁ := (Finset.mem_filter.1 h1).2.1
      have hb2 : bundle i₂ ⊆ alloc i₂ := (Finset.mem_filter.1 h2).2.1
      exact (hfeas hne).mono hb1 hb2
    have hsum_eq : welfareOn (retiredAt (ksmProc bundle alg) σ j) (fun i => (st.val i : ℝ))
        (restrictedDesired (fun i => (players i).desired) st.bundle) alloc =
        ∑ i ∈ Wopt, (st.val i : ℝ) := by
      simp only [welfareOn, Wopt, Finset.sum_filter]
    rw [hsum_eq]
    have happrox := halg_approx (fun i => (st.val i : ℝ)) (fun _ => Nat.cast_nonneg _) Wopt hWopt_pw
    let wAlg := (alg fun i => (st.val i : ℝ)).filter fun i => 0 < st.val i
    have hfilter_eq : ∑ i ∈ alg (fun i => (st.val i : ℝ)), (st.val i : ℝ) =
        ∑ i ∈ wAlg, (st.val i : ℝ) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => ?_
      simp only [wAlg, Finset.mem_filter, not_and, not_lt, Nat.le_zero] at hi
      have h0 : st.val i = 0 := hi (by assumption)
      simp only [h0, Nat.cast_zero]
    let wBase := if ∑ i ∈ st.winners, st.val i ≤ ∑ i ∈ wAlg, st.val i then wAlg else st.winners
    have hwAlg_le_base : ∑ i ∈ wAlg, (st.val i : ℝ) ≤ ∑ i ∈ wBase, (st.val i : ℝ) := by
      have hnat : ∑ i ∈ wAlg, st.val i ≤ ∑ i ∈ wBase, st.val i := by
        simp only [wBase]
        split_ifs with h
        · exact le_rfl
        · exact le_of_not_ge h
      exact_mod_cast hnat
    have hbase_sub : wBase ⊆ (wrapperState (ksmProc bundle alg) σ (j + 1)).winners := by
      have hW1 : (wrapperState (ksmProc bundle alg) σ (j + 1)).winners =
          ksmExtendPareto bundle st.losers wBase := by
        simp only [wrapperState, wrapperRunHist, wrapperNext, TerminatedAt, ksmProc, st, wBase,
          wAlg] at hnotT ⊢
        simp only [hnotT, ↓reduceIte]
      rw [hW1]
      have hwAlg_disj : Disjoint wAlg st.losers := by
        rw [Finset.disjoint_left]
        intro i hi hiL
        rw [mem_losers_iff_val_eq_zero] at hiL
        exact (Finset.mem_filter.1 hi).2.ne' hiL
      have hwAlg_pw : (wAlg : Set N).PairwiseDisjoint bundle :=
        (halg_feas _ fun _ => Nat.cast_nonneg _).subset (by exact_mod_cast Finset.filter_subset _ _)
      have hst_disj := disjoint_winners_losers_of_isProperOn hproper j
      have hst_pw : (st.winners : Set N).PairwiseDisjoint bundle := by
        simpa only [ksmProc_bundle_eq] using winners_pairwiseDisjoint_of_isProperOn hproper j
      have hwBase_disj : Disjoint wBase st.losers := by
        simp only [wBase]; split_ifs <;> [exact hwAlg_disj; exact hst_disj]
      have hwBase_pw : (wBase : Set N).PairwiseDisjoint bundle := by
        simp only [wBase]; split_ifs <;> [exact hwAlg_pw; exact hst_pw]
      exact (ksmExtendPareto_props bundle st.losers wBase hwBase_disj hwBase_pw).1
    have hbase_le_W1 : ∑ i ∈ wBase, (st.val i : ℝ) ≤
        ∑ i ∈ (wrapperState (ksmProc bundle alg) σ (j + 1)).winners, (st.val i : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hbase_sub fun _ _ _ => Nat.cast_nonneg _
    exact happrox.trans (mul_le_mul_of_nonneg_left
      (hfilter_eq.trans_le (hwAlg_le_base.trans hbase_le_W1)) hc)
  · intro j i
    rw [ksmProc_bundle_eq]
    exact Subset.rfl
  · intro j i
    exact ksmDominantSet_val_le (hv i) (hσ i) j
  · intro j i hi
    exact ksmDominantSet_retire_ge (hσ i) hi

/-- **Theorem 12.45** ([Lavi2007], §12.5, p. 324): given any feasible `c`-approximation algorithm
`alg` for known single-minded players with `1 ≤ v_i ≤ v_max`, `Wrapper + KSM-PROC` is a
dominant-strategy implementation achieving welfare approximation
`1 + 2 * (2 * Nat.log 2 ⌊v_max⌋₊ + 1) * c = O(log(v_max) * c)`. -/
theorem ksmProc_isDominantStrategyImpl [Fintype M] (bundle : N → Finset M)
    (hbundle : ∀ i, (bundle i).Nonempty) (v : N → ℝ) (hv : ∀ i, 1 ≤ v i)
    {v_max : ℝ} (hv_le : ∀ i, v i ≤ v_max)
    {alg : (N → ℝ) → Finset N} {c : ℝ} (hc : 0 ≤ c)
    (halg_feas : ∀ w : N → ℝ, (∀ i, 0 ≤ w i) → (alg w : Set N).PairwiseDisjoint bundle)
    (halg_approx : ∀ (w : N → ℝ), (∀ i, 0 ≤ w i) → ∀ W : Finset N,
      (W : Set N).PairwiseDisjoint bundle → ∑ i ∈ W, w i ≤ c * ∑ i ∈ alg w, w i) :
    let players := fun i => SingleValuePlayer.singleMinded (bundle i) (hbundle i) (v i) (hv i)
    (ksmProc bundle alg).IsDominantStrategyImpl players (fun i => ksmDominantStrategy i (v i))
      (1 + 2 * (2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 1) * c) := by
  intro players
  set P := ksmProc bundle alg
  set σStar : N → KsmStrategy N M := fun i => ksmDominantStrategy i (v i)
  have hloc := ksmProc_isLocalApproxOn bundle hbundle v hv hc halg_feas halg_approx
  have hσStar_mem : ∀ i, σStar i ∈ ksmDominantSet i (v i) := fun i =>
    ksmDominantStrategy_mem i (v i)
  obtain ⟨hT, _, _, hrBar⟩ := P.optWelfare_rBar_le hloc hc hv_le hσStar_mem
  obtain ⟨hproper, _, _, hdes, _, _⟩ := hloc σStar hσStar_mem
  set J := termRound P σStar
  have hSW : P.socialWelfare σStar players = ∑ i ∈ (wrapperState P σStar J).winners, v i :=
    socialWelfare_eq_sum_winners hT fun i _ => hdes J i
  -- For KSM players, restricting to `bundle i` does not reduce optimal welfare over `L_J`.
  have hopt_losers : optWelfareOn (wrapperState P σStar J).losers v (fun i => (players i).desired) ≤
      optWelfareOn (wrapperState P σStar J).losers v (rBarDesired P σStar players) := by
    classical
    obtain ⟨alloc, hfeas, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn
      (wrapperState P σStar J).losers v (fun i => (players i).desired)
    rw [← hEq]
    let alloc' : N → Finset M := fun i => if bundle i ⊆ alloc i then bundle i else ∅
    have hfeas' : IsFeasibleAlloc alloc' := by
      intro i₁ i₂ hne
      simp only [alloc']
      split_ifs with h1 h2
      · exact (hfeas hne).mono h1 h2
      · exact Finset.disjoint_empty_right _
      · exact Finset.disjoint_empty_left _
      · exact Finset.disjoint_empty_left _
    have hw_eq : welfareOn (wrapperState P σStar J).losers v (fun i => (players i).desired) alloc =
        welfareOn (wrapperState P σStar J).losers v (rBarDesired P σStar players) alloc' := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hbun : (wrapperState P σStar (retireRound P σStar i)).bundle i = bundle i := by
        rw [ksmProc_bundle_eq]
      by_cases hsub : bundle i ⊆ alloc i
      · have hmem₁ : alloc i ∈ (players i).desired := hsub
        have hmem₂ : alloc' i ∈ rBarDesired P σStar players i := by
          simp only [rBarDesired, restrictedDesired, hbun, alloc', hsub, ↓reduceIte]
          exact ⟨Subset.rfl, Subset.rfl⟩
        simp only [hmem₁, hmem₂, ↓reduceIte]
      · have hmem₁ : alloc i ∉ (players i).desired := hsub
        have hmem₂ : alloc' i ∉ rBarDesired P σStar players i := by
          simp only [rBarDesired, restrictedDesired, hbun, alloc', hsub, ↓reduceIte]
          intro h
          exact (hbundle i).ne_empty (Finset.subset_empty.1 h.1)
        simp only [hmem₁, hmem₂, ↓reduceIte]
    rw [hw_eq]
    exact welfareOn_le_optWelfareOn _ _ _ hfeas'
  have hopt_all : optWelfare players ≤
      (1 + 2 * (2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 1) * c) * P.socialWelfare σStar players := by
    have huniv : Finset.univ = (wrapperState P σStar J).winners ∪ (wrapperState P σStar J).losers :=
      (termRound_spec hT).symm
    have hv_eq : (fun i => (players i).value) = v := rfl
    have hsplit : optWelfare players ≤
        optWelfareOn (wrapperState P σStar J).winners v (fun i => (players i).desired) +
        optWelfareOn (wrapperState P σStar J).losers v (fun i => (players i).desired) := by
      simp only [optWelfare, hv_eq]
      rw [huniv]
      exact optWelfareOn_union_le fun i _ => (players i).value_pos.le
    have hW_le : optWelfareOn (wrapperState P σStar J).winners v (fun i => (players i).desired) ≤
        P.socialWelfare σStar players := by
      rw [hSW]
      exact optWelfareOn_le_sum fun i _ => (players i).value_pos.le
    rw [hv_eq] at hrBar
    linarith
  exact ⟨fun i => ksmDominantStrategy_isDominant bundle alg (halg_feas := halg_feas) i (players i)
      Subset.rfl,
    hT, P.isFeasibleAlloc_of_isProperOn hproper, hopt_all⟩

end KsmProc

/-! ### Single-Value Players (`1-CA-PROC`, Lemmas 12.47 & 12.49, Claim 12.50, Theorem 12.51) -/

section OneCaProc

variable [Fintype N] [LinearOrder N] [Fintype M] [DecidableEq M]

/-- Items not allocated to any player in `X` under bundle assignment `s` ([Lavi2007], p. 325):
`Free(X, s) = Ω \ ⋃_{i ∈ X} s_i`. -/
@[expose] def freeItems (X : Finset N) (s : N → Finset M) : Finset M :=
  Finset.univ \ X.biUnion s

omit [Fintype N] [LinearOrder N] in
private theorem subset_freeItems_iff (X : Finset N) (s : N → Finset M) (b : Finset M) :
    b ⊆ freeItems X s ↔ ∀ k ∈ X, Disjoint b (s k) := by
  rw [freeItems, Finset.subset_sdiff, and_iff_right (Finset.subset_univ b),
    Finset.disjoint_biUnion_right]

/-- Intermediate state visible to player `i` when asked to shrink her bundle during `1-CA-PROC`
([Lavi2007], Definition 12.46, p. 325). -/
structure OneCaShrinkView (N M : Type*) where
  /-- Past wrapper states (strictly earlier iterations). -/
  past : List (WrapperState N M)
  /-- Wrapper state at the start of the current iteration `j`. -/
  state : WrapperState N M
  /-- Current tentative winner allocation `W_j` (with earlier updates in this iteration). -/
  currentWinners : Finset N
  /-- Current max-bidder allocation `M_j` (with earlier updates in this iteration). -/
  currentMax : Finset N
  /-- Current greedy allocation `GREEDY_j` (with earlier updates in this iteration). -/
  currentGreedy : Finset N
  /-- Current bundles `s^{j+1}` (updated for players already processed in this iteration). -/
  currentBundles : N → Finset M

/-- Full-history adaptive strategy for `Wrapper + 1-CA-PROC`. -/
structure OneCaStrategy (N M : Type*) where
  /-- Bundle shrink choice during `1-CA-PROC`: `some b` to shrink to `b`, or `none` to stay
  silent. Invalid bundles are ignored (treated as silent). -/
  shrink : OneCaShrinkView N M → Option (Finset M)
  /-- Step-2 choice when an active nonwinner: `true` to double, `false` to permanently retire. -/
  double : List (WrapperState N M) → WrapperState N M → Finset N → (N → Finset M) → Bool

/-- Validity of a shrink choice `b` in `1-CA-PROC`: nonempty, contained in
`Free(GREEDY_j, s^{j+1}) ∩ s_i^j`, and of cardinality at most `⌊√m⌋` (equivalently `≤ √m`). -/
@[expose] def IsValidShrink (G : Finset N) (s : N → Finset M) (cur b : Finset M) : Prop :=
  b.Nonempty ∧ b ⊆ freeItems G s ∩ cur ∧ b.card ≤ Nat.sqrt (Fintype.card M)

instance (G : Finset N) (s : N → Finset M) (cur b : Finset M) :
    Decidable (IsValidShrink G s cur b) := by
  unfold IsValidShrink
  infer_instance

private theorem card_le_natSqrt_iff (k m : ℕ) :
    k ≤ Nat.sqrt m ↔ (k : ℝ) ≤ Real.sqrt (m : ℝ) := by
  rw [Nat.le_sqrt, Real.le_sqrt (Nat.cast_nonneg k) (Nat.cast_nonneg m), sq]
  exact_mod_cast Iff.rfl

/-- Descending bid order with deterministic tie-breaking by `≤` on `N`. -/
private def oneCaRel (v : N → ℕ) (i k : N) : Prop :=
  v k < v i ∨ (v k = v i ∧ i ≤ k)

private instance (v : N → ℕ) : DecidableRel (oneCaRel v) := fun i k => by
  unfold oneCaRel; infer_instance

private instance (v : N → ℕ) : Std.Total (oneCaRel v) := ⟨fun a b => by
  unfold oneCaRel
  rcases lt_trichotomy (v a) (v b) with h | h | h
  · exact Or.inr (Or.inl h)
  · rcases le_total a b with hab | hba
    · exact Or.inl (Or.inr ⟨h.symm, hab⟩)
    · exact Or.inr (Or.inr ⟨h, hba⟩)
  · exact Or.inl (Or.inl h)⟩

private instance (v : N → ℕ) : IsTrans N (oneCaRel v) := ⟨fun a b c hab hbc => by
  unfold oneCaRel at hab hbc ⊢
  rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hbc with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h2.trans h1)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h2.trans h1, h1'.trans h2'⟩⟩

private instance (v : N → ℕ) : Std.Antisymm (oneCaRel v) := ⟨fun a b hab hba => by
  unfold oneCaRel at hab hba
  rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hba with h2 | ⟨h2, h2'⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · exact absurd (h2 ▸ h1) (lt_irrefl _)
  · exact absurd (h1 ▸ h2) (lt_irrefl _)
  · exact le_antisymm h1' h2'⟩

/-- Accumulator state inside one iteration of `1-CA-PROC`. -/
private structure OneCaAcc (N M : Type*) where
  wSet : Finset N
  mSet : Finset N
  gSet : Finset N
  bundles : N → Finset M

/-- Effective bundle selected for player `i` during `1-CA-PROC`. -/
private def oneCaPickBundle (σ : N → OneCaStrategy N M) (past : List (WrapperState N M))
    (st : WrapperState N M) (acc : OneCaAcc N M) (i : N) : Finset M :=
  if i ∈ st.winners then acc.bundles i
  else
    let view : OneCaShrinkView N M := ⟨past, st, acc.wSet, acc.mSet, acc.gSet, acc.bundles⟩
    match (σ i).shrink view with
    | some b => if IsValidShrink acc.gSet acc.bundles (acc.bundles i) b then b else acc.bundles i
    | none => acc.bundles i

/-- One player step of the descending-value loop in `1-CA-PROC` ([Lavi2007], Definition 12.46,
p. 325). -/
private def oneCaStep (σ : N → OneCaStrategy N M) (past : List (WrapperState N M))
    (st : WrapperState N M) (acc : OneCaAcc N M) (i : N) : OneCaAcc N M :=
  let bNew := oneCaPickBundle σ past st acc i
  let sNext := Function.update acc.bundles i bNew
  if bNew.card ≤ Nat.sqrt (Fintype.card M) then
    let wNext := if bNew ⊆ freeItems acc.wSet sNext then insert i acc.wSet else acc.wSet
    let mNext := if bNew ⊆ freeItems acc.mSet sNext then insert i acc.mSet else acc.mSet
    let gNext := if bNew ⊆ freeItems acc.gSet sNext then insert i acc.gSet else acc.gSet
    ⟨wNext, mNext, gNext, sNext⟩
  else
    ⟨acc.wSet, acc.mSet, acc.gSet, sNext⟩

omit [Fintype N] in
private theorem oneCaStep_wSet_eq (σ : N → OneCaStrategy N M) (past : List (WrapperState N M))
    (st : WrapperState N M) (acc : OneCaAcc N M) (i : N) :
    (oneCaStep σ past st acc i).wSet =
      if (oneCaPickBundle σ past st acc i).card ≤ Nat.sqrt (Fintype.card M) then
        if oneCaPickBundle σ past st acc i ⊆
            freeItems acc.wSet (Function.update acc.bundles i (oneCaPickBundle σ past st acc i))
        then insert i acc.wSet else acc.wSet
      else acc.wSet := by
  dsimp only [oneCaStep]
  split_ifs <;> rfl

omit [Fintype N] in
private theorem oneCaStep_mSet_eq (σ : N → OneCaStrategy N M) (past : List (WrapperState N M))
    (st : WrapperState N M) (acc : OneCaAcc N M) (i : N) :
    (oneCaStep σ past st acc i).mSet =
      if (oneCaPickBundle σ past st acc i).card ≤ Nat.sqrt (Fintype.card M) then
        if oneCaPickBundle σ past st acc i ⊆
            freeItems acc.mSet (Function.update acc.bundles i (oneCaPickBundle σ past st acc i))
        then insert i acc.mSet else acc.mSet
      else acc.mSet := by
  dsimp only [oneCaStep]
  split_ifs <;> rfl

omit [Fintype N] in
private theorem oneCaStep_gSet_eq (σ : N → OneCaStrategy N M) (past : List (WrapperState N M))
    (st : WrapperState N M) (acc : OneCaAcc N M) (i : N) :
    (oneCaStep σ past st acc i).gSet =
      if (oneCaPickBundle σ past st acc i).card ≤ Nat.sqrt (Fintype.card M) then
        if oneCaPickBundle σ past st acc i ⊆
            freeItems acc.gSet (Function.update acc.bundles i (oneCaPickBundle σ past st acc i))
        then insert i acc.gSet else acc.gSet
      else acc.gSet := by
  dsimp only [oneCaStep]
  split_ifs <;> rfl

omit [Fintype N] in
private theorem oneCaStep_bundles_eq (σ : N → OneCaStrategy N M) (past : List (WrapperState N M))
    (st : WrapperState N M) (acc : OneCaAcc N M) (i : N) :
    (oneCaStep σ past st acc i).bundles =
      Function.update acc.bundles i (oneCaPickBundle σ past st acc i) := by
  dsimp only [oneCaStep]
  split_ifs <;> rfl

/-- Choose the highest-value allocation among `W_j`, `M_j`, `GREEDY_j`. -/
private def oneCaSelectBest (v : N → ℕ) (acc : OneCaAcc N M) : Finset N :=
  let sumW := ∑ k ∈ acc.wSet, v k
  let sumM := ∑ k ∈ acc.mSet, v k
  let sumG := ∑ k ∈ acc.gSet, v k
  if sumM ≤ sumW ∧ sumG ≤ sumW then acc.wSet
  else if sumG ≤ sumM then acc.mSet
  else acc.gSet

/-- Full execution of one call to `1-CA-PROC`, returning the final accumulator. -/
private def oneCaRunAcc (σ : N → OneCaStrategy N M) (past : List (WrapperState N M))
    (st : WrapperState N M) : OneCaAcc N M :=
  let active := Finset.univ.filter fun i => 0 < st.val i
  let order := active.sort (oneCaRel st.val)
  match order with
  | [] => ⟨st.winners, ∅, ∅, st.bundle⟩
  | iMax :: _ => order.foldl (oneCaStep σ past st) ⟨st.winners, {iMax}, ∅, st.bundle⟩

/-- **The `1-CA-PROC` subprocedure** ([Lavi2007], Definition 12.46, p. 325) for single-value
combinatorial auctions. Initializes `s_i^0 = Finset.univ`. -/
@[expose] def oneCaProc : WrapperProc N M (OneCaStrategy N M) where
  initBundle := fun _ => Finset.univ
  proc σ past st :=
    let rel : N → N → Prop := fun i k => st.val k < st.val i ∨ (st.val k = st.val i ∧ i ≤ k)
    letI : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
    letI : Std.Total rel := ⟨fun a b => by
      rcases lt_trichotomy (st.val a) (st.val b) with h | h | h
      · exact Or.inr (Or.inl h)
      · rcases le_total a b with hab | hba
        · exact Or.inl (Or.inr ⟨h.symm, hab⟩)
        · exact Or.inr (Or.inr ⟨h, hba⟩)
      · exact Or.inl (Or.inl h)⟩
    letI : IsTrans N rel := ⟨fun a b c hab hbc => by
      rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hbc with h2 | ⟨h2, h2'⟩
      · exact Or.inl (h2.trans h1)
      · exact Or.inl (h2 ▸ h1)
      · exact Or.inl (h1 ▸ h2)
      · exact Or.inr ⟨h2.trans h1, h1'.trans h2'⟩⟩
    letI : Std.Antisymm rel := ⟨fun a b hab hba => by
      rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hba with h2 | ⟨h2, h2'⟩
      · exact absurd (h1.trans h2) (lt_irrefl _)
      · exact absurd (h2 ▸ h1) (lt_irrefl _)
      · exact absurd (h1 ▸ h2) (lt_irrefl _)
      · exact le_antisymm h1' h2'⟩
    let active := Finset.univ.filter fun i => 0 < st.val i
    let order := active.sort rel
    match order with
    | [] => (st.winners, st.bundle)
    | iMax :: _ =>
      let (wSet, mSet, gSet, bundles) :=
        order.foldl (fun (wSet, mSet, gSet, bundles) i =>
          let bNew :=
            if i ∈ st.winners then bundles i
            else
              let view : OneCaShrinkView N M := ⟨past, st, wSet, mSet, gSet, bundles⟩
              match (σ i).shrink view with
              | some b => if IsValidShrink gSet bundles (bundles i) b then b else bundles i
              | none => bundles i
          let sNext := Function.update bundles i bNew
          if bNew.card ≤ Nat.sqrt (Fintype.card M) then
            let wNext := if bNew ⊆ freeItems wSet sNext then insert i wSet else wSet
            let mNext := if bNew ⊆ freeItems mSet sNext then insert i mSet else mSet
            let gNext := if bNew ⊆ freeItems gSet sNext then insert i gSet else gSet
            (wNext, mNext, gNext, sNext)
          else
            (wSet, mSet, gSet, sNext))
          (st.winners, {iMax}, ∅, st.bundle)
      let sumW := ∑ k ∈ wSet, st.val k
      let sumM := ∑ k ∈ mSet, st.val k
      let sumG := ∑ k ∈ gSet, st.val k
      let W := if sumM ≤ sumW ∧ sumG ≤ sumW then wSet
        else if sumG ≤ sumM then mSet else gSet
      (W, bundles)
  chooseDouble s past st W' s' := s.double past st W' s'

private theorem oneCaProc_proc_eq (σ : N → OneCaStrategy N M) (past : List (WrapperState N M))
    (st : WrapperState N M) :
    (oneCaProc (N := N) (M := M)).proc σ past st =
      (oneCaSelectBest st.val (oneCaRunAcc σ past st), (oneCaRunAcc σ past st).bundles) := by
  dsimp only [oneCaProc, oneCaRunAcc, oneCaSelectBest]
  set active := Finset.univ.filter fun i => 0 < st.val i
  let rel : N → N → Prop := fun i k => st.val k < st.val i ∨ (st.val k = st.val i ∧ i ≤ k)
  let _ : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
  let _ : Std.Total rel := ⟨fun a b => by
    rcases lt_trichotomy (st.val a) (st.val b) with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases le_total a b with hab | hba
      · exact Or.inl (Or.inr ⟨h.symm, hab⟩)
      · exact Or.inr (Or.inr ⟨h, hba⟩)
    · exact Or.inl (Or.inl h)⟩
  let _ : IsTrans N rel := ⟨fun a b c hab hbc => by
    rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hbc with h2 | ⟨h2, h2'⟩
    · exact Or.inl (h2.trans h1)
    · exact Or.inl (h2 ▸ h1)
    · exact Or.inl (h1 ▸ h2)
    · exact Or.inr ⟨h2.trans h1, h1'.trans h2'⟩⟩
  let _ : Std.Antisymm rel := ⟨fun a b hab hba => by
    rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hba with h2 | ⟨h2, h2'⟩
    · exact absurd (h1.trans h2) (lt_irrefl _)
    · exact absurd (h2 ▸ h1) (lt_irrefl _)
    · exact absurd (h1 ▸ h2) (lt_irrefl _)
    · exact le_antisymm h1' h2'⟩
  have hperm : (active.sort rel).Perm (active.sort (oneCaRel st.val)) :=
    (List.perm_ext_iff_of_nodup (active.sort_nodup rel)
      (active.sort_nodup (oneCaRel st.val))).2 fun _ => by simp only [Finset.mem_sort]
  have hsort : active.sort rel = active.sort (oneCaRel st.val) :=
    hperm.eq_of_pairwise
      (fun _ _ _ _ h1 h2 => Std.Antisymm.antisymm (r := oneCaRel st.val) _ _ h1 h2)
      (active.pairwise_sort rel) (active.pairwise_sort (oneCaRel st.val))
  rw [hsort]
  cases hord : active.sort (oneCaRel st.val) with
  | nil =>
    simp only [Finset.sum_empty, Nat.zero_le, and_self, ↓reduceIte]
  | cons iMax tl =>
    let toTuple : OneCaAcc N M → Finset N × Finset N × Finset N × (N → Finset M) :=
      fun a => (a.wSet, a.mSet, a.gSet, a.bundles)
    have hfold : ∀ (xs : List N) (acc : OneCaAcc N M),
        xs.foldl (fun (wSet, mSet, gSet, bundles) i =>
          let bNew :=
            if i ∈ st.winners then bundles i
            else
              let view : OneCaShrinkView N M := ⟨past, st, wSet, mSet, gSet, bundles⟩
              match (σ i).shrink view with
              | some b => if IsValidShrink gSet bundles (bundles i) b then b else bundles i
              | none => bundles i
          let sNext := Function.update bundles i bNew
          if bNew.card ≤ Nat.sqrt (Fintype.card M) then
            let wNext := if bNew ⊆ freeItems wSet sNext then insert i wSet else wSet
            let mNext := if bNew ⊆ freeItems mSet sNext then insert i mSet else mSet
            let gNext := if bNew ⊆ freeItems gSet sNext then insert i gSet else gSet
            (wNext, mNext, gNext, sNext)
          else
            (wSet, mSet, gSet, sNext)) (toTuple acc) =
        toTuple (xs.foldl (oneCaStep σ past st) acc) := by
      intro xs
      induction xs with
      | nil => intro _; rfl
      | cons a l ih =>
        intro acc
        rw [List.foldl_cons, List.foldl_cons]
        have hstep : (let bNew :=
              if a ∈ st.winners then acc.bundles a
              else
                let view : OneCaShrinkView N M :=
                  ⟨past, st, acc.wSet, acc.mSet, acc.gSet, acc.bundles⟩
                match (σ a).shrink view with
                | some b =>
                  if IsValidShrink acc.gSet acc.bundles (acc.bundles a) b then b else acc.bundles a
                | none => acc.bundles a
            let sNext := Function.update acc.bundles a bNew
            if bNew.card ≤ Nat.sqrt (Fintype.card M) then
              let wNext := if bNew ⊆ freeItems acc.wSet sNext then insert a acc.wSet else acc.wSet
              let mNext := if bNew ⊆ freeItems acc.mSet sNext then insert a acc.mSet else acc.mSet
              let gNext := if bNew ⊆ freeItems acc.gSet sNext then insert a acc.gSet else acc.gSet
              (wNext, mNext, gNext, sNext)
            else
              (acc.wSet, acc.mSet, acc.gSet, sNext)) =
            toTuple (oneCaStep σ past st acc a) := by
          dsimp only [toTuple, oneCaStep, oneCaPickBundle]
          split_ifs <;> rfl
        dsimp only [toTuple] at hstep ⊢
        rw [hstep]
        exact ih (oneCaStep σ past st acc a)
    exact congrArg (fun t =>
      let sumW := ∑ k ∈ t.1, st.val k
      let sumM := ∑ k ∈ t.2.1, st.val k
      let sumG := ∑ k ∈ t.2.2.1, st.val k
      let W := if sumM ≤ sumW ∧ sumG ≤ sumW then t.1
        else if sumG ≤ sumM then t.2.1 else t.2.2.1
      (W, t.2.2.2)) (hfold (iMax :: tl) ⟨st.winners, {iMax}, ∅, st.bundle⟩)

/-- **Loser-if-silent** condition for player `i` at a `1-CA-PROC` shrink query ([Lavi2007], §12.5,
p. 325): `v̄ᵢ / 2 ≤ v_i^j`, `i` is not currently in `W_j`, `M_j`, or `GREEDY_j`, and staying silent
cannot place `i` into any of `W_j`, `M_j`, or `GREEDY_j`. -/
@[expose] def IsLoserIfSilent (p : SingleValuePlayer M) (i : N)
    (view : OneCaShrinkView N M) : Prop :=
  p.value / 2 ≤ (view.state.val i : ℝ) ∧
  i ∉ view.currentWinners ∧
  i ∉ view.currentMax ∧
  i ∉ view.currentGreedy ∧
  ¬ ((view.state.bundle i).card ≤ Nat.sqrt (Fintype.card M) ∧
      (view.state.bundle i ⊆ freeItems view.currentWinners view.currentBundles ∨
       view.state.bundle i ⊆ freeItems view.currentMax view.currentBundles ∨
       view.state.bundle i ⊆ freeItems view.currentGreedy view.currentBundles))

/-- **The undominated strategy class `D_i`** for player `i` with valuation `p` in
`Wrapper + 1-CA-PROC` ([Lavi2007], §12.5, p. 325):
1. Never shrinks to a non-desired bundle.
2. Whenever `IsLoserIfSilent` and a valid desired bundle exists, declares a valid desired bundle.
3. Never doubles above `p.value` and never retires strictly below `p.value / 2`. -/
@[expose] def oneCaStrategyClass (p : SingleValuePlayer M) (i : N) : Set (OneCaStrategy N M) :=
  {s |
    (∀ view b, s.shrink view = some b →
      IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle i) b →
      b ∈ p.desired) ∧
    (∀ view, IsLoserIfSilent p i view →
      (∃ b, IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle i) b ∧
        b ∈ p.desired) →
      ∃ b, s.shrink view = some b ∧
        IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle i) b ∧
        b ∈ p.desired) ∧
    (∀ past st W' s',
      (p.value < 2 * (st.val i : ℝ) → s.double past st W' s' = false) ∧
      (2 * (st.val i : ℝ) < p.value → s.double past st W' s' = true))}

/-- Explicit dominance transformation mapping any strategy `st` to a weakly dominating strategy in
`oneCaStrategyClass p i` ([Lavi2007], §12.5, p. 325). -/
@[expose] noncomputable def dominateOneCaStrategy (p : SingleValuePlayer M) (i : N)
    (st : OneCaStrategy N M) : OneCaStrategy N M where
  shrink view := by
    classical
    let fallback : Option (Finset M) :=
      if IsLoserIfSilent p i view then
        if h : ∃ b, IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle i) b ∧
            b ∈ p.desired then some h.choose else none
      else none
    exact match st.shrink view with
    | some b =>
      if IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle i) b ∧
          b ∈ p.desired then some b
      else fallback
    | none => fallback
  double past st' W' s' := by
    classical
    exact if p.value < 2 * (st'.val i : ℝ) then false
    else if 2 * (st'.val i : ℝ) < p.value then true
    else st.double past st' W' s'

omit [Fintype N] [LinearOrder N] in
theorem dominateOneCaStrategy_mem (p : SingleValuePlayer M) (i : N) (st : OneCaStrategy N M) :
    dominateOneCaStrategy p i st ∈ oneCaStrategyClass p i := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro view b hsb _
    simp only [dominateOneCaStrategy] at hsb
    cases hst : st.shrink view with
    | none =>
      simp only [hst] at hsb
      split_ifs at hsb with h1 h2
      · injection hsb with hb
        exact hb ▸ h2.choose_spec.2
    | some b₀ =>
      simp only [hst] at hsb
      split_ifs at hsb with h0 h1 h2
      · injection hsb with hb
        exact hb ▸ h0.2
      · injection hsb with hb
        exact hb ▸ h2.choose_spec.2
  · intro view hlis hex
    simp only [dominateOneCaStrategy]
    cases hst : st.shrink view with
    | none =>
      simp only [hlis, hex, ↓reduceDIte, ↓reduceIte]
      exact ⟨hex.choose, rfl, hex.choose_spec⟩
    | some b₀ =>
      by_cases h0 : IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle i) b₀ ∧
          b₀ ∈ p.desired
      · simp only [h0]
        exact ⟨b₀, rfl, h0⟩
      · simp only [h0, ↓reduceIte, hlis, hex, ↓reduceDIte]
        exact ⟨hex.choose, rfl, hex.choose_spec⟩
  · intro past st' W' s'
    simp only [dominateOneCaStrategy]
    constructor
    · intro hgt; simp only [hgt, ↓reduceIte]
    · intro hlt
      have hnot : ¬ (p.value < 2 * (st'.val i : ℝ)) := not_lt.2 hlt.le
      simp only [hnot, hlt, ↓reduceIte]

/-! #### Loop invariants for `1-CA-PROC` -/

private structure OneCaFoldInv (st : WrapperState N M) (active : Finset N) (iMax : N)
    (visited : List N) (acc : OneCaAcc N M) : Prop where
  w_sub_active : acc.wSet ⊆ active
  m_sub_active : acc.mSet ⊆ active
  g_sub_active : acc.gSet ⊆ active
  stW_sub_w : st.winners ⊆ acc.wSet
  iMax_mem_m : iMax ∈ acc.mSet
  w_diff_visited : ∀ k ∈ acc.wSet, k ∈ st.winners ∨ k ∈ visited
  m_diff_visited : ∀ k ∈ acc.mSet, k = iMax ∨ k ∈ visited
  g_sub_visited : ∀ k ∈ acc.gSet, k ∈ visited
  bundle_sub : ∀ k, acc.bundles k ⊆ st.bundle k
  bundle_unvisited : ∀ k, k ∉ visited → acc.bundles k = st.bundle k
  bundle_winners : ∀ k ∈ st.winners, acc.bundles k = st.bundle k
  bundle_nonempty : ∀ k, (acc.bundles k).Nonempty
  bundle_dichotomy : ∀ k,
    acc.bundles k = Finset.univ ∨ (acc.bundles k).card ≤ Nat.sqrt (Fintype.card M)
  w_pw : (acc.wSet : Set N).PairwiseDisjoint acc.bundles
  m_pw : (acc.mSet : Set N).PairwiseDisjoint acc.bundles
  g_pw : (acc.gSet : Set N).PairwiseDisjoint acc.bundles
  g_small : ∀ k ∈ acc.gSet, (acc.bundles k).card ≤ Nat.sqrt (Fintype.card M)
  g_first_shrink : ∀ k ∈ visited, (st.bundle k).card = Fintype.card M →
    (acc.bundles k).card < Fintype.card M → k ∈ acc.gSet
  w_pareto : ∀ k ∈ visited, k ∉ acc.wSet → (acc.bundles k).card ≤ Nat.sqrt (Fintype.card M) →
    ∃ l ∈ acc.wSet, ¬ Disjoint (acc.bundles k) (acc.bundles l)
  m_pareto : ∀ k ∈ visited, k ∉ acc.mSet → (acc.bundles k).card ≤ Nat.sqrt (Fintype.card M) →
    ∃ l ∈ acc.mSet, ¬ Disjoint (acc.bundles k) (acc.bundles l)
  g_pareto : ∀ k ∈ visited, k ∉ acc.gSet → (acc.bundles k).card ≤ Nat.sqrt (Fintype.card M) →
    ∃ l ∈ acc.gSet, ¬ Disjoint (acc.bundles k) (acc.bundles l)

omit [Fintype N] in
private theorem oneCaStep_preserves_inv (σ : N → OneCaStrategy N M)
    (past : List (WrapperState N M)) (st : WrapperState N M) (active : Finset N) (iMax : N)
    (visited : List N) (acc : OneCaAcc N M) (i : N)
    (hinv : OneCaFoldInv st active iMax visited acc)
    (hi_act : i ∈ active) (hi_fresh : i ∉ visited)
    (hiMax_first : i = iMax → visited = []) :
    OneCaFoldInv st active iMax (i :: visited) (oneCaStep σ past st acc i) ∧
    acc.wSet ⊆ (oneCaStep σ past st acc i).wSet ∧
    acc.mSet ⊆ (oneCaStep σ past st acc i).mSet ∧
    acc.gSet ⊆ (oneCaStep σ past st acc i).gSet ∧
    (∀ k, k ≠ i → (oneCaStep σ past st acc i).bundles k = acc.bundles k) := by
  set bNew := oneCaPickBundle σ past st acc i
  set sNext := Function.update acc.bundles i bNew
  have hbi_eq : acc.bundles i = st.bundle i := hinv.bundle_unvisited i hi_fresh
  have hb_props :
      bNew ⊆ acc.bundles i ∧ bNew.Nonempty ∧
      (bNew = Finset.univ ∨ bNew.card ≤ Nat.sqrt (Fintype.card M)) ∧
      (bNew ≠ acc.bundles i → i ∉ st.winners ∧
        IsValidShrink acc.gSet acc.bundles (acc.bundles i) bNew) := by
    simp only [bNew, oneCaPickBundle]
    by_cases hW : i ∈ st.winners
    · simp only [hW, ↓reduceIte]
      exact ⟨Subset.rfl, hinv.bundle_nonempty i, hinv.bundle_dichotomy i, fun h => absurd rfl h⟩
    · simp only [hW, ↓reduceIte]
      cases hsh : (σ i).shrink ⟨past, st, acc.wSet, acc.mSet, acc.gSet, acc.bundles⟩ with
      | none =>
        exact ⟨Subset.rfl, hinv.bundle_nonempty i, hinv.bundle_dichotomy i, fun h => absurd rfl h⟩
      | some b =>
        by_cases hval : IsValidShrink acc.gSet acc.bundles (acc.bundles i) b
        · simp only [hval, ↓reduceIte]
          exact ⟨hval.2.1.trans Finset.inter_subset_right, hval.1, Or.inr hval.2.2,
            fun _ => ⟨not_false, trivial⟩⟩
        · simp only [hval, ↓reduceIte]
          exact ⟨Subset.rfl, hinv.bundle_nonempty i, hinv.bundle_dichotomy i, fun h => absurd rfl h⟩
  obtain ⟨hb_sub, hb_ne, hb_dich, hb_shrink⟩ := hb_props
  have hsNext_ne : ∀ k, k ≠ i → sNext k = acc.bundles k := fun k hk =>
    Function.update_of_ne hk bNew acc.bundles
  have hsNext_self : sNext i = bNew := Function.update_self i bNew acc.bundles
  have hsNext_w : ∀ k ∈ acc.wSet, sNext k = acc.bundles k := by
    intro k hk
    by_cases hki : k = i
    · subst hki
      have hiW : k ∈ st.winners := (hinv.w_diff_visited k hk).resolve_right hi_fresh
      rw [hsNext_self]
      simp only [bNew, oneCaPickBundle, hiW, ↓reduceIte]
    · exact hsNext_ne k hki
  have hsNext_g : ∀ k ∈ acc.gSet, sNext k = acc.bundles k := fun k hk =>
    hsNext_ne k fun h => hi_fresh (h ▸ hinv.g_sub_visited k hk)
  have hw_pw0 : (acc.wSet : Set N).PairwiseDisjoint sNext := fun a ha b hb hne => by
    change Disjoint (sNext a) (sNext b)
    rw [hsNext_w a ha, hsNext_w b hb]; exact hinv.w_pw ha hb hne
  have hg_pw0 : (acc.gSet : Set N).PairwiseDisjoint sNext := fun a ha b hb hne => by
    change Disjoint (sNext a) (sNext b)
    rw [hsNext_g a ha, hsNext_g b hb]; exact hinv.g_pw ha hb hne
  have hm_pw0 : (acc.mSet : Set N).PairwiseDisjoint sNext := by
    intro a ha b hb hne
    have hsub_a : sNext a ⊆ acc.bundles a := by
      by_cases hai : a = i
      · subst hai; rw [hsNext_self]; exact hb_sub
      · rw [hsNext_ne a hai]
    have hsub_b : sNext b ⊆ acc.bundles b := by
      by_cases hbi : b = i
      · subst hbi; rw [hsNext_self]; exact hb_sub
      · rw [hsNext_ne b hbi]
    exact (hinv.m_pw ha hb hne).mono hsub_a hsub_b
  have hW_eq : (oneCaStep σ past st acc i).wSet =
      if bNew.card ≤ Nat.sqrt (Fintype.card M) then
        if bNew ⊆ freeItems acc.wSet sNext then insert i acc.wSet else acc.wSet
      else acc.wSet := oneCaStep_wSet_eq σ past st acc i
  have hM_eq : (oneCaStep σ past st acc i).mSet =
      if bNew.card ≤ Nat.sqrt (Fintype.card M) then
        if bNew ⊆ freeItems acc.mSet sNext then insert i acc.mSet else acc.mSet
      else acc.mSet := oneCaStep_mSet_eq σ past st acc i
  have hG_eq : (oneCaStep σ past st acc i).gSet =
      if bNew.card ≤ Nat.sqrt (Fintype.card M) then
        if bNew ⊆ freeItems acc.gSet sNext then insert i acc.gSet else acc.gSet
      else acc.gSet := oneCaStep_gSet_eq σ past st acc i
  have hbundles_eq : (oneCaStep σ past st acc i).bundles = sNext :=
    oneCaStep_bundles_eq σ past st acc i
  have hsubW : acc.wSet ⊆ (oneCaStep σ past st acc i).wSet := by
    rw [hW_eq]; split_ifs <;> [exact Finset.subset_insert _ _; exact Subset.rfl; exact Subset.rfl]
  have hsubM : acc.mSet ⊆ (oneCaStep σ past st acc i).mSet := by
    rw [hM_eq]; split_ifs <;> [exact Finset.subset_insert _ _; exact Subset.rfl; exact Subset.rfl]
  have hsubG : acc.gSet ⊆ (oneCaStep σ past st acc i).gSet := by
    rw [hG_eq]; split_ifs <;> [exact Finset.subset_insert _ _; exact Subset.rfl; exact Subset.rfl]
  have hpw_insert : ∀ (S : Finset N), (S : Set N).PairwiseDisjoint sNext →
      ((if bNew ⊆ freeItems S sNext then insert i S else S : Finset N) : Set N).PairwiseDisjoint
        sNext := by
    intro S hS
    split_ifs with hfree
    · rw [Finset.coe_insert]
      exact hS.insert fun k hk _ => by
        rw [hsNext_self]
        exact (subset_freeItems_iff S sNext bNew).1 hfree k hk
    · exact hS
  have hpareto_step : ∀ (S : Finset N),
      (∀ k ∈ visited, k ∉ S → (acc.bundles k).card ≤ Nat.sqrt (Fintype.card M) →
        ∃ l ∈ S, ¬ Disjoint (acc.bundles k) (acc.bundles l)) →
      ∀ (S' : Finset N),
        S' = (if bNew.card ≤ Nat.sqrt (Fintype.card M) then
                if bNew ⊆ freeItems S sNext then insert i S else S
              else S) →
        (∀ l ∈ S, sNext l = acc.bundles l) →
        ∀ k ∈ i :: visited, k ∉ S' → (sNext k).card ≤ Nat.sqrt (Fintype.card M) →
          ∃ l ∈ S', ¬ Disjoint (sNext k) (sNext l) := by
    intro S hpar S' hS' hseq k hk hkNotS' hkCard
    have hSS' : S ⊆ S' := by
      rw [hS']; split_ifs <;> [exact Finset.subset_insert _ _; exact Subset.rfl; exact Subset.rfl]
    rcases List.mem_cons.1 hk with rfl | hkvis
    · rw [hsNext_self] at hkCard ⊢
      have hnotFree : ¬ bNew ⊆ freeItems S sNext := by
        intro hf
        apply hkNotS'
        rw [hS']
        simp only [hkCard, hf, ↓reduceIte, Finset.mem_insert_self]
      rw [subset_freeItems_iff] at hnotFree
      push Not at hnotFree
      obtain ⟨l, hl, hnd⟩ := hnotFree
      exact ⟨l, hSS' hl, hnd⟩
    · have hkne : k ≠ i := fun h => hi_fresh (h ▸ hkvis)
      rw [hsNext_ne k hkne] at hkCard ⊢
      obtain ⟨l, hl, hnd⟩ := hpar k hkvis (fun h => hkNotS' (hSS' h)) hkCard
      exact ⟨l, hSS' hl, by rw [hseq l hl]; exact hnd⟩
  have hseq_m : i ∉ acc.mSet → ∀ l ∈ acc.mSet, sNext l = acc.bundles l := fun hni l hl =>
    hsNext_ne l fun h => hni (h ▸ hl)
  refine ⟨⟨?_, ?_, ?_, hinv.stW_sub_w.trans hsubW, hsubM hinv.iMax_mem_m, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hsubW, hsubM, hsubG, fun k hk => by
    rw [hbundles_eq]; exact hsNext_ne k hk⟩
  · rw [hW_eq]
    split_ifs <;> [exact Finset.insert_subset_iff.2 ⟨hi_act, hinv.w_sub_active⟩;
      exact hinv.w_sub_active; exact hinv.w_sub_active]
  · rw [hM_eq]
    split_ifs <;> [exact Finset.insert_subset_iff.2 ⟨hi_act, hinv.m_sub_active⟩;
      exact hinv.m_sub_active; exact hinv.m_sub_active]
  · rw [hG_eq]
    split_ifs <;> [exact Finset.insert_subset_iff.2 ⟨hi_act, hinv.g_sub_active⟩;
      exact hinv.g_sub_active; exact hinv.g_sub_active]
  · intro k hk
    rw [hW_eq] at hk
    split_ifs at hk
    · rcases Finset.mem_insert.1 hk with rfl | hk'
      · exact Or.inr List.mem_cons_self
      · exact (hinv.w_diff_visited k hk').imp_right (List.mem_cons_of_mem i)
    · exact (hinv.w_diff_visited k hk).imp_right (List.mem_cons_of_mem i)
    · exact (hinv.w_diff_visited k hk).imp_right (List.mem_cons_of_mem i)
  · intro k hk
    rw [hM_eq] at hk
    split_ifs at hk
    · rcases Finset.mem_insert.1 hk with rfl | hk'
      · exact Or.inr List.mem_cons_self
      · exact (hinv.m_diff_visited k hk').imp_right (List.mem_cons_of_mem i)
    · exact (hinv.m_diff_visited k hk).imp_right (List.mem_cons_of_mem i)
    · exact (hinv.m_diff_visited k hk).imp_right (List.mem_cons_of_mem i)
  · intro k hk
    rw [hG_eq] at hk
    split_ifs at hk
    · rcases Finset.mem_insert.1 hk with rfl | hk'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem i (hinv.g_sub_visited k hk')
    · exact List.mem_cons_of_mem i (hinv.g_sub_visited k hk)
    · exact List.mem_cons_of_mem i (hinv.g_sub_visited k hk)
  · intro k; rw [hbundles_eq]
    by_cases hki : k = i
    · subst hki; rw [hsNext_self]; exact hb_sub.trans (hinv.bundle_sub k)
    · rw [hsNext_ne k hki]; exact hinv.bundle_sub k
  · intro k hk; rw [hbundles_eq]
    rw [List.mem_cons, not_or] at hk
    rw [hsNext_ne k hk.1]; exact hinv.bundle_unvisited k hk.2
  · intro k hk; rw [hbundles_eq]
    rw [hsNext_w k (hinv.stW_sub_w hk)]; exact hinv.bundle_winners k hk
  · intro k; rw [hbundles_eq]
    by_cases hki : k = i
    · subst hki; rw [hsNext_self]; exact hb_ne
    · rw [hsNext_ne k hki]; exact hinv.bundle_nonempty k
  · intro k; rw [hbundles_eq]
    by_cases hki : k = i
    · subst hki; rw [hsNext_self]; exact hb_dich
    · rw [hsNext_ne k hki]; exact hinv.bundle_dichotomy k
  · rw [hbundles_eq, hW_eq]
    by_cases hc : bNew.card ≤ Nat.sqrt (Fintype.card M) <;> simp only [hc, ↓reduceIte]
    · exact hpw_insert acc.wSet hw_pw0
    · exact hw_pw0
  · rw [hbundles_eq, hM_eq]
    by_cases hc : bNew.card ≤ Nat.sqrt (Fintype.card M) <;> simp only [hc, ↓reduceIte]
    · exact hpw_insert acc.mSet hm_pw0
    · exact hm_pw0
  · rw [hbundles_eq, hG_eq]
    by_cases hc : bNew.card ≤ Nat.sqrt (Fintype.card M) <;> simp only [hc, ↓reduceIte]
    · exact hpw_insert acc.gSet hg_pw0
    · exact hg_pw0
  · intro k hk; rw [hbundles_eq]
    rw [hG_eq] at hk
    split_ifs at hk with hc hf
    · rcases Finset.mem_insert.1 hk with rfl | hk'
      · rwa [hsNext_self]
      · rw [hsNext_g k hk']; exact hinv.g_small k hk'
    · rw [hsNext_g k hk]; exact hinv.g_small k hk
    · rw [hsNext_g k hk]; exact hinv.g_small k hk
  · intro k hk hcardM hltM
    rw [hbundles_eq] at hltM
    rcases List.mem_cons.1 hk with rfl | hkvis
    · rw [hsNext_self] at hltM
      have hne_b : bNew ≠ acc.bundles k := fun heq => by
        rw [heq, hbi_eq] at hltM; omega
      obtain ⟨_, hval⟩ := hb_shrink hne_b
      have hfree_next : bNew ⊆ freeItems acc.gSet sNext := by
        rw [subset_freeItems_iff]
        intro l hl
        rw [hsNext_g l hl]
        exact (subset_freeItems_iff acc.gSet acc.bundles bNew).1
          (hval.2.1.trans Finset.inter_subset_left) l hl
      rw [hG_eq]
      simp only [hval.2.2, hfree_next, ↓reduceIte, Finset.mem_insert_self]
    · have hkne : k ≠ i := fun h => hi_fresh (h ▸ hkvis)
      rw [hsNext_ne k hkne] at hltM
      exact hsubG (hinv.g_first_shrink k hkvis hcardM hltM)
  · rw [hbundles_eq]
    exact hpareto_step acc.wSet hinv.w_pareto _ hW_eq hsNext_w
  · intro k hk hkNotM hkCard
    rw [hbundles_eq] at hkCard ⊢
    by_cases hiM : i ∈ acc.mSet
    · have hkne : k ≠ i := fun h => hkNotM (hsubM (h ▸ hiM))
      have hkvis : k ∈ visited := (List.mem_cons.1 hk).resolve_left hkne
      have hiEqMax : i = iMax := (hinv.m_diff_visited i hiM).resolve_right hi_fresh
      rw [hiMax_first hiEqMax] at hkvis
      exact absurd hkvis List.not_mem_nil
    · exact hpareto_step acc.mSet hinv.m_pareto _ hM_eq (hseq_m hiM) k hk hkNotM hkCard
  · rw [hbundles_eq]
    exact hpareto_step acc.gSet hinv.g_pareto _ hG_eq hsNext_g

omit [Fintype N] in
private theorem oneCaFold_preserves_inv (σ : N → OneCaStrategy N M)
    (past : List (WrapperState N M)) (st : WrapperState N M) (active : Finset N) (iMax : N)
    (rem visited : List N) (acc : OneCaAcc N M)
    (hinv : OneCaFoldInv st active iMax visited acc)
    (hnodup : rem.Nodup) (hact : ∀ x ∈ rem, x ∈ active)
    (hdisj : ∀ x ∈ rem, x ∉ visited)
    (hiMax_first : ∀ x ∈ rem, x = iMax → visited = [] ∧ rem.head? = some iMax) :
    let accEnd := rem.foldl (oneCaStep σ past st) acc
    OneCaFoldInv st active iMax (rem.reverse ++ visited) accEnd ∧
    acc.wSet ⊆ accEnd.wSet ∧ acc.mSet ⊆ accEnd.mSet ∧ acc.gSet ⊆ accEnd.gSet ∧
    (∀ k, k ∉ rem → accEnd.bundles k = acc.bundles k) ∧
    (∀ k, k ∉ rem → k ∉ acc.wSet → k ∉ accEnd.wSet) ∧
    (∀ k, k ∉ rem → k ∉ acc.mSet → k ∉ accEnd.mSet) ∧
    (∀ k, k ∉ rem → k ∉ acc.gSet → k ∉ accEnd.gSet) := by
  induction rem generalizing visited acc with
  | nil =>
    exact ⟨by simpa only [List.reverse_nil, List.nil_append, List.foldl_nil] using hinv,
      Subset.rfl, Subset.rfl, Subset.rfl, fun _ _ => rfl, fun _ _ h => h, fun _ _ h => h,
      fun _ _ h => h⟩
  | cons a tl ih =>
    rw [List.nodup_cons] at hnodup
    obtain ⟨ha_not_tl, htl_nodup⟩ := hnodup
    have ha_first : a = iMax → visited = [] := fun h =>
      (hiMax_first a List.mem_cons_self h).1
    obtain ⟨hinv1, hsubW1, hsubM1, hsubG1, hbun1⟩ := oneCaStep_preserves_inv σ past st active iMax
      visited acc a hinv (hact a List.mem_cons_self) (hdisj a List.mem_cons_self) ha_first
    have htl_first : ∀ x ∈ tl, x = iMax → a :: visited = [] ∧ tl.head? = some iMax := by
      intro x hx hxi
      have hhead := (hiMax_first x (List.mem_cons_of_mem a hx) hxi).2
      simp only [List.head?_cons, Option.some.injEq] at hhead
      exact absurd (hhead.symm ▸ hxi ▸ hx) ha_not_tl
    obtain ⟨hinv2, hsubW2, hsubM2, hsubG2, hbun2, hnotW2, hnotM2, hnotG2⟩ :=
      ih (a :: visited) (oneCaStep σ past st acc a) hinv1 htl_nodup
        (fun x hx => hact x (List.mem_cons_of_mem a hx))
        (fun x hx hxmem => by
          rcases List.mem_cons.1 hxmem with rfl | hxvis
          · exact ha_not_tl hx
          · exact hdisj x (List.mem_cons_of_mem a hx) hxvis)
        htl_first
    have hrev : (a :: tl).reverse ++ visited = tl.reverse ++ (a :: visited) := by
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    have hnot_step : ∀ (S : Finset N) (k : N), k ≠ a → k ∉ S →
        ∀ (S' : Finset N), (∀ y ∈ S', y = a ∨ y ∈ S) → k ∉ S' := by
      intro S k hka hkS S' hS' hkS'
      rcases hS' k hkS' with rfl | hk
      · exact hka rfl
      · exact hkS hk
    refine ⟨hrev ▸ hinv2, hsubW1.trans hsubW2, hsubM1.trans hsubM2, hsubG1.trans hsubG2,
      ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [List.mem_cons, not_or] at hk
      rw [List.foldl_cons, hbun2 k hk.2, hbun1 k hk.1]
    · intro k hk hkW
      rw [List.mem_cons, not_or] at hk
      refine hnotW2 k hk.2 (hnot_step acc.wSet k hk.1 hkW _ fun y hy => ?_)
      rw [oneCaStep_wSet_eq] at hy
      split_ifs at hy
      · exact Finset.mem_insert.1 hy
      · exact Or.inr hy
      · exact Or.inr hy
    · intro k hk hkM
      rw [List.mem_cons, not_or] at hk
      refine hnotM2 k hk.2 (hnot_step acc.mSet k hk.1 hkM _ fun y hy => ?_)
      rw [oneCaStep_mSet_eq] at hy
      split_ifs at hy
      · exact Finset.mem_insert.1 hy
      · exact Or.inr hy
      · exact Or.inr hy
    · intro k hk hkG
      rw [List.mem_cons, not_or] at hk
      refine hnotG2 k hk.2 (hnot_step acc.gSet k hk.1 hkG _ fun y hy => ?_)
      rw [oneCaStep_gSet_eq] at hy
      split_ifs at hy
      · exact Finset.mem_insert.1 hy
      · exact Or.inr hy
      · exact Or.inr hy

omit [Fintype N] [LinearOrder N] [Fintype M] [DecidableEq M] in
private theorem oneCaSelectBest_props (v : N → ℕ) (acc : OneCaAcc N M) :
    (oneCaSelectBest v acc = acc.wSet ∨ oneCaSelectBest v acc = acc.mSet ∨
      oneCaSelectBest v acc = acc.gSet) ∧
    ∑ k ∈ acc.wSet, v k ≤ ∑ k ∈ oneCaSelectBest v acc, v k ∧
    ∑ k ∈ acc.mSet, v k ≤ ∑ k ∈ oneCaSelectBest v acc, v k ∧
    ∑ k ∈ acc.gSet, v k ≤ ∑ k ∈ oneCaSelectBest v acc, v k := by
  simp only [oneCaSelectBest]
  split_ifs with h1 h2
  · exact ⟨Or.inl rfl, le_rfl, h1.1, h1.2⟩
  · refine ⟨Or.inr (Or.inl rfl), ?_, le_rfl, h2⟩
    by_contra hlt
    exact h1 ⟨Nat.le_of_lt (Nat.lt_of_not_ge hlt), h2.trans (Nat.le_of_lt (Nat.lt_of_not_ge hlt))⟩
  · refine ⟨Or.inr (Or.inr rfl), ?_, Nat.le_of_lt (Nat.lt_of_not_ge h2), le_rfl⟩
    by_contra hlt
    have hgw : ∑ k ∈ acc.gSet, v k ≤ ∑ k ∈ acc.wSet, v k := Nat.le_of_lt (Nat.lt_of_not_ge hlt)
    have hmw : ∑ k ∈ acc.mSet, v k ≤ ∑ k ∈ acc.wSet, v k :=
      (Nat.le_of_lt (Nat.lt_of_not_ge h2)).trans hgw
    exact h1 ⟨hmw, hgw⟩

/-- State invariants maintained across every iteration of `Wrapper + 1-CA-PROC`. -/
private structure OneCaStateInv (st : WrapperState N M) : Prop where
  disj : Disjoint st.winners st.losers
  pw : (st.winners : Set N).PairwiseDisjoint st.bundle
  nonempty : ∀ i, (st.bundle i).Nonempty
  dichotomy : ∀ i, st.bundle i = Finset.univ ∨ (st.bundle i).card ≤ Nat.sqrt (Fintype.card M)

private theorem oneCaRunAcc_inv (σ : N → OneCaStrategy N M)
    (past : List (WrapperState N M)) (st : WrapperState N M)
    (hlos : ∀ i, i ∈ st.losers ↔ st.val i = 0)
    (hst : OneCaStateInv st)
    (hnotT : st.winners ∪ st.losers ≠ Finset.univ) :
    let active := Finset.univ.filter fun i => 0 < st.val i
    let order := active.sort (oneCaRel st.val)
    ∃ iMax : N, order.head? = some iMax ∧
      iMax ∈ active ∧
      (∀ k ∈ active, st.val k ≤ st.val iMax) ∧
      OneCaFoldInv st active iMax order.reverse (oneCaRunAcc σ past st) ∧
      (oneCaSelectBest st.val (oneCaRunAcc σ past st) : Set N).PairwiseDisjoint
        (oneCaRunAcc σ past st).bundles ∧
      Disjoint (oneCaSelectBest st.val (oneCaRunAcc σ past st)) st.losers ∧
      (∀ i, i ∉ oneCaSelectBest st.val (oneCaRunAcc σ past st) ∪ st.losers →
        ∃ l ∈ oneCaSelectBest st.val (oneCaRunAcc σ past st),
          ¬ Disjoint ((oneCaRunAcc σ past st).bundles i) ((oneCaRunAcc σ past st).bundles l)) ∧
      (∀ i, (oneCaRunAcc σ past st).bundles i ⊆ st.bundle i) ∧
      ∑ i ∈ st.winners, st.val i ≤
        ∑ i ∈ oneCaSelectBest st.val (oneCaRunAcc σ past st), st.val i := by
  set active := Finset.univ.filter fun i => 0 < st.val i
  set order := active.sort (oneCaRel st.val)
  have hact_ne : active.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hnotT
    refine Finset.eq_univ_iff_forall.2 fun i => Finset.mem_union_right _ ?_
    rw [hlos i]
    by_contra hnz
    have hi : i ∈ active := Finset.mem_filter.2 ⟨Finset.mem_univ i, Nat.pos_of_ne_zero hnz⟩
    rw [hemp] at hi
    exact Finset.notMem_empty i hi
  have hord_ne : order ≠ [] := by
    intro hnil
    obtain ⟨a, ha⟩ := hact_ne
    have ham : a ∈ order := (Finset.mem_sort (oneCaRel st.val)).2 ha
    rw [hnil] at ham
    exact List.not_mem_nil ham
  cases hord : order with
  | nil => exact absurd hord hord_ne
  | cons iMax tl =>
    have hnodup : (iMax :: tl).Nodup := hord ▸ active.sort_nodup (oneCaRel st.val)
    have hmem_iff : ∀ x, x ∈ iMax :: tl ↔ x ∈ active := fun x => by
      rw [← hord, Finset.mem_sort]
    have hiMax_act : iMax ∈ active := (hmem_iff iMax).1 List.mem_cons_self
    have hiMax_ge : ∀ k ∈ active, st.val k ≤ st.val iMax := by
      intro k hk
      have hkm : k ∈ iMax :: tl := (hmem_iff k).2 hk
      rcases List.mem_cons.1 hkm with rfl | hktl
      · exact le_rfl
      · have hpair : (iMax :: tl).Pairwise (oneCaRel st.val) := by
          rw [← hord]
          exact active.pairwise_sort (oneCaRel st.val)
        have hrel : oneCaRel st.val iMax k := (List.pairwise_cons.1 hpair).1 k hktl
        rcases hrel with hlt | ⟨heq, _⟩
        · exact hlt.le
        · exact heq.le
    have hw_sub_act : st.winners ⊆ active := by
      intro k hk
      refine Finset.mem_filter.2 ⟨Finset.mem_univ k, Nat.pos_of_ne_zero ?_⟩
      exact mt (hlos k).2 (Finset.disjoint_left.1 hst.disj hk)
    have hinit_inv : OneCaFoldInv st active iMax [] ⟨st.winners, {iMax}, ∅, st.bundle⟩ := {
      w_sub_active := hw_sub_act
      m_sub_active := Finset.singleton_subset_iff.2 hiMax_act
      g_sub_active := Finset.empty_subset _
      stW_sub_w := Subset.rfl
      iMax_mem_m := Finset.mem_singleton_self iMax
      w_diff_visited := fun _ hk => Or.inl hk
      m_diff_visited := fun _ hk => Or.inl (Finset.mem_singleton.1 hk)
      g_sub_visited := fun _ hk => absurd hk (Finset.notMem_empty _)
      bundle_sub := fun _ => Subset.rfl
      bundle_unvisited := fun _ _ => rfl
      bundle_winners := fun _ _ => rfl
      bundle_nonempty := hst.nonempty
      bundle_dichotomy := hst.dichotomy
      w_pw := hst.pw
      m_pw := by simp only [Finset.coe_singleton, Set.pairwiseDisjoint_singleton]
      g_pw := by simp only [Finset.coe_empty, Set.pairwiseDisjoint_empty]
      g_small := fun _ hk => absurd hk (Finset.notMem_empty _)
      g_first_shrink := fun _ hk => absurd hk List.not_mem_nil
      w_pareto := fun _ hk => absurd hk List.not_mem_nil
      m_pareto := fun _ hk => absurd hk List.not_mem_nil
      g_pareto := fun _ hk => absurd hk List.not_mem_nil }
    have hfirst : ∀ x ∈ iMax :: tl, x = iMax →
        ([] : List N) = [] ∧ (iMax :: tl).head? = some iMax :=
      fun _ _ _ => ⟨rfl, rfl⟩
    obtain ⟨hfold_inv, _, _, _, _, _, _, _⟩ := oneCaFold_preserves_inv σ past st active iMax
      (iMax :: tl) [] ⟨st.winners, {iMax}, ∅, st.bundle⟩ hinit_inv hnodup
      (fun x hx => (hmem_iff x).1 hx) (fun _ _ => List.not_mem_nil) hfirst
    have hrun_eq : oneCaRunAcc σ past st =
        (iMax :: tl).foldl (oneCaStep σ past st) ⟨st.winners, {iMax}, ∅, st.bundle⟩ := by
      dsimp only [oneCaRunAcc]
      rw [show (Finset.univ.filter fun i => 0 < st.val i).sort (oneCaRel st.val) = iMax :: tl from
        hord]
    rw [List.append_nil, ← hrun_eq] at hfold_inv
    set acc := oneCaRunAcc σ past st
    set Wout := oneCaSelectBest st.val acc
    obtain ⟨hchoice, hgeW, hgeM, _⟩ := oneCaSelectBest_props st.val acc
    have hchoice' : Wout = acc.wSet ∨ Wout = acc.mSet ∨ Wout = acc.gSet := hchoice
    have hWout_pw : (Wout : Set N).PairwiseDisjoint acc.bundles := by
      rcases hchoice' with h | h | h <;> rw [h]
      · exact hfold_inv.w_pw
      · exact hfold_inv.m_pw
      · exact hfold_inv.g_pw
    have hWout_sub_act : Wout ⊆ active := by
      rcases hchoice' with h | h | h <;> rw [h]
      · exact hfold_inv.w_sub_active
      · exact hfold_inv.m_sub_active
      · exact hfold_inv.g_sub_active
    have hWout_disj : Disjoint Wout st.losers := by
      rw [Finset.disjoint_left]
      intro k hk hkL
      exact (Finset.mem_filter.1 (hWout_sub_act hk)).2.ne' ((hlos k).1 hkL)
    have hWout_ne : Wout.Nonempty := by
      have hposM : 0 < ∑ k ∈ acc.mSet, st.val k :=
        lt_of_lt_of_le (Finset.mem_filter.1 hiMax_act).2
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hfold_inv.iMax_mem_m)
      have hposOut : 0 < ∑ k ∈ Wout, st.val k := lt_of_lt_of_le hposM hgeM
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      simp only [hemp, Finset.sum_empty, lt_self_iff_false] at hposOut
    have hpareto : ∀ i, i ∉ Wout ∪ st.losers →
        ∃ l ∈ Wout, ¬ Disjoint (acc.bundles i) (acc.bundles l) := by
      intro i hi
      rw [Finset.mem_union, not_or] at hi
      have hi_act : i ∈ active := Finset.mem_filter.2
        ⟨Finset.mem_univ i, Nat.pos_of_ne_zero (mt (hlos i).2 hi.2)⟩
      have hi_rev : i ∈ (iMax :: tl).reverse := List.mem_reverse.2 ((hmem_iff i).2 hi_act)
      rcases hfold_inv.bundle_dichotomy i with huniv | hsmall
      · obtain ⟨l, hl⟩ := hWout_ne
        refine ⟨l, hl, ?_⟩
        rw [huniv]
        intro hdisj
        obtain ⟨x, hx⟩ := hfold_inv.bundle_nonempty l
        exact Finset.disjoint_left.1 hdisj (Finset.mem_univ x) hx
      · rcases hchoice' with h | h | h <;> rw [h] at hi ⊢
        · exact hfold_inv.w_pareto i hi_rev hi.1 hsmall
        · exact hfold_inv.m_pareto i hi_rev hi.1 hsmall
        · exact hfold_inv.g_pareto i hi_rev hi.1 hsmall
    have himp : ∑ i ∈ st.winners, st.val i ≤ ∑ i ∈ Wout, st.val i :=
      (Finset.sum_le_sum_of_subset hfold_inv.stW_sub_w).trans hgeW
    refine ⟨iMax, by rw [show active.sort (oneCaRel st.val) = iMax :: tl from hord]; rfl,
      hiMax_act, hiMax_ge, ?_, hWout_pw, hWout_disj, hpareto, hfold_inv.bundle_sub, himp⟩
    rw [show active.sort (oneCaRel st.val) = iMax :: tl from hord]
    exact hfold_inv

private theorem oneCaStateInv_of_run [Nonempty M] (σ : N → OneCaStrategy N M) (j : ℕ) :
    OneCaStateInv (wrapperState oneCaProc σ j) := by
  induction j with
  | zero =>
    refine ⟨Finset.disjoint_empty_left _, by simp only [wrapperState_zero, initState,
      Finset.coe_empty, Set.pairwiseDisjoint_empty],
      fun _ => Finset.univ_nonempty, fun _ => Or.inl rfl⟩
  | succ j ih =>
    by_cases ht : TerminatedAt oneCaProc σ j
    · rwa [wrapperState_succ_of_terminatedAt ht]
    · set cur := wrapperRunHist oneCaProc σ j
      obtain ⟨_, _, _, _, hfold, hpw, hdisj, _, _, _⟩ :=
        oneCaRunAcc_inv σ cur.2 cur.1 (mem_losers_iff_val_eq_zero oneCaProc σ j) ih ht
      have hW' : (wrapperState oneCaProc σ (j + 1)).winners =
          oneCaSelectBest cur.1.val (oneCaRunAcc σ cur.2 cur.1) := by
        rw [wrapperState_succ_winners ht, oneCaProc_proc_eq]
      have hB' : (wrapperState oneCaProc σ (j + 1)).bundle =
          (oneCaRunAcc σ cur.2 cur.1).bundles := by
        rw [wrapperState_succ_bundle ht, oneCaProc_proc_eq]
      refine ⟨?_, hW' ▸ hB' ▸ hpw, hB' ▸ hfold.bundle_nonempty, hB' ▸ hfold.bundle_dichotomy⟩
      rw [Finset.disjoint_left]
      intro i hiW hiL
      rw [mem_losers_iff_val_eq_zero] at hiL
      rw [hW'] at hiW
      have hnotL : i ∉ cur.1.losers := Finset.disjoint_left.1 hdisj hiW
      have hnz : cur.1.val i ≠ 0 := mt (mem_losers_iff_val_eq_zero oneCaProc σ j i).2 hnotL
      have hval_eq : (wrapperState oneCaProc σ (j + 1)).val i = cur.1.val i := by
        rw [wrapperState_succ_val ht i]
        have hmem : i ∈ (oneCaProc.proc σ cur.2 cur.1).1 ∪ cur.1.losers := by
          rw [oneCaProc_proc_eq]
          exact Finset.mem_union_left _ hiW
        change (if i ∈ (oneCaProc.proc σ cur.2 cur.1).1 ∪ cur.1.losers then cur.1.val i
          else _) = cur.1.val i
        simp only [hmem, ↓reduceIte]
      exact hnz (hval_eq.symm.trans hiL)

private theorem oneCaProc_isProperOn [Nonempty M] (σ : N → OneCaStrategy N M) :
    (oneCaProc (N := N) (M := M)).IsProperOn σ := by
  intro j hnotT
  set cur := wrapperRunHist oneCaProc σ j
  obtain ⟨_, _, _, _, _, hpw, hdisj, hpar, hsub, _⟩ := oneCaRunAcc_inv σ cur.2 cur.1
    (mem_losers_iff_val_eq_zero oneCaProc σ j) (oneCaStateInv_of_run σ j) hnotT
  dsimp only [WrapperProc.IsProperOn]
  change ((oneCaProc.proc σ cur.2 cur.1).1 : Set N).PairwiseDisjoint
      (oneCaProc.proc σ cur.2 cur.1).2 ∧
    Disjoint (oneCaProc.proc σ cur.2 cur.1).1 cur.1.losers ∧
    (∀ i, i ∉ (oneCaProc.proc σ cur.2 cur.1).1 ∪ cur.1.losers →
      ∃ l ∈ (oneCaProc.proc σ cur.2 cur.1).1,
        ¬ Disjoint ((oneCaProc.proc σ cur.2 cur.1).2 i) ((oneCaProc.proc σ cur.2 cur.1).2 l)) ∧
    (∀ i, (oneCaProc.proc σ cur.2 cur.1).2 i ⊆ cur.1.bundle i)
  rw [oneCaProc_proc_eq]
  exact ⟨hpw, hdisj, hpar, hsub⟩

private theorem oneCaProc_hasImprovementOn [Nonempty M] (σ : N → OneCaStrategy N M) :
    (oneCaProc (N := N) (M := M)).HasImprovementOn σ := by
  intro j hnotT
  set cur := wrapperRunHist oneCaProc σ j
  obtain ⟨_, _, _, _, _, _, _, _, _, himp⟩ := oneCaRunAcc_inv σ cur.2 cur.1
    (mem_losers_iff_val_eq_zero oneCaProc σ j) (oneCaStateInv_of_run σ j) hnotT
  change ∑ i ∈ cur.1.winners, cur.1.val i ≤ ∑ i ∈ (oneCaProc.proc σ cur.2 cur.1).1, cur.1.val i
  rw [oneCaProc_proc_eq]
  exact himp

/-- `1-CA-PROC` satisfies first-time shrink (Definition 12.48, p. 326) for every strategy profile
`σ`. -/
theorem oneCaProc_hasFirstTimeShrinkOn [Nonempty M] (σ : N → OneCaStrategy N M) :
    (oneCaProc (N := N) (M := M)).HasFirstTimeShrinkOn σ := by
  intro j hnotT i₁ i₂ hne h1eq h1lt h2eq h2lt
  set cur := wrapperRunHist oneCaProc σ j
  obtain ⟨_, _, _, _, hfold, _, _, _, _, _⟩ := oneCaRunAcc_inv σ cur.2 cur.1
    (mem_losers_iff_val_eq_zero oneCaProc σ j) (oneCaStateInv_of_run σ j) hnotT
  have hB' : (wrapperState oneCaProc σ (j + 1)).bundle =
      (oneCaRunAcc σ cur.2 cur.1).bundles := by
    rw [wrapperState_succ_bundle hnotT, oneCaProc_proc_eq]
  rw [hB'] at h1lt h2lt ⊢
  set active := Finset.univ.filter fun i => 0 < cur.1.val i
  set order := active.sort (oneCaRel cur.1.val)
  have hmem_rev : ∀ k, ((oneCaRunAcc σ cur.2 cur.1).bundles k).card < Fintype.card M →
      (cur.1.bundle k).card = Fintype.card M → k ∈ order.reverse := by
    intro k hlt heq
    by_contra hnot
    have hbun := hfold.bundle_unvisited k hnot
    rw [hbun, heq] at hlt
    exact lt_irrefl _ hlt
  have hg1 : i₁ ∈ (oneCaRunAcc σ cur.2 cur.1).gSet :=
    hfold.g_first_shrink i₁ (hmem_rev i₁ h1lt h1eq) h1eq h1lt
  have hg2 : i₂ ∈ (oneCaRunAcc σ cur.2 cur.1).gSet :=
    hfold.g_first_shrink i₂ (hmem_rev i₂ h2lt h2eq) h2eq h2lt
  exact hfold.g_pw hg1 hg2 hne

/-! #### Turn decomposition for `1-CA-PROC` (shared by weak dominance and Lemma 12.47) -/

private theorem oneCaRunAcc_split_at (σ : N → OneCaStrategy N M)
    (past : List (WrapperState N M)) (st : WrapperState N M)
    (hlos : ∀ i, i ∈ st.losers ↔ st.val i = 0)
    (hst : OneCaStateInv st)
    (hnotT : st.winners ∪ st.losers ≠ Finset.univ)
    {i : N} (hi_pos : 0 < st.val i) :
    let active := Finset.univ.filter fun k => 0 < st.val k
    let order := active.sort (oneCaRel st.val)
    ∃ (pre suf : List N) (iMax : N) (accBefore : OneCaAcc N M),
      order = pre ++ i :: suf ∧
      order.head? = some iMax ∧
      accBefore = pre.foldl (oneCaStep σ past st) ⟨st.winners, {iMax}, ∅, st.bundle⟩ ∧
      (∀ k ∈ pre, st.val i ≤ st.val k) ∧
      i ∉ pre ∧ i ∉ suf ∧
      OneCaFoldInv st active iMax pre.reverse accBefore ∧
      accBefore.bundles i = st.bundle i ∧
      oneCaRunAcc σ past st = suf.foldl (oneCaStep σ past st) (oneCaStep σ past st accBefore i) ∧
      accBefore.wSet ⊆ (oneCaRunAcc σ past st).wSet ∧
      accBefore.mSet ⊆ (oneCaRunAcc σ past st).mSet ∧
      accBefore.gSet ⊆ (oneCaRunAcc σ past st).gSet ∧
      (oneCaStep σ past st accBefore i).wSet ⊆ (oneCaRunAcc σ past st).wSet ∧
      (oneCaStep σ past st accBefore i).mSet ⊆ (oneCaRunAcc σ past st).mSet ∧
      (oneCaStep σ past st accBefore i).gSet ⊆ (oneCaRunAcc σ past st).gSet ∧
      (oneCaRunAcc σ past st).bundles i = (oneCaStep σ past st accBefore i).bundles i ∧
      (∀ k ∈ pre, (oneCaRunAcc σ past st).bundles k = accBefore.bundles k) ∧
      (i ∉ (oneCaStep σ past st accBefore i).wSet → i ∉ (oneCaRunAcc σ past st).wSet) ∧
      (i ∉ (oneCaStep σ past st accBefore i).mSet → i ∉ (oneCaRunAcc σ past st).mSet) ∧
      (i ∉ (oneCaStep σ past st accBefore i).gSet → i ∉ (oneCaRunAcc σ past st).gSet) := by
  set active := Finset.univ.filter fun k => 0 < st.val k
  set order := active.sort (oneCaRel st.val)
  have hi_act : i ∈ active := Finset.mem_filter.2 ⟨Finset.mem_univ i, hi_pos⟩
  have hi_ord : i ∈ order := (Finset.mem_sort (oneCaRel st.val)).2 hi_act
  obtain ⟨pre, suf, hsplit⟩ := List.append_of_mem hi_ord
  have hnodup : order.Nodup := active.sort_nodup (oneCaRel st.val)
  rw [hsplit] at hnodup
  have hpre_nodup : pre.Nodup := hnodup.of_append_left
  have hsuf_nodup : suf.Nodup := (List.nodup_cons.1 hnodup.of_append_right).2
  have hi_not_suf : i ∉ suf := (List.nodup_cons.1 hnodup.of_append_right).1
  have hi_not_pre : i ∉ pre := fun h =>
    List.disjoint_of_nodup_append hnodup h List.mem_cons_self
  have hdisj_ps : ∀ x ∈ suf, x ∉ pre := fun x hx hxp =>
    List.disjoint_of_nodup_append hnodup hxp (List.mem_cons_of_mem i hx)
  have hmem_act : ∀ x ∈ pre ++ i :: suf, x ∈ active := fun x hx =>
    (Finset.mem_sort (oneCaRel st.val)).1 (by change x ∈ order; rw [hsplit]; exact hx)
  have hpair : (pre ++ i :: suf).Pairwise (oneCaRel st.val) := by
    rw [← hsplit]
    exact active.pairwise_sort (oneCaRel st.val)
  have hpre_ge : ∀ k ∈ pre, st.val i ≤ st.val k := by
    intro k hk
    have hrel : oneCaRel st.val k i :=
      (List.pairwise_append.1 hpair).2.2 k hk i List.mem_cons_self
    rcases hrel with hlt | ⟨heq, _⟩
    · exact hlt.le
    · exact heq.le
  obtain ⟨iMax, hhead, hiMax_act, _, _, _, _, _, _, _⟩ :=
    oneCaRunAcc_inv σ past st hlos hst hnotT
  change order.head? = some iMax at hhead
  have hw_sub_act : st.winners ⊆ active := fun k hk =>
    Finset.mem_filter.2 ⟨Finset.mem_univ k, Nat.pos_of_ne_zero (mt (hlos k).2
      (Finset.disjoint_left.1 hst.disj hk))⟩
  have hinit_inv : OneCaFoldInv st active iMax [] ⟨st.winners, {iMax}, ∅, st.bundle⟩ := {
    w_sub_active := hw_sub_act
    m_sub_active := Finset.singleton_subset_iff.2 hiMax_act
    g_sub_active := Finset.empty_subset _
    stW_sub_w := Subset.rfl
    iMax_mem_m := Finset.mem_singleton_self iMax
    w_diff_visited := fun _ hk => Or.inl hk
    m_diff_visited := fun _ hk => Or.inl (Finset.mem_singleton.1 hk)
    g_sub_visited := fun _ hk => absurd hk (Finset.notMem_empty _)
    bundle_sub := fun _ => Subset.rfl
    bundle_unvisited := fun _ _ => rfl
    bundle_winners := fun _ _ => rfl
    bundle_nonempty := hst.nonempty
    bundle_dichotomy := hst.dichotomy
    w_pw := hst.pw
    m_pw := by simp only [Finset.coe_singleton, Set.pairwiseDisjoint_singleton]
    g_pw := by simp only [Finset.coe_empty, Set.pairwiseDisjoint_empty]
    g_small := fun _ hk => absurd hk (Finset.notMem_empty _)
    g_first_shrink := fun _ hk => absurd hk List.not_mem_nil
    w_pareto := fun _ hk => absurd hk List.not_mem_nil
    m_pareto := fun _ hk => absurd hk List.not_mem_nil
    g_pareto := fun _ hk => absurd hk List.not_mem_nil }
  have hpre_first : ∀ x ∈ pre, x = iMax → ([] : List N) = [] ∧ pre.head? = some iMax := by
    intro x hx rfl
    refine ⟨rfl, ?_⟩
    cases hpre : pre with
    | nil => rw [hpre] at hx; exact absurd hx List.not_mem_nil
    | cons a l =>
      rw [hpre] at hsplit
      rw [hsplit, List.cons_append, List.head?_cons] at hhead
      exact hhead
  obtain ⟨hinv_pre, _, _, _, _, _, _, _⟩ := oneCaFold_preserves_inv σ past st active iMax
    pre [] ⟨st.winners, {iMax}, ∅, st.bundle⟩ hinit_inv hpre_nodup
    (fun x hx => hmem_act x (List.mem_append_left _ hx)) (fun _ _ => List.not_mem_nil) hpre_first
  rw [List.append_nil] at hinv_pre
  set accBefore := pre.foldl (oneCaStep σ past st) ⟨st.winners, {iMax}, ∅, st.bundle⟩
  have hi_first : i = iMax → pre.reverse = [] := by
    intro rfl
    cases hpre : pre with
    | nil => rfl
    | cons a l =>
      rw [hpre] at hsplit
      have hhead' : a = i := by
        rw [hsplit, List.cons_append, List.head?_cons, Option.some.injEq] at hhead
        exact hhead
      exact absurd (hpre ▸ hhead' ▸ List.mem_cons_self) hi_not_pre
  obtain ⟨hinv_mid, hsubW_i, hsubM_i, hsubG_i, hbun_i⟩ := oneCaStep_preserves_inv σ past st active
    iMax pre.reverse accBefore i hinv_pre hi_act (by rwa [List.mem_reverse]) hi_first
  have hsuf_first : ∀ x ∈ suf, x = iMax → i :: pre.reverse = [] ∧ suf.head? = some iMax := by
    intro x hx rfl
    have hneq_i : x ≠ i := fun h => hi_not_suf (h ▸ hx)
    cases hpre : pre with
    | nil =>
      rw [hpre, List.nil_append] at hsplit
      rw [hsplit, List.head?_cons, Option.some.injEq] at hhead
      exact absurd hhead.symm hneq_i
    | cons a l =>
      rw [hpre] at hsplit
      rw [hsplit, List.cons_append, List.head?_cons, Option.some.injEq] at hhead
      exact absurd (hpre ▸ hhead ▸ List.mem_cons_self) (hdisj_ps x hx)
  obtain ⟨_, hsubW_s, hsubM_s, hsubG_s, hbun_s, hnotW_s, hnotM_s, hnotG_s⟩ :=
    oneCaFold_preserves_inv σ past st active iMax suf (i :: pre.reverse)
      (oneCaStep σ past st accBefore i) hinv_mid hsuf_nodup
      (fun x hx => hmem_act x (List.mem_append_right _ (List.mem_cons_of_mem i hx)))
      (fun x hx hxmem => by
        rcases List.mem_cons.1 hxmem with rfl | hxp
        · exact hi_not_suf hx
        · exact hdisj_ps x hx (List.mem_reverse.1 hxp))
      hsuf_first
  have hrun_eq : oneCaRunAcc σ past st =
      suf.foldl (oneCaStep σ past st) (oneCaStep σ past st accBefore i) := by
    have hfold_eq : order.foldl (oneCaStep σ past st) ⟨st.winners, {iMax}, ∅, st.bundle⟩ =
        suf.foldl (oneCaStep σ past st) (oneCaStep σ past st accBefore i) := by
      rw [hsplit, List.foldl_append, List.foldl_cons]
    cases hord : order with
    | nil => rw [hord] at hhead; simp only [List.head?_nil, reduceCtorEq] at hhead
    | cons a l =>
      rw [hord, List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      dsimp only [oneCaRunAcc]
      rw [show (Finset.univ.filter fun k => 0 < st.val k).sort (oneCaRel st.val) = a :: l from
        hord]
      dsimp only
      rw [← hord, hfold_eq]
  refine ⟨pre, suf, iMax, accBefore, hsplit, hhead, rfl, hpre_ge, hi_not_pre, hi_not_suf, hinv_pre,
    hinv_pre.bundle_unvisited i (by rwa [List.mem_reverse]), hrun_eq,
    hsubW_i.trans (hrun_eq ▸ hsubW_s), hsubM_i.trans (hrun_eq ▸ hsubM_s),
    hsubG_i.trans (hrun_eq ▸ hsubG_s), hrun_eq ▸ hsubW_s, hrun_eq ▸ hsubM_s, hrun_eq ▸ hsubG_s,
    by rw [hrun_eq]; exact hbun_s i hi_not_suf,
    fun k hk => by
      rw [hrun_eq, hbun_s k (fun h => hdisj_ps k h hk), hbun_i k (fun h => hi_not_pre (h ▸ hk))],
    fun h => hrun_eq ▸ hnotW_s i hi_not_suf h,
    fun h => hrun_eq ▸ hnotM_s i hi_not_suf h,
    fun h => hrun_eq ▸ hnotG_s i hi_not_suf h⟩

/-! #### Strategy class `D` invariants and explicit weak dominance -/

private theorem oneCaStrategyClass_invariants [Nonempty M] {σ : N → OneCaStrategy N M}
    {i : N} {p : SingleValuePlayer M} (hσ : σ i ∈ oneCaStrategyClass p i) :
    (∀ j, (wrapperState oneCaProc σ j).bundle i ∈ p.desired) ∧
    (∀ j, ((wrapperState oneCaProc σ j).val i : ℝ) ≤ p.value) ∧
    (∀ j, i ∈ retiredAt oneCaProc σ j →
      p.value / 2 ≤ ((wrapperState oneCaProc σ j).val i : ℝ)) := by
  have hbun : ∀ j, (wrapperState oneCaProc σ j).bundle i ∈ p.desired := by
    intro j
    induction j with
    | zero =>
      simp only [wrapperState_zero, initState, oneCaProc]
      exact p.univ_mem
    | succ j ih =>
      by_cases ht : TerminatedAt oneCaProc σ j
      · rwa [wrapperState_succ_of_terminatedAt ht]
      · set cur := wrapperRunHist oneCaProc σ j
        have hB' : (wrapperState oneCaProc σ (j + 1)).bundle i =
            (oneCaRunAcc σ cur.2 cur.1).bundles i := by
          rw [wrapperState_succ_bundle ht, oneCaProc_proc_eq]
        rw [hB']
        by_cases hpos : 0 < cur.1.val i
        · obtain ⟨pre, suf, iMax, accBefore, _, _, _, _, _, _, _, hbi_eq, _, _, _, _, _, _, _,
            hbun_end, _, _, _, _⟩ := oneCaRunAcc_split_at σ cur.2 cur.1
            (mem_losers_iff_val_eq_zero oneCaProc σ j) (oneCaStateInv_of_run σ j) ht hpos
          rw [hbun_end, oneCaStep_bundles_eq, Function.update_self]
          simp only [oneCaPickBundle]
          by_cases hW : i ∈ cur.1.winners
          · simp only [hW, ↓reduceIte, hbi_eq]; exact ih
          · simp only [hW, ↓reduceIte]
            cases hsh : (σ i).shrink ⟨cur.2, cur.1, accBefore.wSet, accBefore.mSet,
              accBefore.gSet, accBefore.bundles⟩ with
            | none => rw [hbi_eq]; exact ih
            | some b =>
              by_cases hval : IsValidShrink accBefore.gSet accBefore.bundles (accBefore.bundles i) b
              · simp only [hval, ↓reduceIte]
                rw [hbi_eq] at hval
                exact hσ.1 _ b hsh hval
              · simp only [hval, ↓reduceIte]
                rw [hbi_eq]
                exact ih
        · have hnot_act : i ∉ (Finset.univ.filter fun k => 0 < cur.1.val k).sort
              (oneCaRel cur.1.val) := by
            rw [Finset.mem_sort, Finset.mem_filter]
            exact fun h => hpos h.2
          obtain ⟨_, _, _, _, hfold, _, _, _, _, _⟩ := oneCaRunAcc_inv σ cur.2 cur.1
            (mem_losers_iff_val_eq_zero oneCaProc σ j) (oneCaStateInv_of_run σ j) ht
          rw [hfold.bundle_unvisited i (by rwa [List.mem_reverse])]
          exact ih
  have hval : ∀ j, ((wrapperState oneCaProc σ j).val i : ℝ) ≤ p.value := by
    intro j
    induction j with
    | zero =>
      simpa only [wrapperState_zero, initState, Nat.cast_one] using p.one_le_value
    | succ j ih =>
      by_cases ht : TerminatedAt oneCaProc σ j
      · rwa [wrapperState_succ_of_terminatedAt ht]
      · set cur := wrapperRunHist oneCaProc σ j
        set res := oneCaProc.proc σ cur.2 cur.1
        have hval_succ : (wrapperState oneCaProc σ (j + 1)).val i =
            if i ∈ res.1 ∪ cur.1.losers then cur.1.val i
            else if (σ i).double cur.2 cur.1 res.1 res.2 then 2 * cur.1.val i else 0 :=
          wrapperState_succ_val ht i
        rw [hval_succ]
        split_ifs with h1 h2
        · exact ih
        · by_contra hgt
          push Not at hgt
          have hgt' : p.value < 2 * (cur.1.val i : ℝ) := by
            have : ((2 * cur.1.val i : ℕ) : ℝ) = 2 * (cur.1.val i : ℝ) := by
              rw [Nat.cast_mul, Nat.cast_ofNat]
            linarith
          have hfalse := (hσ.2.2 cur.2 cur.1 res.1 res.2).1 hgt'
          exact Bool.false_ne_true (hfalse.symm.trans h2)
        · simp only [Nat.cast_zero]
          exact p.value_pos.le
  have hret : ∀ j, i ∈ retiredAt oneCaProc σ j →
      p.value / 2 ≤ ((wrapperState oneCaProc σ j).val i : ℝ) := by
    intro j hi
    rw [retiredAt, Finset.mem_sdiff] at hi
    obtain ⟨hi1, hi0⟩ := hi
    have hnotT : ¬ TerminatedAt oneCaProc σ j := fun ht =>
      hi0 (by rwa [wrapperState_succ_of_terminatedAt ht] at hi1)
    rw [mem_losers_iff_val_eq_zero] at hi1
    set cur := wrapperRunHist oneCaProc σ j
    set res := oneCaProc.proc σ cur.2 cur.1
    have hnz : cur.1.val i ≠ 0 := mt (mem_losers_iff_val_eq_zero oneCaProc σ j i).2 hi0
    have hval_succ : (wrapperState oneCaProc σ (j + 1)).val i =
        if i ∈ res.1 ∪ cur.1.losers then cur.1.val i
        else if (σ i).double cur.2 cur.1 res.1 res.2 then 2 * cur.1.val i else 0 :=
      wrapperState_succ_val hnotT i
    rw [hval_succ] at hi1
    by_contra hlt
    push Not at hlt
    have hlt' : 2 * (cur.1.val i : ℝ) < p.value := by
      have : (cur.1.val i : ℝ) = ((wrapperState oneCaProc σ j).val i : ℝ) := rfl
      linarith
    have htrue := (hσ.2.2 cur.2 cur.1 res.1 res.2).2 hlt'
    rw [htrue] at hi1
    simp only [↓reduceIte] at hi1
    split_ifs at hi1
    · exact hnz hi1
    · exact mul_ne_zero two_ne_zero hnz hi1
  exact ⟨hbun, hval, hret⟩

/-- **Weak dominance of `oneCaStrategyClass` (`D`) in `Wrapper + 1-CA-PROC`** ([Lavi2007], §12.5,
p. 325): for every player `i` and every full-history strategy `st`, `dominateOneCaStrategy p i st`
belongs to `oneCaStrategyClass p i` and weakly dominates `st` against all opponent profiles. -/
theorem dominateOneCaStrategy_weaklyDominates [Nonempty M] (p : SingleValuePlayer M) (i : N)
    (st : OneCaStrategy N M) :
    (oneCaProc (N := N) (M := M)).WeaklyDominates p i (dominateOneCaStrategy p i st) st := by
  intro σ
  set P := oneCaProc (N := N) (M := M)
  set σ₁ := Function.update σ i st
  set σ₂ := Function.update σ i (dominateOneCaStrategy p i st)
  have hσ₂_mem : σ₂ i ∈ oneCaStrategyClass p i := by
    simpa only [σ₂, Function.update_self] using dominateOneCaStrategy_mem p i st
  obtain ⟨hbun₂, hval₂, _⟩ := oneCaStrategyClass_invariants hσ₂_mem
  have hutil₂_nonneg : 0 ≤ P.utility σ₂ p i := by
    classical
    simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment]
    split_ifs with hT hW
    · rw [p.eval_of_mem (hbun₂ (termRound P σ₂))]
      linarith [hval₂ (termRound P σ₂)]
    · simp only [SingleValuePlayer.eval_empty, sub_zero, le_refl]
    · simp only [SingleValuePlayer.eval_empty, sub_zero, le_refl]
  by_cases heq : ∀ j, wrapperRunHist P σ₁ j = wrapperRunHist P σ₂ j
  · have hstEq : ∀ j, wrapperState P σ₁ j = wrapperState P σ₂ j := fun j =>
      congrArg Prod.fst (heq j)
    have hTeq : Terminates P σ₁ ↔ Terminates P σ₂ := by
      simp only [Terminates, TerminatedAt, hstEq]
    have hreq : termRound P σ₁ = termRound P σ₂ := by
      classical
      simp only [termRound, hTeq]
      split_ifs with hT₂
      · refine le_antisymm ?_ ?_
        · exact Nat.find_min' (hTeq.2 hT₂)
            (by simpa only [TerminatedAt, hstEq] using Nat.find_spec hT₂)
        · exact Nat.find_min' hT₂
            (by simpa only [TerminatedAt, ← hstEq] using Nat.find_spec (hTeq.2 hT₂))
      · rfl
    have haeq : P.alloc σ₁ i = P.alloc σ₂ i := by
      classical simp only [WrapperProc.alloc, hTeq, hreq, hstEq]
    have hpeq : P.payment σ₁ i = P.payment σ₂ i := by
      classical simp only [WrapperProc.payment, hTeq, hreq, hstEq]
    simp only [WrapperProc.utility, haeq, hpeq, le_refl]
  · -- Consider the first iteration `j` where `wrapperRunHist` diverges.
    classical
    push Not at heq
    set m := Nat.find heq
    have hm_ne : wrapperRunHist P σ₁ m ≠ wrapperRunHist P σ₂ m := Nat.find_spec heq
    have hm_pos : 0 < m := by
      by_contra h0
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos h0
      exact hm_ne (by simp only [hm0, wrapperRunHist])
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm_pos.ne'
    rw [hj] at hm_ne
    have hj_eq : wrapperRunHist P σ₁ j = wrapperRunHist P σ₂ j := by
      by_contra hne
      exact Nat.find_min heq (by omega : j < m) hne
    have hnotT₁ : ¬ TerminatedAt P σ₁ j := by
      intro ht
      have ht₂ : TerminatedAt P σ₂ j := by
        simpa only [TerminatedAt, wrapperState, hj_eq] using ht
      apply hm_ne
      simp only [wrapperRunHist, wrapperNext, TerminatedAt, wrapperState] at ht ht₂ ⊢
      simp only [hj_eq, ht₂, ↓reduceIte]
    have hnotT₂ : ¬ TerminatedAt P σ₂ j := by
      simpa only [TerminatedAt, wrapperState, hj_eq] using hnotT₁
    set cur := wrapperRunHist P σ₁ j
    have hcur₂ : wrapperRunHist P σ₂ j = cur := hj_eq.symm
    suffices hutil₁_le_zero : P.utility σ₁ p i ≤ 0 by exact hutil₁_le_zero.trans hutil₂_nonneg
    by_cases hT₁ : Terminates P σ₁
    · have hJ_ge : j + 1 ≤ termRound P σ₁ := by
        by_contra hlt
        push Not at hlt
        exact hnotT₁ (terminatedAt_mono (termRound_spec hT₁) (Nat.le_of_lt_succ hlt))
      have hproper₁ := oneCaProc_isProperOn σ₁
      -- Check whether `oneCaRunAcc` itself differed at iteration `j`.
      by_cases hproc_eq : oneCaRunAcc σ₁ cur.2 cur.1 = oneCaRunAcc σ₂ cur.2 cur.1
      · -- `oneCaRunAcc` matched, so `σ₁` and `σ₂` must have differed in step 2 (`double`) for `i`.
        have hprocP : P.proc σ₁ cur.2 cur.1 = P.proc σ₂ cur.2 cur.1 := by
          simp only [P, oneCaProc_proc_eq, hproc_eq]
        set W' := oneCaSelectBest cur.1.val (oneCaRunAcc σ₁ cur.2 cur.1)
        set s' := (oneCaRunAcc σ₁ cur.2 cur.1).bundles
        have hprocP₁ : P.proc σ₁ cur.2 cur.1 = (W', s') := oneCaProc_proc_eq σ₁ cur.2 cur.1
        have hnotMem : i ∉ W' ∪ cur.1.losers := by
          intro hm
          apply hm_ne
          simp only [wrapperRunHist]
          refine Prod.ext ?_ (by rw [hcur₂])
          rw [hcur₂]
          exact wrapperNext_congr hprocP fun k hk => by
            have hki : k ≠ i := fun h => hk (by
              change k ∈ (P.proc σ₁ cur.2 cur.1).1 ∪ cur.1.losers
              rw [hprocP₁]; exact h ▸ hm)
            have hσk : σ₁ k = σ₂ k := by simp only [σ₁, σ₂, Function.update_of_ne hki]
            change P.chooseDouble (σ₁ k) cur.2 cur.1
              (P.proc σ₁ cur.2 cur.1).1 (P.proc σ₁ cur.2 cur.1).2 =
              P.chooseDouble (σ₂ k) cur.2 cur.1
              (P.proc σ₂ cur.2 cur.1).1 (P.proc σ₂ cur.2 cur.1).2
            rw [hσk, hprocP]
        have hch_ne : st.double cur.2 cur.1 W' s' ≠
            (dominateOneCaStrategy p i st).double cur.2 cur.1 W' s' := by
          intro hch
          apply hm_ne
          simp only [wrapperRunHist]
          refine Prod.ext ?_ (by rw [hcur₂])
          rw [hcur₂]
          exact wrapperNext_congr hprocP fun k _ => by
            by_cases hk : k = i
            · subst hk
              change P.chooseDouble (σ₁ k) cur.2 cur.1
                (P.proc σ₁ cur.2 cur.1).1 (P.proc σ₁ cur.2 cur.1).2 =
                P.chooseDouble (σ₂ k) cur.2 cur.1
                (P.proc σ₂ cur.2 cur.1).1 (P.proc σ₂ cur.2 cur.1).2
              rw [← hprocP, hprocP₁]
              have hσ₁i : σ₁ k = st := Function.update_self k st σ
              have hσ₂i : σ₂ k = dominateOneCaStrategy p k st := Function.update_self k _ σ
              change (σ₁ k).double cur.2 cur.1 W' s' = (σ₂ k).double cur.2 cur.1 W' s'
              rw [hσ₁i, hσ₂i]
              exact hch
            · have hσk : σ₁ k = σ₂ k := by simp only [σ₁, σ₂, Function.update_of_ne hk]
              change P.chooseDouble (σ₁ k) cur.2 cur.1
                (P.proc σ₁ cur.2 cur.1).1 (P.proc σ₁ cur.2 cur.1).2 =
                P.chooseDouble (σ₂ k) cur.2 cur.1
                (P.proc σ₂ cur.2 cur.1).1 (P.proc σ₂ cur.2 cur.1).2
              rw [hσk, hprocP]
        have hval_j1 : (wrapperState P σ₁ (j + 1)).val i =
            if st.double cur.2 cur.1 W' s' then 2 * cur.1.val i else 0 := by
          rw [wrapperState_succ_val hnotT₁ i]
          have hσ₁i : σ₁ i = st := Function.update_self i st σ
          change (if i ∈ (P.proc σ₁ cur.2 cur.1).1 ∪ cur.1.losers then cur.1.val i
            else if (σ₁ i).double cur.2 cur.1 (P.proc σ₁ cur.2 cur.1).1 (P.proc σ₁ cur.2 cur.1).2
              then 2 * cur.1.val i else 0) = _
          rw [hprocP₁]
          simp only [hnotMem, hσ₁i, ↓reduceIte]
        cases hst_ch : st.double cur.2 cur.1 W' s'
        · have hret₁ : (wrapperState P σ₁ (j + 1)).val i = 0 := by
            simp only [hval_j1, hst_ch, Bool.false_eq_true, ↓reduceIte]
          have hiL : i ∈ (wrapperState P σ₁ (termRound P σ₁)).losers :=
            losers_mono P σ₁ hJ_ge ((mem_losers_iff_val_eq_zero P σ₁ (j + 1) i).2 hret₁)
          have hiNotW : i ∉ (wrapperState P σ₁ (termRound P σ₁)).winners :=
            Finset.disjoint_right.1 (disjoint_winners_losers_of_isProperOn hproper₁ _) hiL
          simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment, hT₁, ↓reduceIte,
            hiNotW, SingleValuePlayer.eval_empty, sub_zero, le_refl]
        · have hdom_false : (dominateOneCaStrategy p i st).double cur.2 cur.1 W' s' = false := by
            rw [hst_ch] at hch_ne
            cases h2 : (dominateOneCaStrategy p i st).double cur.2 cur.1 W' s'
            · rfl
            · exact absurd h2.symm hch_ne
          have hge_val : p.value ≤ ((wrapperState P σ₁ (j + 1)).val i : ℝ) := by
            simp only [hval_j1, hst_ch, ↓reduceIte, Nat.cast_mul, Nat.cast_ofNat]
            simp only [dominateOneCaStrategy] at hdom_false
            split_ifs at hdom_false with hgt hlt
            · exact hgt.le
            · exact Bool.noConfusion (hst_ch.symm.trans hdom_false)
          simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment, hT₁, ↓reduceIte]
          split_ifs with hW
          · have hiNotL : i ∉ (wrapperState P σ₁ (termRound P σ₁)).losers :=
              Finset.disjoint_left.1 (disjoint_winners_losers_of_isProperOn hproper₁ _) hW
            have hmono : ((wrapperState P σ₁ (j + 1)).val i : ℝ) ≤
                ((wrapperState P σ₁ (termRound P σ₁)).val i : ℝ) := by
              exact_mod_cast val_mono_of_not_mem_losers P σ₁ hJ_ge hiNotL
            linarith [p.eval_le_value ((wrapperState P σ₁ (termRound P σ₁)).bundle i)]
          · simp only [SingleValuePlayer.eval_empty, sub_zero, le_refl]
      · -- `oneCaRunAcc` differed at iteration `j`: `i` is active and `oneCaPickBundle` differed.
        have hi_pos : 0 < cur.1.val i := by
          by_contra h0
          apply hproc_eq
          have hfold_eq : ∀ (xs : List N) (acc : OneCaAcc N M), i ∉ xs →
              xs.foldl (oneCaStep σ₁ cur.2 cur.1) acc =
                xs.foldl (oneCaStep σ₂ cur.2 cur.1) acc := by
            intro xs
            induction xs with
            | nil => intro _ _; rfl
            | cons a l ih =>
              intro acc hni
              rw [List.mem_cons, not_or] at hni
              have hσa : σ₁ a = σ₂ a := by simp only [σ₁, σ₂, Function.update_of_ne (Ne.symm hni.1)]
              have hstep : oneCaStep σ₁ cur.2 cur.1 acc a = oneCaStep σ₂ cur.2 cur.1 acc a := by
                simp only [oneCaStep, oneCaPickBundle, hσa]
              rw [List.foldl_cons, List.foldl_cons, hstep]
              exact ih _ hni.2
          simp only [oneCaRunAcc]
          cases hord : (Finset.univ.filter fun k => 0 < cur.1.val k).sort (oneCaRel cur.1.val) with
          | nil => rfl
          | cons iMax tl =>
            refine hfold_eq (iMax :: tl) _ ?_
            rw [← hord, Finset.mem_sort, Finset.mem_filter]
            exact fun h => h0 h.2
        obtain ⟨pre, suf, iMax, accBefore, hsplit, hhead, hacc_def, _, hi_not_pre, hi_not_suf,
          hinv_pre, hbi_eq, hrun₁, _, _, _, _, _, _, hbun_end₁, _, hnotW₁, hnotM₁, hnotG₁⟩ :=
          oneCaRunAcc_split_at σ₁ cur.2 cur.1 (mem_losers_iff_val_eq_zero P σ₁ j)
            (oneCaStateInv_of_run σ₁ j) hnotT₁ hi_pos
        have hfold_agree : ∀ (xs : List N) (acc : OneCaAcc N M), i ∉ xs →
            xs.foldl (oneCaStep σ₁ cur.2 cur.1) acc = xs.foldl (oneCaStep σ₂ cur.2 cur.1) acc := by
          intro xs
          induction xs with
          | nil => intro _ _; rfl
          | cons a l ih =>
            intro acc hni
            rw [List.mem_cons, not_or] at hni
            have hσa : σ₁ a = σ₂ a := by
              simp only [σ₁, σ₂, Function.update_of_ne (Ne.symm hni.1)]
            have hstep : oneCaStep σ₁ cur.2 cur.1 acc a = oneCaStep σ₂ cur.2 cur.1 acc a := by
              simp only [oneCaStep, oneCaPickBundle, hσa]
            rw [List.foldl_cons, List.foldl_cons, hstep]
            exact ih _ hni.2
        have hpick_ne : oneCaPickBundle σ₁ cur.2 cur.1 accBefore i ≠
            oneCaPickBundle σ₂ cur.2 cur.1 accBefore i := by
          intro hpick
          apply hproc_eq
          have hord_cases : ∃ tl, (Finset.univ.filter fun k => 0 < cur.1.val k).sort
              (oneCaRel cur.1.val) = iMax :: tl := by
            cases hord :
                (Finset.univ.filter fun k => 0 < cur.1.val k).sort (oneCaRel cur.1.val) with
            | nil => rw [hord] at hhead; simp only [List.head?_nil, reduceCtorEq] at hhead
            | cons a l =>
              rw [hord, List.head?_cons, Option.some.injEq] at hhead
              exact ⟨l, hhead ▸ rfl⟩
          obtain ⟨tl, hord⟩ := hord_cases
          have hrun₂ : oneCaRunAcc σ₂ cur.2 cur.1 =
              suf.foldl (oneCaStep σ₂ cur.2 cur.1)
                (oneCaStep σ₂ cur.2 cur.1 accBefore i) := by
            simp only [oneCaRunAcc, hord]
            rw [← hord, hsplit, List.foldl_append, List.foldl_cons,
              ← hfold_agree pre _ hi_not_pre, ← hacc_def]
          have hstep_eq : oneCaStep σ₁ cur.2 cur.1 accBefore i =
              oneCaStep σ₂ cur.2 cur.1 accBefore i := by
            simp only [oneCaStep, hpick]
          rw [hrun₁, hrun₂, ← hstep_eq]
          exact hfold_agree suf _ hi_not_suf
        have hiNotW : i ∉ cur.1.winners := by
          intro hW
          apply hpick_ne
          simp only [oneCaPickBundle, hW, ↓reduceIte]
        set view : OneCaShrinkView N M :=
          ⟨cur.2, cur.1, accBefore.wSet, accBefore.mSet, accBefore.gSet, accBefore.bundles⟩
        have hσ₁i : σ₁ i = st := Function.update_self i st σ
        have hσ₂i : σ₂ i = dominateOneCaStrategy p i st := Function.update_self i _ σ
        -- Analyze why `oneCaPickBundle` differed between `st` and `dominateOneCaStrategy p i st`.
        by_cases hst_undes : ∃ b, st.shrink view = some b ∧
            IsValidShrink accBefore.gSet accBefore.bundles (cur.1.bundle i) b ∧ b ∉ p.desired
        · -- Violation 1: `st` shrunk to a valid but undesired bundle `b ∉ p.desired`.
          obtain ⟨b, hsh, hval, hbNotD⟩ := hst_undes
          have hpick₁ : oneCaPickBundle σ₁ cur.2 cur.1 accBefore i = b := by
            simp only [oneCaPickBundle, hiNotW, ↓reduceIte, hσ₁i, hbi_eq]
            change (match st.shrink view with
              | some b' => if IsValidShrink accBefore.gSet accBefore.bundles (cur.1.bundle i) b'
                  then b' else cur.1.bundle i
              | none => cur.1.bundle i) = b
            simp only [hsh, hval, ↓reduceIte]
          have hB_j1 : (wrapperState P σ₁ (j + 1)).bundle i = b := by
            have hB' : (wrapperState P σ₁ (j + 1)).bundle i =
                (oneCaRunAcc σ₁ cur.2 cur.1).bundles i := by
              rw [wrapperState_succ_bundle hnotT₁, oneCaProc_proc_eq]
            rw [hB', hbun_end₁]
            have hstep_bun : (oneCaStep σ₁ cur.2 cur.1 accBefore i).bundles i =
                oneCaPickBundle σ₁ cur.2 cur.1 accBefore i := by
              simp only [oneCaStep]; split_ifs <;> exact Function.update_self _ _ _
            rw [hstep_bun, hpick₁]
          have hnotDes_J : (wrapperState P σ₁ (termRound P σ₁)).bundle i ∉ p.desired := fun hmem =>
            hbNotD (p.upward_closed hmem (hB_j1 ▸ bundle_subset_of_isProperOn hproper₁ hJ_ge i))
          simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment, hT₁, ↓reduceIte]
          split_ifs with hW
          · rw [p.eval_of_not_mem hnotDes_J, zero_sub, neg_nonpos]
            exact Nat.cast_nonneg _
          · simp only [SingleValuePlayer.eval_empty, sub_zero, le_refl]
        · -- Violation 2: `st` stayed silent while `IsLoserIfSilent p i view` held!
          have hsilent : oneCaPickBundle σ₁ cur.2 cur.1 accBefore i = cur.1.bundle i := by
            simp only [oneCaPickBundle, hiNotW, ↓reduceIte, hσ₁i, hbi_eq]
            cases hsh : st.shrink view with
            | none => rfl
            | some b =>
              by_cases hval : IsValidShrink accBefore.gSet accBefore.bundles (cur.1.bundle i) b
              · -- Then `b ∈ p.desired`, so `dominateOneCaStrategy` also returns `some b`.
                have hdes : b ∈ p.desired := by
                  by_contra hnd
                  exact hst_undes ⟨b, hsh, hval, hnd⟩
                exfalso
                apply hpick_ne
                simp only [oneCaPickBundle, hiNotW, ↓reduceIte, hσ₁i, hσ₂i, hbi_eq]
                change (match st.shrink view with
                  | some b' => if IsValidShrink accBefore.gSet accBefore.bundles (cur.1.bundle i) b'
                      then b' else cur.1.bundle i
                  | none => cur.1.bundle i) =
                  (match (dominateOneCaStrategy p i st).shrink view with
                  | some b' => if IsValidShrink accBefore.gSet accBefore.bundles (cur.1.bundle i) b'
                      then b' else cur.1.bundle i
                  | none => cur.1.bundle i)
                simp only [dominateOneCaStrategy, view, hsh, hval, hdes, and_self, ↓reduceIte]
              · simp only [hval, ↓reduceIte]
          have hlis : IsLoserIfSilent p i view := by
            by_contra hnotLis
            apply hpick_ne
            rw [hsilent]
            symm
            simp only [oneCaPickBundle, hiNotW, ↓reduceIte, hσ₂i, hbi_eq]
            change (match (dominateOneCaStrategy p i st).shrink view with
              | some b' => if IsValidShrink accBefore.gSet accBefore.bundles (cur.1.bundle i) b'
                  then b' else cur.1.bundle i
              | none => cur.1.bundle i) = cur.1.bundle i
            simp only [dominateOneCaStrategy]
            cases hsh : st.shrink view with
            | none => simp only [hnotLis, ↓reduceIte]
            | some b =>
              by_cases hgood : IsValidShrink accBefore.gSet accBefore.bundles (cur.1.bundle i) b ∧
                  b ∈ p.desired
              · exfalso
                have hpick₁ : oneCaPickBundle σ₁ cur.2 cur.1 accBefore i = b := by
                  simp only [oneCaPickBundle, hiNotW, ↓reduceIte, hσ₁i, hbi_eq]
                  change (match st.shrink view with
                    | some b' =>
                      if IsValidShrink accBefore.gSet accBefore.bundles (cur.1.bundle i) b'
                        then b' else cur.1.bundle i
                    | none => cur.1.bundle i) = b
                  simp only [hsh, hgood.1, ↓reduceIte]
                apply hpick_ne
                rw [hpick₁]
                symm
                simp only [oneCaPickBundle, hiNotW, ↓reduceIte, hσ₂i, hbi_eq]
                change (match (dominateOneCaStrategy p i st).shrink view with
                  | some b' => if IsValidShrink accBefore.gSet accBefore.bundles (cur.1.bundle i) b'
                      then b' else cur.1.bundle i
                  | none => cur.1.bundle i) = b
                simp only [dominateOneCaStrategy, view, hsh, hgood.1, hgood.2, and_self, ↓reduceIte]
              · simp only [view, hgood, hnotLis, ↓reduceIte]
          -- Since `i` stayed silent while `IsLoserIfSilent p i view`, `i ∉ W_{j+1}`.
          obtain ⟨hval_half, hiNotW0, hiNotM0, hiNotG0, hnotFree⟩ := hlis
          have hsNext_eq : Function.update accBefore.bundles i (cur.1.bundle i) =
              accBefore.bundles := by
            rw [← hbi_eq, Function.update_eq_self]
          have hstep_notW : i ∉ (oneCaStep σ₁ cur.2 cur.1 accBefore i).wSet := by
            rw [oneCaStep_wSet_eq, hsilent, hsNext_eq]
            split_ifs with hc hf
            · exact absurd ⟨hc, Or.inl hf⟩ hnotFree
            · exact hiNotW0
            · exact hiNotW0
          have hstep_notM : i ∉ (oneCaStep σ₁ cur.2 cur.1 accBefore i).mSet := by
            rw [oneCaStep_mSet_eq, hsilent, hsNext_eq]
            split_ifs with hc hf
            · exact absurd ⟨hc, Or.inr (Or.inl hf)⟩ hnotFree
            · exact hiNotM0
            · exact hiNotM0
          have hstep_notG : i ∉ (oneCaStep σ₁ cur.2 cur.1 accBefore i).gSet := by
            rw [oneCaStep_gSet_eq, hsilent, hsNext_eq]
            split_ifs with hc hf
            · exact absurd ⟨hc, Or.inr (Or.inr hf)⟩ hnotFree
            · exact hiNotG0
            · exact hiNotG0
          have hiNotW_j1 : i ∉ (wrapperState P σ₁ (j + 1)).winners := by
            have hW1 : (wrapperState P σ₁ (j + 1)).winners =
                oneCaSelectBest cur.1.val (oneCaRunAcc σ₁ cur.2 cur.1) := by
              rw [wrapperState_succ_winners hnotT₁, oneCaProc_proc_eq]
            rw [hW1]
            rcases (oneCaSelectBest_props cur.1.val
                (oneCaRunAcc σ₁ cur.2 cur.1)).1 with h | h | h <;>
              rw [h]
            · exact hnotW₁ hstep_notW
            · exact hnotM₁ hstep_notM
            · exact hnotG₁ hstep_notG
          have hiNotL_j : i ∉ cur.1.losers := by
            change i ∉ (wrapperState P σ₁ j).losers
            rw [mem_losers_iff_val_eq_zero]
            exact hi_pos.ne'
          -- At step 2, `st` either retires (utility `0`) or doubles to `2 * v_i^j ≥ p.value`.
          by_cases hret₁ : (wrapperState P σ₁ (j + 1)).val i = 0
          · have hiL : i ∈ (wrapperState P σ₁ (termRound P σ₁)).losers :=
              losers_mono P σ₁ hJ_ge ((mem_losers_iff_val_eq_zero P σ₁ (j + 1) i).2 hret₁)
            have hiNotWJ : i ∉ (wrapperState P σ₁ (termRound P σ₁)).winners :=
              Finset.disjoint_right.1 (disjoint_winners_losers_of_isProperOn hproper₁ _) hiL
            simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment, hT₁, ↓reduceIte,
              hiNotWJ, SingleValuePlayer.eval_empty, sub_zero, le_refl]
          · have hval_j1 : (wrapperState P σ₁ (j + 1)).val i = 2 * cur.1.val i := by
              have hnotMem : i ∉ oneCaSelectBest cur.1.val (oneCaRunAcc σ₁ cur.2 cur.1) ∪
                  cur.1.losers := by
                rw [Finset.mem_union, not_or]
                refine ⟨?_, hiNotL_j⟩
                have hW1 : (wrapperState P σ₁ (j + 1)).winners =
                    oneCaSelectBest cur.1.val (oneCaRunAcc σ₁ cur.2 cur.1) := by
                  rw [wrapperState_succ_winners hnotT₁, oneCaProc_proc_eq]
                rwa [← hW1]
              rw [wrapperState_succ_val hnotT₁ i] at hret₁ ⊢
              change (if i ∈ (P.proc σ₁ cur.2 cur.1).1 ∪ cur.1.losers
                then cur.1.val i
                else if (σ₁ i).double _ _ _ _ then 2 * cur.1.val i else 0) ≠ 0 at hret₁
              change (if i ∈ (P.proc σ₁ cur.2 cur.1).1 ∪ cur.1.losers
                then cur.1.val i
                else if (σ₁ i).double _ _ _ _ then 2 * cur.1.val i else 0) = 2 * cur.1.val i
              rw [oneCaProc_proc_eq] at hret₁ ⊢
              simp only [hnotMem, ↓reduceIte] at hret₁ ⊢
              split_ifs at hret₁ ⊢
              · rfl
              · exact absurd rfl hret₁
            simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment, hT₁, ↓reduceIte]
            split_ifs with hW
            · have hiNotLJ : i ∉ (wrapperState P σ₁ (termRound P σ₁)).losers :=
                Finset.disjoint_left.1 (disjoint_winners_losers_of_isProperOn hproper₁ _) hW
              have hmono : ((wrapperState P σ₁ (j + 1)).val i : ℝ) ≤
                  ((wrapperState P σ₁ (termRound P σ₁)).val i : ℝ) := by
                exact_mod_cast val_mono_of_not_mem_losers P σ₁ hJ_ge hiNotLJ
              have hge_val : p.value ≤ ((wrapperState P σ₁ (j + 1)).val i : ℝ) := by
                rw [hval_j1, Nat.cast_mul, Nat.cast_ofNat]
                linarith
              linarith [p.eval_le_value ((wrapperState P σ₁ (termRound P σ₁)).bundle i)]
            · simp only [SingleValuePlayer.eval_empty, sub_zero, le_refl]
    · simp only [WrapperProc.utility, WrapperProc.alloc, WrapperProc.payment, hT₁, ↓reduceIte,
        SingleValuePlayer.eval_empty, sub_zero, le_refl]

/-! #### Lemma 12.47 (`1-CA-PROC` is a `(3 + 2 √m)`-local-approximation) -/

/-- **Lemma 12.47** ([Lavi2007], §12.5, pp. 325–326): `1-CA-PROC` is a
`(3 + 2 * Real.sqrt (Fintype.card M))`-local-approximation with respect to `oneCaStrategyClass`. -/
theorem oneCaProc_isLocalApproxOn [Nonempty M] (players : N → SingleValuePlayer M) :
    (oneCaProc (N := N) (M := M)).IsLocalApproxOn players
      (fun i => oneCaStrategyClass (players i) i)
      (3 + 2 * Real.sqrt (Fintype.card M)) := by
  intro σ hσ
  have hinv_all : ∀ i,
      (∀ j, (wrapperState oneCaProc σ j).bundle i ∈ (players i).desired) ∧
      (∀ j, ((wrapperState oneCaProc σ j).val i : ℝ) ≤ (players i).value) ∧
      (∀ j, i ∈ retiredAt oneCaProc σ j →
        (players i).value / 2 ≤ ((wrapperState oneCaProc σ j).val i : ℝ)) :=
    fun i => oneCaStrategyClass_invariants (hσ i)
  refine ⟨oneCaProc_isProperOn σ, oneCaProc_hasImprovementOn σ, ?_,
    fun j i => (hinv_all i).1 j, fun j i => (hinv_all i).2.1 j, fun j i hi => (hinv_all i).2.2 j hi⟩
  intro j hnotT
  classical
  set P := oneCaProc (N := N) (M := M)
  set cur := wrapperRunHist P σ j
  set st := cur.1
  set acc := oneCaRunAcc σ cur.2 st
  set Wout := oneCaSelectBest st.val acc
  have hW1 : (wrapperState P σ (j + 1)).winners = Wout := by
    rw [wrapperState_succ_winners hnotT, oneCaProc_proc_eq]
  rw [hW1]
  obtain ⟨iMax, _, hiMax_act, hiMax_ge, hfold, _, _, _, _, _⟩ :=
    oneCaRunAcc_inv σ cur.2 st (mem_losers_iff_val_eq_zero P σ j) (oneCaStateInv_of_run σ j) hnotT
  obtain ⟨_, hgeW, hgeM, hgeG⟩ := oneCaSelectBest_props st.val acc
  set sumBest : ℝ := ∑ k ∈ Wout, (st.val k : ℝ)
  have hgeW_R : ∑ k ∈ acc.wSet, (st.val k : ℝ) ≤ sumBest := by
    change ∑ k ∈ acc.wSet, (st.val k : ℝ) ≤ ∑ k ∈ Wout, (st.val k : ℝ)
    exact_mod_cast hgeW
  have hgeM_R : ∑ k ∈ acc.mSet, (st.val k : ℝ) ≤ sumBest := by
    change ∑ k ∈ acc.mSet, (st.val k : ℝ) ≤ ∑ k ∈ Wout, (st.val k : ℝ)
    exact_mod_cast hgeM
  have hgeG_R : ∑ k ∈ acc.gSet, (st.val k : ℝ) ≤ sumBest := by
    change ∑ k ∈ acc.gSet, (st.val k : ℝ) ≤ ∑ k ∈ Wout, (st.val k : ℝ)
    exact_mod_cast hgeG
  have hsumBest_nonneg : 0 ≤ sumBest := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  change optWelfareOn (retiredAt P σ j) (fun i => (st.val i : ℝ))
      (restrictedDesired (fun k => (players k).desired) st.bundle) ≤
    (3 + 2 * Real.sqrt (Fintype.card M)) * sumBest
  obtain ⟨alloc, hfeas, hEq⟩ := exists_feasibleAlloc_eq_optWelfareOn
    (retiredAt P σ j) (fun i => (st.val i : ℝ))
    (restrictedDesired (fun k => (players k).desired) st.bundle)
  rw [← hEq]
  set optW : Finset N := (retiredAt P σ j).filter fun i =>
    alloc i ∈ restrictedDesired (fun k => (players k).desired) st.bundle i
  have hopt_sum : welfareOn (retiredAt P σ j) (fun i => (st.val i : ℝ))
      (restrictedDesired (fun k => (players k).desired) st.bundle) alloc =
      ∑ i ∈ optW, (st.val i : ℝ) := by
    simp only [welfareOn, optW, Finset.sum_filter]
  rw [hopt_sum]
  set m := Fintype.card M
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm_pos
  set rest := optW \ (acc.mSet ∪ acc.gSet ∪ acc.wSet)
  set bigSet := rest.filter fun i => Nat.sqrt m < (alloc i).card
  set smallSet := rest.filter fun i => (alloc i).card ≤ Nat.sqrt m
  -- Cover `optW` by the 5 sets: `mSet`, `gSet`, `wSet`, `bigSet`, `smallSet`.
  have hcover : optW ⊆ (optW ∩ acc.mSet) ∪ (optW ∩ acc.gSet) ∪ (optW ∩ acc.wSet) ∪
      bigSet ∪ smallSet := by
    intro i hi
    by_cases hM : i ∈ acc.mSet
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hi, hM⟩))))
    · by_cases hG : i ∈ acc.gSet
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hi, hG⟩))))
      · by_cases hW : i ∈ acc.wSet
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hi, hW⟩)))
        · have hrest : i ∈ rest := by
            simp only [rest, Finset.mem_sdiff, Finset.mem_union, not_or]
            exact ⟨hi, ⟨⟨hM, hG⟩, hW⟩⟩
          by_cases hcard : (alloc i).card ≤ Nat.sqrt m
          · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hrest, hcard⟩)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.2 ⟨hrest, Nat.lt_of_not_ge hcard⟩))
  -- Bounds on the first three sets (`M_j`, `GREEDY_j`, `W_j`).
  have hsum_M : ∑ i ∈ optW ∩ acc.mSet, (st.val i : ℝ) ≤ sumBest :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      fun _ _ _ => Nat.cast_nonneg _).trans hgeM_R
  have hsum_G : ∑ i ∈ optW ∩ acc.gSet, (st.val i : ℝ) ≤ sumBest :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      fun _ _ _ => Nat.cast_nonneg _).trans hgeG_R
  have hsum_W : ∑ i ∈ optW ∩ acc.wSet, (st.val i : ℝ) ≤ sumBest :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      fun _ _ _ => Nat.cast_nonneg _).trans hgeW_R
  -- Bound on `bigSet`: each bundle has size `> √m`, so at most `√m` such players exist, each
  -- `≤ v_{iMax}`.
  have hsum_big : ∑ i ∈ bigSet, (st.val i : ℝ) ≤ Real.sqrt (m : ℝ) * sumBest := by
    have hcard_le : (bigSet.card : ℝ) ≤ Real.sqrt (m : ℝ) := by
      have hmul : (bigSet.card : ℝ) * Real.sqrt (m : ℝ) ≤
          Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) := by
        have h1 : (bigSet.card : ℝ) * Real.sqrt (m : ℝ) ≤ ∑ i ∈ bigSet, ((alloc i).card : ℝ) := by
          calc (bigSet.card : ℝ) * Real.sqrt (m : ℝ)
            _ = ∑ _i ∈ bigSet, Real.sqrt (m : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ i ∈ bigSet, ((alloc i).card : ℝ) := by
                refine Finset.sum_le_sum fun i hi => ?_
                have hgt : Nat.sqrt m < (alloc i).card := (Finset.mem_filter.1 hi).2
                have hnotle : ¬ ((alloc i).card : ℝ) ≤ Real.sqrt (m : ℝ) := by
                  rw [← card_le_natSqrt_iff]; omega
                exact le_of_not_ge hnotle
        have h2 : (∑ i ∈ bigSet, (alloc i).card) ≤ m := by
          rw [← Finset.card_biUnion (fun a _ b _ hne => hfeas hne)]
          exact Finset.card_le_univ _
        have h2R : ∑ i ∈ bigSet, ((alloc i).card : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2
        rw [Real.mul_self_sqrt hm_pos.le]
        exact h1.trans h2R
      exact le_of_mul_le_mul_right hmul hsqrt_pos
    have hval_le_best : ∀ i ∈ bigSet, (st.val i : ℝ) ≤ sumBest := by
      intro i hi
      have hiret : i ∈ retiredAt P σ j :=
        (Finset.mem_filter.1 (Finset.mem_sdiff.1 (Finset.mem_filter.1 hi).1).1).1
      have hnotL : i ∉ st.losers := (Finset.mem_sdiff.1 hiret).2
      have hi_act : i ∈ Finset.univ.filter fun k => 0 < st.val k :=
        Finset.mem_filter.2 ⟨Finset.mem_univ i,
          Nat.pos_of_ne_zero (mt (mem_losers_iff_val_eq_zero P σ j i).2 hnotL)⟩
      have hle_iMax : (st.val i : ℝ) ≤ (st.val iMax : ℝ) := by exact_mod_cast hiMax_ge i hi_act
      have hiMax_le_M : (st.val iMax : ℝ) ≤ ∑ k ∈ acc.mSet, (st.val k : ℝ) :=
        Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) hfold.iMax_mem_m
      exact hle_iMax.trans (hiMax_le_M.trans hgeM_R)
    calc ∑ i ∈ bigSet, (st.val i : ℝ)
      _ ≤ ∑ _i ∈ bigSet, sumBest := Finset.sum_le_sum hval_le_best
      _ = (bigSet.card : ℝ) * sumBest := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.sqrt (m : ℝ) * sumBest := mul_le_mul_of_nonneg_right hcard_le hsumBest_nonneg
  -- Bound on `smallSet`: map each `i ∈ smallSet` to a higher-bid blocker `k ∈ acc.gSet`.
  have hmap_ex : ∀ i ∈ smallSet, ∃ k ∈ acc.gSet,
      ¬ Disjoint (alloc i) (acc.bundles k) ∧ st.val i ≤ st.val k := by
    intro i hi
    have hsmall : (alloc i).card ≤ Nat.sqrt m := (Finset.mem_filter.1 hi).2
    have hrest : i ∈ rest := (Finset.mem_filter.1 hi).1
    obtain ⟨hiOpt, hiNotMGW⟩ := Finset.mem_sdiff.1 hrest
    simp only [Finset.mem_union, not_or] at hiNotMGW
    obtain ⟨⟨hiNotM, hiNotG⟩, hiNotW⟩ := hiNotMGW
    obtain ⟨hiRet, hiDes, hiSub⟩ := Finset.mem_filter.1 hiOpt
    have hnotL : i ∉ st.losers := (Finset.mem_sdiff.1 hiRet).2
    have hi_pos : 0 < st.val i :=
      Nat.pos_of_ne_zero (mt (mem_losers_iff_val_eq_zero P σ j i).2 hnotL)
    obtain ⟨pre, suf, iMax', accBefore, _, _, _, hpre_ge, _, _, hinv_pre, hbi_eq, _,
      hW_sub, hM_sub, hG_sub, hW_step_sub, hM_step_sub, hG_step_sub, _, hbun_pre, _, _, _⟩ :=
      oneCaRunAcc_split_at σ cur.2 st (mem_losers_iff_val_eq_zero P σ j)
        (oneCaStateInv_of_run σ j) hnotT hi_pos
    set view : OneCaShrinkView N M :=
      ⟨cur.2, st, accBefore.wSet, accBefore.mSet, accBefore.gSet, accBefore.bundles⟩
    have hiNotW_st : i ∉ st.winners := fun h => hiNotW (hW_sub (hinv_pre.stW_sub_w h))
    have hiNotW0 : i ∉ accBefore.wSet := fun h => hiNotW (hW_sub h)
    have hiNotM0 : i ∉ accBefore.mSet := fun h => hiNotM (hM_sub h)
    have hiNotG0 : i ∉ accBefore.gSet := fun h => hiNotG (hG_sub h)
    -- Show `IsLoserIfSilent (players i) i view`.
    have hlis : IsLoserIfSilent (players i) i view := by
      refine ⟨(hinv_all i).2.2 j hiRet, hiNotW0, hiNotM0, hiNotG0, ?_⟩
      rintro ⟨hcard_st, hfree_or⟩
      set bNew := oneCaPickBundle σ cur.2 st accBefore i
      set sNext := Function.update accBefore.bundles i bNew
      have hb_sub : bNew ⊆ st.bundle i := by
        rw [← hbi_eq]
        simp only [bNew, oneCaPickBundle, hiNotW_st, ↓reduceIte]
        cases (σ i).shrink view with
        | none => exact Subset.rfl
        | some b =>
          dsimp only
          split_ifs with hval
          · exact hval.2.1.trans Finset.inter_subset_right
          · exact Subset.rfl
      have hb_card : bNew.card ≤ Nat.sqrt m := (Finset.card_le_card hb_sub).trans hcard_st
      have hfree_trans : ∀ S : Finset N, i ∉ S →
          st.bundle i ⊆ freeItems S accBefore.bundles → bNew ⊆ freeItems S sNext := by
        intro S hni hf
        rw [subset_freeItems_iff] at hf ⊢
        intro l hl
        have hli : l ≠ i := fun h => hni (h ▸ hl)
        dsimp only [sNext]
        rw [Function.update_of_ne hli]
        exact (hf l hl).mono_left hb_sub
      rcases hfree_or with hfW | hfM | hfG
      · have hmem : i ∈ (oneCaStep σ cur.2 st accBefore i).wSet := by
          rw [oneCaStep_wSet_eq]
          have hfw : bNew ⊆ freeItems accBefore.wSet sNext := hfree_trans _ hiNotW0 hfW
          change i ∈ if bNew.card ≤ Nat.sqrt m then
            if bNew ⊆ freeItems accBefore.wSet sNext then insert i accBefore.wSet
            else accBefore.wSet
            else accBefore.wSet
          simp only [hb_card, hfw, ↓reduceIte, Finset.mem_insert_self]
        exact hiNotW (hW_step_sub hmem)
      · have hmem : i ∈ (oneCaStep σ cur.2 st accBefore i).mSet := by
          rw [oneCaStep_mSet_eq]
          have hfm : bNew ⊆ freeItems accBefore.mSet sNext := hfree_trans _ hiNotM0 hfM
          change i ∈ if bNew.card ≤ Nat.sqrt m then
            if bNew ⊆ freeItems accBefore.mSet sNext then insert i accBefore.mSet
            else accBefore.mSet
            else accBefore.mSet
          simp only [hb_card, hfm, ↓reduceIte, Finset.mem_insert_self]
        exact hiNotM (hM_step_sub hmem)
      · have hmem : i ∈ (oneCaStep σ cur.2 st accBefore i).gSet := by
          rw [oneCaStep_gSet_eq]
          have hfg : bNew ⊆ freeItems accBefore.gSet sNext := hfree_trans _ hiNotG0 hfG
          change i ∈ if bNew.card ≤ Nat.sqrt m then
            if bNew ⊆ freeItems accBefore.gSet sNext then insert i accBefore.gSet
            else accBefore.gSet
            else accBefore.gSet
          simp only [hb_card, hfg, ↓reduceIte, Finset.mem_insert_self]
        exact hiNotG (hG_step_sub hmem)
    -- Therefore NO valid desired shrink exists for `i` at `view` (else `i` would enter `gSet`).
    have hno_valid : ¬ IsValidShrink accBefore.gSet accBefore.bundles (st.bundle i) (alloc i) := by
      intro hval_alloc
      obtain ⟨b, hsh, hval_b, _⟩ := (hσ i).2.1 view hlis ⟨alloc i, hval_alloc, hiDes⟩
      have hval_b' : IsValidShrink accBefore.gSet accBefore.bundles (st.bundle i) b := hval_b
      have hpick : oneCaPickBundle σ cur.2 st accBefore i = b := by
        simp only [oneCaPickBundle, hiNotW_st, ↓reduceIte, hbi_eq]
        change (match (σ i).shrink view with
          | some b' => if IsValidShrink accBefore.gSet accBefore.bundles (st.bundle i) b'
              then b' else st.bundle i
          | none => st.bundle i) = b
        simp only [hsh, hval_b', ↓reduceIte]
      have hfree_g : b ⊆ freeItems accBefore.gSet (Function.update accBefore.bundles i b) := by
        rw [subset_freeItems_iff]
        intro l hl
        have hli : l ≠ i := fun h => hiNotG0 (h ▸ hl)
        rw [Function.update_of_ne hli]
        exact (subset_freeItems_iff _ _ _).1 (hval_b'.2.1.trans Finset.inter_subset_left) l hl
      have hmemG : i ∈ (oneCaStep σ cur.2 st accBefore i).gSet := by
        rw [oneCaStep_gSet_eq]
        simp only [hpick, hval_b'.2.2, hfree_g, ↓reduceIte, Finset.mem_insert_self]
      exact hiNotG (hG_step_sub hmemG)
    -- Since `alloc i` is nonempty, `⊆ st.bundle i`, and `card ≤ √m`, it hits `accBefore.gSet`.
    have hnotFree : ¬ alloc i ⊆ freeItems accBefore.gSet accBefore.bundles := fun hf =>
      hno_valid ⟨(players i).nonempty_of_mem hiDes, Finset.subset_inter hf hiSub, hsmall⟩
    rw [subset_freeItems_iff] at hnotFree
    push Not at hnotFree
    obtain ⟨k, hkG0, hnd⟩ := hnotFree
    have hk_pre : k ∈ pre := List.mem_reverse.1 (hinv_pre.g_sub_visited k hkG0)
    refine ⟨k, hG_sub hkG0, ?_, hpre_ge k hk_pre⟩
    rwa [hbun_pre k hk_pre]
  have hsum_small : ∑ i ∈ smallSet, (st.val i : ℝ) ≤ Real.sqrt (m : ℝ) * sumBest := by
    let φ : N → N := fun i => if h : i ∈ smallSet then (hmap_ex i h).choose else i
    have hφ_maps : ∀ i ∈ smallSet, φ i ∈ acc.gSet := fun i hi => by
      simp only [φ, hi, ↓reduceDIte]
      exact (hmap_ex i hi).choose_spec.1
    rw [← Finset.sum_fiberwise_of_maps_to hφ_maps]
    calc ∑ k ∈ acc.gSet, ∑ i ∈ smallSet with φ i = k, (st.val i : ℝ)
      _ ≤ ∑ k ∈ acc.gSet, Real.sqrt (m : ℝ) * (st.val k : ℝ) := by
          refine Finset.sum_le_sum fun k hkG => ?_
          set fib := smallSet.filter fun i => φ i = k
          have hfib_val : ∀ i ∈ fib, (st.val i : ℝ) ≤ (st.val k : ℝ) := by
            intro i hi
            obtain ⟨hiS, hφi⟩ := Finset.mem_filter.1 hi
            have hspec := (hmap_ex i hiS).choose_spec
            have hkeq : (hmap_ex i hiS).choose = k := by
              simpa only [φ, hiS, ↓reduceDIte] using hφi
            exact_mod_cast (hkeq ▸ hspec.2.2)
          have hfib_card : fib.card ≤ (acc.bundles k).card := by
            -- Inject `fib` into `acc.bundles k` via a witness item in `alloc i ∩ acc.bundles k`.
            have hex_item : ∀ i ∈ fib, ∃ x ∈ acc.bundles k, x ∈ alloc i := by
              intro i hi
              obtain ⟨hiS, hφi⟩ := Finset.mem_filter.1 hi
              have hspec := (hmap_ex i hiS).choose_spec
              have hkeq : (hmap_ex i hiS).choose = k := by
                simpa only [φ, hiS, ↓reduceDIte] using hφi
              have hnd : ¬ Disjoint (alloc i) (acc.bundles k) := hkeq ▸ hspec.2.1
              rw [Finset.not_disjoint_iff] at hnd
              obtain ⟨x, hx1, hx2⟩ := hnd
              exact ⟨x, hx2, hx1⟩
            let witness : N → M := fun i =>
              if h : i ∈ fib then (hex_item i h).choose else Classical.arbitrary M
            refine Finset.card_le_card_of_injOn witness
              (fun i hi => by
                have hi' : i ∈ fib := Finset.mem_coe.1 hi
                simp only [witness, hi', ↓reduceDIte]
                exact (hex_item i hi').choose_spec.1)
              (fun i₁ h1 i₂ h2 hweq => ?_)
            by_contra hne
            have h1' : i₁ ∈ fib := Finset.mem_coe.1 h1
            have h2' : i₂ ∈ fib := Finset.mem_coe.1 h2
            have hx1 : witness i₁ ∈ alloc i₁ := by
              simp only [witness, h1', ↓reduceDIte]
              exact (hex_item i₁ h1').choose_spec.2
            have hx2 : witness i₂ ∈ alloc i₂ := by
              simp only [witness, h2', ↓reduceDIte]
              exact (hex_item i₂ h2').choose_spec.2
            exact Finset.disjoint_left.1 (hfeas hne) hx1 (hweq ▸ hx2)
          have hfib_le_sqrt : (fib.card : ℝ) ≤ Real.sqrt (m : ℝ) := by
            rw [← card_le_natSqrt_iff]
            exact hfib_card.trans (hfold.g_small k hkG)
          calc ∑ i ∈ fib, (st.val i : ℝ)
            _ ≤ ∑ _i ∈ fib, (st.val k : ℝ) := Finset.sum_le_sum hfib_val
            _ = (fib.card : ℝ) * (st.val k : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul]
            _ ≤ Real.sqrt (m : ℝ) * (st.val k : ℝ) :=
                mul_le_mul_of_nonneg_right hfib_le_sqrt (Nat.cast_nonneg _)
      _ = Real.sqrt (m : ℝ) * ∑ k ∈ acc.gSet, (st.val k : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ Real.sqrt (m : ℝ) * sumBest := mul_le_mul_of_nonneg_left hgeG_R hsqrt_pos.le
  -- Sum the 5 bounds.
  have htotal : ∑ i ∈ optW, (st.val i : ℝ) ≤
      (∑ i ∈ optW ∩ acc.mSet, (st.val i : ℝ)) +
      (∑ i ∈ optW ∩ acc.gSet, (st.val i : ℝ)) +
      (∑ i ∈ optW ∩ acc.wSet, (st.val i : ℝ)) +
      (∑ i ∈ bigSet, (st.val i : ℝ)) +
      (∑ i ∈ smallSet, (st.val i : ℝ)) := by
    have hnn : ∀ i, 0 ≤ (st.val i : ℝ) := fun _ => Nat.cast_nonneg _
    calc ∑ i ∈ optW, (st.val i : ℝ)
      _ ≤ ∑ i ∈ (optW ∩ acc.mSet) ∪ (optW ∩ acc.gSet) ∪ (optW ∩ acc.wSet) ∪
            bigSet ∪ smallSet, (st.val i : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun i _ _ => hnn i
      _ ≤ (∑ i ∈ (optW ∩ acc.mSet) ∪ (optW ∩ acc.gSet) ∪ (optW ∩ acc.wSet) ∪ bigSet,
            (st.val i : ℝ)) + ∑ i ∈ smallSet, (st.val i : ℝ) :=
          sum_union_le fun i _ => hnn i
      _ ≤ ((∑ i ∈ (optW ∩ acc.mSet) ∪ (optW ∩ acc.gSet) ∪ (optW ∩ acc.wSet), (st.val i : ℝ)) +
            ∑ i ∈ bigSet, (st.val i : ℝ)) + ∑ i ∈ smallSet, (st.val i : ℝ) :=
          add_le_add (sum_union_le fun i _ => hnn i) le_rfl
      _ ≤ (((∑ i ∈ (optW ∩ acc.mSet) ∪ (optW ∩ acc.gSet), (st.val i : ℝ)) +
            ∑ i ∈ optW ∩ acc.wSet, (st.val i : ℝ)) +
            ∑ i ∈ bigSet, (st.val i : ℝ)) + ∑ i ∈ smallSet, (st.val i : ℝ) :=
          add_le_add (add_le_add (sum_union_le fun i _ => hnn i) le_rfl) le_rfl
      _ ≤ (∑ i ∈ optW ∩ acc.mSet, (st.val i : ℝ)) +
            (∑ i ∈ optW ∩ acc.gSet, (st.val i : ℝ)) +
            (∑ i ∈ optW ∩ acc.wSet, (st.val i : ℝ)) +
            (∑ i ∈ bigSet, (st.val i : ℝ)) +
            (∑ i ∈ smallSet, (st.val i : ℝ)) :=
          add_le_add (add_le_add (add_le_add (sum_union_le fun i _ => hnn i) le_rfl) le_rfl) le_rfl
  linarith

/-! #### Claim 12.50, Lemma 12.49, and Theorem 12.51 -/

omit [DecidableEq M] in
/-- **Claim 12.50** ([Lavi2007], §12.5, p. 326): for any proper procedure starting from
`s_i^0 = Finset.univ` and satisfying first-time shrink, the optimal unrestricted welfare of the
losing players who shrank their bundle (`P = {i ∈ L_J | |s_i^J| < m}`) is at most `J * OPT(R̄)`. -/
theorem WrapperProc.optWelfare_shrunkLosers_le {P : WrapperProc N M Strat}
    {players : N → SingleValuePlayer M} {σ : N → Strat}
    (hinit : P.initBundle = fun _ => Finset.univ)
    (hproper : P.IsProperOn σ) (hfts : P.HasFirstTimeShrinkOn σ)
    (hdes : ∀ i, (wrapperState P σ (termRound P σ)).bundle i ∈ (players i).desired) :
    let J := termRound P σ
    let Pset := (wrapperState P σ J).losers.filter fun i =>
      ((wrapperState P σ J).bundle i).card < Fintype.card M
    optWelfareOn Pset (fun i => (players i).value) (fun i => (players i).desired) ≤
      (J : ℝ) * optWelfareOn (wrapperState P σ J).losers (fun i => (players i).value)
        (rBarDesired P σ players) := by
  classical
  set J := termRound P σ
  set L_J := (wrapperState P σ J).losers
  set Pset := L_J.filter fun i => ((wrapperState P σ J).bundle i).card < Fintype.card M
  let Pj : ℕ → Finset N := fun j => Pset.filter fun i =>
    ((wrapperState P σ j).bundle i).card = Fintype.card M ∧
    ((wrapperState P σ (j + 1)).bundle i).card < Fintype.card M
  have hcover : Pset ⊆ (Finset.range J).biUnion Pj := by
    intro i hi
    have hltJ : ((wrapperState P σ J).bundle i).card < Fintype.card M := (Finset.mem_filter.1 hi).2
    have hex : ∃ t, ((wrapperState P σ t).bundle i).card < Fintype.card M := ⟨J, hltJ⟩
    set k := Nat.find hex
    have hk_lt : ((wrapperState P σ k).bundle i).card < Fintype.card M := Nat.find_spec hex
    have hk_le : k ≤ J := Nat.find_min' hex hltJ
    have hk_pos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos h0
      rw [hk0, wrapperState_zero, initState, hinit, Finset.card_univ] at hk_lt
      exact lt_irrefl _ hk_lt
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
    have hj_not_lt : ¬ ((wrapperState P σ j).bundle i).card < Fintype.card M :=
      Nat.find_min hex (by omega : j < k)
    have hj_eq : ((wrapperState P σ j).bundle i).card = Fintype.card M :=
      le_antisymm (Finset.card_le_univ _) (le_of_not_gt hj_not_lt)
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 (by omega),
      Finset.mem_filter.2 ⟨hi, hj_eq, by rwa [← Nat.succ_eq_add_one, ← hj]⟩⟩
  have hper_j : ∀ j ∈ Finset.range J,
      optWelfareOn (Pj j) (fun i => (players i).value) (fun i => (players i).desired) ≤
        optWelfareOn L_J (fun i => (players i).value) (rBarDesired P σ players) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hnotT : ¬ TerminatedAt P σ j := not_terminatedAt_of_lt_termRound hj
    let alloc : N → Finset M := fun i => if i ∈ Pj j then (wrapperState P σ J).bundle i else ∅
    have hfeas : IsFeasibleAlloc alloc := by
      intro i₁ i₂ hne
      simp only [alloc]
      split_ifs with h1 h2
      · obtain ⟨_, h1eq, h1lt⟩ := Finset.mem_filter.1 h1
        obtain ⟨_, h2eq, h2lt⟩ := Finset.mem_filter.1 h2
        have hdisj_j1 := hfts j hnotT hne h1eq h1lt h2eq h2lt
        exact hdisj_j1.mono (bundle_subset_of_isProperOn hproper (Nat.succ_le_of_lt hj) i₁)
          (bundle_subset_of_isProperOn hproper (Nat.succ_le_of_lt hj) i₂)
      · exact Finset.disjoint_empty_right _
      · exact Finset.disjoint_empty_left _
      · exact Finset.disjoint_empty_left _
    have hsum_le : ∑ i ∈ Pj j, (players i).value ≤
        welfareOn L_J (fun i => (players i).value) (rBarDesired P σ players) alloc := by
      have hsubL : Pj j ⊆ L_J := fun i hi =>
        (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).1
      calc ∑ i ∈ Pj j, (players i).value
        _ = ∑ i ∈ Pj j, if alloc i ∈ rBarDesired P σ players i then (players i).value else 0 := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hmemR : alloc i ∈ rBarDesired P σ players i := by
              simp only [alloc, hi, ↓reduceIte, rBarDesired, restrictedDesired]
              have hret_lt : retireRound P σ i < J := (mem_retiredAt_retireRound (hsubL hi)).1
              exact ⟨hdes i, bundle_subset_of_isProperOn hproper hret_lt.le i⟩
            simp only [hmemR, ↓reduceIte]
        _ ≤ welfareOn L_J (fun i => (players i).value) (rBarDesired P σ players) alloc := by
            simp only [welfareOn]
            refine Finset.sum_le_sum_of_subset_of_nonneg hsubL fun i _ _ => ?_
            split_ifs
            · exact (players i).value_pos.le
            · exact le_rfl
    exact (optWelfareOn_le_sum fun i _ => (players i).value_pos.le).trans
      (hsum_le.trans (welfareOn_le_optWelfareOn _ _ _ hfeas))
  calc optWelfareOn Pset (fun i => (players i).value) (fun i => (players i).desired)
    _ ≤ optWelfareOn ((Finset.range J).biUnion Pj) (fun i => (players i).value)
          (fun i => (players i).desired) :=
        optWelfareOn_subset_le hcover fun i _ => (players i).value_pos.le
    _ ≤ ∑ j ∈ Finset.range J, optWelfareOn (Pj j) (fun i => (players i).value)
          (fun i => (players i).desired) :=
        optWelfareOn_biUnion_le _ _ fun _ _ i _ => (players i).value_pos.le
    _ ≤ ∑ _j ∈ Finset.range J,
          optWelfareOn L_J (fun i => (players i).value) (rBarDesired P σ players) :=
        Finset.sum_le_sum hper_j
    _ = (J : ℝ) * optWelfareOn L_J (fun i => (players i).value) (rBarDesired P σ players) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [DecidableEq M] in
/-- **Lemma 12.49** ([Lavi2007], §12.5, pp. 326–327): given any `c`-local-approximation
starting from `s_i^0 = Finset.univ` that satisfies first-time shrink, every strategy profile in `D`
obtains an explicit `(1 + 2 * (2 ⌊log₂ v_max⌋ + 1) * (2 ⌊log₂ v_max⌋ + 2) * c)`-approximation
(`O(log²(v_max) * c)`) to optimal social welfare. -/
theorem WrapperProc.optWelfare_le_of_firstTimeShrink
    {P : WrapperProc N M Strat} {players : N → SingleValuePlayer M} {D : N → Set Strat}
    {c v_max : ℝ} {σ : N → Strat}
    (hinit : P.initBundle = fun _ => Finset.univ)
    (hloc : P.IsLocalApproxOn players D c) (hc : 0 ≤ c)
    (hfts : P.HasFirstTimeShrinkOn σ)
    (hval_le : ∀ i, (players i).value ≤ v_max)
    (hσ : ∀ i, σ i ∈ D i) :
    Terminates P σ ∧ IsFeasibleAlloc (P.alloc σ) ∧
    optWelfare players ≤
      (1 + 2 * (2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 1) * (2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 2) * c) *
        P.socialWelfare σ players := by
  obtain ⟨hproper, _, _, hdes, _, _⟩ := hloc σ hσ
  obtain ⟨hT, hJle, hrBar_J, _⟩ := P.optWelfare_rBar_le hloc hc hval_le hσ
  set J := termRound P σ
  set W_J := (wrapperState P σ J).winners
  set L_J := (wrapperState P σ J).losers
  set Pset := L_J.filter fun i => ((wrapperState P σ J).bundle i).card < Fintype.card M
  set Uset := L_J.filter fun i => ¬ ((wrapperState P σ J).bundle i).card < Fintype.card M
  have hSW : P.socialWelfare σ players = ∑ i ∈ W_J, (players i).value :=
    socialWelfare_eq_sum_winners hT fun i _ => hdes J i
  have hSW_nonneg : 0 ≤ P.socialWelfare σ players := by
    rw [hSW]; exact Finset.sum_nonneg fun i _ => (players i).value_pos.le
  -- Unshrunk losers `Uset` still had `s_i^{r_i} = Finset.univ`, so `OPT(Uset) ≤ OPT(R̄)`.
  have hU_le_rBar : optWelfareOn Uset (fun i => (players i).value) (fun i => (players i).desired) ≤
      optWelfareOn L_J (fun i => (players i).value) (rBarDesired P σ players) := by
    have hdes_eq : ∀ i ∈ Uset, (players i).desired ⊆ rBarDesired P σ players i := by
      intro i hi b hb
      obtain ⟨hiL, hnotlt⟩ := Finset.mem_filter.1 hi
      have hcardJ : ((wrapperState P σ J).bundle i).card = Fintype.card M :=
        le_antisymm (Finset.card_le_univ _) (le_of_not_gt hnotlt)
      have hunivJ : (wrapperState P σ J).bundle i = Finset.univ :=
        Finset.eq_univ_of_card _ hcardJ
      have hret_lt : retireRound P σ i < J := (mem_retiredAt_retireRound hiL).1
      have huniv_r : (wrapperState P σ (retireRound P σ i)).bundle i = Finset.univ :=
        Finset.eq_univ_iff_forall.2 fun x =>
          bundle_subset_of_isProperOn hproper hret_lt.le i (hunivJ ▸ Finset.mem_univ x)
      exact ⟨hb, by rw [huniv_r]; exact Finset.subset_univ b⟩
    exact (optWelfareOn_mono_des (fun i _ => (players i).value_pos.le) hdes_eq).trans
      (optWelfareOn_subset_le (Finset.filter_subset _ _) fun i _ => (players i).value_pos.le)
  have hP_le : optWelfareOn Pset (fun i => (players i).value) (fun i => (players i).desired) ≤
      (J : ℝ) * optWelfareOn L_J (fun i => (players i).value) (rBarDesired P σ players) :=
    P.optWelfare_shrunkLosers_le hinit hproper hfts (hdes J)
  have hW_le : optWelfareOn W_J (fun i => (players i).value) (fun i => (players i).desired) ≤
      P.socialWelfare σ players := by
    rw [hSW]; exact optWelfareOn_le_sum fun i _ => (players i).value_pos.le
  have hL_split : L_J = Pset ∪ Uset := by
    ext i
    simp only [Pset, Uset, Finset.mem_union, Finset.mem_filter]
    by_cases hlt : ((wrapperState P σ J).bundle i).card < Fintype.card M
    · simp only [hlt, not_true_eq_false, and_true, and_false, or_false]
    · simp only [hlt, not_false_eq_true, and_false, and_true, false_or]
  have huniv : Finset.univ = W_J ∪ (Pset ∪ Uset) := by
    rw [← hL_split]
    exact (termRound_spec hT).symm
  have hopt_bound_J : optWelfare players ≤
      (1 + 2 * (J : ℝ) * ((J : ℝ) + 1) * c) * P.socialWelfare σ players := by
    have h1 : optWelfare players ≤
        optWelfareOn W_J (fun i => (players i).value) (fun i => (players i).desired) +
        (optWelfareOn Pset (fun i => (players i).value) (fun i => (players i).desired) +
         optWelfareOn Uset (fun i => (players i).value) (fun i => (players i).desired)) := by
      simp only [optWelfare]
      rw [huniv]
      exact (optWelfareOn_union_le fun i _ => (players i).value_pos.le).trans
        (add_le_add le_rfl (optWelfareOn_union_le fun i _ => (players i).value_pos.le))
    have h2 : optWelfareOn Pset (fun i => (players i).value) (fun i => (players i).desired) +
        optWelfareOn Uset (fun i => (players i).value) (fun i => (players i).desired) ≤
        ((J : ℝ) + 1) * optWelfareOn L_J (fun i => (players i).value)
          (rBarDesired P σ players) := by linarith
    have h3 : ((J : ℝ) + 1) * optWelfareOn L_J (fun i => (players i).value)
        (rBarDesired P σ players) ≤
        ((J : ℝ) + 1) * (2 * (J : ℝ) * c * P.socialWelfare σ players) :=
      mul_le_mul_of_nonneg_left hrBar_J (by positivity)
    linarith
  have hJleR : (J : ℝ) ≤ 2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 1 := by exact_mod_cast hJle
  have hJJ : (J : ℝ) * ((J : ℝ) + 1) ≤
      (2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 1) * (2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 2) := by
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    nlinarith
  have hcSW : 0 ≤ c * P.socialWelfare σ players := mul_nonneg hc hSW_nonneg
  refine ⟨hT, P.isFeasibleAlloc_of_isProperOn hproper, hopt_bound_J.trans ?_⟩
  nlinarith

/-- **Theorem 12.51** ([Lavi2007], §12.5, p. 327; note the printed text writes `c` where `√m`
is intended from Lemma 12.47): `Wrapper + 1-CA-PROC` is a game-theoretic implementation in
undominated strategies (`oneCaStrategyClass`) achieving an explicit
`O(log²(v_max) * √m)`-approximation to optimal social welfare for single-value players with
`1 ≤ v̄ᵢ ≤ v_max`. -/
theorem oneCaProc_isUndominatedImpl [Nonempty M] (players : N → SingleValuePlayer M)
    {v_max : ℝ} (hval_le : ∀ i, (players i).value ≤ v_max) :
    (oneCaProc (N := N) (M := M)).IsUndominatedImpl players
      (fun i => oneCaStrategyClass (players i) i)
      (1 + 2 * (2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 1) * (2 * (Nat.log 2 ⌊v_max⌋₊ : ℝ) + 2) *
        (3 + 2 * Real.sqrt (Fintype.card M))) := by
  refine ⟨fun σ hσ => ?_, fun i st => ⟨dominateOneCaStrategy (players i) i st,
    dominateOneCaStrategy_mem (players i) i st,
    dominateOneCaStrategy_weaklyDominates (players i) i st⟩⟩
  exact (oneCaProc (N := N) (M := M)).optWelfare_le_of_firstTimeShrink
    rfl (oneCaProc_isLocalApproxOn players) (by positivity)
    (oneCaProc_hasFirstTimeShrinkOn σ) hval_le hσ

end OneCaProc

end Cslib.GameTheory.Mechanism.Wrapper

