/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.RandomAssignment.Basic

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Probabilistic Serial (PS) / Simultaneous Eating Algorithm

Formalizes the **Probabilistic Serial (PS)** random assignment rule (`probabilisticSerial`) of
Bogomolnaia and Moulin ([BogomolnaiaMoulin2001]; note: the primary article PDF has not been
consulted locally, so theorem/lemma/page numbers are unverified).

Each of the `n` indivisible objects is treated as a unit-capacity divisible good (`rem o = 1`
initially). Over the unit time interval `[0, 1]`, at each discrete event round while some object
remains positive (`0 < rem o`), every agent `i` eats her favorite remaining object at unit rate
`1`. The round ends after duration `Δ = min {rem o / demand o | demand o > 0}`, at which point
at least one currently eaten object reaches `rem o = 0`. Iterating `n` rounds finishes every
object simultaneously at elapsed time `t = 1`.

## Main definitions

* `Cslib.GameTheory.RandomAssignment.EatingState`: discrete-event state recording remaining object
  masses `rem`, accumulated allocation matrix `alloc`, elapsed time `elapsed`, and recorded
  exhaustion times `exhaustTime`.
* `Cslib.GameTheory.RandomAssignment.eatingStep`: one discrete eating phase of duration `Δ`.
* `Cslib.GameTheory.RandomAssignment.probabilisticSerial`: the `PS` random assignment rule
  obtained by iterating `eatingStep` `n` times from the uniform initial state.

## Main results

* `Cslib.GameTheory.RandomAssignment.probabilisticSerial_mem_doublyStochastic`: `PS` always
  returns a doubly stochastic matrix.
* `Cslib.GameTheory.RandomAssignment.probabilisticSerial_isSDEnvyFree`: `PS` is
  `sd`-envy-free (every round adds `Δ` of `i`'s best available object, beating `j`'s choice).
* `Cslib.GameTheory.RandomAssignment.probabilisticSerial_isEqualTreatmentOfEquals`: `PS` satisfies
  equal treatment of equals (`ETE`).
* `Cslib.GameTheory.RandomAssignment.probabilisticSerial_isSDEfficient`: `PS` is `sd`-efficient
  (proved via the strict monotonicity of object exhaustion times along the trade relation).
* `Cslib.GameTheory.RandomAssignment.probabilisticSerial_isExPostEfficient`: `PS` is ex-post
  efficient.
* `Cslib.GameTheory.RandomAssignment.not_isSDStrategyProof_probabilisticSerial`: for every
  `n ≥ 3`, `PS` is **not** strongly `sd`-strategy-proof (on `(a b c …, a c b …, b a c …)` padded
  with dummy agents `k ≥ 3`, agent `2` receives `(0, 3/4, 1/4)` truthfully vs `(1/3, 1/2, 1/6)` by
  reporting `a b c …`, raising mass on `{b, a}` from `3/4` to `5/6`).

## References

* [BogomolnaiaMoulin2001] (primary article PDF not consulted; section/theorem locators
  unverified).
-/

public section

namespace Cslib.GameTheory.RandomAssignment

open Finset Matrix

/-- Discrete-event state of the simultaneous eating algorithm for `n` agents and `n` objects. -/
structure EatingState (n : ℕ) where
  /-- Remaining probability supply of each object (initially `1`, decreasing to `0`). -/
  rem : Fin n → ℝ
  /-- Probability matrix accumulated so far (`alloc i o` = mass of object `o` eaten by `i`). -/
  alloc : Matrix (Fin n) (Fin n) ℝ
  /-- Total elapsed eating time in `[0, 1]`. -/
  elapsed : ℝ
  /-- Time at which each exhausted object reached `rem o = 0` (meaningful once `rem o = 0`). -/
  exhaustTime : Fin n → ℝ

/-- Initial state before eating begins: every object has unit supply `1`, zero matrix `alloc`,
and elapsed time `0`. -/
@[expose] def initEatingState (n : ℕ) : EatingState n where
  rem := fun _ => 1
  alloc := 0
  elapsed := 0
  exhaustTime := fun _ => 0

/-- Helper returning the finite set of ranks whose objects still have strictly positive mass. -/
private noncomputable def activeRanks {n : ℕ} (π : Equiv.Perm (Fin n)) (rem : Fin n → ℝ) :
    Finset (Fin n) :=
  @Finset.filter (Fin n) (fun r => 0 < rem (π r)) (Classical.decPred _) Finset.univ

private lemma mem_activeRanks {n : ℕ} (π : Equiv.Perm (Fin n)) (rem : Fin n → ℝ) (r : Fin n) :
    r ∈ activeRanks π rem ↔ 0 < rem (π r) := by
  simp [activeRanks]

private lemma activeRanks_nonempty {n : ℕ} (π : Equiv.Perm (Fin n)) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) : (activeRanks π rem).Nonempty := by
  obtain ⟨o, ho⟩ := h
  exact ⟨π.symm o, (mem_activeRanks π rem _).mpr (by simpa using ho)⟩

/-- Agent `i`'s top remaining object (minimum rank `r` with `0 < rem (p i r)`). -/
private noncomputable def favObject {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (i : Fin n) : Fin n :=
  p i ((activeRanks (p i) rem).min' (activeRanks_nonempty (p i) rem h))

private lemma favObject_rem_pos {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (i : Fin n) : 0 < rem (favObject p rem h i) :=
  (mem_activeRanks (p i) rem _).mp (Finset.min'_mem _ _)

private lemma favObject_rank_le {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (i o : Fin n) (ho : 0 < rem o) :
    (p i).symm (favObject p rem h i) ≤ (p i).symm o := by
  unfold favObject
  rw [Equiv.symm_apply_apply]
  exact Finset.min'_le _ ((p i).symm o) ((mem_activeRanks (p i) rem _).mpr (by simpa using ho))

private lemma favObject_lt_le_zero {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (i a : Fin n)
    (hlt : (p i).symm a < (p i).symm (favObject p rem h i)) : rem a ≤ 0 := by
  by_contra! hpos
  exact hlt.not_ge (favObject_rank_le p rem h i a hpos)

/-- Number of agents simultaneously eating object `o` in the current phase. -/
private noncomputable def eatingDemand {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (o : Fin n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => favObject p rem h i = o).card

private lemma demanded_nonempty {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) :
    (Finset.univ.filter fun o : Fin n => 0 < eatingDemand p rem h o).Nonempty := by
  rcases h with ⟨o₀, ho₀⟩
  refine ⟨favObject p rem ⟨o₀, ho₀⟩ o₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact Finset.card_pos.mpr ⟨o₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- Duration `Δ = min {rem o / demand o | demand o > 0}` of the current eating phase. -/
private noncomputable def eatingDuration {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) : ℝ :=
  (Finset.univ.filter fun o : Fin n => 0 < eatingDemand p rem h o).inf'
    (demanded_nonempty p rem h)
    fun o => rem o / (eatingDemand p rem h o : ℝ)

private lemma exists_exhausted_of_eatingDuration {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) :
    ∃ o : Fin n, 0 < rem o ∧
      rem o - (eatingDemand p rem h o : ℝ) * eatingDuration p rem h = 0 := by
  obtain ⟨o, ho, heq⟩ := Finset.exists_mem_eq_inf' (demanded_nonempty p rem h)
    (fun o => rem o / (eatingDemand p rem h o : ℝ))
  have hd_pos : 0 < eatingDemand p rem h o := (Finset.mem_filter.mp ho).2
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hd_pos
  refine ⟨o, (Finset.mem_filter.mp hi).2 ▸ favObject_rem_pos p rem h i, ?_⟩
  rw [eatingDuration, heq, mul_div_cancel₀ _ (Nat.cast_pos.mpr hd_pos).ne', sub_self]

private lemma eatingDuration_pos {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) : 0 < eatingDuration p rem h := by
  obtain ⟨o, ho, h0⟩ := exists_exhausted_of_eatingDuration p rem h
  exact pos_of_mul_pos_right (by linarith) (Nat.cast_nonneg (eatingDemand p rem h o))

private lemma eatingDuration_le {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (o : Fin n) (hd : 0 < eatingDemand p rem h o) :
    (eatingDemand p rem h o : ℝ) * eatingDuration p rem h ≤ rem o :=
  (le_div_iff₀' (Nat.cast_pos.mpr hd)).mp (Finset.inf'_le _ (by simpa using hd))

/-- One discrete phase of the simultaneous eating algorithm. If no object has strictly positive
remaining mass, the state is left unchanged. -/
noncomputable def eatingStep {n : ℕ} (p : Profile n) (s : EatingState n) : EatingState n :=
  @dite (EatingState n) (∃ o : Fin n, 0 < s.rem o) (Classical.propDecidable _)
    (fun h =>
      let dt := eatingDuration p s.rem h
      let rem' : Fin n → ℝ := fun o => s.rem o - (eatingDemand p s.rem h o : ℝ) * dt
      { rem := rem'
        alloc := Matrix.of fun i o =>
          s.alloc i o + if favObject p s.rem h i = o then dt else 0
        elapsed := s.elapsed + dt
        exhaustTime := fun o =>
          @ite ℝ (0 < s.rem o ∧ rem' o = 0) (Classical.propDecidable _)
            (s.elapsed + dt) (s.exhaustTime o) })
    (fun _ => s)

private lemma eatingStep_pos_rem {n : ℕ} (p : Profile n) (s : EatingState n)
    (h : ∃ o : Fin n, 0 < s.rem o) (o : Fin n) :
    (eatingStep p s).rem o =
      s.rem o - (eatingDemand p s.rem h o : ℝ) * eatingDuration p s.rem h :=
  congrFun (congrArg EatingState.rem (dite_eq_left h)) o

private lemma eatingStep_pos_alloc {n : ℕ} (p : Profile n) (s : EatingState n)
    (h : ∃ o : Fin n, 0 < s.rem o) (i o : Fin n) :
    (eatingStep p s).alloc i o =
      s.alloc i o + if favObject p s.rem h i = o then eatingDuration p s.rem h else 0 :=
  congrFun (congrFun (congrArg EatingState.alloc (dite_eq_left h)) i) o

private lemma eatingStep_pos_elapsed {n : ℕ} (p : Profile n) (s : EatingState n)
    (h : ∃ o : Fin n, 0 < s.rem o) :
    (eatingStep p s).elapsed = s.elapsed + eatingDuration p s.rem h :=
  congrArg EatingState.elapsed (dite_eq_left h)

private lemma eatingStep_pos_exhaust {n : ℕ} (p : Profile n) (s : EatingState n)
    (h : ∃ o : Fin n, 0 < s.rem o) (o : Fin n) :
    (eatingStep p s).exhaustTime o =
      @ite ℝ (0 < s.rem o ∧
          s.rem o - (eatingDemand p s.rem h o : ℝ) * eatingDuration p s.rem h = 0)
        (Classical.propDecidable _)
        (s.elapsed + eatingDuration p s.rem h) (s.exhaustTime o) :=
  congrFun (congrArg EatingState.exhaustTime (dite_eq_left h)) o

/-- **Probabilistic Serial (PS)** random assignment rule ([BogomolnaiaMoulin2001], locator
unverified): run `eatingStep` for `n` discrete event rounds from `initEatingState n`. -/
noncomputable def probabilisticSerial {n : ℕ} : AssignmentRule n := fun p =>
  ((eatingStep p)^[n] (initEatingState n)).alloc

/-- Loop invariant preserved by every `eatingStep p`. -/
private structure EatingInv {n : ℕ} (p : Profile n) (s : EatingState n) : Prop where
  rem_nonneg : ∀ o : Fin n, 0 ≤ s.rem o
  alloc_nonneg : ∀ i o : Fin n, 0 ≤ s.alloc i o
  row_sum : ∀ i : Fin n, ∑ o : Fin n, s.alloc i o = s.elapsed
  col_sum : ∀ o : Fin n, s.rem o + ∑ i : Fin n, s.alloc i o = 1
  elapsed_nonneg : 0 ≤ s.elapsed
  envyFree : IsSDEnvyFree p s.alloc
  exhaust_le : ∀ o : Fin n, s.rem o = 0 → s.exhaustTime o ≤ s.elapsed
  trade_order : ∀ i a b : Fin n, 0 < s.alloc i b → (p i).symm a < (p i).symm b →
    s.rem a = 0 ∧ (s.rem b = 0 → s.exhaustTime a < s.exhaustTime b)

private lemma eatingInv_init {n : ℕ} (p : Profile n) : EatingInv p (initEatingState n) where
  rem_nonneg _ := zero_le_one
  alloc_nonneg _ _ := le_rfl
  row_sum _ := by simp [initEatingState]
  col_sum _ := by simp [initEatingState]
  elapsed_nonneg := le_rfl
  envyFree _ _ := SDDominates.refl _ _
  exhaust_le _ h := by simp [initEatingState] at h
  trade_order _ _ _ h := by simp [initEatingState] at h

private lemma eatingInv_step {n : ℕ} (p : Profile n) {s : EatingState n} (hinv : EatingInv p s) :
    EatingInv p (eatingStep p s) := by
  by_cases h : ∃ o : Fin n, 0 < s.rem o
  swap
  · rwa [eatingStep, dite_eq_right h]
  set dt := eatingDuration p s.rem h
  have hdt_pos : 0 < dt := eatingDuration_pos p s.rem h
  have hrem_eq := eatingStep_pos_rem p s h
  have halloc_eq := eatingStep_pos_alloc p s h
  have hel_eq := eatingStep_pos_elapsed p s h
  have hexh_eq := eatingStep_pos_exhaust p s h
  have hrem_zero_of_zero (o : Fin n) (ho : s.rem o = 0) : (eatingStep p s).rem o = 0 := by
    have hd0 : eatingDemand p s.rem h o = 0 := Finset.card_eq_zero.mpr <|
      Finset.filter_eq_empty_iff.mpr fun i _ hfav => by
        simpa [hfav, ho] using favObject_rem_pos p s.rem h i
    simp [hrem_eq o, ho, hd0]
  have hz : ∀ o : Fin n, ¬ 0 < s.rem o → s.rem o = 0 := fun o ho =>
    le_antisymm (not_lt.mp ho) (hinv.rem_nonneg o)
  have hexh_old : ∀ x : Fin n, s.rem x = 0 →
      (eatingStep p s).exhaustTime x = s.exhaustTime x := fun x hx =>
    (hexh_eq x).trans (ite_eq_right fun hc => hc.1.ne' hx)
  have hexh_new : ∀ x : Fin n, 0 < s.rem x → (eatingStep p s).rem x = 0 →
      (eatingStep p s).exhaustTime x = s.elapsed + dt := fun x hx hx0 =>
    (hexh_eq x).trans (ite_eq_left ⟨hx, (hrem_eq x).symm.trans hx0⟩)
  have hcard_sum (o : Fin n) :
      (∑ i : Fin n, if favObject p s.rem h i = o then dt else 0) =
        (eatingDemand p s.rem h o : ℝ) * dt := by
    simp [← Finset.sum_filter, eatingDemand]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o
    rcases Nat.eq_zero_or_pos (eatingDemand p s.rem h o) with hd0 | hd
    · simp [hrem_eq o, hd0, hinv.rem_nonneg o]
    · exact (hrem_eq o).symm ▸ sub_nonneg.mpr (eatingDuration_le p s.rem h o hd)
  · exact fun i o => (halloc_eq i o).symm ▸
      add_nonneg (hinv.alloc_nonneg i o) (ite_nonneg hdt_pos.le le_rfl)
  · intro i
    simp [halloc_eq i, Finset.sum_add_distrib, hinv.row_sum i, hel_eq]
  · intro o
    rw [hrem_eq o]
    simp only [halloc_eq _ o, Finset.sum_add_distrib]
    linarith [hcard_sum o, hinv.col_sum o]
  · rw [hel_eq]; linarith [hinv.elapsed_nonneg]
  · intro i j
    have hrow (a : Fin n) : (eatingStep p s).alloc a =
        s.alloc a + fun o => if o = favObject p s.rem h a then dt else 0 :=
      funext fun o => by simp [halloc_eq, eq_comm, dt]
    rw [hrow i, hrow j]
    exact (hinv.envyFree i j).add <| (sdDominates_single_iff (p i) _ _ hdt_pos).mpr <|
      favObject_rank_le p s.rem h i _ (favObject_rem_pos p s.rem h j)
  · intro o ho
    by_cases hpos : 0 < s.rem o
    · rw [hexh_new o hpos ho, hel_eq]
    · linarith [hexh_old o (hz o hpos), hel_eq, hinv.exhaust_le o (hz o hpos)]
  · intro i a b hpos' hlt
    obtain ⟨ha0, horder⟩ : s.rem a = 0 ∧ (s.rem b = 0 → s.exhaustTime a < s.exhaustTime b) := by
      rcases (hinv.alloc_nonneg i b).eq_or_lt with hzero | hold
      · have hfav : favObject p s.rem h i = b :=
          by_contra fun hne => by simp [halloc_eq, ← hzero, hne] at hpos'
        exact ⟨le_antisymm (favObject_lt_le_zero p s.rem h i a (hfav ▸ hlt)) (hinv.rem_nonneg a),
          fun hb0 => absurd hb0 (hfav ▸ favObject_rem_pos p s.rem h i).ne'⟩
      · exact hinv.trade_order i a b hold hlt
    refine ⟨hrem_zero_of_zero a ha0, fun hb0' => ?_⟩
    rw [hexh_old a ha0]
    by_cases hb_pos : 0 < s.rem b
    · rw [hexh_new b hb_pos hb0']; linarith [hinv.exhaust_le a ha0]
    · exact hexh_old b (hz b hb_pos) ▸ horder (hz b hb_pos)

private noncomputable def activeObjs {n : ℕ} (s : EatingState n) : Finset (Fin n) :=
  @Finset.filter (Fin n) (fun o => 0 < s.rem o) (Classical.decPred _) Finset.univ

private lemma mem_activeObjs {n : ℕ} (s : EatingState n) (o : Fin n) :
    o ∈ activeObjs s ↔ 0 < s.rem o := by
  simp [activeObjs]

private lemma activeCard_step_le {n : ℕ} (p : Profile n) (s : EatingState n) :
    (activeObjs (eatingStep p s)).card = 0 ∨
      (activeObjs (eatingStep p s)).card < (activeObjs s).card := by
  by_cases h : ∃ o : Fin n, 0 < s.rem o
  · right
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
    · intro o ho
      rw [mem_activeObjs, eatingStep_pos_rem p s h o] at ho
      rw [mem_activeObjs]
      linarith [mul_nonneg (Nat.cast_nonneg (eatingDemand p s.rem h o))
        (eatingDuration_pos p s.rem h).le]
    · intro heq
      obtain ⟨o₀, ho_pos, ho_zero⟩ := exists_exhausted_of_eatingDuration p s.rem h
      have hmem := (mem_activeObjs _ o₀).mp (heq ▸ (mem_activeObjs s o₀).mpr ho_pos)
      rw [eatingStep_pos_rem p s h o₀] at hmem
      linarith
  · left
    rw [eatingStep, dite_eq_right h, Finset.card_eq_zero]
    exact Finset.eq_empty_of_forall_notMem fun o ho => h ⟨o, (mem_activeObjs s o).mp ho⟩

private lemma eatingStep_iter_inv {n : ℕ} (p : Profile n) (k : ℕ) :
    EatingInv p ((eatingStep p)^[k] (initEatingState n)) := by
  induction k with
  | zero => exact eatingInv_init p
  | succ k ih => exact Function.iterate_succ_apply' (eatingStep p) k _ ▸ eatingInv_step p ih

private lemma eatingStep_iter_activeCard_le {n : ℕ} (p : Profile n) (k : ℕ) :
    (activeObjs ((eatingStep p)^[k] (initEatingState n))).card ≤ n - k := by
  induction k with
  | zero => exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases activeCard_step_le p ((eatingStep p)^[k] (initEatingState n)) with h0 | hlt <;> omega

private lemma eatingStep_rem_eq_zero {n : ℕ} (p : Profile n) (o : Fin n) :
    ((eatingStep p)^[n] (initEatingState n)).rem o = 0 := by
  refine le_antisymm (not_lt.mp fun h => ?_) ((eatingStep_iter_inv p n).rem_nonneg o)
  have := eatingStep_iter_activeCard_le p n
  have := Finset.card_pos.mpr ⟨o, (mem_activeObjs _ o).mpr h⟩
  omega

private lemma eatingStep_elapsed_eq_one {n : ℕ} (hn : 0 < n) (p : Profile n) :
    ((eatingStep p)^[n] (initEatingState n)).elapsed = 1 := by
  set s := (eatingStep p)^[n] (initEatingState n)
  have hinv : EatingInv p s := eatingStep_iter_inv p n
  have hrem : ∑ o : Fin n, s.rem o = 0 :=
    Finset.sum_eq_zero fun o _ => eatingStep_rem_eq_zero p o
  have hsum : ∑ o : Fin n, (s.rem o + ∑ i : Fin n, s.alloc i o) = ∑ _o : Fin n, (1 : ℝ) :=
    Finset.sum_congr rfl fun o _ => hinv.col_sum o
  rw [Finset.sum_add_distrib, hrem, Finset.sum_comm,
    Finset.sum_congr rfl fun i _ => hinv.row_sum i] at hsum
  simp only [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  exact mul_left_cancel₀ (Nat.cast_pos.mpr hn).ne' hsum

/-- The Probabilistic Serial assignment is always a doubly stochastic matrix. -/
theorem probabilisticSerial_mem_doublyStochastic {n : ℕ} (p : Profile n) :
    probabilisticSerial p ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  have hinv := eatingStep_iter_inv p n
  refine ⟨hinv.alloc_nonneg, fun i => ?_, fun o => ?_⟩
  · exact (hinv.row_sum i).trans (eatingStep_elapsed_eq_one (Nat.zero_lt_of_lt i.isLt) p)
  · simpa only [probabilisticSerial, eatingStep_rem_eq_zero p o, zero_add] using hinv.col_sum o

/-- **Probabilistic Serial is `sd`-envy-free** ([BogomolnaiaMoulin2001], locator unverified). -/
theorem probabilisticSerial_isSDEnvyFree {n : ℕ} (p : Profile n) :
    IsSDEnvyFree p (probabilisticSerial p) :=
  (eatingStep_iter_inv p n).envyFree

/-- Probabilistic Serial satisfies equal treatment of equals (`ETE`). -/
theorem probabilisticSerial_isEqualTreatmentOfEquals {n : ℕ} (p : Profile n) :
    IsEqualTreatmentOfEquals p (probabilisticSerial p) :=
  (probabilisticSerial_isSDEnvyFree p).equalTreatmentOfEquals

/-- **Probabilistic Serial is `sd`-efficient (ordinally efficient)** ([BogomolnaiaMoulin2001],
locator unverified): object exhaustion times increase strictly along the trade relation `tradeRel`,
making the trade graph acyclic. -/
theorem probabilisticSerial_isSDEfficient {n : ℕ} (p : Profile n) :
    IsSDEfficient p (probabilisticSerial p) := by
  rw [isSDEfficient_iff_isAcyclicTrade]
  refine ⟨probabilisticSerial_mem_doublyStochastic p, ⟨fun a ha => ?_⟩⟩
  set s := (eatingStep p)^[n] (initEatingState n)
  have hinv := eatingStep_iter_inv p n
  have hmono : ∀ {x y : Fin n},
      Relation.TransGen (tradeRel p (probabilisticSerial p)) x y →
        s.exhaustTime x < s.exhaustTime y := fun hxy =>
    hxy.trans_induction_on
      (fun ⟨i, hpos, hpref⟩ => (hinv.trade_order i _ _ hpos hpref).2 (eatingStep_rem_eq_zero p _))
      fun _ _ => lt_trans
  exact lt_irrefl _ (hmono ha)

/-- Probabilistic Serial is ex-post efficient (corollary of `sd`-efficiency via Birkhoff's
theorem). -/
theorem probabilisticSerial_isExPostEfficient {n : ℕ} (p : Profile n) :
    IsExPostEfficient p (probabilisticSerial p) :=
  (probabilisticSerial_isSDEfficient p).isExPostEfficient

private lemma eatingStep_eq_self_of_rem_zero {n : ℕ} (p : Profile n) (s : EatingState n)
    (h0 : ∀ o : Fin n, s.rem o = 0) : eatingStep p s = s :=
  dite_eq_right fun ⟨o, ho⟩ => ho.ne' (h0 o)

private lemma eatingStep_iter_of_rem_zero {n : ℕ} (p : Profile n) (s : EatingState n)
    (h0 : ∀ o : Fin n, s.rem o = 0) (k : ℕ) : (eatingStep p)^[k] s = s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, eatingStep_eq_self_of_rem_zero p s h0, ih]

private lemma favObject_eq_of_lt_nonpos {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (i o : Fin n) (hpos : 0 < rem o)
    (hprev : ∀ a : Fin n, (p i).symm a < (p i).symm o → rem a ≤ 0) :
    favObject p rem h i = o :=
  (p i).symm.injective <| (favObject_rank_le p rem h i o hpos).antisymm <|
    not_lt.mp fun hlt => (hprev _ hlt).not_gt (favObject_rem_pos p rem h i)

private lemma eatingDuration_eq_of_le {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (d : ℝ)
    (hmem : ∃ o : Fin n, 0 < eatingDemand p rem h o ∧
      rem o / (eatingDemand p rem h o : ℝ) = d)
    (hle : ∀ o : Fin n, 0 < eatingDemand p rem h o →
      d ≤ rem o / (eatingDemand p rem h o : ℝ)) :
    eatingDuration p rem h = d := by
  obtain ⟨o₀, hd₀, rfl⟩ := hmem
  exact le_antisymm (Finset.inf'_le _ (by simpa using hd₀))
    (Finset.le_inf' _ _ fun o ho => hle o (by simpa using ho))

/-- Remaining-supply vector assigning `(r 0, r 1, r 2)` to the first three objects and uniform
supply `d` to every dummy object `o ≥ 3`. -/
private def padVec {n : ℕ} (r : Fin 3 → ℝ) (d : ℝ) (o : Fin n) : ℝ :=
  if h : o.val < 3 then r ⟨o.val, h⟩ else d

/-- Demand count among the first three agents `0, 1, 2` for object `j : Fin 3`. -/
private def coreCount (f : Fin 3 → Fin 3) (j : Fin 3) : ℕ :=
  (Finset.univ.filter fun a : Fin 3 => f a = j).card

/-- Advance `eatingStep` by one phase on a dummy-padded profile whose first three agents target
`f : Fin 3 → Fin 3` and whose dummy agents `i ≥ 3` each target their own top object `i`. -/
private lemma eatingStep_padded {n : ℕ} (hn : 3 ≤ n) (p : Profile n) (s : EatingState n)
    (r : Fin 3 → ℝ) (d dt : ℝ) (f : Fin 3 → Fin 3)
    (hdum : ∀ i : Fin n, 3 ≤ i.val → (p i).symm i = ⟨0, by omega⟩)
    (hs : ∀ o : Fin n, s.rem o = padVec r d o)
    (hpos : 0 < r 2) (hdpos : 0 < d)
    (hfav : ∀ a : Fin 3, favObject p s.rem ⟨⟨2, by omega⟩, by simpa [hs, padVec] using hpos⟩
      ⟨a.val, by omega⟩ = ⟨(f a).val, by omega⟩)
    (hdt_mem : ∃ j : Fin 3, 0 < coreCount f j ∧ r j / (coreCount f j : ℝ) = dt)
    (hdt_le : ∀ j : Fin 3, 0 < coreCount f j → dt ≤ r j / (coreCount f j : ℝ))
    (hdt_d : dt ≤ d) :
    (∀ o : Fin n, (eatingStep p s).rem o =
      padVec (fun j => r j - (coreCount f j : ℝ) * dt) (d - dt) o) ∧
    (∀ a : Fin 3, (eatingStep p s).alloc ⟨2, by omega⟩ ⟨a.val, by omega⟩ =
      s.alloc ⟨2, by omega⟩ ⟨a.val, by omega⟩ + if f 2 = a then dt else 0) := by
  have hex : ∃ o : Fin n, 0 < s.rem o := ⟨⟨2, by omega⟩, by simpa [hs, padVec] using hpos⟩
  have hfav_all : ∀ i : Fin n, favObject p s.rem hex i =
      if h : i.val < 3 then ⟨(f ⟨i.val, h⟩).val, by omega⟩ else i := fun i => by
    split_ifs with hi
    · exact hfav ⟨i.val, hi⟩
    · refine favObject_eq_of_lt_nonpos p s.rem hex i i
        (by simpa [hs, padVec, hi] using hdpos) fun _ ha => by
          rw [hdum i (by omega)] at ha; exact absurd ha (by simp [Fin.lt_def])
  have hdem : ∀ o : Fin n, eatingDemand p s.rem hex o =
      if h : o.val < 3 then coreCount f ⟨o.val, h⟩ else 1 := fun o => by
    unfold eatingDemand; simp_rw [hfav_all]
    by_cases ho : o.val < 3
    · simp only [ho, ↓reduceDIte, coreCount]
      refine (Finset.card_bij (fun a _ => Fin.castLE hn a)
        (fun a ha => by simpa [Fin.ext_iff] using ha)
        (fun a _ b _ h => Fin.castLE_injective hn h) fun i hi => ?_).symm
      have hi3 : i.val < 3 := by
        by_contra hnot
        simp [hnot, Fin.ext_iff] at hi
        omega
      exact ⟨⟨i.val, hi3⟩, by simpa [hi3, Fin.ext_iff] using hi, rfl⟩
    · simp only [ho, ↓reduceDIte]
      refine Finset.card_eq_one.mpr ⟨o, Finset.ext fun i => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      split_ifs with hi
      · have := (f ⟨i.val, hi⟩).isLt
        simp only [Fin.ext_iff]; omega
      · rfl
  have hdt : eatingDuration p s.rem hex = dt := by
    obtain ⟨j, hj_pos, hj_eq⟩ := hdt_mem
    refine eatingDuration_eq_of_le p s.rem hex dt
      ⟨⟨j.val, by omega⟩, by simpa [hdem, j.isLt] using hj_pos,
        by simpa [hs, padVec, hdem, j.isLt] using hj_eq⟩ fun o hd => ?_
    by_cases ho : o.val < 3
    · simp only [hdem o, ho, ↓reduceDIte] at hd ⊢
      simpa [hs, padVec, ho] using hdt_le ⟨o.val, ho⟩ hd
    · simpa [hs o, padVec, hdem o, ho] using hdt_d
  refine ⟨fun o => ?_, fun a => ?_⟩
  · rw [eatingStep_pos_rem p s hex o, hs o, hdem o, hdt]
    by_cases ho : o.val < 3 <;> simp [padVec, ho]
  · rw [eatingStep_pos_alloc p s hex ⟨2, by omega⟩ ⟨a.val, by omega⟩, hdt, hfav_all ⟨2, by omega⟩]
    simp [Fin.ext_iff]

/-- Generalized 3-object manipulation witness profile `(a b c …, a c b …, b a c …)` padded with
dummy agents `k ≥ 3` whose top choice is object `k`. -/
@[expose] def psManipProfile {n : ℕ} (hn : 3 ≤ n) : Profile n := fun i =>
  if i.val = 0 then Equiv.refl (Fin n)
  else if i.val = 1 then Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩
  else if i.val = 2 then Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩
  else Equiv.swap ⟨0, by omega⟩ i

private lemma psManip_symm_dummy {n : ℕ} (hn : 3 ≤ n) (i : Fin n) (hi : 3 ≤ i.val) :
    (psManipProfile hn i).symm i = ⟨0, by omega⟩ := by
  unfold psManipProfile
  split_ifs <;> first | omega | simp

/-- Verify the favorite object of agent `i` under a permutation `π` agreeing with `id`, `swap 1 2`,
or `swap 0 1` on `{0, 1, 2}`: every strictly preferred object in `{0, 1, 2}` is `≤ 0`. -/
private lemma fav_core {n : ℕ} (hn : 3 ≤ n) (p : Profile n) {r : Fin 3 → ℝ} {d : ℝ}
    (s : EatingState n) (hs : ∀ o, s.rem o = padVec r d o)
    (h : ∃ o : Fin n, 0 < s.rem o) (i : Fin n) (k : Fin 3)
    (hpos : 0 < r k)
    (hprev : ∀ x : Fin n, (p i).symm x < (p i).symm ⟨k.val, by omega⟩ →
      ∃ j : Fin 3, x.val = j.val ∧ r j ≤ 0) :
    favObject p s.rem h i = ⟨k.val, by omega⟩ :=
  favObject_eq_of_lt_nonpos p s.rem h i ⟨k.val, by omega⟩
    (by simpa [hs, padVec, k.isLt] using hpos) fun x hx => by
      obtain ⟨j, hj, hjle⟩ := hprev x hx
      have hx3 : x.val < 3 := by omega
      have hxj : (⟨x.val, hx3⟩ : Fin 3) = j := Fin.ext hj
      simpa [hs, padVec, hx3, hxj] using hjle

private lemma eq_iter_three_of_rem_zero {n : ℕ} (hn : 3 ≤ n) (p : Profile n)
    (h0 : ∀ o : Fin n, ((eatingStep p)^[3] (initEatingState n)).rem o = 0) :
    (eatingStep p)^[n] (initEatingState n) = (eatingStep p)^[3] (initEatingState n) :=
  calc (eatingStep p)^[n] (initEatingState n)
      = (eatingStep p)^[(n - 3) + 3] (initEatingState n) :=
        congrArg (fun k => (eatingStep p)^[k] (initEatingState n)) (by omega)
    _ = (eatingStep p)^[n - 3] ((eatingStep p)^[3] (initEatingState n)) :=
        Function.iterate_add_apply _ _ _ _
    _ = (eatingStep p)^[3] (initEatingState n) := eatingStep_iter_of_rem_zero p _ h0 (n - 3)

private lemma swap01_lt {n : ℕ} (hn : 3 ≤ n) (x : Fin n)
    (h : (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩).symm x <
      (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩).symm ⟨2, by omega⟩) :
    x.val = 0 ∨ x.val = 1 := by
  simp only [Equiv.symm_swap, Equiv.swap_apply_def, Fin.lt_def, Fin.ext_iff, apply_ite Fin.val] at h
  split_ifs at h <;> omega

private lemma swap12_lt_two {n : ℕ} (hn : 3 ≤ n) (x : Fin n)
    (hx : (Equiv.swap (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩).symm x <
      (Equiv.swap (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩).symm ⟨2, by omega⟩) :
    x.val = 0 := by
  simp only [Equiv.symm_swap, Equiv.swap_apply_def, Fin.lt_def, Fin.ext_iff,
    apply_ite Fin.val] at hx
  split_ifs at hx <;> omega

private lemma psManip_eq_swap01 {n : ℕ} (hn : 3 ≤ n) (i : Fin n) (hi : i.val = 2) :
    psManipProfile hn i = Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  simp [psManipProfile, hi]

/-- Common 3-round trace when agent `0` has `0 > 1 > 2`, agent `1` has `0 > 2 > 1`, dummies `≥ 3`
rank themselves first, and agent `2` has either `1 > 0 > 2` (truthful) or `0 > 1 > 2`
(misreport). -/
private lemma eval_psManip_three {n : ℕ} (hn : 3 ≤ n) (p : Profile n)
    (hp0 : p ⟨0, by omega⟩ = Equiv.refl (Fin n))
    (hp1 : p ⟨1, by omega⟩ = Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩)
    (hdum : ∀ i : Fin n, 3 ≤ i.val → (p i).symm i = ⟨0, by omega⟩)
    (f₀ : Fin 3 → Fin 3) (dt₀ dt₁ dt₂ : ℝ)
    (r₁ r₂ : Fin 3 → ℝ) (d₁ d₂ : ℝ)
    (hr₁_def : ∀ j : Fin 3, 1 - (coreCount f₀ j : ℝ) * dt₀ = r₁ j)
    (hd₁_def : 1 - dt₀ = d₁)
    (hr₂_def : ∀ j : Fin 3, r₁ j - (coreCount ![1, 2, 1] j : ℝ) * dt₁ = r₂ j)
    (hd₂_def : d₁ - dt₁ = d₂)
    (hr₃_zero : ∀ j : Fin 3, r₂ j - (coreCount ![2, 2, 2] j : ℝ) * dt₂ = 0)
    (hd₃_zero : d₂ - dt₂ = 0)
    (h0_p2 : (p ⟨2, by omega⟩).symm ⟨(f₀ 2).val, by omega⟩ = ⟨0, by omega⟩)
    (hf0_0 : f₀ 0 = 0) (hf0_1 : f₀ 1 = 0)
    (hdt₀ : (∃ j : Fin 3, 0 < coreCount f₀ j ∧ 1 / (coreCount f₀ j : ℝ) = dt₀) ∧
      (∀ j : Fin 3, 0 < coreCount f₀ j → dt₀ ≤ 1 / (coreCount f₀ j : ℝ)) ∧ dt₀ ≤ 1)
    (hr₁_0 : r₁ 0 ≤ 0) (hr₁_1 : 0 < r₁ 1) (hr₁_2 : 0 < r₁ 2) (hd₁_pos : 0 < d₁)
    (hprev1_2 : ∀ x : Fin n, (p ⟨2, by omega⟩).symm x < (p ⟨2, by omega⟩).symm ⟨1, by omega⟩ →
      x.val = 0)
    (hdt₁ : (∃ j : Fin 3, 0 < coreCount ![1, 2, 1] j ∧
        r₁ j / (coreCount ![1, 2, 1] j : ℝ) = dt₁) ∧
      (∀ j : Fin 3, 0 < coreCount ![1, 2, 1] j →
        dt₁ ≤ r₁ j / (coreCount ![1, 2, 1] j : ℝ)) ∧ dt₁ ≤ d₁)
    (hr₂_0 : r₂ 0 ≤ 0) (hr₂_1 : r₂ 1 ≤ 0) (hr₂_2 : 0 < r₂ 2) (hd₂_pos : 0 < d₂)
    (hprev2_2 : ∀ x : Fin n, (p ⟨2, by omega⟩).symm x < (p ⟨2, by omega⟩).symm ⟨2, by omega⟩ →
      x.val = 0 ∨ x.val = 1)
    (hdt₂ : (∃ j : Fin 3, 0 < coreCount ![2, 2, 2] j ∧
        r₂ j / (coreCount ![2, 2, 2] j : ℝ) = dt₂) ∧
      (∀ j : Fin 3, 0 < coreCount ![2, 2, 2] j →
        dt₂ ≤ r₂ j / (coreCount ![2, 2, 2] j : ℝ)) ∧ dt₂ ≤ d₂) :
    ∀ a : Fin 3, probabilisticSerial p ⟨2, by omega⟩ ⟨a.val, by omega⟩ =
      (if f₀ 2 = a then dt₀ else 0) + (if (1 : Fin 3) = a then dt₁ else 0) +
        (if (2 : Fin 3) = a then dt₂ else 0) := by
  let s0 := initEatingState n
  let s1 := eatingStep p s0
  let s2 := eatingStep p s1
  let s3 := eatingStep p s2
  have hs0 : ∀ o : Fin n, s0.rem o = padVec (fun _ => 1) 1 o := fun o => by
    simp [s0, initEatingState, padVec]
  obtain ⟨hs1_rem', hs1_a⟩ := eatingStep_padded hn p s0 (fun _ => 1) 1 dt₀ f₀ hdum hs0
    zero_lt_one zero_lt_one (fun a => by
      fin_cases a
      · exact fav_core hn p s0 hs0 _ _ (f₀ 0) zero_lt_one fun x hx => by
          rw [hf0_0, hp0] at hx; exact absurd hx (by simp [Fin.lt_def])
      · exact fav_core hn p s0 hs0 _ _ (f₀ 1) zero_lt_one fun x hx => by
          rw [hf0_1, hp1] at hx
          simp [Equiv.swap_apply_def, Fin.lt_def] at hx
      · exact fav_core hn p s0 hs0 _ _ (f₀ 2) zero_lt_one fun x hx => by
          rw [h0_p2] at hx; exact absurd hx (by simp [Fin.lt_def]))
    hdt₀.1 hdt₀.2.1 hdt₀.2.2
  have hs1_rem : ∀ o : Fin n, s1.rem o = padVec r₁ d₁ o := fun o => by
    rw [hs1_rem' o]; by_cases ho : o.val < 3 <;> simp [padVec, ho, hr₁_def, hd₁_def]
  obtain ⟨hs2_rem', hs2_a⟩ := eatingStep_padded hn p s1 r₁ d₁ dt₁ ![1, 2, 1] hdum hs1_rem
    hr₁_2 hd₁_pos (fun a => by
      fin_cases a
      · exact fav_core hn p s1 hs1_rem _ _ 1 hr₁_1 fun x hx => by
          rw [hp0] at hx; exact ⟨0, by change x.val = 0; have : x.val < 1 := hx; omega, hr₁_0⟩
      · exact fav_core hn p s1 hs1_rem _ _ 2 hr₁_2 fun x hx => by
          rw [hp1] at hx; exact ⟨0, swap12_lt_two hn x hx, hr₁_0⟩
      · exact fav_core hn p s1 hs1_rem _ _ 1 hr₁_1 fun x hx =>
          ⟨0, hprev1_2 x hx, hr₁_0⟩)
    hdt₁.1 hdt₁.2.1 hdt₁.2.2
  have hs2_rem : ∀ o : Fin n, s2.rem o = padVec r₂ d₂ o := fun o => by
    rw [hs2_rem' o]; by_cases ho : o.val < 3 <;> simp [padVec, ho, hr₂_def, hd₂_def]
  obtain ⟨hs3_rem', hs3_a⟩ := eatingStep_padded hn p s2 r₂ d₂ dt₂ ![2, 2, 2] hdum hs2_rem
    hr₂_2 hd₂_pos (fun a => by
      fin_cases a
      · exact fav_core hn p s2 hs2_rem _ _ 2 hr₂_2 fun x hx => by
          rw [hp0] at hx
          obtain h | h : x.val = 0 ∨ x.val = 1 := by change x.val < 2 at hx; omega
          exacts [⟨0, h, hr₂_0⟩, ⟨1, h, hr₂_1⟩]
      · exact fav_core hn p s2 hs2_rem _ _ 2 hr₂_2 fun x hx => by
          rw [hp1] at hx; exact ⟨0, swap12_lt_two hn x hx, hr₂_0⟩
      · exact fav_core hn p s2 hs2_rem _ _ 2 hr₂_2 fun x hx =>
          (hprev2_2 x hx).elim (fun h => ⟨0, h, hr₂_0⟩) (fun h => ⟨1, h, hr₂_1⟩))
    hdt₂.1 hdt₂.2.1 hdt₂.2.2
  have hs3_zero : ∀ o : Fin n, s3.rem o = 0 := fun o => by
    rw [hs3_rem' o]; by_cases ho : o.val < 3 <;> simp [padVec, ho, hr₃_zero, hd₃_zero]
  intro a
  rw [probabilisticSerial, eq_iter_three_of_rem_zero hn p hs3_zero]
  change s3.alloc _ _ = _
  rw [hs3_a, hs2_a, hs1_a]
  exact congrArg (· + _ + _) (zero_add _)

private lemma coreCount_t0 (j : Fin 3) : coreCount ![0, 0, 1] j = ![2, 1, 0] j := by
  fin_cases j <;> decide

private lemma coreCount_m0 (j : Fin 3) : coreCount ![0, 0, 0] j = ![3, 0, 0] j := by
  fin_cases j <;> decide

private lemma coreCount_r1 (j : Fin 3) : coreCount ![1, 2, 1] j = ![0, 2, 1] j := by
  fin_cases j <;> decide

private lemma coreCount_r2 (j : Fin 3) : coreCount ![2, 2, 2] j = ![0, 0, 3] j := by
  fin_cases j <;> decide

private lemma psManip_truthful_row2 {n : ℕ} (hn : 3 ≤ n) :
    probabilisticSerial (psManipProfile hn) ⟨2, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    probabilisticSerial (psManipProfile hn) ⟨2, by omega⟩ ⟨1, by omega⟩ = 3 / 4 ∧
    probabilisticSerial (psManipProfile hn) ⟨2, by omega⟩ ⟨2, by omega⟩ = 1 / 4 := by
  have heval := eval_psManip_three hn (psManipProfile hn)
    (by simp [psManipProfile]) (by simp [psManipProfile]) (psManip_symm_dummy hn)
    ![0, 0, 1] (1 / 2) (1 / 4) (1 / 4)
    ![0, 1 / 2, 1] ![0, 0, 3 / 4] (1 / 2) (1 / 4)
    (fun j => by fin_cases j <;> simp [coreCount_t0]; norm_num)
    (by norm_num)
    (fun j => by fin_cases j <;> simp [coreCount_r1] <;> norm_num)
    (by norm_num)
    (fun j => by fin_cases j <;> simp [coreCount_r2]; norm_num)
    (by norm_num)
    (by simp [psManipProfile]) rfl rfl
    ⟨⟨0, by decide, by simp [coreCount_t0]⟩,
      fun j hj => by fin_cases j <;> simp [coreCount_t0] at hj ⊢; norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx => by
      rw [psManip_eq_swap01 hn _ rfl] at hx
      simp [Equiv.swap_apply_def, Fin.lt_def] at hx)
    ⟨⟨1, by decide, by simp [coreCount_r1]; norm_num⟩,
      fun j hj => by fin_cases j <;> simp [coreCount_r1] at hj ⊢ <;> norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx => by rw [psManip_eq_swap01 hn _ rfl] at hx; exact swap01_lt hn x hx)
    ⟨⟨2, by decide, by simp [coreCount_r2]; norm_num⟩,
      fun j hj => by fin_cases j <;> simp [coreCount_r2] at hj ⊢; norm_num, by norm_num⟩
  exact ⟨by simpa using heval 0, (heval 1).trans (by norm_num), by simpa using heval 2⟩

private lemma psManip_misreport_row2 {n : ℕ} (hn : 3 ≤ n) :
    let p' := Function.update (psManipProfile hn) ⟨2, by omega⟩ (Equiv.refl (Fin n))
    probabilisticSerial p' ⟨2, by omega⟩ ⟨0, by omega⟩ = 1 / 3 ∧
    probabilisticSerial p' ⟨2, by omega⟩ ⟨1, by omega⟩ = 1 / 2 ∧
    probabilisticSerial p' ⟨2, by omega⟩ ⟨2, by omega⟩ = 1 / 6 := by
  intro p'
  have hne2 : ∀ i : Fin n, i.val ≠ 2 → p' i = psManipProfile hn i := fun i hi =>
    Function.update_of_ne (fun h => hi (congrArg Fin.val h)) _ _
  have hp2 : p' ⟨2, by omega⟩ = Equiv.refl (Fin n) := Function.update_self _ _ _
  have heval := eval_psManip_three hn p'
    (by simpa [psManipProfile] using hne2 ⟨0, by omega⟩ (by simp))
    (by simpa [psManipProfile] using hne2 ⟨1, by omega⟩ (by simp))
    (fun i hi => by rw [hne2 i (by omega)]; exact psManip_symm_dummy hn i hi)
    ![0, 0, 0] (1 / 3) (1 / 2) (1 / 6)
    ![0, 1, 1] ![0, 0, 1 / 2] (2 / 3) (1 / 6)
    (fun j => by fin_cases j <;> simp [coreCount_m0])
    (by norm_num)
    (fun j => by fin_cases j <;> simp [coreCount_r1]; norm_num)
    (by norm_num)
    (fun j => by fin_cases j <;> simp [coreCount_r2]; norm_num)
    (by norm_num)
    (by rw [hp2]; rfl) rfl rfl
    ⟨⟨0, by decide, by simp [coreCount_m0]⟩,
      fun j hj => by fin_cases j <;> simp [coreCount_m0] at hj ⊢, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx => by rw [hp2] at hx; change x.val < 1 at hx; omega)
    ⟨⟨1, by decide, by simp [coreCount_r1]⟩,
      fun j hj => by fin_cases j <;> simp [coreCount_r1] at hj ⊢; norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx => by rw [hp2] at hx; change x.val < 2 at hx; omega)
    ⟨⟨2, by decide, by simp [coreCount_r2]; norm_num⟩,
      fun j hj => by fin_cases j <;> simp [coreCount_r2] at hj ⊢; norm_num, by norm_num⟩
  exact ⟨by simpa using heval 0, by simpa using heval 1, by simpa using heval 2⟩

/-- Exact values of agent `2`'s lottery under `probabilisticSerial` on `psManipProfile hn`:
truthful `(0, 3/4, 1/4)` vs misreported `(1/3, 1/2, 1/6)`. -/
theorem probabilisticSerial_manip_values {n : ℕ} (hn : 3 ≤ n) :
    (probabilisticSerial (psManipProfile hn) ⟨2, by omega⟩ ⟨0, by omega⟩ = 0 ∧
     probabilisticSerial (psManipProfile hn) ⟨2, by omega⟩ ⟨1, by omega⟩ = 3 / 4 ∧
     probabilisticSerial (psManipProfile hn) ⟨2, by omega⟩ ⟨2, by omega⟩ = 1 / 4) ∧
    (probabilisticSerial (Function.update (psManipProfile hn) ⟨2, by omega⟩ (Equiv.refl (Fin n)))
        ⟨2, by omega⟩ ⟨0, by omega⟩ = 1 / 3 ∧
     probabilisticSerial (Function.update (psManipProfile hn) ⟨2, by omega⟩ (Equiv.refl (Fin n)))
        ⟨2, by omega⟩ ⟨1, by omega⟩ = 1 / 2 ∧
     probabilisticSerial (Function.update (psManipProfile hn) ⟨2, by omega⟩ (Equiv.refl (Fin n)))
        ⟨2, by omega⟩ ⟨2, by omega⟩ = 1 / 6) :=
  ⟨psManip_truthful_row2 hn, psManip_misreport_row2 hn⟩

/-- **Non-strategy-proofness of Probabilistic Serial** ([BogomolnaiaMoulin2001], locator
unverified): for every `n ≥ 3`, `probabilisticSerial` fails strong `sd`-strategy-proofness.
On `psManipProfile hn`, agent `2` (`1 > 0 > 2 > …`) raises her cumulative probability on `{1, 0}`
from `3/4` to `1/2 + 1/3 = 5/6` by misreporting `0 > 1 > 2 > …`. -/
theorem not_isSDStrategyProof_probabilisticSerial {n : ℕ} (hn : 3 ≤ n) :
    ¬ IsSDStrategyProof (probabilisticSerial (n := n)) := by
  intro hsp
  have hdom := hsp (psManipProfile hn) ⟨2, by omega⟩ (Equiv.refl (Fin n)) ⟨1, by omega⟩
  have hiic : Finset.Iic (⟨1, by omega⟩ : Fin n) =
      {⟨0, by omega⟩, ⟨1, by omega⟩} := by
    ext r
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
    omega
  have hsum (x : Fin n → ℝ) :
      upperContourSum (psManipProfile hn ⟨2, by omega⟩) x ⟨1, by omega⟩ =
        x ⟨1, by omega⟩ + x ⟨0, by omega⟩ := by
    rw [upperContourSum, hiic, Finset.sum_pair (by simp [Fin.ext_iff]),
      psManip_eq_swap01 hn ⟨2, by omega⟩ rfl]
    simp
  rw [hsum, hsum] at hdom
  obtain ⟨⟨ht0, ht1, _⟩, ⟨hm0, hm1, _⟩⟩ := probabilisticSerial_manip_values hn
  linarith

end Cslib.GameTheory.RandomAssignment
