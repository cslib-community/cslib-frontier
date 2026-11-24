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
  returns a doubly stochastic matrix (`probabilisticSerial_isFeasible`).
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
noncomputable def favObject {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
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
noncomputable def eatingDemand {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (o : Fin n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => favObject p rem h i = o).card

private lemma demanded_nonempty {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) :
    (Finset.univ.filter fun o : Fin n => 0 < eatingDemand p rem h o).Nonempty := by
  rcases h with ⟨o₀, ho₀⟩
  refine ⟨favObject p rem ⟨o₀, ho₀⟩ o₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact Finset.card_pos.mpr ⟨o₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- Duration `Δ = min {rem o / demand o | demand o > 0}` of the current eating phase. -/
noncomputable def eatingDuration {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) : ℝ :=
  (Finset.univ.filter fun o : Fin n => 0 < eatingDemand p rem h o).inf'
    (demanded_nonempty p rem h)
    fun o => rem o / (eatingDemand p rem h o : ℝ)

private lemma eatingDuration_pos {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) : 0 < eatingDuration p rem h := by
  obtain ⟨o, ho, heq⟩ := Finset.exists_mem_eq_inf' (demanded_nonempty p rem h)
    (fun o => rem o / (eatingDemand p rem h o : ℝ))
  have hd_pos : 0 < eatingDemand p rem h o := (Finset.mem_filter.mp ho).2
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hd_pos
  have hrem : 0 < rem o := by
    rw [← (Finset.mem_filter.mp hi).2]
    exact favObject_rem_pos p rem h i
  rw [eatingDuration, heq]
  exact div_pos hrem (Nat.cast_pos.mpr hd_pos)

private lemma eatingDuration_le {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (o : Fin n) (hd : 0 < eatingDemand p rem h o) :
    (eatingDemand p rem h o : ℝ) * eatingDuration p rem h ≤ rem o := by
  have hmem : o ∈ Finset.univ.filter fun o : Fin n => 0 < eatingDemand p rem h o :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
  have hle : eatingDuration p rem h ≤ rem o / (eatingDemand p rem h o : ℝ) :=
    Finset.inf'_le _ hmem
  have hdp : (0 : ℝ) < (eatingDemand p rem h o : ℝ) := Nat.cast_pos.mpr hd
  exact (le_div_iff₀' hdp).mp hle

private lemma exists_exhausted_of_eatingDuration {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) :
    ∃ o : Fin n, 0 < rem o ∧
      rem o - (eatingDemand p rem h o : ℝ) * eatingDuration p rem h = 0 := by
  obtain ⟨o, ho, heq⟩ := Finset.exists_mem_eq_inf' (demanded_nonempty p rem h)
    (fun o => rem o / (eatingDemand p rem h o : ℝ))
  have hd_pos : 0 < eatingDemand p rem h o := (Finset.mem_filter.mp ho).2
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hd_pos
  have hrem : 0 < rem o := by
    rw [← (Finset.mem_filter.mp hi).2]
    exact favObject_rem_pos p rem h i
  refine ⟨o, hrem, ?_⟩
  rw [eatingDuration, heq]
  have hd_ne : (eatingDemand p rem h o : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd_pos).ne'
  rw [mul_div_cancel₀ _ hd_ne, sub_self]

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

private lemma dite_pos_classical {α : Sort*} {P : Prop} {t : P → α} {e : ¬ P → α} (h : P) :
    @dite α P (Classical.propDecidable P) t e = t h := by
  cases Classical.propDecidable P with
  | isTrue _ => rfl
  | isFalse hneg => exact absurd h hneg

private lemma dite_neg_classical {α : Sort*} {P : Prop} {t : P → α} {e : ¬ P → α} (h : ¬ P) :
    @dite α P (Classical.propDecidable P) t e = e h := by
  cases Classical.propDecidable P with
  | isTrue hpos => exact absurd hpos h
  | isFalse _ => rfl

private lemma ite_pos_classical {α : Sort*} {P : Prop} {t e : α} (h : P) :
    @ite α P (Classical.propDecidable P) t e = t := by
  cases Classical.propDecidable P with
  | isTrue _ => rfl
  | isFalse hneg => exact absurd h hneg

private lemma ite_neg_classical {α : Sort*} {P : Prop} {t e : α} (h : ¬ P) :
    @ite α P (Classical.propDecidable P) t e = e := by
  cases Classical.propDecidable P with
  | isTrue hpos => exact absurd hpos h
  | isFalse _ => rfl

private lemma eatingStep_pos_rem {n : ℕ} (p : Profile n) (s : EatingState n)
    (h : ∃ o : Fin n, 0 < s.rem o) (o : Fin n) :
    (eatingStep p s).rem o =
      s.rem o - (eatingDemand p s.rem h o : ℝ) * eatingDuration p s.rem h := by
  have heq : (eatingStep p s).rem =
      fun o => s.rem o - (eatingDemand p s.rem h o : ℝ) * eatingDuration p s.rem h :=
    congrArg EatingState.rem (dite_pos_classical h)
  exact congrFun heq o

private lemma eatingStep_pos_alloc {n : ℕ} (p : Profile n) (s : EatingState n)
    (h : ∃ o : Fin n, 0 < s.rem o) (i o : Fin n) :
    (eatingStep p s).alloc i o =
      s.alloc i o + if favObject p s.rem h i = o then eatingDuration p s.rem h else 0 := by
  have heq : (eatingStep p s).alloc = Matrix.of fun i o =>
      s.alloc i o + if favObject p s.rem h i = o then eatingDuration p s.rem h else 0 :=
    congrArg EatingState.alloc (dite_pos_classical h)
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i o) heq

private lemma eatingStep_pos_elapsed {n : ℕ} (p : Profile n) (s : EatingState n)
    (h : ∃ o : Fin n, 0 < s.rem o) :
    (eatingStep p s).elapsed = s.elapsed + eatingDuration p s.rem h :=
  congrArg EatingState.elapsed (dite_pos_classical h)

private lemma eatingStep_pos_exhaust {n : ℕ} (p : Profile n) (s : EatingState n)
    (h : ∃ o : Fin n, 0 < s.rem o) (o : Fin n) :
    (eatingStep p s).exhaustTime o =
      @ite ℝ (0 < s.rem o ∧
          s.rem o - (eatingDemand p s.rem h o : ℝ) * eatingDuration p s.rem h = 0)
        (Classical.propDecidable _)
        (s.elapsed + eatingDuration p s.rem h) (s.exhaustTime o) :=
  congrFun (congrArg EatingState.exhaustTime (dite_pos_classical h)) o

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
  · have hfix : eatingStep p s = s := dite_neg_classical h
    rwa [hfix]
  set dt := eatingDuration p s.rem h
  have hdt_pos : 0 < dt := eatingDuration_pos p s.rem h
  have hrem_eq : ∀ o : Fin n,
      (eatingStep p s).rem o = s.rem o - (eatingDemand p s.rem h o : ℝ) * dt :=
    eatingStep_pos_rem p s h
  have halloc_eq : ∀ i o : Fin n,
      (eatingStep p s).alloc i o =
        s.alloc i o + if favObject p s.rem h i = o then dt else 0 :=
    eatingStep_pos_alloc p s h
  have hel_eq : (eatingStep p s).elapsed = s.elapsed + dt :=
    eatingStep_pos_elapsed p s h
  have hexh_eq := eatingStep_pos_exhaust p s h
  have hrem_zero_of_zero : ∀ o : Fin n, s.rem o = 0 → (eatingStep p s).rem o = 0 := by
    intro o ho
    have hd0 : eatingDemand p s.rem h o = 0 := by
      rw [eatingDemand, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hfav
      have hpos := favObject_rem_pos p s.rem h i
      rw [hfav, ho] at hpos
      exact lt_irrefl _ hpos
    rw [hrem_eq o, ho, hd0]
    simp
  have hcard_sum : ∀ o : Fin n,
      (∑ i : Fin n, if favObject p s.rem h i = o then dt else 0) =
        (eatingDemand p s.rem h o : ℝ) * dt := by
    intro o
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o
    rw [hrem_eq o]
    by_cases hd : 0 < eatingDemand p s.rem h o
    · exact sub_nonneg.mpr (eatingDuration_le p s.rem h o hd)
    · have hd0 : eatingDemand p s.rem h o = 0 := by omega
      simp only [hd0, Nat.cast_zero, zero_mul, sub_zero]
      exact hinv.rem_nonneg o
  · intro i o
    rw [halloc_eq i o]
    refine add_nonneg (hinv.alloc_nonneg i o) ?_
    split_ifs
    · exact hdt_pos.le
    · exact le_rfl
  · intro i
    simp_rw [halloc_eq i, Finset.sum_add_distrib, hinv.row_sum i, hel_eq]
    congr 1
    rw [Finset.sum_eq_single (favObject p s.rem h i)]
    · simp
    · intro o _ ho; simp [ho.symm]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · intro o
    simp_rw [hrem_eq o, halloc_eq _ o, Finset.sum_add_distrib, hcard_sum o]
    linarith [hinv.col_sum o]
  · rw [hel_eq]; linarith [hinv.elapsed_nonneg]
  · intro i j
    have hi_le : (p i).symm (favObject p s.rem h i) ≤
        (p i).symm (favObject p s.rem h j) :=
      favObject_rank_le p s.rem h i (favObject p s.rem h j) (favObject_rem_pos p s.rem h j)
    have hstep_dom : SDDominates (p i)
        (fun o => if o = favObject p s.rem h i then dt else 0)
        (fun o => if o = favObject p s.rem h j then dt else 0) :=
      (sdDominates_single_iff (p i) _ _ hdt_pos).mpr hi_le
    have hadd := SDDominates.add (hinv.envyFree i j) hstep_dom
    have hrow : ∀ a : Fin n, (eatingStep p s).alloc a =
        s.alloc a + fun o => if o = favObject p s.rem h a then dt else 0 := by
      intro a; funext o; rw [halloc_eq a o]; simp [eq_comm]
    rw [hrow i, hrow j]
    exact hadd
  · intro o ho
    rw [hexh_eq o, hel_eq]
    have ho' : s.rem o - (eatingDemand p s.rem h o : ℝ) * dt = 0 := by
      rw [← hrem_eq o]; exact ho
    by_cases hpos : 0 < s.rem o
    · rw [ite_pos_classical ⟨hpos, ho'⟩]
    · have hnot : ¬ (0 < s.rem o ∧
          s.rem o - (eatingDemand p s.rem h o : ℝ) * dt = 0) := fun hc => hpos hc.1
      rw [ite_neg_classical hnot]
      have hz : s.rem o = 0 := le_antisymm (not_lt.mp hpos) (hinv.rem_nonneg o)
      linarith [hinv.exhaust_le o hz]
  · intro i a b hpos' hlt
    rw [halloc_eq i b] at hpos'
    have hexh_old : ∀ x : Fin n, s.rem x = 0 →
        (eatingStep p s).exhaustTime x = s.exhaustTime x := by
      intro x hx
      rw [hexh_eq x]
      have hnot : ¬ (0 < s.rem x ∧
          s.rem x - (eatingDemand p s.rem h x : ℝ) * dt = 0) := fun hc => by
        rw [hx] at hc; exact lt_irrefl _ hc.1
      exact ite_neg_classical hnot
    have hexh_new : ∀ x : Fin n, 0 < s.rem x → (eatingStep p s).rem x = 0 →
        (eatingStep p s).exhaustTime x = s.elapsed + dt := by
      intro x hx hx0
      rw [hexh_eq x]
      have hx0' : s.rem x - (eatingDemand p s.rem h x : ℝ) * dt = 0 := by
        rw [← hrem_eq x]; exact hx0
      exact ite_pos_classical ⟨hx, hx0'⟩
    rcases (hinv.alloc_nonneg i b).eq_or_lt with hzero | hold
    · have hfav : favObject p s.rem h i = b := by
        by_contra hne
        simp only [← hzero, hne, ↓reduceIte, add_zero] at hpos'
        exact lt_irrefl _ hpos'
      have ha_le : s.rem a ≤ 0 := favObject_lt_le_zero p s.rem h i a (by rwa [hfav])
      have ha0 : s.rem a = 0 := le_antisymm ha_le (hinv.rem_nonneg a)
      refine ⟨hrem_zero_of_zero a ha0, fun hb0' => ?_⟩
      rw [hexh_old a ha0, hexh_new b (hfav ▸ favObject_rem_pos p s.rem h i) hb0']
      linarith [hinv.exhaust_le a ha0]
    · obtain ⟨ha0, horder⟩ := hinv.trade_order i a b hold hlt
      refine ⟨hrem_zero_of_zero a ha0, fun hb0' => ?_⟩
      rw [hexh_old a ha0]
      by_cases hb_pos : 0 < s.rem b
      · rw [hexh_new b hb_pos hb0']
        linarith [hinv.exhaust_le a ha0]
      · have hb0 : s.rem b = 0 := le_antisymm (not_lt.mp hb_pos) (hinv.rem_nonneg b)
        rw [hexh_old b hb0]
        exact horder hb0

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
      have hterm : 0 ≤ (eatingDemand p s.rem h o : ℝ) * eatingDuration p s.rem h :=
        mul_nonneg (Nat.cast_nonneg _) (eatingDuration_pos p s.rem h).le
      linarith
    · intro heq
      obtain ⟨o₀, ho_pos, ho_zero⟩ := exists_exhausted_of_eatingDuration p s.rem h
      have hmem : o₀ ∈ activeObjs (eatingStep p s) := by
        rw [heq, mem_activeObjs]; exact ho_pos
      rw [mem_activeObjs, eatingStep_pos_rem p s h o₀] at hmem
      linarith
  · left
    have hfix : eatingStep p s = s := dite_neg_classical h
    rw [hfix, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro o ho
    exact h ⟨o, (mem_activeObjs s o).mp ho⟩

private lemma eatingStep_iter_inv {n : ℕ} (p : Profile n) (k : ℕ) :
    EatingInv p ((eatingStep p)^[k] (initEatingState n)) := by
  induction k with
  | zero => exact eatingInv_init p
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact eatingInv_step p ih

private lemma eatingStep_iter_activeCard_le {n : ℕ} (p : Profile n) (k : ℕ) :
    (activeObjs ((eatingStep p)^[k] (initEatingState n))).card ≤ n - k := by
  induction k with
  | zero =>
    calc (activeObjs (initEatingState n)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := Fintype.card_fin n
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases activeCard_step_le p ((eatingStep p)^[k] (initEatingState n)) with h0 | hlt
    · omega
    · omega

private lemma eatingStep_rem_eq_zero {n : ℕ} (p : Profile n) (o : Fin n) :
    ((eatingStep p)^[n] (initEatingState n)).rem o = 0 := by
  have hle := eatingStep_iter_activeCard_le p n
  rw [Nat.sub_self] at hle
  have h0 : activeObjs ((eatingStep p)^[n] (initEatingState n)) = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
  have hnpos : ¬ 0 < ((eatingStep p)^[n] (initEatingState n)).rem o := fun h => by
    have : o ∈ (∅ : Finset (Fin n)) := h0 ▸ (mem_activeObjs _ o).mpr h
    exact (Finset.notMem_empty o) this
  exact le_antisymm (not_lt.mp hnpos) ((eatingStep_iter_inv p n).rem_nonneg o)

private lemma eatingStep_elapsed_eq_one {n : ℕ} (hn : 0 < n) (p : Profile n) :
    ((eatingStep p)^[n] (initEatingState n)).elapsed = 1 := by
  set s := (eatingStep p)^[n] (initEatingState n)
  have hinv := eatingStep_iter_inv p n
  have hsum_col : ∑ o : Fin n, (s.rem o + ∑ i : Fin n, s.alloc i o) = (n : ℝ) := by
    calc ∑ o : Fin n, (s.rem o + ∑ i : Fin n, s.alloc i o)
        = ∑ _o : Fin n, (1 : ℝ) := Finset.sum_congr rfl fun o _ => hinv.col_sum o
      _ = (n : ℝ) := by simp
  have hrem_zero : ∑ o : Fin n, s.rem o = 0 :=
    Finset.sum_eq_zero fun o _ => eatingStep_rem_eq_zero p o
  have hsum_row : ∑ o : Fin n, ∑ i : Fin n, s.alloc i o = (n : ℝ) * s.elapsed := by
    rw [Finset.sum_comm]
    calc ∑ i : Fin n, ∑ o : Fin n, s.alloc i o
        = ∑ _i : Fin n, s.elapsed := Finset.sum_congr rfl fun i _ => hinv.row_sum i
      _ = (n : ℝ) * s.elapsed := by simp
  rw [Finset.sum_add_distrib, hrem_zero, zero_add, hsum_row] at hsum_col
  have hn_ne : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  exact mul_left_cancel₀ hn_ne (by simpa [mul_one] using hsum_col)

/-- The Probabilistic Serial assignment is always a doubly stochastic matrix. -/
theorem probabilisticSerial_mem_doublyStochastic {n : ℕ} (p : Profile n) :
    probabilisticSerial p ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  have hinv := eatingStep_iter_inv p n
  refine ⟨hinv.alloc_nonneg, fun i => ?_, fun o => ?_⟩
  · have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    change ∑ o : Fin n, ((eatingStep p)^[n] (initEatingState n)).alloc i o = 1
    rw [hinv.row_sum i, eatingStep_elapsed_eq_one hn p]
  · have hcol := hinv.col_sum o
    rw [eatingStep_rem_eq_zero p o, zero_add] at hcol
    exact hcol

/-- `probabilisticSerial` is a feasible random assignment rule. -/
theorem probabilisticSerial_isFeasible {n : ℕ} :
    IsFeasible (probabilisticSerial (n := n)) :=
  fun p => probabilisticSerial_mem_doublyStochastic p

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
  refine ⟨probabilisticSerial_mem_doublyStochastic p, fun a ha => ?_⟩
  set s := (eatingStep p)^[n] (initEatingState n)
  have hinv := eatingStep_iter_inv p n
  have hmono : ∀ {x y : Fin n},
      Relation.TransGen (tradeRel p (probabilisticSerial p)) x y →
        s.exhaustTime x < s.exhaustTime y := by
    intro x y hxy
    induction hxy with
    | @single b hr =>
      obtain ⟨i, hpos, hpref⟩ := hr
      exact (hinv.trade_order i x b hpos hpref).2 (eatingStep_rem_eq_zero p b)
    | @tail b c _ hbc ih =>
      obtain ⟨i, hpos, hpref⟩ := hbc
      exact lt_trans ih ((hinv.trade_order i b c hpos hpref).2 (eatingStep_rem_eq_zero p c))
  exact lt_irrefl _ (hmono ha)

/-- Probabilistic Serial is ex-post efficient (corollary of `sd`-efficiency via Birkhoff's
theorem). -/
theorem probabilisticSerial_isExPostEfficient {n : ℕ} (p : Profile n) :
    IsExPostEfficient p (probabilisticSerial p) :=
  (probabilisticSerial_isSDEfficient p).isExPostEfficient

private lemma eatingStep_eq_self_of_rem_zero {n : ℕ} (p : Profile n) (s : EatingState n)
    (h0 : ∀ o : Fin n, s.rem o = 0) : eatingStep p s = s := by
  have hnot : ¬ ∃ o : Fin n, 0 < s.rem o := by
    rintro ⟨o, ho⟩; rw [h0 o] at ho; exact lt_irrefl _ ho
  exact dite_neg_classical hnot

private lemma eatingStep_iter_of_rem_zero {n : ℕ} (p : Profile n) (s : EatingState n)
    (h0 : ∀ o : Fin n, s.rem o = 0) (k : ℕ) : (eatingStep p)^[k] s = s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, eatingStep_eq_self_of_rem_zero p s h0, ih]

private lemma favObject_eq_of_lt_nonpos {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (i o : Fin n) (hpos : 0 < rem o)
    (hprev : ∀ a : Fin n, (p i).symm a < (p i).symm o → rem a ≤ 0) :
    favObject p rem h i = o := by
  have hle : (p i).symm (favObject p rem h i) ≤ (p i).symm o :=
    favObject_rank_le p rem h i o hpos
  have hge : ¬ (p i).symm (favObject p rem h i) < (p i).symm o := fun hlt =>
    (hprev _ hlt).not_gt (favObject_rem_pos p rem h i)
  exact (p i).symm.injective (le_antisymm hle (not_lt.mp hge))

private lemma eatingDuration_eq_of_le {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (d : ℝ)
    (hmem : ∃ o : Fin n, 0 < eatingDemand p rem h o ∧
      rem o / (eatingDemand p rem h o : ℝ) = d)
    (hle : ∀ o : Fin n, 0 < eatingDemand p rem h o →
      d ≤ rem o / (eatingDemand p rem h o : ℝ)) :
    eatingDuration p rem h = d := by
  obtain ⟨o₀, hd₀, heq₀⟩ := hmem
  refine le_antisymm ?_ ?_
  · have hmem : o₀ ∈ Finset.univ.filter fun o : Fin n => 0 < eatingDemand p rem h o :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd₀⟩
    exact (Finset.inf'_le (fun o => rem o / (eatingDemand p rem h o : ℝ)) hmem).trans_eq heq₀
  · rw [eatingDuration]
    refine Finset.le_inf' (demanded_nonempty p rem h)
      (fun o => rem o / (eatingDemand p rem h o : ℝ)) fun o ho =>
        hle o (Finset.mem_filter.mp ho).2

/-- Helper evaluating a filter cardinality via an explicit list of matching indices. -/
private lemma card_filter_eq_of_iff {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (s : Finset (Fin n)) (hs : ∀ i : Fin n, P i ↔ i ∈ s) :
    (Finset.univ.filter P).card = s.card := by
  congr 1; ext i; simp [hs i]

/-- Generalized 3-object manipulation witness profile `(a b c …, a c b …, b a c …)` padded with
dummy agents `k ≥ 3` whose top choice is object `k`. -/
@[expose] def psManipProfile {n : ℕ} (hn : 3 ≤ n) : Profile n := fun i =>
  if i.val = 0 then Equiv.refl (Fin n)
  else if i.val = 1 then Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩
  else if i.val = 2 then Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩
  else Equiv.swap ⟨0, by omega⟩ i

private lemma psManip_eq_refl {n : ℕ} (hn : 3 ≤ n) (i : Fin n) (hi : i.val = 0) :
    psManipProfile hn i = Equiv.refl (Fin n) := by
  simp [psManipProfile, hi]

private lemma psManip_eq_swap12 {n : ℕ} (hn : 3 ≤ n) (i : Fin n) (hi : i.val = 1) :
    psManipProfile hn i = Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩ := by
  simp [psManipProfile, hi]

private lemma psManip_eq_swap01 {n : ℕ} (hn : 3 ≤ n) (i : Fin n) (hi : i.val = 2) :
    psManipProfile hn i = Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  simp [psManipProfile, hi]

private lemma psManip_symm_dummy {n : ℕ} (hn : 3 ≤ n) (i : Fin n) (hi : 3 ≤ i.val) :
    (psManipProfile hn i).symm i = ⟨0, by omega⟩ := by
  have hp : psManipProfile hn i = Equiv.swap ⟨0, by omega⟩ i := by
    simp [psManipProfile, show i.val ≠ 0 by omega, show i.val ≠ 1 by omega,
      show i.val ≠ 2 by omega]
  rw [hp, Equiv.symm_apply_eq]
  simp

private lemma fav_rank_zero {n : ℕ} (p : Profile n) (rem : Fin n → ℝ)
    (h : ∃ o : Fin n, 0 < rem o) (i o : Fin n)
    (hr : (p i).symm o = ⟨0, Nat.zero_lt_of_lt i.isLt⟩) (hpos : 0 < rem o) :
    favObject p rem h i = o :=
  favObject_eq_of_lt_nonpos p rem h i o hpos fun _ ha => by
    rw [hr] at ha
    exact absurd ha (by simp [Fin.lt_def])

/-- Exact first 3 rounds of `eatingStep` on the truthful `psManipProfile hn`. -/
private lemma psManip_truthful_row2 {n : ℕ} (hn : 3 ≤ n) :
    probabilisticSerial (psManipProfile hn) ⟨2, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    probabilisticSerial (psManipProfile hn) ⟨2, by omega⟩ ⟨1, by omega⟩ = 3 / 4 ∧
    probabilisticSerial (psManipProfile hn) ⟨2, by omega⟩ ⟨2, by omega⟩ = 1 / 4 := by
  set p := psManipProfile hn
  let f0 : Fin n := ⟨0, by omega⟩
  let f1 : Fin n := ⟨1, by omega⟩
  let f2 : Fin n := ⟨2, by omega⟩
  have h01 : f0 ≠ f1 := by simp [f0, f1, Fin.ext_iff]
  have h02 : f0 ≠ f2 := by simp [f0, f2, Fin.ext_iff]
  have h12 : f1 ≠ f2 := by simp [f1, f2, Fin.ext_iff]
  let s0 := initEatingState n
  let s1 := eatingStep p s0
  let s2 := eatingStep p s1
  let s3 := eatingStep p s2
  -- Rank checks for agents 0, 1, 2
  have hp0_r : ∀ o : Fin n, (p f0).symm o = o := fun o => by
    rw [show p f0 = Equiv.refl (Fin n) from psManip_eq_refl hn f0 rfl]; rfl
  have hp1_r0 : (p f1).symm f0 = f0 := by
    rw [show p f1 = Equiv.swap f1 f2 from psManip_eq_swap12 hn f1 rfl, Equiv.symm_apply_eq]
    exact Equiv.swap_apply_of_ne_of_ne h01 h02
  have hp1_r2 : (p f1).symm f2 = f1 := by
    rw [show p f1 = Equiv.swap f1 f2 from psManip_eq_swap12 hn f1 rfl, Equiv.symm_apply_eq]
    exact Equiv.swap_apply_left f1 f2
  have hp2_r1 : (p f2).symm f1 = f0 := by
    rw [show p f2 = Equiv.swap f0 f1 from psManip_eq_swap01 hn f2 rfl, Equiv.symm_apply_eq]
    exact Equiv.swap_apply_left f0 f1
  have hp2_r2 : (p f2).symm f2 = f2 := by
    rw [show p f2 = Equiv.swap f0 f1 from psManip_eq_swap01 hn f2 rfl, Equiv.symm_apply_eq]
    exact Equiv.swap_apply_of_ne_of_ne h02.symm h12.symm
  -- Round 0
  have hex0 : ∃ o : Fin n, 0 < s0.rem o := ⟨f0, by simp [s0, initEatingState]⟩
  have hfav0 : ∀ i : Fin n, favObject p s0.rem hex0 i =
      if i.val = 0 ∨ i.val = 1 then f0 else if i.val = 2 then f1 else i := by
    intro i
    have hpos : ∀ o, (0 : ℝ) < s0.rem o := fun _ => by simp [s0, initEatingState]
    by_cases h0 : i.val = 0
    · have hi : i = f0 := Fin.ext h0; rw [hi]
      simp only [f0, true_or, ↓reduceIte]
      exact fav_rank_zero p _ hex0 f0 f0 (hp0_r f0) (hpos f0)
    · by_cases h1 : i.val = 1
      · have hi : i = f1 := Fin.ext h1; rw [hi]
        simp only [f1, or_true, ↓reduceIte]
        exact fav_rank_zero p _ hex0 f1 f0 hp1_r0 (hpos f0)
      · by_cases h2 : i.val = 2
        · have hi : i = f2 := Fin.ext h2; rw [hi]
          simp only [f2, show ¬ ((2 : ℕ) = 0 ∨ (2 : ℕ) = 1) by omega, ↓reduceIte]
          exact fav_rank_zero p _ hex0 f2 f1 hp2_r1 (hpos f1)
        · simp only [h0, h1, or_self, h2, ↓reduceIte]
          exact fav_rank_zero p _ hex0 i i (psManip_symm_dummy hn i (by omega)) (hpos i)
  have hdem0 : ∀ o : Fin n, eatingDemand p s0.rem hex0 o =
      if o.val = 0 then 2 else if o.val = 2 then 0 else 1 := by
    intro o; unfold eatingDemand; simp_rw [hfav0]
    by_cases h0 : o.val = 0
    · simp only [h0, ↓reduceIte]
      have ho : o = f0 := Fin.ext h0; rw [ho]
      rw [card_filter_eq_of_iff _ {f0, f1} (fun i => by
        split_ifs <;> simp [Fin.ext_iff, f0, f1] <;> omega), Finset.card_pair h01]
    · by_cases h2 : o.val = 2
      · rw [ite_eq_right h0, ite_eq_left h2]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _; split_ifs <;> simp [Fin.ext_iff, f0, f1] <;> omega
      · rw [ite_eq_right h0, ite_eq_right h2]
        by_cases h1 : o.val = 1
        · have ho : o = f1 := Fin.ext h1; rw [ho]
          rw [card_filter_eq_of_iff _ {f2} (fun i => by
            split_ifs <;> simp [Fin.ext_iff, f0, f1, f2] <;> omega), Finset.card_singleton]
        · rw [card_filter_eq_of_iff _ {o} (fun i => by
            split_ifs <;> simp [Fin.ext_iff, f0, f1] <;> omega), Finset.card_singleton]
  have hdt0 : eatingDuration p s0.rem hex0 = 1 / 2 := by
    refine eatingDuration_eq_of_le p _ hex0 (1 / 2)
      ⟨f0, by simp [hdem0, f0], by rw [hdem0 f0]; simp [s0, initEatingState, f0]⟩
      fun o hd => ?_
    rw [hdem0 o] at hd ⊢
    change 1 / 2 ≤ (1 : ℝ) / _
    split_ifs at hd ⊢
    · norm_num
    · omega
    · norm_num
  have hs1_rem : ∀ o : Fin n, s1.rem o =
      if o.val = 0 then 0 else if o.val = 2 then 1 else 1 / 2 := fun o => by
    rw [eatingStep_pos_rem p s0 hex0 o, hdem0 o, hdt0]
    change 1 - _ = _
    split_ifs <;> norm_num
  have hs1_a2 : ∀ o : Fin n, s1.alloc f2 o = if o.val = 1 then 1 / 2 else 0 := fun o => by
    rw [eatingStep_pos_alloc p s0 hex0 f2 o, hfav0 f2, hdt0]
    have h0a : s0.alloc f2 o = 0 := rfl
    rw [h0a, zero_add]
    simp only [f2, show ¬ ((2 : ℕ) = 0 ∨ (2 : ℕ) = 1) by omega, ↓reduceIte, Fin.ext_iff, f1]
    by_cases h1 : o.val = 1 <;> simp [h1, eq_comm]
  -- Round 1
  have hex1 : ∃ o : Fin n, 0 < s1.rem o := ⟨f2, by simp [hs1_rem, f2]⟩
  have hfav1 : ∀ i : Fin n, favObject p s1.rem hex1 i =
      if i.val = 0 ∨ i.val = 2 then f1 else if i.val = 1 then f2 else i := by
    intro i
    by_cases h0 : i.val = 0
    · have hi : i = f0 := Fin.ext h0; rw [hi]
      simp only [f0, true_or, ↓reduceIte]
      refine favObject_eq_of_lt_nonpos p _ hex1 f0 f1 (by simp [hs1_rem, f1]) ?_
      intro a ha
      rw [hp0_r a, hp0_r f1] at ha
      have ha0 : a.val = 0 := by change a.val < 1 at ha; omega
      simp [hs1_rem, ha0]
    · by_cases h2 : i.val = 2
      · have hi : i = f2 := Fin.ext h2; rw [hi]
        simp only [f2, or_true, ↓reduceIte]
        exact fav_rank_zero p _ hex1 f2 f1 hp2_r1 (by simp [hs1_rem, f1])
      · by_cases h1 : i.val = 1
        · have hi : i = f1 := Fin.ext h1; rw [hi]
          simp only [f1, show ¬ ((1 : ℕ) = 0 ∨ (1 : ℕ) = 2) by omega, ↓reduceIte]
          refine favObject_eq_of_lt_nonpos p _ hex1 f1 f2 (by simp [hs1_rem, f2]) ?_
          intro a ha
          rw [hp1_r2] at ha
          have ha_lt : ((p f1).symm a).val < 1 := ha
          have ha_eq : (p f1).symm a = (p f1).symm f0 := by
            rw [hp1_r0]; apply Fin.ext; change _ = (0 : ℕ); omega
          rw [(p f1).symm.injective ha_eq]
          simp [hs1_rem, f0]
        · simp only [h0, h2, or_self, h1, ↓reduceIte]
          exact fav_rank_zero p _ hex1 i i (psManip_symm_dummy hn i (by omega))
            (by simp [hs1_rem, h0, h2])
  have hdem1 : ∀ o : Fin n, eatingDemand p s1.rem hex1 o =
      if o.val = 0 then 0 else if o.val = 1 then 2 else 1 := by
    intro o; unfold eatingDemand; simp_rw [hfav1]
    by_cases h0 : o.val = 0
    · simp only [h0, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _; split_ifs <;> simp [Fin.ext_iff, f1, f2] <;> omega
    · by_cases h1 : o.val = 1
      · rw [ite_eq_right h0, ite_eq_left h1]
        have ho : o = f1 := Fin.ext h1; rw [ho]
        rw [card_filter_eq_of_iff _ {f0, f2} (fun i => by
          split_ifs <;> simp [Fin.ext_iff, f0, f1, f2] <;> omega), Finset.card_pair h02]
      · rw [ite_eq_right h0, ite_eq_right h1]
        by_cases h2 : o.val = 2
        · have ho : o = f2 := Fin.ext h2; rw [ho]
          rw [card_filter_eq_of_iff _ {f1} (fun i => by
            split_ifs <;> simp [Fin.ext_iff, f1, f2] <;> omega), Finset.card_singleton]
        · rw [card_filter_eq_of_iff _ {o} (fun i => by
            split_ifs <;> simp [Fin.ext_iff, f1, f2] <;> omega), Finset.card_singleton]
  have hdt1 : eatingDuration p s1.rem hex1 = 1 / 4 := by
    refine eatingDuration_eq_of_le p _ hex1 (1 / 4)
      ⟨f1, by simp [hdem1, f1], by simp [hs1_rem, hdem1, f1]; norm_num⟩
      fun o hd => ?_
    rw [hdem1 o] at hd ⊢; rw [hs1_rem o]
    by_cases h0 : o.val = 0
    · simp [h0] at hd
    · by_cases h1 : o.val = 1
      · rw [ite_eq_right h0, ite_eq_left h1, ite_eq_right h0,
          ite_eq_right (show o.val ≠ 2 by omega)]
        norm_num
      · by_cases h2 : o.val = 2 <;> simp [h0, h1, h2] <;> norm_num
  have hs2_rem : ∀ o : Fin n, s2.rem o =
      if o.val = 0 ∨ o.val = 1 then 0 else if o.val = 2 then 3 / 4 else 1 / 4 := fun o => by
    rw [eatingStep_pos_rem p s1 hex1 o, hs1_rem o, hdem1 o, hdt1]
    by_cases h0 : o.val = 0
    · simp [h0]
    · by_cases h1 : o.val = 1
      · rw [ite_eq_right h0, ite_eq_right (show o.val ≠ 2 by omega),
          ite_eq_right h0, ite_eq_left h1, ite_eq_left (Or.inr h1)]
        norm_num
      · by_cases h2 : o.val = 2 <;> simp [h0, h1, h2] <;> norm_num
  have hs2_a2 : ∀ o : Fin n, s2.alloc f2 o = if o.val = 1 then 3 / 4 else 0 := fun o => by
    rw [eatingStep_pos_alloc p s1 hex1 f2 o, hs1_a2 o, hfav1 f2, hdt1]
    simp only [f2, or_true, ↓reduceIte, Fin.ext_iff, f1]
    by_cases h1 : o.val = 1
    · simp [h1, eq_comm]; norm_num
    · simp [h1, eq_comm]
  -- Round 2
  have hex2 : ∃ o : Fin n, 0 < s2.rem o := ⟨f2, by simp [hs2_rem, f2]⟩
  have hfav2 : ∀ i : Fin n, favObject p s2.rem hex2 i = if i.val < 3 then f2 else i := by
    intro i
    by_cases hi : i.val < 3
    · simp only [hi, ↓reduceIte]
      refine favObject_eq_of_lt_nonpos p _ hex2 i f2 (by simp [hs2_rem, f2]) fun a ha => ?_
      have ha01 : a.val = 0 ∨ a.val = 1 := by
        by_cases h0 : i.val = 0
        · rw [show i = f0 from Fin.ext h0, hp0_r a, hp0_r f2] at ha
          have : a.val < 2 := ha; omega
        · by_cases h1 : i.val = 1
          · rw [show i = f1 from Fin.ext h1, hp1_r2] at ha
            have ha_lt : ((p f1).symm a).val < 1 := ha
            have heq : (p f1).symm a = (p f1).symm f0 := by
              rw [hp1_r0]; apply Fin.ext; change _ = (0 : ℕ); omega
            left; exact congrArg Fin.val ((p f1).symm.injective heq)
          · have h2 : i = f2 := Fin.ext (show i.val = 2 by omega)
            rw [h2, hp2_r2] at ha
            have ha_lt : ((p f2).symm a).val < 2 := ha
            by_contra hnot
            have ha0 : a ≠ f0 := fun h => hnot (Or.inl (congrArg Fin.val h))
            have ha1 : a ≠ f1 := fun h => hnot (Or.inr (congrArg Fin.val h))
            have hpa : (p f2).symm a = a := by
              rw [show p f2 = Equiv.swap f0 f1 from psManip_eq_swap01 hn f2 rfl,
                Equiv.symm_apply_eq]
              exact (Equiv.swap_apply_of_ne_of_ne ha0 ha1).symm
            rw [hpa] at ha_lt; omega
      simp [hs2_rem, ha01]
    · simp only [hi, ↓reduceIte]
      exact fav_rank_zero p _ hex2 i i (psManip_symm_dummy hn i (by omega))
        (by simp [hs2_rem, show ¬ (i.val = 0 ∨ i.val = 1) by omega,
          show i.val ≠ 2 by omega])
  have hdem2 : ∀ o : Fin n, eatingDemand p s2.rem hex2 o =
      if o.val = 0 ∨ o.val = 1 then 0 else if o.val = 2 then 3 else 1 := by
    intro o; unfold eatingDemand; simp_rw [hfav2]
    by_cases h01' : o.val = 0 ∨ o.val = 1
    · rw [ite_eq_left h01']
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _; split_ifs <;> simp [Fin.ext_iff, f2] <;> omega
    · by_cases h2 : o.val = 2
      · rw [ite_eq_right h01', ite_eq_left h2]
        have ho : o = f2 := Fin.ext h2; rw [ho]
        rw [card_filter_eq_of_iff _ {f0, f1, f2} (fun i => by
          split_ifs <;> simp [Fin.ext_iff, f0, f1, f2] <;> omega),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h01, h02⟩),
          Finset.card_pair h12]
      · rw [ite_eq_right h01', ite_eq_right h2]
        rw [card_filter_eq_of_iff _ {o} (fun i => by
          split_ifs
          · simp [Fin.ext_iff, f2]; omega
          · simp [Fin.ext_iff]), Finset.card_singleton]
  have hdt2 : eatingDuration p s2.rem hex2 = 1 / 4 := by
    refine eatingDuration_eq_of_le p _ hex2 (1 / 4)
      ⟨f2, by simp [hdem2, f2], by simp [hs2_rem, hdem2, f2]; norm_num⟩
      fun o hd => ?_
    rw [hdem2 o] at hd ⊢; rw [hs2_rem o]
    by_cases h01' : o.val = 0 ∨ o.val = 1
    · simp [h01'] at hd
    · by_cases h2 : o.val = 2
      · simp [h2]; norm_num
      · simp [h01', h2]
  have hs3_rem : ∀ o : Fin n, s3.rem o = 0 := fun o => by
    rw [eatingStep_pos_rem p s2 hex2 o, hs2_rem o, hdem2 o, hdt2]
    by_cases h01' : o.val = 0 ∨ o.val = 1
    · simp [h01']
    · by_cases h2 : o.val = 2
      · simp [h2]; norm_num
      · simp [h01', h2]
  have hfinal : (eatingStep p)^[n] s0 = s3 :=
    calc (eatingStep p)^[n] s0
        = (eatingStep p)^[(n - 3) + 3] s0 :=
          congrArg (fun k => (eatingStep p)^[k] s0) (by omega)
      _ = (eatingStep p)^[n - 3] ((eatingStep p)^[3] s0) := Function.iterate_add_apply _ _ _ _
      _ = s3 := eatingStep_iter_of_rem_zero p s3 hs3_rem (n - 3)
  have hs3_a2 : ∀ o : Fin n, s3.alloc f2 o =
      if o.val = 1 then 3 / 4 else if o.val = 2 then 1 / 4 else 0 := fun o => by
    rw [eatingStep_pos_alloc p s2 hex2 f2 o, hs2_a2 o, hfav2 f2, hdt2]
    have hf2_lt : f2.val < 3 := by change (2 : ℕ) < 3; omega
    rw [ite_eq_left hf2_lt]
    by_cases h1 : o.val = 1
    · have hne2 : f2 ≠ o := fun heq => by
        have := congrArg Fin.val heq; change 2 = o.val at this; omega
      rw [ite_eq_left h1, ite_eq_right hne2, add_zero, ite_eq_left h1]
    · by_cases h2 : o.val = 2
      · have heq2 : f2 = o := Fin.ext (show 2 = o.val from h2.symm)
        rw [ite_eq_right h1, ite_eq_left heq2, zero_add, ite_eq_right h1, ite_eq_left h2]
      · have hne2 : f2 ≠ o := fun heq => h2 (congrArg Fin.val heq).symm
        rw [ite_eq_right h1, ite_eq_right hne2, zero_add, ite_eq_right h1, ite_eq_right h2]
  have hs3_eval : probabilisticSerial p f2 f0 = 0 ∧
      probabilisticSerial p f2 f1 = 3 / 4 ∧ probabilisticSerial p f2 f2 = 1 / 4 := by
    change ((eatingStep p)^[n] s0).alloc f2 f0 = 0 ∧
      ((eatingStep p)^[n] s0).alloc f2 f1 = 3 / 4 ∧
      ((eatingStep p)^[n] s0).alloc f2 f2 = 1 / 4
    rw [hfinal, hs3_a2 f0, hs3_a2 f1, hs3_a2 f2]
    simp [f0, f1, f2]
  exact hs3_eval

/-- Exact first 3 rounds of `eatingStep` when agent `2` misreports `Equiv.refl (Fin n)`. -/
private lemma psManip_misreport_row2 {n : ℕ} (hn : 3 ≤ n) :
    let p' := Function.update (psManipProfile hn) ⟨2, by omega⟩ (Equiv.refl (Fin n))
    probabilisticSerial p' ⟨2, by omega⟩ ⟨0, by omega⟩ = 1 / 3 ∧
    probabilisticSerial p' ⟨2, by omega⟩ ⟨1, by omega⟩ = 1 / 2 ∧
    probabilisticSerial p' ⟨2, by omega⟩ ⟨2, by omega⟩ = 1 / 6 := by
  intro p'
  let f0 : Fin n := ⟨0, by omega⟩
  let f1 : Fin n := ⟨1, by omega⟩
  let f2 : Fin n := ⟨2, by omega⟩
  have h01 : f0 ≠ f1 := by simp [f0, f1, Fin.ext_iff]
  have h02 : f0 ≠ f2 := by simp [f0, f2, Fin.ext_iff]
  have h12 : f1 ≠ f2 := by simp [f1, f2, Fin.ext_iff]
  have hp'_ne2 : ∀ i : Fin n, i.val ≠ 2 → p' i = psManipProfile hn i := fun i hi =>
    Function.update_of_ne (fun h => hi (congrArg Fin.val h)) _ _
  have hp0_r : ∀ o : Fin n, (p' f0).symm o = o := fun o => by
    rw [hp'_ne2 f0 (by simp [f0]), psManip_eq_refl hn f0 rfl]; rfl
  have hp2_r : ∀ o : Fin n, (p' f2).symm o = o := fun o => by
    have : p' f2 = Equiv.refl (Fin n) := Function.update_self _ _ _
    rw [this]; rfl
  have hp1_r0 : (p' f1).symm f0 = f0 := by
    rw [hp'_ne2 f1 (by simp [f1]), show psManipProfile hn f1 = Equiv.swap f1 f2 from
      psManip_eq_swap12 hn f1 rfl, Equiv.symm_apply_eq]
    exact Equiv.swap_apply_of_ne_of_ne h01 h02
  have hp1_r2 : (p' f1).symm f2 = f1 := by
    rw [hp'_ne2 f1 (by simp [f1]), show psManipProfile hn f1 = Equiv.swap f1 f2 from
      psManip_eq_swap12 hn f1 rfl, Equiv.symm_apply_eq]
    exact Equiv.swap_apply_left f1 f2
  have hp'_dummy : ∀ i : Fin n, 3 ≤ i.val → (p' i).symm i = f0 := fun i hi => by
    rw [hp'_ne2 i (by omega)]; exact psManip_symm_dummy hn i hi
  let s0 := initEatingState n
  let s1 := eatingStep p' s0
  let s2 := eatingStep p' s1
  let s3 := eatingStep p' s2
  -- Round 0
  have hex0 : ∃ o : Fin n, 0 < s0.rem o := ⟨f0, by simp [s0, initEatingState]⟩
  have hfav0 : ∀ i : Fin n, favObject p' s0.rem hex0 i = if i.val < 3 then f0 else i := by
    intro i
    have hpos : ∀ o, (0 : ℝ) < s0.rem o := fun _ => by simp [s0, initEatingState]
    by_cases hi : i.val < 3
    · simp only [hi, ↓reduceIte]
      by_cases h0 : i.val = 0
      · rw [show i = f0 from Fin.ext h0]; exact fav_rank_zero p' _ hex0 f0 f0 (hp0_r f0) (hpos f0)
      · by_cases h1 : i.val = 1
        · rw [show i = f1 from Fin.ext h1]; exact fav_rank_zero p' _ hex0 f1 f0 hp1_r0 (hpos f0)
        · rw [show i = f2 from Fin.ext (show i.val = 2 by omega)]
          exact fav_rank_zero p' _ hex0 f2 f0 (hp2_r f0) (hpos f0)
    · simp only [hi, ↓reduceIte]
      exact fav_rank_zero p' _ hex0 i i (hp'_dummy i (by omega)) (hpos i)
  have hdem0 : ∀ o : Fin n, eatingDemand p' s0.rem hex0 o =
      if o.val = 0 then 3 else if o.val = 1 ∨ o.val = 2 then 0 else 1 := by
    intro o; unfold eatingDemand; simp_rw [hfav0]
    by_cases h0 : o.val = 0
    · rw [ite_eq_left h0]
      have ho : o = f0 := Fin.ext h0; rw [ho]
      rw [card_filter_eq_of_iff _ {f0, f1, f2} (fun i => by
        split_ifs <;> simp [Fin.ext_iff, f0, f1, f2] <;> omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h01, h02⟩),
        Finset.card_pair h12]
    · by_cases h12' : o.val = 1 ∨ o.val = 2
      · rw [ite_eq_right h0, ite_eq_left h12']
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _; split_ifs <;> simp [Fin.ext_iff, f0] <;> omega
      · rw [ite_eq_right h0, ite_eq_right h12']
        rw [card_filter_eq_of_iff _ {o} (fun i => by
          split_ifs
          · simp [Fin.ext_iff, f0]; omega
          · simp [Fin.ext_iff]), Finset.card_singleton]
  have hdt0 : eatingDuration p' s0.rem hex0 = 1 / 3 := by
    refine eatingDuration_eq_of_le p' _ hex0 (1 / 3)
      ⟨f0, by simp [hdem0, f0], by rw [hdem0 f0]; simp [s0, initEatingState, f0]⟩
      fun o hd => ?_
    rw [hdem0 o] at hd ⊢
    change 1 / 3 ≤ (1 : ℝ) / _
    split_ifs at hd ⊢
    · norm_num
    · omega
    · norm_num
  have hs1_rem : ∀ o : Fin n, s1.rem o =
      if o.val = 0 then 0 else if o.val = 1 ∨ o.val = 2 then 1 else 2 / 3 := fun o => by
    rw [eatingStep_pos_rem p' s0 hex0 o, hdem0 o, hdt0]
    change 1 - _ = _
    split_ifs <;> norm_num
  have hs1_a2 : ∀ o : Fin n, s1.alloc f2 o = if o.val = 0 then 1 / 3 else 0 := fun o => by
    rw [eatingStep_pos_alloc p' s0 hex0 f2 o, hfav0 f2, hdt0]
    have h0a : s0.alloc f2 o = 0 := rfl
    rw [h0a, zero_add]
    have hf2_lt : f2.val < 3 := by change (2 : ℕ) < 3; omega
    rw [ite_eq_left hf2_lt]
    by_cases h0 : o.val = 0
    · rw [ite_eq_left (Fin.ext (show 0 = o.val from h0.symm)), ite_eq_left h0]
    · rw [ite_eq_right (fun heq => h0 (congrArg Fin.val heq).symm), ite_eq_right h0]
  -- Round 1
  have hex1 : ∃ o : Fin n, 0 < s1.rem o := ⟨f1, by simp [hs1_rem, f1]⟩
  have hfav1 : ∀ i : Fin n, favObject p' s1.rem hex1 i =
      if i.val = 0 ∨ i.val = 2 then f1 else if i.val = 1 then f2 else i := by
    intro i
    by_cases h02' : i.val = 0 ∨ i.val = 2
    · rw [ite_eq_left h02']
      rcases h02' with h0 | h2
      · rw [show i = f0 from Fin.ext h0]
        refine favObject_eq_of_lt_nonpos p' _ hex1 f0 f1 (by simp [hs1_rem, f1]) fun a ha => ?_
        rw [hp0_r a, hp0_r f1] at ha
        have ha0 : a.val = 0 := by change a.val < 1 at ha; omega
        simp [hs1_rem, ha0]
      · rw [show i = f2 from Fin.ext h2]
        refine favObject_eq_of_lt_nonpos p' _ hex1 f2 f1 (by simp [hs1_rem, f1]) fun a ha => ?_
        rw [hp2_r a, hp2_r f1] at ha
        have ha0 : a.val = 0 := by change a.val < 1 at ha; omega
        simp [hs1_rem, ha0]
    · by_cases h1 : i.val = 1
      · rw [ite_eq_right h02', ite_eq_left h1]
        rw [show i = f1 from Fin.ext h1]
        refine favObject_eq_of_lt_nonpos p' _ hex1 f1 f2 (by simp [hs1_rem, f2]) fun a ha => ?_
        rw [hp1_r2] at ha
        have ha_lt : ((p' f1).symm a).val < 1 := ha
        have heq : (p' f1).symm a = (p' f1).symm f0 := by
          rw [hp1_r0]; apply Fin.ext; change _ = (0 : ℕ); omega
        rw [(p' f1).symm.injective heq]; simp [hs1_rem, f0]
      · rw [ite_eq_right h02', ite_eq_right h1]
        exact fav_rank_zero p' _ hex1 i i (hp'_dummy i (by omega))
          (by simp [hs1_rem, show i.val ≠ 0 by omega,
            show ¬ (i.val = 1 ∨ i.val = 2) by omega])
  have hdem1 : ∀ o : Fin n, eatingDemand p' s1.rem hex1 o =
      if o.val = 0 then 0 else if o.val = 1 then 2 else 1 := by
    intro o; unfold eatingDemand; simp_rw [hfav1]
    by_cases h0 : o.val = 0
    · rw [ite_eq_left h0]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _; split_ifs <;> simp [Fin.ext_iff, f1, f2] <;> omega
    · by_cases h1 : o.val = 1
      · rw [ite_eq_right h0, ite_eq_left h1]
        have ho : o = f1 := Fin.ext h1; rw [ho]
        rw [card_filter_eq_of_iff _ {f0, f2} (fun i => by
          split_ifs <;> simp [Fin.ext_iff, f0, f1, f2] <;> omega), Finset.card_pair h02]
      · rw [ite_eq_right h0, ite_eq_right h1]
        by_cases h2 : o.val = 2
        · have ho : o = f2 := Fin.ext h2; rw [ho]
          rw [card_filter_eq_of_iff _ {f1} (fun i => by
            split_ifs <;> simp [Fin.ext_iff, f1, f2] <;> omega), Finset.card_singleton]
        · rw [card_filter_eq_of_iff _ {o} (fun i => by
            split_ifs <;> simp [Fin.ext_iff, f1, f2] <;> omega), Finset.card_singleton]
  have hdt1 : eatingDuration p' s1.rem hex1 = 1 / 2 := by
    refine eatingDuration_eq_of_le p' _ hex1 (1 / 2)
      ⟨f1, by simp [hdem1, f1], by simp [hs1_rem, hdem1, f1]⟩
      fun o hd => ?_
    rw [hdem1 o] at hd ⊢; rw [hs1_rem o]
    by_cases h0 : o.val = 0
    · simp [h0] at hd
    · by_cases h1 : o.val = 1
      · rw [ite_eq_right h0, ite_eq_left h1, ite_eq_right h0, ite_eq_left (Or.inl h1)]; norm_num
      · by_cases h2 : o.val = 2 <;> simp [h0, h1, h2] <;> norm_num
  have hs2_rem : ∀ o : Fin n, s2.rem o =
      if o.val = 0 ∨ o.val = 1 then 0 else if o.val = 2 then 1 / 2 else 1 / 6 := fun o => by
    rw [eatingStep_pos_rem p' s1 hex1 o, hs1_rem o, hdem1 o, hdt1]
    by_cases h0 : o.val = 0
    · simp [h0]
    · by_cases h1 : o.val = 1
      · rw [ite_eq_right h0, ite_eq_left (Or.inl h1), ite_eq_right h0,
          ite_eq_left h1, ite_eq_left (Or.inr h1)]
        norm_num
      · by_cases h2 : o.val = 2 <;> simp [h0, h1, h2] <;> norm_num
  have hs2_a2 : ∀ o : Fin n, s2.alloc f2 o =
      if o.val = 0 then 1 / 3 else if o.val = 1 then 1 / 2 else 0 := fun o => by
    rw [eatingStep_pos_alloc p' s1 hex1 f2 o, hs1_a2 o, hfav1 f2, hdt1]
    simp only [f2, or_true, ↓reduceIte, Fin.ext_iff, f1]
    by_cases h0 : o.val = 0
    · simp [h0]
    · by_cases h1 : o.val = 1 <;> simp [h0, h1, eq_comm]
  -- Round 2
  have hex2 : ∃ o : Fin n, 0 < s2.rem o := ⟨f2, by simp [hs2_rem, f2]⟩
  have hfav2 : ∀ i : Fin n, favObject p' s2.rem hex2 i = if i.val < 3 then f2 else i := by
    intro i
    by_cases hi : i.val < 3
    · simp only [hi, ↓reduceIte]
      refine favObject_eq_of_lt_nonpos p' _ hex2 i f2 (by simp [hs2_rem, f2]) fun a ha => ?_
      have ha01 : a.val = 0 ∨ a.val = 1 := by
        by_cases h0 : i.val = 0
        · rw [show i = f0 from Fin.ext h0, hp0_r a, hp0_r f2] at ha
          have : a.val < 2 := ha; omega
        · by_cases h1 : i.val = 1
          · rw [show i = f1 from Fin.ext h1, hp1_r2] at ha
            have ha_lt : ((p' f1).symm a).val < 1 := ha
            have heq : (p' f1).symm a = (p' f1).symm f0 := by
              rw [hp1_r0]; apply Fin.ext; change _ = (0 : ℕ); omega
            left; exact congrArg Fin.val ((p' f1).symm.injective heq)
          · rw [show i = f2 from Fin.ext (show i.val = 2 by omega), hp2_r a, hp2_r f2] at ha
            have : a.val < 2 := ha; omega
      simp [hs2_rem, ha01]
    · simp only [hi, ↓reduceIte]
      exact fav_rank_zero p' _ hex2 i i (hp'_dummy i (by omega))
        (by simp [hs2_rem, show ¬ (i.val = 0 ∨ i.val = 1) by omega,
          show i.val ≠ 2 by omega])
  have hdem2 : ∀ o : Fin n, eatingDemand p' s2.rem hex2 o =
      if o.val = 0 ∨ o.val = 1 then 0 else if o.val = 2 then 3 else 1 := by
    intro o; unfold eatingDemand; simp_rw [hfav2]
    by_cases h01' : o.val = 0 ∨ o.val = 1
    · rw [ite_eq_left h01']
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _; split_ifs <;> simp [Fin.ext_iff, f2] <;> omega
    · by_cases h2 : o.val = 2
      · rw [ite_eq_right h01', ite_eq_left h2]
        have ho : o = f2 := Fin.ext h2; rw [ho]
        rw [card_filter_eq_of_iff _ {f0, f1, f2} (fun i => by
          split_ifs <;> simp [Fin.ext_iff, f0, f1, f2] <;> omega),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h01, h02⟩),
          Finset.card_pair h12]
      · rw [ite_eq_right h01', ite_eq_right h2]
        rw [card_filter_eq_of_iff _ {o} (fun i => by
          split_ifs
          · simp [Fin.ext_iff, f2]; omega
          · simp [Fin.ext_iff]), Finset.card_singleton]
  have hdt2 : eatingDuration p' s2.rem hex2 = 1 / 6 := by
    refine eatingDuration_eq_of_le p' _ hex2 (1 / 6)
      ⟨f2, by simp [hdem2, f2], by simp [hs2_rem, hdem2, f2]; norm_num⟩
      fun o hd => ?_
    rw [hdem2 o] at hd ⊢; rw [hs2_rem o]
    by_cases h01' : o.val = 0 ∨ o.val = 1
    · simp [h01'] at hd
    · by_cases h2 : o.val = 2
      · simp [h2]; norm_num
      · simp [h01', h2]
  have hs3_rem : ∀ o : Fin n, s3.rem o = 0 := fun o => by
    rw [eatingStep_pos_rem p' s2 hex2 o, hs2_rem o, hdem2 o, hdt2]
    by_cases h01' : o.val = 0 ∨ o.val = 1
    · simp [h01']
    · by_cases h2 : o.val = 2
      · simp [h2]; norm_num
      · simp [h01', h2]
  have hfinal : (eatingStep p')^[n] s0 = s3 :=
    calc (eatingStep p')^[n] s0
        = (eatingStep p')^[(n - 3) + 3] s0 :=
          congrArg (fun k => (eatingStep p')^[k] s0) (by omega)
      _ = (eatingStep p')^[n - 3] ((eatingStep p')^[3] s0) := Function.iterate_add_apply _ _ _ _
      _ = s3 := eatingStep_iter_of_rem_zero p' s3 hs3_rem (n - 3)
  have hs3_a2 : ∀ o : Fin n, s3.alloc f2 o =
      if o.val = 0 then 1 / 3 else if o.val = 1 then 1 / 2 else if o.val = 2 then 1 / 6 else 0 :=
    fun o => by
      rw [eatingStep_pos_alloc p' s2 hex2 f2 o, hs2_a2 o, hfav2 f2, hdt2]
      have hf2_lt : f2.val < 3 := by change (2 : ℕ) < 3; omega
      rw [ite_eq_left hf2_lt]
      by_cases h0 : o.val = 0
      · have hne2 : f2 ≠ o := fun heq => by
          have := congrArg Fin.val heq; change 2 = o.val at this; omega
        rw [ite_eq_left h0, ite_eq_right hne2, add_zero, ite_eq_left h0]
      · by_cases h1 : o.val = 1
        · have hne2 : f2 ≠ o := fun heq => by
            have := congrArg Fin.val heq; change 2 = o.val at this; omega
          rw [ite_eq_right h0, ite_eq_left h1, ite_eq_right hne2, add_zero,
            ite_eq_right h0, ite_eq_left h1]
        · by_cases h2 : o.val = 2
          · have heq2 : f2 = o := Fin.ext (show 2 = o.val from h2.symm)
            rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left heq2, zero_add,
              ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
          · have hne2 : f2 ≠ o := fun heq => h2 (congrArg Fin.val heq).symm
            rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right hne2, zero_add,
              ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]
  change ((eatingStep p')^[n] s0).alloc f2 f0 = 1 / 3 ∧
    ((eatingStep p')^[n] s0).alloc f2 f1 = 1 / 2 ∧
    ((eatingStep p')^[n] s0).alloc f2 f2 = 1 / 6
  rw [hfinal, hs3_a2 f0, hs3_a2 f1, hs3_a2 f2]
  simp [f0, f1, f2]

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
  set p := psManipProfile hn
  have hdom := hsp p ⟨2, by omega⟩ (Equiv.refl (Fin n)) ⟨1, by omega⟩
  have hiic : Finset.Iic (⟨1, by omega⟩ : Fin n) =
      {⟨0, by omega⟩, ⟨1, by omega⟩} := by
    ext r
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
    omega
  have hp2 : p ⟨2, by omega⟩ = Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ :=
    psManip_eq_swap01 hn ⟨2, by omega⟩ rfl
  have hsum : ∀ x : Fin n → ℝ,
      upperContourSum (p ⟨2, by omega⟩) x ⟨1, by omega⟩ =
        x ⟨1, by omega⟩ + x ⟨0, by omega⟩ := by
    intro x
    unfold upperContourSum
    rw [hiic, Finset.sum_pair (by simp [Fin.ext_iff]), hp2]
    simp
  rw [hsum, hsum] at hdom
  obtain ⟨⟨ht0, ht1, _⟩, ⟨hm0, hm1, _⟩⟩ := probabilisticSerial_manip_values hn
  rw [ht0, ht1, hm0, hm1] at hdom
  linarith

end Cslib.GameTheory.RandomAssignment
