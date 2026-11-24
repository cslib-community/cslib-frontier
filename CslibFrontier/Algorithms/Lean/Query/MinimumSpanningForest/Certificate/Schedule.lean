/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.History
public import CslibFrontier.Foundations.Combinatorics.FewBadRounds
import Mathlib.Tactic.FieldSimp

/-!
# The schedule of the certificate procedure

The deterministic schedule of [Khanna, Putterman and Song][KhannaPuttermanSong2026] (§3.4,
Lemma 3.11, p. 21) for the program `Cslib.Query.Certificate.certificate`. This is a step in the
proof of [KhannaPuttermanSong2026] Theorem 4.1 (#8325), not a result of its own.

The schedule `Cslib.Query.Certificate.schedule γ hγ inst` assigns each edge of the instance one of
the `t²` rounds. It is chosen, by classical choice and without any comparison, from M5's
`Cslib.exists_schedule_few_bad_rounds` applied to the family of histories of Lemma 3.10
(`Cslib.Query.Certificate.histories`), with the bad rounds of Definition 3.4 read off each history
(`Cslib.Query.Certificate.badRounds`, at most `2t` of them by
`Cslib.Query.Certificate.card_badRound_le`). Since the family depends only on the instance, so
does the schedule, as `Cslib.Query.Certificate.Config.sched` requires.

The actual history is in the family (`Cslib.Query.Certificate.history_mem_histories`), so in the
actual run at most `(log |𝓗| + 2m/t) / log 2` edges act in one of their bad rounds
(`Cslib.Query.Certificate.card_badRound_schedule_mul_log_two_le`), whatever the estimator.

## Main definitions

* `Cslib.Query.Certificate.badRounds`, `Cslib.Query.Certificate.schedule`.

## Main results

* `Cslib.Query.Certificate.card_badRound_schedule_mul_log_two_le`: **Lemma 3.11** for the run.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.4, p. 21.
-/

public section

namespace Cslib.Query.Certificate

open Finset

variable {V E W : Type} [DecidableEq V] [DecidableEq E]

open scoped Classical in
/-- The **bad rounds** of `e` in the history `h` of `t²` rounds (Definition 3.4, p. 17): the rounds
that are bad for the preferences of `e` recorded in `h`. -/
noncomputable def badRounds (t : ℕ) (h : Fin (t ^ 2) → HistoryRound V E) (e : E) :
    Finset (Fin (t ^ 2)) :=
  {i | BadRound t (fun j => if hj : j < t ^ 2 then (h ⟨j, hj⟩).pref e else .find) i}

omit [DecidableEq V] [DecidableEq E] in
/-- A history has at most `2t` bad rounds for each edge (Definition 3.4, p. 17). -/
theorem card_badRounds_le (t : ℕ) (h : Fin (t ^ 2) → HistoryRound V E) (e : E) :
    #(badRounds t h e) ≤ 2 * t := by
  classical
  set a : ℕ → Action := fun j => if hj : j < t ^ 2 then (h ⟨j, hj⟩).pref e else .find
  refine le_trans ?_ (card_badRound_le t a)
  refine card_le_card_of_injOn (fun i => (i : ℕ)) (fun i hi => ?_) (fun i _ j _ hij => Fin.ext hij)
  simp only [badRounds, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi
  simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
  exact ⟨i.2, hi⟩

/-- Bad rounds depend only on the preferences in the `t²` rounds. -/
private theorem badRound_congr {t : ℕ} {a b : ℕ → Action} (hab : ∀ j < t ^ 2, a j = b j) {i : ℕ}
    (hi : i < t ^ 2) : BadRound t a i ↔ BadRound t b i := by
  have key : ∀ j, j / t = i / t → j < t ^ 2 := fun j hj => by
    rcases Nat.eq_zero_or_pos t with ht | ht
    · simp [ht] at hi
    have : i / t < t := Nat.div_lt_of_lt_mul (by rw [sq] at hi; exact hi)
    rw [sq]
    exact (Nat.div_lt_iff_lt_mul ht).1 (hj ▸ this)
  unfold BadRound
  rw [hab i hi]
  refine or_congr (and_congr_right fun _ => forall_congr' fun j => ?_)
    (and_congr_right fun _ => forall_congr' fun j => ?_)
  · exact imp_congr_right fun _ => imp_congr_right fun hj => by rw [hab j (key j hj)]
  · exact imp_congr_right fun hj => imp_congr_right fun _ => by rw [hab j hj]

omit [DecidableEq V] [DecidableEq E] in
private theorem levelT_sq_pos {γ : ℕ} (hγ : 0 < γ) (d : ℕ+) : 0 < levelT γ d ^ 2 := by
  unfold levelT
  have := d.pos
  positivity

/-- **The schedule** (Lemma 3.11, p. 21): a schedule that puts few edges in their bad rounds for
every history of `Cslib.Query.Certificate.histories γ inst` at once, chosen by M5's
`Cslib.exists_schedule_few_bad_rounds`. It depends only on `γ` and the instance, so it costs no
comparisons (p. 21: "we can enumerate all possible schedules and check all possible histories").
-/
noncomputable def schedule (γ : ℕ) (hγ : 0 < γ) (inst : Instance V E) :
    E → Fin (levelT γ inst.level ^ 2) :=
  haveI : Nonempty (Fin (levelT γ inst.level ^ 2)) := ⟨⟨0, levelT_sq_pos hγ inst.level⟩⟩
  (exists_schedule_few_bad_rounds inst.edges (histories γ inst) (badRounds (levelT γ inst.level))
    (B := 2 * levelT γ inst.level) fun h _ e _ => card_badRounds_le _ h e).choose

variable [LinearOrder W] {cfg : Config V E} {w : E → W}

open scoped Classical in
/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): the schedule bound,
Lemma 3.11 (§3.4, p. 21), for the run. When the configuration uses
`Cslib.Query.Certificate.schedule`, at most `(log |𝓗| + 2m/t) / log 2` edges of a call act in one
of their bad rounds, where `𝓗 = histories γ inst` is the family of Lemma 3.10. Any estimator and
any correct exact minimum spanning forest subroutine may be used. -/
theorem card_badRound_schedule_mul_log_two_le (hw : Function.Injective w)
    (hmsf : cfg.ExactMsf w) {inst : Instance V E} (hwf : inst.WellFormed) (hγ : 0 < cfg.γ)
    (hs : cfg.sched = schedule cfg.γ hγ) :
    (#{e ∈ inst.edges | BadRound (levelT cfg.γ inst.level) (prefSeq cfg w inst e)
        (cfg.sched inst e)} : ℝ) * Real.log 2 ≤
      Real.log #(histories cfg.γ inst) + 2 * #inst.edges / levelT cfg.γ inst.level := by
  set t := levelT cfg.γ inst.level
  have : Nonempty (Fin (t ^ 2)) := ⟨⟨0, levelT_sq_pos hγ inst.level⟩⟩
  have hspec := (exists_schedule_few_bad_rounds inst.edges (histories cfg.γ inst)
    (badRounds t) (B := 2 * t) fun h _ e _ => card_badRounds_le _ h e).choose_spec
    (history cfg w inst) (history_mem_histories cfg w hw hmsf hwf)
  have hfilter : {e ∈ inst.edges | BadRound t (prefSeq cfg w inst e) (cfg.sched inst e)} =
      {e ∈ inst.edges | schedule cfg.γ hγ inst e ∈ badRounds t (history cfg w inst) e} := by
    refine filter_congr fun e he => ?_
    rw [hs]
    simp only [badRounds, mem_filter, mem_univ, true_and]
    refine badRound_congr (fun j hj => ?_) (schedule cfg.γ hγ inst e).2
    simp only [hj, ↓reduceDIte]
    exact (pref_history_of_mem cfg w ⟨j, hj⟩ he).symm
  rw [hfilter]
  refine hspec.trans_eq ?_
  have ht : (0 : ℝ) < t := by
    have := levelT_sq_pos hγ inst.level
    exact_mod_cast Nat.pos_of_ne_zero fun h => by simp [t, h] at this
  rw [Fintype.card_fin]
  change _ = Real.log _ + 2 * (#inst.edges : ℝ) / (t : ℝ)
  push_cast
  field_simp

end Cslib.Query.Certificate
