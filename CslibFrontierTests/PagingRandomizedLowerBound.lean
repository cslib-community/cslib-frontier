/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Paging.FIFO
public import CslibFrontier.DataStructure.Paging.LowerBound
public import CslibFrontier.DataStructure.Paging.RandomizedLowerBound
import CslibFrontier.Probability.PMF
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# Tests for FIFO/LIFO Paging and the `H_k` Randomized Paging Lower Bound

Kernel-checked traces (`decide` + `norm_num`, zero `native_decide`) separating FIFO from LRU on
cache hits, witnessing exact `k`-competitiveness of `fifoStrategy` and the `k = 1` vs `k ≥ 2`
competitiveness threshold of `lifoStrategy`, instantiating FKLMSY's `H_k` lower bound on both
`BehavioralStrategy` (`markingStrategy`) and a concrete non-degenerate `RandStrategy` mixture of
LRU and FIFO, and contrasting `markingStrategy`'s `(3 / 2, 0)`-competitiveness on `Fin 3` against
its failure to be `(3 / 2, b)`-competitive on `Fin 4` at `k = 2`.
-/

public section

namespace CslibFrontierTests.PagingRandomizedLowerBound

open Cslib.DataStructure.Online Cslib.DataStructure.Paging
open scoped ENNReal

/-! ### FIFO vs. LRU trace separation and tight `k`-competitiveness -/

/-- Accessing resident page `1` on `[2, 1]` leaves FIFO's arrival order `[2, 1]` unchanged (unlike
LRU, which promotes `1` to `[1, 2]`), so a subsequent miss on `3` evicts `1` under FIFO (`[3, 2]`)
rather than `2` (`[3, 1]` under LRU). -/
example :
    fifoRun 2 [2, 1] [1, 3] = [3, 2] ∧
      lruRun 2 [2, 1] [1, 3] = [3, 1] := by
  decide

/-- Belady's trace `[1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5]` from empty cache at capacities `3` and `4`
exhibits Belady's anomaly for FIFO (`9 < 10` faults), while both capacities still obey Sleator and
Tarjan's `k * OPT` bound. -/
example :
    let belady : List Nat := [1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5]
    fifoFaults 3 [] belady = 9 ∧ fifoFaults 4 [] belady = 10 := by
  decide

/-- Tightness synthesis for `fifoStrategy`: for every `0 < k`, `fifoStrategy` on `Fin (k + 1)` is
`(k, 0)`-competitive from shared initial caches, `(k, k)`-competitive across arbitrary initial
caches, and cannot be `(k - 1, b)`-competitive from `∅`. -/
theorem fifo_tight_competitive_ratio (k : Nat) (hk : 0 < k) (b : Nat) :
    (fifoStrategy (α := Fin (k + 1)) k hk).IsCompetitive k 0 ∧
      (fifoStrategy (α := Fin (k + 1)) k hk).IsCompetitiveAnyInit k k ∧
      ¬ (fifoStrategy (α := Fin (k + 1)) k hk).IsCompetitiveFrom ∅ (k - 1) b :=
  ⟨fifoStrategy_isCompetitive k hk,
    fifoStrategy_isCompetitiveAnyInit k hk,
    fin_not_isCompetitiveFrom_empty_of_lt hk (fifoStrategy k hk) (by omega) b⟩

/-! ### LIFO `k = 1` vs. `k ≥ 2` sharp threshold -/

/-- At `k = 1`, `lifoStrategy` IS `(1, 0)`-competitive, whereas at `k = 2` on `Fin 3` it fails
`(c, b)`-competitiveness from `∅` for every `c, b : Nat`. -/
theorem lifo_sharp_threshold (c b : Nat) :
    (lifoStrategy (α := Fin 2) 1 (by omega)).IsCompetitive 1 0 ∧
      ¬ (lifoStrategy (α := Fin 3) 2 (by omega)).IsCompetitiveFrom ∅ c b :=
  ⟨lifoStrategy_one_isCompetitive,
    fin_lifo_not_isCompetitiveFrom_empty (k := 2) (by omega) c b⟩

/-- Concrete trace of `lifoCounterexample [0] 1 2 2` at `k = 2`: LIFO faults on all `7` requests
while an offline capacity-`2` schedule faults only `3` times. -/
example :
    lifoFaults 2 [] (lifoCounterexample [0] 1 2 2) = 7 ∧
      ∃ offStates,
        (problem Nat 2).ValidSchedule ∅ (lifoCounterexample [0] 1 2 2) offStates ∧
          (problem Nat 2).scheduleCost ∅ (lifoCounterexample [0] 1 2 2) offStates = 3 :=
  ⟨by decide, exists_offline_lifoCounterexample (k := 2) (by omega) rfl (by decide) 2⟩

/-! ### Non-vacuous `H_k` lower bounds and `(k + 1)`-page tightness -/

/-- At `k = 2` (`H_2 = 3 / 2`), on `Fin 3`, `markingStrategy 2` achieves exact `(3 / 2, 0)`
competitiveness, while NO `BehavioralStrategy` (including `markingStrategy 2` itself) can achieve
`(7 / 5, b)`-competitiveness (`7 / 5 < 3 / 2`) from `∅` for any finite `b`. -/
theorem marking_two_tight_fin3 {b : ℝ≥0∞} (hb : b ≠ ⊤) :
    (markingStrategy (α := Fin 3) 2 (by omega)).IsCompetitive (3 / 2) 0 ∧
      ¬ (markingStrategy (α := Fin 3) 2 (by omega)).IsCompetitiveFrom ∅ (7 / 5) b := by
  have hH2 : ENNReal.ofReal (harmonic 2) = (3 : ℝ≥0∞) / 2 := by
    have hq : (harmonic 2 : ℝ) = 3 / 2 := by
      simp only [harmonic_succ, harmonic_zero]
      norm_num
    rw [hq, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  obtain ⟨hcomp, hlb⟩ := markingStrategy_tight_on_fin_succ (k := 2) (by omega)
  rw [hH2] at hcomp
  refine ⟨hcomp, hlb (markingStrategy 2 (by omega)) ?_ hb⟩
  rw [hH2]
  have h75 : ((7 : ℝ≥0∞) / 5) = ENNReal.ofReal (7 / 5) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  have h32 : ((3 : ℝ≥0∞) / 2) = ENNReal.ofReal (3 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  rw [h75, h32]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Concrete non-degenerate `RandStrategy` mixture (uniform coin flip between `lruStrategy 3` and
`fifoStrategy 3` on `Fin 4`, where `H_3 = 11 / 6`): cannot achieve `(9 / 5, b)`-competitiveness
(`9 / 5 = 54 / 30 < 55 / 30 = 11 / 6`) from `∅` for any finite `b`. -/
noncomputable def lruFifoMixture : RandStrategy (problem (Fin 4) 3) :=
  (Cslib.Probability.PMF.uniformOfFintype Bool).map fun coin =>
    if coin then lruStrategy 3 (by omega) else fifoStrategy 3 (by omega)

theorem lruFifoMixture_not_competitive_nine_fifths {b : ℝ≥0∞} (hb : b ≠ ⊤) :
    ¬ lruFifoMixture.IsCompetitiveFrom ∅ (9 / 5) b := by
  refine fin_not_isCompetitiveFrom_empty_rand_of_lt (k := 3) (n := 4) (by omega) (by omega)
    lruFifoMixture ?_ hb
  have hH3 : (harmonic 3 : ℝ) = 11 / 6 := by
    simp only [harmonic_succ, harmonic_zero]
    norm_num
  have h95 : ((9 : ℝ≥0∞) / 5) = ENNReal.ofReal (9 / 5) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  rw [hH3, h95]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Separation between `n = 3` and `n = 4` for `markingStrategy 2`:
on `Fin 3` (`n = k + 1`), `markingStrategy 2` IS `(H_2, 0)`-competitive, whereas on `Fin 4`
(`n = k + 2`), `markingStrategy 2` is NOT `(H_2, b)`-competitive for any finite `b` (though it
remains `(2 * H_2, 0)`-competitive by FKLMSY Theorem 1). -/
theorem marking_two_fin3_vs_fin4 {b : ℝ≥0∞} (hb : b ≠ ⊤) :
    (markingStrategy (α := Fin 3) 2 (by omega)).IsCompetitive (ENNReal.ofReal (harmonic 2)) 0 ∧
      ¬ (markingStrategy (α := Fin 4) 2 (by omega)).IsCompetitive (ENNReal.ofReal (harmonic 2)) b ∧
      (markingStrategy (α := Fin 4) 2 (by omega)).IsCompetitive
        (2 * ENNReal.ofReal (harmonic 2)) 0 :=
  ⟨markingStrategy_isCompetitive_of_card_le (by omega) (by simp),
    markingStrategy_not_isCompetitive_harmonic_two_fin_four hb,
    markingStrategy_isCompetitive (by omega)⟩

end CslibFrontierTests.PagingRandomizedLowerBound
