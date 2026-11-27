/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.AcceptCount
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.BitString.List.Vote
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Probability.MajorityVote
import Mathlib.Tactic.Linarith

/-!
# Error counts for strict majority of independent seeded decisions

The bound is pointwise in the input, the seed length, the expected answer, and the number
of repetitions. Clients can choose the repetition count separately for each input.

## Main results

* `Cslib.Complexity.acceptCount_listStrictMajority_ne_le`: the strict-majority error count
  for consecutive independent seed blocks.
-/

public section

namespace Cslib.Complexity

open Cslib.BitString

/-- If one seeded answer disagrees with `truth` on at most an `ε < 1 / 2` fraction of seeds,
strict majority of `2 * r` independent blocks disagrees on at most a
`(4 * ε * (1 - ε)) ^ r` fraction. Ties are counted as potential errors for either answer. -/
theorem acceptCount_listStrictMajority_ne_le {α : Type} (V : α × List Bool → Bool)
    (a : α) (n r : ℕ) (truth : Bool) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2)
    (herr : (acceptCount (fun p => V p != truth) a n : ℝ) ≤ ε * (2 : ℝ) ^ n) :
    (acceptCount (fun p =>
      listStrictMajority ((listRows (2 * r) n p.2).map fun w => V (p.1, w)) != truth)
      a ((2 * r) * n) : ℝ) ≤ (4 * ε * (1 - ε)) ^ r * (2 : ℝ) ^ ((2 * r) * n) := by
  let G : Finset (Fin n → Bool) := Finset.univ.filter fun u => V (a, List.ofFn u) = truth
  have hsum : (G.card : ℝ) + acceptCount (fun p => V p != truth) a n = (2 : ℝ) ^ n := by
    exact_mod_cast (show G.card + acceptCount (fun p => V p != truth) a n = 2 ^ n from by
      simpa only [G, acceptCount, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne,
        bne_iff_ne] using
        acceptCount_add_acceptCount_not (fun p => V p == truth) a n)
  have hG : (1 - ε) * (2 : ℝ) ^ n ≤ G.card := by linarith
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by simp
  have hmajority := card_filter_card_filter_le_of_err_lt_half G hε0 hε1 (hcard ▸ hG) r
  rw [hcard, ← pow_mul, mul_comm n] at hmajority
  refine le_trans ?_ hmajority
  apply Nat.cast_le.mpr
  rw [acceptCount, ← Finset.card_map BitString.blocksEquiv.toEmbedding]
  refine Finset.card_le_card fun ω hω => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hω
  have hwrong : listStrictMajority ((listRows (2 * r) n (List.ofFn x)).map
      fun w => V (a, w)) ≠ truth := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, bne_iff_ne] using hx
  have hmargin := le_of_not_gt (mt (listStrictMajority_eq_of_pos (truth := truth)) hwrong)
  rw [listRows_ofFn, List.map_ofFn] at hmargin
  have hcount :
      ((List.ofFn fun i : Fin (2 * r) => V (a, List.ofFn (block x i))).count truth) =
        (Finset.univ.filter fun i => BitString.blocksEquiv.toEmbedding x i ∈ G).card := by
    simp only [List.count_eq_countP, List.countP_ofFn, beq_iff_eq, G, Finset.mem_filter,
      Finset.mem_univ, true_and, Equiv.toEmbedding_apply, BitString.blocksEquiv_apply]
  simp only [Function.comp_def, listVoteMargin, List.length_ofFn, hcount] at hmargin
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact_mod_cast (show ((Finset.univ.filter
    fun i => BitString.blocksEquiv.toEmbedding x i ∈ G).card : ℝ) ≤ r from by
      push_cast at hmargin
      linarith)

end Cslib.Complexity
