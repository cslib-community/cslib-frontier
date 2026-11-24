/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Linear
public import CslibFrontier.Algorithms.Lean.Query.FreeM.LiftM
import CslibFrontier.Algorithms.Lean.Query.FreeM.CostHom

/-!
# Minimum spanning forests with tied weights

[Khanna, Putterman and Song][KhannaPuttermanSong2026] assume distinct weights, with ties broken
by edge index (§2, p. 11). This file carries Theorem 4.1 over to arbitrary weights by that
convention. With edges in a linear order, `Cslib.Query.tieBreak` answers a comparison of the pairs
`(w a, a)` and `(w b, b)` in the lexicographic order by at most two comparisons of weights and a
free comparison of indices. Running Algorithm 2 (`Cslib.Query.linearMsf`) through it gives
`Cslib.Query.linearMsfTies`, which uses only comparisons `w a ≤ w b`, at most `2 C m` of them,
and returns the minimum spanning forest for the tie-broken weights, which is a spanning forest of
least total weight (`Cslib.Multigraph.sum_msf_le_of_monotone`).

## Main definitions

* `Cslib.Query.tieBreak`: lexicographic comparisons by weight, then index.
* `Cslib.Query.linearMsfTies`: Algorithm 2 for tied weights.

## Main results

* `Cslib.Query.eval_linearMsfTies`: it computes the minimum spanning forest of the tie-broken
  weights.
* `Cslib.Query.linearMsfTies_isSpanningForest_and_sum_le_and_countQueries_le`: a minimum-weight
  spanning forest with at most `2 C m` weight comparisons.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §2, p. 11, and §4, p. 25.
-/

public section

namespace Cslib.Query

open Finset Multigraph

variable {V E : Type} [DecidableEq V] [LinearOrder E]

/-- **Tie-breaking by edge index** (§2, p. 11): answer a comparison of the pairs `(w a, a)` and
`(w b, b)` in the lexicographic order by at most two comparisons of weights, `w a ≤ w b` and
`w b ≤ w a`, and a comparison of the indices `a ≤ b`, which is free since it does not involve the
weights. -/
def tieBreak : {ι : Type} → LEQuery E ι → FreeM (LEQuery E) ι
  | _, .le a b => do
    if ← LEQuery.ask a b then
      if ← LEQuery.ask b a then pure (decide (a ≤ b)) else pure true
    else pure false

/-- Against the comparison oracle of `w`, `Cslib.Query.tieBreak` answers as the comparison oracle
of the tie-broken weights `e ↦ (w e, e)`, ordered lexicographically. -/
theorem eval_tieBreak {W : Type} [LinearOrder W] (w : E → W) :
    (fun {ι} (q : LEQuery E ι) => (tieBreak q).eval (LEQuery.keyOracle w)) =
      fun {ι} (q : LEQuery E ι) => LEQuery.keyOracle (fun e => toLex (w e, e)) q := by
  funext ι q
  cases q with
  | le a b =>
    simp only [tieBreak, FreeM.eval_bind, LEQuery.eval_ask, LEQuery.keyOracle_le,
      Prod.Lex.toLex_le_toLex]
    by_cases hab : w a ≤ w b
    · by_cases hba : w b ≤ w a
      · simp [le_antisymm hab hba]
      · simp [hab, hba, lt_of_not_ge hba]
    · simp only [hab, decide_false, Bool.false_eq, Bool.true_eq_false, ↓reduceIte,
        FreeM.eval_pure]
      refine decide_eq_false fun (h : w a < w b ∨ w a = w b ∧ a ≤ b) => ?_
      rcases h with h | ⟨h, -⟩
      · exact hab h.le
      · exact hab h.le

/-- `Cslib.Query.tieBreak` makes at most two comparisons. -/
theorem countQueries_tieBreak_le (oracle : {ι : Type} → LEQuery E ι → ι) {ι : Type}
    (q : LEQuery E ι) : (tieBreak q).countQueries oracle ≤ 2 := by
  cases q with
  | le a b =>
    simp only [tieBreak, FreeM.countQueries_bind, LEQuery.ask, FreeM.countQueries_lift]
    split <;> simp only [FreeM.countQueries_pure, FreeM.countQueries_bind,
      FreeM.countQueries_lift, apply_ite, ite_self] <;> omega

/-- **Algorithm 2 for tied weights** (§2, p. 11): Algorithm 2 on the tie-broken weights
`e ↦ (w e, e)`, each of its comparisons simulated by `Cslib.Query.tieBreak` with at most two
comparisons of the weights `w` and a free comparison of edge indices. -/
noncomputable def linearMsfTies (ends : E → Sym2 V) (S : Finset E) :
    FreeM (LEQuery E) (Finset E) :=
  (linearMsf linearMsfSteps ends S).liftM tieBreak

/-- `Cslib.Query.linearMsfTies` computes the minimum spanning forest for the tie-broken weights
`e ↦ (w e, e)`, for arbitrary weights `w` in a linear order. -/
theorem eval_linearMsfTies {W : Type} [LinearOrder W] (w : E → W) (ends : E → Sym2 V)
    (S : Finset E) :
    (linearMsfTies ends S).eval (LEQuery.keyOracle w) = msf ends (fun e => toLex (w e, e)) S := by
  rw [linearMsfTies, FreeM.eval_liftM, eval_tieBreak]
  exact eval_linearMsf _ (fun a b h => (Prod.ext_iff.1 (toLex.injective h)).2) ends S

/-- **Theorem 4.1 for tied weights**, a corollary of Theorem 4.1 of [KhannaPuttermanSong2026]
under the paper's convention of breaking ties by edge index (§2, p. 11). There is one absolute
constant `C` such that for every finite multigraph, `Cslib.Query.linearMsfTies` returns a
minimum-weight spanning forest for every assignment of weights in an ordered additive monoid,
ties allowed, with at most `2 C |S|` comparisons of weights. Its output is the minimum spanning
forest for the tie-broken weights `e ↦ (w e, e)` (`Cslib.Query.eval_linearMsfTies`), and the
comparisons of edge indices it makes are free, as computation between comparisons is. -/
theorem linearMsfTies_isSpanningForest_and_sum_le_and_countQueries_le :
    ∃ C : ℕ, ∀ {V E : Type} [DecidableEq V] [LinearOrder E] (ends : E → Sym2 V) (S : Finset E)
      {W : Type} [LinearOrder W] [AddCommMonoid W] [IsOrderedAddMonoid W] (w : E → W),
      IsSpanningForest ends S ((linearMsfTies ends S).eval (LEQuery.keyOracle w)) ∧
      (∀ F, IsSpanningForest ends S F →
        ∑ e ∈ (linearMsfTies ends S).eval (LEQuery.keyOracle w), w e ≤ ∑ e ∈ F, w e) ∧
      (linearMsfTies ends S).countQueries (LEQuery.keyOracle w) ≤ 2 * C * #S := by
  obtain ⟨D, hD⟩ := countQueries_linearMsf_le
  refine ⟨⌈D⌉₊, fun {V E} _ _ ends S {W} _ _ _ w => ?_⟩
  have hκ : Function.Injective fun e => toLex (w e, e) :=
    fun a b h => (Prod.ext_iff.1 (toLex.injective h)).2
  have hmono : ∀ a b, toLex (w a, a) < toLex (w b, b) → w a ≤ w b := fun a b h => by
    rcases Prod.Lex.toLex_lt_toLex.1 h with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  rw [eval_linearMsfTies]
  refine ⟨isSpanningForest_msf _ hκ, fun F hF => sum_msf_le_of_monotone _ hκ hmono hF, ?_⟩
  rw [linearMsfTies, FreeM.countQueries_eq_cost_one, FreeM.cost_liftM, eval_tieBreak]
  refine (FreeM.cost_le_mul_countQueries (c := 2) _ _ (fun q => ?_) _).trans ?_
  · rw [← FreeM.countQueries_eq_cost_one]; exact countQueries_tieBreak_le _ q
  · have h := (hD ends S (fun e => toLex (w e, e)) hκ).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil D) (Nat.cast_nonneg _))
    have h' : (linearMsf linearMsfSteps ends S).countQueries
        (LEQuery.keyOracle fun e => toLex (w e, e)) ≤ ⌈D⌉₊ * #S := by exact_mod_cast h
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 h'

end Cslib.Query
