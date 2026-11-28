/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.Valiant
public import CslibFrontier.Computability.Complexity.Problems.Permanent.MatchingParity
import CslibFrontier.Computability.Complexity.Problems.BipartitePerfectMatching.Membership
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFnGetD
import CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Foundations.Data.Fin.Prod

/-!
# Searching for bipartite perfect matchings

`BipartitePerfectMatching.searchRel` uses the existing 0/1-permanent verifier: a solution is
exactly `n * n` bits describing a permutation matrix supported on a Boolean table with `n` rows.
Missing entries are false and entries beyond the square are ignored, as in `ZeroOnePermanent`.
The relation's count is both the number of perfect matchings and the 0/1 permanent.

The solver calls the certified `maximumMatching` algorithm and writes its edge list as a
row-major Boolean matrix. Thus search is in `FPSearch`, while counting is metric-#P-complete
and unique versus no solution is in promise-P. `exercise_6_36b` assembles these facts for
[Goldreich2007Draft], Exercise 6.36(b), February 2007 `r3.pdf`, PDF p. 61 / printed p. 263.
The source's PC is `FNP`, and PF ∩ PC is `FPSearch`; metric completeness implies its Cook
completeness. Part (a), with a PC-complete relation, is not asserted here.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime
open Cslib.Algorithms.Lean.MaxFlow

namespace BipartitePerfectMatching

/-- The perfect-matching search relation on dense Boolean tables. Certificates are row-major
permutation matrices of exactly `n²` bits, where `n` is the number of rows. -/
@[expose] def searchRel (A : List (List Bool)) (w : List Bool) : Prop :=
  w.length = A.length * A.length ∧ ZeroOnePermanent.verifier (A, w) = true

/-- Counting the search certificates counts perfect matchings, without padding multiplicity. -/
theorem searchCount_searchRel (A : List (List Bool)) :
    searchCount searchRel A = BipartitePerfectMatchingCount A := by
  rw [searchCount_eq_acceptCount (fun _ => Iff.rfl), ZeroOnePermanent.acceptCount_verifier,
    bipartitePerfectMatchingCount_eq_zeroOnePermanent]

private def tableWord (A : List (List Bool)) : List Bool :=
  (List.range (A.length * A.length)).map fun k =>
    (A.getD (k / A.length) []).getD (k % A.length) false

private theorem tableWord_polyTime : ComputableInPolyTime tableWord encBoolTable encBits := by
  unfold tableWord
  exact mapToBitsWithInput (by fun_prop) (by fun_prop)

private theorem graph_tableWord (A : List (List Bool)) (i j : Fin A.length) :
    graph (tableWord A) A.length (i, j) = A[i].getD j false := by
  rw [tableWord, List.map_range_eq_ofFn, graph_ofFn]
  simp [Circuits.BipartiteMatching.graph, finProdFinEquiv, Nat.add_mul_div_left,
    Nat.div_eq_of_lt j.isLt, Nat.mod_eq_of_lt j.isLt,
    Nat.pos_of_ne_zero (Nat.ne_zero_of_lt j.isLt)]

private def matchingWord (A : List (List Bool)) : List Bool :=
  (List.range (A.length * A.length)).map fun k =>
    (maximumMatching (tableWord A) A.length).any fun e =>
      decide (e.1 = k / A.length ∧ e.2 = k % A.length)

private theorem matchingWord_polyTime :
    ComputableInPolyTime matchingWord encBoolTable encBits := by
  have hM := computableInPolyTime_maximumMatching.comp
    (tableWord_polyTime.prod (length_list (encList encBool)))
  unfold matchingWord
  exact mapToBitsWithInput (by fun_prop) (anyWithInput (hM.comp (fst _ _)) (by fun_prop))

private theorem matchingWord_spec (A : List (List Bool)) :
    ZeroOnePermanent.verifier (A, matchingWord A) = true ↔ ∃ w, searchRel A w := by
  let M := edgeSet A.length (maximumMatching (tableWord A) A.length)
  have hmax := isMaxMatching_maximumMatching (tableWord A) A.length
  have hbit (i j : Fin A.length) :
      (maximumMatching (tableWord A) A.length).any (fun e =>
        decide (e.1 = (finProdFinEquiv (i, j)).val / A.length ∧
          e.2 = (finProdFinEquiv (i, j)).val % A.length)) = true ↔ (i, j) ∈ M := by
    simp only [finProdFinEquiv_val_div, finProdFinEquiv_val_mod]
    simp [M, List.any_eq_true]
  rw [matchingWord, List.map_range_eq_ofFn, ZeroOnePermanent.verifier_ofFn]
  simp only [hbit]
  constructor
  · intro h
    refine ⟨matchingWord A, by simp [matchingWord], ?_⟩
    simpa only [matchingWord, List.map_range_eq_ofFn, ZeroOnePermanent.verifier_ofFn, hbit] using h
  · rintro ⟨w, hlen, hw⟩
    rw [← List.ofFn_getD_eq_of_length false hlen, ZeroOnePermanent.verifier_ofFn] at hw
    obtain ⟨hrow, hleft, hright, hsupp⟩ := hw
    let N : Finset (Fin A.length × Fin A.length) :=
      Finset.univ.filter fun e => w.getD (finProdFinEquiv e) false = true
    have hN : IsMatching (graph (tableWord A) A.length) N :=
      ⟨fun e he => graph_tableWord A e.1 e.2 ▸ hsupp e.1 e.2 (Finset.mem_filter.mp he).2,
        fun i j k hj hk => hleft i j k (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2,
        fun i k j hi hk => hright i k j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hk).2⟩
    have hcover : matchedLeft N = Finset.univ := by
      ext i
      obtain ⟨j, hj⟩ := hrow i
      simpa only [mem_matchedLeft, Finset.mem_univ, iff_true] using
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    have hM : matchedLeft M = Finset.univ := Finset.eq_univ_of_card _ <|
      le_antisymm (Finset.card_le_univ _) <| by
        rw [card_matchedLeft hmax.1, ← Finset.card_univ, ← hcover, card_matchedLeft hN]
        exact hmax.2 N hN
    exact ⟨fun i => mem_matchedLeft.mp (hM ▸ Finset.mem_univ i), hmax.1.2.1, hmax.1.2.2,
      fun i j hij => (graph_tableWord A i j) ▸ hmax.1.1 (i, j) hij⟩

/-- Perfect-matching search is polynomial-time: write the certified maximum matching as a
permutation-matrix certificate, returning `none` exactly when no perfect matching exists. -/
theorem searchRel_mem_FPSearch : searchRel ∈ FPSearch encBoolTable := by
  have hn : ComputableInPolyTime (fun A : List (List Bool) => A.length * A.length)
      encBoolTable encUnary := by fun_prop
  obtain ⟨p, hp⟩ := hn.polyBounded.exists_polynomial
  refine ⟨⟨⟨p, fun A w hw => hw.1.le.trans (hp A)⟩,
    fun q => decide (q.2.length = q.1.length * q.1.length) && ZeroOnePermanent.verifier q,
    by fun_prop, fun A w => by simp [searchRel]⟩,
    fun A => if ZeroOnePermanent.verifier (A, matchingWord A) then some (matchingWord A)
      else none, ?_, ?_⟩
  · have := matchingWord_polyTime
    fun_prop
  · intro A
    dsimp only
    split_ifs with h
    · exact ⟨fun w hw => by
        cases Option.some.inj hw
        exact ⟨by simp [matchingWord], h⟩, by simp⟩
    · exact ⟨by simp, fun _ hw => h ((matchingWord_spec A).mpr hw)⟩

/-- Goldreich Exercise 6.36(b): an easy perfect-matching search relation has a metric-#P-complete
count and a polynomial-time unique-versus-none promise solver. The yes/no sets are stated using
the relation's own solution count: count one is `US_R`, and count zero is the complement
of `S_R` (the instances with a solution). Part (a) is a separate assertion. -/
theorem exercise_6_36b :
    searchRel ∈ FPSearch encBoolTable ∧
      SharpPMetricComplete encBoolTable (searchCount searchRel) ∧
      (⟨{A | searchCount searchRel A = 1}, {A | searchCount searchRel A = 0},
        Set.disjoint_left.mpr (fun _ h₁ h₀ => by simp_all)⟩ :
          PromiseProblem (List (List Bool))) ∈ PromiseP encBoolTable := by
  refine ⟨searchRel_mem_FPSearch, ?_, ?_⟩
  · simpa only [funext searchCount_searchRel] using
      bipartitePerfectMatchingCount_sharpPMetricComplete
  · simpa only [searchCount_searchRel, uniqueBipartiteMatching] using
      uniqueBipartiteMatching_mem_PromiseP

end BipartitePerfectMatching

end Cslib.Complexity
