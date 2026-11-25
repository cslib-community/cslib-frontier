/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.BooleanAnalysis.Concentration
import CslibFrontier.Foundations.BooleanAnalysis.FriedgutJunta
import CslibFrontier.Foundations.Combinatorics.SmallSubsets
import CslibFrontier.Foundations.Data.Nat.Choose.Sum

/-!
# A large low-degree Fourier coefficient

A Boolean function `f` of variance at least `1/2` has a nonempty set `S` with `|S| ≤ 8 I[f]` and
`f̂(S)² ≥ exp(-O(I[f]²))` [O'Donnell, Corollary 9.32][ODonnell2014]; it is stated here for any
bound `K ≥ I[f]` (`BitString.exists_le_fourierCoeff_sq_of_le_expect_sub_expect_sq`). By
Friedgut's junta theorem at `ε = 1/8`
(`BitString.exists_sum_filter_not_subset_fourierCoeff_sq_le_of_totalInfluence_le`), a set `J` of
at most `M = (256/9) K³ 81^{8 K} = exp(O(K))` coordinates carries all but `1/8` of the Fourier
weight on its subsets, and the weight above level `8 K` is at most `1/8`
(`BitString.sum_fourierCoeff_sq_le_of_totalInfluence_le`). The weight on the nonempty sets is the
variance (`BitString.expect_sub_expect_sq_eq_sum_fourierCoeff_sq`), at least `1/2`, so the
nonempty subsets of `J` of size at most `8 K`, of which there are at most
`(M + 1)^{⌊8 K⌋} = exp(O(K²))`, carry weight at least `1/4`, and one of them carries at least its
share.

A function of variance below `1/2` instead has `f̂(∅)² > 1/2`
[O'Donnell, Remark 9.33][ODonnell2014]: `f̂(∅)` is the mean (`BitString.fourierCoeff_empty`) and
the variance is one minus the squared mean (`BitString.expect_sub_expect_sq_signVal`).

## Main results

* `Cslib.BitString.exists_le_fourierCoeff_sq_of_le_expect_sub_expect_sq`: Corollary 9.32.

## Usage

Open `Cslib.BitString`. For `hvar : 1 / 2 ≤ 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2` and
`hK : totalInfluence (fun x => signVal (f x)) ≤ K`,
`exists_le_fourierCoeff_sq_of_le_expect_sub_expect_sq f hvar hK` gives a nonempty `S` with
`#S ≤ 8 * K` and `fourierCoeff (fun x => signVal (f x)) S ^ 2` at least `1 / (4 * (M + 1) ^ m)`,
where `M = 256 / 9 * K ^ 3 * 81 ^ (8 * K)` and `m = ⌊8 * K⌋₊`. Taking `K` to be the total
influence gives the book's statement. The spectral step it uses,
`exists_sum_filter_not_subset_fourierCoeff_sq_le_of_totalInfluence_le f hε hK` for `hε : 0 < ε`
(in `CslibFrontier.Foundations.BooleanAnalysis.FriedgutJunta`), gives a set `J` of at most
`4 * K ^ 3 / (9 * ε ^ 2) * 81 ^ (K / ε)` coordinates such that the Fourier weight on the sets that
are not subsets of `J` is at most `ε`. With `sum_fourierCoeff_sq_le_of_totalInfluence_le`
(Proposition 3.2) it gives the book's spectral form of Friedgut's junta theorem, and
`Cslib.BitString.exists_dependsOn_hammingDist_div_le_sum_not_subset_fourierCoeff_sq f J` turns its
`J` into a `J`-junta at relative Hamming distance at most `ε`; this is how
`exists_dependsOn_hammingDist_div_le_of_totalInfluence_le` is proved. Remark 9.33 needs no
separate lemma: combine `fourierCoeff_empty` with `expect_sub_expect_sq_signVal` (in
`CslibFrontier.Foundations.BooleanAnalysis.Variance`). Checked instances, the spectral step on a
constant and the corollary on the dictator on one bit, are in
[`CslibFrontierTests/BooleanAnalysisLargeCoefficient.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisLargeCoefficient.lean).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A large low-degree Fourier coefficient** [O'Donnell, Corollary 9.32][ODonnell2014]: if a
Boolean function, read as signs `F`, has variance at least `1/2` and total influence at most `K`,
then some nonempty `S` with `|S| ≤ 8 K` has `F̂(S)² ≥ 1 / (4 (M + 1)^{⌊8 K⌋})`, where
`M = (256/9) K³ 81^{8 K}` bounds the number of coordinates of Friedgut's junta theorem at
`ε = 1/8`. Taking `K = I[F]` gives the book's statement; since `K ≥ I[F] ≥ Var[F] ≥ 1/2`, the bound
is `exp(-O(K²))`. -/
theorem exists_le_fourierCoeff_sq_of_le_expect_sub_expect_sq (f : (ι → Bool) → Bool) {K : ℝ}
    (hvar : 1 / 2 ≤ 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2)
    (hK : totalInfluence (fun x => signVal (f x)) ≤ K) :
    ∃ S : Finset ι, S ≠ ∅ ∧ (#S : ℝ) ≤ 8 * K ∧
      1 / (4 * (256 / 9 * K ^ 3 * 81 ^ (8 * K) + 1) ^ ⌊8 * K⌋₊) ≤
        fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set c : Finset ι → ℝ := fun S => fourierCoeff F S ^ 2
  have hc (S : Finset ι) : 0 ≤ c S := sq_nonneg _
  have hK0 : 1 / 2 ≤ K := (hvar.trans (expect_sub_expect_sq_le_totalInfluence F)).trans hK
  -- Friedgut's junta theorem at `ε = 1/8`: few coordinates `J` whose subsets carry most weight
  obtain ⟨J, hJ, hout⟩ := exists_sum_filter_not_subset_fourierCoeff_sq_le_of_totalInfluence_le f
    (ε := 1 / 8) (by norm_num) hK
  rw [show 4 * K ^ 3 / (9 * (1 / 8) ^ 2) * 81 ^ (K / (1 / 8)) = 256 / 9 * K ^ 3 * 81 ^ (8 * K) by
    rw [show K / (1 / 8) = 8 * K by ring]; ring] at hJ
  replace hout : ∑ S with ¬S ⊆ J, c S ≤ 1 / 8 := hout
  -- the weight above level `m = ⌊8 K⌋` is at most `1/8`
  set m := ⌊8 * K⌋₊
  have hhigh : ∑ S with m < #S, c S ≤ 1 / 8 :=
    sum_fourierCoeff_sq_le_of_totalInfluence_le hK (by
      have := Nat.lt_floor_add_one (8 * K)
      linarith)
  -- the nonempty sets carry weight `Var[F] ≥ 1/2`, so the remaining ones carry at least `1/4`
  set G : Finset (Finset ι) := {S | S ≠ ∅ ∧ S ⊆ J ∧ #S ≤ m}
  have hcover : ({S | S ≠ ∅} : Finset (Finset ι)) ⊆
      (({S | ¬S ⊆ J} : Finset (Finset ι)) ∪ ({S | m < #S} : Finset (Finset ι))) ∪ G := by
    intro S hS
    simp only [G, mem_union, mem_filter, mem_univ, true_and] at hS ⊢
    by_cases hSJ : S ⊆ J
    · by_cases hm : m < #S
      · exact Or.inl (Or.inr hm)
      · exact Or.inr ⟨hS, hSJ, not_lt.1 hm⟩
    · exact Or.inl (Or.inl hSJ)
  have hunion (s t : Finset (Finset ι)) : ∑ S ∈ s ∪ t, c S ≤ ∑ S ∈ s, c S + ∑ S ∈ t, c S := by
    rw [← sum_union_inter]
    exact le_add_of_nonneg_right (sum_nonneg fun S _ => hc S)
  have hG : 1 / 4 ≤ ∑ S ∈ G, c S := by
    have hne : 1 / 2 ≤ ∑ S with S ≠ ∅, c S :=
      hvar.trans_eq (expect_sub_expect_sq_eq_sum_fourierCoeff_sq F)
    have := (sum_le_sum_of_subset_of_nonneg hcover fun S _ _ => hc S).trans
      ((hunion _ _).trans (add_le_add_left (hunion _ _) _))
    linarith
  -- there are at most `(M + 1)^m` remaining sets
  have hGcard : (#G : ℝ) ≤ (256 / 9 * K ^ 3 * 81 ^ (8 * K) + 1) ^ m := by
    have hsub : G ⊆ {S ∈ J.powerset | #S ≤ m} := fun S hS => by
      obtain ⟨-, -, hSJ, hSm⟩ := mem_filter.1 hS
      exact mem_filter.2 ⟨mem_powerset.2 hSJ, hSm⟩
    have hN : #G ≤ (#J + 1) ^ m := (card_le_card hsub).trans <|
      (card_filter_powerset_card_le_eq_sum_choose J m).trans_le
        (sum_range_choose_le_add_one_pow _ m)
    calc (#G : ℝ) ≤ ((#J + 1) ^ m : ℕ) := by exact_mod_cast hN
      _ ≤ _ := by push_cast; gcongr
  -- pigeonhole
  have hGne : G.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at hG
    norm_num at hG
  have hGpos : (0 : ℝ) < #G := by exact_mod_cast hGne.card_pos
  obtain ⟨S, hS, hSc⟩ := exists_le_of_sum_le hGne (f := fun _ => (1 / 4 / #G : ℝ)) (g := c) (by
    rwa [sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hGpos.ne'])
  obtain ⟨-, hS0, -, hSm⟩ := mem_filter.1 hS
  refine ⟨S, hS0, (Nat.cast_le.2 hSm).trans (Nat.floor_le (by linarith)), le_trans ?_ hSc⟩
  rw [div_div]
  exact one_div_le_one_div_of_le (by linarith) (mul_le_mul_of_nonneg_left hGcard (by norm_num))

end Cslib.BitString
