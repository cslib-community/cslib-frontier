/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PairwiseIndependentHash
import CslibFrontier.Foundations.Data.Finset.Expect.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Retention by pairwise independent hashing

Fix a target set `B ⊆ Y` and a pairwise independent family `h i : X → Y`. A point `x` is
*retained* by the seed `i` when its hash `h i x` lies in `B`. Each point is then retained with
probability exactly `p = #B / |Y|`, and the retention events of two distinct points are
independent: both are retained with probability exactly `p ^ 2`
(`IsPairwiseIndependentHash.expect_boole_apply_mem_and_apply_mem`). This is sampling at rate `p`
with pairwise independence, the technique of Chor and Goldreich [ChorGoldreich1989] built on the
hash families of Carter and Wegman [CarterWegman1979], [WegmanCarter1981]. For polynomial or affine
hashing over a finite field with a box `B`, the rate `p` ranges over the ratios of box size to
field size.

The number `N i = #{x ∈ S | h i x ∈ B}` of retained points of a finite set `S` therefore has mean
`#S p`, second factorial moment `#S (#S - 1) p ^ 2` and variance `#S p (1 - p)`, and Chebyshev's
inequality bounds its deviations. In particular fewer than half of the expected number of points
are retained with probability at most `4 / (#S p)`. For a single target, `B = {y}`, these are the
cell-size moments of `CslibFrontier.Probability.PairwiseIndependentHash`.

Conversely, by inclusion–exclusion some point of `S` is retained with probability at least
`min (#S p) 1 / 2`, and at least `3 #S p / 4` when `2 #S p ≤ 1`. When `h` is a pairwise independence
generator `G : {0,1}^{2n} → ({0,1}^n)^n` (seeds `ι = {0,1}^{2n}`, points `X = Fin n`), this says
that one of the `n` outputs lands in a set of density `p`: Exercise 7.23 of
[Goldreich][Goldreich2007DraftR4], used there in the proof of Lemma 7.22.

## Main results

* `Cslib.Probability.IsPairwiseIndependentHash.expect_boole_apply_mem`,
  `Cslib.Probability.IsPairwiseIndependentHash.dens_filter_apply_mem`: a point is retained with
  probability `#B / |Y|`.
* `Cslib.Probability.IsPairwiseIndependentHash.expect_boole_apply_mem_and_apply_mem`,
  `Cslib.Probability.IsPairwiseIndependentHash.dens_filter_apply_mem_and_apply_mem`: two distinct
  points are retained independently.
* `Cslib.Probability.IsPairwiseIndependentHash.expect_card_filter_apply_mem`,
  `Cslib.Probability.IsPairwiseIndependentHash.expect_card_filter_apply_mem_mul_sub_one`,
  `Cslib.Probability.IsPairwiseIndependentHash.expect_card_filter_apply_mem_sub_sq`: the mean,
  second factorial moment and variance of the number of retained points.
* `Cslib.Probability.IsPairwiseIndependentHash.dens_le_abs_card_filter_apply_mem_sub_le`:
  Chebyshev's inequality for it.
* `Cslib.Probability.IsPairwiseIndependentHash.dens_two_mul_card_filter_apply_mem_lt_le`: fewer
  than half of the expected number of points are retained with probability at most `4 / (#S p)`.
* `Cslib.Probability.IsPairwiseIndependentHash.sub_le_dens_filter_exists_apply_mem`: by
  inclusion–exclusion, some point of `S` is retained with probability at least
  `#S p - #S (#S - 1) p ^ 2 / 2`.
* `Cslib.Probability.IsPairwiseIndependentHash.min_mul_div_two_le_dens_filter_exists_apply_mem`,
  `Cslib.Probability.IsPairwiseIndependentHash.three_quarters_mul_le_dens_filter_exists_apply_mem`:
  hence with probability at least `min (#S p) 1 / 2`, and at least `3 #S p / 4` when
  `2 #S p ≤ 1`. For a pairwise independence generator this is Goldreich's Exercise 7.23.

## References

* [B. Chor, O. Goldreich, *On the power of two-point based sampling*][ChorGoldreich1989]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft `r4.pdf` (March
  2007)][Goldreich2007DraftR4], Lemma 7.22 and Exercise 7.23
* [J. L. Carter, M. N. Wegman, *Universal classes of hash functions*][CarterWegman1979]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

public section

namespace Cslib.Probability.IsPairwiseIndependentHash

open Finset
open scoped BigOperators

variable {ι X Y 𝕜 : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y] {h : ι → X → Y}

/-- **Retention probability**: a point is retained, its hash lying in `B`, with probability
`#B / |Y|`. -/
theorem expect_boole_apply_mem [Semifield 𝕜] [CharZero 𝕜] (hh : IsPairwiseIndependentHash h)
    (x : X) (B : Finset Y) :
    𝔼 i, (if h i x ∈ B then 1 else 0 : 𝕜) = #B / Fintype.card Y := by
  have hpt (i : ι) : (if h i x ∈ B then 1 else 0 : 𝕜) = ∑ y ∈ B, if h i x = y then 1 else 0 :=
    (sum_ite_eq B (h i x) fun _ ↦ (1 : 𝕜)).symm
  simp only [hpt, expect_sum_comm, Fintype.expect_boole, hh.dens_filter_apply_eq, NNRat.cast_inv,
    NNRat.cast_natCast, sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **Retention probability**: a point is retained, its hash lying in `B`, with probability
`#B / |Y|`. -/
theorem dens_filter_apply_mem (hh : IsPairwiseIndependentHash h) (x : X) (B : Finset Y) :
    dens {i | h i x ∈ B} = #B / Fintype.card Y := by
  simpa [Fintype.expect_boole] using hh.expect_boole_apply_mem (𝕜 := ℚ≥0) x B

/-- **Pairwise independent retention**: two distinct points are retained by `B₁` and `B₂` with
probability `#B₁ / |Y| * (#B₂ / |Y|)`. -/
theorem expect_boole_apply_mem_and_apply_mem [Semifield 𝕜] [CharZero 𝕜]
    (hh : IsPairwiseIndependentHash h) {x₁ x₂ : X} (hx : x₁ ≠ x₂) (B₁ B₂ : Finset Y) :
    𝔼 i, (if h i x₁ ∈ B₁ ∧ h i x₂ ∈ B₂ then 1 else 0 : 𝕜) =
      #B₁ / Fintype.card Y * (#B₂ / Fintype.card Y) := by
  have hpt (i : ι) : (if h i x₁ ∈ B₁ ∧ h i x₂ ∈ B₂ then 1 else 0 : 𝕜) =
      ∑ y₁ ∈ B₁, ∑ y₂ ∈ B₂, if h i x₁ = y₁ ∧ h i x₂ = y₂ then 1 else 0 := by
    rw [ite_and, ← sum_ite_eq B₁ (h i x₁) fun _ ↦ (if h i x₂ ∈ B₂ then 1 else 0 : 𝕜)]
    refine sum_congr rfl fun y₁ _ ↦ ?_
    by_cases hy : h i x₁ = y₁ <;> simp [hy, sum_ite_eq]
  simp only [hpt, expect_sum_comm, Fintype.expect_boole, hh.dens_filter_apply_eq_and_apply_eq hx,
    NNRat.cast_inv, NNRat.cast_pow, NNRat.cast_natCast, sum_const, nsmul_eq_mul]
  ring

/-- **Pairwise independent retention**: two distinct points are retained by `B₁` and `B₂` with
probability `#B₁ / |Y| * (#B₂ / |Y|)`. -/
theorem dens_filter_apply_mem_and_apply_mem (hh : IsPairwiseIndependentHash h) {x₁ x₂ : X}
    (hx : x₁ ≠ x₂) (B₁ B₂ : Finset Y) :
    dens {i | h i x₁ ∈ B₁ ∧ h i x₂ ∈ B₂} = #B₁ / Fintype.card Y * (#B₂ / Fintype.card Y) := by
  simpa [Fintype.expect_boole] using hh.expect_boole_apply_mem_and_apply_mem (𝕜 := ℚ≥0) hx B₁ B₂

/-- **The mean number of retained points** of `S` is `#S * (#B / |Y|)`. -/
theorem expect_card_filter_apply_mem [Semifield 𝕜] [CharZero 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y) :
    𝔼 i, (#{x ∈ S | h i x ∈ B} : 𝕜) = #S * (#B / Fintype.card Y) := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    expect_sum_comm, hh.expect_boole_apply_mem, sum_const, nsmul_eq_mul]

/-- **The second factorial moment of the number of retained points**: the number of ordered
pairs of distinct retained points of `S` has expectation `#S (#S - 1) (#B / |Y|) ^ 2`. -/
theorem expect_card_filter_apply_mem_mul_sub_one [Field 𝕜] [CharZero 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y) :
    𝔼 i, (#{x ∈ S | h i x ∈ B} : 𝕜) * (#{x ∈ S | h i x ∈ B} - 1) =
      #S * (#S - 1) * (#B / Fintype.card Y) ^ 2 := by
  classical
  have hcount (i : ι) : (#{x ∈ S | h i x ∈ B} : 𝕜) * (#{x ∈ S | h i x ∈ B} - 1) =
      ∑ q ∈ S.offDiag, if h i q.1 ∈ B ∧ h i q.2 ∈ B then 1 else 0 := by
    have hoff : {x ∈ S | h i x ∈ B}.offDiag = {q ∈ S.offDiag | h i q.1 ∈ B ∧ h i q.2 ∈ B} := by
      ext q
      simp only [mem_offDiag, mem_filter]
      tauto
    rw [sum_boole, ← hoff, offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  have hpair (q : X × X) (hq : q ∈ S.offDiag) :
      𝔼 i, (if h i q.1 ∈ B ∧ h i q.2 ∈ B then 1 else 0 : 𝕜) = (#B / Fintype.card Y) ^ 2 := by
    rw [hh.expect_boole_apply_mem_and_apply_mem (mem_offDiag.1 hq).2.2, sq]
  simp only [hcount]
  rw [expect_sum_comm, sum_congr rfl hpair, sum_const, nsmul_eq_mul, offDiag_card,
    Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
  ring

/-- **The variance of the number of retained points** is `#S p (1 - p)` with `p = #B / |Y|`. -/
theorem expect_card_filter_apply_mem_sub_sq [Field 𝕜] [CharZero 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y) :
    𝔼 i, ((#{x ∈ S | h i x ∈ B} : 𝕜) - #S * (#B / Fintype.card Y)) ^ 2 =
      #S * (#B / Fintype.card Y) * (1 - #B / Fintype.card Y) := by
  have hsq (i : ι) : ((#{x ∈ S | h i x ∈ B} : 𝕜) - #S * (#B / Fintype.card Y)) ^ 2 =
      (#{x ∈ S | h i x ∈ B} : 𝕜) * (#{x ∈ S | h i x ∈ B} - 1) +
        (1 - 2 * (#S * (#B / Fintype.card Y))) * #{x ∈ S | h i x ∈ B} +
        (#S * (#B / Fintype.card Y)) ^ 2 := by
    ring
  rcases isEmpty_or_nonempty ι with hι | hι
  · rcases S.eq_empty_or_nonempty with rfl | ⟨x, -⟩
    · simp
    rcases B.eq_empty_or_nonempty with rfl | ⟨y, -⟩
    · simp
    exact absurd (hh.nonempty x y) (not_nonempty_iff.2 hι)
  simp only [hsq, expect_add_distrib, ← mul_expect, hh.expect_card_filter_apply_mem_mul_sub_one,
    hh.expect_card_filter_apply_mem, Fintype.expect_const]
  ring

/-- **Chebyshev's inequality for the number of retained points**: it is at distance at least
`ε > 0` from its mean `#S p`, with `p = #B / |Y|`, with probability at most `#S p / ε²`. -/
theorem dens_le_abs_card_filter_apply_mem_sub_le [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y)
    {ε : 𝕜} (hε : 0 < ε) :
    (dens {i | ε ≤ |(#{x ∈ S | h i x ∈ B} : 𝕜) - #S * (#B / Fintype.card Y)|} : 𝕜) ≤
      #S * (#B / Fintype.card Y) / ε ^ 2 := by
  refine (Fintype.dens_le_abs_le_expect_sq_div_sq _ hε).trans
    (div_le_div_of_nonneg_right ?_ (sq_nonneg ε))
  rw [hh.expect_card_filter_apply_mem_sub_sq]
  exact mul_le_of_le_one_right (by positivity) (sub_le_self _ (by positivity))

/-- **Lower tail of the number of retained points**: fewer than half of the expected number
`#S p`, with `p = #B / |Y|`, are retained with probability at most `4 / (#S p)`. -/
theorem dens_two_mul_card_filter_apply_mem_lt_le [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y)
    (hpos : 0 < (#S : 𝕜) * (#B / Fintype.card Y)) :
    (dens {i | 2 * (#{x ∈ S | h i x ∈ B} : 𝕜) < #S * (#B / Fintype.card Y)} : 𝕜) ≤
      4 / (#S * (#B / Fintype.card Y)) := by
  set μ : 𝕜 := #S * (#B / Fintype.card Y)
  have hsub : ({i | 2 * (#{x ∈ S | h i x ∈ B} : 𝕜) < μ} : Finset ι) ⊆
      ({i | μ / 2 ≤ |(#{x ∈ S | h i x ∈ B} : 𝕜) - μ|} : Finset ι) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  calc (dens {i | 2 * (#{x ∈ S | h i x ∈ B} : 𝕜) < μ} : 𝕜)
      ≤ (dens {i | μ / 2 ≤ |(#{x ∈ S | h i x ∈ B} : 𝕜) - μ|} : 𝕜) := by
        exact_mod_cast dens_le_dens hsub
    _ ≤ μ / (μ / 2) ^ 2 := hh.dens_le_abs_card_filter_apply_mem_sub_le S B (by positivity)
    _ = 4 / μ := by field_simp; ring

/-- **Inclusion–exclusion for retention**: some point of `S` is retained with probability at
least `#S p - #S (#S - 1) p ^ 2 / 2`, where `p = #B / |Y|`. -/
theorem sub_le_dens_filter_exists_apply_mem [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y) :
    (#S : 𝕜) * (#B / Fintype.card Y) - #S * (#S - 1) * (#B / Fintype.card Y) ^ 2 / 2 ≤
      (dens {i | ∃ x ∈ S, h i x ∈ B} : 𝕜) := by
  calc (#S : 𝕜) * (#B / Fintype.card Y) - #S * (#S - 1) * (#B / Fintype.card Y) ^ 2 / 2
      = 𝔼 i, ((#{x ∈ S | h i x ∈ B} : 𝕜) -
          #{x ∈ S | h i x ∈ B} * (#{x ∈ S | h i x ∈ B} - 1) / 2) := by
        rw [expect_sub_distrib, ← expect_div, hh.expect_card_filter_apply_mem,
          hh.expect_card_filter_apply_mem_mul_sub_one]
    _ ≤ 𝔼 i, (if ∃ x ∈ S, h i x ∈ B then 1 else 0 : 𝕜) :=
        expect_le_expect fun i _ => by
          simp only [← filter_nonempty_iff, ← card_pos]
          exact natCast_sub_mul_sub_one_div_two_le _
    _ = _ := Fintype.expect_boole _

omit [Fintype ι] [DecidableEq Y] in
private theorem cast_dens_eq (B : Finset Y) : ((dens B : ℚ≥0) : ℚ) = #B / Fintype.card Y := by
  rw [dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast]

/-- **A pairwise independent generator hits a dense set** [Goldreich, Exercise 7.23, first
claim][Goldreich2007DraftR4]: some point of `S` is sent into a set `B` of density
`p = #B / |Y|` with probability at least `min (#S p) 1 / 2`. Goldreich states it for a pairwise
independence generator `G : {0,1}^{2n} → ({0,1}^n)^n` as in his Lemma 7.22: the case
`ι = {0,1}^{2n}`, `X = Fin n`, `S = univ` and `Y = {0,1}^n`. As in the guideline, the bound follows
from inclusion–exclusion on `min #S ⌈1 / p⌉` points of `S`. -/
theorem min_mul_div_two_le_dens_filter_exists_apply_mem (hh : IsPairwiseIndependentHash h)
    (S : Finset X) (B : Finset Y) :
    min (#S * dens B) 1 / 2 ≤ dens {i | ∃ x ∈ S, h i x ∈ B} := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have : Nonempty Y := hB.to_subtype.map Subtype.val
  set p : ℚ := #B / Fintype.card Y with hp_def
  have hp : 0 < p := div_pos (Nat.cast_pos.2 hB.card_pos) (Nat.cast_pos.2 Fintype.card_pos)
  set k := min #S ⌈1 / p⌉₊ with hk_def
  obtain ⟨S', hS'S, hS'⟩ := exists_subset_card_eq (min_le_left #S ⌈1 / p⌉₊)
  have hmono : dens {i | ∃ x ∈ S', h i x ∈ B} ≤ dens {i | ∃ x ∈ S, h i x ∈ B} :=
    dens_le_dens fun _ hi =>
      mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2.imp fun _ ⟨hx, hxB⟩ => ⟨hS'S hx, hxB⟩⟩
  rw [← NNRat.cast_le (K := ℚ)]
  refine le_trans ?_ ((NNRat.cast_le.2 hmono).trans' (hh.sub_le_dens_filter_exists_apply_mem S' B))
  push_cast [cast_dens_eq B]
  rw [hS', ← hp_def]
  have hkp : ((k : ℚ) - 1) * p ≤ 1 := by
    have hlt : (k : ℚ) < 1 / p + 1 := (Nat.cast_le.2 (min_le_right _ _)).trans_lt
      (Nat.ceil_lt_add_one (by positivity))
    have := mul_lt_mul_of_pos_right (sub_lt_iff_lt_add.2 hlt) hp
    rw [one_div_mul_cancel hp.ne'] at this
    exact this.le
  have hmin : min ((#S : ℚ) * p) 1 ≤ k * p := by
    rcases min_choice #S ⌈1 / p⌉₊ with hk | hk
    · rw [hk_def, hk]; exact min_le_left _ _
    · refine (min_le_right _ _).trans ?_
      rw [hk_def, hk]
      calc (1 : ℚ) = 1 / p * p := (one_div_mul_cancel hp.ne').symm
        _ ≤ ⌈1 / p⌉₊ * p := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hp.le
  have h2 := mul_le_mul_of_nonneg_left hkp (mul_nonneg (Nat.cast_nonneg k) hp.le)
  have hsq : (k : ℚ) * (k - 1) * p ^ 2 = (k * p) * ((k - 1) * p) := by ring
  linarith

/-- **A pairwise independent generator hits a sparse set** [Goldreich, Exercise 7.23, second
claim][Goldreich2007DraftR4]: if the set `B` has density `p = #B / |Y|` with `p ≤ 1 / (2 #S)`, then
some point of `S` is sent into `B` with probability at least `0.75 #S p`. The case of Goldreich's
generator is as in `min_mul_div_two_le_dens_filter_exists_apply_mem`. -/
theorem three_quarters_mul_le_dens_filter_exists_apply_mem (hh : IsPairwiseIndependentHash h)
    {S : Finset X} {B : Finset Y} (hSB : 2 * #S * dens B ≤ 1) :
    3 / 4 * (#S * dens B) ≤ dens {i | ∃ x ∈ S, h i x ∈ B} := by
  set p : ℚ := #B / Fintype.card Y with hp_def
  have hp : 0 ≤ p := by positivity
  rw [← NNRat.cast_le (K := ℚ)] at hSB ⊢
  refine le_trans ?_ (hh.sub_le_dens_filter_exists_apply_mem S B)
  push_cast [cast_dens_eq B] at hSB ⊢
  rw [← hp_def]
  have hsp : 0 ≤ (#S : ℚ) * p := by positivity
  have h2 := mul_le_mul_of_nonneg_left (by linarith : (#S : ℚ) * p ≤ 1 / 2) hsp
  have hsq : (#S : ℚ) * (#S - 1) * p ^ 2 = (#S * p) * (#S * p) - (#S * p) * p := by ring
  linarith [mul_nonneg hsp hp]

end Cslib.Probability.IsPairwiseIndependentHash
