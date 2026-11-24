/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Communication.Nondeterministic.UniqueDisjointnessUpper
import CslibFrontier.Foundations.Combinatorics.LovaszSteinCover
import CslibFrontier.Foundations.Data.Code.HammingCode

/-!
# Client tests for unique-disjointness monotone-rank upper bounds

Exercises the public module interfaces of `HammingCode`, `LovaszSteinCover`, `PartitionCover`, and
`UniqueDisjointnessUpper` under ordinary `module` imports:

1. Concrete syndrome evaluations, distance-`3` checks, and negative distance-`2` witnesses for the
   shortened binary Hamming code on `Fin 3 → Bool` and `Fin 4 → Bool`.
2. Uniform Sapozhenko–Lovász–Stein covering on the edges of a triangle on `Fin 3`.
3. Exact values (`Fin 0` and `Fin 1`), invalid cross-intersection witnesses, `*`-entry overlap
   vs `1`-entry double-coverage boundary witnesses on `Fin 2`, and the `(ℕ, +, ·)`-semiring rank
   equivalence for `IsPartitionCover` and `partitionCoverNumber`.
4. Specializations of Sergeev's Theorem 1 and Theorem 2 alongside Kaibel–Weltge's lower bound.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.UniqueDisjointnessUpper

open Finset Function Cslib Cslib.Code Cslib.Communication Cslib.Communication.Nondeterministic

/-! ### 1. Shortened binary Hamming codes and distance-3 partitions -/

-- `![true, true, true]` has syndrome `(0+1) ^^^ (1+1) ^^^ (2+1) = 1 ^^^ 2 ^^^ 3 = 0`, forming the
-- `[3, 1, 3]` repetition code together with `0`.
example : syndrome (hammingCheckMatrix 3) ![true, true, true] = 0 := by
  rw [syndrome_eq]
  decide

-- Two distinct words at Hamming distance `2` cannot share the same Hamming syndrome.
example :
    syndrome (hammingCheckMatrix 3) ![true, true, false] ≠
      syndrome (hammingCheckMatrix 3) 0 := by
  rw [syndrome_eq, syndrome_eq]
  decide

-- Any two distinct words in `Fin 4 → Bool` with the same syndrome have Hamming distance `≥ 3`.
example (x y : Fin 4 → Bool) (hne : x ≠ y)
    (hsyn : syndrome (hammingCheckMatrix 4) x = syndrome (hammingCheckMatrix 4) y) :
    3 ≤ hammingDist x y := by
  have h3 := le_minDist_iff.1
    (three_le_minDist_hammingSyndrome_preimage 4 (syndrome (hammingCheckMatrix 4) x))
    x rfl y hsyn.symm hne
  exact_mod_cast h3

-- `Fin 4 → Bool` partitions into `2 * 4 = 8` pairwise-disjoint `3`-codes.
example : ∃ P : Fin 8 → Set (Fin 4 → Bool),
    Pairwise (Disjoint on P) ∧ (⋃ i, P i) = Set.univ ∧ ∀ i, 3 ≤ minDist (P i) :=
  exists_partition_minDist_three (n := 4) (by omega)

/-! ### 2. Sapozhenko–Lovász–Stein uniform covering -/

private def triangleEdges : Finset (Finset (Fin 3)) :=
  {{0, 1}, {1, 2}, {0, 2}}

example : ∃ G ⊆ triangleEdges,
    (univ : Finset (Fin 3)) ⊆ G.biUnion id ∧
      (G.card : ℝ) ≤ (1 + Real.log 3) * 3 / 2 := by
  have hXne : (univ : Finset (Fin 3)).Nonempty := univ_nonempty
  have hsub : triangleEdges ⊆ (univ : Finset (Fin 3)).powerset := by decide
  have hunif : ∀ x ∈ (univ : Finset (Fin 3)), (triangleEdges.filter (x ∈ ·)).card = 2 := by decide
  obtain ⟨G, hGF, hGcov, hGcard⟩ :=
    exists_subset_cover_card_le_of_uniform hXne hsub (by omega : 1 ≤ 2) hunif
  refine ⟨G, hGF, hGcov, hGcard.trans_eq ?_⟩
  have hcardX : (univ : Finset (Fin 3)).card = 3 := by decide
  have hcardF : triangleEdges.card = 3 := by decide
  have hsum : ∑ A ∈ triangleEdges, A.card = 6 := by decide
  have hsumR : ∑ A ∈ triangleEdges, (A.card : ℝ) = 6 := by exact_mod_cast hsum
  rw [hcardX, hcardF, hsumR]
  norm_num

/-! ### 3. Partition covers, `*`-entries, and exact small values -/

-- On `Fin 0`, the unique pair `(∅, ∅)` is disjoint, so `partitionCoverNumber` equals `1`.
example : partitionCoverNumber true (uniqueDisjointnessRel (Fin 0)) Set.univ Set.univ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, partitionCoverNumber_le_iff]
    refine ⟨fun _ => (Set.univ, Set.univ), ?_, fun a _ b _ _ => ⟨0, ⟨trivial, trivial⟩,
      fun i _ => Subsingleton.elim i 0⟩⟩
    intro _ a _ _ b _ _
    simp only [uniqueDisjointnessRel, ↓reduceIte, Subsingleton.elim a ∅,
      Subsingleton.elim b ∅, inter_self, card_empty, ne_eq, zero_ne_one, not_false_eq_true]
  · have hkw := three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel (α := Fin 0)
    simp only [Fintype.card_fin, pow_zero, one_mul, Nat.cast_one] at hkw
    exact hkw.trans coverNumber_le_partitionCoverNumber

-- On `Fin 1`, `partitionCoverNumber` and `coverNumber` both equal `2`: `({∅}, {∅, {0}})` and
-- `({{0}}, {∅})` partition all three disjoint pairs while avoiding `({0}, {0})`.
private def fin1Cover : Fin 2 → Set (Finset (Fin 1)) × Set (Finset (Fin 1))
  | 0 => ({∅}, {∅, {0}})
  | 1 => ({{0}}, {∅})

private theorem isPartitionCover_fin1Cover :
    IsPartitionCover true (uniqueDisjointnessRel (Fin 1)) Set.univ Set.univ fin1Cover := by
  refine ⟨fun i a _ ha b _ hb => ?_, fun a _ b _ hreq => ?_⟩
  · fin_cases i
    · simp only [fin1Cover, Set.mem_singleton_iff] at ha
      subst ha
      simp [uniqueDisjointnessRel]
    · simp only [fin1Cover, Set.mem_singleton_iff] at hb
      subst hb
      simp [uniqueDisjointnessRel]
  · simp only [uniqueDisjointnessRel, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      not_not] at hreq
    by_cases ha : a = ∅
    · subst ha
      refine ⟨0, ⟨rfl, ?_⟩, fun j hj => ?_⟩
      · by_cases hb0 : (0 : Fin 1) ∈ b
        · refine Or.inr (ext fun x => ?_)
          rw [Subsingleton.elim x 0]
          simp [hb0]
        · refine Or.inl (eq_empty_iff_forall_notMem.2 fun x hx => hb0 ?_)
          rwa [Subsingleton.elim x 0] at hx
      · fin_cases j
        · rfl
        · simp [fin1Cover, eq_comm (a := ∅)] at hj
    · have ha0 : a = {0} := by
        obtain ⟨x, hx⟩ := ne_empty_iff_nonempty.1 ha
        ext y
        rw [Subsingleton.elim y 0, Subsingleton.elim x 0] at *
        simp [hx]
      have hb0 : b = ∅ := by
        subst ha0
        exact eq_empty_iff_forall_notMem.2 fun y hy => by
          rw [Subsingleton.elim y 0] at hy
          exact Finset.disjoint_left.1 hreq (mem_singleton_self 0) hy
      subst ha0 hb0
      refine ⟨1, ⟨rfl, rfl⟩, fun j hj => ?_⟩
      fin_cases j
      · simp [fin1Cover] at hj
      · rfl

private theorem two_le_coverNumber_fin1 :
    (2 : ℕ∞) ≤ coverNumber true (uniqueDisjointnessRel (Fin 1)) Set.univ Set.univ := by
  have hkw := three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel (α := Fin 1)
  simp only [Fintype.card_fin, pow_one] at hkw
  by_contra! hlt
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  rw [← hr] at hlt hkw
  have hr2 : r < 2 := by exact_mod_cast hlt
  have hnat : 3 ≤ 2 * r := by exact_mod_cast hkw
  omega

example : partitionCoverNumber true (uniqueDisjointnessRel (Fin 1)) Set.univ Set.univ = 2 :=
  le_antisymm
    (isPartitionCover_fin1Cover.partitionCoverNumber_le.trans_eq (by simp))
    (two_le_coverNumber_fin1.trans coverNumber_le_partitionCoverNumber)

-- Negative rectangle witness on `Fin 2`: putting `({0}, {1})` and `({1}, {0})` in one rectangle
-- forces cross-pair `({0}, {0})`, which has intersection size `1` and violates monochromaticity.
private def invalidFin2Cover : Fin 1 → Set (Finset (Fin 2)) × Set (Finset (Fin 2)) :=
  fun _ => ({{0}, {1}}, {{1}, {0}})

example : ¬ IsCover true (uniqueDisjointnessRel (Fin 2)) Set.univ Set.univ invalidFin2Cover := by
  rintro ⟨hmem, _⟩
  have hbad := hmem 0 {0} trivial (Or.inl rfl) {0} trivial (Or.inr rfl)
  simp [uniqueDisjointnessRel] at hbad

-- Subtle `*`-entry vs `1`-entry boundary on `Fin 2`: on the subdomain `A = B = {∅, {0, 1}}`,
-- `({0, 1}, {0, 1})` has intersection size `2` (a `*`-entry where `false` IS acceptable), so a
-- partition cover MAY cover `({0, 1}, {0, 1})` twice while covering the `1`-entries uniquely...
private def subDomFin2 : Set (Finset (Fin 2)) := {∅, {0, 1}}

private def starOverlapCover : Fin 2 → Set (Finset (Fin 2)) × Set (Finset (Fin 2))
  | 0 => ({{0, 1}}, {{0, 1}})
  | 1 => (subDomFin2, subDomFin2)

example : IsPartitionCover true (uniqueDisjointnessRel (Fin 2)) subDomFin2 subDomFin2
    starOverlapCover := by
  refine ⟨fun i a ha _ b hb _ => ?_, fun a ha b hb hreq => ?_⟩
  · simp only [uniqueDisjointnessRel, ↓reduceIte]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  · simp only [uniqueDisjointnessRel, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      not_not] at hreq
    refine ⟨1, ⟨ha, hb⟩, fun j hj => ?_⟩
    fin_cases j
    · simp only [starOverlapCover, Set.mem_singleton_iff] at hj
      rcases hj with ⟨rfl, rfl⟩
      exact absurd hreq (by decide)
    · rfl

-- ...whereas covering the `1`-entry `(∅, ∅)` twice yields an ordinary `IsCover` that is NOT an
-- `IsPartitionCover`.
private def oneEntryOverlapCover : Fin 2 → Set (Finset (Fin 2)) × Set (Finset (Fin 2))
  | 0 => ({∅}, {∅})
  | 1 => (subDomFin2, subDomFin2)

example : IsCover true (uniqueDisjointnessRel (Fin 2)) subDomFin2 subDomFin2
    oneEntryOverlapCover ∧
    ¬ IsPartitionCover true (uniqueDisjointnessRel (Fin 2)) subDomFin2 subDomFin2
      oneEntryOverlapCover := by
  refine ⟨⟨fun i a ha _ b hb _ => ?_, fun a ha b hb _ => ⟨1, ha, hb⟩⟩, fun ⟨_, huniq⟩ => ?_⟩
  · simp only [uniqueDisjointnessRel, ↓reduceIte]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  · have hreq : ¬ uniqueDisjointnessRel (Fin 2) ∅ ∅ (!true) := by
      simp [uniqueDisjointnessRel]
    obtain ⟨w, _, hw⟩ := huniq ∅ (Or.inl rfl) ∅ (Or.inl rfl) hreq
    have h0 : w = 0 := (hw 0 ⟨rfl, rfl⟩).symm
    have h1 : w = 1 := (hw 1 ⟨Or.inl rfl, Or.inl rfl⟩).symm
    exact absurd (h0.symm.trans h1) (by decide)

-- Equivalence between `partitionCoverNumber` and minimum `(ℕ, +, ·)`-semiring rank on `Fin 1`.
example :
    (⨅ (M : Matrix (Finset (Fin 1)) (Finset (Fin 1)) ℕ)
      (_ : (∀ a b, ¬ uniqueDisjointnessRel (Fin 1) a b (!true) → M a b = 1) ∧
        (∀ a b, ¬ uniqueDisjointnessRel (Fin 1) a b true → M a b = 0)),
      M.nonnegRank) = 2 := by
  rw [← partitionCoverNumber_eq_iInf_nonnegRank_nat]
  exact le_antisymm
    (isPartitionCover_fin1Cover.partitionCoverNumber_le.trans_eq (by simp))
    (two_le_coverNumber_fin1.trans coverNumber_le_partitionCoverNumber)

/-! ### 4. Sergeev's Theorem 1 and Theorem 2 with Kaibel–Weltge -/

-- Theorem 1 specialized to `Fin 3`: `partitionCoverNumber ≤ (3 + 1)^3 * C(3, 1) = 192`.
example :
    partitionCoverNumber true (uniqueDisjointnessRel (Fin 3)) Set.univ Set.univ ≤ 192 := by
  simpa using partitionCoverNumber_uniqueDisjointnessRel_le (α := Fin 3)

-- Real exponential form of Theorem 1 on `Fin 3`.
example : ∃ r : ℕ,
    partitionCoverNumber true (uniqueDisjointnessRel (Fin 3)) Set.univ Set.univ = r ∧
      (r : ℝ) ≤ 64 * (3 / (4 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
  obtain ⟨r, hr, hle⟩ := exists_partitionCoverNumber_uniqueDisjointnessRel_le_rpow (α := Fin 3)
  refine ⟨r, hr, hle.trans_eq ?_⟩
  simp only [Fintype.card_fin]
  norm_num

-- Asymptotic `1.89^n` form of Theorem 1.
example : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ r : ℕ,
    partitionCoverNumber true (uniqueDisjointnessRel (Fin n)) Set.univ Set.univ = r ∧
      (r : ℝ) < (189 / 100 : ℝ) ^ n := by
  simpa only [Filter.eventually_atTop] using
    eventually_partitionCoverNumber_uniqueDisjointnessRel_lt

-- Two-sided `ℕ∞` sandwich on `Fin 3` combining Kaibel–Weltge and Sergeev's Theorem 2.
example :
    (27 : ℕ∞) ≤ 8 * coverNumber true (uniqueDisjointnessRel (Fin 3)) Set.univ Set.univ ∧
      8 * coverNumber true (uniqueDisjointnessRel (Fin 3)) Set.univ Set.univ ≤ 3538944 := by
  have hlow := three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel (α := Fin 3)
  have hupp := two_pow_mul_coverNumber_uniqueDisjointnessRel_le (α := Fin 3)
  simp only [Fintype.card_fin] at hlow hupp
  norm_num at hlow hupp
  exact ⟨hlow, hupp⟩

-- Polynomial-factor tightness instantiated at `n = 2`.
example : ∃ C k : ℕ, ∃ r : ℕ,
    coverNumber true (uniqueDisjointnessRel (Fin 2)) Set.univ Set.univ = r ∧
      (9 / 4 : ℝ) ≤ r ∧ (r : ℝ) ≤ C * (2 : ℝ) ^ k * (9 / 4 : ℝ) := by
  obtain ⟨C, k, h⟩ := exists_poly_coverNumber_uniqueDisjointnessRel
  obtain ⟨r, hr, hlow, hupp⟩ := h 2 (by omega)
  refine ⟨C, k, r, hr, ?_, ?_⟩
  · norm_num at hlow ⊢
    exact hlow
  · norm_num at hupp ⊢
    exact hupp

end CslibFrontierTests.UniqueDisjointnessUpper
