/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Nondeterministic.PartitionCover
public import CslibFrontier.Computability.Communication.Nondeterministic.UniqueDisjointness
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Combinatorics.CentralBinomial
import CslibFrontier.Foundations.Combinatorics.LovaszSteinCover
import CslibFrontier.Foundations.Data.Code.HammingCode
import CslibFrontier.Foundations.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Upper bounds on the partition rank and covering rank of unique disjointness

This module formalizes Igor S. Sergeev's upper bounds on the SUM-rank (partition cover number
`partitionCoverNumber`) and OR-rank (rectangle covering number `coverNumber`) of the unique
disjointness relation `uniqueDisjointnessRel` [Sergeev2026UniqueDisjointness]:

1. **SUM-rank / partition cover number ([Sergeev2026UniqueDisjointness, §2, Theorem 1, pp. 3–4])**:
   Partitioning inputs `(a, b)` of `uniqueDisjointnessRel α` (`|α| = n`) by their weights
   `p = |a|` and `q = |b|` (`p + q ≤ n`) and choosing the smaller of row singletons (`C(n, p)`),
   column singletons (`C(n, q)`), and the Hamming `3`-code partition over `(p + q)`-subsets `S`
   (`≤ max 1 (2 n) C(n, p + q)`) bounds the partition cover number by
   `(n + 1) ^ 3 * C(n, ⌊n / 3⌋)` (`partitionCoverNumber_uniqueDisjointnessRel_le`). Since
   `4 ^ n C(n, ⌊n / 3⌋) ^ 3 ≤ 27 ^ n`, this yields `(n + 1) ^ 3 (3 / 4 ^ (1 / 3)) ^ n` for every
   `n` (`exists_partitionCoverNumber_uniqueDisjointnessRel_le_rpow`) and strictly less than
   `(189 / 100) ^ n` (`1.89 ^ n`) for all sufficiently large `n`
   (`eventually_partitionCoverNumber_uniqueDisjointnessRel_lt`).
2. **OR-rank / covering number ([Sergeev2026UniqueDisjointness, §3, Theorem 2, pp. 4–6])**:
   Combining the Sapozhenko–Lovász–Stein greedy covering bound
   (`Cslib.exists_cover_card_le_of_const_hit`) with variable separation and Hamming `3`-code
   partitions across the weight regimes `2 (p + q) ≤ n`, `n < 2 (p + q)` with `2 p ≤ n`, and
   `n < 2 p` proves that `coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ` is at most
   `8 (n + 1) ^ 7 (3 / 2) ^ n` (`exists_coverNumber_uniqueDisjointnessRel_le`), matching the
   Kaibel–Weltge `(3 / 2) ^ n` lower bound
   (`three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel`) up to a polynomial factor
   (`exists_poly_coverNumber_uniqueDisjointnessRel`).

## Main results

* `Cslib.Communication.Nondeterministic.partitionCoverNumber_uniqueDisjointnessRel_le`:
  `partitionCoverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ ≤
    (Fintype.card α + 1) ^ 3 * (Fintype.card α).choose (Fintype.card α / 3)`.
* `Cslib.Communication.Nondeterministic.exists_partitionCoverNumber_uniqueDisjointnessRel_le_rpow`:
  real form `(r : ℝ) ≤ (|α| + 1) ^ 3 * (3 / 4 ^ (1 / 3)) ^ |α|` of Theorem 1.
* `Cslib.Communication.Nondeterministic.eventually_partitionCoverNumber_uniqueDisjointnessRel_lt`:
  asymptotic `rk_+ U_n < (189 / 100) ^ n` form of Theorem 1.
* `Cslib.Communication.Nondeterministic.exists_coverNumber_uniqueDisjointnessRel_le`,
  `Cslib.Communication.Nondeterministic.two_pow_mul_coverNumber_uniqueDisjointnessRel_le`:
  explicit `8 (|α| + 1) ^ 7 (3 / 2) ^ |α|` upper bound on `coverNumber` (Theorem 2).
* `Cslib.Communication.Nondeterministic.exists_poly_coverNumber_uniqueDisjointnessRel`:
  two-sided tightness `(3 / 2) ^ n ≤ r ≤ C * n ^ k * (3 / 2) ^ n` combining Kaibel–Weltge and
  Sergeev's Theorem 2.

## References

* [V. Kaibel, S. Weltge, *A short proof that the extension complexity of the correlation polytope
  grows exponentially*][KaibelWeltge2015], §2 (proof of Theorem 1, p. 3) and §3 (p. 3)
* [I. S. Sergeev, *Upper Bounds for the Monotone Rank of the Unique Disjointness Matrix*]
  [Sergeev2026UniqueDisjointness], §2 (Theorem 1) and §3 (Theorem 2)
-/

public section

namespace Cslib.Communication

namespace Nondeterministic

open Finset

section Helpers

/-- Zero-extended Hamming syndrome of `a ⊆ S`, typed cleanly in `BitString k` without dependent
casts on `S.card`. When `Nat.clog 2 (S.card + 1) ≤ k`, `BitString.zeroExtend_injective` recovers
equality of `Code.finsetHammingSyndrome S`. -/
private noncomputable def synPad {α : Type*} [DecidableEq α] (k : ℕ) (S a : Finset α) :
    BitString k :=
  BitString.zeroExtend (Code.finsetHammingSyndrome S a)

/-- Core geometric observation of [Sergeev2026UniqueDisjointness, §2, p. 4]: if `a, a' ⊆ S` have
the same cardinality and satisfy `a ≠ a' → 3 ≤ #(symmDiff a a')`, then `#(a ∩ (S \ a')) ≠ 1`
(it is `0` when `a = a'` and at least `2` when `a ≠ a'`). -/
private theorem card_inter_sdiff_ne_one_of_three_le_symmDiff {α : Type*} [DecidableEq α]
    {S a a' : Finset α} (haS : a ⊆ S) (hcard : a.card = a'.card)
    (hd : a ≠ a' → 3 ≤ (symmDiff a a').card) :
    (a ∩ (S \ a')).card ≠ 1 := by
  rw [← inter_sdiff_assoc, inter_eq_left.2 haS]
  by_cases heq : a = a'
  · simp [heq]
  · have h3 := hd heq
    rw [Finset.symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff] at h3
    have h1 := card_sdiff_add_card_inter a a'
    have h2 := card_sdiff_add_card_inter a' a
    rw [inter_comm] at h2
    omega

private theorem card_inter_sdiff_ne_one_of_synPad_eq {α : Type*} [DecidableEq α]
    {k : ℕ} {S a a' : Finset α} (hk : Nat.clog 2 (S.card + 1) ≤ k)
    (haS : a ⊆ S) (ha'S : a' ⊆ S) (hcard : a.card = a'.card)
    (hsyn : synPad k S a = synPad k S a') :
    (a ∩ (S \ a')).card ≠ 1 :=
  card_inter_sdiff_ne_one_of_three_le_symmDiff haS hcard fun hne =>
    Code.three_le_card_symmDiff_of_finsetHammingSyndrome_eq haS ha'S hne
      (BitString.zeroExtend_injective hk hsyn)

/-- Subsets of `α` of fixed cardinality `k`. -/
private def weightSlice (α : Type*) (k : ℕ) : Set (Finset α) :=
  {s | s.card = k}

private def cardFin (α : Type*) [Fintype α] (s : Finset α) : Fin (Fintype.card α + 1) :=
  ⟨s.card, Nat.lt_succ_of_le s.card_le_univ⟩

private theorem weightSlice_eq_univ_inter_preimage {α : Type*} [Fintype α]
    (p : Fin (Fintype.card α + 1)) :
    (Set.univ : Set (Finset α)) ∩ cardFin α ⁻¹' {p} = weightSlice α p.val := by
  ext s
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage, Set.mem_singleton_iff,
    cardFin, Fin.ext_iff, weightSlice, Set.mem_ofPred_eq]

private theorem partitionCoverNumber_weightSlice_eq_zero_of_lt {α : Type*} [Fintype α]
    [DecidableEq α] {p q : ℕ} (hlt : Fintype.card α < p + q) :
    partitionCoverNumber true (uniqueDisjointnessRel α)
      (weightSlice α p) (weightSlice α q) = 0 := by
  refine nonpos_iff_eq_zero.1 (partitionCoverNumber_le_iff (r := 0).2
    ⟨Fin.elim0, fun i => i.elim0, fun a ha b hb hnd => ?_⟩)
  simp only [Bool.not_true, uniqueDisjointnessRel, Bool.false_eq_true, ↓reduceIte, not_not] at hnd
  have hunion : (a ∪ b).card ≤ Fintype.card α := card_le_univ (a ∪ b)
  rw [card_union_of_disjoint hnd, ha, hb] at hunion
  omega

private theorem uniqueDisjointnessRel_comm {α : Type*} [DecidableEq α] (a b : Finset α)
    (z : Bool) : uniqueDisjointnessRel α a b z ↔ uniqueDisjointnessRel α b a z := by
  rw [uniqueDisjointnessRel, uniqueDisjointnessRel, inter_comm, disjoint_comm]

private theorem partitionCoverNumber_weightSlice_symm {α : Type*} [DecidableEq α] (p q : ℕ) :
    partitionCoverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) =
      partitionCoverNumber true (uniqueDisjointnessRel α) (weightSlice α q) (weightSlice α p) := by
  have hle : ∀ u v,
      partitionCoverNumber true (uniqueDisjointnessRel α) (weightSlice α u) (weightSlice α v) ≤
        partitionCoverNumber true (uniqueDisjointnessRel α)
          (weightSlice α v) (weightSlice α u) := fun u v =>
    le_partitionCoverNumber_iff.2 fun r C hC =>
      partitionCoverNumber_le_iff.2 ⟨fun i => ((C i).2, (C i).1),
        fun i a ha haC b hb hbC => (uniqueDisjointnessRel_comm ..).1 (hC.1 i b hb hbC a ha haC),
        fun a ha b hb hnd => (existsUnique_congr fun _ => and_comm).1
          (hC.2 b hb a ha ((uniqueDisjointnessRel_comm ..).not.1 hnd))⟩
  exact le_antisymm (hle p q) (hle q p)

private theorem coverNumber_weightSlice_symm {α : Type*} [DecidableEq α] (p q : ℕ) :
    coverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) =
      coverNumber true (uniqueDisjointnessRel α) (weightSlice α q) (weightSlice α p) := by
  have hle : ∀ u v,
      coverNumber true (uniqueDisjointnessRel α) (weightSlice α u) (weightSlice α v) ≤
        coverNumber true (uniqueDisjointnessRel α) (weightSlice α v) (weightSlice α u) :=
    fun u v => le_coverNumber_iff.2 fun r C hC =>
      coverNumber_le_iff.2 ⟨fun i => ((C i).2, (C i).1),
        fun i a ha haC b hb hbC => (uniqueDisjointnessRel_comm ..).1 (hC.1 i b hb hbC a ha haC),
        fun a ha b hb hnd => (hC.2 b hb a ha ((uniqueDisjointnessRel_comm ..).not.1 hnd)).imp
          fun _ h => h.symm⟩
  exact le_antisymm (hle p q) (hle q p)

end Helpers

/-! ### Section 2: Theorem 1 — SUM-rank / Partition Cover Number Upper Bound -/

section Theorem1

private theorem partitionCoverNumber_weightSlice_le_choose_left {α : Type*} [Fintype α]
    [DecidableEq α] (p q : ℕ) :
    partitionCoverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) ≤
      ((Fintype.card α).choose p : ℕ) := by
  let κ := (univ : Finset α).powersetCard p
  let C : κ → Set (Finset α) × Set (Finset α) :=
    fun a₀ => ({a₀.val}, {b | Disjoint a₀.val b})
  have hcov : IsPartitionCover true (uniqueDisjointnessRel α)
      (weightSlice α p) (weightSlice α q) C := by
    refine ⟨fun a₀ a _ ha b _ hb => ?_, fun a ha b _ hnd => ?_⟩
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [uniqueDisjointnessRel, ↓reduceIte]
      rw [disjoint_iff_inter_eq_empty.1 hb, card_empty]
      decide
    · simp only [Bool.not_true, uniqueDisjointnessRel, Bool.false_eq_true, ↓reduceIte,
        not_not] at hnd
      let a₀ : κ := ⟨a, mem_powersetCard.2 ⟨subset_univ a, ha⟩⟩
      refine ⟨a₀, ⟨rfl, hnd⟩, ?_⟩
      rintro ⟨a', ha'⟩ ⟨ha_eq, -⟩
      exact Subtype.ext ha_eq.symm
  refine hcov.partitionCoverNumber_le.trans_eq ?_
  congr 1
  simp only [κ, Fintype.card_coe, card_powersetCard, card_univ]

private theorem partitionCoverNumber_weightSlice_le_choose_right {α : Type*} [Fintype α]
    [DecidableEq α] (p q : ℕ) :
    partitionCoverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) ≤
      ((Fintype.card α).choose q : ℕ) := by
  rw [partitionCoverNumber_weightSlice_symm]
  exact partitionCoverNumber_weightSlice_le_choose_left q p

private theorem partitionCoverNumber_weightSlice_le_code {α : Type*} [Fintype α] [DecidableEq α]
    {p q : ℕ} (hpq : p + q ≤ Fintype.card α) :
    partitionCoverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) ≤
      (max 1 (2 * Fintype.card α) * (Fintype.card α).choose (p + q) : ℕ) := by
  set k := Nat.clog 2 (p + q + 1)
  let κ := (univ : Finset α).powersetCard (p + q) × BitString k
  let Y (S : Finset α) (syn : BitString k) : Set (Finset α) :=
    {a | a ⊆ S ∧ a.card = p ∧ synPad k S a = syn}
  let C : κ → Set (Finset α) × Set (Finset α) :=
    fun ⟨S, syn⟩ => (Y S.val syn, {b | ∃ a' ∈ Y S.val syn, b = S.val \ a'})
  have hcov : IsPartitionCover true (uniqueDisjointnessRel α)
      (weightSlice α p) (weightSlice α q) C := by
    refine ⟨fun ⟨S, syn⟩ a _ ha b _ hb => ?_, fun a ha b hb hnd => ?_⟩
    · obtain ⟨a', ha', rfl⟩ := hb
      have hScard : S.val.card = p + q := (mem_powersetCard.1 S.property).2
      simp only [uniqueDisjointnessRel, ↓reduceIte]
      exact card_inter_sdiff_ne_one_of_synPad_eq (by rw [hScard]) ha.1 ha'.1
        (ha.2.1.trans ha'.2.1.symm) (ha.2.2.trans ha'.2.2.symm)
    · simp only [Bool.not_true, uniqueDisjointnessRel, Bool.false_eq_true, ↓reduceIte,
        not_not] at hnd
      have hunion_card : (a ∪ b).card = p + q := by
        rw [card_union_of_disjoint hnd, ha, hb]
      let S₀ : (univ : Finset α).powersetCard (p + q) :=
        ⟨a ∪ b, mem_powersetCard.2 ⟨subset_univ _, hunion_card⟩⟩
      let syn₀ : BitString k := synPad k S₀.val a
      have haY : a ∈ Y S₀.val syn₀ := ⟨subset_union_left, ha, rfl⟩
      have hbC : b ∈ (C ⟨S₀, syn₀⟩).2 := ⟨a, haY, (union_sdiff_cancel_left hnd).symm⟩
      refine ⟨⟨S₀, syn₀⟩, ⟨haY, hbC⟩, ?_⟩
      rintro ⟨S', syn'⟩ ⟨haY', a', _, hb_eq⟩
      have hS'_sub : a ∪ b ⊆ S'.val := union_subset haY'.1 (hb_eq ▸ sdiff_subset)
      have hS'_card : S'.val.card = p + q := (mem_powersetCard.1 S'.property).2
      have hS'_eq : S'.val = S₀.val :=
        (eq_of_subset_of_card_le hS'_sub (by rw [hS'_card, hunion_card])).symm
      have hS_sub_eq : S' = S₀ := Subtype.ext hS'_eq
      subst hS_sub_eq
      exact Prod.ext rfl haY'.2.2.symm
  have hcard : Fintype.card κ ≤ max 1 (2 * Fintype.card α) * (Fintype.card α).choose (p + q) := by
    have h1 : Fintype.card κ = (Fintype.card α).choose (p + q) * 2 ^ k := by
      rw [Fintype.card_prod, BitString.card]
      simp only [Fintype.card_coe, card_powersetCard, card_univ]
    have h2 : 2 ^ k ≤ max 1 (2 * Fintype.card α) :=
      (Code.two_pow_clog_succ_le_max (p + q)).trans (max_le_max le_rfl (by omega))
    rw [h1, mul_comm]
    exact Nat.mul_le_mul_right _ h2
  exact hcov.partitionCoverNumber_le.trans (by exact_mod_cast hcard)

private theorem partitionCoverNumber_weightSlice_le_third {α : Type*} [Fintype α] [DecidableEq α]
    {p q : ℕ} (hpq : p + q ≤ Fintype.card α) :
    partitionCoverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) ≤
      (max 1 (2 * Fintype.card α) * (Fintype.card α).choose (Fintype.card α / 3) : ℕ) := by
  set n := Fintype.card α
  have hmax_pos : 1 ≤ max 1 (2 * n) := le_max_left 1 (2 * n)
  have h3 : p ≤ n / 3 ∨ q ≤ n / 3 ∨ n - (p + q) ≤ n / 3 := by omega
  rcases h3 with hp | hq | hr
  · have hch : n.choose p ≤ max 1 (2 * n) * n.choose (n / 3) :=
      (Cslib.choose_le_choose_of_le_of_le_half hp (by omega)).trans
        (Nat.le_mul_of_pos_left _ hmax_pos)
    exact (partitionCoverNumber_weightSlice_le_choose_left p q).trans (by exact_mod_cast hch)
  · have hch : n.choose q ≤ max 1 (2 * n) * n.choose (n / 3) :=
      (Cslib.choose_le_choose_of_le_of_le_half hq (by omega)).trans
        (Nat.le_mul_of_pos_left _ hmax_pos)
    exact (partitionCoverNumber_weightSlice_le_choose_right p q).trans (by exact_mod_cast hch)
  · have hch : n.choose (p + q) ≤ n.choose (n / 3) := by
      rw [← Nat.choose_symm hpq]
      exact Cslib.choose_le_choose_of_le_of_le_half hr (by omega)
    exact (partitionCoverNumber_weightSlice_le_code hpq).trans
      (by exact_mod_cast Nat.mul_le_mul_left _ hch)

private theorem two_mul_sum_range_succ (m : ℕ) :
    2 * ∑ i ∈ range m, (i + 1) = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

private theorem sum_pairs_le_mul_max_le_cube (n : ℕ) :
    (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
      if p.val + q.val ≤ n then max 1 (2 * n) else 0) ≤ (n + 1) ^ 3 := by
  have hrow : ∀ p : Fin (n + 1),
      (∑ q : Fin (n + 1), if p.val + q.val ≤ n then max 1 (2 * n) else 0) =
        (n + 1 - p.val) * max 1 (2 * n) := by
    intro p
    rw [← sum_filter]
    have hfilt : (univ.filter fun q : Fin (n + 1) => p.val + q.val ≤ n).card = n + 1 - p.val := by
      rw [← card_range (n + 1 - p.val)]
      refine card_bij (fun (q : Fin (n + 1)) _ => q.val) (fun q hq => ?_)
        (fun q₁ _ q₂ _ h => Fin.ext h) (fun j hj => ?_)
      · rw [mem_filter] at hq
        exact mem_range.2 (by omega)
      · rw [mem_range] at hj
        exact ⟨⟨j, by omega⟩, mem_filter.2 ⟨mem_univ _, by dsimp; omega⟩, rfl⟩
    rw [sum_const, hfilt, smul_eq_mul]
  simp_rw [hrow, ← sum_mul, Fin.sum_univ_eq_sum_range (fun i => n + 1 - i)]
  have hrev : ∑ i ∈ range (n + 1), (n + 1 - i) = ∑ i ∈ range (n + 1), (i + 1) := by
    have hr := sum_range_reflect (fun i => i + 1) (n + 1)
    refine (sum_congr rfl fun j hj => ?_).trans hr
    rw [mem_range] at hj
    omega
  have htri : 2 * ∑ i ∈ range (n + 1), (n + 1 - i) = (n + 1) * (n + 2) := by
    rw [hrev, two_mul_sum_range_succ]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hmax : max 1 (2 * n) = 2 * n := max_eq_right (by omega)
    rw [hmax]
    calc (∑ i ∈ range (n + 1), (n + 1 - i)) * (2 * n)
        = (2 * ∑ i ∈ range (n + 1), (n + 1 - i)) * n := by ring
      _ = (n + 1) * (n + 2) * n := by rw [htri]
      _ ≤ (n + 1) ^ 3 := by nlinarith

/-- **SUM-rank (partition cover number) upper bound for unique disjointness**
([Sergeev2026UniqueDisjointness, §2, Theorem 1, pp. 3–4]): on any finite ground type `α` of size
`n = |α|`, `uniqueDisjointnessRel α` has a partition `1`-cover by at most
`(n + 1) ^ 3 * C(n, ⌊n / 3⌋)` rectangles. -/
theorem partitionCoverNumber_uniqueDisjointnessRel_le {α : Type*} [Fintype α] [DecidableEq α] :
    partitionCoverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ ≤
      (((Fintype.card α + 1) ^ 3 * (Fintype.card α).choose (Fintype.card α / 3) : ℕ) : ℕ∞) := by
  set n := Fintype.card α
  calc partitionCoverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ
      ≤ ∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
          partitionCoverNumber true (uniqueDisjointnessRel α)
            (Set.univ ∩ cardFin α ⁻¹' {p}) (Set.univ ∩ cardFin α ⁻¹' {q}) :=
        partitionCoverNumber_le_sum_fibers (cardFin α) (cardFin α)
    _ ≤ ∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
          (((if p.val + q.val ≤ n then max 1 (2 * n) else 0) * n.choose (n / 3) : ℕ) : ℕ∞) := by
        refine sum_le_sum fun p _ => sum_le_sum fun q _ => ?_
        rw [weightSlice_eq_univ_inter_preimage, weightSlice_eq_univ_inter_preimage]
        split_ifs with hpq
        · exact partitionCoverNumber_weightSlice_le_third hpq
        · rw [partitionCoverNumber_weightSlice_eq_zero_of_lt (by omega)]
          simp
    _ = (((∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
          if p.val + q.val ≤ n then max 1 (2 * n) else 0) * n.choose (n / 3) : ℕ) : ℕ∞) := by
        push_cast
        simp_rw [← sum_mul]
    _ ≤ (((n + 1) ^ 3 * n.choose (n / 3) : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.mul_le_mul_right _ (sum_pairs_le_mul_max_le_cube n)

private theorem exists_eq_natCast_of_le {x : ℕ∞} {m : ℕ} (h : x ≤ m) :
    ∃ r : ℕ, x = r ∧ r ≤ m := by
  obtain ⟨r, rfl⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top m) h)
  exact ⟨r, rfl, by exact_mod_cast h⟩

private theorem choose_third_cube_le (n : ℕ) :
    (n.choose (n / 3) : ℝ) ^ 3 ≤ (27 / 4 : ℝ) ^ n := by
  have hle : (n.choose (n / 3) * 2 ^ n : ℝ) ≤ 2 ^ (n / 3) * 3 ^ n := by
    exact_mod_cast (Nat.mul_le_mul_right _ (single_le_sum (fun _ _ => Nat.zero_le _)
      (mem_range.2 (Nat.lt_succ_self _)))).trans (Cslib.sum_range_choose_mul_pow_le 2 n (n / 3))
  have h2 : ((2 : ℝ) ^ (n / 3)) ^ 3 ≤ 2 ^ n := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.div_mul_le_self n 3)
  have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  have h27 : (27 : ℝ) ^ n = 3 ^ n * 3 ^ n * 3 ^ n := by rw [← mul_pow, ← mul_pow]; norm_num
  have key : (n.choose (n / 3) : ℝ) ^ 3 * 4 ^ n * 2 ^ n ≤ 27 ^ n * 2 ^ n :=
    calc (n.choose (n / 3) : ℝ) ^ 3 * 4 ^ n * 2 ^ n = (n.choose (n / 3) * 2 ^ n : ℝ) ^ 3 := by
          rw [h4]; ring
      _ ≤ (2 ^ (n / 3) * 3 ^ n) ^ 3 := pow_le_pow_left₀ (by positivity) hle 3
      _ = ((2 : ℝ) ^ (n / 3)) ^ 3 * 27 ^ n := by rw [h27]; ring
      _ ≤ 27 ^ n * 2 ^ n := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [div_pow, le_div_iff₀ (by positivity)]
  exact le_of_mul_le_mul_right key (by positivity)

/-- **Real exponential form of Sergeev's Theorem 1**
([Sergeev2026UniqueDisjointness, §2, Theorem 1, p. 3]): on any finite ground type `α`,
`partitionCoverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ` is a finite natural number
`r ≤ (|α| + 1) ^ 3 * (3 / 4 ^ (1 / 3)) ^ |α|`. -/
theorem exists_partitionCoverNumber_uniqueDisjointnessRel_le_rpow {α : Type*} [Fintype α]
    [DecidableEq α] :
    ∃ r : ℕ,
      partitionCoverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ = r ∧
        (r : ℝ) ≤ (Fintype.card α + 1 : ℝ) ^ 3 * (3 / (4 : ℝ) ^ (1 / 3 : ℝ)) ^ Fintype.card α := by
  set n := Fintype.card α
  obtain ⟨r, hr, hr_nat⟩ :=
    exists_eq_natCast_of_le (partitionCoverNumber_uniqueDisjointnessRel_le (α := α))
  refine ⟨r, hr, ?_⟩
  have h4_3 : ((4 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hch : (n.choose (n / 3) : ℝ) ≤ (3 / (4 : ℝ) ^ (1 / 3 : ℝ)) ^ n := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) three_ne_zero, ← pow_mul,
      mul_comm n 3, pow_mul, div_pow, h4_3, show (3 : ℝ) ^ 3 / 4 = 27 / 4 by norm_num]
    exact choose_third_cube_le n
  calc (r : ℝ) ≤ (n + 1 : ℝ) ^ 3 * n.choose (n / 3) := by exact_mod_cast hr_nat
    _ ≤ (n + 1 : ℝ) ^ 3 * (3 / (4 : ℝ) ^ (1 / 3 : ℝ)) ^ n := by gcongr

/-- **Asymptotic `1.89 ^ n` upper bound on the SUM-rank of unique disjointness**
([Sergeev2026UniqueDisjointness, §2, Theorem 1, p. 3]): for all sufficiently large `n`,
`partitionCoverNumber true (uniqueDisjointnessRel (Fin n)) Set.univ Set.univ` is strictly less than
`(189 / 100) ^ n`. -/
theorem eventually_partitionCoverNumber_uniqueDisjointnessRel_lt :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ r : ℕ,
        partitionCoverNumber true (uniqueDisjointnessRel (Fin n)) Set.univ Set.univ = r ∧
          (r : ℝ) < (189 / 100 : ℝ) ^ n := by
  let c : ℝ := (189 / 100 : ℝ) ^ 3 / (27 / 4 : ℝ)
  have hc : 1 < c := by norm_num [c]
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 ((tendsto_pow_const_div_const_pow_of_one_lt 9 hc
    ).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / c)))
  refine Filter.eventually_atTop.2 ⟨M₀, fun n hn => ?_⟩
  have hle := partitionCoverNumber_uniqueDisjointnessRel_le (α := Fin n)
  rw [Fintype.card_fin] at hle
  obtain ⟨r, hr, hr_nat⟩ := exists_eq_natCast_of_le hle
  refine ⟨r, hr, ?_⟩
  have hpoly : (n + 1 : ℝ) ^ 9 < c ^ n := by
    have h1 : (((n + 1 : ℕ) : ℝ) ^ 9) / c ^ (n + 1) < 1 / c := hM₀ (n + 1) (by omega)
    rw [div_lt_iff₀ (by positivity), pow_succ' c n, one_div,
      inv_mul_cancel_left₀ (zero_lt_one.trans hc).ne'] at h1
    exact_mod_cast h1
  rw [← pow_lt_pow_iff_left₀ (by positivity) (by positivity) three_ne_zero]
  calc (r : ℝ) ^ 3 ≤ ((n + 1 : ℝ) ^ 3 * n.choose (n / 3)) ^ 3 := by
        gcongr; exact_mod_cast hr_nat
    _ = (n + 1 : ℝ) ^ 9 * (n.choose (n / 3) : ℝ) ^ 3 := by ring
    _ ≤ (n + 1 : ℝ) ^ 9 * (27 / 4 : ℝ) ^ n := by gcongr; exact choose_third_cube_le n
    _ < c ^ n * (27 / 4 : ℝ) ^ n := by gcongr
    _ = ((189 / 100 : ℝ) ^ n) ^ 3 := by
      rw [← mul_pow, show c * (27 / 4 : ℝ) = (189 / 100 : ℝ) ^ 3 by simp [c], ← pow_mul,
        mul_comm 3 n, pow_mul]

end Theorem1

/-! ### Section 3: Theorem 2 — Tight `(3 / 2) ^ n` Covering-Rank Upper Bound -/

section Theorem2

/-- Hypergeometric mode inequality via Vandermonde's identity: if `m₁ + m₂ = n` and `w` satisfies
the integer mode conditions for `i ↦ C(m₁, i) C(m₂, k - i)`, then
`C(n, k) ≤ (k + 1) C(m₁, w) C(m₂, k - w)`. -/
private theorem hypergeom_choose_le {n m₁ m₂ k w : ℕ} (hm : m₁ + m₂ = n) (hwk : w ≤ k)
    (hwm₁ : w ≤ m₁) (hkwm₂ : k - w ≤ m₂)
    (h_hi : (m₁ - w) * (k - w) ≤ (w + 1) * (m₂ - (k - w) + 1))
    (h_lo : w * (m₂ - (k - w)) ≤ (m₁ - w + 1) * (k - w + 1)) :
    n.choose k ≤ (k + 1) * (m₁.choose w * m₂.choose (k - w)) := by
  let g : ℕ → ℕ := fun i => m₁.choose i * m₂.choose (k - i)
  have hstep : ∀ i < k, i < m₁ → k - i - 1 < m₂ →
      g (i + 1) * ((i + 1) * (m₂ - (k - i - 1))) = g i * ((m₁ - i) * (k - i)) := by
    intro i hik him₁ _hkim₂
    have h1 := Nat.choose_succ_right_eq m₁ i
    have h2 := Nat.choose_succ_right_eq m₂ (k - i - 1)
    rw [show k - i - 1 + 1 = k - i by omega] at h2
    dsimp only [g]
    rw [show k - (i + 1) = k - i - 1 by omega]
    calc m₁.choose (i + 1) * m₂.choose (k - i - 1) * ((i + 1) * (m₂ - (k - i - 1)))
        = (m₁.choose (i + 1) * (i + 1)) * (m₂.choose (k - i - 1) * (m₂ - (k - i - 1))) := by ring
      _ = (m₁.choose i * (m₁ - i)) * (m₂.choose (k - i) * (k - i)) := by rw [h1, ← h2]
      _ = m₁.choose i * m₂.choose (k - i) * ((m₁ - i) * (k - i)) := by ring
  have hdown : ∀ i, w ≤ i → i < k → g (i + 1) ≤ g i := by
    intro i hwi hik
    rcases le_or_gt m₁ i with hm₁i | him₁
    · simp only [g, Nat.choose_eq_zero_of_lt (show m₁ < i + 1 by omega), zero_mul, Nat.zero_le]
    · have hkim₂ : k - i - 1 < m₂ := by omega
      have hpos : 0 < (i + 1) * (m₂ - (k - i - 1)) := Nat.mul_pos (by omega) (by omega)
      have hcmp : (m₁ - i) * (k - i) ≤ (i + 1) * (m₂ - (k - i - 1)) :=
        calc (m₁ - i) * (k - i)
            ≤ (m₁ - w) * (k - w) := Nat.mul_le_mul (by omega) (by omega)
          _ ≤ (w + 1) * (m₂ - (k - w) + 1) := h_hi
          _ ≤ (i + 1) * (m₂ - (k - i - 1)) := Nat.mul_le_mul (by omega) (by omega)
      have heq := hstep i hik him₁ hkim₂
      exact Nat.le_of_mul_le_mul_right (heq ▸ Nat.mul_le_mul_left (g i) hcmp) hpos
  have hup : ∀ i < w, g i ≤ g (i + 1) := by
    intro i hiw
    rcases lt_or_ge m₂ (k - i) with hm₂ki | hkim₂
    · simp only [g, Nat.choose_eq_zero_of_lt hm₂ki, mul_zero, Nat.zero_le]
    · have hik : i < k := by omega
      have him₁ : i < m₁ := by omega
      have hpos : 0 < (m₁ - i) * (k - i) := Nat.mul_pos (by omega) (by omega)
      have hcmp : (i + 1) * (m₂ - (k - i - 1)) ≤ (m₁ - i) * (k - i) :=
        calc (i + 1) * (m₂ - (k - i - 1))
            ≤ w * (m₂ - (k - w)) := Nat.mul_le_mul (by omega) (by omega)
          _ ≤ (m₁ - w + 1) * (k - w + 1) := h_lo
          _ ≤ (m₁ - i) * (k - i) := Nat.mul_le_mul (by omega) (by omega)
      have heq := hstep i hik him₁ (by omega)
      exact Nat.le_of_mul_le_mul_right (heq ▸ Nat.mul_le_mul_left (g (i + 1)) hcmp) hpos
  have hle_mode : ∀ i ≤ k, g i ≤ g w := by
    intro i hik
    rcases le_total i w with hiw | hwi
    · exact monotoneOn_of_le_add_one Set.ordConnected_Iic (fun j _ _ hj => hup j hj)
        (Set.mem_Iic.2 hiw) (Set.mem_Iic.2 le_rfl) hiw
    · exact antitoneOn_of_add_one_le Set.ordConnected_Icc (fun j _ hj hj1 => hdown j hj.1 hj1.2)
        ⟨le_rfl, hwk⟩ ⟨hwi, hik⟩ hwi
  calc n.choose k
      = (m₁ + m₂).choose k := by rw [hm]
    _ = ∑ ij ∈ antidiagonal k, m₁.choose ij.1 * m₂.choose ij.2 := Nat.add_choose_eq m₁ m₂ k
    _ = ∑ i ∈ range (k + 1), g i := Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => m₁.choose i * m₂.choose j) k
    _ ≤ ∑ _i ∈ range (k + 1), g w :=
          sum_le_sum fun i hi => hle_mode i (Nat.lt_succ_iff.1 (mem_range.1 hi))
    _ = (k + 1) * (m₁.choose w * m₂.choose (k - w)) := by
          rw [sum_const, card_range, smul_eq_mul]

/-- Transitivity of `Equiv.Perm α` on disjoint subset pairs of matching cardinalities. -/
private theorem exists_perm_disjoint_pair {α : Type*} [Finite α]
    {a₁ b₁ a₂ b₂ : Finset α} (ha : a₁.card = a₂.card) (hb : b₁.card = b₂.card)
    (hd₁ : Disjoint a₁ b₁) (hd₂ : Disjoint a₂ b₂) :
    ∃ σ : Equiv.Perm α, a₁.map σ.toEmbedding = a₂ ∧ b₁.map σ.toEmbedding = b₂ := by
  classical
  let e : (a₁ ∪ b₁ : Finset α) ≃ (a₂ ∪ b₂ : Finset α) :=
    (Equiv.Finset.union a₁ b₁ hd₁).symm.trans <|
      ((Fintype.equivOfCardEq (by simpa using ha)).sumCongr
        (Fintype.equivOfCardEq (by simpa using hb))).trans (Equiv.Finset.union a₂ b₂ hd₂)
  have hσ : ∀ {s₁ s₂ : Finset α}, s₁.card = s₂.card → (∀ x ∈ s₁, e.extendSubtype x ∈ s₂) →
      s₁.map e.extendSubtype.toEmbedding = s₂ := fun hc h =>
    eq_of_subset_of_card_le (fun y hy => by obtain ⟨x, hx, rfl⟩ := mem_map.1 hy; exact h x hx)
      (by rw [card_map, hc])
  refine ⟨e.extendSubtype, hσ ha fun x hx => ?_, hσ hb fun x hx => ?_⟩
  · rw [e.extendSubtype_apply_of_mem x (mem_union_left _ hx)]
    simp [e, hx]
  · rw [e.extendSubtype_apply_of_mem x (mem_union_right _ hx)]
    simp [e, hx]

/-- Counting `(u, syn) : U × BitString k` where `syn` is uniquely pinned down when `good u`
holds. -/
private theorem card_filter_prod_unique_syn {ι : Type*} {U : Finset ι} {k : ℕ}
    (P : U × BitString k → Prop) [DecidablePred P] (good : ι → Prop) [DecidablePred good]
    (synOf : ι → BitString k)
    (hiff : ∀ (u : U) (syn : BitString k), P (u, syn) ↔ good u.val ∧ syn = synOf u.val) :
    (univ.filter P).card = (U.filter good).card := by
  refine card_bij (fun x _ => x.1.val) (fun x hx => ?_) (fun x hx y hy h => ?_) (fun u hu => ?_)
  · exact mem_filter.2 ⟨x.1.property, ((hiff x.1 x.2).1 (mem_filter.1 hx).2).1⟩
  · refine Prod.ext (Subtype.ext h) ?_
    rw [((hiff x.1 x.2).1 (mem_filter.1 hx).2).2, ((hiff y.1 y.2).1 (mem_filter.1 hy).2).2, h]
  · obtain ⟨huU, hg⟩ := mem_filter.1 hu
    exact ⟨(⟨u, huU⟩, synOf u), mem_filter.2 ⟨mem_univ _, (hiff _ _).2 ⟨hg, rfl⟩⟩, rfl⟩

/-- Disjoint subset pairs `(a, b)` of weights `(p, q)` (the `1`-entries of `U_n^{p, q}`). -/
private def disjointWeightPairs (α : Type*) [Fintype α] [DecidableEq α] (p q : ℕ) :
    Finset (Finset α × Finset α) :=
  ((univ : Finset α).powersetCard p ×ˢ (univ : Finset α).powersetCard q).filter
    fun ab => Disjoint ab.1 ab.2

private theorem mem_disjointWeightPairs {α : Type*} [Fintype α] [DecidableEq α]
    {p q : ℕ} {a b : Finset α} :
    (a, b) ∈ disjointWeightPairs α p q ↔ a.card = p ∧ b.card = q ∧ Disjoint a b := by
  simp only [disjointWeightPairs, mem_filter, mem_product, mem_powersetCard, subset_univ,
    true_and, and_assoc]

/-- Permutation symmetry of [Sergeev2026UniqueDisjointness, §3]: if a family `D` of
configurations and a predicate `good` are invariant under relabelling by permutations, then the
number of configurations that are `good` for a disjoint weight pair does not depend on the pair. -/
private theorem card_filter_eq_of_perm_invariant {α β : Type*} [Fintype α] [DecidableEq α]
    (D : Finset β) (act : Equiv.Perm α → β → β) (hD : ∀ σ, ∀ t ∈ D, act σ t ∈ D)
    (hact : ∀ σ t, act σ.symm (act σ t) = t) (good : β → Finset α → Finset α → Prop)
    [∀ t a b, Decidable (good t a b)]
    (hgood : ∀ σ t a b, good (act σ t) (a.map σ.toEmbedding) (b.map σ.toEmbedding) ↔ good t a b)
    {p q : ℕ} {a₁ b₁ a₂ b₂ : Finset α}
    (hw₁ : (a₁, b₁) ∈ disjointWeightPairs α p q) (hw₂ : (a₂, b₂) ∈ disjointWeightPairs α p q) :
    (D.filter fun t => good t a₁ b₁).card = (D.filter fun t => good t a₂ b₂).card := by
  obtain ⟨ha₁, hb₁, hd₁⟩ := mem_disjointWeightPairs.1 hw₁
  obtain ⟨ha₂, hb₂, hd₂⟩ := mem_disjointWeightPairs.1 hw₂
  obtain ⟨σ, rfl, rfl⟩ :=
    exists_perm_disjoint_pair (ha₁.trans ha₂.symm) (hb₁.trans hb₂.symm) hd₁ hd₂
  have hinv : ∀ t, act σ (act σ.symm t) = t := fun t => by simpa using hact σ.symm t
  let e : Equiv.Perm β := ⟨act σ, act σ.symm, hact σ, hinv⟩
  refine card_equiv e fun t => ?_
  simp only [mem_filter]
  refine and_congr ⟨hD σ t, fun h => ?_⟩ (hgood σ t a₁ b₁).symm
  simpa only [hact] using hD σ.symm (act σ t) h

private theorem card_disjointWeightPairs {α : Type*} [Fintype α] [DecidableEq α] (p q : ℕ) :
    (disjointWeightPairs α p q).card =
      (Fintype.card α).choose p * (Fintype.card α - p).choose q := by
  let dom := ((univ : Finset α).powersetCard p).sigma fun a => (univ \ a).powersetCard q
  have hcard : dom.card = (Fintype.card α).choose p * (Fintype.card α - p).choose q := by
    rw [card_sigma]
    have hcongr : ∀ a ∈ (univ : Finset α).powersetCard p,
        ((univ \ a).powersetCard q).card = (Fintype.card α - p).choose q := by
      intro a ha
      rw [card_powersetCard, card_sdiff_of_subset (subset_univ a), card_univ,
        (mem_powersetCard.1 ha).2]
    rw [sum_congr rfl hcongr, sum_const, card_powersetCard, card_univ, smul_eq_mul]
  rw [← hcard]
  refine (card_bij (fun x _ => (x.1, x.2)) (fun x hx => ?_)
    (fun x₁ _ x₂ _ h => Sigma.ext (Prod.mk.inj h).1 (heq_of_eq (Prod.mk.inj h).2))
    (fun ⟨a, b⟩ hab => ?_)).symm
  · rw [mem_sigma, mem_powersetCard, mem_powersetCard] at hx
    exact mem_disjointWeightPairs.2 ⟨hx.1.2, hx.2.2, disjoint_sdiff_self_right.mono_right hx.2.1⟩
  · obtain ⟨ha, hb, hd⟩ := mem_disjointWeightPairs.1 hab
    refine ⟨⟨a, b⟩, mem_sigma.2 ⟨mem_powersetCard.2 ⟨subset_univ a, ha⟩,
      mem_powersetCard.2 ⟨subset_sdiff.2 ⟨subset_univ b, hd.symm⟩, hb⟩⟩, rfl⟩

private theorem card_disjointWeightPairs_eq_choose_add {α : Type*} [Fintype α] [DecidableEq α]
    (p q : ℕ) :
    (disjointWeightPairs α p q).card =
      (Fintype.card α).choose (p + q) * (p + q).choose p := by
  rw [card_disjointWeightPairs p q]
  have h := Nat.choose_mul (n := Fintype.card α) (k := p + q) (s := p) (by omega)
  simpa only [Nat.add_sub_cancel_left] using h.symm

private theorem disjointWeightPairs_subset_disjointPairs {α : Type*} [Fintype α] [DecidableEq α]
    (p q : ℕ) : disjointWeightPairs α p q ⊆ disjointPairs (univ : Finset α) := by
  intro ⟨a, b⟩ hab
  exact mem_disjointPairs.2 ⟨subset_univ a, subset_univ b, (mem_disjointWeightPairs.1 hab).2.2⟩

private theorem one_add_log_card_disjointWeightPairs_le {α : Type*} [Fintype α] [DecidableEq α]
    (p q : ℕ) :
    1 + Real.log (disjointWeightPairs α p q).card ≤ 2 * (Fintype.card α + 1 : ℝ) := by
  rcases Nat.eq_zero_or_pos (disjointWeightPairs α p q).card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    linarith [(Nat.cast_nonneg (Fintype.card α) : (0 : ℝ) ≤ Fintype.card α)]
  · have hle3 : ((disjointWeightPairs α p q).card : ℝ) ≤ (3 : ℝ) ^ Fintype.card α := by
      have hsub := card_le_card (disjointWeightPairs_subset_disjointPairs (α := α) p q)
      rw [card_disjointPairs, card_univ] at hsub
      exact_mod_cast hsub
    have hlog3 : Real.log 3 ≤ 2 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hlog_le : Real.log (disjointWeightPairs α p q).card ≤ 2 * Fintype.card α := by
      calc Real.log (disjointWeightPairs α p q).card
          ≤ Real.log ((3 : ℝ) ^ Fintype.card α) :=
              Real.log_le_log (by exact_mod_cast hpos) hle3
        _ = Fintype.card α * Real.log 3 := Real.log_pow 3 (Fintype.card α)
        _ ≤ Fintype.card α * 2 :=
              mul_le_mul_of_nonneg_left hlog3 (Nat.cast_nonneg _)
        _ = 2 * Fintype.card α := by ring
    linarith

private theorem two_pow_half_le_three_div_two_pow (n : ℕ) :
    ((2 ^ (n / 2) : ℕ) : ℝ) ≤ (3 / 2 : ℝ) ^ n :=
  calc ((2 ^ (n / 2) : ℕ) : ℝ) = (2 : ℝ) ^ (n / 2) := by norm_num
    _ ≤ ((3 / 2 : ℝ) ^ 2) ^ (n / 2) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (3 / 2 : ℝ) ^ (2 * (n / 2)) := (pow_mul _ _ _).symm
    _ ≤ (3 / 2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (Nat.mul_div_le n 2)

private theorem two_mul_div_le_eight_mul_pow_five {n W S M : ℕ} (hM0 : 0 < M)
    (hW_le : W * S ≤ 2 * (n + 1) ^ 2 * 2 ^ (n / 2) * M) :
    2 * (n + 1 : ℝ) * W * S / M ≤ 8 * (n + 1 : ℝ) ^ 5 * (3 / 2 : ℝ) ^ n := by
  have h2 := two_pow_half_le_three_div_two_pow n
  have hW_real : (W : ℝ) * S ≤ 2 * (n + 1 : ℝ) ^ 2 * ((2 ^ (n / 2) : ℕ) : ℝ) * M := by
    exact_mod_cast hW_le
  have h1 : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [div_le_iff₀ (by exact_mod_cast hM0)]
  calc 2 * (n + 1 : ℝ) * W * S = 2 * (n + 1) * (W * S) := by ring
    _ ≤ 2 * (n + 1) * (2 * (n + 1 : ℝ) ^ 2 * ((2 ^ (n / 2) : ℕ) : ℝ) * M) := by gcongr
    _ = 4 * (n + 1) ^ 3 * ((2 ^ (n / 2) : ℕ) : ℝ) * M := by ring
    _ ≤ 8 * (n + 1) ^ 5 * (3 / 2 : ℝ) ^ n * M := by gcongr <;> norm_num

private theorem mul_le_sum_card_filter_of_card_filter_eq {S β γ : Type*} [Fintype S]
    (W : Finset β) (D : Finset γ) (hitS : S → β → Prop) (hitD : γ → β → Prop)
    [DecidableRel hitS] [DecidableRel hitD] {Cprod : ℕ}
    (hhit : ∀ w ∈ W, (univ.filter (hitS · w)).card = (D.filter (hitD · w)).card)
    (hper : ∀ d ∈ D, Cprod ≤ (W.filter (hitD d ·)).card) :
    D.card * Cprod ≤ ∑ s : S, (W.filter (hitS s ·)).card := by
  have hswap : ∑ s : S, (W.filter (hitS s ·)).card = ∑ d ∈ D, (W.filter (hitD d ·)).card := by
    calc ∑ s : S, (W.filter (hitS s ·)).card
        = ∑ w ∈ W, (univ.filter (hitS · w)).card := by simp_rw [card_filter]; exact sum_comm
      _ = ∑ w ∈ W, (D.filter (hitD · w)).card := sum_congr rfl fun w hw => hhit w hw
      _ = ∑ d ∈ D, (W.filter (hitD d ·)).card := by simp_rw [card_filter]; exact sum_comm
  rw [hswap]
  calc D.card * Cprod = ∑ _d ∈ D, Cprod := by rw [sum_const, smul_eq_mul]
    _ ≤ ∑ d ∈ D, (W.filter (hitD d ·)).card := sum_le_sum fun d hd => hper d hd

/-- Shared bridge from Lovász–Stein on `disjointWeightPairs α p q` to `coverNumber` on
`(weightSlice α p, weightSlice α q)`. -/
private theorem exists_coverNumber_weightSlice_le_of_const_hit {α S : Type*} [Fintype α]
    [DecidableEq α] [Fintype S] [Nonempty S] {p q : ℕ} (hpq : p + q ≤ Fintype.card α)
    (row col : S → Finset (Finset α))
    (hmono : ∀ s, ∀ a ∈ row s, ∀ b ∈ col s, (a ∩ b).card ≠ 1)
    (hconst : ∀ w₁ ∈ disjointWeightPairs α p q, ∀ w₂ ∈ disjointWeightPairs α p q,
      (univ.filter fun s : S => w₁.1 ∈ row s ∧ w₁.2 ∈ col s).card =
        (univ.filter fun s : S => w₂.1 ∈ row s ∧ w₂.2 ∈ col s).card)
    {M : ℕ} (hM0 : 0 < M)
    (hM : M ≤ ∑ s : S, ((disjointWeightPairs α p q).filter
      fun w => w.1 ∈ row s ∧ w.2 ∈ col s).card) :
    ∃ r : ℕ,
      coverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) ≤ r ∧
        (r : ℝ) ≤
          2 * (Fintype.card α + 1 : ℝ) * (disjointWeightPairs α p q).card * Fintype.card S / M := by
  let W := disjointWeightPairs α p q
  have hWpos : 0 < W.card := by
    rw [card_disjointWeightPairs p q]
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hWne : W.Nonempty := card_pos.1 hWpos
  let hit : S → Finset α × Finset α → Prop := fun s w => w.1 ∈ row s ∧ w.2 ∈ col s
  have hMreal : (M : ℝ) ≤ ∑ s : S, ((W.filter (hit s ·)).card : ℝ) := by exact_mod_cast hM
  obtain ⟨G, hGcov, hGcard⟩ := Cslib.exists_cover_card_le_of_const_hit hWne hit hconst
    (by exact_mod_cast hM0) hMreal
  have hisCov : IsCover true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q)
      (fun s : G => ((row s.val : Set (Finset α)), (col s.val : Set (Finset α)))) := by
    refine ⟨fun s a _ ha b _ hb => ?_, fun a ha b hb hnd => ?_⟩
    · simp only [uniqueDisjointnessRel, ↓reduceIte]
      exact hmono s.val a ha b hb
    · simp only [Bool.not_true, uniqueDisjointnessRel, Bool.false_eq_true, ↓reduceIte,
        not_not] at hnd
      obtain ⟨s, hsG, hhit⟩ := hGcov (a, b) (mem_disjointWeightPairs.2 ⟨ha, hb, hnd⟩)
      exact ⟨⟨s, hsG⟩, hhit.1, hhit.2⟩
  refine ⟨G.card, hisCov.coverNumber_le.trans_eq (by rw [Fintype.card_coe]), ?_⟩
  refine hGcard.trans ?_
  have hlog := one_add_log_card_disjointWeightPairs_le (α := α) p q
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))
    (Nat.cast_nonneg M)

/-! #### Case III of [Sergeev2026UniqueDisjointness]: `2 * (p + q) ≤ n` -/

private theorem exists_coverNumber_weightSlice_case3 {α : Type*} [Fintype α] [DecidableEq α]
    {p q : ℕ} (hs_pos : 1 ≤ p + q) (h2s : 2 * (p + q) ≤ Fintype.card α) :
    ∃ r : ℕ,
      coverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) ≤ r ∧
        (r : ℝ) ≤ 8 * (Fintype.card α + 1 : ℝ) ^ 5 * (3 / 2 : ℝ) ^ Fintype.card α := by
  set n := Fintype.card α
  set s := p + q
  set m₁ : ℕ := (n * p) / s
  set m₂ : ℕ := n - m₁
  have hpm₁ : p ≤ m₁ := (Nat.le_div_iff_mul_le hs_pos).2 (by nlinarith)
  have hm₁n : m₁ ≤ n := Nat.div_le_of_le_mul (by
    rw [mul_comm s n]
    exact Nat.mul_le_mul_left n (Nat.le_add_right p q))
  have hsm₁ : m₁ * s ≤ n * p := Nat.div_mul_le_self (n * p) s
  have hsm₁_gt : n * p < (m₁ + 1) * s := by
    rw [mul_comm (m₁ + 1) s]
    exact Nat.lt_mul_div_succ (n * p) hs_pos
  have h2pm₁ : 2 * p ≤ m₁ := (Nat.le_div_iff_mul_le hs_pos).2 (by nlinarith)
  have hm : m₁ + m₂ = n := Nat.add_sub_cancel' hm₁n
  have hqm₂ : q ≤ m₂ := by
    have hsq : s * q ≤ s * m₂ := by
      have hspq : s = p + q := rfl
      nlinarith
    exact Nat.le_of_mul_le_mul_left hsq hs_pos
  let S := (univ : Finset α).powersetCard m₁
  let _ : Nonempty S :=
    (powersetCard_nonempty.2 (by rw [card_univ]; exact hm₁n)).coe_sort
  let row (X₁ : S) : Finset (Finset α) := X₁.val.powersetCard p
  let col (X₁ : S) : Finset (Finset α) := (univ \ X₁.val).powersetCard q
  have hmono : ∀ X₁ : S, ∀ a ∈ row X₁, ∀ b ∈ col X₁, (a ∩ b).card ≠ 1 := by
    intro X₁ a ha b hb
    have hd : Disjoint a b :=
      disjoint_sdiff_self_right.mono (mem_powersetCard.1 ha).1 (mem_powersetCard.1 hb).1
    rw [disjoint_iff_inter_eq_empty.1 hd, card_empty]
    decide
  have hconst : ∀ w₁ ∈ disjointWeightPairs α p q, ∀ w₂ ∈ disjointWeightPairs α p q,
      (univ.filter fun X₁ : S => w₁.1 ∈ row X₁ ∧ w₁.2 ∈ col X₁).card =
        (univ.filter fun X₁ : S => w₂.1 ∈ row X₁ ∧ w₂.2 ∈ col X₁).card := by
    intro ⟨a₁, b₁⟩ hw₁ ⟨a₂, b₂⟩ hw₂
    refine card_filter_eq_of_perm_invariant (univ : Finset S)
      (fun σ X₁ => ⟨X₁.val.map σ.toEmbedding,
        mem_powersetCard.2 ⟨subset_univ _, by rw [card_map, (mem_powersetCard.1 X₁.property).2]⟩⟩)
      (fun _ _ _ => mem_univ _) (fun σ X₁ => Subtype.ext (by simp [map_map]))
      (fun X₁ a b => a ∈ row X₁ ∧ b ∈ col X₁) (fun σ X₁ a b => ?_) hw₁ hw₂
    simp only [row, col, mem_powersetCard, map_subset_map, card_map, subset_sdiff, subset_univ,
      true_and, disjoint_map]
  let M : ℕ := n.choose m₁ * (m₁.choose p * m₂.choose q)
  have hM0 : 0 < M :=
    Nat.mul_pos (Nat.choose_pos hm₁n) (Nat.mul_pos (Nat.choose_pos hpm₁) (Nat.choose_pos hqm₂))
  have hM : M ≤ ∑ X₁ : S,
      ((disjointWeightPairs α p q).filter fun w => w.1 ∈ row X₁ ∧ w.2 ∈ col X₁).card := by
    have hper : ∀ X₁ : S, m₁.choose p * m₂.choose q ≤
        ((disjointWeightPairs α p q).filter fun w => w.1 ∈ row X₁ ∧ w.2 ∈ col X₁).card := by
      intro X₁
      have hX₁c : X₁.val.card = m₁ := (mem_powersetCard.1 X₁.property).2
      have hX₂c : (univ \ X₁.val).card = m₂ := by
        rw [card_sdiff_of_subset (subset_univ _), card_univ, hX₁c]
      have hprod : (row X₁ ×ˢ col X₁).card = m₁.choose p * m₂.choose q := by
        rw [card_product, card_powersetCard, card_powersetCard, hX₁c, hX₂c]
      rw [← hprod]
      refine card_le_card fun ⟨a, b⟩ hab => ?_
      rw [mem_product] at hab
      have hd : Disjoint a b :=
        disjoint_sdiff_self_right.mono (mem_powersetCard.1 hab.1).1 (mem_powersetCard.1 hab.2).1
      exact mem_filter.2 ⟨mem_disjointWeightPairs.2
        ⟨(mem_powersetCard.1 hab.1).2, (mem_powersetCard.1 hab.2).2, hd⟩, hab.1, hab.2⟩
    have hS_card : Fintype.card S = n.choose m₁ := by
      simp only [S, Fintype.card_coe, card_powersetCard, card_univ]
      rfl
    calc M = ∑ _X₁ : S, m₁.choose p * m₂.choose q := by
            rw [sum_const, card_univ, hS_card, smul_eq_mul]
      _ ≤ ∑ X₁ : S, _ := sum_le_sum fun X₁ _ => hper X₁
  obtain ⟨r, hcov, hr_le⟩ :=
    exists_coverNumber_weightSlice_le_of_const_hit (by omega) row col hmono hconst hM0 hM
  refine ⟨r, hcov, hr_le.trans ?_⟩
  have hhyp : n.choose s ≤ (s + 1) * (m₁.choose p * m₂.choose q) := by
    have hks : s - p = q := by omega
    have hspq : s = p + q := rfl
    rw [← hks]
    refine hypergeom_choose_le hm (by omega) hpm₁ (by rw [hks]; exact hqm₂) ?_ ?_
    · rw [hks]
      zify [hpm₁, hqm₂] at hsm₁ hm hspq ⊢
      nlinarith
    · rw [hks]
      zify [hpm₁, hqm₂] at hsm₁_gt h2pm₁ hm hspq ⊢
      nlinarith
  have hS_card : Fintype.card S = n.choose m₁ := by
    simp only [S, Fintype.card_coe, card_powersetCard, card_univ]
    rfl
  have hW_le : (disjointWeightPairs α p q).card * Fintype.card S ≤
      2 * (n + 1) ^ 2 * 2 ^ (n / 2) * M := by
    rw [card_disjointWeightPairs_eq_choose_add p q, hS_card]
    have hsp : s.choose p ≤ 2 ^ (n / 2) :=
      (Nat.choose_le_two_pow s p).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hs1 : s + 1 ≤ 2 * (n + 1) ^ 2 := by nlinarith
    calc n.choose s * s.choose p * n.choose m₁
        ≤ ((s + 1) * (m₁.choose p * m₂.choose q)) * 2 ^ (n / 2) * n.choose m₁ :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul hhyp hsp)
      _ ≤ (2 * (n + 1) ^ 2 * (m₁.choose p * m₂.choose q)) * 2 ^ (n / 2) * n.choose m₁ :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
              (Nat.mul_le_mul_right _ hs1))
      _ = 2 * (n + 1) ^ 2 * 2 ^ (n / 2) * M := by ring
  exact two_mul_div_le_eight_mul_pow_five hM0 hW_le

/-! #### Case II of [Sergeev2026UniqueDisjointness]: `n < 2 * (p + q)` and `2 * p ≤ n` -/

private theorem exists_coverNumber_weightSlice_case2 {α : Type*} [Fintype α] [DecidableEq α]
    {p q : ℕ} (hqp : q ≤ p) (hgt : Fintype.card α < 2 * (p + q))
    (h2p : 2 * p ≤ Fintype.card α) :
    ∃ r : ℕ,
      coverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) ≤ r ∧
        (r : ℝ) ≤ 8 * (Fintype.card α + 1 : ℝ) ^ 5 * (3 / 2 : ℝ) ^ Fintype.card α := by
  set n := Fintype.card α
  set x₀ : ℕ := p + q - n / 2
  have hx₀_pos : 1 ≤ x₀ := by omega
  have hx₀_q : x₀ ≤ q := by omega
  have hx₀_p : x₀ ≤ p := hx₀_q.trans hqp
  set m₁ : ℕ := p - x₀
  set m₂ : ℕ := q - x₀
  have hsum_half : x₀ + m₁ + m₂ = n / 2 := by omega
  have h2sum_le : 2 * x₀ + 2 * m₁ + 2 * m₂ ≤ n := by omega
  set k : ℕ := Nat.clog 2 (2 * x₀ + 1)
  let T : Finset (Finset α × Finset α × Finset α) :=
    ((univ : Finset α).powersetCard (2 * x₀) ×ˢ
      ((univ : Finset α).powersetCard (2 * m₁) ×ˢ
        (univ : Finset α).powersetCard (2 * m₂))).filter
      fun t => Disjoint t.1 t.2.1 ∧ Disjoint t.1 t.2.2 ∧ Disjoint t.2.1 t.2.2
  have hTne : T.Nonempty := by
    obtain ⟨X₀, hX₀⟩ := (powersetCard_nonempty (n := 2 * x₀) (s := (univ : Finset α))).2
      (by rw [card_univ]; omega)
    have hX₀c : X₀.card = 2 * x₀ := (mem_powersetCard.1 hX₀).2
    obtain ⟨X₁, hX₁⟩ := (powersetCard_nonempty (n := 2 * m₁) (s := univ \ X₀)).2
      (by rw [card_sdiff_of_subset (subset_univ _), card_univ, hX₀c]; omega)
    have hX₁c : X₁.card = 2 * m₁ := (mem_powersetCard.1 hX₁).2
    have hd01 : Disjoint X₀ X₁ := disjoint_sdiff_self_right.mono_right (mem_powersetCard.1 hX₁).1
    obtain ⟨X₂, hX₂⟩ := (powersetCard_nonempty (n := 2 * m₂) (s := univ \ (X₀ ∪ X₁))).2
      (by rw [card_sdiff_of_subset (subset_univ _), card_univ,
        card_union_of_disjoint hd01, hX₀c, hX₁c]; omega)
    have hX₂_sub := (mem_powersetCard.1 hX₂).1
    have hd02 : Disjoint X₀ X₂ := disjoint_sdiff_self_right.mono subset_union_left hX₂_sub
    have hd12 : Disjoint X₁ X₂ := disjoint_sdiff_self_right.mono subset_union_right hX₂_sub
    exact ⟨(X₀, X₁, X₂), mem_filter.2 ⟨mem_product.2 ⟨hX₀, mem_product.2
      ⟨mem_powersetCard.2 ⟨subset_univ _, hX₁c⟩,
        mem_powersetCard.2 ⟨subset_univ _, (mem_powersetCard.1 hX₂).2⟩⟩⟩,
      hd01, hd02, hd12⟩⟩
  let S := T × BitString k
  let _ : Nonempty S := ⟨(⟨hTne.choose, hTne.choose_spec⟩, 0)⟩
  let codeFib (X₀ : Finset α) (syn : BitString k) : Finset (Finset α) :=
    (X₀.powersetCard x₀).filter fun a₀ => synPad k X₀ a₀ = syn
  let row (s : S) : Finset (Finset α) :=
    (codeFib s.1.val.1 s.2).biUnion fun a₀ => (s.1.val.2.1.powersetCard m₁).image (a₀ ∪ ·)
  let col (s : S) : Finset (Finset α) :=
    (codeFib s.1.val.1 s.2).biUnion fun b₀' =>
      (s.1.val.2.2.powersetCard m₂).image ((s.1.val.1 \ b₀') ∪ ·)
  have hmono : ∀ s : S, ∀ a ∈ row s, ∀ b ∈ col s, (a ∩ b).card ≠ 1 := by
    rintro ⟨⟨⟨X₀, X₁, X₂⟩, ht⟩, syn⟩ a ha b hb
    obtain ⟨hmem_prod, hd01, hd02, hd12⟩ := mem_filter.1 ht
    have hX₀c : X₀.card = 2 * x₀ := (mem_powersetCard.1 (mem_product.1 hmem_prod).1).2
    obtain ⟨a₀, ha₀, ha₁_im⟩ := mem_biUnion.1 ha
    obtain ⟨a₁, ha₁, rfl⟩ := mem_image.1 ha₁_im
    obtain ⟨b₀', hb₀', hb₂_im⟩ := mem_biUnion.1 hb
    obtain ⟨b₂, hb₂, rfl⟩ := mem_image.1 hb₂_im
    have ha₀_f := mem_filter.1 ha₀
    have hb₀'_f := mem_filter.1 hb₀'
    have ha₀_sub : a₀ ⊆ X₀ := (mem_powersetCard.1 ha₀_f.1).1
    have hb₀'_sub : b₀' ⊆ X₀ := (mem_powersetCard.1 hb₀'_f.1).1
    have ha₁_sub : a₁ ⊆ X₁ := (mem_powersetCard.1 ha₁).1
    have hb₂_sub : b₂ ⊆ X₂ := (mem_powersetCard.1 hb₂).1
    have hinter : (a₀ ∪ a₁) ∩ (X₀ \ b₀' ∪ b₂) = a₀ ∩ (X₀ \ b₀') := by
      ext x
      simp only [mem_inter, mem_union, mem_sdiff]
      refine ⟨fun ⟨hx1, hx2⟩ => ?_, fun ⟨hxa₀, hxX₀, hxnb⟩ => ⟨Or.inl hxa₀, Or.inl ⟨hxX₀, hxnb⟩⟩⟩
      rcases hx1 with hxa₀ | hxa₁
      · rcases hx2 with ⟨hxX₀, hxnb⟩ | hxb₂
        · exact ⟨hxa₀, hxX₀, hxnb⟩
        · exact absurd (hb₂_sub hxb₂) (Finset.disjoint_left.1 hd02 (ha₀_sub hxa₀))
      · rcases hx2 with ⟨hxX₀, _⟩ | hxb₂
        · exact absurd hxX₀ (Finset.disjoint_right.1 hd01 (ha₁_sub hxa₁))
        · exact absurd (hb₂_sub hxb₂) (Finset.disjoint_left.1 hd12 (ha₁_sub hxa₁))
    rw [hinter]
    exact card_inter_sdiff_ne_one_of_synPad_eq (by rw [hX₀c]) ha₀_sub hb₀'_sub
      ((mem_powersetCard.1 ha₀_f.1).2.trans (mem_powersetCard.1 hb₀'_f.1).2.symm)
      (ha₀_f.2.trans hb₀'_f.2.symm)
  let goodB (X₀ X₁ X₂ a b : Finset α) : Prop :=
    (a ∩ X₀).card = x₀ ∧ a ⊆ X₀ ∪ X₁ ∧ X₀ \ (a ∩ X₀) ⊆ b ∧ b ⊆ X₀ ∪ X₂
  have hhit_iff : ∀ (t : T) (syn : BitString k) (a b : Finset α),
      (a, b) ∈ disjointWeightPairs α p q →
      ((a ∈ row (t, syn) ∧ b ∈ col (t, syn)) ↔
        goodB t.val.1 t.val.2.1 t.val.2.2 a b ∧ syn = synPad k t.val.1 (a ∩ t.val.1)) := by
    rintro ⟨⟨X₀, X₁, X₂⟩, ht⟩ syn a b hab
    dsimp only [row, col, goodB]
    obtain ⟨hmem_prod, hd01, hd02, hd12⟩ := mem_filter.1 ht
    have hX₀c : X₀.card = 2 * x₀ := (mem_powersetCard.1 (mem_product.1 hmem_prod).1).2
    obtain ⟨ha_card, hb_card, hdab⟩ := mem_disjointWeightPairs.1 hab
    refine ⟨fun ⟨har, hbc⟩ => ?_, fun ⟨⟨hax₀, ha_sub, hbX₀, hb_sub⟩, hsyn⟩ => ?_⟩
    · obtain ⟨a₀, ha₀, ha₁_im⟩ := mem_biUnion.1 har
      obtain ⟨a₁, ha₁, rfl⟩ := mem_image.1 ha₁_im
      obtain ⟨b₀', hb₀', hb₂_im⟩ := mem_biUnion.1 hbc
      obtain ⟨b₂, hb₂, rfl⟩ := mem_image.1 hb₂_im
      have ha₀_sub : a₀ ⊆ X₀ := (mem_powersetCard.1 (mem_filter.1 ha₀).1).1
      have ha₁_sub : a₁ ⊆ X₁ := (mem_powersetCard.1 ha₁).1
      have hb₀'_sub : b₀' ⊆ X₀ := (mem_powersetCard.1 (mem_filter.1 hb₀').1).1
      have hb₂_sub : b₂ ⊆ X₂ := (mem_powersetCard.1 hb₂).1
      have ha_inter : (a₀ ∪ a₁) ∩ X₀ = a₀ := by
        ext x
        simp only [mem_inter, mem_union]
        exact ⟨fun ⟨h1, h2⟩ => h1.resolve_right
          (fun hx1 => Finset.disjoint_right.1 hd01 (ha₁_sub hx1) h2),
          fun hx => ⟨Or.inl hx, ha₀_sub hx⟩⟩
      have hb₀'_card : (X₀ \ b₀').card = x₀ := by
        rw [card_sdiff_of_subset hb₀'_sub, hX₀c, (mem_powersetCard.1 (mem_filter.1 hb₀').1).2]
        omega
      have ha₀_card : a₀.card = x₀ := (mem_powersetCard.1 (mem_filter.1 ha₀).1).2
      have hdisj_a₀_sdiff : Disjoint a₀ (X₀ \ b₀') :=
        hdab.mono subset_union_left subset_union_left
      have hsdiff_eq : X₀ \ a₀ = X₀ \ b₀' := by
        refine (eq_of_subset_of_card_le (subset_sdiff.2 ⟨sdiff_subset, hdisj_a₀_sdiff.symm⟩)
          ?_).symm
        rw [card_sdiff_of_subset ha₀_sub, hX₀c, ha₀_card, hb₀'_card]
        omega
      rw [ha_inter]
      refine ⟨⟨ha₀_card, union_subset_union ha₀_sub ha₁_sub, ?_,
        union_subset_union sdiff_subset hb₂_sub⟩, (mem_filter.1 ha₀).2.symm⟩
      rw [hsdiff_eq]
      exact subset_union_left
    · subst hsyn
      let a₀ := a ∩ X₀
      let a₁ := a \ X₀
      have ha₀_mem : a₀ ∈ codeFib X₀ (synPad k X₀ a₀) :=
        mem_filter.2 ⟨mem_powersetCard.2 ⟨inter_subset_right, hax₀⟩, rfl⟩
      have ha₁_sub : a₁ ⊆ X₁ := fun x hx =>
        (mem_union.1 (ha_sub (mem_sdiff.1 hx).1)).resolve_left (mem_sdiff.1 hx).2
      have ha₁_card : a₁.card = m₁ := by
        have h1 := card_sdiff_add_card_inter a X₀
        change a₁.card + (a ∩ X₀).card = a.card at h1
        rw [hax₀, ha_card] at h1
        omega
      have ha_mem : a ∈ (codeFib X₀ (synPad k X₀ a₀)).biUnion
          (fun u => (X₁.powersetCard m₁).image (u ∪ ·)) := by
        refine mem_biUnion.2 ⟨a₀, ha₀_mem, mem_image.2 ⟨a₁,
          mem_powersetCard.2 ⟨ha₁_sub, ha₁_card⟩, ?_⟩⟩
        exact union_comm a₀ a₁ ▸ sdiff_union_inter a X₀
      have hb_inter : b ∩ X₀ = X₀ \ a₀ := by
        refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
        · rw [mem_inter] at hx
          exact mem_sdiff.2 ⟨hx.2, fun hxa₀ =>
            Finset.disjoint_left.1 hdab (mem_inter.1 hxa₀).1 hx.1⟩
        · exact card_le_card (subset_inter hbX₀ sdiff_subset)
      let b₂ := b \ X₀
      have hb₂_sub : b₂ ⊆ X₂ := fun x hx =>
        (mem_union.1 (hb_sub (mem_sdiff.1 hx).1)).resolve_left (mem_sdiff.1 hx).2
      have hb₂_card : b₂.card = m₂ := by
        have h1 := card_sdiff_add_card_inter b X₀
        have h2 : (X₀ \ a₀).card = x₀ := by
          rw [card_sdiff_of_subset inter_subset_right, hX₀c, hax₀]
          omega
        change b₂.card + (b ∩ X₀).card = b.card at h1
        rw [hb_inter, h2] at h1
        omega
      have hb_mem : b ∈ (codeFib X₀ (synPad k X₀ a₀)).biUnion
          (fun v => (X₂.powersetCard m₂).image ((X₀ \ v) ∪ ·)) := by
        refine mem_biUnion.2 ⟨a₀, ha₀_mem, mem_image.2 ⟨b₂,
          mem_powersetCard.2 ⟨hb₂_sub, hb₂_card⟩, ?_⟩⟩
        rw [← hb_inter, union_comm]
        exact sdiff_union_inter b X₀
      exact ⟨ha_mem, hb_mem⟩
  have hhit_card : ∀ w ∈ disjointWeightPairs α p q,
      (univ.filter fun s : S => w.1 ∈ row s ∧ w.2 ∈ col s).card =
        (T.filter fun t => goodB t.1 t.2.1 t.2.2 w.1 w.2).card := by
    rintro ⟨a, b⟩ hw
    exact card_filter_prod_unique_syn (fun s : S => a ∈ row s ∧ b ∈ col s)
      (fun t => goodB t.1 t.2.1 t.2.2 a b) (fun t => synPad k t.1 (a ∩ t.1))
      fun t syn => hhit_iff t syn a b hw
  have hconst : ∀ w₁ ∈ disjointWeightPairs α p q, ∀ w₂ ∈ disjointWeightPairs α p q,
      (univ.filter fun s : S => w₁.1 ∈ row s ∧ w₁.2 ∈ col s).card =
        (univ.filter fun s : S => w₂.1 ∈ row s ∧ w₂.2 ∈ col s).card := by
    intro ⟨a₁, b₁⟩ hw₁ ⟨a₂, b₂⟩ hw₂
    rw [hhit_card (a₁, b₁) hw₁, hhit_card (a₂, b₂) hw₂]
    refine card_filter_eq_of_perm_invariant T
      (fun σ t => (t.1.map σ.toEmbedding, t.2.1.map σ.toEmbedding, t.2.2.map σ.toEmbedding))
      (fun σ t ht => ?_) (fun σ t => by simp [map_map]) (fun t a b => goodB t.1 t.2.1 t.2.2 a b)
      (fun σ t a b => by
        simp only [goodB, ← map_inter, ← map_union, ← map_sdiff, card_map, map_subset_map])
      hw₁ hw₂
    simpa only [T, mem_filter, mem_product, mem_powersetCard, subset_univ, true_and, card_map,
      disjoint_map] using ht
  let Cprod : ℕ := (2 * x₀).choose x₀ * (2 * m₁).choose m₁ * (2 * m₂).choose m₂
  let M : ℕ := T.card * Cprod
  have hCprod_pos : 0 < Cprod :=
    Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
      (Nat.choose_pos (by omega))
  have hM0 : 0 < M := Nat.mul_pos hTne.card_pos hCprod_pos
  have hM : M ≤ ∑ s : S,
      ((disjointWeightPairs α p q).filter fun w => w.1 ∈ row s ∧ w.2 ∈ col s).card := by
    classical
    let W := disjointWeightPairs α p q
    refine mul_le_sum_card_filter_of_card_filter_eq W T
      (fun s w => w.1 ∈ row s ∧ w.2 ∈ col s) (fun t w => goodB t.1 t.2.1 t.2.2 w.1 w.2)
      hhit_card ?_
    rintro ⟨X₀, X₁, X₂⟩ ht
    obtain ⟨hp_mem, hd01, hd02, hd12⟩ := mem_filter.1 ht
    obtain ⟨h0, h12⟩ := mem_product.1 hp_mem
    obtain ⟨h1, h2⟩ := mem_product.1 h12
    have hX₀c : X₀.card = 2 * x₀ := (mem_powersetCard.1 h0).2
    have hX₁c : X₁.card = 2 * m₁ := (mem_powersetCard.1 h1).2
    have hX₂c : X₂.card = 2 * m₂ := (mem_powersetCard.1 h2).2
    let src := X₀.powersetCard x₀ ×ˢ (X₁.powersetCard m₁ ×ˢ X₂.powersetCard m₂)
    have hsrc_card : src.card = Cprod := by
      rw [card_product, card_product, card_powersetCard, card_powersetCard, card_powersetCard,
        hX₀c, hX₁c, hX₂c]
      dsimp only [Cprod]
      ring
    rw [← hsrc_card]
    refine card_le_card_of_injOn (fun u => (u.1 ∪ u.2.1, (X₀ \ u.1) ∪ u.2.2))
      (fun ⟨a₀, a₁, b₂⟩ hu => ?_) (fun ⟨a₀, a₁, b₂⟩ hu ⟨a₀', a₁', b₂'⟩ hu' heq => ?_)
    · rw [mem_coe, mem_product] at hu
      obtain ⟨ha₀, ha₁b₂⟩ := hu
      obtain ⟨ha₁, hb₂⟩ := mem_product.1 ha₁b₂
      have ha₀s : a₀ ⊆ X₀ := (mem_powersetCard.1 ha₀).1
      have ha₁s : a₁ ⊆ X₁ := (mem_powersetCard.1 ha₁).1
      have hb₂s : b₂ ⊆ X₂ := (mem_powersetCard.1 hb₂).1
      have hd_a : Disjoint a₀ a₁ := hd01.mono ha₀s ha₁s
      have hd_b : Disjoint (X₀ \ a₀) b₂ := hd02.mono sdiff_subset hb₂s
      have ha_c : (a₀ ∪ a₁).card = p := by
        rw [card_union_of_disjoint hd_a, (mem_powersetCard.1 ha₀).2, (mem_powersetCard.1 ha₁).2]
        omega
      have hb_c : ((X₀ \ a₀) ∪ b₂).card = q := by
        rw [card_union_of_disjoint hd_b, card_sdiff_of_subset ha₀s, hX₀c,
          (mem_powersetCard.1 ha₀).2, (mem_powersetCard.1 hb₂).2]
        omega
      have hd_ab : Disjoint (a₀ ∪ a₁) ((X₀ \ a₀) ∪ b₂) :=
        disjoint_union_left.2
          ⟨disjoint_union_right.2 ⟨disjoint_sdiff_self_right, hd02.mono ha₀s hb₂s⟩,
           disjoint_union_right.2 ⟨(hd01.mono sdiff_subset ha₁s).symm, hd12.mono ha₁s hb₂s⟩⟩
      have hw_mem : (a₀ ∪ a₁, (X₀ \ a₀) ∪ b₂) ∈ W :=
        mem_disjointWeightPairs.2 ⟨ha_c, hb_c, hd_ab⟩
      have hg : goodB X₀ X₁ X₂ (a₀ ∪ a₁) ((X₀ \ a₀) ∪ b₂) := by
        have hex :=
          (hhit_iff ⟨(X₀, X₁, X₂), ht⟩ (synPad k X₀ a₀) (a₀ ∪ a₁) ((X₀ \ a₀) ∪ b₂) hw_mem).1
        refine (hex ⟨?_, ?_⟩).1
        · exact mem_biUnion.2 ⟨a₀, mem_filter.2 ⟨ha₀, rfl⟩,
            mem_image.2 ⟨a₁, ha₁, rfl⟩⟩
        · exact mem_biUnion.2 ⟨a₀, mem_filter.2 ⟨ha₀, rfl⟩,
            mem_image.2 ⟨b₂, hb₂, rfl⟩⟩
      exact mem_coe.2 (mem_filter.2 ⟨hw_mem, hg⟩)
    · rw [mem_coe, mem_product] at hu hu'
      have ha₀s := (mem_powersetCard.1 hu.1).1
      have ha₁s := (mem_powersetCard.1 (mem_product.1 hu.2).1).1
      have hb₂s := (mem_powersetCard.1 (mem_product.1 hu.2).2).1
      have ha₀'s := (mem_powersetCard.1 hu'.1).1
      have ha₁'s := (mem_powersetCard.1 (mem_product.1 hu'.2).1).1
      have hb₂'s := (mem_powersetCard.1 (mem_product.1 hu'.2).2).1
      obtain ⟨heq1, heq2⟩ := Prod.mk.inj heq
      have hinter0 : ∀ u₀ u₁, u₀ ⊆ X₀ → u₁ ⊆ X₁ → (u₀ ∪ u₁) ∩ X₀ = u₀ := by
        intro u₀ u₁ hu₀ hu₁
        ext x
        simp only [mem_inter, mem_union]
        exact ⟨fun ⟨h1, h2⟩ => h1.resolve_right
          (fun hx1 => Finset.disjoint_right.1 hd01 (hu₁ hx1) h2),
          fun hx => ⟨Or.inl hx, hu₀ hx⟩⟩
      have hinter1 : ∀ u₀ u₁, u₀ ⊆ X₀ → u₁ ⊆ X₁ → (u₀ ∪ u₁) ∩ X₁ = u₁ := by
        intro u₀ u₁ hu₀ hu₁
        ext x
        simp only [mem_inter, mem_union]
        exact ⟨fun ⟨h1, h2⟩ => h1.resolve_left
          (fun hx0 => Finset.disjoint_left.1 hd01 (hu₀ hx0) h2),
          fun hx => ⟨Or.inr hx, hu₁ hx⟩⟩
      have hinter2 : ∀ v₀ v₂, v₀ ⊆ X₀ → v₂ ⊆ X₂ → (v₀ ∪ v₂) ∩ X₂ = v₂ := by
        intro v₀ v₂ hv₀ hv₂
        ext x
        simp only [mem_inter, mem_union]
        exact ⟨fun ⟨h1, h2⟩ => h1.resolve_left
          (fun hx0 => Finset.disjoint_left.1 hd02 (hv₀ hx0) h2),
          fun hx => ⟨Or.inr hx, hv₂ hx⟩⟩
      have ha₀_eq : a₀ = a₀' := by
        have := congrArg (· ∩ X₀) heq1
        rwa [hinter0 a₀ a₁ ha₀s ha₁s, hinter0 a₀' a₁' ha₀'s ha₁'s] at this
      have ha₁_eq : a₁ = a₁' := by
        have := congrArg (· ∩ X₁) heq1
        rwa [hinter1 a₀ a₁ ha₀s ha₁s, hinter1 a₀' a₁' ha₀'s ha₁'s] at this
      have hb₂_eq : b₂ = b₂' := by
        have := congrArg (· ∩ X₂) heq2
        rwa [hinter2 _ b₂ sdiff_subset hb₂s, hinter2 _ b₂' sdiff_subset hb₂'s] at this
      exact Prod.ext ha₀_eq (Prod.ext ha₁_eq hb₂_eq)
  obtain ⟨r, hcov, hr_le⟩ :=
    exists_coverNumber_weightSlice_le_of_const_hit (by omega) row col hmono hconst hM0 hM
  refine ⟨r, hcov, hr_le.trans ?_⟩
  have htwo_pow : 2 ^ n ≤ 2 * (n + 1) ^ 3 * Cprod := by
    have hc0 := Nat.four_pow_le_two_mul_add_one_mul_centralBinom x₀
    have hc1 := Nat.four_pow_le_two_mul_add_one_mul_centralBinom m₁
    have hc2 := Nat.four_pow_le_two_mul_add_one_mul_centralBinom m₂
    rw [Nat.centralBinom_eq_two_mul_choose] at hc0 hc1 hc2
    have hmul : 4 ^ (x₀ + m₁ + m₂) ≤
        ((2 * x₀ + 1) * (2 * m₁ + 1) * (2 * m₂ + 1)) * Cprod := by
      calc 4 ^ (x₀ + m₁ + m₂)
          = 4 ^ x₀ * 4 ^ m₁ * 4 ^ m₂ := by rw [pow_add, pow_add]
        _ ≤ ((2 * x₀ + 1) * (2 * x₀).choose x₀) *
              ((2 * m₁ + 1) * (2 * m₁).choose m₁) *
              ((2 * m₂ + 1) * (2 * m₂).choose m₂) :=
              Nat.mul_le_mul (Nat.mul_le_mul hc0 hc1) hc2
        _ = ((2 * x₀ + 1) * (2 * m₁ + 1) * (2 * m₂ + 1)) * Cprod := by ring
    have h4half : 2 ^ n ≤ 2 * 4 ^ (n / 2) := by
      have : n ≤ 1 + 2 * (n / 2) := by omega
      calc 2 ^ n ≤ 2 ^ (1 + 2 * (n / 2)) := Nat.pow_le_pow_right (by norm_num) this
        _ = 2 * 4 ^ (n / 2) := by rw [pow_add, pow_one, pow_mul]; norm_num
    have hfactors : (2 * x₀ + 1) * (2 * m₁ + 1) * (2 * m₂ + 1) ≤ (n + 1) ^ 3 := by
      calc (2 * x₀ + 1) * (2 * m₁ + 1) * (2 * m₂ + 1)
          ≤ (n + 1) * (n + 1) * (n + 1) :=
              Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
        _ = (n + 1) ^ 3 := by ring
    rw [hsum_half] at hmul
    calc 2 ^ n ≤ 2 * 4 ^ (n / 2) := h4half
      _ ≤ 2 * (((2 * x₀ + 1) * (2 * m₁ + 1) * (2 * m₂ + 1)) * Cprod) :=
            Nat.mul_le_mul_left 2 hmul
      _ ≤ 2 * ((n + 1) ^ 3 * Cprod) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right Cprod hfactors)
      _ = 2 * (n + 1) ^ 3 * Cprod := by ring
  have hk_le : 2 ^ k ≤ 2 * (n + 1) := by
    have hk0 : 2 ^ k ≤ 2 * (2 * x₀) := Code.two_pow_clog_succ_le_two_mul (by omega : 1 ≤ 2 * x₀)
    omega
  have hS_card : Fintype.card S = T.card * 2 ^ k := by
    rw [Fintype.card_prod, Fintype.card_coe, BitString.card]
  have hW3 : (disjointWeightPairs α p q).card ≤ 3 ^ n := by
    have hsub := card_le_card (disjointWeightPairs_subset_disjointPairs (α := α) p q)
    rwa [card_disjointPairs, card_univ] at hsub
  have hnat_bound :
      2 * (n + 1) * (disjointWeightPairs α p q).card * Fintype.card S * 2 ^ n ≤
        8 * (n + 1) ^ 5 * 3 ^ n * M := by
    rw [hS_card]
    calc 2 * (n + 1) * (disjointWeightPairs α p q).card * (T.card * 2 ^ k) * 2 ^ n
        ≤ 2 * (n + 1) * 3 ^ n * (T.card * (2 * (n + 1))) * (2 * (n + 1) ^ 3 * Cprod) :=
            Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul_left _ hW3)
                (Nat.mul_le_mul_left _ hk_le))
              htwo_pow
      _ = 8 * (n + 1) ^ 5 * 3 ^ n * M := by simp only [M]; ring
  have hreal_bound := (Nat.cast_le (α := ℝ)).2 hnat_bound
  push_cast at hreal_bound
  have hM0_real : (0 : ℝ) < M := by exact_mod_cast hM0
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [div_pow, div_le_iff₀ hM0_real]
  calc 2 * (n + 1 : ℝ) * (disjointWeightPairs α p q).card * Fintype.card S
      = (2 * (n + 1 : ℝ) * (disjointWeightPairs α p q).card * Fintype.card S * (2 : ℝ) ^ n) /
          (2 : ℝ) ^ n := by field_simp
    _ ≤ (8 * (n + 1 : ℝ) ^ 5 * (3 : ℝ) ^ n * M) / (2 : ℝ) ^ n :=
          div_le_div_of_nonneg_right hreal_bound h2n_pos.le
    _ = 8 * (n + 1 : ℝ) ^ 5 * ((3 : ℝ) ^ n / (2 : ℝ) ^ n) * M := by ring

/-! #### Case IV of [Sergeev2026UniqueDisjointness]: `n < 2 * p` and `p < n` -/

private theorem exists_coverNumber_weightSlice_case4 {α : Type*} [Fintype α] [DecidableEq α]
    {p q : ℕ} (hpq : p + q ≤ Fintype.card α) (h2p : Fintype.card α < 2 * p)
    (hpn : p < Fintype.card α) :
    ∃ r : ℕ,
      coverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) ≤ r ∧
        (r : ℝ) ≤ 8 * (Fintype.card α + 1 : ℝ) ^ 5 * (3 / 2 : ℝ) ^ Fintype.card α := by
  set n := Fintype.card α
  set z₀ : ℕ := (p * q) / (n - p)
  have hnp_pos : 1 ≤ n - p := by omega
  have hqz₀ : q ≤ z₀ := by
    have : q * (n - p) ≤ p * q := by
      rw [mul_comm]
      exact Nat.mul_le_mul_right q (by omega)
    exact (Nat.le_div_iff_mul_le hnp_pos).2 this
  have hz₀p : z₀ ≤ p := Nat.div_le_of_le_mul (by
    rw [mul_comm (n - p) p]
    exact Nat.mul_le_mul_left p (by omega))
  set m₁ : ℕ := q + z₀
  have hm₁_eq : m₁ = (n * q) / (n - p) := by
    have hadd := Nat.add_mul_div_right (p * q) q hnp_pos
    have hnum : p * q + q * (n - p) = n * q := by
      zify [show p ≤ n by omega]
      ring
    rw [hnum] at hadd
    omega
  have hm₁n : m₁ ≤ n := by
    rw [hm₁_eq]
    exact Nat.div_le_of_le_mul (by
      rw [mul_comm (n - p) n]
      exact Nat.mul_le_mul_left n (by omega))
  set m₂ : ℕ := n - m₁
  have hpm₂ : p - z₀ ≤ m₂ := by omega
  set k : ℕ := Nat.clog 2 (m₁ + 1)
  let Xdom := (univ : Finset α).powersetCard m₁
  let _ : Nonempty Xdom :=
    (powersetCard_nonempty.2 (by rw [card_univ]; exact hm₁n)).coe_sort
  let S := Xdom × BitString k
  let col (s : S) : Finset (Finset α) :=
    (s.1.val.powersetCard q).filter fun b => synPad k s.1.val b = s.2
  let row (s : S) : Finset (Finset α) :=
    (col s).biUnion fun b' => ((univ \ s.1.val).powersetCard (p - z₀)).image ((s.1.val \ b') ∪ ·)
  have hmono : ∀ s : S, ∀ a ∈ row s, ∀ b ∈ col s, (a ∩ b).card ≠ 1 := by
    rintro ⟨X, syn⟩ a ha b hb
    have hXc : X.val.card = m₁ := (mem_powersetCard.1 X.property).2
    obtain ⟨b', hb', ha₁_im⟩ := mem_biUnion.1 ha
    obtain ⟨a₁, ha₁, rfl⟩ := mem_image.1 ha₁_im
    have hb_f := mem_filter.1 hb
    have hb'_f := mem_filter.1 hb'
    have hb_sub : b ⊆ X.val := (mem_powersetCard.1 hb_f.1).1
    have hb'_sub : b' ⊆ X.val := (mem_powersetCard.1 hb'_f.1).1
    have ha₁_sub : a₁ ⊆ univ \ X.val := (mem_powersetCard.1 ha₁).1
    have hinter : ((X.val \ b') ∪ a₁) ∩ b = b ∩ (X.val \ b') := by
      ext x
      simp only [mem_inter, mem_union, mem_sdiff]
      refine ⟨fun ⟨hx1, hxb⟩ => ⟨hxb, ?_⟩, fun ⟨hxb, hxXb'⟩ => ⟨Or.inl hxXb', hxb⟩⟩
      exact hx1.resolve_right fun hxa₁ => (mem_sdiff.1 (ha₁_sub hxa₁)).2 (hb_sub hxb)
    rw [hinter]
    exact card_inter_sdiff_ne_one_of_synPad_eq (by rw [hXc]) hb_sub hb'_sub
      ((mem_powersetCard.1 hb_f.1).2.trans (mem_powersetCard.1 hb'_f.1).2.symm)
      (hb_f.2.trans hb'_f.2.symm)
  let goodC (X a b : Finset α) : Prop := b ⊆ X ∧ X \ b ⊆ a
  have hhit_iff : ∀ (X : Xdom) (syn : BitString k) (a b : Finset α),
      (a, b) ∈ disjointWeightPairs α p q →
      ((a ∈ row (X, syn) ∧ b ∈ col (X, syn)) ↔ goodC X.val a b ∧ syn = synPad k X.val b) := by
    intro X syn a b hab
    have hXc : X.val.card = m₁ := (mem_powersetCard.1 X.property).2
    obtain ⟨ha_card, hb_card, hdab⟩ := mem_disjointWeightPairs.1 hab
    refine ⟨fun ⟨har, hbc⟩ => ?_, fun ⟨⟨hbX, hXba⟩, hsyn⟩ => ?_⟩
    · obtain ⟨b', hb', ha₁_im⟩ := mem_biUnion.1 har
      obtain ⟨a₁, _, rfl⟩ := mem_image.1 ha₁_im
      have hb_f := mem_filter.1 hbc
      have hb'_f := mem_filter.1 hb'
      have hb_sub : b ⊆ X.val := (mem_powersetCard.1 hb_f.1).1
      have hdisj_b : Disjoint (X.val \ b') b := hdab.mono_left subset_union_left
      have hbb' : b ⊆ b' := fun x hxb => by
        by_contra hxnb'
        exact Finset.disjoint_left.1 hdisj_b (mem_sdiff.2 ⟨hb_sub hxb, hxnb'⟩) hxb
      have hb_eq : b = b' :=
        eq_of_subset_of_card_le hbb'
          (by rw [(mem_powersetCard.1 hb'_f.1).2, (mem_powersetCard.1 hb_f.1).2])
      subst hb_eq
      exact ⟨⟨hb_sub, subset_union_left⟩, hb_f.2.symm⟩
    · subst hsyn
      have hb_col : b ∈ col (X, synPad k X.val b) :=
        mem_filter.2 ⟨mem_powersetCard.2 ⟨hbX, hb_card⟩, rfl⟩
      let a₁ := a \ X.val
      have ha_inter : a ∩ X.val = X.val \ b := by
        refine (eq_of_subset_of_card_le (subset_inter hXba sdiff_subset) ?_).symm
        refine card_le_card fun x hx => ?_
        rw [mem_inter] at hx
        exact mem_sdiff.2 ⟨hx.2, Finset.disjoint_left.1 hdab hx.1⟩
      have ha₁_card : a₁.card = p - z₀ := by
        have h1 := card_sdiff_add_card_inter a X.val
        have h2 : (X.val \ b).card = z₀ := by
          rw [card_sdiff_of_subset hbX, hXc, hb_card]
          omega
        change a₁.card + (a ∩ X.val).card = a.card at h1
        rw [ha_inter, h2] at h1
        omega
      have ha₁_mem : a₁ ∈ (univ \ X.val).powersetCard (p - z₀) :=
        mem_powersetCard.2 ⟨subset_sdiff.2 ⟨subset_univ _, disjoint_sdiff_self_left⟩, ha₁_card⟩
      have ha_row : a ∈ row (X, synPad k X.val b) := by
        refine mem_biUnion.2 ⟨b, hb_col, mem_image.2 ⟨a₁, ha₁_mem, ?_⟩⟩
        rw [← ha_inter, union_comm]
        exact sdiff_union_inter a X.val
      exact ⟨ha_row, hb_col⟩
  have hhit_card : ∀ w ∈ disjointWeightPairs α p q,
      (univ.filter fun s : S => w.1 ∈ row s ∧ w.2 ∈ col s).card =
        (Xdom.filter fun X => goodC X w.1 w.2).card := by
    rintro ⟨a, b⟩ hw
    exact card_filter_prod_unique_syn (fun s : S => a ∈ row s ∧ b ∈ col s)
      (fun X => goodC X a b) (fun X => synPad k X b) fun X syn => hhit_iff X syn a b hw
  have hconst : ∀ w₁ ∈ disjointWeightPairs α p q, ∀ w₂ ∈ disjointWeightPairs α p q,
      (univ.filter fun s : S => w₁.1 ∈ row s ∧ w₁.2 ∈ col s).card =
        (univ.filter fun s : S => w₂.1 ∈ row s ∧ w₂.2 ∈ col s).card := by
    intro ⟨a₁, b₁⟩ hw₁ ⟨a₂, b₂⟩ hw₂
    rw [hhit_card (a₁, b₁) hw₁, hhit_card (a₂, b₂) hw₂]
    refine card_filter_eq_of_perm_invariant Xdom (fun σ X => X.map σ.toEmbedding)
      (fun σ X hX =>
        mem_powersetCard.2 ⟨subset_univ _, by rw [card_map, (mem_powersetCard.1 hX).2]⟩)
      (fun σ X => by simp [map_map]) goodC (fun σ X a b => ?_) hw₁ hw₂
    simp only [goodC, ← map_sdiff, map_subset_map]
  let Cprod : ℕ := m₁.choose z₀ * m₂.choose (p - z₀)
  let M : ℕ := n.choose m₁ * Cprod
  have hCprod_pos : 0 < Cprod :=
    Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos hpm₂)
  have hM0 : 0 < M := Nat.mul_pos (Nat.choose_pos hm₁n) hCprod_pos
  have hM : M ≤ ∑ s : S,
      ((disjointWeightPairs α p q).filter fun w => w.1 ∈ row s ∧ w.2 ∈ col s).card := by
    classical
    let W := disjointWeightPairs α p q
    have hXdom_c : Xdom.card = n.choose m₁ := by
      simp only [Xdom, card_powersetCard, card_univ]
      rfl
    rw [show M = Xdom.card * Cprod by simp only [M, hXdom_c]]
    refine mul_le_sum_card_filter_of_card_filter_eq W Xdom
      (fun s w => w.1 ∈ row s ∧ w.2 ∈ col s) (fun X w => goodC X w.1 w.2)
      hhit_card fun X hX => ?_
    have hXc : X.card = m₁ := (mem_powersetCard.1 hX).2
    have hX₂c : (univ \ X).card = m₂ := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, hXc]
    let src := X.powersetCard q ×ˢ (univ \ X).powersetCard (p - z₀)
    have hsrc_card : src.card = Cprod := by
      rw [card_product, card_powersetCard, card_powersetCard, hXc, hX₂c]
      have hsymm : m₁.choose q = m₁.choose z₀ := by
        have : m₁ - z₀ = q := by omega
        rw [← this, Nat.choose_symm (by omega)]
      rw [hsymm]
    rw [← hsrc_card]
    refine card_le_card_of_injOn (fun ba => ((X \ ba.1) ∪ ba.2, ba.1))
      (fun ⟨b, a₁⟩ hba => ?_) (fun ⟨b, a₁⟩ hba ⟨b', a₁'⟩ hba' heq => ?_)
    · obtain ⟨hb, ha₁⟩ := mem_product.1 (mem_coe.1 hba)
      have hbs := (mem_powersetCard.1 hb).1
      have ha₁s := (mem_powersetCard.1 ha₁).1
      have hd_a : Disjoint (X \ b) a₁ :=
        disjoint_sdiff_self_right.mono sdiff_subset ha₁s
      have ha_c : ((X \ b) ∪ a₁).card = p := by
        rw [card_union_of_disjoint hd_a, card_sdiff_of_subset hbs, hXc,
          (mem_powersetCard.1 hb).2, (mem_powersetCard.1 ha₁).2]
        omega
      have hd_ab : Disjoint ((X \ b) ∪ a₁) b :=
        disjoint_union_left.2
          ⟨disjoint_sdiff_self_left, disjoint_sdiff_self_left.mono ha₁s hbs⟩
      exact mem_coe.2 (mem_filter.2
        ⟨mem_disjointWeightPairs.2 ⟨ha_c, (mem_powersetCard.1 hb).2, hd_ab⟩,
         hbs, subset_union_left⟩)
    · obtain ⟨heq1, rfl⟩ := Prod.mk.inj heq
      have ha₁s := (mem_powersetCard.1 (mem_product.1 (mem_coe.1 hba)).2).1
      have ha₁'s := (mem_powersetCard.1 (mem_product.1 (mem_coe.1 hba')).2).1
      have hsdiffX : ∀ u, u ⊆ univ \ X → ((X \ b) ∪ u) \ X = u := by
        intro u hu
        ext x
        simp only [mem_sdiff, mem_union]
        exact ⟨fun ⟨h1, h2⟩ => h1.resolve_left (fun hx => h2 hx.1),
          fun hxu => ⟨Or.inr hxu, (mem_sdiff.1 (hu hxu)).2⟩⟩
      have ha₁_eq : a₁ = a₁' := by
        have := congrArg (· \ X) heq1
        rwa [hsdiffX a₁ ha₁s, hsdiffX a₁' ha₁'s] at this
      exact Prod.ext rfl ha₁_eq
  obtain ⟨r, hcov, hr_le⟩ :=
    exists_coverNumber_weightSlice_le_of_const_hit hpq row col hmono hconst hM0 hM
  refine ⟨r, hcov, hr_le.trans ?_⟩
  have hz₀_le : z₀ * (n - p) ≤ p * q := Nat.div_mul_le_self (p * q) (n - p)
  have hz₀_gt : p * q < (z₀ + 1) * (n - p) := by
    rw [mul_comm (z₀ + 1)]
    exact Nat.lt_mul_div_succ (p * q) hnp_pos
  have hhyp : n.choose p ≤ (p + 1) * Cprod := by
    have hm : m₁ + m₂ = n := Nat.add_sub_cancel' hm₁n
    have hm₁z : m₁ - z₀ = q := by omega
    have hm₂pz : m₂ - (p - z₀) = n - p - q := by omega
    refine hypergeom_choose_le hm hz₀p (by omega) hpm₂ ?_ ?_
    · rw [hm₁z, hm₂pz]
      zify [hz₀p, show q ≤ n - p by omega, show p ≤ n by omega] at hz₀_gt hqz₀ ⊢
      nlinarith
    · rw [hm₁z, hm₂pz]
      zify [hz₀p, show q ≤ n - p by omega, show p ≤ n by omega] at hz₀_le ⊢
      nlinarith
  have hk_le : 2 ^ k ≤ 2 * (n + 1) := by
    have hk0 : 2 ^ k ≤ max 1 (2 * m₁) := Code.two_pow_clog_succ_le_max m₁
    omega
  have hS_card : Fintype.card S = n.choose m₁ * 2 ^ k := by
    rw [Fintype.card_prod, Fintype.card_coe, BitString.card]
    simp only [Xdom, card_powersetCard, card_univ]
    rfl
  have hnp_choose : (n - p).choose q ≤ 2 ^ (n / 2) :=
    (Nat.choose_le_two_pow (n - p) q).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hW_le : (disjointWeightPairs α p q).card * Fintype.card S ≤
      2 * (n + 1) ^ 2 * 2 ^ (n / 2) * M := by
    rw [card_disjointWeightPairs p q, hS_card]
    have hp1 : p + 1 ≤ n + 1 := by omega
    calc n.choose p * (n - p).choose q * (n.choose m₁ * 2 ^ k)
        ≤ ((p + 1) * Cprod) * 2 ^ (n / 2) * (n.choose m₁ * (2 * (n + 1))) :=
            Nat.mul_le_mul (Nat.mul_le_mul hhyp hnp_choose) (Nat.mul_le_mul_left _ hk_le)
      _ ≤ ((n + 1) * Cprod) * 2 ^ (n / 2) * (n.choose m₁ * (2 * (n + 1))) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hp1))
      _ = 2 * (n + 1) ^ 2 * 2 ^ (n / 2) * M := by simp only [M]; ring
  exact two_mul_div_le_eight_mul_pow_five hM0 hW_le

/-! #### Assembling all weight slices `(p, q)` -/

private theorem exists_coverNumber_weightSlice_le {α : Type*} [Fintype α] [DecidableEq α]
    (p q : ℕ) :
    ∃ r : ℕ,
      coverNumber true (uniqueDisjointnessRel α) (weightSlice α p) (weightSlice α q) ≤ r ∧
        (r : ℝ) ≤ 8 * (Fintype.card α + 1 : ℝ) ^ 5 * (3 / 2 : ℝ) ^ Fintype.card α := by
  set n := Fintype.card α
  have hwlog : ∀ u v, v ≤ u →
      ∃ r : ℕ,
        coverNumber true (uniqueDisjointnessRel α) (weightSlice α u) (weightSlice α v) ≤ r ∧
          (r : ℝ) ≤ 8 * (n + 1 : ℝ) ^ 5 * (3 / 2 : ℝ) ^ n := by
    intro u v hvu
    rcases lt_or_ge n (u + v) with hgt | huv
    · refine ⟨0, ?_, by rw [Nat.cast_zero]; positivity⟩
      have h0 := partitionCoverNumber_weightSlice_eq_zero_of_lt (α := α) hgt
      exact coverNumber_le_partitionCoverNumber.trans h0.le
    · rcases Nat.eq_zero_or_pos v with rfl | hv_pos
      · refine ⟨1, ?_, ?_⟩
        · have h1 := partitionCoverNumber_weightSlice_le_choose_right (α := α) u 0
          rw [Nat.choose_zero_right] at h1
          exact coverNumber_le_partitionCoverNumber.trans h1
        · have hpow : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
          have hn1 : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 5 :=
            one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
          rw [Nat.cast_one]
          nlinarith
      · rcases le_or_gt (2 * u) n with h2u | h2u
        · rcases le_or_gt (2 * (u + v)) n with h2uv | h2uv
          · exact exists_coverNumber_weightSlice_case3 (by omega) h2uv
          · exact exists_coverNumber_weightSlice_case2 hvu h2uv h2u
        · exact exists_coverNumber_weightSlice_case4 huv h2u (by omega)
  rcases le_total q p with hqp | hpq
  · exact hwlog p q hqp
  · obtain ⟨r, hr, hbound⟩ := hwlog q p hpq
    rw [coverNumber_weightSlice_symm]
    exact ⟨r, hr, hbound⟩

/-- **Covering-rank (OR-rank) upper bound for unique disjointness**
([Sergeev2026UniqueDisjointness, §3, Theorem 2, pp. 4–6]): on any finite ground type `α`,
`coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ` is a finite natural number
`r ≤ 8 * (|α| + 1) ^ 7 * (3 / 2) ^ |α|`. -/
theorem exists_coverNumber_uniqueDisjointnessRel_le {α : Type*} [Fintype α] [DecidableEq α] :
    ∃ r : ℕ,
      coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ = r ∧
        (r : ℝ) ≤ 8 * (Fintype.card α + 1 : ℝ) ^ 7 * (3 / 2 : ℝ) ^ Fintype.card α := by
  set n := Fintype.card α
  choose r_pq hr_pq using fun (p q : Fin (n + 1)) =>
    exists_coverNumber_weightSlice_le (α := α) p.val q.val
  have hsum_cov : coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ ≤
      ((∑ p : Fin (n + 1), ∑ q : Fin (n + 1), r_pq p q : ℕ) : ℕ∞) := by
    calc coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ
        ≤ ∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
            coverNumber true (uniqueDisjointnessRel α)
              (Set.univ ∩ cardFin α ⁻¹' {p}) (Set.univ ∩ cardFin α ⁻¹' {q}) :=
          coverNumber_le_sum_fibers (cardFin α) (cardFin α)
      _ ≤ ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), (r_pq p q : ℕ∞) := by
          refine sum_le_sum fun p _ => sum_le_sum fun q _ => ?_
          rw [weightSlice_eq_univ_inter_preimage, weightSlice_eq_univ_inter_preimage]
          exact (hr_pq p q).1
      _ = ((∑ p : Fin (n + 1), ∑ q : Fin (n + 1), r_pq p q : ℕ) : ℕ∞) := by
          push_cast; rfl
  obtain ⟨r, hr⟩ :=
    ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hsum_cov)
  refine ⟨r, hr.symm, ?_⟩
  have hr_nat : r ≤ ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), r_pq p q := by
    exact_mod_cast hr.le.trans hsum_cov
  calc (r : ℝ)
      ≤ ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), (r_pq p q : ℝ) := by
          exact_mod_cast hr_nat
    _ ≤ ∑ _p : Fin (n + 1), ∑ _q : Fin (n + 1),
          8 * (n + 1 : ℝ) ^ 5 * (3 / 2 : ℝ) ^ n :=
          sum_le_sum fun p _ => sum_le_sum fun q _ => (hr_pq p q).2
    _ = 8 * (n + 1 : ℝ) ^ 7 * (3 / 2 : ℝ) ^ n := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

/-- **Exact `ℕ∞` form of Sergeev's Theorem 2** (matching the `ℕ∞` shape of Kaibel–Weltge's
`three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel`):
`2 ^ |α| * coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ ≤
  8 * (|α| + 1) ^ 7 * 3 ^ |α|`. -/
theorem two_pow_mul_coverNumber_uniqueDisjointnessRel_le {α : Type*} [Fintype α] [DecidableEq α] :
    (2 ^ Fintype.card α : ℕ∞) *
      coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ ≤
      ((8 * (Fintype.card α + 1) ^ 7 * 3 ^ Fintype.card α : ℕ) : ℕ∞) := by
  set n := Fintype.card α
  obtain ⟨r, hr_eq, hr_le⟩ := exists_coverNumber_uniqueDisjointnessRel_le (α := α)
  rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)] at hr_le
  have hnat : 2 ^ n * r ≤ 8 * (n + 1) ^ 7 * 3 ^ n := by
    have hreal : ((2 ^ n * r : ℕ) : ℝ) ≤ ((8 * (n + 1) ^ 7 * 3 ^ n : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hreal
  rw [hr_eq]
  calc (2 ^ n : ℕ∞) * (r : ℕ∞)
      = ((2 ^ n * r : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ ((8 * (n + 1) ^ 7 * 3 ^ n : ℕ) : ℕ∞) := by exact_mod_cast hnat

/-- **Polynomial-factor tightness of `(3 / 2) ^ n` for the covering rank of unique disjointness**
([KaibelWeltge2015, §3, p. 3, via the proof of Theorem 1 in §2, p. 3];
[Sergeev2026UniqueDisjointness, §3, Theorem 2, p. 4]): there exist
explicit constants `C, k : ℕ` (`C = 1024, k = 7`) such that for every `n ≥ 1`,
`coverNumber true (uniqueDisjointnessRel (Fin n)) Set.univ Set.univ` is a finite natural number `r`
satisfying `(3 / 2) ^ n ≤ r ≤ C * n ^ k * (3 / 2) ^ n`. -/
theorem exists_poly_coverNumber_uniqueDisjointnessRel :
    ∃ C k : ℕ, ∀ n ≥ 1, ∃ r : ℕ,
      coverNumber true (uniqueDisjointnessRel (Fin n)) Set.univ Set.univ = r ∧
        (3 / 2 : ℝ) ^ n ≤ r ∧ (r : ℝ) ≤ C * (n : ℝ) ^ k * (3 / 2 : ℝ) ^ n := by
  refine ⟨1024, 7, fun n hn => ?_⟩
  obtain ⟨r, hr_eq, hr_le⟩ := exists_coverNumber_uniqueDisjointnessRel_le (α := Fin n)
  simp only [Fintype.card_fin] at hr_le
  have hlow : (3 / 2 : ℝ) ^ n ≤ r := by
    simpa only [Fintype.card_fin] using
      three_div_two_pow_le_of_coverNumber_uniqueDisjointnessRel_le (K := ℝ) hr_eq.le
  have hn1 : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpow7 : (n + 1 : ℝ) ^ 7 ≤ 128 * (n : ℝ) ^ 7 := by
    calc (n + 1 : ℝ) ^ 7 ≤ (2 * (n : ℝ)) ^ 7 := pow_le_pow_left₀ (by positivity) hn1 7
      _ = 128 * (n : ℝ) ^ 7 := by ring
  refine ⟨r, hr_eq, hlow, hr_le.trans ?_⟩
  push_cast
  calc 8 * (n + 1 : ℝ) ^ 7 * (3 / 2 : ℝ) ^ n
      ≤ 8 * (128 * (n : ℝ) ^ 7) * (3 / 2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow7 (by norm_num)) (by positivity)
    _ = 1024 * (n : ℝ) ^ 7 * (3 / 2 : ℝ) ^ n := by ring

end Theorem2

end Nondeterministic

end Cslib.Communication
