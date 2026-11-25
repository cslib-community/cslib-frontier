/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Few coordinates separate a finite family of vectors

Let `A` be a finite family of vectors `κ → β`, compared on a finset `I` of `M` coordinates, and let
`t > 0`. Some set `S ⊆ I` of at most `⌈2 t log #A⌉` coordinates has the following property: any two
vectors of `A` that agree on `S` differ in at most `M / t` coordinates of `I`.

This is a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026], tracked in #8325: the
counting form of the paper's Claim 3.12 (§3.5, p. 22), abstracted from the estimation of preferred
actions. The source samples `k` coordinates independently and uniformly and takes a union bound over
pairs. Here the sample is a sequence in `I ^ k`, and the union bound is a count. For a pair `(a, b)`
differing in `D > M / t` coordinates of `I`, the sequences that miss every one of them number
`(M - D) ^ k = M ^ k (1 - D / M) ^ k`, at most `M ^ k / #A ^ 2` once `k ≥ 2 t log #A`. Fewer than
`#A ^ 2` ordered pairs (the diagonal never counts) therefore cover fewer than `M ^ k` sequences, and
the coordinates of any sequence they miss form `S`.

The source takes `k = 2t (log |A| + 1)`, so that `|A|² e^{-k/t} = e^{-2} < 1`. The count gives
`k = ⌈2 t log #A⌉` directly, and `S = ∅` whenever `#A ≤ 1` or `M = 0`. Only `t > 0` is needed; for
`t ≤ 1` the conclusion is trivial.

## Main results

* `Cslib.exists_separating_coordinates`: few coordinates separate a finite family, a step in the
  proof of Theorem 4.1 of [KhannaPuttermanSong2026] (the paper's Claim 3.12, abstracted).

## References

* [S. Khanna, A. Putterman, J. Song, *A Deterministic Linear Time Algorithm for Minimum Spanning
  Tree*][KhannaPuttermanSong2026]
-/

public section

namespace Cslib

open Finset

/-- **Few separating coordinates**, a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026]
(the paper's Claim 3.12, §3.5, p. 22, abstracted). For a finite family `A` of vectors `κ → β`, a
finset `I` of coordinates and `t > 0`, some `S ⊆ I` with `#S ≤ ⌈2 t log #A⌉₊` is such that any
`a, b ∈ A` agreeing on `S` differ in at most `#I / t` coordinates of `I`.

The source states `|S| = O(t √(m n))` from `|A| = e^{O(√(m n))}`, through the sample size
`k = 2t (log |A| + 1)`; the bound here is the sample size `⌈2 t log #A⌉₊`, which needs no `+ 1`. -/
theorem exists_separating_coordinates {κ β : Type*} [DecidableEq β]
    (I : Finset κ) (A : Finset (κ → β)) {t : ℝ} (ht : 0 < t) :
    ∃ S ⊆ I, #S ≤ ⌈2 * t * Real.log #A⌉₊ ∧
      ∀ a ∈ A, ∀ b ∈ A, (∀ i ∈ S, a i = b i) → (#{i ∈ I | a i ≠ b i} : ℝ) ≤ #I / t := by
  classical
  set M := #I
  set k := ⌈2 * t * Real.log #A⌉₊
  -- the pairs that differ in more than `M / t` coordinates
  set P := (A ×ˢ A).filter fun p => (M : ℝ) / t < #{i ∈ I | p.1 i ≠ p.2 i} with hPdef
  have hmemP {a b : κ → β} (ha : a ∈ A) (hb : b ∈ A)
      (hab : ¬ (#{i ∈ I | a i ≠ b i} : ℝ) ≤ M / t) : (a, b) ∈ P :=
    mem_filter.2 ⟨mem_product.2 ⟨ha, hb⟩, not_le.1 hab⟩
  rcases eq_empty_or_nonempty P with hP | ⟨⟨a₀, b₀⟩, hp₀⟩
  · exact ⟨∅, empty_subset _, by simp, fun a ha b hb _ => by_contra fun hab => by
      simpa [hP] using hmemP ha hb hab⟩
  have hA : (0 : ℝ) < #A := by
    exact_mod_cast card_pos.2 ⟨a₀, (mem_product.1 (mem_filter.1 hp₀).1).1⟩
  -- the coordinates of `I` where a pair agrees
  let agree : (κ → β) × (κ → β) → Finset κ := fun p => {i ∈ I | p.1 i = p.2 i}
  -- each pair of `P` agrees on at most a `1 / #A ^ 2` fraction of the `M ^ k` sequences
  have hkey : ∀ p ∈ P, (#(agree p) : ℝ) ^ k * #A ^ 2 ≤ (M : ℝ) ^ k := by
    intro p hp
    have hD := (mem_filter.1 hp).2
    set D := #{i ∈ I | p.1 i ≠ p.2 i}
    have hsplit : #(agree p) + D = M := card_filter_add_card_filter_not _
    have hDM : (D : ℝ) ≤ M := by exact_mod_cast (show D ≤ M by omega)
    have hD0 : (0 : ℝ) < D := lt_of_le_of_lt (by positivity) hD
    have hM : (0 : ℝ) < M := hD0.trans_le hDM
    have hq : (D : ℝ) / M ≤ 1 := (div_le_one hM).2 hDM
    have hc : Real.log ((#A : ℝ) ^ 2) ≤ k * ((D : ℝ) / M) := by
      have hk : 2 * t * Real.log #A ≤ k := Nat.le_ceil _
      have htq : 1 / t ≤ (D : ℝ) / M := by
        rw [div_le_div_iff₀ ht hM]; rw [div_lt_iff₀ ht] at hD; linarith
      rw [Real.log_pow]
      calc ((2 : ℕ) : ℝ) * Real.log #A = 2 * t * Real.log #A * (1 / t) := by push_cast; field_simp
        _ ≤ k * (1 / t) := mul_le_mul_of_nonneg_right hk (by positivity)
        _ ≤ k * ((D : ℝ) / M) := mul_le_mul_of_nonneg_left htq (by positivity)
    have hpow := Real.one_sub_pow_le_exp hq hc
    rw [Real.exp_neg, Real.exp_log (by positivity)] at hpow
    have hagree : (#(agree p) : ℝ) = M * (1 - D / M) := by
      rw [mul_one_sub, mul_div_cancel₀ _ hM.ne']
      have : ((#(agree p) + D : ℕ) : ℝ) = M := by exact_mod_cast hsplit
      push_cast at this; linarith
    rw [hagree, mul_pow, mul_assoc]
    calc (M : ℝ) ^ k * ((1 - D / M) ^ k * #A ^ 2) ≤ (M : ℝ) ^ k * (((#A : ℝ) ^ 2)⁻¹ * #A ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (by positivity))
            (by positivity)
      _ = (M : ℝ) ^ k := by rw [inv_mul_cancel₀ (by positivity), mul_one]
  have hM : 0 < M := by
    have hD := (mem_filter.1 hp₀).2
    by_contra h0
    have hsub : #{i ∈ I | a₀ i ≠ b₀ i} ≤ M := card_filter_le _ _
    have : (#{i ∈ I | a₀ i ≠ b₀ i} : ℝ) ≤ M / t := by
      rw [show #{i ∈ I | a₀ i ≠ b₀ i} = 0 by omega, show M = 0 by omega]; simp
    linarith
  -- fewer than `#A ^ 2` pairs: the diagonal is excluded
  have hPlt : #P < #A ^ 2 := by
    have ha₀ : a₀ ∈ A := (mem_product.1 (mem_filter.1 hp₀).1).1
    rw [sq, ← card_product]
    refine card_lt_card ⟨filter_subset _ _, fun h => ?_⟩
    have := (mem_filter.1 (h (show (a₀, a₀) ∈ A ×ˢ A from mem_product.2 ⟨ha₀, ha₀⟩))).2
    have h0 : #{i ∈ I | a₀ i ≠ a₀ i} = 0 := by simp
    rw [h0, Nat.cast_zero] at this
    exact (not_lt.2 (by positivity)) this
  -- the sequences of `k` coordinates, and those on which some pair of `P` agrees throughout
  let seqs := Fintype.piFinset fun _ : Fin k => I
  let badSeqs := P.biUnion fun p => Fintype.piFinset fun _ : Fin k => agree p
  have hlt : #badSeqs < #seqs := by
    have hbad : #badSeqs ≤ ∑ p ∈ P, #(agree p) ^ k := by
      refine card_biUnion_le.trans (le_of_eq (sum_congr rfl fun p _ => ?_))
      rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    have hseqs : #seqs = M ^ k := by
      rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    rw [hseqs]
    have hreal : (∑ p ∈ P, (#(agree p) : ℝ) ^ k) < (M : ℝ) ^ k := by
      have hA2 : (0 : ℝ) < #A ^ 2 := by positivity
      have hMk : (0 : ℝ) < (M : ℝ) ^ k := pow_pos (by exact_mod_cast hM) k
      calc (∑ p ∈ P, (#(agree p) : ℝ) ^ k) ≤ ∑ _p ∈ P, (M : ℝ) ^ k / #A ^ 2 :=
            sum_le_sum fun p hp => (le_div_iff₀ hA2).2 (hkey p hp)
        _ = #P * (M : ℝ) ^ k / #A ^ 2 := by rw [sum_const, nsmul_eq_mul, mul_div_assoc]
        _ < (M : ℝ) ^ k := by
          rw [div_lt_iff₀ hA2, mul_comm ((M : ℝ) ^ k)]
          exact mul_lt_mul_of_pos_right (by exact_mod_cast hPlt) hMk
    exact hbad.trans_lt (by exact_mod_cast hreal)
  obtain ⟨s, hs, hsbad⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hsI : ∀ j, s j ∈ I := Fintype.mem_piFinset.1 hs
  refine ⟨univ.image s, fun i hi => ?_, ?_, fun a ha b hb hab => by_contra fun hne => ?_⟩
  · obtain ⟨j, -, rfl⟩ := mem_image.1 hi
    exact hsI j
  · exact card_image_le.trans (by rw [card_univ, Fintype.card_fin])
  · refine hsbad (mem_biUnion.2 ⟨(a, b), hmemP ha hb hne, Fintype.mem_piFinset.2 fun j => ?_⟩)
    exact mem_filter.2 ⟨hsI j, hab _ (mem_image_of_mem s (mem_univ j))⟩

end Cslib
