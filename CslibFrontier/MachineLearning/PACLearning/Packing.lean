/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.GrowthFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Data.Code.HammingBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Packing numbers of a binary class on a sample

Fix points `x : Fin m → α` and a binary concept class `C`. A set `P` of labelings of `x` realized
by `C` is *`ε`-separated* if any two distinct labelings in `P` differ on at least `ε m` of the
points, i.e. their normalized Hamming distance is at least `ε`. This file bounds the size of such
a set by the growth function, and hence, by Sauer's lemma, by a power of `1 / ε` whose exponent is
proportional to the VC dimension and independent of `m`.

The argument is *subsampling* [Vershynin2018, Lemma 8.3.19 and Theorem 8.3.18]. A uniformly random
tuple `t` of `k` indices separates a fixed pair of `ε`-separated labelings unless all `k` indices
land where they agree, which happens with probability at most `(1 - ε) ^ k ≤ exp (-ε k)`. When
`|P|² exp (-ε k) < 1`, some `t` separates every pair, so the labelings in `P` stay distinct on the
`k` points `x ∘ t` and `|P| ≤ Π_C(k)`. The proof counts the tuples directly. Taking
`k = ⌊2 log |P| / ε⌋ + 1` and the form `Π_C(k) ≤ exp (k / T) T ^ d` of Sauer's lemma with
`T = 4 / ε` gives `|P| ≤ (8 / ε) ^ (2 d)` when every set shattered by `C` has at most `d` points.
This is Dudley's bound, with a constant in the exponent; Haussler's sharper
`e (d + 1) (2 e / ε) ^ d` is proved in
`CslibFrontier/MachineLearning/PACLearning/HausslerPacking.lean`.

A maximal separated subset is also a net at the same scale
(`Cslib.Code.exists_subset_pairwise_lt_hammingDist_forall_exists_le`), so the bound also limits the
size of nets. Chaining arguments need nets at every scale whose sizes grow polynomially in `1 / ε`.
They give the agnostic sample complexity `O((d + log (1 / δ)) / ε²)` stated in
[ShalevShwartzBenDavid2014, Theorem 6.8]. That book proves only the weaker
`O((d log (d / ε) + log (1 / δ)) / ε²)` (Section 28.1), leaving out the chaining argument
(Lemma 27.4) that the sharp form needs.

## Main results

- `exists_injOn_comp_of_two_mul_log_card_lt`: a tuple of `k` indices on which the words of an
  `ε`-separated set stay distinct, when `2 log |P| < ε k`.
- `card_le_growthFunction_of_two_mul_log_card_lt`: an `ε`-separated set of labelings realized by
  `C` has at most `Π_C(k)` elements.
- `card_le_div_pow_of_forall_two_mul_log_card_lt`: general subsampling-and-squaring step turning an
  exponential-polynomial subsample bound `exp (r / T) (T K) ^ d` into `(8 K / ε) ^ (2 d)`.
- `card_le_div_pow_of_le_hammingDist`: with Sauer's lemma, it has at most `(8 / ε) ^ (2 d)`.

## References

* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Section 8.3
* [R. M. Dudley, *Central limit theorems for empirical measures*][Dudley1978]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open Finset

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- **Subsampling.** If any two distinct words in `P` differ in at least `ε m` of their `m` letters
and `2 log |P| < ε k`, then some `k` of the positions, possibly repeated, already distinguish all
words in `P`. -/
theorem exists_injOn_comp_of_two_mul_log_card_lt {β : Type*} [DecidableEq β] {m k : ℕ}
    (hm : 0 < m) (P : Finset (Fin m → β)) {ε : ℝ}
    (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v)
    (hk : 2 * Real.log P.card < ε * k) :
    ∃ t : Fin k → Fin m, Set.InjOn (fun (u : Fin m → β) j => u (t j)) P := by
  classical
  -- The tuples on which a given ordered pair of distinct words agree.
  set agree : (Fin m → β) × (Fin m → β) → Finset (Fin m) := fun p => univ.filter
    fun i => p.1 i = p.2 i
  set bad : Finset (Fin k → Fin m) :=
    P.offDiag.biUnion fun p => Fintype.piFinset fun _ : Fin k => agree p
  -- A pair at Hamming distance at least `ε m` agrees on at most `exp (-ε) m` points.
  have hagree : ∀ p ∈ P.offDiag, ((agree p).card : ℝ) ≤ Real.exp (-ε) * m := fun p hp => by
    obtain ⟨hp1, hp2, hne⟩ := mem_offDiag.1 hp
    have hsum : ((agree p).card : ℝ) + hammingDist p.1 p.2 = m := by
      exact_mod_cast (by simpa [agree, hammingDist] using
        card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun i => p.1 i = p.2 i) :
          (agree p).card + hammingDist p.1 p.2 = m)
    nlinarith [hP _ hp1 _ hp2 hne, Real.add_one_le_exp (-ε), Nat.cast_nonneg (α := ℝ) m]
  -- Fewer than `m ^ k` tuples are bad.
  have hbad : bad.card < Fintype.card (Fin k → Fin m) := by
    rcases P.eq_empty_or_nonempty with rfl | hPne
    · simpa [bad] using pow_pos hm k
    have hN : (0 : ℝ) < P.card := Nat.cast_pos.mpr hPne.card_pos
    have hlt : (P.card : ℝ) ^ 2 * Real.exp (-ε) ^ k < 1 := by
      rw [← Real.exp_log hN, ← Real.exp_natCast_mul, ← Real.exp_natCast_mul, ← Real.exp_add,
        Real.exp_lt_one_iff]
      push_cast
      linarith
    have hcard : (bad.card : ℝ) < (m : ℝ) ^ k := calc
      (bad.card : ℝ) ≤ ∑ p ∈ P.offDiag, ((agree p).card : ℝ) ^ k := by
        exact_mod_cast (card_biUnion_le.trans_eq <| by simp [Fintype.card_piFinset])
      _ ≤ ∑ _p ∈ P.offDiag, (Real.exp (-ε) * m) ^ k :=
        sum_le_sum fun p hp => pow_le_pow_left₀ (Nat.cast_nonneg _) (hagree p hp) k
      _ = P.offDiag.card * (Real.exp (-ε) * m) ^ k := by rw [sum_const, nsmul_eq_mul]
      _ ≤ P.card ^ 2 * (Real.exp (-ε) * m) ^ k := by
        gcongr
        rw [offDiag_card]
        exact_mod_cast (Nat.sub_le _ _).trans_eq (sq _).symm
      _ = (P.card ^ 2 * Real.exp (-ε) ^ k) * (m : ℝ) ^ k := by ring
      _ < 1 * (m : ℝ) ^ k := by gcongr
      _ = (m : ℝ) ^ k := one_mul _
    simpa [Fintype.card_fun] using (by exact_mod_cast hcard : bad.card < m ^ k)
  obtain ⟨t, -, ht⟩ := exists_mem_notMem_of_card_lt_card
    (by simpa using hbad : bad.card < (univ : Finset (Fin k → Fin m)).card)
  exact ⟨t, fun u hu v hv huv => by_contra fun hne => ht (mem_biUnion.2 ⟨(u, v),
    mem_offDiag.2 ⟨hu, hv, hne⟩, by simp [agree, fun j => congrFun huv j]⟩)⟩

/-- **Packing by the growth function.** If the labelings in `P ⊆ restriction C x` pairwise differ
on at least `ε m` of the `m > 0` points `x` and `2 log |P| < ε k`, then `|P| ≤ Π_C(k)`. -/
theorem card_le_growthFunction_of_two_mul_log_card_lt (C : ConceptClass α Bool) {m k : ℕ}
    (hm : 0 < m) {x : Fin m → α} {P : Finset (Fin m → Bool)}
    (hPC : ∀ u ∈ P, u ∈ restriction C x) {ε : ℝ}
    (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v)
    (hk : 2 * Real.log P.card < ε * k) :
    P.card ≤ growthFunction C k := by
  classical
  obtain ⟨t, ht⟩ := exists_injOn_comp_of_two_mul_log_card_lt hm P hP hk
  calc P.card = ((P.image fun (u : Fin m → Bool) j => u (t j) : Finset _) : Set _).ncard := by
        rw [Set.ncard_coe_finset, card_image_of_injOn ht]
    _ ≤ (restriction C (x ∘ t)).ncard := Set.ncard_le_ncard (fun w hw => by
        obtain ⟨u, hu, rfl⟩ := mem_image.1 (mem_coe.1 hw)
        obtain ⟨c, hc, hcu⟩ := mem_restriction.1 (hPC u hu)
        exact mem_restriction.2 ⟨c, hc, fun j => hcu (t j)⟩) (Set.toFinite _)
    _ ≤ growthFunction C k := ncard_restriction_le_growthFunction C (x ∘ t)

/-- **Subsampling-and-squaring packing step:** if any `r` satisfying `2 log |P| < ε r` (with
`0 < m`) bounds `P.card` by `exp (r / T) · (T · K) ^ d` for every `T ≥ 1` (where `K ≥ 1` and
`0 < ε ≤ 1`), then `P.card ≤ (8 K / ε) ^ (2 d)`. Choosing `K = 1` gives Dudley's binary VC bound;
choosing `K = max 1 (|β| choose 2)` gives the multiclass Natarajan bound. -/
theorem card_le_div_pow_of_forall_two_mul_log_card_lt {β : Type*} {m d : ℕ}
    {P : Finset (Fin m → β)} {ε K : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsub : ∀ {r : ℕ} {T : ℝ}, 0 < m → 2 * Real.log P.card < ε * r → 1 ≤ T →
      (P.card : ℝ) ≤ Real.exp (r / T) * (T * K) ^ d) :
    (P.card : ℝ) ≤ (8 * K / ε) ^ (2 * d) := by
  have hone : (1 : ℝ) ≤ (8 * K / ε) ^ (2 * d) :=
    one_le_pow₀ (by rw [le_div_iff₀ hε]; linarith)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact (by exact_mod_cast (card_le_one.mpr fun _ _ _ _ => funext fun i => i.elim0 :
      P.card ≤ 1) : (P.card : ℝ) ≤ 1).trans hone
  rcases P.eq_empty_or_nonempty with rfl | hPne
  · simpa using zero_le_one.trans hone
  have hN : (0 : ℝ) < P.card := Nat.cast_pos.mpr hPne.card_pos
  set L := Real.log P.card
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hPne.card_pos)
  set k := ⌊2 * L / ε⌋₊ + 1
  set T := 4 / ε
  have hk1 : 2 * L / ε < k := by
    push_cast [k]
    exact Nat.lt_floor_add_one _
  have hk2 : (k : ℝ) ≤ 2 * L / ε + 1 := by
    push_cast [k]; linarith [Nat.floor_le (by positivity : 0 ≤ 2 * L / ε)]
  have hsauer := hsub (T := T) hm (by linarith [(div_lt_iff₀ hε).1 hk1])
    (by rw [le_div_iff₀ hε]; linarith)
  have hkT : (k : ℝ) / T ≤ L / 2 + ε / 4 := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have := mul_le_mul_of_nonneg_left hk2 hε.le
    rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one] at this; linarith
  have hle : (P.card : ℝ) ≤ Real.exp (ε / 2) * (T * K) ^ (2 * d) := by
    refine le_of_mul_le_mul_left ?_ hN
    calc (P.card : ℝ) * P.card = (P.card : ℝ) ^ 2 := (sq _).symm
      _ ≤ (Real.exp (L / 2 + ε / 4) * (T * K) ^ d) ^ 2 := by
        gcongr
        exact hsauer.trans (by gcongr)
      _ = Real.exp L * (Real.exp (ε / 2) * (T * K) ^ (2 * d)) := by
        rw [mul_pow, ← pow_mul, mul_comm d, ← Real.exp_natCast_mul, ← mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring
      _ = P.card * (Real.exp (ε / 2) * (T * K) ^ (2 * d)) := by rw [Real.exp_log hN]
  have hexp2 : Real.exp (ε / 2) < 2 := lt_of_pow_lt_pow_left₀ 2 zero_le_two <| by
    rw [← Real.exp_natCast_mul]
    calc Real.exp ((2 : ℕ) * (ε / 2)) = Real.exp ε := by push_cast; ring_nf
      _ ≤ Real.exp 1 := Real.exp_le_exp.2 hε1
      _ < 2 ^ 2 := by linarith [Real.exp_one_lt_d9]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hlt2 : P.card < 2 := by
      exact_mod_cast (calc (P.card : ℝ) ≤ Real.exp (ε / 2) * (T * K) ^ (2 * 0) := hle
        _ = Real.exp (ε / 2) := by ring
        _ < 2 := hexp2)
    simpa using (by exact_mod_cast (show P.card ≤ 1 by omega) : (P.card : ℝ) ≤ 1)
  · calc (P.card : ℝ) ≤ Real.exp (ε / 2) * (T * K) ^ (2 * d) := hle
      _ ≤ 2 ^ (2 * d) * (T * K) ^ (2 * d) := by
          gcongr
          calc Real.exp (ε / 2) ≤ 2 := hexp2.le
            _ = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (2 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (8 * K / ε) ^ (2 * d) := by
          rw [← mul_pow]
          congr 1
          ring

/-- **Packing bound for VC classes** [Vershynin2018, Theorem 8.3.18; Dudley1978]: if every set
shattered by `C` has at most `d` points, a set of labelings realized by `C` on `m` points whose
members pairwise differ on at least `ε m` points, `0 < ε ≤ 1`, has at most `(8 / ε) ^ (2 d)`
elements. -/
theorem card_le_div_pow_of_le_hammingDist {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} {x : Fin m → α}
    {P : Finset (Fin m → Bool)} (hPC : ∀ u ∈ P, u ∈ restriction C x) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v) :
    (P.card : ℝ) ≤ (8 / ε) ^ (2 * d) := by
  simpa only [mul_one] using
    card_le_div_pow_of_forall_two_mul_log_card_lt (K := 1) le_rfl hε hε1
      fun {r T} hm hlog hT1 => by
        simpa only [mul_one] using (Nat.cast_le.mpr
          (card_le_growthFunction_of_two_mul_log_card_lt C hm hPC hP hlog)).trans
          (growthFunction_le_exp_mul_pow hC r hT1)

/-- Every finite set `L : Finset (Fin m → β)` contains an `ε`-separated subset `N ⊆ L` (`0 ≤ ε`)
whose `ε m`-Hamming balls cover `L`. -/
theorem exists_subset_separated_and_covering {β : Type*} [DecidableEq β] {m : ℕ}
    (L : Finset (Fin m → β)) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ N ⊆ L, (∀ u ∈ N, ∀ v ∈ N, u ≠ v → ε * m ≤ hammingDist u v) ∧
      ∀ u ∈ L, ∃ v ∈ N, (hammingDist v u : ℝ) ≤ ε * m := by
  obtain ⟨N, hNL, hNsep, hcov⟩ :=
    Cslib.Code.exists_subset_pairwise_lt_hammingDist_forall_exists_le L ⌊ε * m⌋₊
  refine ⟨N, hNL, fun u hu v hv huv => ?_, fun u hu => ?_⟩
  · calc ε * m ≤ (⌊ε * m⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one (ε * m)).le
      _ ≤ hammingDist u v := by exact_mod_cast hNsep hu hv huv
  · obtain ⟨v, hvN, hvu⟩ := hcov u hu
    exact ⟨v, hvN, (Nat.cast_le.mpr hvu).trans (Nat.floor_le (by positivity))⟩

end Cslib.MachineLearning.PACLearning
