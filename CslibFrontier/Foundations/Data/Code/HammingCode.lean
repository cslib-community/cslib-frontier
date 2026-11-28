/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.Code.ParityCheck
import Mathlib.Data.Finset.SymmDiff

/-!
# Shortened binary Hamming codes and distance-3 cube partitions

If a binary parity-check matrix `H : Matrix κ ι Bool` has nonzero, pairwise distinct columns, every
nonzero word in `parityCheckCode H` has Hamming weight at least `3`, so `parityCheckCode H` and all
of its syndrome cosets `syndrome H ⁻¹' {s}` have minimum distance at least `3`
(`three_le_minDist_parityCheckCode_of_injective`, `minDist_parityCheckCode_le_syndrome_preimage`).

Taking column `i : Fin n` to be the `⌈log₂ (n + 1)⌉`-bit binary numeral of `i + 1` gives the
shortened binary Hamming parity-check matrix `hammingCheckMatrix n` (at `n = 2 ^ m - 1`, the
classic `[2 ^ m - 1, 2 ^ m - 1 - m, 3]` Hamming code [MacWilliamsSloane1977, Chapter 1, §7]). Its
`2 ^ ⌈log₂ (n + 1)⌉ ≤ max 1 (2 * n)` syndrome fibers partition the Boolean cube `Fin n → Bool` into
pairwise-disjoint codes of minimum distance at least `3`, formalizing Lemma 1 of
[Sergeev2026UniqueDisjointness, §2, p. 3] (`exists_partition_minDist_three`). Transporting the
syndrome coloring along `Finset.equivFin` colors the subsets of any finite set `S : Finset α` with
at most `max 1 (2 * S.card)` colors so that distinct subsets of `S` in the same color class have
symmetric difference of size at least `3` (`three_le_card_symmDiff_of_finsetHammingSyndrome_eq`).

## Main definitions

* `Cslib.Code.hammingCheckMatrix`: the `⌈log₂ (n + 1)⌉ × n` binary Hamming parity-check matrix.
* `Cslib.Code.finsetHammingSyndrome`: the induced Hamming syndrome coloring on subsets of a finite
  set `S : Finset α`.

## Main results

* `Cslib.Code.minDist_parityCheckCode_le_syndrome_preimage`: every syndrome coset of a linear
  parity-check code over a commutative ring has minimum distance at least that of the kernel.
* `Cslib.Code.three_le_minDist_parityCheckCode_of_injective`: nonzero, pairwise distinct binary
  parity-check columns force minimum distance at least `3`.
* `Cslib.Code.three_le_minDist_hammingParityCheckCode`,
  `Cslib.Code.three_le_minDist_hammingSyndrome_preimage`: the shortened binary Hamming code and its
  syndrome fibers have minimum distance at least `3`.
* `Cslib.Code.two_pow_clog_succ_le_two_mul`, `Cslib.Code.two_pow_clog_succ_le_max`: the syndrome
  count `2 ^ ⌈log₂ (n + 1)⌉` is at most `2 * n` for `1 ≤ n` (and `max 1 (2 * n)` for all `n`).
* `Cslib.Code.exists_partition_minDist_three`: Lemma 1 of [Sergeev2026UniqueDisjointness]: for
  `1 ≤ n`, `Fin n → Bool` partitions into `2 * n` pairwise-disjoint `3`-codes.
* `Cslib.Code.three_le_card_symmDiff_of_finsetHammingSyndrome_eq`: distinct subsets of `S` with the
  same `finsetHammingSyndrome` differ on at least `3` elements.

## References

* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977], Chapter 1, §7
* [I. S. Sergeev, *Upper Bounds for the Monotone Rank of the Unique Disjointness Matrix*]
  [Sergeev2026UniqueDisjointness], §2, Lemma 1, p. 3
-/

public section

namespace Cslib.Code

open Finset Function Matrix

section General

/-- Every syndrome coset `syndrome H ⁻¹' {s}` of a parity-check matrix over a commutative ring has
minimum distance at least that of `parityCheckCode H`. -/
theorem minDist_parityCheckCode_le_syndrome_preimage {κ ι R : Type*} [Fintype ι] [CommRing R]
    [DecidableEq R] (H : Matrix κ ι R) (s : κ → R) :
    minDist (parityCheckCode H : Set (ι → R)) ≤ minDist (syndrome H ⁻¹' {s}) := by
  refine le_minDist_iff.2 fun x hx y hy hxy => ?_
  rw [Set.mem_preimage, Set.mem_singleton_iff, syndrome_eq] at hx hy
  have hmem : -x + y ∈ parityCheckCode H := by
    rw [mem_parityCheckCode, Matrix.mulVec_add, Matrix.mulVec_neg, hx, hy, neg_add_cancel]
  rw [hammingDist_eq_hammingNorm]
  exact (le_minDist_iff_hammingNorm (parityCheckCode H)).1 le_rfl (-x + y) hmem
    (fun h0 => hxy (neg_add_eq_zero.1 h0))

/-- If a binary parity-check matrix `H : Matrix κ ι Bool` has nonzero, pairwise distinct columns,
then `parityCheckCode H` has minimum distance at least `3`. -/
theorem three_le_minDist_parityCheckCode_of_injective {κ ι : Type*} [Fintype ι]
    {H : Matrix κ ι Bool} (hne : ∀ i, (fun k => H k i) ≠ 0)
    (hinj : Function.Injective fun i k => H k i) :
    3 ≤ minDist (parityCheckCode H : Set (ι → Bool)) := by
  classical
  refine (le_minDist_iff_hammingNorm (parityCheckCode H)).2 fun x hx hx0 => ?_
  rw [mem_parityCheckCode] at hx
  let col : ι → (κ → Bool) := fun i k => H k i
  let D : Finset ι := univ.filter fun i => x i ≠ 0
  have hcard : D.card = hammingNorm x := rfl
  have hsum : ∑ i ∈ D, col i = 0 := by
    funext k
    rw [Pi.zero_apply, Finset.sum_apply]
    have hmul : (H *ᵥ x) k = ∑ i ∈ D, col i k := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases hxi : x i
      · change H k i * 0 = if (0 : Bool) ≠ 0 then col i k else 0
        simp only [mul_zero, ne_eq, not_true_eq_false, ↓reduceIte]
      · change H k i * 1 = if (1 : Bool) ≠ 0 then col i k else 0
        simp only [col, mul_one, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte]
    rw [← hmul, hx, Pi.zero_apply]
  suffices 3 ≤ D.card by exact_mod_cast hcard ▸ this
  by_contra! hlt
  rcases (by omega : D.card = 0 ∨ D.card = 1 ∨ D.card = 2) with h0 | h1 | h2
  · exact hx0 (hammingNorm_eq_zero.1 (hcard ▸ h0))
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
    rw [hi, Finset.sum_singleton] at hsum
    exact hne i hsum
  · obtain ⟨i, j, hij, hij_eq⟩ := Finset.card_eq_two.1 h2
    rw [hij_eq, Finset.sum_pair hij] at hsum
    exact hij (hinj (by
      simpa only [BitString.add_cancel_right, zero_add] using congrArg (· + col j) hsum))

end General

section Hamming

/-- The parity-check matrix of the shortened binary Hamming code of length `n`: column `i` is the
`⌈log₂ (n + 1)⌉`-bit binary numeral of `i + 1` (nonzero and injective). At `n = 2 ^ m - 1` (`m ≥ 1`)
this is the standard `[2 ^ m - 1, 2 ^ m - 1 - m, 3]` binary Hamming parity-check matrix
[MacWilliamsSloane1977, Chapter 1, §7]; for general `n`, its syndrome fibers realize the coset
restriction `(c, 0⃗) ∈ C_s` of [Sergeev2026UniqueDisjointness, §2, Lemma 1, p. 3]. -/
@[expose] def hammingCheckMatrix (n : ℕ) :
    Matrix (Fin (Nat.clog 2 (n + 1))) (Fin n) Bool :=
  fun k i => BitString.indexBits (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) k

private theorem hammingCheckMatrix_col_ne_zero (n : ℕ) (i : Fin n) :
    (fun k => hammingCheckMatrix n k i) ≠ 0 := by
  intro h0
  have hval := congrArg (fun w => (BitString.equivFin (Nat.clog 2 (n + 1)) w : ℕ)) h0
  have h1 : (BitString.equivFin (Nat.clog 2 (n + 1)) (fun k => hammingCheckMatrix n k i) : ℕ) =
      i.val + 1 := by
    change (BitString.equivFin _ (BitString.indexBits ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) : ℕ) =
      i.val + 1
    simp only [BitString.indexBits, Equiv.apply_symm_apply, Fin.val_castLE]
  have h2 : (BitString.equivFin (Nat.clog 2 (n + 1)) (0 : BitString _) : ℕ) = 0 :=
    BitString.val_equivFin_false _
  omega

private theorem hammingCheckMatrix_col_injective (n : ℕ) :
    Function.Injective fun i k => hammingCheckMatrix n k i := fun _ _ hij =>
  Fin.ext (Nat.succ.inj (Fin.mk.inj (BitString.indexBits_injective (n := n + 1) hij)))

/-- The shortened binary Hamming code `parityCheckCode (hammingCheckMatrix n)` has minimum distance
at least `3`. -/
theorem three_le_minDist_hammingParityCheckCode (n : ℕ) :
    3 ≤ minDist (parityCheckCode (hammingCheckMatrix n) : Set (Fin n → Bool)) :=
  three_le_minDist_parityCheckCode_of_injective
    (hammingCheckMatrix_col_ne_zero n)
    (hammingCheckMatrix_col_injective n)

/-- Every syndrome fiber of `hammingCheckMatrix n` has minimum distance at least `3`. -/
theorem three_le_minDist_hammingSyndrome_preimage (n : ℕ)
    (s : BitString (Nat.clog 2 (n + 1))) :
    3 ≤ minDist (syndrome (hammingCheckMatrix n) ⁻¹' {s}) :=
  (three_le_minDist_hammingParityCheckCode n).trans
    (minDist_parityCheckCode_le_syndrome_preimage (hammingCheckMatrix n) s)

/-- For `1 ≤ n`, the number of Hamming syndromes `2 ^ ⌈log₂ (n + 1)⌉` is at most `2 * n`. -/
theorem two_pow_clog_succ_le_two_mul {n : ℕ} (hn : 1 ≤ n) :
    2 ^ Nat.clog 2 (n + 1) ≤ 2 * n := by
  have h1 : 1 < n + 1 := by omega
  have hpos : 1 ≤ Nat.clog 2 (n + 1) := Nat.clog_pos Nat.one_lt_two h1
  have hlt : 2 ^ (Nat.clog 2 (n + 1) - 1) < n + 1 :=
    Nat.pow_pred_clog_lt_self 2 h1
  rw [← Nat.sub_add_cancel hpos, pow_succ']
  omega

/-- For every `n : ℕ`, `2 ^ ⌈log₂ (n + 1)⌉ ≤ max 1 (2 * n)`. -/
theorem two_pow_clog_succ_le_max (n : ℕ) :
    2 ^ Nat.clog 2 (n + 1) ≤ max 1 (2 * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (two_pow_clog_succ_le_two_mul hn).trans (le_max_right _ _)

/-- **Cube partition into `3`-codes** ([Sergeev2026UniqueDisjointness, §2, Lemma 1, p. 3]): for
`1 ≤ n`, the Boolean cube `Fin n → Bool` can be partitioned into `2 * n` pairwise-disjoint subsets
each having minimum Hamming distance at least `3`. -/
theorem exists_partition_minDist_three {n : ℕ} (hn : 1 ≤ n) :
    ∃ P : Fin (2 * n) → Set (Fin n → Bool),
      Pairwise (Disjoint on P) ∧ (⋃ i, P i) = Set.univ ∧ ∀ i, 3 ≤ minDist (P i) := by
  classical
  let e : BitString (Nat.clog 2 (n + 1)) ↪ Fin (2 * n) :=
    (BitString.equivFin (Nat.clog 2 (n + 1))).toEmbedding.trans
      (Fin.castLEEmb (two_pow_clog_succ_le_two_mul hn))
  let fib : BitString (Nat.clog 2 (n + 1)) → Set (Fin n → Bool) :=
    fun s => syndrome (hammingCheckMatrix n) ⁻¹' {s}
  refine ⟨Function.extend e fib fun _ => ∅, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : ∃ s, e s = i
    · obtain ⟨s₁, rfl⟩ := hi
      by_cases hj : ∃ s, e s = j
      · obtain ⟨s₂, rfl⟩ := hj
        have hs : s₁ ≠ s₂ := fun h => hij (congrArg e h)
        simp only [Function.onFun, e.injective.extend_apply, fib, Set.disjoint_left,
          Set.mem_preimage, Set.mem_singleton_iff]
        exact fun x hx1 hx2 => hs (hx1.symm.trans hx2)
      · simp only [Function.onFun, Function.extend_apply' _ _ _ hj, Set.disjoint_empty]
    · simp only [Function.onFun, Function.extend_apply' _ _ _ hi, Set.empty_disjoint]
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨e (syndrome (hammingCheckMatrix n) x),
      ?_⟩
    rw [e.injective.extend_apply]; exact rfl
  · intro i
    by_cases hi : ∃ s, e s = i
    · obtain ⟨s, rfl⟩ := hi
      rw [e.injective.extend_apply]
      exact three_le_minDist_hammingSyndrome_preimage n s
    · rw [Function.extend_apply' _ _ _ hi, minDist_empty]
      exact le_top

/-- Hamming syndrome of a subset `a` inside a finite ground set `S : Finset α`, obtained by
transporting the indicator of `a` on `S` along `S.equivFin`. -/
noncomputable def finsetHammingSyndrome {α : Type*} [DecidableEq α] (S a : Finset α) :
    BitString (Nat.clog 2 (S.card + 1)) :=
  syndrome (hammingCheckMatrix S.card) fun i => decide ((S.equivFin.symm i : α) ∈ a)

/-- Two distinct subsets `a, b ⊆ S` with the same `finsetHammingSyndrome S` differ on at least `3`
elements: `3 ≤ (symmDiff a b).card`. -/
theorem three_le_card_symmDiff_of_finsetHammingSyndrome_eq {α : Type*} [DecidableEq α]
    {S a b : Finset α} (ha : a ⊆ S) (hb : b ⊆ S) (hab : a ≠ b)
    (hsyn : finsetHammingSyndrome S a = finsetHammingSyndrome S b) :
    3 ≤ (symmDiff a b).card := by
  let va : Fin S.card → Bool := fun i => decide ((S.equivFin.symm i : α) ∈ a)
  let vb : Fin S.card → Bool := fun i => decide ((S.equivFin.symm i : α) ∈ b)
  have hvne : va ≠ vb := fun h => hab <| Finset.ext fun x => by
    by_cases hx : x ∈ S
    · have hi := congrFun h (S.equivFin ⟨x, hx⟩)
      simpa only [va, vb, Equiv.symm_apply_apply, Subtype.coe_mk, decide_eq_decide] using hi
    · exact iff_of_false (fun hxa => hx (ha hxa)) (fun hxb => hx (hb hxb))
  have hdist : 3 ≤ hammingDist va vb := by
    exact_mod_cast le_minDist_iff.1
      (three_le_minDist_hammingSyndrome_preimage S.card (finsetHammingSyndrome S a))
      va rfl vb hsyn.symm hvne
  have heq : hammingDist va vb = (symmDiff a b).card := by
    rw [hammingDist]
    refine Finset.card_bij (fun i _ => (S.equivFin.symm i : α))
      (fun i hi => ?_) (fun i₁ _ i₂ _ h => ?_) (fun x hx => ?_)
    · rw [Finset.mem_filter] at hi
      rw [Finset.mem_symmDiff]
      by_cases hia : (S.equivFin.symm i : α) ∈ a
      · exact Or.inl ⟨hia, fun hib => hi.2 (by simp only [va, vb, hia, hib])⟩
      · exact Or.inr ⟨Classical.byContradiction fun hib => hi.2 (by simp only [va, vb, hia, hib]),
          hia⟩
    · exact S.equivFin.symm.injective (Subtype.ext h)
    · have hxS : x ∈ S := (Finset.symmDiff_subset_union.trans (Finset.union_subset ha hb)) hx
      refine ⟨S.equivFin ⟨x, hxS⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simp only [va, vb, Equiv.symm_apply_apply, Subtype.coe_mk, ne_eq, decide_eq_decide]
        exact (Finset.mem_symmDiff.1 hx).elim (fun ⟨hxa, hxb⟩ h => hxb (h.1 hxa))
          fun ⟨hxb, hxa⟩ h => hxa (h.2 hxb)
      · simp only [Equiv.symm_apply_apply, Subtype.coe_mk]
  exact heq ▸ hdist

end Hamming

end Cslib.Code
