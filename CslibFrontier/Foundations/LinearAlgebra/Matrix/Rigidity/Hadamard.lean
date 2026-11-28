/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Rigidity of Hadamard and Sylvester–Hadamard matrices

An `n × n` Hadamard matrix `H` (`Matrix.IsHadamard`: entries of unit modulus satisfying
`H * Hᴴ = n • 1`, covering classical `±1` Hadamard matrices over rings with trivial `star` and
generalized complex Hadamard matrices such as discrete Fourier transform matrices over `ℂ`) has
rigidity at least `n ^ 2 / (4 r)` for every target rank `1 ≤ r` with `2 r ≤ n`
(`Matrix.IsHadamard.card_sq_le_four_mul_rigidity`, [Lokam2009], §3.2.1, Theorem 3.8, following
[deWolf2006], §3, Theorem 2).

The proof has two steps:

1. **Submatrix rank lower bound** (`Matrix.IsHadamard.card_mul_le_rank_submatrix`,
   [deWolf2006], §3, Theorem 1; [Lokam2009], §3.2, Lemma 3.6): every `a × b` submatrix `M` of `H`
   on distinct rows and distinct columns satisfies `a * b ≤ n * rank M`. For `G = M * Mᴴ`, unit
   entries give `tr G = a * b`, while embedding `M` into the `a × n` row submatrix of `H` bounds
   every eigenvalue of `G` by `n`, so the sum `a * b` of the nonzero eigenvalues of `G` is at most
   `rank M * n`. Because matrix rank over a field is invariant under scalar extensions
   (`Matrix.rank_map_of_field`), the same submatrix rank and rigidity bounds carry over from `ℝ`
   through `ℚ` to `±1` Hadamard matrices over any field of characteristic zero
   (`Matrix.IsHadamard.card_mul_le_rank_submatrix_of_trivialStar`,
   `Matrix.IsHadamard.card_sq_le_four_mul_rigidity_of_trivialStar`).
2. **Row averaging** (`card_sq_le_four_mul_rigidity_of_submatrix`): if `rank B ≤ r` and `2 r ≤ n`,
   the `2 r` rows of `H` with fewest changes contain at most `2 r · diffCount H B / n` changed
   columns in total. On those `2 r` rows and the `b` columns with no changes among them, `H` and
   `B` agree, so `2 r * b ≤ n * r`. For `1 ≤ r` this gives `2 b ≤ n`, hence at least `n / 2`
   changed columns in those `2 r` rows and `n ^ 2 ≤ 4 * r * diffCount H B`.

[Lokam2009], Theorem 3.8 omits the hypothesis `r ≤ n / 2` in its printed statement while selecting
`2 r` rows in the first line of its proof; [deWolf2006], §1.2 and §3, Theorem 2 states `r ≤ n / 2`
explicitly, and the bound fails for `2 r > n` (for example, changing a single entry of the `4 × 4`
Sylvester–Hadamard matrix drops its rank to `3`, so `R(3) = 1 < 4 ^ 2 / (4 · 3)`).

This module also defines the explicit `2 ^ k × 2 ^ k` Sylvester–Hadamard matrix
`Matrix.sylvesterHadamard R k` ([Lokam2009], §2.2, eq. (2.3); [Midrijanis2005], §1.3), proves its
Kronecker decomposition `Matrix.sylvesterHadamard_add_submatrix`, `IsHadamard` instance over any
commutative `*`-ring, and full rank `Matrix.rank_sylvesterHadamard_of_two_ne_zero` in
characteristic other than two, establishes Midrijānis's combinatorial block-tiling bound for
power-of-two target ranks `r = 2 ^ t` (`t < k`) over every field of characteristic other than two
(`Matrix.two_pow_le_four_mul_rigidity_sylvesterHadamard_two_pow`, [Lokam2009], §2.2, Theorem 2.11;
[Midrijanis2005], §2, Theorem 1), and deduces the general bound
`2 ^ (2 * k) ≤ 4 * r * (sylvesterHadamard K k).rigidity r` for all `1 ≤ r` with `2 * r ≤ 2 ^ k`
over every field of characteristic zero (`Matrix.two_pow_le_four_mul_rigidity_sylvesterHadamard`).

## Main definitions

* `Matrix.sylvesterHadamard R k`: the `2 ^ k × 2 ^ k` Sylvester–Hadamard matrix with `(i, j)`-entry
  `∏ t ∈ Finset.range k, if i.val.testBit t && j.val.testBit t then -1 else 1` (with interface
  lemmas `Matrix.sylvesterHadamard_apply`, `Matrix.sylvesterHadamard_apply_eq_one_or_neg_one`,
  `Matrix.sylvesterHadamard_zero`, `Matrix.sylvesterHadamard_one`,
  `Matrix.transpose_sylvesterHadamard`, and `Matrix.map_sylvesterHadamard`).

## Main results

* `Matrix.IsHadamard.rigidity_zero`: at target rank `0`, an `n × n` Hadamard matrix has rigidity
  `n ^ 2`.
* `Matrix.IsHadamard.rank_eq_card`: an `n × n` Hadamard matrix over a field with `(n : K) ≠ 0` has
  full rank `n`.
* `Matrix.IsHadamard.card_mul_le_rank_submatrix`,
  `Matrix.IsHadamard.card_mul_le_rank_submatrix_of_trivialStar`: every `a × b` submatrix of an
  `n × n` Hadamard matrix has `a * b ≤ n * rank`.
* `Matrix.IsHadamard.card_sq_le_four_mul_rigidity`,
  `Matrix.IsHadamard.card_sq_le_four_mul_rigidity_of_trivialStar`: every `n × n` Hadamard matrix
  satisfies `n ^ 2 ≤ 4 * r * H.rigidity r` for `1 ≤ r` and `2 * r ≤ n`.
* `Matrix.sylvesterHadamard_add_submatrix`: Kronecker decomposition of
  `sylvesterHadamard R (k₁ + k₂)`.
* `Matrix.isHadamard_sylvesterHadamard`: `sylvesterHadamard R k` is a Hadamard matrix over every
  commutative `*`-ring.
* `Matrix.rigidity_sylvesterHadamard_zero`: `(sylvesterHadamard K k).rigidity 0 = 2 ^ (2 * k)` over
  every field.
* `Matrix.rank_sylvesterHadamard_of_two_ne_zero`: `(sylvesterHadamard K k).rank = 2 ^ k` over any
  field with `(2 : K) ≠ 0`.
* `Matrix.two_pow_le_four_mul_rigidity_sylvesterHadamard_two_pow`: Midrijānis's bound
  `2 ^ (2 * k) ≤ 4 * 2 ^ t * (sylvesterHadamard K k).rigidity (2 ^ t)` for `t < k` over any field
  with `(2 : K) ≠ 0` ([Lokam2009], §2.2, Theorem 2.11; [Midrijanis2005], Theorem 1).
* `Matrix.two_pow_le_four_mul_rigidity_sylvesterHadamard`:
  `2 ^ (2 * k) ≤ 4 * r * (sylvesterHadamard K k).rigidity r` for `1 ≤ r` and `2 * r ≤ 2 ^ k` over
  any field of characteristic zero.

## References

* [R. de Wolf, *Lower Bounds on Matrix Rigidity via a Quantum Argument*][deWolf2006], §3,
  Theorems 1 and 2
* [S. V. Lokam, *Complexity Lower Bounds using Linear Algebra*][Lokam2009], §2.2, Theorem 2.11 and
  §3.2.1, Theorem 3.8
* [G. Midrijānis, *Three lines proof of the lower bound for the matrix rigidity*][Midrijanis2005],
  §2, Theorem 1
-/

public section

namespace Matrix

open Finset
open scoped Kronecker

/-! ### Averaging and submatrix-rank criterion for rigidity -/

/-- Among `N` natural-number weights `c`, some subset of `a ≤ N` indices has total weight at most
an `a / N` fraction of the full sum: `N * ∑ i ∈ I, c i ≤ a * ∑ i, c i`. -/
private theorem exists_card_eq_and_mul_sum_le {n : Type*} [Fintype n] (c : n → ℕ) {a : ℕ}
    (ha : a ≤ Fintype.card n) :
    ∃ I : Finset n, #I = a ∧ Fintype.card n * ∑ i ∈ I, c i ≤ a * ∑ i, c i := by
  classical
  set N := Fintype.card n
  let e : Fin N ≃ n := (Fintype.equivFin n).symm
  let σ : Equiv.Perm (Fin N) := Tuple.sort (c ∘ e)
  have hmono : Monotone (c ∘ e ∘ σ) := Tuple.monotone_sort (c ∘ e)
  let emb : Fin N ↪ n := σ.toEmbedding.trans e.toEmbedding
  let S : Finset (Fin N) := univ.filter fun k : Fin N => k.val < a
  let Sc : Finset (Fin N) := univ.filter fun k : Fin N => ¬k.val < a
  have hS_card : #S = a := Fin.card_filter_val_lt.trans (min_eq_right ha)
  have hSc_card : #Sc = N - a := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin N))) fun k => k.val < a
    rw [card_univ, Fintype.card_fin] at h
    change #S + #Sc = N at h
    omega
  let g : Fin N → ℕ := fun k => c (emb k)
  have hcross : (N - a) * ∑ x ∈ S, g x ≤ a * ∑ y ∈ Sc, g y := by
    rw [← hSc_card, ← hS_card]
    calc #Sc * ∑ x ∈ S, g x = ∑ x ∈ S, ∑ _y ∈ Sc, g x := by
          simp only [sum_const, smul_eq_mul, mul_sum]
      _ ≤ ∑ x ∈ S, ∑ y ∈ Sc, g y := sum_le_sum fun x hx => sum_le_sum fun y hy =>
          hmono (Fin.mk_le_mk.mpr ((mem_filter.mp hx).2.le.trans (not_lt.mp (mem_filter.mp hy).2)))
      _ = #S * ∑ y ∈ Sc, g y := by rw [sum_comm]; simp only [sum_const, smul_eq_mul, mul_sum]
  have htot : ∑ i : n, c i = ∑ x ∈ S, g x + ∑ y ∈ Sc, g y := by
    rw [sum_filter_add_sum_filter_not]
    exact (Fintype.sum_equiv (σ.trans e) _ _ fun _ => rfl).symm
  refine ⟨S.map emb, by rw [card_map, hS_card], ?_⟩
  rw [sum_map, htot]
  change N * ∑ x ∈ S, g x ≤ a * (∑ x ∈ S, g x + ∑ y ∈ Sc, g y)
  calc N * ∑ x ∈ S, g x = a * ∑ x ∈ S, g x + (N - a) * ∑ x ∈ S, g x := by
        rw [← add_mul, Nat.add_sub_of_le ha]
    _ ≤ a * (∑ x ∈ S, g x + ∑ y ∈ Sc, g y) := by rw [mul_add]; exact Nat.add_le_add_left hcross _

/-- Row-averaging reduction from a submatrix rank lower bound `#I * #J ≤ |n| * rank A_{I, J}` to
the rigidity lower bound `|n| ^ 2 ≤ 4 * r * A.rigidity r` ([deWolf2006], §3, Theorem 2;
[Lokam2009], §3.2.1, Theorem 3.8). -/
private theorem card_sq_le_four_mul_rigidity_of_submatrix {n K : Type*} [Fintype n] [Field K]
    {A : Matrix n n K}
    (hsub : ∀ I J : Finset n,
      #I * #J ≤ Fintype.card n * (A.submatrix (Subtype.val : I → n) (Subtype.val : J → n)).rank)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : 2 * r ≤ Fintype.card n) :
    Fintype.card n ^ 2 ≤ 4 * r * A.rigidity r := by
  classical
  obtain ⟨B, hB, hAB⟩ := exists_rigidity_eq A r
  rw [← hAB]
  set N := Fintype.card n
  let rowDiff (i : n) : ℕ := #(univ.filter fun j : n => A i j ≠ B i j)
  obtain ⟨I, hI, hIsum⟩ := exists_card_eq_and_mul_sum_le rowDiff hr
  rw [← diffCount_eq_sum A B] at hIsum
  let badCols : Finset n := I.biUnion fun i => univ.filter fun j : n => A i j ≠ B i j
  let J : Finset n := badColsᶜ
  have hN_bad : N * #badCols ≤ 2 * r * diffCount A B :=
    (Nat.mul_le_mul_left N card_biUnion_le).trans hIsum
  have hagree : A.submatrix (Subtype.val : I → n) (Subtype.val : J → n) =
      B.submatrix (Subtype.val : I → n) (Subtype.val : J → n) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    by_contra hne
    exact mem_compl.mp hj (mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨mem_univ j, hne⟩⟩)
  have hIJ : 2 * r * #J ≤ N * r := by
    calc 2 * r * #J = #I * #J := by rw [hI]
      _ ≤ N * (A.submatrix (Subtype.val : I → n) (Subtype.val : J → n)).rank := hsub I J
      _ ≤ N * r := by rw [hagree]; exact Nat.mul_le_mul_left N ((rank_submatrix_le B _ _).trans hB)
  have h2J : 2 * #J ≤ N := Nat.le_of_mul_le_mul_left (by linarith : r * (2 * #J) ≤ r * N) hr0
  have hJ_compl : #J + #badCols = N := by
    simpa only [J] using card_compl_add_card badCols
  have hN_le : N ≤ 2 * #badCols := by omega
  linarith [Nat.mul_le_mul_left N hN_le]

/-! ### General Hadamard matrices -/

/-- At target rank zero, every `n × n` Hadamard matrix over a field has rigidity `n ^ 2`, since all
of its entries are unitary and therefore nonzero. -/
theorem IsHadamard.rigidity_zero {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [StarRing K]
    {H : Matrix n n K} (hH : H.IsHadamard) :
    H.rigidity 0 = Fintype.card n ^ 2 := by
  classical
  have hne (p : n × n) : H p.1 p.2 ≠ 0 := fun h0 => by
    simpa only [h0, zero_mul, zero_ne_one] using (Unitary.mem_iff.mp (hH.apply_mem p.1 p.2)).2
  rw [Matrix.rigidity_zero, diffCount_eq_card_filter]
  have hfilt : (univ.filter fun p : n × n => H p.1 p.2 ≠ (0 : Matrix n n K) p.1 p.2) = univ :=
    filter_true_of_mem fun p _ => by simpa only [Matrix.zero_apply] using hne p
  rw [hfilt, card_univ, Fintype.card_prod, sq]

/-- Every `n × n` Hadamard matrix over a field in which `|n|` is nonzero has full rank `|n|`. -/
theorem IsHadamard.rank_eq_card {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [StarRing K]
    {H : Matrix n n K} (hH : H.IsHadamard) (hcard : (Fintype.card n : K) ≠ 0) :
    H.rank = Fintype.card n :=
  rank_of_isUnit H ((isUnit_iff_isUnit_det H).mpr (isUnit_iff_ne_zero.mpr (hH.det_ne_zero hcard)))

/-- Quadratic form of `X * Xᴴ` over `[RCLike K]` equals `∑ c, ‖(Xᴴ *ᵥ v) c‖ ^ 2`. -/
private theorem re_star_dotProduct_mul_conjTranspose_mulVec {α γ K : Type*}
    [Fintype α] [Fintype γ] [RCLike K] (X : Matrix α γ K) (v : α → K) :
    RCLike.re (star v ⬝ᵥ ((X * Xᴴ) *ᵥ v)) = ∑ c : γ, ‖(Xᴴ *ᵥ v) c‖ ^ 2 := by
  have hvec : star v ᵥ* X = star (Xᴴ *ᵥ v) := by
    ext c
    simp only [vecMul, mulVec, dotProduct, conjTranspose_apply, Pi.star_apply, star_sum, star_mul,
      star_star, mul_comm]
  have hdot : star v ⬝ᵥ ((X * Xᴴ) *ᵥ v) = star (Xᴴ *ᵥ v) ⬝ᵥ (Xᴴ *ᵥ v) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, hvec]
  rw [hdot]
  change RCLike.re (∑ c : γ, star ((Xᴴ *ᵥ v) c) * (Xᴴ *ᵥ v) c) = ∑ c : γ, ‖(Xᴴ *ᵥ v) c‖ ^ 2
  rw [map_sum]
  refine sum_congr rfl fun c _ => ?_
  simp only [RCLike.star_def]
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- **Submatrix rank bound for generalized Hadamard matrices** ([deWolf2006], §3, Theorem 1;
[Lokam2009], §3.2, Lemma 3.6). Every `|α| × |β|` submatrix of an `|n| × |n|` Hadamard matrix `H`
over `ℝ` or `ℂ` (`[RCLike K]`), on distinct rows and distinct columns, satisfies
`|α| * |β| ≤ |n| * rank (H.submatrix f g)`. -/
theorem IsHadamard.card_mul_le_rank_submatrix {n α β K : Type*} [Fintype n] [DecidableEq n]
    [Fintype α] [Fintype β] [RCLike K] {H : Matrix n n K} (hH : H.IsHadamard)
    {f : α → n} {g : β → n} (hf : Function.Injective f) (hg : Function.Injective g) :
    Fintype.card α * Fintype.card β ≤ Fintype.card n * (H.submatrix f g).rank := by
  classical
  open scoped ComplexOrder in
  let M : Matrix α β K := H.submatrix f g
  let R : Matrix α n K := H.submatrix f id
  let G : Matrix α α K := M * Mᴴ
  have hG : G.IsHermitian := isHermitian_mul_conjTranspose_self M
  have htr : G.trace = (Fintype.card α * Fintype.card β : ℕ) := by
    simp only [G, trace, diag_apply, Matrix.mul_apply, conjTranspose_apply, M, submatrix_apply]
    have hunit (a : α) (b : β) : H (f a) (g b) * star (H (f a) (g b)) = 1 :=
      Unitary.mem_iff_self_mul_star.mp (hH.apply_mem (f a) (g b))
    simp only [hunit, sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.cast_mul]
  have hRR : R * Rᴴ = (Fintype.card n : K) • (1 : Matrix α α K) := by
    ext a₁ a₂
    have h := congr_fun₂ hH.mul_conjTranspose (f a₁) (f a₂)
    simpa only [R, Matrix.mul_apply, conjTranspose_apply, submatrix_apply, id_eq,
      Matrix.smul_apply, Matrix.one_apply, hf.eq_iff] using h
  have heig_le (a : α) : hG.eigenvalues a ≤ Fintype.card n := by
    let v : α → K := (hG.eigenvectorBasis a).ofLp
    have hv_norm : RCLike.re (star v ⬝ᵥ v) = 1 := by
      have h1 : ‖hG.eigenvectorBasis a‖ = 1 := hG.eigenvectorBasis.orthonormal.1 a
      have h2 := EuclideanSpace.norm_sq_eq (hG.eigenvectorBasis a)
      rw [h1, one_pow] at h2
      rw [dotProduct, map_sum, h2]
      refine sum_congr rfl fun i _ => ?_
      simp only [Pi.star_apply, RCLike.star_def]
      rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    have hG_quad : RCLike.re (star v ⬝ᵥ ((M * Mᴴ) *ᵥ v)) = hG.eigenvalues a := by
      change RCLike.re (star v ⬝ᵥ (G *ᵥ v)) = hG.eigenvalues a
      rw [hG.mulVec_eigenvectorBasis a, dotProduct_smul, RCLike.real_smul_eq_coe_mul,
        RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, zero_mul, sub_zero, hv_norm, mul_one]
    have hR_quad : RCLike.re (star v ⬝ᵥ ((R * Rᴴ) *ᵥ v)) = Fintype.card n := by
      rw [hRR, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
        show (Fintype.card n : K) = ((Fintype.card n : ℝ) : K) from (RCLike.ofReal_natCast _).symm,
        RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, zero_mul, sub_zero, hv_norm, mul_one]
    have hMR_entry (b : β) : (Mᴴ *ᵥ v) b = (Rᴴ *ᵥ v) (g b) := by
      simp only [M, R, mulVec, dotProduct, conjTranspose_apply, submatrix_apply, id_eq]
    rw [← hG_quad, re_star_dotProduct_mul_conjTranspose_mulVec M v,
      ← hR_quad, re_star_dotProduct_mul_conjTranspose_mulVec R v]
    simp_rw [hMR_entry]
    exact (sum_map univ ⟨g, hg⟩ fun k => ‖(Rᴴ *ᵥ v) k‖ ^ 2).symm.trans_le
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _)
  let nz : Finset α := univ.filter fun a => hG.eigenvalues a ≠ 0
  have hrank_G : #nz = M.rank := by
    rw [← rank_self_mul_conjTranspose M, hG.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hsum : (Fintype.card α * Fintype.card β : ℝ) = ∑ a ∈ nz, hG.eigenvalues a := by
    have h1 := congrArg RCLike.re hG.trace_eq_sum_eigenvalues
    rw [htr, RCLike.natCast_re, map_sum] at h1
    simp only [RCLike.ofReal_re] at h1
    rw [← Finset.sum_filter_ne_zero] at h1
    exact_mod_cast h1
  have hbound : (Fintype.card α * Fintype.card β : ℝ) ≤ Fintype.card n * M.rank := by
    rw [hsum, ← hrank_G, mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun a _ => heig_le a
  exact_mod_cast hbound

/-- **Submatrix rank bound for `±1` Hadamard matrices in characteristic zero.** Over any field `K`
of characteristic zero with trivial `star` (such as `ℚ` or `ℝ`), every `|α| × |β|` submatrix of an
`|n| × |n|` Hadamard matrix `H`, on distinct rows and distinct columns, satisfies
`|α| * |β| ≤ |n| * rank (H.submatrix f g)`. -/
theorem IsHadamard.card_mul_le_rank_submatrix_of_trivialStar {n α β K : Type*} [Fintype n]
    [DecidableEq n] [Fintype α] [Fintype β] [Field K] [CharZero K] [StarRing K] [TrivialStar K]
    {H : Matrix n n K} (hH : H.IsHadamard) {f : α → n} {g : β → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Fintype.card α * Fintype.card β ≤ Fintype.card n * (H.submatrix f g).rank := by
  classical
  have hpm (i j : n) : H i j = 1 ∨ H i j = -1 :=
    Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j)
  have h1_ne_neg1 : (1 : K) ≠ -1 := by norm_num
  let H₀ : Matrix n n ℚ := of fun i j => if H i j = 1 then 1 else -1
  have hmap_K : H₀.map (Rat.castHom K) = H := by
    ext i j
    rcases hpm i j with h | h
    · simp only [H₀, of_apply, map_apply, h, ↓reduceIte, map_one]
    · simp only [H₀, of_apply, map_apply, h, h1_ne_neg1.symm, ↓reduceIte, map_neg, map_one]
  let H₁ : Matrix n n ℝ := H₀.map (Rat.castHom ℝ)
  have hconj_K : H₀ᴴ.map (Rat.castHom K) = Hᴴ := by
    ext i j; simp only [conjTranspose_apply, star_trivial, map_apply, ← hmap_K]
  have hconj_R : H₀ᴴ.map (Rat.castHom ℝ) = H₁ᴴ := by
    ext i j; simp only [H₁, conjTranspose_apply, star_trivial, map_apply]
  have hmul (X Y : Matrix n n ℚ)
      (hXY : X.map (Rat.castHom K) * Y.map (Rat.castHom K) = (Fintype.card n : K) • 1) :
      X.map (Rat.castHom ℝ) * Y.map (Rat.castHom ℝ) = (Fintype.card n : ℝ) • 1 := by
    have hQ : X * Y = (Fintype.card n : ℚ) • 1 := by
      ext i j
      apply (Rat.castHom K).injective
      have hm := congr_fun₂ hXY i j
      simp only [Matrix.mul_apply, map_sum, map_mul, map_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at hm ⊢
      rwa [apply_ite (Rat.castHom K), map_natCast, map_zero]
    ext i j
    have hm := congr_fun₂ (congrArg (fun M => M.map (Rat.castHom ℝ)) hQ) i j
    simp only [Matrix.mul_apply, map_sum, map_mul, map_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at hm ⊢
    rwa [apply_ite (Rat.castHom ℝ), map_natCast, map_zero] at hm
  have hH₁ : H₁.IsHadamard := by
    refine ⟨fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr ?_, ?_, ?_⟩
    · simp only [H₁, H₀, map_apply, of_apply]
      split_ifs <;> simp
    · rw [← hconj_R]
      exact hmul H₀ H₀ᴴ (by rw [hmap_K, hconj_K, hH.mul_conjTranspose])
    · rw [← hconj_R]
      exact hmul H₀ᴴ H₀ (by rw [hconj_K, hmap_K, hH.conjTranspose_mul])
  have hrank : (H.submatrix f g).rank = (H₁.submatrix f g).rank := by
    rw [show H.submatrix f g = (H₀.submatrix f g).map (Rat.castHom K) by rw [← hmap_K]; rfl,
      show H₁.submatrix f g = (H₀.submatrix f g).map (Rat.castHom ℝ) from rfl,
      rank_map_of_field, rank_map_of_field]
  rw [hrank]
  exact hH₁.card_mul_le_rank_submatrix hf hg

/-- **Rigidity lower bound for generalized Hadamard matrices** ([Lokam2009], §3.2.1, Theorem 3.8;
[deWolf2006], §3, Theorem 2). Every `|n| × |n|` Hadamard matrix `H` over `ℝ` or `ℂ` (`[RCLike K]`)
satisfies `|n| ^ 2 ≤ 4 * r * H.rigidity r` whenever `1 ≤ r` and `2 * r ≤ |n|`. -/
theorem IsHadamard.card_sq_le_four_mul_rigidity {n K : Type*} [Fintype n] [DecidableEq n]
    [RCLike K] {H : Matrix n n K} (hH : H.IsHadamard) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : 2 * r ≤ Fintype.card n) :
    Fintype.card n ^ 2 ≤ 4 * r * H.rigidity r :=
  card_sq_le_four_mul_rigidity_of_submatrix
    (fun I J => by
      have h := hH.card_mul_le_rank_submatrix
        (Subtype.val_injective (p := (· ∈ I))) (Subtype.val_injective (p := (· ∈ J)))
      simpa only [Fintype.card_coe] using h)
    hr0 hr

/-- **Rigidity lower bound for `±1` Hadamard matrices in characteristic zero** ([Lokam2009], §3.2.1,
Theorem 3.8; [deWolf2006], §3, Theorem 2). Over any field `K` of characteristic zero with trivial
`star` (such as `ℚ` or `ℝ`), every `|n| × |n|` Hadamard matrix `H` satisfies
`|n| ^ 2 ≤ 4 * r * H.rigidity r` whenever `1 ≤ r` and `2 * r ≤ |n|`. -/
theorem IsHadamard.card_sq_le_four_mul_rigidity_of_trivialStar {n K : Type*} [Fintype n]
    [DecidableEq n] [Field K] [CharZero K] [StarRing K] [TrivialStar K]
    {H : Matrix n n K} (hH : H.IsHadamard) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : 2 * r ≤ Fintype.card n) :
    Fintype.card n ^ 2 ≤ 4 * r * H.rigidity r :=
  card_sq_le_four_mul_rigidity_of_submatrix
    (fun I J => by
      have h := hH.card_mul_le_rank_submatrix_of_trivialStar
        (Subtype.val_injective (p := (· ∈ I))) (Subtype.val_injective (p := (· ∈ J)))
      simpa only [Fintype.card_coe] using h)
    hr0 hr

/-! ### Explicit `2 ^ k × 2 ^ k` Sylvester–Hadamard matrices -/

/-- The `2 ^ k × 2 ^ k` **Sylvester–Hadamard matrix** over `R` ([Lokam2009], §2.2, eq. (2.3);
[Midrijanis2005], §1.3), with `(i, j)`-entry `(-1)` raised to the bitwise inner product of `i` and
`j`: `∏ t ∈ Finset.range k, if i.val.testBit t && j.val.testBit t then -1 else 1`. -/
def sylvesterHadamard (R : Type*) [CommRing R] (k : ℕ) :
    Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R :=
  of fun i j => ∏ t ∈ range k, if i.val.testBit t && j.val.testBit t then -1 else 1

@[simp]
theorem sylvesterHadamard_apply (R : Type*) [CommRing R] (k : ℕ) (i j : Fin (2 ^ k)) :
    sylvesterHadamard R k i j =
      ∏ t ∈ range k, if i.val.testBit t && j.val.testBit t then -1 else 1 := by
  rfl

/-- Every entry of `sylvesterHadamard R k` is `1` or `-1`. -/
theorem sylvesterHadamard_apply_eq_one_or_neg_one (R : Type*) [CommRing R] (k : ℕ)
    (i j : Fin (2 ^ k)) :
    sylvesterHadamard R k i j = 1 ∨ sylvesterHadamard R k i j = -1 := by
  rw [sylvesterHadamard_apply]
  suffices ∀ m,
      (∏ t ∈ range m, if i.val.testBit t && j.val.testBit t then (-1 : R) else 1) = 1 ∨
        (∏ t ∈ range m, if i.val.testBit t && j.val.testBit t then (-1 : R) else 1) = -1 from
    this k
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [prod_range_succ]
      rcases ih with h | h <;> rw [h] <;>
        cases (i.val.testBit m && j.val.testBit m) <;> simp

@[simp]
theorem sylvesterHadamard_zero (R : Type*) [CommRing R] :
    sylvesterHadamard R 0 = 1 := by
  ext i j
  obtain rfl : i = j := Fin.ext (by omega)
  simp [sylvesterHadamard]

/-- For `k = 1`, `sylvesterHadamard R 1` is `!![1, 1; 1, -1]`. -/
theorem sylvesterHadamard_one (R : Type*) [CommRing R] :
    sylvesterHadamard R 1 = !![1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sylvesterHadamard]

@[simp]
theorem transpose_sylvesterHadamard (R : Type*) [CommRing R] (k : ℕ) :
    (sylvesterHadamard R k)ᵀ = sylvesterHadamard R k := by
  ext i j
  simp only [transpose_apply, sylvesterHadamard_apply]
  refine prod_congr rfl fun t _ => ?_
  rw [Bool.and_comm]

/-- Mapping `sylvesterHadamard R k` along a ring homomorphism changes its coefficient ring. -/
theorem map_sylvesterHadamard {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (k : ℕ) :
    (sylvesterHadamard R k).map f = sylvesterHadamard S k := by
  ext i j
  simp only [map_apply, sylvesterHadamard_apply, map_prod]
  refine prod_congr rfl fun t _ => ?_
  cases (i.val.testBit t && j.val.testBit t) <;> simp

/-- Reindexing `sylvesterHadamard R (k₁ + k₂)` by `(u, x) ↦ x + 2 ^ k₂ * u` decomposes it as the
Kronecker product `sylvesterHadamard R k₁ ⊗ₖ sylvesterHadamard R k₂`, recovering the recursive
Kronecker specification of Sylvester–Hadamard matrices. -/
theorem sylvesterHadamard_add_submatrix (R : Type*) [CommRing R] (k₁ k₂ : ℕ) :
    (sylvesterHadamard R (k₁ + k₂)).submatrix
      (finProdFinEquiv.trans (finCongr (pow_add 2 k₁ k₂).symm))
      (finProdFinEquiv.trans (finCongr (pow_add 2 k₁ k₂).symm)) =
      sylvesterHadamard R k₁ ⊗ₖ sylvesterHadamard R k₂ := by
  ext ⟨u, x⟩ ⟨v, y⟩
  simp only [submatrix_apply, Equiv.trans_apply, finCongr_apply, sylvesterHadamard_apply,
    kroneckerMap_apply, Fin.val_cast]
  let a : ℕ := (finProdFinEquiv (u, x)).val
  let b : ℕ := (finProdFinEquiv (v, y)).val
  have ha : a = 2 ^ k₂ * u.val + x.val := show x.val + 2 ^ k₂ * u.val = _ from Nat.add_comm _ _
  have hb : b = 2 ^ k₂ * v.val + y.val := show y.val + 2 ^ k₂ * v.val = _ from Nat.add_comm _ _
  change (∏ t ∈ range (k₁ + k₂), if a.testBit t && b.testBit t then (-1 : R) else 1) =
    (∏ t ∈ range k₁, if u.val.testBit t && v.val.testBit t then (-1 : R) else 1) *
      ∏ t ∈ range k₂, if x.val.testBit t && y.val.testBit t then (-1 : R) else 1
  rw [add_comm k₁ k₂, prod_range_add, mul_comm]
  congr 1
  · refine prod_congr rfl fun t _ => ?_
    have hlt : ¬ k₂ + t < k₂ := by omega
    rw [ha, hb, Nat.testBit_two_pow_mul_add u.val x.isLt, Nat.testBit_two_pow_mul_add v.val y.isLt,
      ite_eq_right hlt, ite_eq_right hlt, Nat.add_sub_cancel_left]
  · refine prod_congr rfl fun t ht => ?_
    rw [ha, hb, Nat.testBit_two_pow_mul_add u.val x.isLt, Nat.testBit_two_pow_mul_add v.val y.isLt,
      ite_eq_left (mem_range.mp ht), ite_eq_left (mem_range.mp ht)]

/-- `sylvesterHadamard R k` is a Hadamard matrix over every commutative `*`-ring. -/
theorem isHadamard_sylvesterHadamard (R : Type*) [CommRing R] [StarRing R] (k : ℕ) :
    (sylvesterHadamard R k).IsHadamard := by
  induction k with
  | zero =>
      have hij (i j : Fin (2 ^ 0)) : i = j := Fin.ext (by omega)
      refine ⟨fun i j => ?_, ?_, ?_⟩
      · rw [sylvesterHadamard_zero, hij i j]
        simp
      all_goals
        ext i j
        rw [hij i j]
        simp [sylvesterHadamard_zero]
  | succ k ih =>
      have h1 : (sylvesterHadamard R 1).IsHadamard := by
        refine ⟨fun i j => ?_, ?_, ?_⟩
        · rcases sylvesterHadamard_apply_eq_one_or_neg_one R 1 i j with h | h <;>
            rw [h] <;> simp [Unitary.mem_iff]
        all_goals
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_two, sylvesterHadamard_one] <;> ring
      have hk := h1.kronecker ih
      rw [← sylvesterHadamard_add_submatrix R 1 k, isHadamard_submatrix_equiv_iff] at hk
      rwa [add_comm 1 k] at hk

/-- At target rank zero, `sylvesterHadamard K k` has rigidity `2 ^ (2 * k)` over every field `K`
(including characteristic two, since every entry is `±1` and therefore nonzero). -/
@[simp]
theorem rigidity_sylvesterHadamard_zero (K : Type*) [Field K] (k : ℕ) :
    (sylvesterHadamard K k).rigidity 0 = 2 ^ (2 * k) := by
  let _ : StarRing K := starRingOfComm
  rw [(isHadamard_sylvesterHadamard K k).rigidity_zero, Fintype.card_fin, ← pow_mul, mul_comm k 2]

/-- `sylvesterHadamard K k` has full rank `2 ^ k` over any field `K` with `(2 : K) ≠ 0`. -/
theorem rank_sylvesterHadamard_of_two_ne_zero {K : Type*} [Field K] (hchar : (2 : K) ≠ 0)
    (k : ℕ) : (sylvesterHadamard K k).rank = 2 ^ k := by
  let _ : StarRing K := starRingOfComm
  have hcard : (Fintype.card (Fin (2 ^ k)) : K) ≠ 0 := by
    rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_ne_zero k hchar
  rw [(isHadamard_sylvesterHadamard K k).rank_eq_card hcard, Fintype.card_fin]

/-- **Midrijānis's Sylvester–Hadamard rigidity bound** ([Lokam2009], §2.2, Theorem 2.11;
[Midrijanis2005], §2, Theorem 1). Over any field `K` of characteristic other than two
(`(2 : K) ≠ 0`), for every power-of-two target rank `r = 2 ^ t` with `t < k` (`2 * r ≤ 2 ^ k`),
tiling `sylvesterHadamard K k` into `2 ^ (2 * (k - t - 1))` blocks equal to
`± sylvesterHadamard K (t + 1)` of full rank `2 ^ (t + 1)` gives
`2 ^ (2 * k) ≤ 4 * 2 ^ t * (sylvesterHadamard K k).rigidity (2 ^ t)`. -/
theorem two_pow_le_four_mul_rigidity_sylvesterHadamard_two_pow {K : Type*} [Field K]
    (hchar : (2 : K) ≠ 0) {k t : ℕ} (ht : t < k) :
    2 ^ (2 * k) ≤ 4 * 2 ^ t * (sylvesterHadamard K k).rigidity (2 ^ t) := by
  classical
  obtain ⟨k₁, rfl⟩ : ∃ k₁, k₁ + (t + 1) = k := ⟨k - (t + 1), Nat.sub_add_cancel ht⟩
  obtain ⟨B, hB, hAB⟩ := exists_rigidity_eq (sylvesterHadamard K (k₁ + (t + 1))) (2 ^ t)
  rw [← hAB]
  let e : Fin (2 ^ k₁) × Fin (2 ^ (t + 1)) ≃ Fin (2 ^ (k₁ + (t + 1))) :=
    finProdFinEquiv.trans (finCongr (pow_add 2 k₁ (t + 1)).symm)
  have hblock (u v : Fin (2 ^ k₁)) :
      (sylvesterHadamard K (k₁ + (t + 1))).submatrix (fun x => e (u, x)) (fun y => e (v, y)) =
        sylvesterHadamard K k₁ u v • sylvesterHadamard K (t + 1) := by
    ext x y
    have hsub := congr_fun₂ (sylvesterHadamard_add_submatrix K k₁ (t + 1)) (u, x) (v, y)
    simpa only [e, submatrix_apply, kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul] using hsub
  have htile_diff (u v : Fin (2 ^ k₁)) :
      2 ^ t ≤ diffCount
        ((sylvesterHadamard K (k₁ + (t + 1))).submatrix (fun x => e (u, x)) (fun y => e (v, y)))
        (B.submatrix (fun x => e (u, x)) (fun y => e (v, y))) := by
    let Stile :=
      (sylvesterHadamard K (k₁ + (t + 1))).submatrix (fun x => e (u, x)) (fun y => e (v, y))
    let Btile := B.submatrix (fun x => e (u, x)) (fun y => e (v, y))
    have hSrank : Stile.rank = 2 ^ (t + 1) := by
      change ((sylvesterHadamard K (k₁ + (t + 1))).submatrix _ _).rank = 2 ^ (t + 1)
      rw [hblock u v]
      rcases sylvesterHadamard_apply_eq_one_or_neg_one K k₁ u v with h1 | h1
      · rw [h1, one_smul, rank_sylvesterHadamard_of_two_ne_zero hchar]
      · rw [h1, neg_one_smul, rank_neg, rank_sylvesterHadamard_of_two_ne_zero hchar]
    have hBrank : Btile.rank ≤ 2 ^ t := (rank_submatrix_le B _ _).trans hB
    have hrd := rank_sub_diffCount_le_rank Stile Btile
    rw [hSrank] at hrd
    dsimp only [Stile, Btile] at hBrank hrd
    have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by ring
    omega
  have hpart : diffCount (sylvesterHadamard K (k₁ + (t + 1))) B =
      ∑ u : Fin (2 ^ k₁), ∑ v : Fin (2 ^ k₁),
        diffCount
          ((sylvesterHadamard K (k₁ + (t + 1))).submatrix (fun x => e (u, x)) (fun y => e (v, y)))
          (B.submatrix (fun x => e (u, x)) (fun y => e (v, y))) := by
    have hrow_card {m : Type} [Fintype m] (A' B' : Matrix m m K) :
        diffCount A' B' = ∑ i : m, ∑ j : m, if A' i j ≠ B' i j then 1 else 0 := by
      rw [diffCount_eq_sum]
      simp only [sum_boole, Nat.cast_id]
    rw [hrow_card, ← e.sum_comp, Fintype.sum_prod_type]
    simp_rw [← e.sum_comp, Fintype.sum_prod_type]
    exact sum_congr rfl fun u _ => by
      rw [sum_comm]; exact sum_congr rfl fun v _ => by rw [hrow_card]; rfl
  have hsum_le :
      (2 ^ k₁) * (2 ^ k₁) * 2 ^ t ≤ diffCount (sylvesterHadamard K (k₁ + (t + 1))) B := by
    rw [hpart]
    calc (2 ^ k₁) * (2 ^ k₁) * 2 ^ t
        = ∑ _u : Fin (2 ^ k₁), ∑ _v : Fin (2 ^ k₁), 2 ^ t := by
          simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]
      _ ≤ _ := sum_le_sum fun u _ => sum_le_sum fun v _ => htile_diff u v
  calc 2 ^ (2 * (k₁ + (t + 1))) = 4 * 2 ^ t * ((2 ^ k₁) * (2 ^ k₁) * 2 ^ t) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hsum_le

/-- **Rigidity lower bound for Sylvester–Hadamard matrices in characteristic zero**
([Lokam2009], §2.2, Theorem 2.11 and §3.2.1, Theorem 3.8; [deWolf2006], §3, Theorem 2). Over any
field `K` of characteristic zero (such as `ℚ`, `ℝ`, or `ℂ`), for every `1 ≤ r` with
`2 * r ≤ 2 ^ k`, `2 ^ (2 * k) ≤ 4 * r * (sylvesterHadamard K k).rigidity r`. -/
theorem two_pow_le_four_mul_rigidity_sylvesterHadamard (K : Type*) [Field K] [CharZero K]
    {k r : ℕ} (hr0 : 1 ≤ r) (hr : 2 * r ≤ 2 ^ k) :
    2 ^ (2 * k) ≤ 4 * r * (sylvesterHadamard K k).rigidity r := by
  let _ : StarRing K := starRingOfComm
  let _ : TrivialStar K := ⟨fun _ => rfl⟩
  have h := (isHadamard_sylvesterHadamard K k).card_sq_le_four_mul_rigidity_of_trivialStar
    hr0 (by simpa only [Fintype.card_fin] using hr)
  rwa [Fintype.card_fin, ← pow_mul, mul_comm k 2] at h

end Matrix
