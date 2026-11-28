/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.Code.HammingBound
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rigidity of random matrices over finite fields

Valiant [Valiant1977] observed that while every `n × n` matrix over a field has rigidity at most
`(n - r) ^ 2` (`Matrix.rigidity_le_sq_sub`), almost all matrices over a finite field come within a
logarithmic factor of this upper bound ([Lokam2009], §2.1, pp. 11–12). This module formalizes the
counting proof for `m × n` and `n × n` matrices over any finite field `K` of size `q = |K|`.

## Proof

1. **Counting low-rank matrices** (`Matrix.card_rank_le_mul_lt`). Every matrix `B` of rank at most
   `r ≤ |n|` has its row space contained in an `r`-dimensional subspace of `K ^ n`. Double-counting
   ordered `r`-frames (`card_linearIndependent`) shows that the number of `r`-dimensional subspaces
   of `K ^ n` is `∏_{i < r} (q ^ |n| - q ^ i) / ∏_{i < r} (q ^ r - q ^ i)`, which is strictly less
   than `4 q ^ (r (|n| - r))` because `∏_{k = 1}^r (1 - q ^ -k) > 1 / 4` for `q ≥ 2`. Each such
   subspace contains `(q ^ r) ^ |m|` matrices, leaving fewer than
   `4 q ^ (|m| |n| - (|m| - r) (|n| - r))` matrices of rank at most `r`.
2. **Union bound over Hamming balls** (`Matrix.card_rigidity_lt_mul_le`). A matrix `A` with
   `A.rigidity r < s` lies in the Hamming ball of radius `s - 1` around some matrix `B` of rank at
   most `r`, and each ball has `∑_{j < s} C(|m| |n|, j) (q - 1) ^ j` matrices
   (`Cslib.Code.card_filter_hammingDist_le_eq_sum`).
3. **Closed-form probability and existence bounds.** Bounding the ball volume by
   `(|m| |n| (q - 1) + 1) ^ (s - 1) ≤ q ^ ((⌊log_q (|m| |n|)⌋ + 2) (s - 1))` shows that whenever
   `(⌊log_q (|m| |n|)⌋ + 2) s + t ≤ (|m| - r) (|n| - r)`, more than a `1 - q ^ -t` fraction of all
   `m × n` matrices have rigidity at least `s` (`Matrix.one_sub_inv_pow_lt_card_le_rigidity_div`).
   Setting `t = 0` gives existence (`Matrix.exists_div_log_le_rigidity`), and setting
   `t = ⌊(|n| - r) ^ 2 / 2⌋` on square matrices gives rigidity at least
   `(|n| - r) ^ 2 / (4 ⌊log_q |n|⌋ + 6)` for a `> 1 - q ^ -⌊(|n| - r) ^ 2 / 2⌋` fraction of
   matrices (`Matrix.one_sub_inv_pow_lt_card_sq_div_log_le_rigidity`); this fraction tends to `1`
   whenever `|n| - r → ∞`, the integer floor is positive once
   `4 ⌊log_q |n|⌋ + 6 ≤ (|n| - r) ^ 2`, and for a fixed finite field `K` and `r ≤ (1 - ε) |n|`
   (fixed `ε > 0`) it has order `Ω((|n| - r) ^ 2 / log |n|)`. For fixed dimensions and large fields
   (`|K| > 4 · 2 ^ (|m| |n|)`), almost all matrices attain the exact upper bound
   `(|m| - r) (|n| - r)` (`Matrix.one_sub_lt_card_rigidity_eq_mul_sub_div`, original to this
   library).

## Main results

* `Matrix.card_rank_le_mul_lt`: counting step showing fewer than
  `4 q ^ (|m| |n| - (|m| - r) (|n| - r))` of the `m × n` matrices over `K` have rank at most `r`.
* `Matrix.card_rigidity_lt_mul_le`: Hamming-ball union-bound step on the number of `m × n` matrices
  with `A.rigidity r < s`.
* `Matrix.one_sub_inv_pow_lt_card_le_rigidity_div`: rectangular tail-bound step on the rigidity of a
  uniformly random `m × n` matrix over `K`.
* `Matrix.one_sub_inv_pow_lt_card_sq_div_log_le_rigidity`: random `n × n` matrices over `K` have
  rigidity at least `(|n| - r) ^ 2 / (4 ⌊log_q |n|⌋ + 6)` with probability
  `> 1 - q ^ -⌊(|n| - r) ^ 2 / 2⌋`, giving order `Ω((|n| - r) ^ 2 / log |n|)` for fixed `K` and
  `r ≤ (1 - ε) |n|` (`ε > 0`) ([Valiant1977]; [Lokam2009], §2.1, pp. 11–12).
* `Matrix.exists_div_log_le_rigidity`: existence corollary showing some `m × n` matrix over `K` has
  rigidity at least `(|m| - r) (|n| - r) / (⌊log_q (|m| |n|)⌋ + 2)`.
* `Matrix.one_sub_lt_card_rigidity_eq_mul_sub_div`: over large finite fields (original to this
  library), more than a `1 - 4 · 2 ^ (|m| |n|) / |K|` fraction of `m × n` matrices attain the exact
  maximum rigidity `(|m| - r) (|n| - r)`.

## References

* [S. V. Lokam, *Complexity Lower Bounds using Linear Algebra*][Lokam2009], §2.1, pp. 11–12
* [L. G. Valiant, *Graph-theoretic arguments in low-level complexity*][Valiant1977]
-/

public section

open Finset Module

namespace Matrix

section Helpers

/-- Strengthened induction for `∏_{k = 1}^r (1 - q ^ -k) > 1 / 4` when `q ≥ 2`:
`(q ^ (r - 1) + 1) ∏_{k = 1}^r q ^ k ≤ 4 q ^ (r - 1) ∏_{k = 1}^r (q ^ k - 1)`. -/
private theorem add_one_mul_prod_pow_le {q : ℕ} (hq : 2 ≤ q) :
    ∀ {r : ℕ}, 1 ≤ r →
      (q ^ (r - 1) + 1) * (∏ k ∈ range r, q ^ (k + 1)) ≤
        4 * q ^ (r - 1) * ∏ k ∈ range r, (q ^ (k + 1) - 1)
  | 0, h => absurd h (by decide)
  | 1, _ => by
    simp only [Nat.sub_self, pow_zero, range_one, prod_singleton, zero_add, pow_one]
    have h1 : 1 ≤ q := by omega
    zify [h1]
    linarith
  | r + 2, _ => by
    have hr : 1 ≤ r + 1 := Nat.succ_pos r
    have ih := add_one_mul_prod_pow_le hq hr
    rw [Nat.add_sub_cancel] at ih
    change (q ^ (r + 1) + 1) * (∏ k ∈ range (r + 2), q ^ (k + 1)) ≤
      4 * q ^ (r + 1) * ∏ k ∈ range (r + 2), (q ^ (k + 1) - 1)
    rw [prod_range_succ (n := r + 1), prod_range_succ (n := r + 1)]
    set P := ∏ k ∈ range (r + 1), (q ^ (k + 1) - 1)
    set Q := ∏ k ∈ range (r + 1), q ^ (k + 1)
    set a := q ^ r
    have ha : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
    have hqr : q ^ (r + 1) = a * q := pow_succ q r
    have hqr1 : q ^ (r + 2) = a * q * q := by rw [pow_succ, hqr]
    have hq2 : q + 2 ≤ q * q := by nlinarith
    have hstep : (q ^ (r + 1) + 1) * q ^ (r + 2) ≤ q * (a + 1) * (q ^ (r + 2) - 1) := by
      rw [hqr, hqr1, Nat.mul_sub_one]
      refine Nat.le_sub_of_add_le ?_
      have hcore : a * q + a + 1 ≤ a * (q * q) := by nlinarith
      nlinarith
    calc (q ^ (r + 1) + 1) * (Q * q ^ (r + 2))
        = Q * ((q ^ (r + 1) + 1) * q ^ (r + 2)) := by ring
      _ ≤ Q * (q * (a + 1) * (q ^ (r + 2) - 1)) := Nat.mul_le_mul_left _ hstep
      _ = q * ((a + 1) * Q) * (q ^ (r + 2) - 1) := by ring
      _ ≤ q * (4 * a * P) * (q ^ (r + 2) - 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ih)
      _ = 4 * q ^ (r + 1) * (P * (q ^ (r + 2) - 1)) := by rw [hqr]; ring

/-- For `q ≥ 2`, `(q ^ r) ^ r ≤ 4 * ∏_{i < r} (q ^ r - q ^ i)`. -/
private theorem pow_mul_le_four_mul_prod_sub {q : ℕ} (hq : 2 ≤ q) (r : ℕ) :
    (q ^ r) ^ r ≤ 4 * ∏ i : Fin r, (q ^ r - q ^ i.val) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hbase : (∏ k ∈ range r, q ^ (k + 1)) ≤ 4 * ∏ k ∈ range r, (q ^ (k + 1) - 1) :=
    Nat.le_of_mul_le_mul_left (((Nat.mul_le_mul_right _ (Nat.le_succ _)).trans
      (add_one_mul_prod_pow_le hq hr)).trans_eq (by ring)) (Nat.pow_pos (by omega : 0 < q))
  have hrev (f : ℕ → ℕ) : (∏ i : Fin r, f (r - i.val)) = ∏ k ∈ range r, f (k + 1) := by
    rw [← Equiv.prod_comp Fin.revPerm (fun i : Fin r => f (r - i.val)),
      ← Fin.prod_univ_eq_prod_range]
    exact prod_congr rfl fun i _ => by simp only [Fin.revPerm_apply, Fin.val_rev]; congr 1; omega
  have hsplit (i : Fin r) : q ^ r = q ^ i.val * q ^ (r - i.val) := by
    rw [← pow_add, Nat.add_sub_of_le i.isLt.le]
  calc (q ^ r) ^ r = (∏ i : Fin r, q ^ i.val) * ∏ i : Fin r, q ^ (r - i.val) := by
        rw [← prod_mul_distrib, ← Fin.prod_const]; exact prod_congr rfl fun i _ => hsplit i
    _ ≤ (∏ i : Fin r, q ^ i.val) * (4 * ∏ i : Fin r, (q ^ (r - i.val) - 1)) := by
        rw [hrev (q ^ ·), hrev (q ^ · - 1)]; exact Nat.mul_le_mul_left _ hbase
    _ = 4 * ∏ i : Fin r, (q ^ r - q ^ i.val) := by
        rw [mul_left_comm, ← prod_mul_distrib]
        exact congrArg (4 * ·) (prod_congr rfl fun i _ => by rw [Nat.mul_sub_one, ← hsplit])

/-- Every subspace of dimension at most `r ≤ finrank K V` is contained in an `r`-dimensional
subspace. -/
private theorem exists_submodule_le_finrank_eq {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (U : Submodule K V) {r : ℕ}
    (hU : finrank K U ≤ r) (hr : r ≤ finrank K V) :
    ∃ W : Submodule K V, U ≤ W ∧ finrank K W = r := by
  obtain ⟨U', hUU'⟩ := U.exists_isCompl
  have hsum := Submodule.finrank_add_eq_of_isCompl hUU'
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := U')
    (n := r - finrank K U) (by omega)
  let W' : Submodule K V := Submodule.map U'.subtype (Submodule.span K (Set.range f))
  have hdisj : Disjoint U W' := hUU'.disjoint.mono_right (Submodule.map_subtype_le U' _)
  have hW' : finrank K W' = r - finrank K U := by
    dsimp only [W']
    rw [Submodule.finrank_map_subtype_eq, finrank_span_eq_card hf, Fintype.card_fin]
  refine ⟨U ⊔ W', le_sup_left, ?_⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq U W'
  rw [hdisj.eq_bot, finrank_bot, add_zero, hW'] at hsup
  omega

/-- If `a + b = n` and `b k < x n` with `0 < k`, then `1 - x / k < a / n`. -/
private theorem one_sub_div_lt_div_of_add_eq {a b n k : ℕ} {x : ℝ} (hn : 0 < n) (hk : 0 < k)
    (hab : a + b = n) (hb : (b : ℝ) * k < x * n) : 1 - x / k < (a : ℝ) / n := by
  subst hab
  rw [lt_div_iff₀ (by exact_mod_cast hn), sub_mul, one_mul, sub_lt_comm, div_mul_eq_mul_div,
    lt_div_iff₀ (by exact_mod_cast hk)]
  simpa only [Nat.cast_add, add_sub_cancel_left] using hb

end Helpers

variable {m n K : Type*} [Fintype m] [Fintype n] [Field K] [Fintype K]

/-- Over a finite field `K` of size `q`, the number of `r`-dimensional subspaces of `K ^ n` is
strictly less than `4 q ^ (r (|n| - r))` whenever `r ≤ |n|`. -/
private theorem card_submodule_finrank_eq_lt {r : ℕ} (hr : r ≤ Fintype.card n) :
    Nat.card {W : Submodule K (n → K) // finrank K W = r} <
      4 * Fintype.card K ^ (r * (Fintype.card n - r)) := by
  classical
  have := Fintype.ofFinite (Submodule K (n → K))
  set q := Fintype.card K
  set N := Fintype.card n
  have hq : 2 ≤ q := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set S : Finset (Submodule K (n → K)) := {W | finrank K W = r}
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · refine (card_le_one.mpr fun a ha b hb => ?_).trans_lt (by simp)
    simp only [S, mem_filter, mem_univ, true_and, Submodule.finrank_eq_zero] at ha hb
    rw [ha, hb]
  let LI := {s : Fin r → n → K // LinearIndependent K s}
  have hLI_card : Fintype.card LI = ∏ i : Fin r, (q ^ N - q ^ i.val) := by
    rw [← Nat.card_eq_fintype_card, card_linearIndependent (K := K) (V := n → K)
      (by rwa [Module.finrank_fintype_fun_eq_card])]
    simp only [Module.finrank_fintype_fun_eq_card, q, N]
  let spanOf : LI → Submodule K (n → K) := fun s => Submodule.span K (Set.range s.val)
  have hmaps : ∀ s ∈ (univ : Finset LI), spanOf s ∈ S := fun s _ => by
    simp only [S, mem_filter, mem_univ, true_and, spanOf, finrank_span_eq_card s.property,
      Fintype.card_fin]
  have hfiber : ∀ W ∈ S, #{s : LI | spanOf s = W} = ∏ i : Fin r, (q ^ r - q ^ i.val) := by
    intro W hW
    have hWr : finrank K W = r := (mem_filter.mp hW).2
    let e : {s' : Fin r → W // LinearIndependent K s'} ≃ {s : LI // spanOf s = W} :=
      { toFun := fun s' =>
          ⟨⟨W.subtype ∘ s'.val, s'.property.map' W.subtype W.ker_subtype⟩, by
            apply Submodule.eq_of_le_of_finrank_eq
            · rw [Submodule.span_le]
              rintro _ ⟨i, rfl⟩
              exact (s'.val i).property
            · rw [finrank_span_eq_card (s'.property.map' W.subtype W.ker_subtype),
                Fintype.card_fin, hWr]⟩
        invFun := fun s =>
          ⟨fun i => ⟨s.val.val i, s.property.le (Submodule.subset_span ⟨i, rfl⟩)⟩,
            LinearIndependent.of_comp W.subtype s.val.property⟩
        left_inv := fun s' => Subtype.ext (funext fun _ => Subtype.ext rfl)
        right_inv := fun s => Subtype.ext (Subtype.ext (funext fun _ => rfl)) }
    rw [← Fintype.card_subtype, ← Fintype.card_congr e, ← Nat.card_eq_fintype_card,
      card_linearIndependent (K := K) (V := W) (by omega), hWr]
  have hprod_eq : #S * ∏ i : Fin r, (q ^ r - q ^ i.val) = ∏ i : Fin r, (q ^ N - q ^ i.val) := by
    have hsum := card_eq_sum_card_fiberwise hmaps
    simp only [card_univ, hLI_card] at hsum
    rw [hsum, sum_congr rfl hfiber, sum_const, smul_eq_mul]
  have hnum_lt : (∏ i : Fin r, (q ^ N - q ^ i.val)) < (q ^ N) ^ r :=
    (prod_lt_prod_of_nonempty₀ (fun i _ => Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by omega)
      (i.isLt.trans_le hr)))
      (fun i _ => Nat.sub_lt (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega)))
      ⟨⟨0, hr0⟩, mem_univ _⟩).trans_eq (Fin.prod_const r _)
  refine Nat.lt_of_mul_lt_mul_right ?_ (a := ∏ i : Fin r, (q ^ r - q ^ i.val))
  rw [hprod_eq]
  calc (∏ i : Fin r, (q ^ N - q ^ i.val))
      < (q ^ N) ^ r := hnum_lt
    _ = q ^ (r * (N - r)) * (q ^ r) ^ r := by
        rw [← pow_mul, ← pow_mul, ← pow_add, ← mul_add, Nat.sub_add_cancel hr, mul_comm]
    _ ≤ 4 * q ^ (r * (N - r)) * ∏ i : Fin r, (q ^ r - q ^ i.val) :=
        (Nat.mul_le_mul_left _ (pow_mul_le_four_mul_prod_sub hq r)).trans_eq (by ring)

section DecidableIndex

variable [DecidableEq m] [DecidableEq n]

omit [Field K] in
private theorem card_matrix_eq_pow :
    Fintype.card (Matrix m n K) = Fintype.card K ^ (Fintype.card m * Fintype.card n) := by
  change Fintype.card (m → n → K) = _
  rw [Fintype.card_fun, Fintype.card_fun, ← pow_mul, mul_comm]

/-- Counting step for finite-field rigidity bounds: over a finite field `K` of size `q`, fewer than
`4 q ^ (|m| |n| - (|m| - r) (|n| - r))` of the `q ^ (|m| |n|)` matrices of size `m × n` have rank
at most `r`. -/
theorem card_rank_le_mul_lt (r : ℕ) :
    #{B : Matrix m n K | B.rank ≤ r} *
        Fintype.card K ^ ((Fintype.card m - r) * (Fintype.card n - r)) <
      4 * Fintype.card K ^ (Fintype.card m * Fintype.card n) := by
  classical
  set q := Fintype.card K
  set M := Fintype.card m
  set N := Fintype.card n
  have hq : 2 ≤ q := Fintype.one_lt_card
  by_cases hMN : r ≤ M ∧ r ≤ N
  · obtain ⟨hrM, hrN⟩ := hMN
    have := Fintype.ofFinite (Submodule K (n → K))
    set S : Finset (Submodule K (n → K)) := {W | finrank K W = r}
    have hcov : ({B : Matrix m n K | B.rank ≤ r} : Finset _) ⊆
        S.biUnion fun W => {B : Matrix m n K | ∀ i, B.row i ∈ W} := by
      intro B hB
      rw [mem_filter, ← B.finrank_span_range_row] at hB
      obtain ⟨W, hUW, hW⟩ := exists_submodule_le_finrank_eq
        (Submodule.span K (Set.range B.row)) hB.2 (by rwa [Module.finrank_fintype_fun_eq_card])
      exact mem_biUnion.mpr ⟨W, mem_filter.mpr ⟨mem_univ _, hW⟩,
        mem_filter.mpr ⟨mem_univ _, fun i => hUW (Submodule.subset_span ⟨i, rfl⟩)⟩⟩
    have hWcard : ∀ W ∈ S, #{B : Matrix m n K | ∀ i, B.row i ∈ W} = q ^ (r * M) := by
      intro W hW
      let e : (m → W) ≃ {B : Matrix m n K // ∀ i, B.row i ∈ W} :=
        { toFun := fun f => ⟨of fun i j => (f i).val j, fun i => (f i).property⟩
          invFun := fun B => fun i => ⟨B.val.row i, B.property i⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => Subtype.ext rfl }
      rw [← Fintype.card_subtype, ← Fintype.card_congr e, Fintype.card_fun,
        Module.card_eq_pow_finrank (K := K) (V := W), (mem_filter.mp hW).2, ← pow_mul]
    have hSlt : #S < 4 * q ^ (r * (N - r)) := by
      have h := card_submodule_finrank_eq_lt (K := K) hrN
      rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    calc #{B : Matrix m n K | B.rank ≤ r} * q ^ ((M - r) * (N - r))
        ≤ #S * q ^ (r * M) * q ^ ((M - r) * (N - r)) := by
          refine Nat.mul_le_mul_right _ ((card_le_card hcov).trans (card_biUnion_le.trans_eq ?_))
          rw [sum_congr rfl hWcard, sum_const, smul_eq_mul]
      _ < 4 * q ^ (r * (N - r)) * q ^ (r * M) * q ^ ((M - r) * (N - r)) :=
          Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hSlt (Nat.pow_pos (by omega)))
            (Nat.pow_pos (by omega))
      _ = 4 * q ^ (M * N) := by
          rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
          congr 2
          have h1 : M - r + r = M := Nat.sub_add_cancel hrM
          have h2 : N - r + r = N := Nat.sub_add_cancel hrN
          nlinarith
  · have hzero : (M - r) * (N - r) = 0 := Nat.mul_eq_zero.mpr (by omega)
    rw [hzero, pow_zero, mul_one]
    calc #{B : Matrix m n K | B.rank ≤ r}
        ≤ Fintype.card (Matrix m n K) := card_le_univ _
      _ = q ^ (M * N) := card_matrix_eq_pow
      _ < 4 * q ^ (M * N) := by
          have : 0 < q ^ (M * N) := Nat.pow_pos (by omega)
          omega

/-- For a fixed `m × n` matrix `B` over a finite type `α` of size `q`, the number of matrices
differing from `B` in fewer than `s` entries is `∑_{j < s} C(|m| |n|, j) (q - 1) ^ j`. -/
private theorem card_diffCount_lt_eq_sum {α : Type*} [Fintype α] (B : Matrix m n α) (s : ℕ) :
    #{A : Matrix m n α | diffCount B A < s} =
      ∑ j ∈ range s, (Fintype.card m * Fintype.card n).choose j * (Fintype.card α - 1) ^ j := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  let e : Matrix m n α ≃ (m × n → α) :=
    (Equiv.curry m n α).symm
  have hhd : ∀ A : Matrix m n α, diffCount B A = hammingDist (e B) (e A) := fun A => by
    rw [diffCount_eq_card_filter]
    rfl
  have hbij : #{A : Matrix m n α | diffCount B A < s} =
      #{y : m × n → α | hammingDist (e B) y ≤ s - 1} := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    refine Fintype.card_congr (Equiv.subtypeEquiv e fun A => ?_)
    simp only [mem_filter, mem_univ, true_and, hhd A]
    omega
  rw [hbij, Cslib.Code.card_filter_hammingDist_le_eq_sum,
    show s - 1 + 1 = s by omega]
  refine sum_congr rfl fun j _ => ?_
  rw [Cslib.Code.card_filter_hammingDist_eq_choose_mul_pow (q := Fintype.card α) (fun _ => rfl),
    Fintype.card_prod]

/-- Strict version of `card_rigidity_lt_mul_le` when `1 ≤ s`. -/
private theorem card_rigidity_lt_mul_lt_of_pos {r s : ℕ} (hs : 1 ≤ s) :
    #{A : Matrix m n K | A.rigidity r < s} *
        Fintype.card K ^ ((Fintype.card m - r) * (Fintype.card n - r)) <
      4 * (∑ j ∈ range s,
          (Fintype.card m * Fintype.card n).choose j * (Fintype.card K - 1) ^ j) *
        Fintype.card K ^ (Fintype.card m * Fintype.card n) := by
  classical
  set V := ∑ j ∈ range s,
    (Fintype.card m * Fintype.card n).choose j * (Fintype.card K - 1) ^ j
  have hVpos : 0 < V := sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, mem_range.mpr hs, by simp⟩
  have hcov : ({A : Matrix m n K | A.rigidity r < s} : Finset _) ⊆
      ({B : Matrix m n K | B.rank ≤ r} : Finset _).biUnion
        fun B => {A : Matrix m n K | diffCount B A < s} := by
    intro A hA
    obtain ⟨B, hBr, hAB⟩ := exists_rigidity_eq A r
    refine mem_biUnion.mpr ⟨B, mem_filter.mpr ⟨mem_univ _, hBr⟩,
      mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    rw [diffCount_comm, hAB]
    exact (mem_filter.mp hA).2
  have hcard : #{A : Matrix m n K | A.rigidity r < s} ≤
      #{B : Matrix m n K | B.rank ≤ r} * V := by
    calc #{A : Matrix m n K | A.rigidity r < s}
        ≤ ∑ B ∈ {B : Matrix m n K | B.rank ≤ r}, #{A : Matrix m n K | diffCount B A < s} :=
          (card_le_card hcov).trans card_biUnion_le
      _ = #{B : Matrix m n K | B.rank ≤ r} * V := by
          rw [sum_congr rfl fun B _ => card_diffCount_lt_eq_sum B s, sum_const, smul_eq_mul]
  calc _ ≤ #{B : Matrix m n K | B.rank ≤ r} * V *
          Fintype.card K ^ ((Fintype.card m - r) * (Fintype.card n - r)) := by gcongr
    _ = V * (#{B : Matrix m n K | B.rank ≤ r} *
          Fintype.card K ^ ((Fintype.card m - r) * (Fintype.card n - r))) := by ring
    _ < V * (4 * Fintype.card K ^ (Fintype.card m * Fintype.card n)) :=
        Nat.mul_lt_mul_of_pos_left (card_rank_le_mul_lt r) hVpos
    _ = 4 * V * Fintype.card K ^ (Fintype.card m * Fintype.card n) := by ring

/-- Hamming-ball union-bound step for finite-field random-matrix rigidity (after [Lokam2009], §2.1,
pp. 11–12): a matrix of rigidity less than `s` at target rank `r` lies within Hamming distance
`s - 1` of some matrix of rank at most `r`, so combining `Matrix.card_rank_le_mul_lt` with the
volume of a Hamming ball bounds the number of such matrices. -/
theorem card_rigidity_lt_mul_le (r s : ℕ) :
    #{A : Matrix m n K | A.rigidity r < s} *
        Fintype.card K ^ ((Fintype.card m - r) * (Fintype.card n - r)) ≤
      4 * (∑ j ∈ range s,
          (Fintype.card m * Fintype.card n).choose j * (Fintype.card K - 1) ^ j) *
        Fintype.card K ^ (Fintype.card m * Fintype.card n) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · exact (card_rigidity_lt_mul_lt_of_pos hs).le

/-- Natural-number tail bound underlying the probability and existence theorems: if
`(⌊log_q (|m| |n|)⌋ + 2) s + t ≤ (|m| - r) (|n| - r)`, strictly fewer than a `q ^ -t` fraction of
`m × n` matrices over `K` have rigidity less than `s`. -/
private theorem card_rigidity_lt_mul_pow_lt {r s t : ℕ}
    (h : (Nat.log (Fintype.card K) (Fintype.card m * Fintype.card n) + 2) * s + t ≤
      (Fintype.card m - r) * (Fintype.card n - r)) :
    #{A : Matrix m n K | A.rigidity r < s} * Fintype.card K ^ t <
      Fintype.card (Matrix m n K) := by
  set q := Fintype.card K
  set M := Fintype.card m
  set N := Fintype.card n
  set L := Nat.log q (M * N) + 2
  have hq : 2 ≤ q := Fintype.one_lt_card
  rw [card_matrix_eq_pow]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rw [filter_false_of_mem fun A _ => Nat.not_lt_zero (A.rigidity r), card_empty, zero_mul]
    exact Nat.pow_pos (by omega)
  -- Bound the Hamming ball of radius `s - 1` by `(M N (q - 1) + 1) ^ (s - 1) ≤ q ^ (L (s - 1))`.
  have hbase : M * N * (q - 1) + 1 ≤ q ^ L := by
    have hle : M * N ≤ q ^ (Nat.log q (M * N) + 1) - 1 :=
      Nat.le_sub_one_of_lt (Nat.lt_pow_succ_log_self (by omega) (M * N))
    have hpos : 1 ≤ q ^ (Nat.log q (M * N) + 1) := Nat.one_le_pow _ _ (by omega)
    calc M * N * (q - 1) + 1
        ≤ (q ^ (Nat.log q (M * N) + 1) - 1) * (q - 1) + 1 := by gcongr
      _ ≤ q ^ (Nat.log q (M * N) + 1) * q := by
          zify [hpos, (by omega : 1 ≤ q)]
          nlinarith
      _ = q ^ L := by rw [← pow_succ]
  have hV : (∑ j ∈ range s, (M * N).choose j * (q - 1) ^ j) ≤ q ^ (L * (s - 1)) := by
    classical
    have h0 : #{y : m × n → K | hammingDist (0 : m × n → K) y ≤ s - 1} ≤
        (Fintype.card (m × n) * (q - 1) + 1) ^ (s - 1) :=
      Cslib.Code.card_filter_hammingDist_le_le_pow (fun _ => rfl) 0 (s - 1)
    rw [Cslib.Code.card_filter_hammingDist_le_eq_sum, show s - 1 + 1 = s by omega,
      sum_congr rfl fun j _ =>
        Cslib.Code.card_filter_hammingDist_eq_choose_mul_pow (fun _ => rfl) 0 j,
      Fintype.card_prod] at h0
    exact h0.trans ((Nat.pow_le_pow_left hbase _).trans_eq (pow_mul q L (s - 1)).symm)
  have h4 : 4 ≤ q ^ 2 := by nlinarith
  have hexp : 2 + L * (s - 1) + t ≤ (M - r) * (N - r) := by
    have hL : 2 ≤ L := by omega
    have hLs : L * (s - 1) + L = L * s := by
      rw [← mul_add_one, Nat.sub_add_cancel (by omega : 1 ≤ s)]
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hexp
  have hmain := card_rigidity_lt_mul_lt_of_pos (m := m) (n := n) (K := K) (r := r) hs
  have hscale :
      #{A : Matrix m n K | A.rigidity r < s} * q ^ t * q ^ (2 + L * (s - 1) + d) <
        q ^ (M * N) * q ^ (2 + L * (s - 1) + d) := by
    calc #{A : Matrix m n K | A.rigidity r < s} * q ^ t * q ^ (2 + L * (s - 1) + d)
        = #{A : Matrix m n K | A.rigidity r < s} * q ^ ((M - r) * (N - r)) := by
          rw [mul_assoc, ← pow_add, hd]
          ring_nf
      _ < 4 * (∑ j ∈ range s, (M * N).choose j * (q - 1) ^ j) * q ^ (M * N) := hmain
      _ ≤ q ^ 2 * q ^ (L * (s - 1)) * q ^ (M * N) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul h4 hV)
      _ ≤ q ^ 2 * q ^ (L * (s - 1)) * q ^ (M * N) * q ^ d :=
          Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
      _ = q ^ (M * N) * q ^ (2 + L * (s - 1) + d) := by
          rw [← pow_add, ← pow_add]
          ring_nf
  exact Nat.lt_of_mul_lt_mul_right hscale

/-- Rectangular tail-bound step for `Matrix.one_sub_inv_pow_lt_card_sq_div_log_le_rigidity` (after
[Lokam2009], §2.1, pp. 11–12): over a finite field `K` of size `q`, whenever
`(⌊log_q (|m| |n|)⌋ + 2) s + t ≤ (|m| - r) (|n| - r)`, strictly more than a `1 - q ^ -t` fraction
of all `m × n` matrices have rigidity at least `s` at target rank `r`. -/
theorem one_sub_inv_pow_lt_card_le_rigidity_div {r s t : ℕ}
    (h : (Nat.log (Fintype.card K) (Fintype.card m * Fintype.card n) + 2) * s + t ≤
      (Fintype.card m - r) * (Fintype.card n - r)) :
    1 - ((Fintype.card K : ℝ)⁻¹) ^ t <
      (#{A : Matrix m n K | s ≤ A.rigidity r} : ℝ) / Fintype.card (Matrix m n K) := by
  rw [inv_pow, ← one_div, ← Nat.cast_pow]
  refine one_sub_div_lt_div_of_add_eq (b := #{A : Matrix m n K | A.rigidity r < s})
    Fintype.card_pos (Nat.pow_pos Fintype.card_pos) ?_ ?_
  · simpa only [not_le, card_univ] using card_filter_add_card_filter_not
      (s := (univ : Finset (Matrix m n K))) fun A => s ≤ A.rigidity r
  · rw [one_mul]
    exact_mod_cast card_rigidity_lt_mul_pow_lt h

/-- Over a large finite field `K` (original to this library), strictly more than a
`1 - 4 · 2 ^ (|m| |n|) / |K|` fraction of all `m × n` matrices attain the maximum possible
rigidity `(|m| - r) (|n| - r)`. In particular, when `4 · 2 ^ (|m| |n|) ≤ |K|`, some `m × n`
matrix has rigidity `(|m| - r) (|n| - r)`. -/
theorem one_sub_lt_card_rigidity_eq_mul_sub_div (r : ℕ) :
    1 - 4 * (2 : ℝ) ^ (Fintype.card m * Fintype.card n) / Fintype.card K <
      (#{A : Matrix m n K |
          A.rigidity r = (Fintype.card m - r) * (Fintype.card n - r)} : ℝ) /
        Fintype.card (Matrix m n K) := by
  set q := Fintype.card K
  set M := Fintype.card m
  set N := Fintype.card n
  set s := (M - r) * (N - r)
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hbad : #{A : Matrix m n K | A.rigidity r ≠ s} * q <
      4 * 2 ^ (M * N) * Fintype.card (Matrix m n K) := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs
    · rw [filter_false_of_mem (p := fun A : Matrix m n K => A.rigidity r ≠ s) fun A _ hne =>
        hne ((Nat.eq_zero_of_le_zero ((A.rigidity_le_mul_sub r).trans_eq hs0)).trans hs0.symm),
        card_empty, zero_mul]
      exact Nat.mul_pos (by positivity) Fintype.card_pos
    have heq_set : #{A : Matrix m n K | A.rigidity r ≠ s} =
        #{A : Matrix m n K | A.rigidity r < s} := by
      congr 1
      exact filter_congr fun A _ => by have : A.rigidity r ≤ s := A.rigidity_le_mul_sub r; omega
    rw [heq_set, card_matrix_eq_pow]
    have hsMN : s ≤ M * N := Nat.mul_le_mul (Nat.sub_le M r) (Nat.sub_le N r)
    have hV : (∑ j ∈ range s, (M * N).choose j * (q - 1) ^ j) ≤
        2 ^ (M * N) * q ^ (s - 1) := by
      calc (∑ j ∈ range s, (M * N).choose j * (q - 1) ^ j)
          ≤ ∑ j ∈ range s, (M * N).choose j * q ^ (s - 1) := by
            gcongr with j hj
            all_goals first | exact Nat.le_sub_one_of_lt (mem_range.mp hj) | omega
        _ ≤ (∑ j ∈ range (M * N + 1), (M * N).choose j) * q ^ (s - 1) := by
            rw [← sum_mul]
            gcongr
            omega
        _ = 2 ^ (M * N) * q ^ (s - 1) := by rw [Nat.sum_range_choose]
    have hmain := card_rigidity_lt_mul_lt_of_pos (m := m) (n := n) (K := K) (r := r) hs
    have hscale :
        #{A : Matrix m n K | A.rigidity r < s} * q * q ^ (s - 1) <
          4 * 2 ^ (M * N) * q ^ (M * N) * q ^ (s - 1) := by
      calc #{A : Matrix m n K | A.rigidity r < s} * q * q ^ (s - 1)
          = #{A : Matrix m n K | A.rigidity r < s} * q ^ s := by
            rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hs]
        _ < 4 * (∑ j ∈ range s, (M * N).choose j * (q - 1) ^ j) * q ^ (M * N) := hmain
        _ ≤ 4 * (2 ^ (M * N) * q ^ (s - 1)) * q ^ (M * N) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hV)
        _ = 4 * 2 ^ (M * N) * q ^ (M * N) * q ^ (s - 1) := by ring
    exact Nat.lt_of_mul_lt_mul_right hscale
  refine one_sub_div_lt_div_of_add_eq (b := #{A : Matrix m n K | A.rigidity r ≠ s})
    Fintype.card_pos (by omega) ?_ (by exact_mod_cast hbad)
  simpa only [card_univ] using card_filter_add_card_filter_not
    (s := (univ : Finset (Matrix m n K))) fun A => A.rigidity r = s

end DecidableIndex

/-- **Random square matrices over a finite field are nearly maximally rigid** ([Valiant1977];
[Lokam2009], §2.1, pp. 11–12). Over a finite field `K` of size `q`, strictly more than a
`1 - q ^ -⌊(|n| - r) ^ 2 / 2⌋` fraction of all `n × n` matrices have rigidity at least
`(|n| - r) ^ 2 / (4 ⌊log_q |n|⌋ + 6)`. The fraction tends to `1` whenever `|n| - r → ∞`; the
integer floor is positive once `4 ⌊log_q |n|⌋ + 6 ≤ (|n| - r) ^ 2`, and for a fixed finite field
`K` and `r ≤ (1 - ε) |n|` (fixed `ε > 0`) has order `Ω((|n| - r) ^ 2 / log |n|)`. -/
theorem one_sub_inv_pow_lt_card_sq_div_log_le_rigidity [DecidableEq n] (r : ℕ) :
    1 - ((Fintype.card K : ℝ)⁻¹) ^ ((Fintype.card n - r) ^ 2 / 2) <
      (#{A : Matrix n n K |
          (Fintype.card n - r) ^ 2 / (4 * Nat.log (Fintype.card K) (Fintype.card n) + 6) ≤
            A.rigidity r} : ℝ) /
        Fintype.card (Matrix n n K) := by
  set q := Fintype.card K
  set N := Fintype.card n
  have hq : 1 < q := Fintype.one_lt_card
  have hlog : Nat.log q (N * N) + 2 ≤ 2 * Nat.log q N + 3 := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · simp [hN0]
    have hlt : N < q ^ (Nat.log q N + 1) := Nat.lt_pow_succ_log_self hq N
    have hsq : N * N < q ^ (2 * Nat.log q N + 2) := (Nat.mul_lt_mul'' hlt hlt).trans_eq (by ring)
    have hle : Nat.log q (N * N) < 2 * Nat.log q N + 2 :=
      (Nat.log_lt_iff_lt_pow hq (Nat.mul_pos hNpos hNpos).ne').2 hsq
    omega
  refine one_sub_inv_pow_lt_card_le_rigidity_div ?_
  set X := (N - r) ^ 2
  set L' := 2 * Nat.log q N + 3
  have hdiv : X / (4 * Nat.log q N + 6) = X / 2 / L' := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    dsimp only [L']
    ring
  rw [hdiv]
  calc (Nat.log q (N * N) + 2) * (X / 2 / L') + X / 2
      ≤ L' * (X / 2 / L') + X / 2 := Nat.add_le_add_right (Nat.mul_le_mul_right _ hlog) _
    _ ≤ X / 2 + X / 2 := Nat.add_le_add_right (Nat.mul_div_le _ _) _
    _ = 2 * (X / 2) := (two_mul _).symm
    _ ≤ X := Nat.mul_div_le X 2
    _ = (N - r) * (N - r) := sq (N - r)

/-- Existence corollary of the finite-field counting step (after [Lokam2009], §2.1, pp. 11–12):
for every finite field `K`, dimensions `m, n`, and target rank `r`, some `m × n` matrix over `K`
has rigidity at least `(|m| - r) (|n| - r) / (⌊log_{|K|} (|m| |n|)⌋ + 2)`. -/
theorem exists_div_log_le_rigidity (r : ℕ) :
    ∃ A : Matrix m n K,
      (Fintype.card m - r) * (Fintype.card n - r) /
          (Nat.log (Fintype.card K) (Fintype.card m * Fintype.card n) + 2) ≤
        A.rigidity r := by
  classical
  set L := Nat.log (Fintype.card K) (Fintype.card m * Fintype.card n) + 2
  set s := (Fintype.card m - r) * (Fintype.card n - r) / L
  have hbad := card_rigidity_lt_mul_pow_lt (m := m) (n := n) (K := K) (r := r) (s := s) (t := 0)
    (by simpa only [add_zero] using Nat.mul_div_le ((Fintype.card m - r) * (Fintype.card n - r)) L)
  rw [pow_zero, mul_one, ← card_univ] at hbad
  obtain ⟨A, -, hA⟩ := exists_mem_notMem_of_card_lt_card hbad
  exact ⟨A, not_lt.mp fun hlt => hA (mem_filter.mpr ⟨mem_univ _, hlt⟩)⟩

end Matrix
