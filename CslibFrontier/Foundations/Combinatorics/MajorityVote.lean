/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Combinatorics.FiniteCover.Basic
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Majority votes

If at least two thirds of the elements of a finite type `Ω` are *good*, then among the tuples
of `2 r` elements of `Ω`, those in which at most half of the entries are good make up at most an
`(8 / 9) ^ r` fraction. This is the error bound for repeating a bounded-error test `2 r` times
independently and taking the majority answer, in counting form.

The proof is the exponential-moment (Chernoff) argument with weight `2` on the bad elements: the
weights of all tuples sum to `(|good| + 2 |bad|) ^ (2 r) ≤ (4 |Ω| / 3) ^ (2 r)`, and a tuple with
at most `r` good entries has weight at least `2 ^ r`.

## Main results

* `Cslib.card_filter_card_filter_le_le`: the bound.
* `Cslib.exists_forall_lt_card_filter_mem`: for a family of at most `2 ^ n` tests, each passed by
  two thirds of `Ω`, some `12 (n + 1)` elements of `Ω` contain a majority passing each test.
* `Cslib.exists_forall_exists_apply_mem`: for a family of at most `2 ^ n` tests, each passed by
  half of `Ω`, some `n + 1` elements of `Ω` contain one passing each test; this is the exact
  finite-cover union bound with failure ratio `1 / 2`.
* `Cslib.two_pow_mul_eight_pow_lt`: the numeric bound `2 ^ n * 8 ^ (6 n + 6) < 9 ^ (6 n + 6)`
  behind the choice of `12 (n + 1)` repetitions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.4][AroraBarak09]
-/

public section

namespace Cslib

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Bernoulli's bound for a power of `1 - x`**: `(1 - x) ^ r ≤ 1 / (1 + r x)` for `0 ≤ x ≤ 1`,
since `(1 - x) ^ r (1 + x) ^ r = (1 - x ^ 2) ^ r ≤ 1` and `1 + r x ≤ (1 + x) ^ r`. -/
theorem one_sub_pow_mul_one_add_mul_le_one {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (r : ℕ) :
    (1 - x) ^ r * (1 + r * x) ≤ 1 := by
  calc (1 - x) ^ r * (1 + r * x) ≤ (1 - x) ^ r * (1 + x) ^ r :=
        mul_le_mul_of_nonneg_left (one_add_mul_le_pow (by linarith) r)
          (pow_nonneg (by linarith) r)
    _ = (1 - x ^ 2) ^ r := by rw [← mul_pow]; ring
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

/-- **Majority votes at any advantage.** If at least half of `Ω` lies in `G`, then at most
`(4 |G| |Ω \ G|) ^ r` of the `2 r`-tuples of elements of `Ω` have at most `r` entries in `G`. When
`G` has density `1 / 2 + δ`, this is an at most `(1 - 4 δ ^ 2) ^ r` fraction.

The proof is the exponential-moment argument with weight `|Ω \ G|` on the elements of `G` and
weight `|G|` on the others: the weights of all tuples sum to `(2 |G| |Ω \ G|) ^ (2 r)`, and a tuple
with at most `r` entries in `G` has weight at least `(|G| |Ω \ G|) ^ r`. -/
theorem card_filter_card_filter_le_le_pow (G : Finset Ω) (hG : Fintype.card Ω ≤ 2 * G.card)
    (r : ℕ) :
    (univ.filter fun ω : Fin (2 * r) → Ω => (univ.filter fun i => ω i ∈ G).card ≤ r).card ≤
      (4 * G.card * (Fintype.card Ω - G.card)) ^ r := by
  set N := Fintype.card Ω
  set g := G.card
  set b := N - g
  set bad := univ.filter fun ω : Fin (2 * r) → Ω => (univ.filter fun i => ω i ∈ G).card ≤ r
  have hgN : g ≤ N := card_le_univ G
  have hbg : b ≤ g := by omega
  rcases Nat.eq_zero_or_pos b with hb | hb
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa using card_le_univ bad
    · simp [bad, eq_univ_of_card G (by omega), show ¬2 * r ≤ r by omega]
  have hg : 0 < g := lt_of_lt_of_le hb hbg
  let w : Ω → ℕ := fun a => if a ∈ G then b else g
  -- the weights of all tuples sum to `(2 g b) ^ (2 r)`
  have hsum : ∑ ω : Fin (2 * r) → Ω, ∏ i, w (ω i) = (2 * g * b) ^ (2 * r) := by
    rw [← Fintype.sum_pow (f := w)]
    congr 1
    simp only [w, sum_ite, sum_const, smul_eq_mul, filter_mem_eq_inter, univ_inter, filter_not,
      ← compl_eq_univ_sdiff, card_compl]
    ring
  -- a bad tuple has weight at least `(g b) ^ r`
  have hweight : ∀ ω ∈ bad, (g * b) ^ r ≤ ∏ i, w (ω i) := fun ω hω => by
    have hk := (mem_filter.1 hω).2
    set k := (univ.filter fun i => ω i ∈ G).card
    have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * r)))) (ω · ∈ G)
    rw [card_univ, Fintype.card_fin] at hc
    have hprod : ∏ i, w (ω i) = b ^ k * g ^ (2 * r - k) := by
      simp only [w, prod_ite, prod_const]; congr 2; omega
    have e1 : g ^ (2 * r - k) = g ^ (r - k) * g ^ r := by rw [← pow_add]; congr 1; omega
    have e2 : b ^ r = b ^ k * b ^ (r - k) := by rw [← pow_add]; congr 1; omega
    rw [hprod, e1, mul_pow, e2]
    calc g ^ r * (b ^ k * b ^ (r - k)) = b ^ k * b ^ (r - k) * g ^ r := by ring
      _ ≤ b ^ k * g ^ (r - k) * g ^ r := by gcongr
      _ = b ^ k * (g ^ (r - k) * g ^ r) := by ring
  refine Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < (g * b) ^ r)
  calc (g * b) ^ r * bad.card
      ≤ ∑ ω : Fin (2 * r) → Ω, ∏ i, w (ω i) := by
        rw [mul_comm, ← smul_eq_mul, ← sum_const]
        exact (sum_le_sum hweight).trans
          (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _)
    _ = (g * b) ^ r * (4 * g * b) ^ r := by rw [hsum, pow_mul, ← mul_pow]; ring

/-- **Majority votes at an inverse-polynomial advantage.** If `G` has density at least
`1 / 2 + 1 / q` in `Ω`, that is `2 |Ω| ≤ q (2 |G| - |Ω|)`, then at most a fifth of the
`2 q ^ 2`-tuples of elements of `Ω` have at most `q ^ 2` entries in `G`. -/
theorem five_mul_card_filter_card_filter_le_sq_le [Nonempty Ω] (G : Finset Ω) {q : ℕ}
    (hG : 2 * Fintype.card Ω ≤ q * (2 * G.card - Fintype.card Ω)) :
    5 * (univ.filter fun ω : Fin (2 * q ^ 2) → Ω =>
      (univ.filter fun i => ω i ∈ G).card ≤ q ^ 2).card ≤ Fintype.card Ω ^ (2 * q ^ 2) := by
  set N := Fintype.card Ω
  set g := G.card
  set D := 2 * g - N
  have hN : 0 < N := Fintype.card_pos
  have hgN : g ≤ N := card_le_univ G
  have hD : 0 < D := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hG; omega
  have hbad := card_filter_card_filter_le_le_pow G (by omega) (q ^ 2)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h4 : ((4 * g * (N - g) : ℕ) : ℝ) = (N : ℝ) ^ 2 * (1 - (D : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hgN, show (D : ℝ) = 2 * g - N by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    field_simp; ring
  have hx₁ : (D : ℝ) ^ 2 / (N : ℝ) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr <|
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : D ≤ N)) 2
  have hrx : (4 : ℝ) ≤ ((q ^ 2 : ℕ) : ℝ) * ((D : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
    rw [Nat.cast_pow, ← mul_div_assoc, le_div_iff₀ (by positivity), ← mul_pow]; cast_nlinarith [hG]
  have hB := one_sub_pow_mul_one_add_mul_le_one (by positivity) hx₁ (q ^ 2)
  have key : (5 : ℝ) * ((4 * g * (N - g) : ℕ) : ℝ) ^ q ^ 2 ≤ (N : ℝ) ^ (2 * q ^ 2) := by
    rw [h4, mul_pow, ← pow_mul, mul_comm 2]
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - (D : ℝ) ^ 2 / (N : ℝ) ^ 2) (q ^ 2),
      pow_pos hNr (q ^ 2 * 2)]
  exact (Nat.mul_le_mul_left 5 hbad).trans (by exact_mod_cast key)

/-- **Majority votes.** If at least two thirds of `Ω` lie in `G`, then at most an `(8 / 9) ^ r`
fraction of the `2 r`-tuples have at most `r` entries in `G`: the case of
`Cslib.card_filter_card_filter_le_le_pow` with `36 |G| |Ω \ G| ≤ 8 |Ω| ^ 2`. -/
theorem card_filter_card_filter_le_le (G : Finset Ω) (hG : 2 * Fintype.card Ω ≤ 3 * G.card)
    (r : ℕ) :
    9 ^ r * (univ.filter fun ω : Fin (2 * r) → Ω => (univ.filter fun i => ω i ∈ G).card ≤ r).card
      ≤ 8 ^ r * Fintype.card Ω ^ (2 * r) := by
  set N := Fintype.card Ω
  have hgN : G.card ≤ N := card_le_univ G
  have hnum : 9 * (4 * G.card * (N - G.card)) ≤ 8 * N ^ 2 := by
    obtain ⟨b, hb⟩ : ∃ b, N = G.card + b := ⟨N - G.card, by omega⟩
    rw [hb, Nat.add_sub_cancel_left]
    nlinarith [Nat.mul_le_mul (by omega : 2 * b ≤ G.card) (by omega : b ≤ 2 * G.card)]
  calc 9 ^ r * _ ≤ 9 ^ r * (4 * G.card * (N - G.card)) ^ r :=
        Nat.mul_le_mul_left _ (card_filter_card_filter_le_le_pow G (by omega) r)
    _ = (9 * (4 * G.card * (N - G.card))) ^ r := (mul_pow _ _ _).symm
    _ ≤ (8 * N ^ 2) ^ r := Nat.pow_le_pow_left hnum r
    _ = 8 ^ r * N ^ (2 * r) := by rw [mul_pow, ← pow_mul, mul_comm 2]

/-- For any `n`, `2 ^ n * 8 ^ (6 * n + 6) < 9 ^ (6 * n + 6)`, since `2 * 8 ^ 6 < 9 ^ 6`. -/
theorem two_pow_mul_eight_pow_lt (n : ℕ) : 2 ^ n * 8 ^ (6 * n + 6) < 9 ^ (6 * n + 6) := by
  calc 2 ^ n * 8 ^ (6 * n + 6) = (2 * 8 ^ 6) ^ n * 8 ^ 6 := by
        rw [mul_pow, pow_add, pow_mul]; ring
    _ < (9 ^ 6) ^ n * 9 ^ 6 :=
      Nat.mul_lt_mul_of_le_of_lt (Nat.pow_le_pow_left (by norm_num) n) (by norm_num)
        (by positivity)
    _ = 9 ^ (6 * n + 6) := by rw [pow_add, pow_mul]

/-- **Majority votes good for many tests at once.** If each of at most `2 ^ n` tests is passed by
at least two thirds of `Ω`, then some `12 (n + 1)` elements of `Ω` contain more than `6 (n + 1)`
elements passing each test. -/
theorem exists_forall_lt_card_filter_mem {X : Type*} [Fintype X] [Nonempty Ω] {n : ℕ}
    (hX : Fintype.card X ≤ 2 ^ n) (good : X → Finset Ω)
    (hgood : ∀ x, 2 * Fintype.card Ω ≤ 3 * (good x).card) :
    ∃ ω : Fin (2 * (6 * n + 6)) → Ω, ∀ x,
      6 * n + 6 < (univ.filter fun i => ω i ∈ good x).card := by
  by_contra! h
  set R := 6 * n + 6
  set N := Fintype.card Ω
  let bad : X → Finset (Fin (2 * R) → Ω) := fun x =>
    univ.filter fun ω => (univ.filter fun i => ω i ∈ good x).card ≤ R
  have hcover : (univ : Finset (Fin (2 * R) → Ω)) ⊆ univ.biUnion bad := fun ω _ =>
    let ⟨x, hx⟩ := h ω; mem_biUnion.2 ⟨x, mem_univ _, mem_filter.2 ⟨mem_univ _, hx⟩⟩
  have hcard := (card_le_card hcover).trans card_biUnion_le
  rw [card_univ, Fintype.card_fun, Fintype.card_fin] at hcard
  have hsum : 9 ^ R * N ^ (2 * R) ≤ 2 ^ n * 8 ^ R * N ^ (2 * R) := by
    calc 9 ^ R * N ^ (2 * R) ≤ 9 ^ R * ∑ x, (bad x).card := Nat.mul_le_mul_left _ hcard
      _ = ∑ x, 9 ^ R * (bad x).card := mul_sum ..
      _ ≤ ∑ _x : X, 8 ^ R * N ^ (2 * R) :=
        sum_le_sum fun x _ => card_filter_card_filter_le_le (good x) (hgood x) R
      _ ≤ 2 ^ n * 8 ^ R * N ^ (2 * R) := by
        rw [sum_const, card_univ, smul_eq_mul, mul_assoc]; exact Nat.mul_le_mul_right _ hX
  exact absurd (hsum.trans_lt (Nat.mul_lt_mul_of_pos_right (two_pow_mul_eight_pow_lt n)
    (pow_pos Fintype.card_pos _))) (lt_irrefl _)

omit [DecidableEq Ω] in
/-- **One good element for many tests at once.** If each of at most `2 ^ n` tests is passed by at
least half of `Ω`, then some `n + 1` elements of `Ω` contain one passing each test. -/
theorem exists_forall_exists_apply_mem {X : Type*} [Fintype X] [Nonempty Ω] {n : ℕ}
    (hX : Fintype.card X ≤ 2 ^ n) (good : X → Finset Ω)
    (hgood : ∀ x, Fintype.card Ω ≤ 2 * (good x).card) :
    ∃ ω : Fin (n + 1) → Ω, ∀ x, ∃ i, ω i ∈ good x := by
  classical
  refine exists_cover_of_scaled_card_lt (fun ω x => ω ∈ good x) 1 2 (n + 1) (fun x => ?_)
    (by simpa only [one_pow, mul_one] using hX.trans_lt (Nat.pow_lt_pow_right (by decide) (by lia)))
  rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have := hgood x; have := card_le_univ (good x); lia

end Cslib
