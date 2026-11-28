/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.BinPacking.OnlineLowerBound
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Brown–Liang lower bound for online bin packing

[Brown][Brown1979] and [Liang][Liang1980] independently extended Yao's three-phase adversary
(`OnlinePacker.yao_lower_bound`) to items of sizes `1/d + ε` for the Sylvester denominators
`d = 1807, 43, 7, 3, 2`, presented smallest first and stopped after any phase, and derived that no
online bin-packing algorithm has asymptotic competitive ratio below `1.53635`.
[Van Vliet][VanVliet1992] analysed such sequences through the dual linear program. These values,
the sequence and van Vliet's method are as reported in
[Balogh, Békési, Dósa, Epstein and Levin, Section 1][BaloghBekesiDosaEpsteinLevin2018]; the
primary sources were not inspected.

This file proves the bound `56029 / 36379 ≈ 1.54015` for Brown's and Liang's five-phase input
(`OnlinePacker.brown_liang_lower_bound`). The constant is the exact optimum of the linear program
of this input, in van Vliet's analysis: the optimum was computed outside Lean, and the matching
dual certificate is checked in Lean. It exceeds the `1.53635` that Brown and Liang derived. Van
Vliet's `1.5401474`, which uses additional items, remains a target.

**The instance.** Let `D = 2 * 3 * 7 * 43 * 1807 = 3263442`. The bins have capacity `D - 1` and
the items have sizes `D / d` for `d = 1807, 43, 7, 3, 2` (`brownLiangSizes`). Items of sizes
`D / dᵢ` fit together into one bin exactly when `∑ 1/dᵢ < 1`, so this instance has the same
feasible bin patterns as the sizes `1/dᵢ + ε` with capacity `1`. The input
(`brownLiangInput (1806 * m) j`) presents `1806 * m` items of each size, smallest first, and stops
after phase `j + 1`. Its optimum is `brownLiangOpt j * m`, where `brownLiangOpt = 1, 43, 301,
903, 1806` (`exists_isPacking_brownLiangInput` and `le_length_of_isPacking_brownLiangInput`): a
bin holds at most `1806`, `42`, `6`, `2` and `1` items of the five sizes, and a bin with
`1806 / brownLiangOpt j` items of each of the first `j + 1` sizes fits.

**Phase counting** (`OnlinePacker.sum_map_le_sum_mul_length`, which generalizes Yao's counting):
if the items carry weights `w` and every bin's weight is at most
`∑ⱼ yⱼ * [the bin holds an item of the first j phases]`, then the total weight is at most
`∑ⱼ yⱼ * ALGⱼ`, where `ALGⱼ` is the number of bins after phase `j`.

**The certificate.** Give the five sizes the weights `1, 42, 252, 504, 504`
(`brownLiangWeight`) and the five phases the multipliers `42, 252, 504, 504, 504`
(`brownLiangMult`). Then every bin of capacity `D - 1` satisfies the hypothesis above
(`sum_map_brownLiangWeight_le`): `omega` checks the resulting linear inequalities over the
counts of the five sizes. The total weight is `1303 * 1806 * m`, and
`∑ⱼ yⱼ * brownLiangOpt j * m = 1527918 * m`, so if `36379 * ALGⱼ < 56029 * OPTⱼ` for every
phase, then `36379 * 1303 * 1806 * m ≤ 36379 * ∑ⱼ yⱼ ALGⱼ < 56029 * 1527918 * m`, which is the
same number. The weights and multipliers are an optimal dual solution of the linear program over
the feasible patterns, so no weight certificate gives a larger constant for these five phases.
The input is Brown's and Liang's; its integer scaling, the batch size `1806 * m` and the
certificate are chosen here.

`OnlinePacker.brown_liang_exists_ratio_violation_of_lt` restates the bound: for `p / q` below
`56029 / 36379` and every additive constant `c`, every online packer violates
`q * ALG ≤ p * OPT + c` on some input.

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.brownLiangSizes`, `brownLiangInput`, `brownLiangOpt`: the
  instance, the inputs and their optima.
* `Cslib.Algorithms.Lean.BinPacking.brownLiangWeight`, `brownLiangMult`: the certificate.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.sum_map_brownLiangWeight_le`: the certificate for one bin.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.brown_liang_lower_bound`: the `56029 / 36379`
  lower bound for Brown's and Liang's five-phase input.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.brown_liang_exists_ratio_violation_of_lt`: no
  ratio below `56029 / 36379` with any additive constant.
* `Cslib.Algorithms.Lean.BinPacking.exists_isPacking_brownLiangInput` and
  `Cslib.Algorithms.Lean.BinPacking.le_length_of_isPacking_brownLiangInput`: the optima.

## References

* [D. J. Brown, *A lower bound for on-line one-dimensional bin packing algorithms*][Brown1979]
* [F. M. Liang, *A lower bound for on-line bin packing*][Liang1980]
* [A. van Vliet, *An improved lower bound for on-line bin packing algorithms*][VanVliet1992]
* [J. Balogh, J. Békési, G. Dósa, L. Epstein, A. Levin, *A new lower bound for classic online bin
  packing*][BaloghBekesiDosaEpsteinLevin2018]
-/

public section

namespace Cslib.Algorithms.Lean.BinPacking

open List

/-! ### The instance -/

/-- The item sizes of the Brown–Liang input in bins of capacity `3263441`, in order of arrival:
`3263442 / d` for `d = 1807, 43, 7, 3, 2`. -/
@[expose] def brownLiangSizes : List ℕ := [1806, 75894, 466206, 1087814, 1631721]

/-- The Brown–Liang input with `n` items per phase, stopped after phase `j + 1`: `n` items of
each of the first `j + 1` sizes of `brownLiangSizes`, smallest first. -/
@[expose] def brownLiangInput (n : ℕ) (j : Fin 5) : List ℕ :=
  (brownLiangSizes.take (j + 1)).flatMap (replicate n)

/-- The optimum of `brownLiangInput (1806 * m) j` is `brownLiangOpt j * m`. -/
@[expose] def brownLiangOpt : Fin 5 → ℕ := ![1, 43, 301, 903, 1806]

/-- The weight of an item in the certificate: `1`, `42`, `252`, `504` and `504` for the five
sizes of `brownLiangSizes`, and `0` otherwise. -/
@[expose] def brownLiangWeight (a : ℕ) : ℕ :=
  if a = 1806 then 1 else if a = 75894 then 42 else if a = 466206 then 252
  else if a = 1087814 ∨ a = 1631721 then 504 else 0

/-- The multiplier of each phase in the certificate. -/
@[expose] def brownLiangMult : Fin 5 → ℕ := ![42, 252, 504, 504, 504]

private theorem sum_map_brownLiangWeight (b : List ℕ) :
    (b.map brownLiangWeight).sum = b.count 1806 + 42 * b.count 75894 + 252 * b.count 466206 +
      504 * b.count 1087814 + 504 * b.count 1631721 := by
  induction b with
  | nil => simp
  | cons a b ih =>
    simp only [map_cons, sum_cons, ih, count_cons, brownLiangWeight, beq_iff_eq]
    split_ifs <;> omega

private theorem mul_count_add_le_sum (b : List ℕ) :
    1806 * b.count 1806 + 75894 * b.count 75894 + 466206 * b.count 466206 +
      1087814 * b.count 1087814 + 1631721 * b.count 1631721 ≤ b.sum := by
  induction b with
  | nil => simp
  | cons a b ih =>
    simp only [sum_cons, count_cons, beq_iff_eq]
    split_ifs <;> omega

private theorem toNat_any_mem (b l : List ℕ) :
    (b.any (· ∈ l)).toNat = if 0 < (l.map b.count).sum then 1 else 0 := by
  have : b.any (· ∈ l) = true ↔ 0 < (l.map b.count).sum := by
    simp only [any_eq_true, decide_eq_true_eq, Nat.pos_iff_ne_zero, ne_eq, sum_eq_zero_iff,
      mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, count_eq_zero, not_forall,
      not_not]
    exact ⟨fun ⟨a, ha, hl⟩ => ⟨a, hl, ha⟩, fun ⟨a, hl, ha⟩ => ⟨a, ha, hl⟩⟩
  by_cases h : b.any (· ∈ l) <;> simp_all

/-- **The certificate.** A bin of capacity `3263441` has weight at most `42`, `252`, `504`, `504`
and `504` for each phase `j + 1` such that the bin holds an item of one of the first `j + 1`
sizes. -/
theorem sum_map_brownLiangWeight_le {b : List ℕ} (hb : b.sum ≤ 3263441) :
    (b.map brownLiangWeight).sum ≤
      ∑ j : Fin 5, brownLiangMult j * (b.any (· ∈ brownLiangSizes.take (j + 1))).toNat := by
  have h := mul_count_add_le_sum b
  simp only [toNat_any_mem, sum_map_brownLiangWeight]
  simp only [Fin.sum_univ_five, brownLiangMult, brownLiangSizes, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Fin.val_zero, Fin.val_one, Fin.val_two]
  simp +decide only [take, map_cons, map_nil, sum_cons, sum_nil]
  split_ifs <;> omega

/-! ### The optima -/

private theorem count_flatMap_replicate (x n : ℕ) (l : List ℕ) :
    (l.flatMap (replicate n)).count x = n * l.count x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [flatMap_cons, count_append, count_replicate, ih, count_cons, beq_iff_eq]
    split_ifs <;> simp_all [Nat.mul_add, Nat.add_comm]

private theorem mul_count_le_sum (x : ℕ) (b : List ℕ) : x * b.count x ≤ b.sum := by
  induction b with
  | nil => simp
  | cons a b ih =>
    simp only [sum_cons, count_cons, beq_iff_eq]
    split_ifs with h
    · subst h; rw [Nat.mul_add, Nat.mul_one]; omega
    · rw [Nat.add_zero]; omega

private theorem sum_flatMap_replicate (k : ℕ) (l : List ℕ) :
    (l.flatMap (replicate k)).sum = k * l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [flatMap_cons, sum_replicate, ih, Nat.mul_add]

private theorem isPacking_replicate {C : ℕ} {l bin : List ℕ} {k : ℕ} (hsum : bin.sum ≤ C)
    (hcnt : ∀ x, l.count x = k * bin.count x) : IsPacking C l (replicate k bin) :=
  ⟨perm_iff_count.2 fun x => by simp [count_flatten, map_replicate, sum_replicate, hcnt x],
   fun _ hb => eq_of_mem_replicate hb ▸ hsum⟩

/-- `brownLiangInput (1806 * m) j` fits into `brownLiangOpt j * m` bins, each holding
`1806 / brownLiangOpt j` items of each of the first `j + 1` sizes. -/
theorem exists_isPacking_brownLiangInput (m : ℕ) (j : Fin 5) :
    ∃ Q, IsPacking 3263441 (brownLiangInput (1806 * m) j) Q ∧ Q.length = brownLiangOpt j * m := by
  have hk : brownLiangOpt j * (1806 / brownLiangOpt j) = 1806 := by fin_cases j <;> rfl
  refine ⟨replicate (brownLiangOpt j * m)
    ((brownLiangSizes.take (j + 1)).flatMap (replicate (1806 / brownLiangOpt j))),
    isPacking_replicate ?_ fun x => ?_, length_replicate⟩
  · rw [sum_flatMap_replicate]
    fin_cases j <;> decide
  · rw [brownLiangInput, count_flatMap_replicate, count_flatMap_replicate,
      show brownLiangOpt j * m * (1806 / brownLiangOpt j * (brownLiangSizes.take (j + 1)).count x)
        = brownLiangOpt j * (1806 / brownLiangOpt j) * m * (brownLiangSizes.take (j + 1)).count x
        by ring, hk]

private theorem le_mul_length_of_count {C s k n : ℕ} {l : List ℕ} {Q : List (List ℕ)}
    (hQ : IsPacking C l Q) (hs : C < s * (k + 1)) (hn : n ≤ l.count s) : n ≤ k * Q.length :=
  hn.trans <| hQ.count_le_mul_length s fun b hb => Nat.lt_succ_iff.1 <|
    Nat.lt_of_mul_lt_mul_left ((mul_count_le_sum s b).trans hb |>.trans_lt hs)

/-- Every packing of `brownLiangInput (1806 * m) j` has at least `brownLiangOpt j * m` bins: a bin
holds at most `1806 / brownLiangOpt j` items of size `3263442 / d` for the last phase's `d`. -/
theorem le_length_of_isPacking_brownLiangInput {m : ℕ} {j : Fin 5} {Q : List (List ℕ)}
    (hQ : IsPacking 3263441 (brownLiangInput (1806 * m) j) Q) : brownLiangOpt j * m ≤ Q.length := by
  obtain ⟨s, hs, hC⟩ : ∃ s ∈ brownLiangSizes.take (j + 1),
      3263441 < s * (1806 / brownLiangOpt j + 1) := by
    fin_cases j <;> decide
  have hk : brownLiangOpt j * (1806 / brownLiangOpt j) = 1806 := by fin_cases j <;> rfl
  have hpos : 0 < 1806 / brownLiangOpt j := by fin_cases j <;> decide
  have h := le_mul_length_of_count hQ hC (n := 1806 * m) <| by
    rw [brownLiangInput, count_flatMap_replicate]
    exact Nat.le_mul_of_pos_right _ (count_pos_iff.2 hs)
  refine Nat.le_of_mul_le_mul_left (h.trans_eq' ?_) hpos
  rw [← Nat.mul_assoc, Nat.mul_comm (1806 / _), hk]

/-! ### The lower bound -/

namespace OnlinePacker

variable (A : OnlinePacker 3263441)

/-- **The Brown–Liang lower bound**, with the constant `56029 / 36379 ≈ 1.54015`. Against Brown's
and Liang's input, `1806 * m` items of each of the sizes `brownLiangSizes` (the sizes `1/d + ε`
for `d = 1807, 43, 7, 3, 2`, scaled to bins of capacity `3263441`), smallest first, every online
packer uses at least `56029 / 36379` times the optimum `brownLiangOpt j * m` after one of the five
phases `j + 1`. The constant is the exact optimum of the linear program of this input (computed
outside Lean; the certificate is checked here) and exceeds the `1.53635` that Brown and Liang
derived. The optima are `exists_isPacking_brownLiangInput` and
`le_length_of_isPacking_brownLiangInput`. -/
theorem brown_liang_lower_bound (m : ℕ) :
    ∃ j : Fin 5, 56029 * (brownLiangOpt j * m) ≤
      36379 * (A.run (brownLiangInput (1806 * m) j)).length := by
  have hnd : brownLiangSizes.Nodup := by decide
  have hl : ∀ a ∈ brownLiangInput (1806 * m) 4, a ≤ 3263441 := by
    intro a ha
    simp only [brownLiangInput, brownLiangSizes, mem_flatMap, mem_replicate] at ha
    obtain ⟨s, hs, -, rfl⟩ := ha
    simp at hs; omega
  have h := A.sum_map_le_sum_mul_length hl brownLiangWeight brownLiangMult
    (fun j a => a ∈ brownLiangSizes.take (j + 1)) (brownLiangInput (1806 * m))
    (fun j => (brownLiangSizes.drop (j + 1)).flatMap (replicate (1806 * m)))
    (fun j => by rw [brownLiangInput, brownLiangInput, ← flatMap_append, take_append_drop]; rfl)
    (fun j a ha => by
      obtain ⟨s, hs, ha⟩ := mem_flatMap.1 ha
      rw [eq_of_mem_replicate ha]
      exact decide_eq_false fun h => disjoint_take_drop hnd le_rfl h hs)
    fun b hb => sum_map_brownLiangWeight_le hb
  have hw : ((brownLiangInput (1806 * m) 4).map brownLiangWeight).sum = 1303 * (1806 * m) := by
    simp [brownLiangInput, brownLiangSizes, brownLiangWeight, take, map_replicate, sum_replicate]
    ring
  rw [hw, Fin.sum_univ_five] at h
  by_contra hcon
  simp only [not_exists, Nat.not_le] at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  have h3 := hcon 3
  have h4 := hcon 4
  simp only [brownLiangOpt, brownLiangMult, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h h0 h1 h2 h3 h4
  omega

/-- **No online ratio below `56029 / 36379`.** If `p / q < 56029 / 36379`, then for every additive
constant `c` some input has an optimal packing `Q` with `p * Q.length + c < q * ALG`. -/
theorem brown_liang_exists_ratio_violation_of_lt {p q : ℕ} (hpq : 36379 * p < 56029 * q) (c : ℕ) :
    ∃ (l : List ℕ) (Q : List (List ℕ)), IsPacking 3263441 l Q ∧
      (∀ Q', IsPacking 3263441 l Q' → Q.length ≤ Q'.length) ∧
      p * Q.length + c < q * (A.run l).length := by
  obtain ⟨j, hj⟩ := A.brown_liang_lower_bound (36379 * c + 1)
  obtain ⟨Q, hQ, hlen⟩ := exists_isPacking_brownLiangInput (36379 * c + 1) j
  refine ⟨_, Q, hQ, fun Q' hQ' => hlen ▸ le_length_of_isPacking_brownLiangInput hQ', ?_⟩
  have hm : 36379 * c + 1 ≤ Q.length :=
    hlen ▸ Nat.le_mul_of_pos_left _ (by fin_cases j <;> decide)
  rw [← hlen] at hj
  have h1 := Nat.mul_le_mul_left q hj
  have h2 := Nat.mul_le_mul_right Q.length hpq
  nlinarith

end OnlinePacker

end Cslib.Algorithms.Lean.BinPacking
