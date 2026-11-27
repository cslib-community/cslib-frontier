/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.BigOperators
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Randomized rounding with a random shift ("snap")

The Saks–Zhou rounding operator [SaksZhou1999], called `Snap` in [ChattopadhyayLiao2020,
Definition A.2] after Hoza and Umans, is
`snap d x y = max (⌊x 2 ^ d - y 2 ^ (-d)⌋ 2 ^ (-d)) 0` for a shift `y ∈ [0, 2 ^ d)`. It perturbs
`x` downward by `y 2 ^ (-2d) ∈ [0, 2 ^ (-d))`, rounds down to a multiple of `2 ^ (-d)` and clips
at `0`. For `x ≥ 0` the result lies in `[x - 2 ^ (1 - d), x]`, and it is always a nonnegative
multiple of `2 ^ (-d)`. Applied entrywise (`snapMatrix`), it maps substochastic matrices to
substochastic matrices with entries in `2 ^ (-d) ℕ` (`IsDyadicSubstochastic`).

The point of the random shift is Lemma A.3 of [ChattopadhyayLiao2020]: two nearby values are
rounded differently for few shifts. If `|a - b| ≤ ε`, at most a `2 ^ d ε + 2 ^ (-d)` fraction of
the shifts `y` give `snap d a y ≠ snap d b y` (`dens_snap_ne_le`). For matrices, a union bound
over the entries gives `|ι| |κ| (2 ^ d ε + 2 ^ (-d))` (`dens_snapMatrix_ne_le`). For `a ≤ b`, each
disagreement contributes at least one to the sum of integer-part differences over the shifts.
Hermite's identity `Int.sum_floor_add_div` evaluates that sum as `⌊2 ^ (2d) b⌋ - ⌊2 ^ (2d) a⌋`.

## Main definitions

* `Cslib.Probability.SaksZhou.snap`: the rounding operator `Snap_d(x, y)`.
* `Cslib.Probability.SaksZhou.snapMatrix`: its entrywise application to a matrix.
* `Cslib.Probability.SaksZhou.IsDyadicSubstochastic`: nonnegative matrices with rows summing to at
  most `1` and entries in `2 ^ (-d) ℕ`.

## Main results

* `Cslib.Probability.SaksZhou.sub_le_snap`, `Cslib.Probability.SaksZhou.snap_le`,
  `Cslib.Probability.SaksZhou.abs_snap_sub_le`: `x - 2 ^ (1 - d) ≤ snap d x y ≤ x` for `x ≥ 0`.
* `Cslib.Probability.SaksZhou.exists_snap_eq`: the values are multiples of `2 ^ (-d)`.
* `Cslib.Probability.SaksZhou.isDyadicSubstochastic_snapMatrix`: snapping preserves
  substochasticity.
* `Cslib.Probability.SaksZhou.dens_snap_ne_le`: Lemma A.3 for one entry.
* `Cslib.Probability.SaksZhou.dens_snapMatrix_ne_le`: Lemma A.3 for matrices.

## References

* [M. Saks and S. Zhou, *BP_H SPACE(S) ⊆ DSPACE(S^{3/2})*][SaksZhou1999]: the rounding operator.
  The publisher copy was not consulted, so its internal numbering is unverified.
* [E. Chattopadhyay and J.-J. Liao, *Optimal Error Pseudodistributions for Read-Once Branching
  Programs*][ChattopadhyayLiao2020], arXiv v4, Appendix A.1, Definition A.2 and Lemma A.3.
-/

public section

namespace Cslib.Probability.SaksZhou

open Finset

/-- The Saks–Zhou rounding operator `Snap_d(x, y) = max (⌊x 2 ^ d - y 2 ^ (-d)⌋ 2 ^ (-d)) 0`
[ChattopadhyayLiao2020, Definition A.2], for a shift `y ∈ [0, 2 ^ d)`. -/
noncomputable def snap (d : ℕ) (x : ℝ) (y : Fin (2 ^ d)) : ℝ :=
  max ((⌊x * 2 ^ d - (y : ℝ) / 2 ^ d⌋ : ℝ) / 2 ^ d) 0

theorem snap_def (d : ℕ) (x : ℝ) (y : Fin (2 ^ d)) :
    snap d x y = max ((⌊x * 2 ^ d - (y : ℝ) / 2 ^ d⌋ : ℝ) / 2 ^ d) 0 := by
  rw [snap]

theorem snap_nonneg (d : ℕ) (x : ℝ) (y : Fin (2 ^ d)) : 0 ≤ snap d x y := by
  rw [snap_def]
  exact le_max_right _ _

private theorem floor_div_le (d : ℕ) (x : ℝ) (y : Fin (2 ^ d)) :
    (⌊x * 2 ^ d - (y : ℝ) / 2 ^ d⌋ : ℝ) / 2 ^ d ≤ x := by
  rw [div_le_iff₀ (by positivity)]
  linarith [Int.floor_le (x * 2 ^ d - (y : ℝ) / 2 ^ d),
    div_nonneg (Nat.cast_nonneg (α := ℝ) y.val) (pow_nonneg zero_le_two d)]

/-- Snapping never exceeds the positive part. -/
theorem snap_le_max (d : ℕ) (x : ℝ) (y : Fin (2 ^ d)) : snap d x y ≤ max x 0 := by
  rw [snap_def]
  exact max_le_max (floor_div_le d x y) le_rfl

/-- Snapping rounds a nonnegative value down. -/
theorem snap_le (d : ℕ) {x : ℝ} (hx : 0 ≤ x) (y : Fin (2 ^ d)) : snap d x y ≤ x :=
  (snap_le_max d x y).trans_eq (max_eq_left hx)

/-- Snapping loses less than `2 ^ (-d)` to the shift and less than `2 ^ (-d)` to rounding. -/
theorem sub_le_snap (d : ℕ) (x : ℝ) (y : Fin (2 ^ d)) : x - 2 / 2 ^ d ≤ snap d x y := by
  rw [snap_def]
  refine le_trans ?_ (le_max_left _ _)
  have hq : (0 : ℝ) < 2 ^ d := by positivity
  have h1 : (y : ℝ) / 2 ^ d < 1 := (div_lt_one hq).2 (by exact_mod_cast y.isLt)
  rw [le_div_iff₀ hq, sub_mul, div_mul_cancel₀ _ hq.ne']
  linarith [Int.lt_floor_add_one (x * 2 ^ d - (y : ℝ) / 2 ^ d)]

/-- For `x ≥ 0`, `|snap d x y - x| ≤ 2 ^ (1 - d)`. -/
theorem abs_snap_sub_le (d : ℕ) {x : ℝ} (hx : 0 ≤ x) (y : Fin (2 ^ d)) :
    |snap d x y - x| ≤ 2 / 2 ^ d := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (snap_le d hx y))]
  linarith [sub_le_snap d x y]

/-- Snapping uses the natural floor, which incorporates the lower cutoff at zero. -/
theorem snap_eq_natFloor (d : ℕ) (x : ℝ) (y : Fin (2 ^ d)) :
    snap d x y = (⌊x * 2 ^ d - (y : ℝ) / 2 ^ d⌋₊ : ℝ) / 2 ^ d := by
  rw [snap_def, ← Int.floor_toNat]
  generalize ⌊x * 2 ^ d - (y : ℝ) / 2 ^ d⌋ = z
  rcases le_total 0 z with h | h
  · rw [max_eq_left (div_nonneg (by exact_mod_cast h) (by positivity))]
    exact congrArg (· / 2 ^ d) (by exact_mod_cast (Int.toNat_of_nonneg h).symm)
  · rw [Int.toNat_eq_zero.2 h,
      max_eq_right (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) (by positivity))]
    simp

/-- Snapped values are multiples of `2 ^ (-d)`. -/
theorem exists_snap_eq (d : ℕ) (x : ℝ) (y : Fin (2 ^ d)) :
    ∃ k : ℕ, snap d x y = k / 2 ^ d :=
  ⟨_, snap_eq_natFloor d x y⟩

/-- Numerator after shifted rounding of a frequency `hits / total` to the grid of denominator
`scale`. Natural subtraction clips negative values before the division. -/
@[expose] def snapCount (scale hits total shift : ℕ) : ℕ :=
  (hits * scale * scale - shift * total) / (total * scale)

/-- Exact binary arithmetic for rounding a frequency at precision `d`. -/
theorem snap_frequency (d hits total : ℕ) (ht : 0 < total) (y : Fin (2 ^ d)) :
    snap d (hits / total) y = (snapCount (2 ^ d) hits total y : ℝ) / 2 ^ d := by
  rw [snap_eq_natFloor]
  congr 2
  let q : ℕ := 2 ^ d
  have hq : 0 < q := Nat.two_pow_pos d
  have heq : (hits : ℝ) / total * 2 ^ d - (y : ℝ) / 2 ^ d =
      ((hits * q * q : ℕ) - (y.val * total : ℕ) : ℝ) / (total * q : ℕ) := by
    simp only [q, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  rw [heq, Nat.floor_div_natCast, Nat.floor_sub_natCast, Nat.floor_natCast]
  rfl

/-- Hermite's identity over a reversed complete residue system:
`∑_{t < q} ⌊c - t / q⌋ = ⌊q c⌋ - (q - 1)`. -/
private theorem sum_floor_sub_div (c : ℝ) {q : ℕ} (hq : 0 < q) :
    ∑ t : Fin q, ⌊c - (t : ℝ) / q⌋ = ⌊q * c⌋ - (q - 1 : ℤ) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [Fin.sum_univ_eq_sum_range (fun t => ⌊c - (t : ℝ) / q⌋), ← Finset.sum_range_reflect]
  have key : ∀ t ∈ Finset.range q,
      ⌊c - ((q - 1 - t : ℕ) : ℝ) / q⌋ = ⌊c - ((q - 1 : ℕ) : ℝ) / q + (t : ℝ) / q⌋ := by
    intro t ht
    congr 1
    rw [Nat.cast_sub (Nat.le_sub_one_of_lt (Finset.mem_range.1 ht)), sub_div]
    ring
  rw [Finset.sum_congr rfl key, Int.sum_floor_add_div, mul_sub, mul_div_cancel₀ _ hq',
    Int.floor_sub_natCast, Nat.cast_sub hq, Nat.cast_one]

/-- **Lemma A.3 of [ChattopadhyayLiao2020], counting form.** If `|a - b| ≤ ε`, at most
`4 ^ d ε + 1` of the `2 ^ d` shifts round `a` and `b` differently. -/
theorem card_snap_ne_le (d : ℕ) {a b ε : ℝ} (hab : |a - b| ≤ ε) :
    (#{y : Fin (2 ^ d) | snap d a y ≠ snap d b y} : ℝ) ≤ 4 ^ d * ε + 1 := by
  wlog hle : a ≤ b generalizing a b
  · simpa only [ne_comm] using this (a := b) (b := a) (by rwa [abs_sub_comm]) (le_of_not_ge hle)
  set f : Fin (2 ^ d) → ℤ := fun t => ⌊a * 2 ^ d - (t : ℝ) / 2 ^ d⌋ with hf
  set g : Fin (2 ^ d) → ℤ := fun t => ⌊b * 2 ^ d - (t : ℝ) / 2 ^ d⌋ with hg
  have hfg : ∀ t, f t ≤ g t := fun t => Int.floor_mono (by gcongr)
  have hcount : ((#{y : Fin (2 ^ d) | snap d a y ≠ snap d b y} : ℕ) : ℤ) ≤
      ∑ t, (g t - f t) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    split_ifs with ht
    · rw [Nat.cast_one, le_sub_iff_add_le, add_comm]
      refine Int.add_one_le_of_lt (lt_of_le_of_ne (hfg t) fun heq => ht ?_)
      simpa only [snap_def] using congrArg (fun z : ℤ => max ((z : ℝ) / 2 ^ d) 0) heq
    · exact sub_nonneg.mpr (hfg t)
  have hsum : ∑ t, (g t - f t) =
      ⌊(2 ^ d : ℕ) * (b * 2 ^ d)⌋ - ⌊(2 ^ d : ℕ) * (a * 2 ^ d)⌋ := by
    have h1 := sum_floor_sub_div (b * 2 ^ d) (Nat.two_pow_pos d)
    have h2 := sum_floor_sub_div (a * 2 ^ d) (Nat.two_pow_pos d)
    push_cast at h1 h2 ⊢
    rw [Finset.sum_sub_distrib, h1, h2]
    ring
  have hfin : ((⌊(2 ^ d : ℕ) * (b * 2 ^ d)⌋ - ⌊(2 ^ d : ℕ) * (a * 2 ^ d)⌋ : ℤ) : ℝ) ≤
      4 ^ d * ε + 1 := by
    have hscale (x : ℝ) : (2 : ℝ) ^ d * (x * 2 ^ d) = 4 ^ d * x := by
      rw [← mul_assoc, mul_right_comm, ← mul_pow]
      norm_num
    have hδ := mul_le_mul_of_nonneg_left (abs_sub_le_iff.mp hab).2
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) d)
    rw [mul_sub] at hδ
    push_cast
    rw [hscale, hscale]
    linarith only [Int.floor_le ((4 : ℝ) ^ d * b), Int.lt_floor_add_one ((4 : ℝ) ^ d * a), hδ]
  calc (#{y : Fin (2 ^ d) | snap d a y ≠ snap d b y} : ℝ)
      ≤ ((⌊(2 ^ d : ℕ) * (b * 2 ^ d)⌋ - ⌊(2 ^ d : ℕ) * (a * 2 ^ d)⌋ : ℤ) : ℝ) := by
        rw [← hsum]
        exact_mod_cast hcount
    _ ≤ 4 ^ d * ε + 1 := hfin

private theorem cast_dens_shift (d : ℕ) (s : Finset (Fin (2 ^ d))) :
    (s.dens : ℝ) = #s / 2 ^ d := by
  simp [Finset.dens]

private theorem dens_shift_le_of_card_le (d : ℕ) {s : Finset (Fin (2 ^ d))} {c ε : ℝ}
    (h : (#s : ℝ) ≤ c * (4 ^ d * ε + 1)) :
    (s.dens : ℝ) ≤ c * (2 ^ d * ε + (2 ^ d)⁻¹) := by
  have htwo : (0 : ℝ) < 2 ^ d := pow_pos zero_lt_two d
  rw [cast_dens_shift, div_le_iff₀ htwo, mul_assoc, add_mul,
    inv_mul_cancel₀ htwo.ne', mul_right_comm (2 ^ d), ← mul_pow]
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using h

/-- **Lemma A.3 of [ChattopadhyayLiao2020]** for one entry: if `|a - b| ≤ ε`, a uniform shift
rounds `a` and `b` differently with probability at most `2 ^ d ε + 2 ^ (-d)`. -/
theorem dens_snap_ne_le (d : ℕ) {a b ε : ℝ} (hab : |a - b| ≤ ε) :
    (({y : Fin (2 ^ d) | snap d a y ≠ snap d b y} : Finset _).dens : ℝ) ≤
      2 ^ d * ε + (2 ^ d)⁻¹ := by
  simpa only [one_mul] using dens_shift_le_of_card_le d (c := 1)
    ((card_snap_ne_le d hab).trans_eq (one_mul _).symm)

/-- Entrywise snapping of a matrix. -/
noncomputable def snapMatrix {ι κ : Type*} (d : ℕ) (A : Matrix ι κ ℝ) (y : Fin (2 ^ d)) :
    Matrix ι κ ℝ :=
  Matrix.of fun i j => snap d (A i j) y

theorem snapMatrix_apply {ι κ : Type*} (d : ℕ) (A : Matrix ι κ ℝ) (y : Fin (2 ^ d)) (i : ι)
    (j : κ) : snapMatrix d A y i j = snap d (A i j) y := by
  rw [snapMatrix, Matrix.of_apply]

/-- **Lemma A.3 of [ChattopadhyayLiao2020]**, counting form for matrices: if two matrices are
entrywise within `ε`, at most `|ι| |κ| (4 ^ d ε + 1)` shifts snap them differently. -/
theorem card_snapMatrix_ne_le {ι κ : Type*} [Fintype ι] [Fintype κ] (d : ℕ)
    {A B : Matrix ι κ ℝ} {ε : ℝ} (hAB : ∀ i j, |A i j - B i j| ≤ ε) :
    (#{y : Fin (2 ^ d) | snapMatrix d A y ≠ snapMatrix d B y} : ℝ) ≤
      Fintype.card ι * Fintype.card κ * (4 ^ d * ε + 1) := by
  classical
  have hsub : ({y : Fin (2 ^ d) | snapMatrix d A y ≠ snapMatrix d B y} : Finset _) ⊆
      (univ : Finset (ι × κ)).biUnion fun p =>
        {y : Fin (2 ^ d) | snap d (A p.1 p.2) y ≠ snap d (B p.1 p.2) y} := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hy ⊢
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
    exact ⟨(i, j), hij⟩
  calc (#{y : Fin (2 ^ d) | snapMatrix d A y ≠ snapMatrix d B y} : ℝ)
      ≤ ∑ p : ι × κ, (#{y : Fin (2 ^ d) | snap d (A p.1 p.2) y ≠ snap d (B p.1 p.2) y} : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _p : ι × κ, (4 ^ d * ε + 1) :=
        Finset.sum_le_sum fun p _ => card_snap_ne_le d (hAB p.1 p.2)
    _ = Fintype.card ι * Fintype.card κ * (4 ^ d * ε + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
        push_cast
        ring

/-- **Lemma A.3 of [ChattopadhyayLiao2020]** for matrices: if two `ι × κ` matrices are entrywise
within `ε`, a uniform shift snaps them differently with probability at most
`|ι| |κ| (2 ^ d ε + 2 ^ (-d))`. -/
theorem dens_snapMatrix_ne_le {ι κ : Type*} [Fintype ι] [Fintype κ] (d : ℕ)
    {A B : Matrix ι κ ℝ} {ε : ℝ} (hAB : ∀ i j, |A i j - B i j| ≤ ε) :
    (({y : Fin (2 ^ d) | snapMatrix d A y ≠ snapMatrix d B y} : Finset _).dens : ℝ) ≤
      Fintype.card ι * Fintype.card κ * (2 ^ d * ε + (2 ^ d)⁻¹) :=
  dens_shift_le_of_card_le d (card_snapMatrix_ne_le d hAB)

/-- A square matrix is dyadic substochastic at precision `d` if its entries are nonnegative
multiples of `2 ^ (-d)` and its rows sum to at most `1`. These are the matrices that a
read-once branching program reading `d` bits per step can realize, as in
[Hoza2021, proof of Theorem A.3]. -/
structure IsDyadicSubstochastic {ι : Type*} [Fintype ι] (d : ℕ) (A : Matrix ι ι ℝ) : Prop where
  /-- The entries are nonnegative. -/
  nonneg : ∀ i j, 0 ≤ A i j
  /-- Every row sums to at most `1`. -/
  sum_le_one : ∀ i, ∑ j, A i j ≤ 1
  /-- The entries are multiples of `2 ^ (-d)`. -/
  dyadic : ∀ i j, ∃ k : ℕ, A i j = k / 2 ^ d

/-- Snapping a substochastic matrix gives a dyadic substochastic matrix. -/
theorem isDyadicSubstochastic_snapMatrix {ι : Type*} [Fintype ι] (d : ℕ) {A : Matrix ι ι ℝ}
    (h0 : ∀ i j, 0 ≤ A i j) (h1 : ∀ i, ∑ j, A i j ≤ 1) (y : Fin (2 ^ d)) :
    IsDyadicSubstochastic d (snapMatrix d A y) where
  nonneg i j := snap_nonneg d (A i j) y
  sum_le_one i := (Finset.sum_le_sum fun j _ => snap_le d (h0 i j) y).trans (h1 i)
  dyadic i j := exists_snap_eq d (A i j) y

end Cslib.Probability.SaksZhou
