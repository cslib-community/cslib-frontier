/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StableMatching.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The fractional stable matching polytope

Vande Vate [VandeVate1989] and Rothblum [Rothblum1992] gave an explicit linear-inequality
description of the convex hull of stable matchings of a one-to-one market `I : Instance n`,
presented in [SchummerVohra2007], Section 10.4.2, pp. 260–261 (Theorem 10.15, p. 261), with a short
geometric threshold rounding proof due to Teo and Sethuraman [TeoSethuraman1998].

A real `n × n` matrix `x : Fin n → Fin n → ℝ` lies in `I.stablePolytope` (`I.IsFractionalStable x`)
when it is doubly stochastic (`0 ≤ x p r`, row sums `1`, column sums `1`) and satisfies the
fractional blocking inequalities

`1 ≤ x p r + (∑ r' with I.PropPrefers p r' r, x p r') + (∑ p' with I.RecvPrefers r p' p, x p' r)`

for every proposer `p` and receiver `r` (under `∑ r', x p r' = 1` and `∑ p', x p' r = 1`, this
*better-partner* inequality is algebraically equivalent to the complementary *worse-partner*
inequality `(∑ r' with I.PropPrefers p r r', x p r') + (∑ p' with I.RecvPrefers r p p', x p' r) +
x p r ≤ 1` printed on p. 261 of [SchummerVohra2007]). We prove:

1. Integral `{0, 1}` incidence matrices in `I.stablePolytope` are precisely the stable matchings
   (`matchingMatrix_mem_stablePolytope_iff`).
2. Every positive entry `0 < x p r` of `x ∈ I.stablePolytope` satisfies the fractional blocking
   inequality with equality (`eq_one_of_mem_stablePolytope_of_pos`).
3. **Theorem 10.15** ([SchummerVohra2007], Section 10.4.2, p. 261; [VandeVate1989]; [Rothblum1992];
   [TeoSethuraman1998]): `I.stablePolytope` equals the convex hull of the incidence matrices of
   stable matchings (`stablePolytope_eq_convexHull`), and its extreme points are precisely the
   incidence matrices of stable matchings (`extremePoints_stablePolytope`).

## Main definitions

* `Cslib.Algorithms.Lean.StableMatching.matchingMatrix`: `{0, 1}` incidence matrix of
  `μ : Matching n`.
* `Instance.propBetterMass`, `Instance.recvBetterMass`: fractional mass strictly preferred by `p`
  to `r` (respectively by `r` to `p`).
* `Instance.IsFractionalStable`, `Instance.stablePolytope`: the fractional stable matching polytope.

## Main results

* `Instance.matchingMatrix_mem_stablePolytope_iff`:
  `matchingMatrix μ ∈ I.stablePolytope ↔ I.IsStable μ`.
* `Instance.eq_one_of_mem_stablePolytope_of_pos`: tight blocking equality on positive support.
* `Instance.stablePolytope_eq_convexHull`:
  `I.stablePolytope = convexHull ℝ (matchingMatrix '' {μ | I.IsStable μ})`.
* `Instance.extremePoints_stablePolytope`:
  `I.stablePolytope.extremePoints ℝ = matchingMatrix '' {μ | I.IsStable μ}`.

## References

* [VandeVate1989] (primary PDF unverified; cited via [SchummerVohra2007])
* [Rothblum1992] (primary PDF unverified)
* [TeoSethuraman1998] (primary PDF unverified; cited via [SchummerVohra2007])
* [SchummerVohra2007], Section 10.4.2, Theorem 10.15, pp. 260–261
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

/-- The `{0, 1}` incidence matrix of a matching `μ : Matching n`. -/
@[expose] def matchingMatrix {n : ℕ} (μ : Matching n) (p r : Fin n) : ℝ :=
  if μ p = r then 1 else 0

theorem matchingMatrix_injective {n : ℕ} : Function.Injective (matchingMatrix (n := n)) := by
  intro μ ν h
  refine Equiv.ext fun p => ?_
  have hp := congrFun (congrFun h p) (μ p)
  simp only [matchingMatrix, ↓reduceIte] at hp
  by_contra hne
  simp only [ite_eq_right (Ne.symm hne)] at hp
  linarith

private theorem matchingMatrix_nonneg {n : ℕ} (μ : Matching n) (p r : Fin n) :
    0 ≤ matchingMatrix μ p r := by
  unfold matchingMatrix
  split_ifs <;> norm_num

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- Total fractional mass proposer `p` places on receivers strictly preferred to `r`. -/
@[expose] def propBetterMass (x : Fin n → Fin n → ℝ) (p r : Fin n) : ℝ :=
  ∑ r' with I.propRank p r' < I.propRank p r, x p r'

/-- Total fractional mass receiver `r` receives from proposers strictly preferred to `p`. -/
@[expose] def recvBetterMass (x : Fin n → Fin n → ℝ) (r p : Fin n) : ℝ :=
  ∑ p' with I.recvRank r p' < I.recvRank r p, x p' r

/-- A matrix `x : Fin n → Fin n → ℝ` is a **fractional stable matching** ([VandeVate1989];
[Rothblum1992]; [SchummerVohra2007], Section 10.4.2, p. 261) if it is doubly stochastic and
satisfies the fractional non-blocking inequality at every pair `(p, r)` (equivalent under row and
column sums `1` to the complementary worse-partner inequality `≤ 1` on p. 261 of
[SchummerVohra2007]). -/
@[expose] def IsFractionalStable (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ p r, 0 ≤ x p r) ∧
  (∀ p, ∑ r, x p r = 1) ∧
  (∀ r, ∑ p, x p r = 1) ∧
  (∀ p r, 1 ≤ x p r + I.propBetterMass x p r + I.recvBetterMass x r p)

/-- The **fractional stable matching polytope** of `I` ([VandeVate1989]; [Rothblum1992];
[SchummerVohra2007], Section 10.4.2, Theorem 10.15, p. 261). -/
@[expose] def stablePolytope : Set (Fin n → Fin n → ℝ) :=
  {x | I.IsFractionalStable x}

theorem entry_le_one_of_mem_stablePolytope {x : Fin n → Fin n → ℝ} (hx : x ∈ I.stablePolytope)
    (p r : Fin n) : x p r ≤ 1 :=
  calc
    x p r ≤ ∑ r' : Fin n, x p r' :=
      Finset.single_le_sum (fun r' _ => hx.1 p r') (Finset.mem_univ r)
    _ = 1 := hx.2.1 p

/-- The fractional stable matching polytope is convex. -/
theorem convex_stablePolytope : Convex ℝ I.stablePolytope := by
  rintro x ⟨hx_nn, hx_row, hx_col, hx_stab⟩ y ⟨hy_nn, hy_row, hy_col, hy_stab⟩ a b ha hb hab
  refine ⟨fun p r => add_nonneg (mul_nonneg ha (hx_nn p r)) (mul_nonneg hb (hy_nn p r)),
    fun p => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx_row p, hy_row p, mul_one, hab],
    fun r => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx_col r, hy_col r, mul_one, hab], fun p r => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, propBetterMass, recvBetterMass,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := mul_le_mul_of_nonneg_left (hx_stab p r) ha
  have h2 := mul_le_mul_of_nonneg_left (hy_stab p r) hb
  simp only [propBetterMass, recvBetterMass] at h1 h2
  linarith

/-! ### Incidence matrices of stable matchings -/

/-- The `{0, 1}` matrix `matchingMatrix μ` belongs to `I.stablePolytope` if and only if `μ` is a
stable matching. -/
theorem matchingMatrix_mem_stablePolytope_iff (μ : Matching n) :
    matchingMatrix μ ∈ I.stablePolytope ↔ I.IsStable μ := by
  constructor
  · rintro ⟨-, -, -, hstab⟩ p r ⟨hp, hr⟩
    have h0 : matchingMatrix μ p r = 0 :=
      ite_eq_right fun h => (ne_of_lt hp) (congrArg (I.propRank p) h.symm)
    have hp0 : I.propBetterMass (matchingMatrix μ) p r = 0 :=
      Finset.sum_eq_zero fun r' hr' => ite_eq_right fun h =>
        not_lt_of_ge (h ▸ (Finset.mem_filter.1 hr').2).le hp
    have hr0 : I.recvBetterMass (matchingMatrix μ) r p = 0 :=
      Finset.sum_eq_zero fun p' hp' => ite_eq_right fun h =>
        not_lt_of_ge ((show p' = μ.symm r by rw [← h, Equiv.symm_apply_apply]) ▸
          (Finset.mem_filter.1 hp').2).le hr
    linarith [hstab p r]
  · intro hstab
    refine ⟨matchingMatrix_nonneg μ, fun p => by simp [matchingMatrix], fun r => ?_, fun p r => ?_⟩
    · have hsum : (∑ p : Fin n, matchingMatrix μ p r) =
          ∑ p : Fin n, if p = μ.symm r then 1 else 0 :=
        Finset.sum_congr rfl fun p _ => by simp only [matchingMatrix, ← Equiv.eq_symm_apply]
      simp [hsum]
    · have h0 : 0 ≤ matchingMatrix μ p r := matchingMatrix_nonneg μ p r
      have hp_nn : 0 ≤ I.propBetterMass (matchingMatrix μ) p r :=
        Finset.sum_nonneg fun r' _ => matchingMatrix_nonneg μ p r'
      have hr_nn : 0 ≤ I.recvBetterMass (matchingMatrix μ) r p :=
        Finset.sum_nonneg fun p' _ => matchingMatrix_nonneg μ p' r
      by_cases hpr : μ p = r
      · have h1 : matchingMatrix μ p r = 1 := ite_eq_left hpr
        linarith
      · by_cases hp : I.PropPrefers p (μ p) r
        · have hp1 : 1 ≤ I.propBetterMass (matchingMatrix μ) p r :=
            calc
              (1 : ℝ) = matchingMatrix μ p (μ p) := by simp [matchingMatrix]
              _ ≤ I.propBetterMass (matchingMatrix μ) p r :=
                Finset.single_le_sum (fun r' _ => matchingMatrix_nonneg μ p r')
                  (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩)
          linarith
        · have hp_lt : I.PropPrefers p r (μ p) :=
            lt_of_le_of_ne (le_of_not_gt hp) fun h => hpr (I.propRank_injective p h).symm
          have hr_lt : I.RecvPrefers r (μ.symm r) p :=
            lt_of_le_of_ne (le_of_not_gt fun hr => hstab p r ⟨hp_lt, hr⟩)
              fun h => hpr (by rw [← I.recvRank_injective r h, Equiv.apply_symm_apply])
          have hr1 : 1 ≤ I.recvBetterMass (matchingMatrix μ) r p :=
            calc
              (1 : ℝ) = matchingMatrix μ (μ.symm r) r := by simp [matchingMatrix]
              _ ≤ I.recvBetterMass (matchingMatrix μ) r p :=
                Finset.single_le_sum (fun p' _ => matchingMatrix_nonneg μ p' r)
                  (Finset.mem_filter.2 ⟨Finset.mem_univ _, hr_lt⟩)
          linarith

/-! ### Quadratic slackness identity on positive support -/

private theorem sum_mul_strictLower_eq {α : Type*} [Fintype α]
    {rk : α → Fin n} (hrk : Function.Injective rk) (y : α → ℝ) :
    2 * (∑ a : α, y a * (∑ b with rk b < rk a, y b)) + ∑ a : α, y a ^ 2 =
      (∑ a : α, y a) ^ 2 := by
  classical
  have hpt (a b : α) : y a * y b =
      (if rk b < rk a then y a * y b else 0) + (if rk a < rk b then y b * y a else 0) +
      (if a = b then y a ^ 2 else 0) := by
    rcases lt_trichotomy (rk a) (rk b) with hlt | heq | hgt
    · have hne : a ≠ b := fun h => (ne_of_lt hlt) (congrArg rk h)
      simp only [not_lt_of_gt hlt, hlt, hne, ↓reduceIte]; ring
    · obtain rfl := hrk heq
      simp only [lt_irrefl, ↓reduceIte]
      ring
    · have hne : a ≠ b := fun h => (ne_of_gt hgt) (congrArg rk h)
      simp only [hgt, not_lt_of_gt hgt, hne, ↓reduceIte]; ring
  have hL : (∑ a : α, ∑ b : α, if rk b < rk a then y a * y b else 0) =
      ∑ a : α, y a * (∑ b with rk b < rk a, y b) :=
    Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_filter, Finset.mul_sum]
  have hL2 : (∑ a : α, ∑ b : α, if rk a < rk b then y b * y a else 0) =
      ∑ a : α, y a * (∑ b with rk b < rk a, y b) := by
        rw [Finset.sum_comm]
        exact hL
  have hD : (∑ a : α, ∑ b : α, if a = b then y a ^ 2 else 0) = ∑ a : α, y a ^ 2 :=
    Finset.sum_congr rfl fun a _ => by simp
  calc
    2 * (∑ a : α, y a * (∑ b with rk b < rk a, y b)) + ∑ a : α, y a ^ 2
      = (∑ a : α, ∑ b : α, if rk b < rk a then y a * y b else 0) +
          (∑ a : α, ∑ b : α, if rk a < rk b then y b * y a else 0) +
          (∑ a : α, ∑ b : α, if a = b then y a ^ 2 else 0) := by
        rw [hL, hL2, hD]
        ring
    _ = ∑ a : α, ∑ b : α, y a * y b := by
        simp_rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (hpt a b).symm
    _ = (∑ a : α, y a) ^ 2 := by
        rw [sq, Finset.sum_mul]
        exact (Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _).symm

/-- Complementary-slackness identity ([Rothblum1992]; [TeoSethuraman1998]): for any
`x ∈ I.stablePolytope` and any pair `(p, r)` with `0 < x p r`, the fractional blocking inequality at
`(p, r)` holds with equality. -/
theorem eq_one_of_mem_stablePolytope_of_pos {x : Fin n → Fin n → ℝ} (hx : x ∈ I.stablePolytope)
    {p r : Fin n} (hpos : 0 < x p r) :
    x p r + I.propBetterMass x p r + I.recvBetterMass x r p = 1 := by
  rcases hx with ⟨hnn, hrow, hcol, hstab⟩
  have hsum_rows :
      2 * (∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ * I.propBetterMass x p₀ r₀) +
        ∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ ^ 2 = (n : ℝ) := by
    have h := Finset.sum_congr rfl fun p₀ (_ : p₀ ∈ Finset.univ) =>
      (sum_mul_strictLower_eq (I.propRank_injective p₀) (x p₀)).trans (by rw [hrow p₀, one_pow])
    simpa only [propBetterMass, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using h
  have hsum_cols :
      2 * (∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ * I.recvBetterMass x r₀ p₀) +
        ∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ ^ 2 = (n : ℝ) := by
    have h := Finset.sum_congr rfl fun r₀ (_ : r₀ ∈ Finset.univ) =>
      (sum_mul_strictLower_eq (I.recvRank_injective r₀) (fun p₀ => x p₀ r₀)).trans
        (by rw [hcol r₀, one_pow])
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    rw [Finset.sum_comm (f := fun p₀ r₀ => x p₀ r₀ * I.recvBetterMass x r₀ p₀),
      Finset.sum_comm (f := fun p₀ r₀ => x p₀ r₀ ^ 2)]
    exact h
  have hsum_ones : ∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ = (n : ℝ) := by
    simp [hrow]
  have hzero_slack :
      ∑ p₀ : Fin n, ∑ r₀ : Fin n,
        x p₀ r₀ * (x p₀ r₀ + I.propBetterMass x p₀ r₀ + I.recvBetterMass x r₀ p₀ - 1) = 0 := by
    have hexpand :
        2 * (∑ p₀ : Fin n, ∑ r₀ : Fin n,
          x p₀ r₀ * (x p₀ r₀ + I.propBetterMass x p₀ r₀ + I.recvBetterMass x r₀ p₀ - 1)) =
        (2 * (∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ * I.propBetterMass x p₀ r₀) +
          ∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ ^ 2) +
        (2 * (∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ * I.recvBetterMass x r₀ p₀) +
          ∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ ^ 2) -
        2 * (∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀) := by
      have hpt (p₀ r₀ : Fin n) :
          2 * (x p₀ r₀ * (x p₀ r₀ + I.propBetterMass x p₀ r₀ + I.recvBetterMass x r₀ p₀ - 1)) =
            2 * (x p₀ r₀ * I.propBetterMass x p₀ r₀) + x p₀ r₀ ^ 2 +
              (2 * (x p₀ r₀ * I.recvBetterMass x r₀ p₀) + x p₀ r₀ ^ 2) - 2 * x p₀ r₀ := by
        ring
      simp only [Finset.mul_sum]
      simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith
  have hterm_nn (p₀ r₀ : Fin n) :
      0 ≤ x p₀ r₀ * (x p₀ r₀ + I.propBetterMass x p₀ r₀ + I.recvBetterMass x r₀ p₀ - 1) :=
    mul_nonneg (hnn p₀ r₀) (sub_nonneg.2 (hstab p₀ r₀))
  have hrow_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun p₀ _ =>
    Finset.sum_nonneg fun r₀ _ => hterm_nn p₀ r₀)).1 hzero_slack p (Finset.mem_univ p)
  have hpr_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun r₀ _ => hterm_nn p r₀)).1
    hrow_zero r (Finset.mem_univ r)
  rcases mul_eq_zero.1 hpr_zero with hx0 | hslack <;> linarith

/-! ### Threshold rounding and Teo–Sethuraman convex decomposition -/

private theorem strictLower_add_le {α : Type*} [Fintype α]
    {rk : α → Fin n} {y : α → ℝ} (hy : ∀ c, 0 ≤ y c) {a b : α} (hab : rk a < rk b) :
    (∑ c with rk c < rk a, y c) + y a ≤ ∑ c with rk c < rk b, y c := by
  classical
  have hnot_mem : a ∉ Finset.univ.filter (fun c => rk c < rk a) := by
    simp
  rw [add_comm, ← Finset.sum_insert hnot_mem]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun c _ _ => hy c)
  intro c hc
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  rcases hc with rfl | hca
  · exact hab
  · exact hca.trans hab

private theorem exists_threshold_receiver (hn : 0 < n) {x : Fin n → Fin n → ℝ}
    (hx : x ∈ I.stablePolytope) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hbp : ∀ p r, t ≠ I.propBetterMass x p r ∧ t ≠ I.propBetterMass x p r + x p r)
    (p : Fin n) :
    ∃ r : Fin n, I.propBetterMass x p r < t ∧ t < I.propBetterMass x p r + x p r := by
  rcases hx with ⟨hnn, hrow, -, -⟩
  let S : Finset (Fin n) := Finset.univ.filter fun r => I.propBetterMass x p r < t
  have hSne : S.Nonempty := ⟨I.propPref p ⟨0, hn⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by
    have hzero : I.propBetterMass x p (I.propPref p ⟨0, hn⟩) = 0 :=
      Finset.sum_eq_zero fun r' hr' => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, propRank_propPref] at hr'
        exact False.elim (Nat.not_lt_zero _ hr')
    linarith⟩⟩
  let kMax : Fin n := (S.image (I.propRank p)).max' (hSne.image _)
  let rStar : Fin n := I.propPref p kMax
  obtain ⟨r', hr'S, hr'eq⟩ := Finset.mem_image.1 (Finset.max'_mem (S.image (I.propRank p)) _)
  have hrStar_eq : rStar = r' := by
    dsimp only [rStar, kMax]
    rw [← hr'eq, propPref_propRank]
  have hlt_low : I.propBetterMass x p rStar < t := by
    rw [hrStar_eq]
    exact (Finset.mem_filter.1 hr'S).2
  refine ⟨rStar, hlt_low, ?_⟩
  by_contra hnot_gt
  have hlt_high : I.propBetterMass x p rStar + x p rStar < t :=
    lt_of_le_of_ne (le_of_not_gt hnot_gt) (hbp p rStar).2.symm
  have hnot_in : rStar ∉ Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p rStar) :=
    fun h => lt_irrefl _ (Finset.mem_filter.1 h).2
  have hmem_ins (r' : Fin n) :
      r' ∈ insert rStar (Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p rStar)) ↔
        (I.propRank p r').val < kMax.val + 1 := by
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
      rStar, propRank_propPref, Nat.lt_succ_iff, Nat.le_iff_lt_or_eq, Fin.lt_def]
    exact ⟨fun h => h.elim (fun h' => Or.inr (by rw [h', propRank_propPref])) Or.inl,
      fun h => h.elim Or.inr fun h' => Or.inl (by rw [← Fin.ext h', propPref_propRank])⟩
  by_cases hk_lt : kMax.val + 1 < n
  · let rNext : Fin n := I.propPref p ⟨kMax.val + 1, hk_lt⟩
    have hfilter_eq :
        Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p rNext) =
          insert rStar (Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p rStar)) := by
      ext r'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, rNext, propRank_propPref, hmem_ins]
      rfl
    have hmass_next : I.propBetterMass x p rNext = I.propBetterMass x p rStar + x p rStar := by
      rw [propBetterMass, hfilter_eq, Finset.sum_insert hnot_in, propBetterMass, add_comm]
    have hkNext_le : (⟨kMax.val + 1, hk_lt⟩ : Fin n) ≤ kMax := by
      simpa only [rNext, propRank_propPref] using
        Finset.le_max' (S.image (I.propRank p)) (I.propRank p rNext)
          (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩))
    exact Nat.not_succ_le_self kMax.val hkNext_le
  · have hfilter_univ :
        insert rStar (Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p rStar)) =
          Finset.univ := by
      ext r'
      simp only [hmem_ins, Finset.mem_univ, iff_true]
      have := (I.propRank p r').isLt
      omega
    have hsum_one : I.propBetterMass x p rStar + x p rStar = 1 := by
      rw [add_comm, propBetterMass, ← Finset.sum_insert hnot_in, hfilter_univ, hrow p]
    linarith

private theorem sum_fin_sub_telescope :
    ∀ {m : ℕ} (f : Fin (m + 1) → ℝ) (ia ib : Fin (m + 1)), ia ≤ ib →
      (∑ k : Fin m, if ia.val ≤ k.val ∧ k.val < ib.val then f k.succ - f k.castSucc else 0) =
        f ib - f ia := by
  intro m f ia ib hle
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Fin.le_def.1 hle)
  induction d generalizing ib with
  | zero =>
    obtain rfl : ib = ia := Fin.ext (by omega)
    rw [Finset.sum_eq_zero fun k _ => ite_eq_right (by omega), sub_self]
  | succ d ih =>
    let ib' : Fin (m + 1) := ⟨ia.val + d, by omega⟩
    let k₀ : Fin m := ⟨ia.val + d, by omega⟩
    have hsplit (k : Fin m) :
        (if ia.val ≤ k.val ∧ k.val < ib.val then f k.succ - f k.castSucc else 0) =
          (if ia.val ≤ k.val ∧ k.val < ib'.val then f k.succ - f k.castSucc else 0) +
            (if k = k₀ then f k.succ - f k.castSucc else 0) := by
      by_cases hk : k = k₀
      · subst hk
        simp only [k₀, ib', show ia.val ≤ ia.val + d ∧ ia.val + d < ib.val by omega,
          and_self, ↓reduceIte, lt_irrefl, and_false, zero_add]
      · have hne : k.val ≠ ia.val + d := fun h => hk (Fin.ext h)
        by_cases h1 : ia.val ≤ k.val ∧ k.val < ib'.val
        · simp [h1, show ia.val ≤ k.val ∧ k.val < ib.val by dsimp [ib'] at h1; omega, hk]
        · simp [h1, show ¬ (ia.val ≤ k.val ∧ k.val < ib.val) by dsimp [ib'] at h1; omega, hk]
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [ih ib' (Nat.le_add_right ia.val d) rfl, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte,
      show k₀.succ = ib from Fin.ext (by dsimp [k₀]; omega),
      show k₀.castSucc = ib' from Fin.ext rfl]
    ring

/-- **Theorem 10.15** ([SchummerVohra2007], Section 10.4.2, p. 261; [VandeVate1989]; [Rothblum1992];
[TeoSethuraman1998]): the fractional stable matching polytope `I.stablePolytope` equals the convex
hull of the `{0, 1}` incidence matrices of stable matchings of `I`. -/
theorem stablePolytope_eq_convexHull :
    I.stablePolytope = convexHull ℝ (matchingMatrix '' {μ : Matching n | I.IsStable μ}) := by
  refine Set.Subset.antisymm ?_
    (convexHull_min (fun _ ⟨μ, h, hx⟩ => hx ▸ (I.matchingMatrix_mem_stablePolytope_iff μ).2 h)
      I.convex_stablePolytope)
  intro x hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show x = matchingMatrix (Equiv.refl (Fin 0)) from funext fun p => Fin.elim0 p]
    exact subset_convexHull ℝ _ ⟨Equiv.refl (Fin 0), fun p => Fin.elim0 p, rfl⟩
  · classical
    obtain ⟨hx_nn, hx_row, hx_col, hx_stab⟩ := hx
    -- Finite breakpoint set containing 0, 1, all P p r, and all P p r + x p r.
    let bpLow : Finset ℝ :=
      Finset.univ.biUnion fun p => Finset.univ.image fun r => I.propBetterMass x p r
    let bpHigh : Finset ℝ :=
      Finset.univ.biUnion fun p => Finset.univ.image fun r => I.propBetterMass x p r + x p r
    let B : Finset ℝ := insert 0 (insert 1 (bpLow ∪ bpHigh))
    have h0B : (0 : ℝ) ∈ B := Finset.mem_insert_self _ _
    have h1B : (1 : ℝ) ∈ B := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hlow_B (p r : Fin n) : I.propBetterMass x p r ∈ B :=
      Finset.mem_insert_of_mem <| Finset.mem_insert_of_mem <| Finset.mem_union_left _ <|
        Finset.mem_biUnion.2 ⟨p, Finset.mem_univ p, Finset.mem_image_of_mem _ (Finset.mem_univ r)⟩
    have hhigh_B (p r : Fin n) : I.propBetterMass x p r + x p r ∈ B :=
      Finset.mem_insert_of_mem <| Finset.mem_insert_of_mem <| Finset.mem_union_right _ <|
        Finset.mem_biUnion.2 ⟨p, Finset.mem_univ p, Finset.mem_image_of_mem _ (Finset.mem_univ r)⟩
    have hB_bounds (y : ℝ) (hy : y ∈ B) : 0 ≤ y ∧ y ≤ 1 := by
      simp only [B, bpLow, bpHigh, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_univ, true_and, Finset.mem_image] at hy
      rcases hy with rfl | rfl | ⟨p, r, rfl⟩ | ⟨p, r, rfl⟩
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨zero_le_one, le_rfl⟩
      · refine ⟨Finset.sum_nonneg fun r' _ => hx_nn p r', ?_⟩
        calc
          I.propBetterMass x p r ≤ ∑ r' : Fin n, x p r' :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun r' _ _ => hx_nn p r'
          _ = 1 := hx_row p
      · refine ⟨add_nonneg (Finset.sum_nonneg fun r' _ => hx_nn p r') (hx_nn p r), ?_⟩
        have hnot_in : r ∉ Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p r) :=
          fun h => lt_irrefl _ (Finset.mem_filter.1 h).2
        rw [add_comm, propBetterMass, ← Finset.sum_insert hnot_in]
        calc
          (∑ r' ∈ insert r (Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p r)),
              x p r') ≤ ∑ r' : Fin n, x p r' :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun r' _ _ => hx_nn p r'
          _ = 1 := hx_row p
    have hB_card_ge : 2 ≤ B.card := by
      have hsub : ({0, 1} : Finset ℝ) ⊆ B := fun y hy => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption
      exact (by norm_num : ({0, 1} : Finset ℝ).card = 2) ▸ Finset.card_le_card hsub
    let m : ℕ := B.card - 1
    have hB_card : B.card = m + 1 := by omega
    let e : Fin (m + 1) ↪o ℝ := B.orderEmbOfFin hB_card
    have hmem_e {y : ℝ} (hy : y ∈ B) : y ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hy
    have he0 : e ⟨0, Nat.succ_pos m⟩ = 0 := by
      rw [Finset.orderEmbOfFin_zero hB_card (Nat.succ_pos m)]
      exact le_antisymm (Finset.min'_le B 0 h0B) (hB_bounds _ (Finset.min'_mem B _)).1
    have heLast : e (Fin.last m) = 1 := by
      rw [show (Fin.last m : Fin (m + 1)) = ⟨m + 1 - 1, by omega⟩ from rfl,
        Finset.orderEmbOfFin_last hB_card (Nat.succ_pos m)]
      exact le_antisymm (hB_bounds _ (Finset.max'_mem B _)).2 (Finset.le_max' B 1 h1B)
    let w : Fin m → ℝ := fun k => e k.succ - e k.castSucc
    let mid : Fin m → ℝ := fun k => (e k.castSucc + e k.succ) / 2
    have hw_pos (k : Fin m) : 0 < w k := sub_pos.2 (e.strictMono k.castSucc_lt_succ)
    have hmid_gt (k : Fin m) : e k.castSucc < mid k := by
      have := e.strictMono k.castSucc_lt_succ
      dsimp only [mid]
      linarith
    have hmid_lt (k : Fin m) : mid k < e k.succ := by
      have := e.strictMono k.castSucc_lt_succ
      dsimp only [mid]
      linarith
    have hmid_not_B (k : Fin m) : mid k ∉ B := fun hmem => by
      obtain ⟨j, hj⟩ := hmem_e hmem
      have : k.val < j.val := e.lt_iff_lt.1 (hj ▸ hmid_gt k)
      have : j.val < k.val + 1 := e.lt_iff_lt.1 (hj ▸ hmid_lt k)
      omega
    have hmid_01 (k : Fin m) : 0 < mid k ∧ mid k < 1 :=
      ⟨lt_of_le_of_lt (he0 ▸ e.monotone (Fin.zero_le _)) (hmid_gt k),
       lt_of_lt_of_le (hmid_lt k) (heLast ▸ e.monotone (Fin.le_last _))⟩
    -- For each midpoint mid k, construct the threshold matching μ_k and prove stability.
    choose f hf using fun (k : Fin m) (p : Fin n) =>
      I.exists_threshold_receiver hn ⟨hx_nn, hx_row, hx_col, hx_stab⟩
        (hmid_01 k).1 (hmid_01 k).2
        (fun p' r' => ⟨fun h => hmid_not_B k (h ▸ hlow_B p' r'),
          fun h => hmid_not_B k (h ▸ hhigh_B p' r')⟩) p
    have hf_recv (k : Fin m) (p : Fin n) :
        I.recvBetterMass x (f k p) p < 1 - mid k ∧
          1 - mid k < I.recvBetterMass x (f k p) p + x p (f k p) := by
      have heq1 := I.eq_one_of_mem_stablePolytope_of_pos ⟨hx_nn, hx_row, hx_col, hx_stab⟩
        (by linarith [(hf k p).1, (hf k p).2])
      exact ⟨by linarith [(hf k p).2], by linarith [(hf k p).1]⟩
    have hf_inj (k : Fin m) : Function.Injective (f k) := fun p₁ p₂ heq => by
      by_contra hpne
      have hr1 := heq ▸ hf_recv k p₁
      have hr2 := hf_recv k p₂
      rcases lt_or_gt_of_ne (fun hrk => hpne (I.recvRank_injective (f k p₂) hrk)) with hlt | hgt
      · have hle : I.recvBetterMass x (f k p₂) p₁ + x p₁ (f k p₂) ≤
            I.recvBetterMass x (f k p₂) p₂ := strictLower_add_le (fun p' => hx_nn p' _) hlt
        linarith [hr1.2, hr2.1]
      · have hle : I.recvBetterMass x (f k p₂) p₂ + x p₂ (f k p₂) ≤
            I.recvBetterMass x (f k p₂) p₁ := strictLower_add_le (fun p' => hx_nn p' _) hgt
        linarith [hr2.2, hr1.1]
    let μ : Fin m → Matching n := fun k => permOfInjective (f k) (hf_inj k)
    have hμ_stab (k : Fin m) : I.IsStable (μ k) := fun p r ⟨hp_pref, hr_pref⟩ => by
      have hp_le : I.propBetterMass x p r + x p r ≤ I.propBetterMass x p (f k p) :=
        strictLower_add_le (fun r' => hx_nn p r') hp_pref
      let pStar : Fin n := (μ k).symm r
      have hr_le : I.recvBetterMass x r p + x p r ≤ I.recvBetterMass x r pStar :=
        strictLower_add_le (fun p' => hx_nn p' r) hr_pref
      have hr_pStar := hf_recv k pStar
      have hpStar_f : f k pStar = r := (μ k).apply_symm_apply r
      rw [hpStar_f] at hr_pStar
      linarith [(hf k p).1, hr_pStar.1, hx_stab p r, hx_nn p r]
    have hμ_iff (k : Fin m) (p r : Fin n) :
        μ k p = r ↔ (I.propBetterMass x p r < mid k ∧ mid k < I.propBetterMass x p r + x p r) := by
      change f k p = r ↔ _
      refine ⟨fun h => h ▸ hf k p, fun hr_int => ?_⟩
      by_contra hne
      rcases lt_or_gt_of_ne (fun hrk => hne (I.propRank_injective p hrk)) with hlt | hgt
      · have hle : I.propBetterMass x p (f k p) + x p (f k p) ≤ I.propBetterMass x p r :=
          strictLower_add_le (fun r' => hx_nn p r') hlt
        linarith [(hf k p).2, hr_int.1]
      · have hle : I.propBetterMass x p r + x p r ≤ I.propBetterMass x p (f k p) :=
          strictLower_add_le (fun r' => hx_nn p r') hgt
        linarith [hr_int.2, (hf k p).1]
    have hw_sum : ∑ k : Fin m, w k = 1 := by
      have htel := sum_fin_sub_telescope e ⟨0, Nat.succ_pos m⟩ (Fin.last m) (Fin.zero_le _)
      simpa only [Fin.val_zero, Fin.val_last, Nat.zero_le, Fin.isLt, and_self, ↓reduceIte,
        heLast, he0, sub_zero] using htel
    have hx_decomp : ∑ k : Fin m, w k • matchingMatrix (μ k) = x := by
      ext p r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      obtain ⟨ia, hia⟩ := hmem_e (hlow_B p r)
      obtain ⟨ib, hib⟩ := hmem_e (hhigh_B p r)
      have hia_le_ib : ia ≤ ib := e.le_iff_le.1 (by linarith [hx_nn p r, hia, hib])
      have hterm (k : Fin m) : w k * matchingMatrix (μ k) p r =
          if ia.val ≤ k.val ∧ k.val < ib.val then e k.succ - e k.castSucc else 0 := by
        rw [matchingMatrix]
        simp only [hμ_iff k p r]
        rw [← hib, ← hia]
        by_cases hidx : ia.val ≤ k.val ∧ k.val < ib.val
        · have hint : e ia < mid k ∧ mid k < e ib :=
            ⟨lt_of_le_of_lt (e.monotone hidx.1) (hmid_gt k),
             lt_of_lt_of_le (hmid_lt k) (e.monotone (Nat.succ_le_of_lt hidx.2))⟩
          simp [hidx, hint, w]
        · have hnot_int : ¬ (e ia < mid k ∧ mid k < e ib) := fun ⟨h1, h2⟩ => hidx ⟨
            by by_contra h
               have := e.monotone (show k.succ ≤ ia from Nat.succ_le_of_lt (lt_of_not_ge h))
               linarith [hmid_lt k],
            by by_contra h
               have := e.monotone (show ib ≤ k.castSucc from le_of_not_gt h)
               linarith [hmid_gt k]⟩
          simp [hidx, hnot_int]
      simp_rw [hterm]
      rw [sum_fin_sub_telescope e ia ib hia_le_ib, hia, hib]; ring
    rw [← hx_decomp]
    exact (convex_convexHull ℝ _).sum_mem (fun k _ => (hw_pos k).le) hw_sum fun k _ =>
      subset_convexHull ℝ _ ⟨μ k, hμ_stab k, rfl⟩

/-- **Theorem 10.15 (Extreme-point integrality)** ([SchummerVohra2007], Section 10.4.2, p. 261;
[VandeVate1989]; [Rothblum1992]; [TeoSethuraman1998]): the extreme points of `I.stablePolytope` are
precisely the `{0, 1}` incidence matrices of stable matchings of `I`. -/
theorem extremePoints_stablePolytope :
    I.stablePolytope.extremePoints ℝ = matchingMatrix '' {μ : Matching n | I.IsStable μ} := by
  refine Set.Subset.antisymm (I.stablePolytope_eq_convexHull ▸ extremePoints_convexHull_subset) ?_
  rintro _ ⟨μ, hstab, rfl⟩
  refine ⟨(I.matchingMatrix_mem_stablePolytope_iff μ).2 hstab, ?_⟩
  rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hseg⟩
  ext p r
  have hval := congrFun (congrFun hseg p) r
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, matchingMatrix] at hval ⊢
  have hx₁_nn := hx₁.1 p r
  have hx₂_nn := hx₂.1 p r
  have hx₁_le := I.entry_le_one_of_mem_stablePolytope hx₁ p r
  have hx₂_le := I.entry_le_one_of_mem_stablePolytope hx₂ p r
  split_ifs at hval ⊢ <;> nlinarith

end Instance

end Cslib.Algorithms.Lean.StableMatching
