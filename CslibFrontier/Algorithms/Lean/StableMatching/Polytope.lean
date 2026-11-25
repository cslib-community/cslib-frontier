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
  have hzero : (if ν p = μ p then (1 : ℝ) else 0) = 0 :=
    ite_eq_right_iff.2 fun h' => (hne h'.symm).elim
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
    (p r : Fin n) : x p r ≤ 1 := by
  rcases hx with ⟨hnn, hrow, -, -⟩
  calc
    x p r ≤ ∑ r' : Fin n, x p r' :=
      Finset.single_le_sum (fun r' _ => hnn p r') (Finset.mem_univ r)
    _ = 1 := hrow p

/-- The fractional stable matching polytope is convex. -/
theorem convex_stablePolytope : Convex ℝ I.stablePolytope := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx_nn, hx_row, hx_col, hx_stab⟩
  rcases hy with ⟨hy_nn, hy_row, hy_col, hy_stab⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p r
    exact add_nonneg (mul_nonneg ha (hx_nn p r)) (mul_nonneg hb (hy_nn p r))
  · intro p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hx_row p, hy_row p, mul_one, hab]
  · intro r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hx_col r, hy_col r, mul_one, hab]
  · intro p r
    have hprop : I.propBetterMass (a • x + b • y) p r =
        a * I.propBetterMass x p r + b * I.propBetterMass y p r := by
      simp only [propBetterMass, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum]
    have hrecv : I.recvBetterMass (a • x + b • y) r p =
        a * I.recvBetterMass x r p + b * I.recvBetterMass y r p := by
      simp only [recvBetterMass, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hprop, hrecv]
    have h1 := mul_le_mul_of_nonneg_left (hx_stab p r) ha
    have h2 := mul_le_mul_of_nonneg_left (hy_stab p r) hb
    linarith

/-! ### Incidence matrices of stable matchings -/

/-- The `{0, 1}` matrix `matchingMatrix μ` belongs to `I.stablePolytope` if and only if `μ` is a
stable matching. -/
theorem matchingMatrix_mem_stablePolytope_iff (μ : Matching n) :
    matchingMatrix μ ∈ I.stablePolytope ↔ I.IsStable μ := by
  constructor
  · rintro ⟨-, -, -, hstab⟩ p r ⟨hp, hr⟩
    have h0 : matchingMatrix μ p r = 0 := by
      simp only [matchingMatrix, ite_eq_right_iff]
      intro h
      exact False.elim ((ne_of_lt hp) (congrArg (I.propRank p) h.symm))
    have hp0 : I.propBetterMass (matchingMatrix μ) p r = 0 := by
      refine Finset.sum_eq_zero fun r' hr' => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
      simp only [matchingMatrix, ite_eq_right_iff]
      intro h
      exact False.elim (not_lt_of_ge (h ▸ hr').le hp)
    have hr0 : I.recvBetterMass (matchingMatrix μ) r p = 0 := by
      refine Finset.sum_eq_zero fun p' hp' => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp'
      simp only [matchingMatrix, ite_eq_right_iff]
      intro h
      have hp'_eq : p' = μ.symm r := by rw [← h, Equiv.symm_apply_apply]
      exact False.elim (not_lt_of_ge (hp'_eq ▸ hp').le hr)
    have hineq := hstab p r
    linarith
  · intro hstab
    refine ⟨matchingMatrix_nonneg μ, ?_, ?_, ?_⟩
    · intro p
      simp [matchingMatrix]
    · intro r
      have hsum : (∑ p : Fin n, matchingMatrix μ p r) =
          ∑ p : Fin n, if p = μ.symm r then 1 else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [matchingMatrix]
        congr 1
        exact propext ⟨fun h => by rw [← h, Equiv.symm_apply_apply],
          fun h => by rw [h, Equiv.apply_symm_apply]⟩
      rw [hsum]
      simp
    · intro p r
      by_cases hpr : μ p = r
      · have h1 : matchingMatrix μ p r = 1 := by simp [matchingMatrix, hpr]
        have hp_nn : 0 ≤ I.propBetterMass (matchingMatrix μ) p r :=
          Finset.sum_nonneg fun r' _ => matchingMatrix_nonneg μ p r'
        have hr_nn : 0 ≤ I.recvBetterMass (matchingMatrix μ) r p :=
          Finset.sum_nonneg fun p' _ => matchingMatrix_nonneg μ p' r
        linarith
      · by_cases hp : I.PropPrefers p (μ p) r
        · have hp1 : 1 ≤ I.propBetterMass (matchingMatrix μ) p r := by
            have hmem : μ p ∈ Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p r) :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩
            calc
              (1 : ℝ) = matchingMatrix μ p (μ p) := by simp [matchingMatrix]
              _ ≤ I.propBetterMass (matchingMatrix μ) p r :=
                Finset.single_le_sum (f := fun r' => matchingMatrix μ p r')
                  (fun r' _ => matchingMatrix_nonneg μ p r') hmem
          have h0 : 0 ≤ matchingMatrix μ p r := matchingMatrix_nonneg μ p r
          have hr_nn : 0 ≤ I.recvBetterMass (matchingMatrix μ) r p :=
            Finset.sum_nonneg fun p' _ => matchingMatrix_nonneg μ p' r
          linarith
        · have hp_ge : I.propRank p r ≤ I.propRank p (μ p) := le_of_not_gt hp
          have hp_lt : I.PropPrefers p r (μ p) :=
            lt_of_le_of_ne hp_ge fun heq => hpr (I.propRank_injective p heq).symm
          have hnot_recv : ¬ I.RecvPrefers r p (μ.symm r) := fun hr => hstab p r ⟨hp_lt, hr⟩
          have hr_le : I.recvRank r (μ.symm r) ≤ I.recvRank r p := le_of_not_gt hnot_recv
          have hne_symm : μ.symm r ≠ p := fun heq => hpr (by rw [← heq, Equiv.apply_symm_apply])
          have hr_lt : I.RecvPrefers r (μ.symm r) p :=
            lt_of_le_of_ne hr_le fun heq => hne_symm (I.recvRank_injective r heq)
          have hr1 : 1 ≤ I.recvBetterMass (matchingMatrix μ) r p := by
            have hmem :
                μ.symm r ∈ Finset.univ.filter (fun p' => I.recvRank r p' < I.recvRank r p) :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, hr_lt⟩
            calc
              (1 : ℝ) = matchingMatrix μ (μ.symm r) r := by
                simp [matchingMatrix, Equiv.apply_symm_apply]
              _ ≤ I.recvBetterMass (matchingMatrix μ) r p :=
                Finset.single_le_sum (f := fun p' => matchingMatrix μ p' r)
                  (fun p' _ => matchingMatrix_nonneg μ p' r) hmem
          have h0 : 0 ≤ matchingMatrix μ p r := matchingMatrix_nonneg μ p r
          have hp_nn : 0 ≤ I.propBetterMass (matchingMatrix μ) p r :=
            Finset.sum_nonneg fun r' _ => matchingMatrix_nonneg μ p r'
          linarith

/-! ### Quadratic slackness identity on positive support -/

private theorem sum_mul_strictLower_eq {α : Type*} [Fintype α]
    {rk : α → Fin n} (hrk : Function.Injective rk) (y : α → ℝ) :
    2 * (∑ a : α, y a * (∑ b with rk b < rk a, y b)) + ∑ a : α, y a ^ 2 =
      (∑ a : α, y a) ^ 2 := by
  classical
  have hpt : ∀ a b : α,
      2 * (y a * y b) =
        (if rk b < rk a then 2 * (y a * y b) else 0) +
        (if rk a < rk b then 2 * (y b * y a) else 0) +
        (if a = b then 2 * y a ^ 2 else 0) := by
    intro a b
    rcases lt_trichotomy (rk a) (rk b) with hlt | heq | hgt
    · have hnot : ¬ rk b < rk a := not_lt_of_gt hlt
      have hne : a ≠ b := fun h => (ne_of_lt hlt) (congrArg rk h)
      simp only [hnot, hlt, hne, ↓reduceIte]
      ring
    · have hab : a = b := hrk heq
      subst hab
      simp only [lt_irrefl, ↓reduceIte]
      ring
    · have hnot : ¬ rk a < rk b := not_lt_of_gt hgt
      have hne : a ≠ b := fun h => (ne_of_gt hgt) (congrArg rk h)
      simp only [hgt, hnot, hne, ↓reduceIte]
      ring
  have hsum_sq : 2 * (∑ a : α, y a) ^ 2 = ∑ a : α, ∑ b : α, 2 * (y a * y b) := by
    rw [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have hL1 : (∑ a : α, ∑ b : α, if rk b < rk a then 2 * (y a * y b) else 0) =
      2 * ∑ a : α, y a * (∑ b with rk b < rk a, y b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  have hL2 : (∑ a : α, ∑ b : α, if rk a < rk b then 2 * (y b * y a) else 0) =
      2 * ∑ b : α, y b * (∑ a with rk a < rk b, y a) := by
    rw [Finset.sum_comm]
    exact hL1
  have hDiag : (∑ a : α, ∑ b : α, if a = b then 2 * y a ^ 2 else 0) =
      2 * ∑ a : α, y a ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hite := Finset.sum_ite_eq (Finset.univ : Finset α) a (fun _ => 2 * y a ^ 2)
    rw [hite, ite_eq_left_iff.2 fun h => (h (Finset.mem_univ a)).elim]
  have htot : 2 * (∑ a : α, y a) ^ 2 =
      4 * (∑ a : α, y a * (∑ b with rk b < rk a, y b)) + 2 * ∑ a : α, y a ^ 2 := by
    rw [hsum_sq]
    calc
      (∑ a : α, ∑ b : α, 2 * (y a * y b)) =
          (∑ a : α, ∑ b : α, if rk b < rk a then 2 * (y a * y b) else 0) +
          (∑ a : α, ∑ b : α, if rk a < rk b then 2 * (y b * y a) else 0) +
          (∑ a : α, ∑ b : α, if a = b then 2 * y a ^ 2 else 0) := by
        have hrew : (∑ a : α, ∑ b : α, 2 * (y a * y b)) =
            ∑ a : α, ∑ b : α,
              ((if rk b < rk a then 2 * (y a * y b) else 0) +
               (if rk a < rk b then 2 * (y b * y a) else 0) +
               (if a = b then 2 * y a ^ 2 else 0)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hpt a b
        rw [hrew]
        simp only [Finset.sum_add_distrib]
      _ = 4 * (∑ a : α, y a * (∑ b with rk b < rk a, y b)) + 2 * ∑ a : α, y a ^ 2 := by
        rw [hL1, hL2, hDiag]
        ring
  linarith

/-- Complementary-slackness identity ([Rothblum1992]; [TeoSethuraman1998]): for any
`x ∈ I.stablePolytope` and any pair `(p, r)` with `0 < x p r`, the fractional blocking inequality at
`(p, r)` holds with equality. -/
theorem eq_one_of_mem_stablePolytope_of_pos {x : Fin n → Fin n → ℝ} (hx : x ∈ I.stablePolytope)
    {p r : Fin n} (hpos : 0 < x p r) :
    x p r + I.propBetterMass x p r + I.recvBetterMass x r p = 1 := by
  rcases hx with ⟨hnn, hrow, hcol, hstab⟩
  have hrow_id : ∀ p₀ : Fin n,
      2 * (∑ r₀ : Fin n, x p₀ r₀ * I.propBetterMass x p₀ r₀) + ∑ r₀ : Fin n, x p₀ r₀ ^ 2 = 1 := by
    intro p₀
    have hid := sum_mul_strictLower_eq (I.propRank_injective p₀) (fun r₀ => x p₀ r₀)
    rw [hrow p₀, one_pow] at hid
    exact hid
  have hcol_id : ∀ r₀ : Fin n,
      2 * (∑ p₀ : Fin n, x p₀ r₀ * I.recvBetterMass x r₀ p₀) + ∑ p₀ : Fin n, x p₀ r₀ ^ 2 = 1 := by
    intro r₀
    have hid := sum_mul_strictLower_eq (I.recvRank_injective r₀) (fun p₀ => x p₀ r₀)
    rw [hcol r₀, one_pow] at hid
    exact hid
  have hsum_rows :
      2 * (∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ * I.propBetterMass x p₀ r₀) +
        ∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ ^ 2 = (n : ℝ) := by
    have h : (∑ p₀ : Fin n,
        (2 * (∑ r₀ : Fin n, x p₀ r₀ * I.propBetterMass x p₀ r₀) + ∑ r₀ : Fin n, x p₀ r₀ ^ 2)) =
        ∑ _p₀ : Fin n, (1 : ℝ) :=
      Finset.sum_congr rfl fun p₀ _ => hrow_id p₀
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    exact h
  have hsum_cols :
      2 * (∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ * I.recvBetterMass x r₀ p₀) +
        ∑ p₀ : Fin n, ∑ r₀ : Fin n, x p₀ r₀ ^ 2 = (n : ℝ) := by
    have h : (∑ r₀ : Fin n,
        (2 * (∑ p₀ : Fin n, x p₀ r₀ * I.recvBetterMass x r₀ p₀) + ∑ p₀ : Fin n, x p₀ r₀ ^ 2)) =
        ∑ _r₀ : Fin n, (1 : ℝ) :=
      Finset.sum_congr rfl fun r₀ _ => hcol_id r₀
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
      have hpt : ∀ p₀ r₀ : Fin n,
          2 * (x p₀ r₀ * (x p₀ r₀ + I.propBetterMass x p₀ r₀ + I.recvBetterMass x r₀ p₀ - 1)) =
            2 * (x p₀ r₀ * I.propBetterMass x p₀ r₀) + x p₀ r₀ ^ 2 +
              (2 * (x p₀ r₀ * I.recvBetterMass x r₀ p₀) + x p₀ r₀ ^ 2) - 2 * x p₀ r₀ := by
        intro p₀ r₀; ring
      simp only [Finset.mul_sum]
      simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith
  have hterm_nn : ∀ p₀ r₀ : Fin n,
      0 ≤ x p₀ r₀ * (x p₀ r₀ + I.propBetterMass x p₀ r₀ + I.recvBetterMass x r₀ p₀ - 1) := by
    intro p₀ r₀
    exact mul_nonneg (hnn p₀ r₀) (sub_nonneg.2 (hstab p₀ r₀))
  have hrow_zero :
      ∑ r₀ : Fin n,
        x p r₀ * (x p r₀ + I.propBetterMass x p r₀ + I.recvBetterMass x r₀ p - 1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun p₀ _ =>
      Finset.sum_nonneg fun r₀ _ => hterm_nn p₀ r₀)).1 hzero_slack p (Finset.mem_univ p)
  have hpr_zero :
      x p r * (x p r + I.propBetterMass x p r + I.recvBetterMass x r p - 1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun r₀ _ => hterm_nn p r₀)).1 hrow_zero r (Finset.mem_univ r)
  rcases mul_eq_zero.1 hpr_zero with hx0 | hslack
  · linarith
  · linarith

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
  have hr0_mem : I.propPref p ⟨0, hn⟩ ∈ S := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hzero : I.propBetterMass x p (I.propPref p ⟨0, hn⟩) = 0 := by
      refine Finset.sum_eq_zero fun r' hr' => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, propRank_propPref] at hr'
      exact False.elim (Nat.not_lt_zero _ hr')
    linarith
  have hSne : S.Nonempty := ⟨I.propPref p ⟨0, hn⟩, hr0_mem⟩
  let kMax : Fin n := (S.image (I.propRank p)).max' (hSne.image _)
  let rStar : Fin n := I.propPref p kMax
  have hkMax_mem : kMax ∈ S.image (I.propRank p) := Finset.max'_mem _ _
  obtain ⟨r', hr'S, hr'eq⟩ := Finset.mem_image.1 hkMax_mem
  have hrStar_eq : rStar = r' := by
    dsimp only [rStar]
    rw [← hr'eq, propPref_propRank]
  have hlt_low : I.propBetterMass x p rStar < t := by
    rw [hrStar_eq]
    exact (Finset.mem_filter.1 hr'S).2
  refine ⟨rStar, hlt_low, ?_⟩
  by_contra hnot_gt
  push Not at hnot_gt
  have hlt_high : I.propBetterMass x p rStar + x p rStar < t :=
    lt_of_le_of_ne hnot_gt (hbp p rStar).2.symm
  by_cases hk_lt : kMax.val + 1 < n
  · let kNext : Fin n := ⟨kMax.val + 1, hk_lt⟩
    let rNext : Fin n := I.propPref p kNext
    have hfilter_eq :
        Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p rNext) =
          insert rStar (Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p rStar)) := by
      ext r'
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and,
        rNext, rStar, propRank_propPref]
      constructor
      · intro hr'
        have hle : (I.propRank p r').val ≤ kMax.val := Nat.lt_succ_iff.1 hr'
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact Or.inr hlt
        · left
          have hfin : I.propRank p r' = kMax := Fin.ext heq
          rw [← hfin, propPref_propRank]
      · rintro (rfl | hlt)
        · rw [propRank_propPref]
          exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt hlt
    have hnot_in : rStar ∉ Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p rStar) :=
      fun h => lt_irrefl _ (Finset.mem_filter.1 h).2
    have hmass_next : I.propBetterMass x p rNext = I.propBetterMass x p rStar + x p rStar := by
      rw [propBetterMass, hfilter_eq, Finset.sum_insert hnot_in, propBetterMass, add_comm]
    have hrNext_S : rNext ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩
    have hkNext_le : kNext ≤ kMax := by
      have hmem_img : I.propRank p rNext ∈ S.image (I.propRank p) :=
        Finset.mem_image_of_mem _ hrNext_S
      have h : I.propRank p rNext ≤ kMax := Finset.le_max' _ _ hmem_img
      have hrk : I.propRank p rNext = kNext := I.propRank_propPref p kNext
      exact hrk ▸ h
    exact Nat.not_succ_le_self kMax.val hkNext_le
  · have hk_top : kMax.val + 1 = n := by omega
    have hfilter_univ :
        insert rStar (Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p rStar)) =
          Finset.univ := by
      ext r'
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, iff_true,
        rStar, propRank_propPref]
      have hr'_lt : (I.propRank p r').val < n := (I.propRank p r').isLt
      have hlt_n : (I.propRank p r').val < kMax.val + 1 := by omega
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hlt_n) with hlt | heq
      · exact Or.inr hlt
      · left
        have hfin : I.propRank p r' = kMax := Fin.ext heq
        rw [← hfin, propPref_propRank]
    have hnot_in : rStar ∉ Finset.univ.filter (fun r' => I.propRank p r' < I.propRank p rStar) :=
      fun h => lt_irrefl _ (Finset.mem_filter.1 h).2
    have hsum_one : I.propBetterMass x p rStar + x p rStar = 1 := by
      rw [add_comm, propBetterMass, ← Finset.sum_insert hnot_in, hfilter_univ, hrow p]
    linarith

private theorem sum_fin_sub_telescope :
    ∀ {m : ℕ} (f : Fin (m + 1) → ℝ) (ia ib : Fin (m + 1)), ia ≤ ib →
      (∑ k : Fin m, if ia.val ≤ k.val ∧ k.val < ib.val then f k.succ - f k.castSucc else 0) =
        f ib - f ia := by
  intro m f ia ib hle
  have hle_val : ia.val ≤ ib.val := hle
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle_val
  revert ib hle hle_val
  induction d with
  | zero =>
    intro ib _ _ hd
    have hib : ib = ia := Fin.ext (by omega)
    rw [hib]
    have hzero : (∑ k : Fin m,
        if ia.val ≤ k.val ∧ k.val < ia.val then f k.succ - f k.castSucc else 0) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [ite_eq_right_iff]
      intro h
      omega
    linarith
  | succ d ih =>
    intro ib _ _ hd
    have hib_lt : ib.val < m + 1 := ib.isLt
    have hib'_lt : ia.val + d < m + 1 := by omega
    have hk₀_lt : ia.val + d < m := by omega
    let ib' : Fin (m + 1) := ⟨ia.val + d, hib'_lt⟩
    let k₀ : Fin m := ⟨ia.val + d, hk₀_lt⟩
    have hib'_val : ib'.val = ia.val + d := rfl
    have hk₀_val : k₀.val = ia.val + d := rfl
    have hsplit : ∀ k : Fin m,
        (if ia.val ≤ k.val ∧ k.val < ib.val then f k.succ - f k.castSucc else 0) =
          (if ia.val ≤ k.val ∧ k.val < ib'.val then f k.succ - f k.castSucc else 0) +
            (if k = k₀ then f k.succ - f k.castSucc else 0) := by
      intro k
      by_cases h1 : ia.val ≤ k.val ∧ k.val < ib'.val
      · have h2 : ia.val ≤ k.val ∧ k.val < ib.val := ⟨h1.1, by omega⟩
        have hne : k ≠ k₀ := fun hk => by have := congrArg Fin.val hk; omega
        simp [h1, h2, hne]
      · by_cases hk : k = k₀
        · subst hk
          have h2 : ia.val ≤ k₀.val ∧ k₀.val < ib.val := by omega
          rw [ite_eq_left_iff.2 fun h => (h h2).elim, ite_eq_right_iff.2 fun h => (h1 h).elim,
            ite_eq_left_iff.2 fun h => (h rfl).elim, zero_add]
        · have h2 : ¬ (ia.val ≤ k.val ∧ k.val < ib.val) := by
            intro h
            have hne_val : k.val ≠ ia.val + d := fun hv => hk (Fin.ext hv)
            exact h1 ⟨h.1, by omega⟩
          simp [h1, h2, hk]
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hia_le_ib' : ia ≤ ib' := Nat.le_add_right ia.val d
    have hih := ih ib' hia_le_ib' hia_le_ib' rfl
    have hsingle : (∑ k : Fin m, if k = k₀ then f k.succ - f k.castSucc else 0) =
        f ib - f ib' := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hsucc : k₀.succ = ib := Fin.ext (by simp only [Fin.val_succ, hk₀_val]; omega)
      have hcast : k₀.castSucc = ib' := Fin.ext rfl
      rw [hsucc, hcast]
    linarith

/-- **Theorem 10.15** ([SchummerVohra2007], Section 10.4.2, p. 261; [VandeVate1989]; [Rothblum1992];
[TeoSethuraman1998]): the fractional stable matching polytope `I.stablePolytope` equals the convex
hull of the `{0, 1}` incidence matrices of stable matchings of `I`. -/
theorem stablePolytope_eq_convexHull :
    I.stablePolytope = convexHull ℝ (matchingMatrix '' {μ : Matching n | I.IsStable μ}) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hstab0 : I.IsStable (Equiv.refl (Fin 0)) := fun p => Fin.elim0 p
      have hmem0 : matchingMatrix (Equiv.refl (Fin 0)) ∈
          matchingMatrix '' {μ : Matching 0 | I.IsStable μ} := ⟨Equiv.refl (Fin 0), hstab0, rfl⟩
      have hx_eq : x = matchingMatrix (Equiv.refl (Fin 0)) := by
        ext p
        exact Fin.elim0 p
      rw [hx_eq]
      exact subset_convexHull ℝ _ hmem0
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
      have hlow_B : ∀ p r, I.propBetterMass x p r ∈ B := by
        intro p r
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_))
        exact Finset.mem_biUnion.2
          ⟨p, Finset.mem_univ p, Finset.mem_image_of_mem _ (Finset.mem_univ r)⟩
      have hhigh_B : ∀ p r, I.propBetterMass x p r + x p r ∈ B := by
        intro p r
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
        exact Finset.mem_biUnion.2
          ⟨p, Finset.mem_univ p, Finset.mem_image_of_mem _ (Finset.mem_univ r)⟩
      have hB_bounds : ∀ y ∈ B, 0 ≤ y ∧ y ≤ 1 := by
        intro y hy
        simp only [B, bpLow, bpHigh, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion,
          Finset.mem_univ, true_and, Finset.mem_image] at hy
        rcases hy with rfl | rfl | ⟨p, r, rfl⟩ | ⟨p, r, rfl⟩
        · exact ⟨le_rfl, zero_le_one⟩
        · exact ⟨zero_le_one, le_rfl⟩
        · refine ⟨Finset.sum_nonneg fun r' _ => hx_nn p r', ?_⟩
          calc
            I.propBetterMass x p r ≤ ∑ r' : Fin n, x p r' :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun r' _ _ =>
                hx_nn p r'
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
        have hsub : ({0, 1} : Finset ℝ) ⊆ B := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact h0B
          · exact h1B
        have hc : ({0, 1} : Finset ℝ).card = 2 := by norm_num
        exact hc ▸ Finset.card_le_card hsub
      let m : ℕ := B.card - 1
      have hm_pos : 0 < m := by omega
      have hB_card : B.card = m + 1 := by omega
      let e : Fin (m + 1) ↪o ℝ := B.orderEmbOfFin hB_card
      have he0 : e ⟨0, Nat.succ_pos m⟩ = 0 := by
        rw [Finset.orderEmbOfFin_zero hB_card (Nat.succ_pos m)]
        refine le_antisymm (Finset.min'_le B 0 h0B) ?_
        exact (hB_bounds _ (Finset.min'_mem B _)).1
      have heLast : e (Fin.last m) = 1 := by
        have hlast_eq : (Fin.last m : Fin (m + 1)) =
            ⟨m + 1 - 1, Nat.sub_lt (Nat.succ_pos m) (Nat.succ_pos 0)⟩ := rfl
        rw [hlast_eq, Finset.orderEmbOfFin_last hB_card (Nat.succ_pos m)]
        refine le_antisymm ?_ (Finset.le_max' B 1 h1B)
        exact (hB_bounds _ (Finset.max'_mem B _)).2
      let w : Fin m → ℝ := fun k => e k.succ - e k.castSucc
      let mid : Fin m → ℝ := fun k => (e k.castSucc + e k.succ) / 2
      have hw_pos : ∀ k : Fin m, 0 < w k := fun k =>
        sub_pos.2 (e.strictMono k.castSucc_lt_succ)
      have hmid_gt : ∀ k : Fin m, e k.castSucc < mid k := fun k => by
        have hlt := e.strictMono k.castSucc_lt_succ
        dsimp only [mid]
        linarith
      have hmid_lt : ∀ k : Fin m, mid k < e k.succ := fun k => by
        have hlt := e.strictMono k.castSucc_lt_succ
        dsimp only [mid]
        linarith
      have hmid_not_B : ∀ k : Fin m, mid k ∉ B := by
        intro k hmem
        have hmem_range : mid k ∈ Set.range e := by
          rw [Finset.range_orderEmbOfFin]
          exact hmem
        obtain ⟨j, hj⟩ := hmem_range
        have hj1 : k.val < j.val := e.lt_iff_lt.1 (hj ▸ hmid_gt k)
        have hj2 : j.val < k.val + 1 := e.lt_iff_lt.1 (hj ▸ hmid_lt k)
        omega
      have hmid_01 : ∀ k : Fin m, 0 < mid k ∧ mid k < 1 := by
        intro k
        have h0_le : 0 ≤ e k.castSucc := he0 ▸ e.monotone (Fin.zero_le _)
        have hle_1 : e k.succ ≤ 1 := heLast ▸ e.monotone (Fin.le_last _)
        exact ⟨lt_of_le_of_lt h0_le (hmid_gt k), lt_of_lt_of_le (hmid_lt k) hle_1⟩
      -- For each midpoint mid k, construct the threshold matching μ_k and prove stability.
      have hex_r : ∀ (k : Fin m) (p : Fin n),
          ∃ r : Fin n, I.propBetterMass x p r < mid k ∧ mid k < I.propBetterMass x p r + x p r := by
        intro k p
        refine I.exists_threshold_receiver hn ⟨hx_nn, hx_row, hx_col, hx_stab⟩
          (hmid_01 k).1 (hmid_01 k).2 ?_ p
        intro p' r'
        exact ⟨fun h => hmid_not_B k (h ▸ hlow_B p' r'),
          fun h => hmid_not_B k (h ▸ hhigh_B p' r')⟩
      choose f hf using hex_r
      have hf_recv : ∀ (k : Fin m) (p : Fin n),
          I.recvBetterMass x (f k p) p < 1 - mid k ∧
            1 - mid k < I.recvBetterMass x (f k p) p + x p (f k p) := by
        intro k p
        have hpos : 0 < x p (f k p) := by linarith [(hf k p).1, (hf k p).2]
        have heq1 :=
          I.eq_one_of_mem_stablePolytope_of_pos ⟨hx_nn, hx_row, hx_col, hx_stab⟩ hpos
        exact ⟨by linarith [(hf k p).2], by linarith [(hf k p).1]⟩
      have hf_inj : ∀ k : Fin m, Function.Injective (f k) := by
        intro k p₁ p₂ heq
        by_contra hpne
        have hr1 := hf_recv k p₁
        have hr2 := hf_recv k p₂
        rw [heq] at hr1
        rcases lt_or_gt_of_ne (fun hrk => hpne (I.recvRank_injective (f k p₂) hrk)) with hlt | hgt
        · have hle := strictLower_add_le (fun p' => hx_nn p' (f k p₂)) hlt
          change I.recvBetterMass x (f k p₂) p₁ + x p₁ (f k p₂) ≤
            I.recvBetterMass x (f k p₂) p₂ at hle
          linarith [hr1.2, hr2.1]
        · have hle := strictLower_add_le (fun p' => hx_nn p' (f k p₂)) hgt
          change I.recvBetterMass x (f k p₂) p₂ + x p₂ (f k p₂) ≤
            I.recvBetterMass x (f k p₂) p₁ at hle
          linarith [hr2.2, hr1.1]
      let μ : Fin m → Matching n := fun k => permOfInjective (f k) (hf_inj k)
      have hμ_stab : ∀ k : Fin m, I.IsStable (μ k) := by
        intro k p r ⟨hp_pref, hr_pref⟩
        have hp_le : I.propBetterMass x p r + x p r ≤ I.propBetterMass x p (f k p) :=
          strictLower_add_le (fun r' => hx_nn p r') hp_pref
        let pStar : Fin n := (μ k).symm r
        have hpStar_f : f k pStar = r := (μ k).apply_symm_apply r
        have hr_le : I.recvBetterMass x r p + x p r ≤ I.recvBetterMass x r pStar :=
          strictLower_add_le (fun p' => hx_nn p' r) hr_pref
        have hr_pStar := hf_recv k pStar
        rw [hpStar_f] at hr_pStar
        have hvande := hx_stab p r
        have hnn_pr := hx_nn p r
        linarith [(hf k p).1, hr_pStar.1]
      have hμ_iff : ∀ (k : Fin m) (p r : Fin n),
          μ k p = r ↔
            (I.propBetterMass x p r < mid k ∧ mid k < I.propBetterMass x p r + x p r) := by
        intro k p r
        change f k p = r ↔ _
        constructor
        · rintro rfl
          exact hf k p
        · intro hr_int
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
        have hcongr : (∑ k : Fin m, w k) =
            ∑ k : Fin m, if (0 : ℕ) ≤ k.val ∧ k.val < m then e k.succ - e k.castSucc else 0 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hk_cond : (0 : ℕ) ≤ k.val ∧ k.val < m := ⟨Nat.zero_le _, k.isLt⟩
          simp only [hk_cond, and_self, ↓reduceIte, w]
        rw [hcongr]
        simpa only [Fin.val_zero, Fin.val_last, heLast, he0, sub_zero] using htel
      have hx_decomp : ∑ k : Fin m, w k • matchingMatrix (μ k) = x := by
        ext p r
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have haB : I.propBetterMass x p r ∈ Set.range e := by
          rw [Finset.range_orderEmbOfFin]; exact hlow_B p r
        have hbB : I.propBetterMass x p r + x p r ∈ Set.range e := by
          rw [Finset.range_orderEmbOfFin]; exact hhigh_B p r
        obtain ⟨ia, hia⟩ := haB
        obtain ⟨ib, hib⟩ := hbB
        have hia_le_ib : ia ≤ ib := e.le_iff_le.1 (by linarith [hx_nn p r, hia, hib])
        have hterm : ∀ k : Fin m,
            w k * matchingMatrix (μ k) p r =
              if ia.val ≤ k.val ∧ k.val < ib.val then e k.succ - e k.castSucc else 0 := by
          intro k
          rw [matchingMatrix]
          simp only [hμ_iff k p r]
          rw [← hib, ← hia]
          by_cases hidx : ia.val ≤ k.val ∧ k.val < ib.val
          · have hia_le : e ia ≤ e k.castSucc := e.monotone hidx.1
            have hib_ge : e k.succ ≤ e ib := e.monotone (Nat.succ_le_of_lt hidx.2)
            have hint : e ia < mid k ∧ mid k < e ib :=
              ⟨lt_of_le_of_lt hia_le (hmid_gt k), lt_of_lt_of_le (hmid_lt k) hib_ge⟩
            simp [hidx, hint, w]
          · have hnot_int : ¬ (e ia < mid k ∧ mid k < e ib) := by
              rintro ⟨h1, h2⟩
              apply hidx
              refine ⟨?_, ?_⟩
              · by_contra hlt_ia
                push Not at hlt_ia
                have hsucc_le : k.succ ≤ ia := Nat.succ_le_of_lt hlt_ia
                have := e.monotone hsucc_le
                linarith [hmid_lt k]
              · by_contra hge_ib
                push Not at hge_ib
                have hcast_ge : ib ≤ k.castSucc := hge_ib
                have := e.monotone hcast_ge
                linarith [hmid_gt k]
            simp [hidx, hnot_int]
        simp_rw [hterm]
        rw [sum_fin_sub_telescope e ia ib hia_le_ib, hia, hib]
        ring
      rw [← hx_decomp]
      exact (convex_convexHull ℝ _).sum_mem (fun k _ => (hw_pos k).le) hw_sum fun k _ =>
        subset_convexHull ℝ _ ⟨μ k, hμ_stab k, rfl⟩
  · refine convexHull_min ?_ I.convex_stablePolytope
    rintro x ⟨μ, hstab, rfl⟩
    exact (I.matchingMatrix_mem_stablePolytope_iff μ).2 hstab

/-- **Theorem 10.15 (Extreme-point integrality)** ([SchummerVohra2007], Section 10.4.2, p. 261;
[VandeVate1989]; [Rothblum1992]; [TeoSethuraman1998]): the extreme points of `I.stablePolytope` are
precisely the `{0, 1}` incidence matrices of stable matchings of `I`. -/
theorem extremePoints_stablePolytope :
    I.stablePolytope.extremePoints ℝ = matchingMatrix '' {μ : Matching n | I.IsStable μ} := by
  refine Set.Subset.antisymm ?_ ?_
  · rw [I.stablePolytope_eq_convexHull]
    exact extremePoints_convexHull_subset
  · rintro _ ⟨μ, hstab, rfl⟩
    refine ⟨(I.matchingMatrix_mem_stablePolytope_iff μ).2 hstab, ?_⟩
    rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hseg⟩
    ext p r
    have hval := congrFun (congrFun hseg p) r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, matchingMatrix] at hval
    have hx₁_nn := hx₁.1 p r
    have hx₂_nn := hx₂.1 p r
    have hx₁_le := I.entry_le_one_of_mem_stablePolytope hx₁ p r
    have hx₂_le := I.entry_le_one_of_mem_stablePolytope hx₂ p r
    split_ifs at hval with hpr
    · simp only [matchingMatrix, hpr, ↓reduceIte]
      by_contra hne
      have hlt : x₁ p r < 1 := lt_of_le_of_ne hx₁_le hne
      have hmul1 : a * x₁ p r < a * 1 := mul_lt_mul_of_pos_left hlt ha
      have hmul2 : b * x₂ p r ≤ b * 1 := mul_le_mul_of_nonneg_left hx₂_le hb.le
      linarith
    · simp only [matchingMatrix, hpr, ↓reduceIte]
      by_contra hne
      have hgt : 0 < x₁ p r := lt_of_le_of_ne hx₁_nn (Ne.symm hne)
      have hmul1 : 0 < a * x₁ p r := mul_pos ha hgt
      have hmul2 : 0 ≤ b * x₂ p r := mul_nonneg hb.le hx₂_nn
      linarith

end Instance

end Cslib.Algorithms.Lean.StableMatching
