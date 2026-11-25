/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Progress
public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
public import Cslib.Foundations.Data.BitString
import CslibFrontier.Foundations.Quantum.Measurement.Overlap

/-!
# Weighted quantum adversary method

A weighted adversary scheme (`Cslib.Quantum.WeightScheme`) attaches nonnegative pair weights
`w(x, y)` to a relation `R` of input pairs and nonnegative coordinate weights `u(x, y, i)` and
`v(x, y, i)` satisfying `w(x, y)² ≤ u(x, y, i) · v(x, y, i)` whenever `xᵢ ≠ yᵢ`
[Ambainis2006], Section 3.3, Definitions 1–3; [Zhang2005], Definition 1.

From the endpoint weights `wtFst x = ∑_{(x, y) ∈ R} w(x, y)` and
`wtSnd y = ∑_{(x, y) ∈ R} w(x, y)` and coordinate loads `loadFst x i` and `loadSnd y i`, balancing
`Cslib.Quantum.one_sub_mul_sum_le_of_sq_le` across the two endpoints yields:

* **Weighted adversary bound** [Ambainis2006], Lemma 1: if `loadFst x i ≤ vA · wtFst x` and
  `loadSnd y i ≤ vB · wtSnd y` for all endpoints and coordinates, then
  `(1 - δ) ∑_{(x, y) ∈ R} w(x, y) ≤ 2 T √(vA · vB) ∑_{(x, y) ∈ R} w(x, y)`
  (`Cslib.Quantum.WeightScheme.one_sub_mul_sum_le`).
* **Ratio form** [Zhang2005], Theorem 3 (`Alb₃`): if `0 < ∑_{(x, y) ∈ R} w(x, y)`,
  `mA · loadFst x i ≤ wtFst x`, and `mB · loadSnd y i ≤ wtSnd y`, then
  `(1 - δ) √(mA · mB) ≤ 2 T` (`Cslib.Quantum.WeightScheme.one_sub_mul_sqrt_le_of_load_le`).
* **Subsumption of unweighted bounds** [Zhang2005], Theorem 5 (`Alb₂ ≤ Alb₃`): every unweighted
  counting instance `(R, m, m', L)` embeds via `Cslib.Quantum.WeightScheme.ofUnweighted`.

## Main definitions

* `Cslib.Quantum.WeightScheme`: a weighted adversary scheme on `BitString N`.
* `Cslib.Quantum.WeightScheme.weightSum`, `Cslib.Quantum.WeightScheme.wtFst`,
  `Cslib.Quantum.WeightScheme.wtSnd`: pair-weight sums.
* `Cslib.Quantum.WeightScheme.loadFst`, `Cslib.Quantum.WeightScheme.loadSnd`: coordinate loads.
* `Cslib.Quantum.WeightScheme.ofUnweighted`: weight scheme induced by unweighted counts.

## Main results

* `Cslib.Quantum.WeightScheme.one_sub_mul_sum_le` and
  `Cslib.Quantum.WeightScheme.one_sub_two_mul_sqrt_mul_sum_le`: Ambainis's weighted adversary bound.
* `Cslib.Quantum.WeightScheme.one_sub_mul_sqrt_le_of_load_le` and
  `Cslib.Quantum.WeightScheme.one_sub_two_mul_sqrt_mul_sqrt_le_of_load_le`: Zhang's ratio form.
* `Cslib.Quantum.WeightScheme.ofUnweighted`, `Cslib.Quantum.WeightScheme.ofUnweighted_wtFst`,
  `Cslib.Quantum.WeightScheme.ofUnweighted_wtSnd`,
  `Cslib.Quantum.WeightScheme.ofUnweighted_loadFst_le`,
  `Cslib.Quantum.WeightScheme.ofUnweighted_loadSnd_le`: unweighted-to-weighted embedding
  (`Alb₂ ≤ Alb₃`).

## References

* [A. Ambainis, *Polynomial degree vs. quantum query complexity*][Ambainis2006]
* [S. Zhang, *On the power of Ambainis lower bounds*][Zhang2005]
-/

public section

namespace Cslib.Quantum

open Finset

variable {N : ℕ} {W : Type*} [Fintype W]

/-- A weighted adversary scheme on `N`-bit inputs ([Ambainis2006], Section 3.3, Definition 1;
[Zhang2005], Definition 1): nonnegative pair weights `w` on `R` and coordinate weights `u, v`
satisfying `w(x, y)² ≤ u(x, y, i) · v(x, y, i)` whenever `(x, y) ∈ R` and `xᵢ ≠ yᵢ`. -/
@[ext] structure WeightScheme (N : ℕ) where
  /-- The relation of input pairs. -/
  R : Finset (BitString N × BitString N)
  /-- Nonnegative pair weights on `R`. -/
  w : BitString N × BitString N → ℝ
  /-- First-endpoint coordinate weights. -/
  u : BitString N × BitString N → Fin N → ℝ
  /-- Second-endpoint coordinate weights. -/
  v : BitString N × BitString N → Fin N → ℝ
  /-- Pair weights are nonnegative on `R`. -/
  w_nonneg : ∀ p ∈ R, 0 ≤ w p
  /-- First-endpoint coordinate weights are nonnegative on differing pairs. -/
  u_nonneg : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ u p i
  /-- Second-endpoint coordinate weights are nonnegative on differing pairs. -/
  v_nonneg : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ v p i
  /-- Splitting inequality `w(p)² ≤ u(p, i) · v(p, i)` on differing pairs. -/
  sq_le : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → w p ^ 2 ≤ u p i * v p i

namespace WeightScheme

/-- Total pair weight of a weight scheme. -/
@[expose] def weightSum (S : WeightScheme N) : ℝ := ∑ p ∈ S.R, S.w p

/-- Total weight `wt(x)` of pairs in `R` with first endpoint `x`. -/
@[expose] noncomputable def wtFst (S : WeightScheme N) (x : BitString N) : ℝ :=
  ∑ p ∈ S.R with p.1 = x, S.w p

/-- Total weight `wt(y)` of pairs in `R` with second endpoint `y`. -/
@[expose] noncomputable def wtSnd (S : WeightScheme N) (y : BitString N) : ℝ :=
  ∑ p ∈ S.R with p.2 = y, S.w p

/-- Coordinate load `v(x, i)` of coordinate `i` at first endpoint `x`. -/
@[expose] noncomputable def loadFst (S : WeightScheme N) (x : BitString N) (i : Fin N) : ℝ :=
  ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p.1 = x, S.u p i

/-- Coordinate load `v(y, i)` of coordinate `i` at second endpoint `y`. -/
@[expose] noncomputable def loadSnd (S : WeightScheme N) (y : BitString N) (i : Fin N) : ℝ :=
  ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p.2 = y, S.v p i

theorem weightSum_nonneg (S : WeightScheme N) : 0 ≤ S.weightSum :=
  sum_nonneg S.w_nonneg

theorem wtFst_nonneg (S : WeightScheme N) (x : BitString N) : 0 ≤ S.wtFst x :=
  sum_nonneg fun p hp => S.w_nonneg p (mem_filter.1 hp).1

theorem wtSnd_nonneg (S : WeightScheme N) (y : BitString N) : 0 ≤ S.wtSnd y :=
  sum_nonneg fun p hp => S.w_nonneg p (mem_filter.1 hp).1

theorem loadFst_nonneg (S : WeightScheme N) (x : BitString N) (i : Fin N) : 0 ≤ S.loadFst x i :=
  sum_nonneg fun p hp => S.u_nonneg p (mem_filter.1 hp).1 i (mem_filter.1 hp).2.1

theorem loadSnd_nonneg (S : WeightScheme N) (y : BitString N) (i : Fin N) : 0 ≤ S.loadSnd y i :=
  sum_nonneg fun p hp => S.v_nonneg p (mem_filter.1 hp).1 i (mem_filter.1 hp).2.1

theorem sum_wtFst_eq_weightSum (S : WeightScheme N) :
    ∑ x ∈ S.R.image Prod.fst, S.wtFst x = S.weightSum := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (s := S.R) (g := Prod.fst)
    (t := S.R.image Prod.fst) (f := S.w) (fun _ h => mem_image_of_mem _ h)

theorem sum_wtSnd_eq_weightSum (S : WeightScheme N) :
    ∑ y ∈ S.R.image Prod.snd, S.wtSnd y = S.weightSum := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (s := S.R) (g := Prod.snd)
    (t := S.R.image Prod.snd) (f := S.w) (fun _ h => mem_image_of_mem _ h)

/-- Rescaled progress-measure bound for any positive balancing factor `c > 0`. -/
private theorem one_sub_mul_sum_le_of_pos (S : WeightScheme N)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    {δ vA vB : ℝ} (hδ : ∀ p ∈ S.R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, S.loadFst x i ≤ vA * S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, S.loadSnd y i ≤ vB * S.wtSnd y)
    {c : ℝ} (hc : 0 < c) :
    (1 - δ) * S.weightSum ≤ T * (c * vA + vB / c) * S.weightSum := by
  have htel := one_sub_mul_sum_le_of_sq_le U hψ₀ T S.R S.w hδ
    (fun p i => c * S.u p i) (fun p i => S.v p i / c)
    (fun x => c * vA * S.wtFst x) (fun y => (vB / c) * S.wtSnd y)
    S.w_nonneg
    (fun p hp i hi => mul_nonneg hc.le (S.u_nonneg p hp i hi))
    (fun p hp i hi => div_nonneg (S.v_nonneg p hp i hi) hc.le)
    (fun p hp i hi => (S.sq_le p hp i hi).trans_eq (by field_simp))
    (fun x hx i => by
      rw [← mul_sum, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hA x hx i) hc.le)
    (fun y hy i => by
      rw [← sum_div, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (hB y hy i) hc.le)
  rw [← mul_sum, ← mul_sum, S.sum_wtFst_eq_weightSum, S.sum_wtSnd_eq_weightSum] at htel
  exact htel.trans_eq (by ring)

private theorem nonpos_of_forall_pos_le_div {x B : ℝ} (hB : 0 ≤ B)
    (h : ∀ c : ℝ, 0 < c → x ≤ B / c) : x ≤ 0 := by
  by_contra! hx
  have hle := h ((B + 1) / x) (by positivity)
  rw [div_div_eq_mul_div, le_div_iff₀ (by positivity)] at hle
  nlinarith

/-- **Weighted quantum adversary bound** ([Ambainis2006], Section 3.3, Lemma 1):
if `T` queries leave every related pair with state overlap at most `δ`, and the coordinate loads
satisfy `loadFst x i ≤ vA · wtFst x` and `loadSnd y i ≤ vB · wtSnd y`, then
`(1 - δ) ∑_{(x, y) ∈ R} w(x, y) ≤ 2 T √(vA · vB) ∑_{(x, y) ∈ R} w(x, y)`. -/
theorem one_sub_mul_sum_le (S : WeightScheme N) (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) {δ : ℝ}
    (hδ : ∀ p ∈ S.R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ)
    {vA vB : ℝ} (hvA : 0 ≤ vA) (hvB : 0 ≤ vB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, S.loadFst x i ≤ vA * S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, S.loadSnd y i ≤ vB * S.wtSnd y) :
    (1 - δ) * S.weightSum ≤ 2 * T * √(vA * vB) * S.weightSum := by
  rcases hvA.eq_or_lt with rfl | hvA_pos
  · simp only [zero_mul, Real.sqrt_zero, mul_zero]
    refine nonpos_of_forall_pos_le_div (B := T * vB * S.weightSum)
      (by have := S.weightSum_nonneg; positivity) fun c hc => ?_
    exact (S.one_sub_mul_sum_le_of_pos U hψ₀ T hδ hA hB hc).trans_eq (by ring)
  rcases hvB.eq_or_lt with rfl | hvB_pos
  · simp only [mul_zero, Real.sqrt_zero, zero_mul]
    refine nonpos_of_forall_pos_le_div (B := T * vA * S.weightSum)
      (by have := S.weightSum_nonneg; positivity) fun c hc => ?_
    exact (S.one_sub_mul_sum_le_of_pos U hψ₀ T hδ hA hB (inv_pos.2 hc)).trans_eq
      (by rw [zero_div, add_zero, inv_mul_eq_div]; ring)
  · have hc : 0 < √vB / √vA := div_pos (Real.sqrt_pos.2 hvB_pos) (Real.sqrt_pos.2 hvA_pos)
    refine (S.one_sub_mul_sum_le_of_pos U hψ₀ T hδ hA hB hc).trans_eq ?_
    rw [Real.sqrt_mul hvA_pos.le]
    field_simp [Real.sqrt_ne_zero'.2 hvA_pos, Real.sqrt_ne_zero'.2 hvB_pos]
    ring_nf
    rw [Real.sq_sqrt hvA_pos.le, Real.sq_sqrt hvB_pos.le]
    ring

/-- **Weighted quantum adversary bound for Boolean outputs** ([Ambainis2006], Lemma 1):
if a `T`-query algorithm accepts the first input of every pair in `R` with probability at least
`1 - ε` and the second with probability at most `ε ≤ 1/2`, then
`(1 - 2√(ε(1-ε))) ∑ w ≤ 2 T √(vA · vB) ∑ w`. -/
theorem one_sub_two_mul_sqrt_mul_sum_le (S : WeightScheme N)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_acc : Finset (Fin N × Bool × W)) {ε : ℝ}
    (h₁ : ∀ p ∈ S.R, 1 - ε ≤ measureProb (run U ψ₀ p.1 T) S_acc)
    (h₂ : ∀ p ∈ S.R, measureProb (run U ψ₀ p.2 T) S_acc ≤ ε) (hε : 2 * ε ≤ 1)
    {vA vB : ℝ} (hvA : 0 ≤ vA) (hvB : 0 ≤ vB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, S.loadFst x i ≤ vA * S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, S.loadSnd y i ≤ vB * S.wtSnd y) :
    (1 - 2 * √(ε * (1 - ε))) * S.weightSum ≤ 2 * T * √(vA * vB) * S.weightSum :=
  S.one_sub_mul_sum_le U hψ₀ T
    (fun p hp => norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀])
      (by rw [norm_run, hψ₀]) (h₁ p hp) (h₂ p hp) hε)
    hvA hvB hA hB

/-- **Weighted quantum adversary bound, ratio form** ([Zhang2005], Theorem 3, `Alb₃`):
if `0 < ∑ p ∈ R, w p`, `mA · loadFst x i ≤ wtFst x`, and `mB · loadSnd y i ≤ wtSnd y`, then
`(1 - δ) √(mA · mB) ≤ 2 T`. -/
theorem one_sub_mul_sqrt_le_of_load_le (S : WeightScheme N)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (hW : 0 < S.weightSum) {δ : ℝ}
    (hδ : ∀ p ∈ S.R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ)
    {mA mB : ℝ} (hmA : 0 ≤ mA) (hmB : 0 ≤ mB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, mA * S.loadFst x i ≤ S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, mB * S.loadSnd y i ≤ S.wtSnd y) :
    (1 - δ) * √(mA * mB) ≤ 2 * T := by
  rcases hmA.eq_or_lt with rfl | hmA_pos
  · simp only [zero_mul, Real.sqrt_zero, mul_zero]
    positivity
  rcases hmB.eq_or_lt with rfl | hmB_pos
  · simp only [mul_zero, Real.sqrt_zero, mul_zero]
    positivity
  have hbal := S.one_sub_mul_sum_le U hψ₀ T hδ (vA := mA⁻¹) (vB := mB⁻¹)
    (inv_nonneg.2 hmA_pos.le) (inv_nonneg.2 hmB_pos.le)
    (fun x hx i => by rw [inv_mul_eq_div, le_div_iff₀' hmA_pos]; exact hA x hx i)
    (fun y hy i => by rw [inv_mul_eq_div, le_div_iff₀' hmB_pos]; exact hB y hy i)
  have hcancel : 1 - δ ≤ 2 * (T : ℝ) * √(mA⁻¹ * mB⁻¹) := by
    simpa [mul_assoc, hW.ne'] using mul_le_mul_of_nonneg_right hbal (inv_nonneg.2 hW.le)
  refine (mul_le_mul_of_nonneg_right hcancel (Real.sqrt_nonneg _)).trans_eq ?_
  rw [mul_assoc, ← Real.sqrt_mul (by positivity),
    show mA⁻¹ * mB⁻¹ * (mA * mB) = 1 by field_simp [hmA_pos.ne', hmB_pos.ne'],
    Real.sqrt_one, mul_one]

/-- **Weighted quantum adversary bound for Boolean outputs, ratio form** ([Zhang2005],
Theorem 3): `(1 - 2√(ε(1-ε))) √(mA · mB) ≤ 2 T`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_le_of_load_le (S : WeightScheme N)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (hW : 0 < S.weightSum) (S_acc : Finset (Fin N × Bool × W)) {ε : ℝ}
    (h₁ : ∀ p ∈ S.R, 1 - ε ≤ measureProb (run U ψ₀ p.1 T) S_acc)
    (h₂ : ∀ p ∈ S.R, measureProb (run U ψ₀ p.2 T) S_acc ≤ ε) (hε : 2 * ε ≤ 1)
    {mA mB : ℝ} (hmA : 0 ≤ mA) (hmB : 0 ≤ mB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, mA * S.loadFst x i ≤ S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, mB * S.loadSnd y i ≤ S.wtSnd y) :
    (1 - 2 * √(ε * (1 - ε))) * √(mA * mB) ≤ 2 * T :=
  S.one_sub_mul_sqrt_le_of_load_le U hψ₀ T hW
    (fun p hp => norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀])
      (by rw [norm_run, hψ₀]) (h₁ p hp) (h₂ p hp) hε)
    hmA hmB hA hB

/-- Weight scheme induced by an unweighted adversary relation `(R, L)` with
`l_{x,i} · l_{y,i} ≤ L` ([Zhang2005], Theorem 5): `w(p) = 1`, `u(p, i) = √L / l_{x,i}`, and
`v(p, i) = √L / l_{y,i}`. -/
@[expose] noncomputable def ofUnweighted (R : Finset (BitString N × BitString N)) (L : ℕ)
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L) :
    WeightScheme N where
  R := R
  w := fun _ => 1
  u := fun p i => √L / #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1}
  v := fun p i => √L / #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2}
  w_nonneg := fun _ _ => zero_le_one
  u_nonneg := fun _ _ _ _ => by positivity
  v_nonneg := fun _ _ _ _ => by positivity
  sq_le := fun p hp i hi => by
    classical
    have hl₁ : (0 : ℝ) < #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} :=
      Nat.cast_pos.2 (card_pos.2 ⟨p, mem_filter.2 ⟨hp, hi, rfl⟩⟩)
    have hl₂ : (0 : ℝ) < #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} :=
      Nat.cast_pos.2 (card_pos.2 ⟨p, mem_filter.2 ⟨hp, hi, rfl⟩⟩)
    have hprod : (#{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} : ℝ) *
        #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ √L * √L := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg L)]
      exact_mod_cast hL p hp i hi
    rw [one_pow, div_mul_div_comm, le_div_iff₀ (mul_pos hl₁ hl₂)]
    simpa [one_mul] using hprod

theorem ofUnweighted_wtFst {R : Finset (BitString N × BitString N)} {L : ℕ}
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L)
    (x : BitString N) :
    (ofUnweighted R L hL).wtFst x = (#{q ∈ R | q.1 = x} : ℝ) := by
  simp [wtFst, ofUnweighted]

theorem ofUnweighted_wtSnd {R : Finset (BitString N × BitString N)} {L : ℕ}
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L)
    (y : BitString N) :
    (ofUnweighted R L hL).wtSnd y = (#{q ∈ R | q.2 = y} : ℝ) := by
  simp [wtSnd, ofUnweighted]

/-- A sum over `S` of terms each equal to `√L / #S` is at most `√L`. -/
private theorem sum_le_sqrt_of_eq_div_card {α : Type*} {S : Finset α} {L : ℕ} {f : α → ℝ}
    (hf : ∀ p ∈ S, f p = √L / (#S : ℝ)) : ∑ p ∈ S, f p ≤ √L := by
  rw [sum_congr rfl hf, sum_const, nsmul_eq_mul, ← mul_div_assoc]
  simpa only [div_one, mul_one] using mul_div_mul_left_le (c := (#S : ℝ)) (a := √L) (b := 1)
    (div_nonneg (Real.sqrt_nonneg L) zero_le_one)

theorem ofUnweighted_loadFst_le {R : Finset (BitString N × BitString N)} {L : ℕ}
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L)
    (x : BitString N) (i : Fin N) :
    (ofUnweighted R L hL).loadFst x i ≤ √L := by
  classical
  exact sum_le_sqrt_of_eq_div_card fun p hp => by simp only [ofUnweighted, (mem_filter.1 hp).2.2]

theorem ofUnweighted_loadSnd_le {R : Finset (BitString N × BitString N)} {L : ℕ}
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L)
    (y : BitString N) (i : Fin N) :
    (ofUnweighted R L hL).loadSnd y i ≤ √L := by
  classical
  exact sum_le_sqrt_of_eq_div_card fun p hp => by simp only [ofUnweighted, (mem_filter.1 hp).2.2]

end WeightScheme

end Cslib.Quantum
