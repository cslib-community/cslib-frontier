/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.BitBounds

import CslibFrontier.Foundations.Data.Rat.Basic
import CslibFrontier.Foundations.LinearAlgebra.Matrix.KroneckerRank
import Mathlib.Data.List.GetD
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Polynomial Coefficient Bit Bounds and Frontier Size Bounds for Rational Sturm Sequences

Over `ℚ`, reducing every rational entry to lowest terms keeps the canonical Euclidean Sturm
sequence `Cslib.RealRoot.sturmSeqList cs` polynomially bounded in bit-length: clearing input
denominators to `(F₀, F₁) ∈ ℤ[X]²` and normalizing the `i`-th extended Euclidean relation
`U_i F₀ + V_i F₁ = E_i` by the leading coefficient `c_i = E_i.leadingCoeff` characterizes the
normalized Bézout pair `(Ũ_i, Ṽ_i)` as the unique solution of an integer Sylvester linear system of
width `N ≤ 2 * cs.length`. Extracting a nonsingular `N × N` minor
(`Matrix.exists_submatrix_det_ne_zero`), solving by Cramer's rule (`Matrix.adjugate_mul`), and
bounding integer determinants by the Leibniz-expansion bound (`Matrix.det_le`) bounds every
coefficient of `Ũ_i`, `Ṽ_i`, and `Ẽ_i`, while the recurrence
`c_i = c_{i-2} * (Ṽ_{i-1}.leadingCoeff / Ṽ_i.leadingCoeff)` telescopes the leading coefficients
across at most `cs.length` steps.

This module also bounds the number of pairwise-disjoint intervals `(u, v]` on which
`sturmVariationsList (sturmSeqList cs)` drops by at least `2` by `2 * cs.length` unconditionally
(including on non-squarefree inputs), via `Polynomial.sturmReducedVariations`.

## Main definitions

* `Cslib.RealRoot.sturmBitBound`: explicit polynomial bit-length upper bound
  `8 * (n + 1) ^ 3 * (B + 1)` on entries of `sturmSeqList cs`.

## Main results

* `Cslib.RealRoot.hasCoeffBitBound_of_mem_sturmSeqList`: every polynomial `f ∈ sturmSeqList cs`
  satisfies `HasCoeffBitBound (sturmBitBound cs.length B) f` whenever `HasCoeffBitBound B cs`.
* `Cslib.RealRoot.card_active_sturm_intervals_le`: any list of pairwise-disjoint rational intervals
  `(u, v]` each having Sturm variation drop at least `2` has length at most `2 * cs.length`.

## References

`sturmBitBound`, the integer Sylvester-matrix Cramer/Hadamard bit-bound proof across
`sturmSeqList cs`, and `card_active_sturm_intervals_le` are this library's own construction,
using the reduced Sturm root-counting ingredient from [BasuPollackRoy2006], Theorem 2.50, p. 52
(adapted in `Sturm.lean` to finite real endpoints on `(a, b]` over `ℝ`).
-/

public section

namespace Cslib.RealRoot

open Polynomial Matrix
open scoped BigOperators

/-! ### Part 1: Rational numerator/denominator, integer determinant, and Cramer bounds -/

private theorem rat_num_den_le_of_eq_div {q : ℚ} {a b : ℤ} (hb : b ≠ 0)
    (heq : q = (a : ℚ) / (b : ℚ)) :
    Int.natAbs q.num ≤ Int.natAbs a ∧ q.den ≤ Int.natAbs b := by
  rw [heq, ← Rat.divInt_eq_div]
  exact ⟨Rat.natAbs_num_divInt_le a b hb, Rat.den_divInt_le a b hb⟩

private theorem rat_mul_div_num_den_le {q u v : ℚ} {K M : ℕ} (hv : v ≠ 0)
    (hq : Int.natAbs q.num ≤ K ∧ q.den ≤ K)
    (hu : Int.natAbs u.num ≤ M ∧ u.den ≤ M)
    (hvB : Int.natAbs v.num ≤ M ∧ v.den ≤ M) :
    Int.natAbs (q * (u / v)).num ≤ K * M ^ 2 ∧ (q * (u / v)).den ≤ K * M ^ 2 := by
  have hv_num : v.num ≠ 0 := Rat.num_ne_zero.mpr hv
  have hd : (q.den * u.den * v.num : ℤ) ≠ 0 := by positivity
  have heq : q * (u / v) =
      ((q.num * u.num * v.den : ℤ) : ℚ) / ((q.den * u.den * v.num : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, ← Rat.num_div_den u, ← Rat.num_div_den v]
    have := q.den_nz; have := u.den_nz; have := v.den_nz
    push_cast
    field_simp
  obtain ⟨hn, hd'⟩ := rat_num_den_le_of_eq_div hd heq
  simp only [Int.natAbs_mul, Int.natAbs_natCast, sq, ← mul_assoc] at hn hd' ⊢
  exact ⟨hn.trans (Nat.mul_le_mul (Nat.mul_le_mul hq.1 hu.1) hvB.2),
    hd'.trans (Nat.mul_le_mul (Nat.mul_le_mul hq.2 hu.2) hvB.1)⟩

private theorem int_det_natAbs_le {N H : ℕ} (K : Matrix (Fin N) (Fin N) ℤ)
    (hK : ∀ i j, Int.natAbs (K i j) ≤ H) :
    Int.natAbs K.det ≤ (N * H) ^ N := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := (H : ℤ)) fun i j => by
    simpa only [AbsoluteValue.abs_apply, Int.abs_eq_natAbs, Nat.cast_le] using hK i j
  simp only [AbsoluteValue.abs_apply, Int.abs_eq_natAbs, Fintype.card_fin, nsmul_eq_mul] at h
  calc K.det.natAbs ≤ N.factorial * H ^ N := by exact_mod_cast h
    _ ≤ N ^ N * H ^ N := by gcongr; exact Nat.factorial_le_pow N
    _ = (N * H) ^ N := (mul_pow _ _ _).symm

private theorem exists_cramer_rep_of_inj_mulVec {R N H : ℕ}
    (S : Matrix (Fin R) (Fin N) ℤ) (rhs : Fin R → ℤ)
    (hS : ∀ r j, Int.natAbs (S r j) ≤ H) (hrhs : ∀ r, Int.natAbs (rhs r) ≤ H)
    (x : Fin N → ℚ) (hx : (S.map (algebraMap ℤ ℚ)) *ᵥ x = (algebraMap ℤ ℚ) ∘ rhs)
    (hinj : ∀ z : Fin N → ℚ, (S.map (algebraMap ℤ ℚ)) *ᵥ z = 0 → z = 0) :
    ∃ (d : ℤ) (nums : Fin N → ℤ),
      d ≠ 0 ∧ Int.natAbs d ≤ (N * H) ^ N ∧
      (∀ j, Int.natAbs (nums j) ≤ (N * H) ^ N) ∧
      (∀ j, x j = (nums j : ℚ) / (d : ℚ)) := by
  let SQ : Matrix (Fin R) (Fin N) ℚ := S.map (algebraMap ℤ ℚ)
  have hker : LinearMap.ker SQ.mulVecLin = ⊥ := LinearMap.ker_eq_bot'.2 hinj
  have hrank : SQ.rank = N := by
    have hf := SQ.mulVecLin.finrank_range_add_finrank_ker
    rwa [hker, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hf
  obtain ⟨r0, c0, _, hc0, hdet0⟩ := Matrix.exists_submatrix_det_ne_zero SQ
  let e : Fin N ≃ Fin SQ.rank := finCongr hrank.symm
  let r : Fin N → Fin R := r0 ∘ e
  let c : Fin N → Fin N := c0 ∘ e
  have hc_inj : Function.Injective c := hc0.comp e.injective
  let ec : Fin N ≃ Fin N := Equiv.ofBijective c (Finite.injective_iff_bijective.mp hc_inj)
  let M : Matrix (Fin N) (Fin N) ℤ := S.submatrix r id
  let MQ : Matrix (Fin N) (Fin N) ℚ := SQ.submatrix r id
  have hMQ_sub : MQ.submatrix id ec = (SQ.submatrix r0 c0).submatrix e e := rfl
  have hMQ_ec_det : (MQ.submatrix id ec).det ≠ 0 := by
    rw [hMQ_sub, Matrix.det_submatrix_equiv_self e]; exact hdet0
  have hMQ_det : MQ.det ≠ 0 := fun hzero => hMQ_ec_det <| by
    rw [← Matrix.det_transpose, Matrix.transpose_submatrix,
      show MQᵀ.submatrix ec id = Matrix.submatrix MQᵀ ec id from rfl,
      Matrix.det_permute ec MQᵀ, Matrix.det_transpose, hzero, mul_zero]
  have hM_map : M.map (algebraMap ℤ ℚ) = MQ := rfl
  have hd0 : M.det ≠ 0 := fun h0 => hMQ_det <| by
    rw [← hM_map, show M.map (algebraMap ℤ ℚ) = (algebraMap ℤ ℚ).mapMatrix M from rfl,
      ← RingHom.map_det (algebraMap ℤ ℚ) M, h0, map_zero]
  let bSub : Fin N → ℤ := rhs ∘ r
  have hMx : MQ *ᵥ x = (algebraMap ℤ ℚ) ∘ bSub := by
    ext i
    simpa only [MQ, submatrix_apply, id_eq, mulVec, dotProduct, Function.comp_apply, bSub] using
      congrFun hx (r i)
  let nums : Fin N → ℤ := M.cramer bSub
  have hM_bound : ∀ i j, Int.natAbs (M i j) ≤ H := fun i j => hS (r i) j
  refine ⟨M.det, nums, hd0, int_det_natAbs_le M hM_bound, ?_, ?_⟩
  · intro j
    rw [show nums j = (M.updateCol j bSub).det from Matrix.cramer_apply M bSub j]
    refine int_det_natAbs_le (M.updateCol j bSub) fun i k => ?_
    by_cases hkj : k = j
    · subst hkj; rw [updateCol_self]; exact hrhs (r i)
    · rw [updateCol_ne hkj]; exact hM_bound i k
  · intro j
    have hadj : (M.adjugate.map (algebraMap ℤ ℚ)) *ᵥ (MQ *ᵥ x) =
        (M.adjugate.map (algebraMap ℤ ℚ)) *ᵥ ((algebraMap ℤ ℚ) ∘ bSub) :=
      congrArg ((M.adjugate.map (algebraMap ℤ ℚ)) *ᵥ ·) hMx
    rw [← hM_map, mulVec_mulVec, ← Matrix.map_mul, Matrix.adjugate_mul] at hadj
    have hj := congrFun hadj j
    have hrhs_j : ((M.adjugate.map (algebraMap ℤ ℚ)) *ᵥ ((algebraMap ℤ ℚ) ∘ bSub)) j =
        (nums j : ℚ) := by
      rw [← (algebraMap ℤ ℚ).map_mulVec M.adjugate bSub, ← Matrix.cramer_eq_adjugate_mulVec M bSub,
        eq_intCast]
    have hsmul : (((M.det • (1 : Matrix (Fin N) (Fin N) ℤ)).map (algebraMap ℤ ℚ)) *ᵥ x) j =
        (M.det : ℚ) * x j := by
      have hmat : (M.det • (1 : Matrix (Fin N) (Fin N) ℤ)).map (algebraMap ℤ ℚ) =
          (M.det : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ) := by
        ext a b
        change algebraMap ℤ ℚ (M.det * (1 : Matrix (Fin N) (Fin N) ℤ) a b) =
          (M.det : ℚ) * (1 : Matrix (Fin N) (Fin N) ℚ) a b
        by_cases hab : a = b <;>
          simp only [Matrix.one_apply, hab, ↓reduceIte, mul_one, mul_zero, eq_intCast, map_zero]
      rw [hmat, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [hsmul, hrhs_j] at hj
    have hdQ : (M.det : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd0
    exact (eq_div_iff hdQ).mpr (by rw [mul_comm]; exact hj)

/-! ### Part 2: Extended signed Sturm sequence and degree/Bézout invariants -/

private noncomputable def bezoutSturm (FQ₀ FQ₁ : ℚ[X]) : ℕ → ℚ[X] × ℚ[X] × ℚ[X]
  | 0 => (FQ₀, 1, 0)
  | 1 => (FQ₁, 0, 1)
  | k + 2 =>
    let t0 := bezoutSturm FQ₀ FQ₁ k
    let t1 := bezoutSturm FQ₀ FQ₁ (k + 1)
    let q := -((-t0.1) / t1.1)
    (-t0.1 % t1.1, q * t1.2.1 - t0.2.1, q * t1.2.2 - t0.2.2)

private theorem bezoutSturm_rel (FQ₀ FQ₁ : ℚ[X]) :
    ∀ k : ℕ,
      let t := bezoutSturm FQ₀ FQ₁ k
      let t1 := bezoutSturm FQ₀ FQ₁ (k + 1)
      t.2.1 * FQ₀ + t.2.2 * FQ₁ = t.1 ∧
      t1.2.1 * FQ₀ + t1.2.2 * FQ₁ = t1.1 ∧
      t.2.1 * t1.2.2 - t1.2.1 * t.2.2 = 1 := by
  intro k
  induction k with
  | zero =>
    dsimp only [bezoutSturm]
    exact ⟨by ring, by ring, by ring⟩
  | succ k ih =>
    obtain ⟨hbez0, hbez1, hdet0⟩ := ih
    dsimp only [bezoutSturm] at hbez0 hbez1 hdet0 ⊢
    set t0 := bezoutSturm FQ₀ FQ₁ k
    set t1 := bezoutSturm FQ₀ FQ₁ (k + 1)
    have hdiv := EuclideanDomain.div_add_mod (-t0.1) t1.1
    refine ⟨hbez1, ?_, ?_⟩
    · linear_combination -((-t0.1) / t1.1) * hbez1 - hbez0 - hdiv
    · linear_combination hdet0

private theorem mem_sturmSeq_bezoutSturm_aux (FQ₀ FQ₁ : ℚ[X]) :
    ∀ (m k : ℕ),
      (bezoutSturm FQ₀ FQ₁ k).1 ≠ 0 →
      (if (bezoutSturm FQ₀ FQ₁ (k + 1)).1 = 0 then 0
        else (bezoutSturm FQ₀ FQ₁ (k + 1)).1.natDegree + 1) ≤ m →
      (∀ r ≤ k, (bezoutSturm FQ₀ FQ₁ r).1 ≠ 0) →
      ∀ s ∈ (open Classical in
          Polynomial.sturmSeq (bezoutSturm FQ₀ FQ₁ k).1 (bezoutSturm FQ₀ FQ₁ (k + 1)).1),
        ∃ i, k ≤ i ∧ s = (bezoutSturm FQ₀ FQ₁ i).1 ∧ ∀ r ≤ i, (bezoutSturm FQ₀ FQ₁ r).1 ≠ 0 := by
  classical
  intro m
  induction m with
  | zero =>
    intro k hk0 hm hall s hs
    have hk1 : (bezoutSturm FQ₀ FQ₁ (k + 1)).1 = 0 := by
      by_contra hne
      rw [ite_eq_right hne] at hm
      omega
    rw [hk1, Polynomial.sturmSeq_zero_right, ite_eq_right hk0, List.mem_singleton] at hs
    exact ⟨k, le_rfl, hs, hall⟩
  | succ m ih =>
    intro k hk0 hm hall s hs
    by_cases hk1 : (bezoutSturm FQ₀ FQ₁ (k + 1)).1 = 0
    · rw [hk1, Polynomial.sturmSeq_zero_right, ite_eq_right hk0, List.mem_singleton] at hs
      exact ⟨k, le_rfl, hs, hall⟩
    · rw [Polynomial.sturmSeq_cons hk0, List.mem_cons] at hs
      rcases hs with rfl | hs_tail
      · exact ⟨k, le_rfl, rfl, hall⟩
      · have he2 : -(bezoutSturm FQ₀ FQ₁ k).1 % (bezoutSturm FQ₀ FQ₁ (k + 1)).1 =
            (bezoutSturm FQ₀ FQ₁ (k + 2)).1 := rfl
        rw [he2] at hs_tail
        have hall' : ∀ r ≤ k + 1, (bezoutSturm FQ₀ FQ₁ r).1 ≠ 0 := fun r hr => by
          rcases Nat.of_le_succ hr with hle | rfl; exacts [hall r hle, hk1]
        have hm' : (if (bezoutSturm FQ₀ FQ₁ (k + 2)).1 = 0 then 0
            else (bezoutSturm FQ₀ FQ₁ (k + 2)).1.natDegree + 1) ≤ m := by
          rw [ite_eq_right hk1] at hm
          by_cases hk2 : (bezoutSturm FQ₀ FQ₁ (k + 2)).1 = 0
          · simp only [hk2, ↓reduceIte, Nat.zero_le]
          · rw [ite_eq_right hk2]
            have hdeg : (bezoutSturm FQ₀ FQ₁ (k + 2)).1.natDegree <
                (bezoutSturm FQ₀ FQ₁ (k + 1)).1.natDegree :=
              natDegree_lt_natDegree hk2 (degree_mod_lt (-(bezoutSturm FQ₀ FQ₁ k).1) hk1)
            omega
        obtain ⟨i, hki, hsi, hall_i⟩ := ih (k + 1) hk1 hm' hall' s hs_tail
        exact ⟨i, Nat.le_of_succ_le hki, hsi, hall_i⟩

private theorem mem_sturmSeq_exists_bezoutSturm {FQ₀ FQ₁ s : ℚ[X]} (h0 : FQ₀ ≠ 0)
    (hs : s ∈ (open Classical in Polynomial.sturmSeq FQ₀ FQ₁)) :
    ∃ i, s = (bezoutSturm FQ₀ FQ₁ i).1 ∧ ∀ r ≤ i, (bezoutSturm FQ₀ FQ₁ r).1 ≠ 0 := by
  obtain ⟨i, _, hsi, hall⟩ :=
    mem_sturmSeq_bezoutSturm_aux FQ₀ FQ₁
      (if FQ₁ = 0 then 0 else FQ₁.natDegree + 1) 0 h0 le_rfl
      (fun r hr => by obtain rfl : r = 0 := Nat.eq_zero_of_le_zero hr; exact h0) s hs
  exact ⟨i, hsi, hall⟩

private theorem bezoutSturm_natDegree_lt {FQ₀ FQ₁ : ℚ[X]} (hd10 : FQ₁.natDegree < FQ₀.natDegree)
    {k : ℕ} (hpos : ∀ r ≤ k, (bezoutSturm FQ₀ FQ₁ r).1 ≠ 0) :
    ∀ i, 1 ≤ i → i ≤ k →
      (bezoutSturm FQ₀ FQ₁ i).1.natDegree < (bezoutSturm FQ₀ FQ₁ (i - 1)).1.natDegree := by
  intro i hi1 hik
  rcases i with _ | _ | j
  · omega
  · simpa only [Nat.add_sub_cancel, bezoutSturm] using hd10
  · change (-(bezoutSturm FQ₀ FQ₁ j).1 % (bezoutSturm FQ₀ FQ₁ (j + 1)).1).natDegree <
      (bezoutSturm FQ₀ FQ₁ (j + 1)).1.natDegree
    exact natDegree_lt_natDegree (hpos (j + 2) hik)
      (degree_mod_lt _ (hpos (j + 1) (by omega)))

private theorem bezoutSturm_natDegree_le_d1 {FQ₀ FQ₁ : ℚ[X]}
    (hd10 : FQ₁.natDegree < FQ₀.natDegree)
    {k : ℕ} (hpos : ∀ r ≤ k, (bezoutSturm FQ₀ FQ₁ r).1 ≠ 0) :
    ∀ i, 1 ≤ i → i ≤ k → (bezoutSturm FQ₀ FQ₁ i).1.natDegree ≤ FQ₁.natDegree := by
  intro i hi1
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  induction m with
  | zero => intro _; exact le_rfl
  | succ m ih =>
    intro hmk
    exact (bezoutSturm_natDegree_lt hd10 hpos (m + 2) (by omega) hmk).le.trans
      (ih (by omega) (by omega))

private theorem bezoutSturm_index_le_natDegree {FQ₀ FQ₁ : ℚ[X]}
    (hd10 : FQ₁.natDegree < FQ₀.natDegree)
    {k : ℕ} (hpos : ∀ r ≤ k, (bezoutSturm FQ₀ FQ₁ r).1 ≠ 0) :
    ∀ i ≤ k, (bezoutSturm FQ₀ FQ₁ i).1.natDegree + i ≤ FQ₀.natDegree := by
  intro i
  induction i with
  | zero => intro _; simp only [bezoutSturm, add_zero, le_refl]
  | succ i ih =>
    intro hik
    have hlt := bezoutSturm_natDegree_lt hd10 hpos (i + 1) (Nat.succ_pos i) hik
    have hprev := ih (Nat.le_of_succ_le hik)
    simp only [Nat.add_sub_cancel] at hlt
    omega

private theorem bezoutSturm_quot_props {FQ₀ FQ₁ : ℚ[X]} (hd10 : FQ₁.natDegree < FQ₀.natDegree)
    {k j : ℕ} (hpos : ∀ r ≤ k, (bezoutSturm FQ₀ FQ₁ r).1 ≠ 0) (hjk : j + 2 ≤ k) :
    let e0 := (bezoutSturm FQ₀ FQ₁ j).1
    let e1 := (bezoutSturm FQ₀ FQ₁ (j + 1)).1
    let q := -((-e0) / e1)
    q ≠ 0 ∧ q.natDegree = e0.natDegree - e1.natDegree ∧
      q.leadingCoeff * e1.leadingCoeff = e0.leadingCoeff := by
  dsimp only
  set e0 := (bezoutSturm FQ₀ FQ₁ j).1
  set e1 := (bezoutSturm FQ₀ FQ₁ (j + 1)).1
  set e2 := (bezoutSturm FQ₀ FQ₁ (j + 2)).1
  set q := -((-e0) / e1)
  have he0 : e0 ≠ 0 := hpos j (by omega)
  have he1 : e1 ≠ 0 := hpos (j + 1) (by omega)
  have hdeg10 : e1.natDegree < e0.natDegree :=
    bezoutSturm_natDegree_lt hd10 hpos (j + 1) (Nat.succ_pos j) (by omega)
  have hdeg21 : e2.degree < e1.degree := degree_mod_lt (-e0) he1
  have hdeg10' : e1.degree < e0.degree := degree_lt_degree hdeg10
  have hdeg20 : e2.degree < e0.degree := lt_trans hdeg21 hdeg10'
  have heq : e0 + e2 = q * e1 := by
    have hdiv := EuclideanDomain.div_add_mod (-e0) e1
    change e1 * ((-e0) / e1) + e2 = -e0 at hdiv
    dsimp only [q]
    linear_combination hdiv
  have hsum_ne : e0 + e2 ≠ 0 := fun h0 => he0 <| degree_eq_bot.1 <| by
    rw [← degree_add_eq_left_of_degree_lt hdeg20, h0, degree_zero]
  have hq0 : q ≠ 0 := fun h0 => hsum_ne (by rw [heq, h0, zero_mul])
  have hnat_eq : (e0 + e2).natDegree = e0.natDegree := natDegree_add_eq_left_of_degree_lt hdeg20
  have hlc_eq : (e0 + e2).leadingCoeff = e0.leadingCoeff := by
    rw [add_comm]; exact leadingCoeff_add_of_degree_lt hdeg20
  rw [heq, natDegree_mul hq0 he1] at hnat_eq
  rw [heq, leadingCoeff_mul] at hlc_eq
  exact ⟨hq0, by omega, hlc_eq⟩

private theorem sub_ne_zero_and_natDegree_and_leadingCoeff {p r : ℚ[X]} (hp : p ≠ 0)
    (hlt : r.degree < p.degree) :
    p - r ≠ 0 ∧ (p - r).natDegree = p.natDegree ∧ (p - r).leadingCoeff = p.leadingCoeff := by
  have hdeg := degree_sub_eq_left_of_degree_lt hlt
  exact ⟨fun h0 => hp (degree_eq_bot.1 (by rw [← hdeg, h0, degree_zero])),
    natDegree_eq_of_degree_eq hdeg, leadingCoeff_sub_of_degree_lt hlt⟩

private theorem bezoutSturm_uv_props {FQ₀ FQ₁ : ℚ[X]} (hd10 : FQ₁.natDegree < FQ₀.natDegree)
    {k : ℕ} (hpos : ∀ r ≤ k, (bezoutSturm FQ₀ FQ₁ r).1 ≠ 0) :
    ∀ i, 2 ≤ i → i ≤ k →
      let ti := bezoutSturm FQ₀ FQ₁ i
      let ti1 := bezoutSturm FQ₀ FQ₁ (i - 1)
      let ti2 := bezoutSturm FQ₀ FQ₁ (i - 2)
      ti.2.1 ≠ 0 ∧ ti.2.1.natDegree = FQ₁.natDegree - ti1.1.natDegree ∧
      ti.2.2 ≠ 0 ∧ ti.2.2.natDegree = FQ₀.natDegree - ti1.1.natDegree ∧
      ti.2.2.leadingCoeff * ti1.1.leadingCoeff = ti2.1.leadingCoeff * ti1.2.2.leadingCoeff := by
  intro i hi2
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rcases m with _ | m
    · intro hik
      obtain ⟨hq0, hq_deg, hq_lc⟩ := bezoutSturm_quot_props (j := 0) hd10 hpos hik
      dsimp only [Nat.zero_add, bezoutSturm] at hq0 hq_deg hq_lc ⊢
      change (bezoutSturm FQ₀ FQ₁ 2).2.1 ≠ 0 ∧
        (bezoutSturm FQ₀ FQ₁ 2).2.1.natDegree = FQ₁.natDegree - FQ₁.natDegree ∧
        (bezoutSturm FQ₀ FQ₁ 2).2.2 ≠ 0 ∧
        (bezoutSturm FQ₀ FQ₁ 2).2.2.natDegree = FQ₀.natDegree - FQ₁.natDegree ∧
        (bezoutSturm FQ₀ FQ₁ 2).2.2.leadingCoeff * FQ₁.leadingCoeff =
          FQ₀.leadingCoeff * (1 : ℚ[X]).leadingCoeff
      dsimp only [bezoutSturm]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [mul_zero, zero_sub, neg_ne_zero]; exact one_ne_zero
      · simp only [mul_zero, zero_sub, natDegree_neg, natDegree_one]; omega
      · simpa only [mul_one, sub_zero] using hq0
      · simpa only [mul_one, sub_zero] using hq_deg
      · simpa only [mul_one, sub_zero, leadingCoeff_one] using hq_lc
    · intro hik
      have hm2k : m + 2 ≤ k := by omega
      have hih1 := ih m (Nat.lt_succ_self m) (by omega) hm2k
      dsimp only [Nat.add_sub_cancel] at hih1
      obtain ⟨hu1_0, hu1_deg, hv1_0, hv1_deg, _⟩ := hih1
      obtain ⟨hq0, hq_deg, hq_lc⟩ := bezoutSturm_quot_props (j := m + 1) hd10 hpos hik
      let t0 := bezoutSturm FQ₀ FQ₁ (m + 1)
      let t1 := bezoutSturm FQ₀ FQ₁ (m + 2)
      let q := -((-t0.1) / t1.1)
      change q ≠ 0 at hq0
      change q.natDegree = t0.1.natDegree - t1.1.natDegree at hq_deg
      change q.leadingCoeff * t1.1.leadingCoeff = t0.1.leadingCoeff at hq_lc
      change t1.2.1 ≠ 0 at hu1_0
      change t1.2.1.natDegree = FQ₁.natDegree - t0.1.natDegree at hu1_deg
      change t1.2.2 ≠ 0 at hv1_0
      change t1.2.2.natDegree = FQ₀.natDegree - t0.1.natDegree at hv1_deg
      have hdeg_t1_t0 : t1.1.natDegree < t0.1.natDegree :=
        bezoutSturm_natDegree_lt hd10 hpos (m + 2) (by omega) hm2k
      have hdeg_t0_le_d1 : t0.1.natDegree ≤ FQ₁.natDegree :=
        bezoutSturm_natDegree_le_d1 hd10 hpos (m + 1) (by omega) (by omega)
      have hqu_ne : q * t1.2.1 ≠ 0 := mul_ne_zero hq0 hu1_0
      have hqu_nat : (q * t1.2.1).natDegree = FQ₁.natDegree - t1.1.natDegree := by
        rw [natDegree_mul hq0 hu1_0, hq_deg, hu1_deg]; omega
      have hqv_ne : q * t1.2.2 ≠ 0 := mul_ne_zero hq0 hv1_0
      have hqv_nat : (q * t1.2.2).natDegree = FQ₀.natDegree - t1.1.natDegree := by
        rw [natDegree_mul hq0 hv1_0, hq_deg, hv1_deg]; omega
      have hdeg_lt_prev (m' D : ℕ) (hm'_eq : m = m' + 1)
          (hD_bound : (bezoutSturm FQ₀ FQ₁ (m' + 1)).1.natDegree ≤ D)
          (a b : ℚ[X]) (ha : a ≠ 0) (hb : b ≠ 0)
          (ha_deg : a.natDegree = D - (bezoutSturm FQ₀ FQ₁ (m' + 1)).1.natDegree)
          (hb_deg : b.natDegree = D - t1.1.natDegree) : a.degree < b.degree := by
        have hprev : t0.1.natDegree < (bezoutSturm FQ₀ FQ₁ (m' + 1)).1.natDegree := by
          dsimp only [t0]; rw [hm'_eq]
          exact bezoutSturm_natDegree_lt hd10 hpos (m' + 2) (by omega) (by omega)
        rw [degree_eq_natDegree ha, degree_eq_natDegree hb]
        exact Nat.cast_lt.mpr (by omega)
      have hu0_deg_lt : t0.2.1.degree < (q * t1.2.1).degree := by
        rcases m with _ | m'
        · rw [show t0.2.1 = 0 from rfl, degree_zero, degree_eq_natDegree hqu_ne]
          exact WithBot.bot_lt_coe _
        · obtain ⟨hu0_ne, hu0_deg, _, _, _⟩ := ih m' (by omega) (by omega) (by omega)
          exact hdeg_lt_prev m' FQ₁.natDegree rfl
            (bezoutSturm_natDegree_le_d1 hd10 hpos (m' + 1) (by omega) (by omega))
            t0.2.1 (q * t1.2.1) hu0_ne hqu_ne hu0_deg hqu_nat
      obtain ⟨hu2_ne, hu2_deg, _⟩ := sub_ne_zero_and_natDegree_and_leadingCoeff hqu_ne hu0_deg_lt
      have hv0_deg_lt : t0.2.2.degree < (q * t1.2.2).degree := by
        rcases m with _ | m'
        · rw [show t0.2.2 = 1 from rfl, degree_one, degree_eq_natDegree hqv_ne]
          have ht1_lt_d0 : t1.1.natDegree < FQ₀.natDegree :=
            lt_of_lt_of_le hdeg_t1_t0 (hdeg_t0_le_d1.trans hd10.le)
          rw [show (0 : WithBot ℕ) = ((0 : ℕ) : WithBot ℕ) from rfl]
          exact Nat.cast_lt.mpr (by rw [hqv_nat]; omega)
        · obtain ⟨_, _, hv0_ne, hv0_deg, _⟩ := ih m' (by omega) (by omega) (by omega)
          exact hdeg_lt_prev m' FQ₀.natDegree rfl
            ((bezoutSturm_natDegree_le_d1 hd10 hpos (m' + 1) (by omega) (by omega)).trans hd10.le)
            t0.2.2 (q * t1.2.2) hv0_ne hqv_ne hv0_deg hqv_nat
      obtain ⟨hv2_ne, hv2_deg, hv2_lc⟩ :=
        sub_ne_zero_and_natDegree_and_leadingCoeff hqv_ne hv0_deg_lt
      have hlc_rel : (q * t1.2.2 - t0.2.2).leadingCoeff * t1.1.leadingCoeff =
          t0.1.leadingCoeff * t1.2.2.leadingCoeff := by
        rw [hv2_lc, leadingCoeff_mul]
        linear_combination t1.2.2.leadingCoeff * hq_lc
      dsimp only [Nat.add_sub_cancel]
      exact ⟨hu2_ne, hu2_deg.trans hqu_nat, hv2_ne, hv2_deg.trans hqv_nat, hlc_rel⟩

/-! ### Part 3: Sylvester linear system and normalized Bézout/remainder bounds -/

private noncomputable def polyFromFin {R : Type*} [CommSemiring R] {k : ℕ} (w : Fin k → R) :
    R[X] :=
  ∑ a : Fin k, C (w a) * X ^ a.1

private theorem coeff_polyFromFin {R : Type*} [CommSemiring R] {k : ℕ} (w : Fin k → R) (m : ℕ) :
    (polyFromFin w).coeff m = if hm : m < k then w ⟨m, hm⟩ else 0 := by
  rw [polyFromFin, Polynomial.finsetSum_coeff]
  by_cases hm : m < k
  · rw [dite_eq_left hm, Finset.sum_eq_single ⟨m, hm⟩]
    · rw [coeff_C_mul, coeff_X_pow_self, mul_one]
    · intro a _ hne
      have hne_val : m ≠ a.1 := fun h => hne (Fin.ext h.symm)
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right hne_val, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · rw [dite_eq_right hm]
    refine Finset.sum_eq_zero fun a _ => ?_
    have hne_val : m ≠ a.1 := fun h => hm (h ▸ a.2)
    rw [coeff_C_mul, coeff_X_pow, ite_eq_right hne_val, mul_zero]

private theorem polyFromFin_eq_of_natDegree_lt {R : Type*} [CommSemiring R] {k : ℕ} (p : R[X])
    (hp : p = 0 ∨ p.natDegree < k) :
    polyFromFin (fun a : Fin k => p.coeff a.1) = p := by
  ext m
  rw [coeff_polyFromFin]
  by_cases hm : m < k
  · rw [dite_eq_left hm]
  · rw [dite_eq_right hm]
    rcases hp with rfl | hdeg
    · simp only [coeff_zero]
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

private theorem coeff_polyFromFin_mul {R : Type*} [CommSemiring R] {k : ℕ} (w : Fin k → R)
    (P : R[X]) (m : ℕ) :
    (polyFromFin w * P).coeff m =
      ∑ a : Fin k, w a * (if a.1 ≤ m then P.coeff (m - a.1) else 0) := by
  rw [polyFromFin, Finset.sum_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_assoc, coeff_C_mul, mul_comm (X ^ a.1) P, coeff_mul_X_pow']

private theorem coeff_polyFromFin_mul_eq_zero_of_gt {R : Type*} [CommSemiring R] {k : ℕ}
    (w : Fin k → R) (P : R[X]) {D m : ℕ} (hP : P = 0 ∨ P.natDegree ≤ D) (hm : k + D ≤ m) :
    (polyFromFin w * P).coeff m = 0 := by
  rw [coeff_polyFromFin_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with ha
  · rcases hP with rfl | hdeg
    · simp only [coeff_zero, mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  · simp only [mul_zero]

private theorem normalized_bezoutSturm_cramer {F₀ F₁ : ℤ[X]} {H : ℕ} (hH : 1 ≤ H)
    (hF₀ : ∀ m, Int.natAbs (F₀.coeff m) ≤ H) (hF₁ : ∀ m, Int.natAbs (F₁.coeff m) ≤ H)
    (h0 : F₀.map (algebraMap ℤ ℚ) ≠ 0)
    (hd10 : (F₁.map (algebraMap ℤ ℚ)).natDegree < (F₀.map (algebraMap ℤ ℚ)).natDegree)
    {k i : ℕ} (hpos : ∀ r ≤ k, (bezoutSturm (F₀.map (algebraMap ℤ ℚ))
      (F₁.map (algebraMap ℤ ℚ)) r).1 ≠ 0)
    (hi2 : 2 ≤ i) (hik : i ≤ k) :
    let FQ₀ := F₀.map (algebraMap ℤ ℚ)
    let FQ₁ := F₁.map (algebraMap ℤ ℚ)
    let ti := bezoutSturm FQ₀ FQ₁ i
    let ci := ti.1.leadingCoeff
    let n := FQ₀.natDegree + 1
    let M := (2 * n * H) ^ (2 * n)
    let vTildeLc := ti.2.2.leadingCoeff / ci
    Int.natAbs vTildeLc.num ≤ M ∧ vTildeLc.den ≤ M ∧
    ∃ (dDet : ℤ) (EInt : ℤ[X]),
      dDet ≠ 0 ∧ Int.natAbs dDet ≤ M ∧
      (∀ r, Int.natAbs (EInt.coeff r) ≤ 2 * n * M * H) ∧
      (∀ r, (C ci⁻¹ * ti.1).coeff r = (EInt.coeff r : ℚ) / (dDet : ℚ)) := by
  dsimp only
  let FQ₀ := F₀.map (algebraMap ℤ ℚ)
  let FQ₁ := F₁.map (algebraMap ℤ ℚ)
  let ti := bezoutSturm FQ₀ FQ₁ i
  let ti1 := bezoutSturm FQ₀ FQ₁ (i - 1)
  let d₀ := FQ₀.natDegree
  let d₁ := FQ₁.natDegree
  have hd10' : d₁ < d₀ := hd10
  let d := ti.1.natDegree
  let δ := ti1.1.natDegree
  have hti0 : ti.1 ≠ 0 := hpos i hik
  have hci0 : ti.1.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hti0
  have hd_lt_δ : d < δ := bezoutSturm_natDegree_lt hd10 hpos i (by omega) hik
  have hδ_le_d1 : δ ≤ d₁ := bezoutSturm_natDegree_le_d1 hd10 hpos (i - 1) (by omega) (by omega)
  obtain ⟨hu0, hu_deg, hv0, hv_deg, _⟩ := bezoutSturm_uv_props hd10 hpos i hi2 hik
  change ti.2.1 ≠ 0 at hu0
  change ti.2.1.natDegree = d₁ - δ at hu_deg
  change ti.2.2 ≠ 0 at hv0
  change ti.2.2.natDegree = d₀ - δ at hv_deg
  obtain ⟨_, hbez_cur, hdet_prev⟩ := bezoutSturm_rel FQ₀ FQ₁ (i - 1)
  have hi_eq : i - 1 + 1 = i := by omega
  rw [hi_eq] at hbez_cur hdet_prev
  change ti.2.1 * FQ₀ + ti.2.2 * FQ₁ = ti.1 at hbez_cur
  change ti1.2.1 * ti.2.2 - ti.2.1 * ti1.2.2 = 1 at hdet_prev
  let nu := d₁ - δ + 1
  let nv := d₀ - δ + 1
  let N := nu + nv
  let Dtop := d₀ + d₁ - δ
  let R := Dtop - d + 1
  let S : Matrix (Fin R) (Fin N) ℤ := fun r =>
    Fin.addCases
      (fun a : Fin nu => if a.1 ≤ d + r.1 then F₀.coeff (d + r.1 - a.1) else 0)
      (fun b : Fin nv => if b.1 ≤ d + r.1 then F₁.coeff (d + r.1 - b.1) else 0)
  let rhs : Fin R → ℤ := fun r => if r.1 = 0 then 1 else 0
  have hS_bound : ∀ r j, Int.natAbs (S r j) ≤ H := fun r j => by
    have hb (P : ℤ[X]) (hP : ∀ m, Int.natAbs (P.coeff m) ≤ H) (k : ℕ) :
        Int.natAbs (if k ≤ d + r.1 then P.coeff (d + r.1 - k) else 0) ≤ H := by
      split_ifs <;> simp [hP]
    dsimp only [S]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · rw [Fin.addCases_left]; exact hb F₀ hF₀ a.1
    · rw [Fin.addCases_right]; exact hb F₁ hF₁ b.1
  have hrhs_bound : ∀ r, Int.natAbs (rhs r) ≤ H := fun r => by dsimp only [rhs]; split_ifs <;> omega
  have hmulVec_eq : ∀ (z : Fin N → ℚ) (r : Fin R),
      ((S.map (algebraMap ℤ ℚ)) *ᵥ z) r =
        (polyFromFin (fun a : Fin nu => z (Fin.castAdd nv a)) * FQ₀ +
          polyFromFin (fun b : Fin nv => z (Fin.natAdd nu b)) * FQ₁).coeff (d + r.1) := by
    intro z r
    rw [coeff_add, coeff_polyFromFin_mul, coeff_polyFromFin_mul]
    change ∑ j : Fin (nu + nv), ((S.map (algebraMap ℤ ℚ)) r j) * z j = _
    rw [Fin.sum_univ_add]
    congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_
    · change algebraMap ℤ ℚ (S r (Fin.castAdd nv a)) * z (Fin.castAdd nv a) = _
      dsimp only [S, FQ₀]; rw [Fin.addCases_left]
      split_ifs <;> simp only [coeff_map, mul_comm, map_zero, zero_mul]
    · change algebraMap ℤ ℚ (S r (Fin.natAdd nu a)) * z (Fin.natAdd nu a) = _
      dsimp only [S, FQ₁]; rw [Fin.addCases_right]
      split_ifs <;> simp only [coeff_map, mul_comm, map_zero, zero_mul]
  let uTilde : ℚ[X] := C ti.1.leadingCoeff⁻¹ * ti.2.1
  let vTilde : ℚ[X] := C ti.1.leadingCoeff⁻¹ * ti.2.2
  let eTilde : ℚ[X] := C ti.1.leadingCoeff⁻¹ * ti.1
  have huT_deg : uTilde.natDegree < nu := by
    dsimp only [uTilde, nu]
    rw [natDegree_C_mul (inv_ne_zero hci0), hu_deg]
    omega
  have hvT_deg : vTilde.natDegree < nv := by
    dsimp only [vTilde, nv]
    rw [natDegree_C_mul (inv_ne_zero hci0), hv_deg]
    omega
  let xSol : Fin N → ℚ :=
    Fin.addCases (fun a : Fin nu => uTilde.coeff a.1) (fun b : Fin nv => vTilde.coeff b.1)
  have hxSol_u : polyFromFin (fun a : Fin nu => xSol (Fin.castAdd nv a)) = uTilde := by
    simp only [xSol, Fin.addCases_left]
    exact polyFromFin_eq_of_natDegree_lt uTilde (Or.inr huT_deg)
  have hxSol_v : polyFromFin (fun b : Fin nv => xSol (Fin.natAdd nu b)) = vTilde := by
    simp only [xSol, Fin.addCases_right]
    exact polyFromFin_eq_of_natDegree_lt vTilde (Or.inr hvT_deg)
  have heT_bez : uTilde * FQ₀ + vTilde * FQ₁ = eTilde := by
    dsimp only [uTilde, vTilde, eTilde]
    linear_combination C ti.1.leadingCoeff⁻¹ * hbez_cur
  have hxSol_sys : (S.map (algebraMap ℤ ℚ)) *ᵥ xSol = (algebraMap ℤ ℚ) ∘ rhs := by
    ext r
    rw [hmulVec_eq, hxSol_u, hxSol_v, heT_bez, Function.comp_apply]
    by_cases hr0 : r.1 = 0
    · simp only [rhs, hr0, ↓reduceIte, map_one, add_zero, eTilde, coeff_C_mul]
      change ti.1.leadingCoeff⁻¹ * ti.1.coeff ti.1.natDegree = 1
      rw [← leadingCoeff, inv_mul_cancel₀ hci0]
    · simp only [rhs, hr0, ↓reduceIte, map_zero]
      have heT_nat : eTilde.natDegree = d := natDegree_C_mul (inv_ne_zero hci0)
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hinj : ∀ z : Fin N → ℚ, (S.map (algebraMap ℤ ℚ)) *ᵥ z = 0 → z = 0 := by
    intro z hz
    let u := polyFromFin (fun a : Fin nu => z (Fin.castAdd nv a))
    let v := polyFromFin (fun b : Fin nv => z (Fin.natAdd nu b))
    let W := u * FQ₀ + v * FQ₁
    have hW_coeff_zero : ∀ m, d ≤ m → W.coeff m = 0 := fun m hm => by
      by_cases hmD : m ≤ Dtop
      · have hr_lt : m - d < R := by dsimp only [R, Dtop] at *; omega
        have hzr := congrFun hz ⟨m - d, hr_lt⟩
        rw [Pi.zero_apply, hmulVec_eq] at hzr
        simpa only [show d + (m - d) = m by omega] using hzr
      · dsimp only [W]
        rw [coeff_add,
          coeff_polyFromFin_mul_eq_zero_of_gt (D := d₀) _ FQ₀ (Or.inr le_rfl)
            (by dsimp only [nu, Dtop] at *; omega),
          coeff_polyFromFin_mul_eq_zero_of_gt (D := d₁) _ FQ₁ (Or.inr le_rfl)
            (by dsimp only [nv, Dtop] at *; omega),
          add_zero]
    have hcross_eq : (u * ti.2.2 - v * ti.2.1) * FQ₀ = ti.2.2 * W - v * ti.1 := by
      dsimp only [W]
      linear_combination -v * hbez_cur
    have hW_deg : W = 0 ∨ W.natDegree < d := or_iff_not_imp_left.2 fun hW0 =>
      not_le.1 fun hge => leadingCoeff_ne_zero.mpr hW0 (hW_coeff_zero W.natDegree hge)
    have hv_deg_bound : v = 0 ∨ v.natDegree ≤ d₀ - δ := or_iff_not_imp_left.2 fun hv_z =>
      not_lt.1 fun hgt => leadingCoeff_ne_zero.mpr hv_z <| by
        have hlt_nv : nv ≤ v.natDegree := hgt
        change (polyFromFin (fun b : Fin nv => z (Fin.natAdd nu b))).coeff v.natDegree = 0
        rw [coeff_polyFromFin, dite_eq_right (not_lt.mpr hlt_nv)]
    have hrhs_lt_d0 : ∀ m, d₀ ≤ m → (ti.2.2 * W - v * ti.1).coeff m = 0 := fun m hm => by
      have hmul_zero {P Q : ℚ[X]} (hdeg : Q = 0 ∨ P.natDegree + Q.natDegree < m) :
          (P * Q).coeff m = 0 := by
        rcases hdeg with rfl | hlt
        · simp only [mul_zero, coeff_zero]
        · exact coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt hlt)
      rw [coeff_sub, hmul_zero (P := ti.2.2) (hW_deg.imp id fun h => by omega),
        mul_comm v ti.1, hmul_zero (P := ti.1) (hv_deg_bound.imp id fun h => by omega), sub_self]
    have huv_rel : u * ti.2.2 - v * ti.2.1 = 0 := by
      by_contra hne
      have hdeg_ge : d₀ ≤ ((u * ti.2.2 - v * ti.2.1) * FQ₀).natDegree := by
        rw [natDegree_mul hne h0]; exact Nat.le_add_left _ _
      have hc := congrArg (fun p => p.coeff ((u * ti.2.2 - v * ti.2.1) * FQ₀).natDegree) hcross_eq
      exact leadingCoeff_ne_zero.mpr (mul_ne_zero hne h0) (hc.trans (hrhs_lt_d0 _ hdeg_ge))
    have huv_eq : v * ti.2.1 = u * ti.2.2 := (sub_eq_zero.mp huv_rel).symm
    let qFactor : ℚ[X] := ti1.2.1 * v - ti1.2.2 * u
    have hv_fac : v = ti.2.2 * qFactor := by
      dsimp only [qFactor]
      linear_combination -v * hdet_prev - ti1.2.2 * huv_eq
    obtain ⟨c, hc_eq⟩ : ∃ c : ℚ, qFactor = C c := by
      by_cases hqF : qFactor = 0
      · exact ⟨0, by rw [hqF, C_0]⟩
      · have hv_ne : v ≠ 0 := by rw [hv_fac]; exact mul_ne_zero hv0 hqF
        rcases hv_deg_bound with hv_z | hvd
        · exact absurd hv_z hv_ne
        · have hdeg_sum : v.natDegree = (d₀ - δ) + qFactor.natDegree := by
            rw [hv_fac, natDegree_mul hv0 hqF, hv_deg]
          have hqF_deg0 : qFactor.natDegree = 0 := by omega
          exact ⟨qFactor.coeff 0, eq_C_of_natDegree_eq_zero hqF_deg0⟩
    rw [hc_eq] at hv_fac
    have hu_fac : u = ti.2.1 * C c :=
      mul_right_cancel₀ hv0 (by linear_combination -huv_eq + ti.2.1 * hv_fac)
    have hW_eq : W = C c * ti.1 := by
      dsimp only [W]
      rw [hu_fac, hv_fac]
      linear_combination C c * hbez_cur
    have hc0 : c = 0 := by
      have hWd0 := hW_coeff_zero d le_rfl
      rw [hW_eq, coeff_C_mul] at hWd0
      exact (mul_eq_zero.mp hWd0).resolve_right hci0
    have hu_z : u = 0 := by rw [hu_fac, hc0, C_0, mul_zero]
    have hv_z : v = 0 := by rw [hv_fac, hc0, C_0, mul_zero]
    ext j
    rw [Pi.zero_apply]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · have hc := congrArg (fun p => p.coeff a.1) hu_z
      simpa only [u, coeff_polyFromFin, dite_eq_left a.2, coeff_zero] using hc
    · have hc := congrArg (fun p => p.coeff b.1) hv_z
      simpa only [v, coeff_polyFromFin, dite_eq_left b.2, coeff_zero] using hc
  obtain ⟨dDet, nums, hdDet0, hdDet_le, hnums_le, hxSol_rep⟩ :=
    exists_cramer_rep_of_inj_mulVec S rhs hS_bound hrhs_bound xSol hxSol_sys hinj
  let n := d₀ + 1
  let M := (2 * n * H) ^ (2 * n)
  have hN_le : N ≤ 2 * n := by dsimp only [N, nu, nv, n]; omega
  have hNH_le_M : (N * H) ^ N ≤ M :=
    (Nat.pow_le_pow_left (Nat.mul_le_mul_right H hN_le) N).trans
      (Nat.pow_le_pow_right (Nat.mul_pos (by omega) hH) hN_le)
  have hdDet_M : Int.natAbs dDet ≤ M := hdDet_le.trans hNH_le_M
  have hnums_M : ∀ j, Int.natAbs (nums j) ≤ M := fun j => (hnums_le j).trans hNH_le_M
  have hvT_lc_eq : ti.2.2.leadingCoeff / ti.1.leadingCoeff = vTilde.coeff (d₀ - δ) := by
    dsimp only [vTilde]
    rw [coeff_C_mul, ← hv_deg, ← leadingCoeff, div_eq_inv_mul]
  have hvT_idx_lt : d₀ - δ < nv := by dsimp only [nv]; omega
  have hvT_rep : ti.2.2.leadingCoeff / ti.1.leadingCoeff =
      (nums (Fin.natAdd nu ⟨d₀ - δ, hvT_idx_lt⟩) : ℚ) / (dDet : ℚ) := by
    rw [hvT_lc_eq]
    simpa only [xSol, Fin.addCases_right] using hxSol_rep (Fin.natAdd nu ⟨d₀ - δ, hvT_idx_lt⟩)
  obtain ⟨hv_num_le, hv_den_le⟩ := rat_num_den_le_of_eq_div hdDet0 hvT_rep
  let UInt : ℤ[X] := polyFromFin (fun a : Fin nu => nums (Fin.castAdd nv a))
  let VInt : ℤ[X] := polyFromFin (fun b : Fin nv => nums (Fin.natAdd nu b))
  let EInt : ℤ[X] := UInt * F₀ + VInt * F₁
  have hmap_part {K : ℕ} (idx : Fin K → Fin N) (p : ℚ[X]) (hp_deg : p.natDegree < K)
      (hp_eq : ∀ a : Fin K, xSol (idx a) = p.coeff a.1) :
      (polyFromFin (fun a : Fin K => nums (idx a))).map (algebraMap ℤ ℚ) =
        C (dDet : ℚ) * p := by
    ext m
    rw [coeff_map, coeff_C_mul, coeff_polyFromFin]
    by_cases hm : m < K
    · rw [dite_eq_left hm, ← hp_eq ⟨m, hm⟩, hxSol_rep (idx ⟨m, hm⟩),
        mul_div_cancel₀ _ (Int.cast_ne_zero.mpr hdDet0), eq_intCast]
    · rw [dite_eq_right hm, map_zero, coeff_eq_zero_of_natDegree_lt (hp_deg.trans_le (by omega)),
        mul_zero]
  have hUInt_map : UInt.map (algebraMap ℤ ℚ) = C (dDet : ℚ) * uTilde :=
    hmap_part (Fin.castAdd nv) uTilde huT_deg fun a => by simp only [xSol, Fin.addCases_left]
  have hVInt_map : VInt.map (algebraMap ℤ ℚ) = C (dDet : ℚ) * vTilde :=
    hmap_part (Fin.natAdd nu) vTilde hvT_deg fun b => by simp only [xSol, Fin.addCases_right]
  have hEInt_map : EInt.map (algebraMap ℤ ℚ) = C (dDet : ℚ) * eTilde := by
    dsimp only [EInt, FQ₀, FQ₁] at *
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hUInt_map, hVInt_map,
      ← heT_bez]
    ring
  have hsum_int_natAbs : ∀ {s : ℕ} (w : Fin s → ℤ) (P : ℤ[X]) (r : ℕ),
      (∀ a, Int.natAbs (w a) ≤ M) → (∀ m, Int.natAbs (P.coeff m) ≤ H) →
      Int.natAbs ((polyFromFin w * P).coeff r) ≤ s * (M * H) := by
    intro s w P r hw hP
    rw [coeff_polyFromFin_mul]
    refine (Int.natAbs_sum_le _ _).trans
      ((Finset.sum_le_card_nsmul _ _ (M * H) fun a _ => ?_).trans_eq
        (by simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul]))
    rw [Int.natAbs_mul]
    refine Nat.mul_le_mul (hw a) ?_
    split_ifs <;> simp [hP]
  refine ⟨hv_num_le.trans (hnums_M _), hv_den_le.trans hdDet_M, dDet, EInt, hdDet0, hdDet_M,
    ?_, ?_⟩
  · intro r
    dsimp only [EInt]
    refine (coeff_add (UInt * F₀) (VInt * F₁) r ▸ Int.natAbs_add_le _ _).trans ?_
    have h1 := hsum_int_natAbs (fun a : Fin nu => nums (Fin.castAdd nv a)) F₀ r
      (fun a => hnums_M _) hF₀
    have h2 := hsum_int_natAbs (fun b : Fin nv => nums (Fin.natAdd nu b)) F₁ r
      (fun b => hnums_M _) hF₁
    calc _ ≤ nu * (M * H) + nv * (M * H) := Nat.add_le_add h1 h2
      _ = N * (M * H) := (add_mul _ _ _).symm
      _ ≤ 2 * n * M * H := by rw [← mul_assoc]; gcongr
  · intro r
    have hc := congrArg (fun p => p.coeff r) hEInt_map
    rw [coeff_map, coeff_C_mul, eq_intCast] at hc
    exact eq_div_of_mul_eq (Int.cast_ne_zero.mpr hdDet0) (by rw [mul_comm]; exact hc.symm)

/-! ### Part 4: Leading-coefficient telescoping and `hasCoeffBitBound_of_mem_sturmSeqList` -/

/-- Explicit polynomial bit-length upper bound `8 * (n + 1) ^ 3 * (B + 1)` on every entry of
`sturmSeqList cs` when `cs.length = n` and `HasCoeffBitBound B cs`. -/
@[expose] def sturmBitBound (n B : ℕ) : ℕ :=
  8 * (n + 1) ^ 3 * (B + 1)

private theorem bezoutSturm_leadingCoeff_bound {F₀ F₁ : ℤ[X]} {H : ℕ} (hH : 1 ≤ H)
    (hF₀ : ∀ m, Int.natAbs (F₀.coeff m) ≤ H) (hF₁ : ∀ m, Int.natAbs (F₁.coeff m) ≤ H)
    (h0 : F₀.map (algebraMap ℤ ℚ) ≠ 0)
    (hd10 : (F₁.map (algebraMap ℤ ℚ)).natDegree < (F₀.map (algebraMap ℤ ℚ)).natDegree)
    {k : ℕ} (hpos : ∀ r ≤ k, (bezoutSturm (F₀.map (algebraMap ℤ ℚ))
      (F₁.map (algebraMap ℤ ℚ)) r).1 ≠ 0) :
    let FQ₀ := F₀.map (algebraMap ℤ ℚ)
    let FQ₁ := F₁.map (algebraMap ℤ ℚ)
    let n := FQ₀.natDegree + 1
    let M := (2 * n * H) ^ (2 * n)
    ∀ i ≤ k,
      Int.natAbs (bezoutSturm FQ₀ FQ₁ i).1.leadingCoeff.num ≤ H * M ^ i ∧
      (bezoutSturm FQ₀ FQ₁ i).1.leadingCoeff.den ≤ H * M ^ i := by
  dsimp only
  set FQ₀ := F₀.map (algebraMap ℤ ℚ)
  set FQ₁ := F₁.map (algebraMap ℤ ℚ)
  set n := FQ₀.natDegree + 1
  set M := (2 * n * H) ^ (2 * n)
  have hHM_ge : H ≤ M :=
    (Nat.le_mul_of_pos_left H (by omega)).trans (Nat.le_self_pow (by omega) (2 * n * H))
  have hM_ge1 : 1 ≤ M := hH.trans hHM_ge
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hik
    rcases i with _ | _ | j
    · simp only [bezoutSturm, pow_zero, mul_one, FQ₀, leadingCoeff, coeff_map, eq_intCast,
        Rat.num_intCast, Rat.den_intCast]
      exact ⟨hF₀ _, hH⟩
    · simp only [bezoutSturm, Nat.zero_add, pow_one, FQ₁, leadingCoeff, coeff_map, eq_intCast,
        Rat.num_intCast, Rat.den_intCast]
      exact ⟨(hF₁ _).trans (Nat.le_mul_of_pos_right H hM_ge1),
        hH.trans (Nat.le_mul_of_pos_right H hM_ge1)⟩
    · have hj_prev := ih j (by omega) (by omega)
      obtain ⟨_, _, hv_ne, _, hlc_rel⟩ := bezoutSturm_uv_props hd10 hpos (j + 2) (by omega) hik
      set tj := bezoutSturm FQ₀ FQ₁ j
      set tj1 := bezoutSturm FQ₀ FQ₁ (j + 1)
      set tj2 := bezoutSturm FQ₀ FQ₁ (j + 2)
      have hlc_rel' :
          tj2.2.2.leadingCoeff * tj1.1.leadingCoeff = tj.1.leadingCoeff * tj1.2.2.leadingCoeff :=
        hlc_rel
      have hcj1_ne : tj1.1.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (hpos (j + 1) (by omega))
      have hcj2_ne : tj2.1.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (hpos (j + 2) hik)
      let vT1 : ℚ := tj1.2.2.leadingCoeff / tj1.1.leadingCoeff
      let vT2 : ℚ := tj2.2.2.leadingCoeff / tj2.1.leadingCoeff
      have hvT2_ne : vT2 ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hv_ne) hcj2_ne
      have hratio : tj2.1.leadingCoeff = tj.1.leadingCoeff * (vT1 / vT2) := by
        dsimp only [vT1, vT2]
        have hv2_ne' : tj2.2.2.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hv_ne
        field_simp [hcj1_ne, hcj2_ne, hv2_ne']
        linear_combination hlc_rel'
      obtain ⟨hvT2_num, hvT2_den, _⟩ :=
        normalized_bezoutSturm_cramer hH hF₀ hF₁ h0 hd10 hpos (by omega : 2 ≤ j + 2) hik
      have hvT1_bound : Int.natAbs vT1.num ≤ M ∧ vT1.den ≤ M := by
        rcases j with _ | j'
        · have hv1_eq : vT1 = ((1 : ℤ) : ℚ) / ((F₁.coeff FQ₁.natDegree : ℤ) : ℚ) := by
            dsimp only [vT1, tj1, bezoutSturm, FQ₁]
            rw [leadingCoeff_one, leadingCoeff, coeff_map, eq_intCast, Int.cast_one]
          have hc1_ne : F₁.coeff FQ₁.natDegree ≠ 0 := by
            intro h0'
            apply hcj1_ne
            dsimp only [tj1, bezoutSturm, FQ₁]
            rw [leadingCoeff, coeff_map, h0', map_zero]
          obtain ⟨hn1, hd1⟩ := rat_num_den_le_of_eq_div hc1_ne hv1_eq
          exact ⟨hn1.trans hM_ge1, (hd1.trans (hF₁ _)).trans hHM_ge⟩
        · obtain ⟨hn1, hd1, _⟩ :=
            normalized_bezoutSturm_cramer hH hF₀ hF₁ h0 hd10 hpos (by omega : 2 ≤ j' + 2)
              (by omega)
          exact ⟨hn1, hd1⟩
      rw [hratio]
      obtain ⟨hn, hd⟩ :=
        rat_mul_div_num_den_le hvT2_ne hj_prev hvT1_bound ⟨hvT2_num, hvT2_den⟩
      have hpow_eq : H * M ^ j * M ^ 2 = H * M ^ (j + 2) := by rw [pow_add]; ring
      exact ⟨hn.trans_eq hpow_eq, hd.trans_eq hpow_eq⟩

/-- **Polynomial coefficient bit-length bound for rational Sturm sequences**: if `cs : List ℚ`
satisfies `HasCoeffBitBound B cs`, then every polynomial `f ∈ sturmSeqList cs` satisfies
`HasCoeffBitBound (sturmBitBound cs.length B) f`. -/
theorem hasCoeffBitBound_of_mem_sturmSeqList {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs)
    {f : List ℚ} (hf : f ∈ sturmSeqList cs) :
    HasCoeffBitBound (sturmBitBound cs.length B) f := by
  classical
  let pList := CoeffList.trim cs
  have hp_ne_nil : pList ≠ [] := fun hnil => by
    simp only [sturmSeqList, show CoeffList.trim cs = [] from hnil, List.isEmpty_nil, ↓reduceIte,
      List.not_mem_nil] at hf
  have hP₀_ne : ofCoeffList pList ≠ 0 :=
    (CoeffList.isTrimmed_trim cs).ofCoeffList_ne_zero hp_ne_nil
  let n := cs.length
  have hp_len : pList.length ≤ n := CoeffList.length_trim_le cs
  have hn_pos : 1 ≤ n := (List.length_pos_of_ne_nil hp_ne_nil).trans_le hp_len
  have hpB : HasCoeffBitBound B pList := hB.trim
  let D := (clearDenomsList pList).1
  let ns := (clearDenomsList pList).2
  have hD_pos : 1 ≤ D := one_le_clearDenomsList_fst pList
  have hD_le : D ≤ 2 ^ (n * B) :=
    (lcmDens_le_of_bitBound hpB).trans
      (Nat.pow_le_pow_right zero_lt_two (Nat.mul_le_mul_right B hp_len))
  let F₀ : ℤ[X] := ofCoeffList ns
  let F₁ : ℤ[X] := derivative F₀
  let FQ₀ : ℚ[X] := F₀.map (algebraMap ℤ ℚ)
  let FQ₁ : ℚ[X] := F₁.map (algebraMap ℤ ℚ)
  have hFQ₀_eq : FQ₀ = C (D : ℚ) * ofCoeffList pList := by
    simpa only [FQ₀, F₀, D, ns] using ofCoeffList_clearDenomsList pList
  have hFQ₁_eq : FQ₁ = C (D : ℚ) * derivative (ofCoeffList pList) := by
    dsimp only [FQ₁, F₁]
    rw [← Polynomial.derivative_map, show F₀.map (algebraMap ℤ ℚ) = FQ₀ from rfl, hFQ₀_eq,
      derivative_C_mul]
  have hDQ_ne : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hFQ₀_ne : FQ₀ ≠ 0 := by rw [hFQ₀_eq]; exact mul_ne_zero (C_ne_zero.mpr hDQ_ne) hP₀_ne
  have hdeg_FQ₀ : FQ₀.natDegree < n := by
    rw [hFQ₀_eq, natDegree_C_mul hDQ_ne]
    have hdeg := CoeffList.length_trim_eq_natDegree_add_one
      (mt (CoeffList.trim_eq_nil_iff cs).mpr hp_ne_nil)
    change pList.length = (ofCoeffList cs).natDegree + 1 at hdeg
    rw [show ofCoeffList pList = ofCoeffList cs from CoeffList.ofCoeffList_trim cs]
    omega
  let eH := n + (n + 1) * B
  have hDH_exp : n * B ≤ eH := by dsimp only [eH]; rw [Nat.add_one_mul]; omega
  generalize hH_def : 2 ^ eH = H
  have hH_pos : 1 ≤ H := hH_def ▸ Nat.one_le_pow eH 2 zero_lt_two
  have hn_two_pow : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  have hF₀_coeff : ∀ m, Int.natAbs (F₀.coeff m) ≤ 2 ^ ((n + 1) * B) := fun m => by
    dsimp only [F₀]
    rw [coeff_ofCoeffList]
    by_cases hm : m < ns.length
    · rw [List.getD_eq_getElem _ _ hm]
      have hm' : m < pList.length := by
        simpa only [ns, clearDenomsList, List.length_map] using hm
      have hget : ns[m] = (pList[m]).num * ((D / (pList[m]).den : ℕ) : ℤ) := by
        simp only [ns, clearDenomsList, List.getElem_map, D]
      rw [hget, Int.natAbs_mul, Int.natAbs_natCast, show (n + 1) * B = B + n * B by ring, pow_add]
      exact Nat.mul_le_mul (hpB pList[m] (List.getElem_mem hm')).1
        ((Nat.div_le_self D (pList[m]).den).trans hD_le)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _
  have hF₀_H : ∀ m, Int.natAbs (F₀.coeff m) ≤ H := fun m =>
    hH_def ▸ (hF₀_coeff m).trans (Nat.pow_le_pow_right zero_lt_two (by dsimp only [eH]; omega))
  have hF₁_H : ∀ m, Int.natAbs (F₁.coeff m) ≤ H := fun m => by
    dsimp only [F₁]
    rw [coeff_derivative]
    by_cases hm1 : m + 1 < ns.length
    · have hns_len : ns.length = pList.length := by simp only [ns, clearDenomsList, List.length_map]
      have hm1_le : m + 1 ≤ n := by omega
      have hcast : F₀.coeff (m + 1) * ((m : ℤ) + 1) = F₀.coeff (m + 1) * ((m + 1 : ℕ) : ℤ) := by
        push_cast; rfl
      rw [hcast, Int.natAbs_mul, Int.natAbs_natCast]
      calc Int.natAbs (F₀.coeff (m + 1)) * (m + 1)
          ≤ 2 ^ ((n + 1) * B) * n := Nat.mul_le_mul (hF₀_coeff (m + 1)) hm1_le
        _ ≤ 2 ^ ((n + 1) * B) * 2 ^ n := Nat.mul_le_mul_left _ hn_two_pow
        _ = H := by rw [← hH_def]; dsimp only [eH]; rw [← pow_add, add_comm]
    · have hzero : F₀.coeff (m + 1) = 0 := by
        dsimp only [F₀]; rw [coeff_ofCoeffList, List.getD_eq_default _ _ (by omega)]
      rw [hzero, zero_mul]; exact Nat.zero_le H
  have hf_poly_mem : ofCoeffList f ∈
      Polynomial.sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs)) := by
    rw [← sturmSeqList_map_ofCoeffList cs]; exact List.mem_map_of_mem hf
  rw [← CoeffList.ofCoeffList_trim cs] at hf_poly_mem
  have hscaled_mem : C (D : ℚ) * ofCoeffList f ∈ Polynomial.sturmSeq FQ₀ FQ₁ := by
    rw [hFQ₀_eq, hFQ₁_eq, Polynomial.sturmSeq_mul_left (C_ne_zero.mpr hDQ_ne)]
    exact List.mem_map_of_mem hf_poly_mem
  obtain ⟨i, hsi, hpos⟩ := mem_sturmSeq_exists_bezoutSturm hFQ₀_ne hscaled_mem
  let n0 := FQ₀.natDegree + 1
  let M0 := (2 * n0 * H) ^ (2 * n0)
  have hn0_le : n0 ≤ n := by omega
  let eM := 2 * n * (n + 1 + eH)
  generalize hP_def : 2 ^ eM = P2
  have hP2_pos : 1 ≤ P2 := hP_def ▸ Nat.one_le_pow eM 2 zero_lt_two
  have hM0_le : M0 ≤ P2 := by
    rw [← hP_def]
    have hbase : 2 * n0 * H ≤ 2 ^ (n + 1 + eH) := by
      calc 2 * n0 * H
          ≤ 2 * n * H := Nat.mul_le_mul_right H (Nat.mul_le_mul_left 2 hn0_le)
        _ ≤ 2 * 2 ^ n * 2 ^ eH := by
            rw [← hH_def]
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hn_two_pow)
        _ = 2 ^ (n + 1 + eH) := by rw [show 2 * 2 ^ n = 2 ^ (n + 1) by ring, ← pow_add]
    calc M0 ≤ (2 ^ (n + 1 + eH)) ^ (2 * n0) := Nat.pow_le_pow_left hbase _
      _ ≤ (2 ^ (n + 1 + eH)) ^ (2 * n) :=
          Nat.pow_le_pow_right (Nat.one_le_pow _ 2 zero_lt_two) (Nat.mul_le_mul_left 2 hn0_le)
      _ = 2 ^ eM := by dsimp only [eM]; rw [← pow_mul, mul_comm]
  have hEi_coeff : ∀ r,
      let qr := ((bezoutSturm FQ₀ FQ₁ i).1).coeff r
      Int.natAbs qr.num ≤ 2 * n * H ^ 2 * P2 ^ (n + 1) ∧
      qr.den ≤ 2 * n * H ^ 2 * P2 ^ (n + 1) := by
    intro r
    dsimp only
    have hK_ge_H : H ≤ 2 * n * H ^ 2 * P2 ^ (n + 1) :=
      calc H ≤ H * (2 * n * H * P2 ^ (n + 1)) := Nat.le_mul_of_pos_right H
            (Nat.mul_pos (Nat.mul_pos (by omega) hH_pos) (Nat.pow_pos hP2_pos))
        _ = _ := by ring
    rcases i with _ | _ | j
    · simp only [bezoutSturm, FQ₀, coeff_map, eq_intCast, Rat.num_intCast, Rat.den_intCast]
      exact ⟨(hF₀_H r).trans hK_ge_H, hH_pos.trans hK_ge_H⟩
    · simp only [bezoutSturm, FQ₁, coeff_map, eq_intCast, Rat.num_intCast, Rat.den_intCast]
      exact ⟨(hF₁_H r).trans hK_ge_H, hH_pos.trans hK_ge_H⟩
    · have hFQ₁_ne : FQ₁ ≠ 0 := hpos 1 (by omega)
      have hd10 : FQ₁.natDegree < FQ₀.natDegree := by
        have hF1_ne : F₁ ≠ 0 := fun h0 => hFQ₁_ne (by simp only [FQ₁, h0, Polynomial.map_zero])
        have hdeg0 : FQ₀.natDegree = F₀.natDegree :=
          natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ)) F₀
        have hdeg1 : FQ₁.natDegree = F₁.natDegree :=
          natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ)) F₁
        rw [hdeg0, hdeg1]
        exact natDegree_derivative_lt fun hd0 =>
          hF1_ne (by dsimp only [F₁]; rw [eq_C_of_natDegree_eq_zero hd0, derivative_C])
      have hi_le_d0 : j + 2 ≤ FQ₀.natDegree := by
        have h := bezoutSturm_index_le_natDegree hd10 hpos (j + 2) le_rfl
        omega
      have hi_le_n : j + 2 ≤ n := by omega
      obtain ⟨hci_num, hci_den⟩ :=
        bezoutSturm_leadingCoeff_bound hH_pos hF₀_H hF₁_H hFQ₀_ne hd10 hpos (j + 2) le_rfl
      obtain ⟨_, _, dDet, EInt, hdDet0, hdDet_le, hEInt_le, heT_rep⟩ :=
        normalized_bezoutSturm_cramer hH_pos hF₀_H hF₁_H hFQ₀_ne hd10 hpos (by omega : 2 ≤ j + 2)
          le_rfl
      set ti := bezoutSturm FQ₀ FQ₁ (j + 2)
      set ci := ti.1.leadingCoeff
      have hci_ne : ci ≠ 0 := leadingCoeff_ne_zero.mpr (hpos (j + 2) le_rfl)
      have hqr_eq : ti.1.coeff r =
          ((ci.num * EInt.coeff r : ℤ) : ℚ) / (((ci.den : ℤ) * dDet : ℤ) : ℚ) := by
        have hmul_c : ti.1.coeff r = ci * (C ci⁻¹ * ti.1).coeff r := by
          rw [coeff_C_mul, ← mul_assoc, mul_inv_cancel₀ hci_ne, one_mul]
        rw [hmul_c, heT_rep r]
        conv_lhs => rw [← Rat.num_div_den ci]
        have hd1 : (ci.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ci.den_nz
        have hd2 : (dDet : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hdDet0
        push_cast
        field_simp
      have hdenZ_ne : (ci.den : ℤ) * dDet ≠ 0 :=
        mul_ne_zero (Int.natCast_ne_zero.mpr ci.den_nz) hdDet0
      obtain ⟨hn_r, hd_r⟩ := rat_num_den_le_of_eq_div hdenZ_ne hqr_eq
      have hci_pow_le : H * M0 ^ (j + 2) ≤ H * P2 ^ n := Nat.mul_le_mul_left H
        ((Nat.pow_le_pow_left hM0_le _).trans (Nat.pow_le_pow_right hP2_pos hi_le_n))
      have hn_bound : Int.natAbs (ci.num * EInt.coeff r) ≤ 2 * n * H ^ 2 * P2 ^ (n + 1) := by
        rw [Int.natAbs_mul]
        calc Int.natAbs ci.num * Int.natAbs (EInt.coeff r)
            ≤ (H * P2 ^ n) * (2 * n0 * M0 * H) :=
              Nat.mul_le_mul (hci_num.trans hci_pow_le) (hEInt_le r)
          _ ≤ (H * P2 ^ n) * (2 * n * P2 * H) :=
              Nat.mul_le_mul_left _
                (Nat.mul_le_mul_right H
                  (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn0_le) hM0_le))
          _ = 2 * n * H ^ 2 * P2 ^ (n + 1) := by rw [pow_succ]; ring
      have hd_bound : Int.natAbs ((ci.den : ℤ) * dDet) ≤ 2 * n * H ^ 2 * P2 ^ (n + 1) := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
        have h1H : 1 ≤ 2 * n * H := Nat.mul_pos (by omega) hH_pos
        calc ci.den * Int.natAbs dDet
            ≤ (H * P2 ^ n) * P2 :=
              Nat.mul_le_mul (hci_den.trans hci_pow_le) (hdDet_le.trans hM0_le)
          _ = 1 * H * P2 ^ (n + 1) := by rw [pow_succ]; ring
          _ ≤ (2 * n * H) * H * P2 ^ (n + 1) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right H h1H)
          _ = 2 * n * H ^ 2 * P2 ^ (n + 1) := by ring
      exact ⟨hn_r.trans hn_bound, hd_r.trans hd_bound⟩
  intro q hq
  obtain ⟨r, hr_lt, rfl⟩ := List.mem_iff_getElem.mp hq
  have hcoeff_f : f[r] = (ofCoeffList f).coeff r := by
    rw [coeff_ofCoeffList, List.getD_eq_getElem _ _ hr_lt]
  have hcoeff_rel : (ofCoeffList f).coeff r = ((bezoutSturm FQ₀ FQ₁ i).1).coeff r / (D : ℚ) := by
    have hc := congrArg (fun p => p.coeff r) hsi
    rw [coeff_C_mul] at hc
    exact (eq_div_iff hDQ_ne).mpr (by rw [mul_comm]; exact hc)
  obtain ⟨hnum_Ei, hden_Ei⟩ := hEi_coeff r
  set qr := ((bezoutSturm FQ₀ FQ₁ i).1).coeff r
  have hdivD_eq : qr / (D : ℚ) = (qr.num : ℚ) / (((qr.den : ℤ) * (D : ℤ) : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den qr]
    push_cast
    rw [div_div]
  have hdenD_ne : (qr.den : ℤ) * (D : ℤ) ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr qr.den_nz) (Int.natCast_ne_zero.mpr (by omega))
  obtain ⟨hnum_f, hden_f⟩ := rat_num_den_le_of_eq_div hdenD_ne hdivD_eq
  rw [hcoeff_f, hcoeff_rel]
  let Kbig := 2 * n * H ^ 3 * P2 ^ (n + 1)
  have hKbig_le : Kbig ≤ 2 ^ sturmBitBound n B := by
    have hpow_form : Kbig ≤ 2 ^ (n + 1 + 3 * eH + (n + 1) * eM) := by
      dsimp only [Kbig]
      rw [← hH_def, ← hP_def]
      calc 2 * n * (2 ^ eH) ^ 3 * (2 ^ eM) ^ (n + 1)
          ≤ 2 * 2 ^ n * (2 ^ eH) ^ 3 * (2 ^ eM) ^ (n + 1) :=
            Nat.mul_le_mul_right _
              (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hn_two_pow))
        _ = 2 ^ (n + 1 + 3 * eH + (n + 1) * eM) := by
            rw [(pow_succ' 2 n).symm, ← pow_mul, ← pow_mul, mul_comm eH 3, mul_comm eM (n + 1),
              ← pow_add, ← pow_add]
    refine hpow_form.trans (Nat.pow_le_pow_right zero_lt_two ?_)
    have heH_le : n + 1 + eH ≤ 2 * (n + 1) * (B + 1) := by dsimp only [eH]; nlinarith
    have heM_le : eM ≤ 4 * (n + 1) ^ 2 * (B + 1) := by
      calc eM = 2 * n * (n + 1 + eH) := rfl
        _ ≤ 2 * (n + 1) * (2 * (n + 1) * (B + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.le_succ n)) heH_le
        _ = 4 * (n + 1) ^ 2 * (B + 1) := by ring
    dsimp only [sturmBitBound]
    nlinarith [Nat.pow_le_pow_left hn_pos 2]
  have hnum_K : Int.natAbs qr.num ≤ Kbig :=
    hnum_Ei.trans ((Nat.le_mul_of_pos_left _ hH_pos).trans_eq (by dsimp only [Kbig]; ring))
  have hden_K : Int.natAbs ((qr.den : ℤ) * (D : ℤ)) ≤ Kbig := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    have hDH : D ≤ H :=
      hH_def ▸ hD_le.trans (Nat.pow_le_pow_right zero_lt_two hDH_exp)
    exact (Nat.mul_le_mul hden_Ei hDH).trans_eq (by dsimp only [Kbig]; ring)
  exact ⟨(hnum_f.trans hnum_K).trans hKbig_le, (hden_f.trans hden_K).trans hKbig_le⟩

/-! ### Part 5: Unconditional active Sturm-interval count bound -/

private noncomputable def rootsInIntervals (P : ℝ[X]) : List (ℚ × ℚ) → Finset ℝ
  | [] => ∅
  | p :: ps =>
    P.roots.toFinset.filter (fun r => (p.1 : ℝ) < r ∧ r ≤ (p.2 : ℝ)) ∪ rootsInIntervals P ps

private theorem mem_rootsInIntervals {P : ℝ[X]} {r : ℝ} :
    ∀ {L : List (ℚ × ℚ)}, r ∈ rootsInIntervals P L →
      r ∈ P.roots.toFinset ∧ ∃ p ∈ L, (p.1 : ℝ) < r ∧ r ≤ (p.2 : ℝ)
  | [], h => by simp only [rootsInIntervals, Finset.notMem_empty] at h
  | p :: ps, h => by
    simp only [rootsInIntervals, Finset.mem_union, Finset.mem_filter] at h
    rcases h with ⟨hr, hp⟩ | htail
    · exact ⟨hr, p, List.mem_cons_self, hp⟩
    · obtain ⟨hr, q, hq, hqr⟩ := mem_rootsInIntervals htail
      exact ⟨hr, q, List.mem_cons_of_mem p hq, hqr⟩

private theorem card_rootsInIntervals_ge (P : ℝ[X]) :
    ∀ (L : List (ℚ × ℚ)),
      (∀ p ∈ L, 2 ≤ (P.roots.toFinset.filter (fun r => (p.1 : ℝ) < r ∧ r ≤ (p.2 : ℝ))).card) →
      L.Pairwise (fun p q => p.2 ≤ q.1) →
      2 * L.length ≤ (rootsInIntervals P L).card
  | [], _, _ => Nat.zero_le _
  | p :: ps, hcard, hpair => by
    rw [List.pairwise_cons] at hpair
    obtain ⟨hhead, htail_pair⟩ := hpair
    have ih := card_rootsInIntervals_ge P ps
      (fun q hq => hcard q (List.mem_cons_of_mem p hq)) htail_pair
    let Sp := P.roots.toFinset.filter (fun r => (p.1 : ℝ) < r ∧ r ≤ (p.2 : ℝ))
    have hdisj : Disjoint Sp (rootsInIntervals P ps) := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      simp only [Sp, Finset.mem_filter] at hr1
      obtain ⟨_, q, hq, hqr⟩ := mem_rootsInIntervals hr2
      have hpq : (p.2 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast hhead q hq
      linarith [hr1.2.2, hqr.1]
    simp only [rootsInIntervals, List.length_cons]
    change 2 * (ps.length + 1) ≤ (Sp ∪ rootsInIntervals P ps).card
    rw [Finset.card_union_of_disjoint hdisj]
    have hp2 : 2 ≤ Sp.card := hcard p List.mem_cons_self
    omega

/-- **Active Sturm-interval count bound**: for any coefficient list `cs : List ℚ` (including
non-squarefree polynomials) and any pairwise-disjoint ordered list `L : List (ℚ × ℚ)` of intervals
`(u, v]` on each of which `sturmVariationsList (sturmSeqList cs)` drops by at least `2`,
`L.length ≤ 2 * cs.length`. -/
theorem card_active_sturm_intervals_le (cs : List ℚ) (L : List (ℚ × ℚ))
    (hmem : ∀ p ∈ L, p.1 < p.2 ∧
      2 ≤ sturmVariationsList (sturmSeqList cs) p.1 - sturmVariationsList (sturmSeqList cs) p.2)
    (hpair : L.Pairwise (fun p q => p.2 ≤ q.1)) :
    L.length ≤ 2 * cs.length := by
  classical
  by_cases hcs0 : ofCoeffList cs = 0
  · cases L with
    | nil => simp only [List.length_nil, Nat.zero_le]
    | cons p ps =>
      have hseq : sturmSeqList cs = [] := by
        have ht : CoeffList.trim cs = [] := (CoeffList.trim_eq_nil_iff cs).mpr hcs0
        simp only [sturmSeqList, ht, List.isEmpty_nil, ↓reduceIte]
      have hp := (hmem p List.mem_cons_self).2
      simp only [hseq, sturmVariationsList, List.map_nil, List.signVariations_nil,
        Nat.sub_self] at hp
      omega
  · let P : ℝ[X] := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hcs0
    have hP_deg_lt : P.natDegree < cs.length := by
      rw [natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective]
      have h1 := CoeffList.length_trim_eq_natDegree_add_one hcs0
      have h2 := CoeffList.length_trim_le cs
      omega
    set g := EuclideanDomain.gcd P (derivative P)
    have hg0 : g ≠ 0 := fun h0 => hP0 (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
    have hg_deg : g.natDegree ≤ P.natDegree :=
      Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left P (derivative P)) hP0
    let isGcdRoot : ℚ × ℚ → Bool := fun p => decide (g.eval (p.2 : ℝ) = 0)
    let L₁ := L.filter isGcdRoot
    let L₂ := L.filter (fun p => !isGcdRoot p)
    have hlen_sum : L₁.length + L₂.length = L.length := by
      have h := (List.length_eq_countP_add_countP isGcdRoot (l := L)).symm
      rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at h
      have hnot : (fun a => decide ¬isGcdRoot a = true) = fun p => !isGcdRoot p :=
        funext fun a => by cases isGcdRoot a <;> rfl
      rwa [hnot] at h
    have hL_snd_lt : L.Pairwise (fun p q => (p.2 : ℝ) < (q.2 : ℝ)) := by
      refine List.Pairwise.imp_of_mem ?_ hpair
      intro p q hp hq hpq
      have hq_lt : (q.1 : ℝ) < (q.2 : ℝ) := Rat.cast_lt.mpr (hmem q hq).1
      have hpq_r : (p.2 : ℝ) ≤ (q.1 : ℝ) := Rat.cast_le.mpr hpq
      linarith
    have hL1_nodup : (L₁.map (fun p : ℚ × ℚ => (p.2 : ℝ))).Nodup :=
      ((List.Pairwise.sublist List.filter_sublist hL_snd_lt).map
        (fun p : ℚ × ℚ => (p.2 : ℝ)) (fun _ _ h => h)).imp ne_of_lt
    have hL1_le : L₁.length ≤ cs.length := by
      have hsub : (L₁.map (fun p : ℚ × ℚ => (p.2 : ℝ))).toFinset ⊆ g.roots.toFinset := by
        intro r hr
        rw [List.mem_toFinset, List.mem_map] at hr
        obtain ⟨p, hp, rfl⟩ := hr
        simp only [L₁, List.mem_filter, isGcdRoot, decide_eq_true_eq] at hp
        exact Multiset.mem_toFinset.mpr ((mem_roots hg0).mpr hp.2)
      have hcard1 : L₁.length = (L₁.map (fun p : ℚ × ℚ => (p.2 : ℝ))).toFinset.card := by
        rw [List.toFinset_card_of_nodup hL1_nodup, List.length_map]
      have hcard_g : g.roots.toFinset.card ≤ cs.length :=
        (Multiset.toFinset_card_le g.roots).trans
          ((card_roots' g).trans (hg_deg.trans hP_deg_lt.le))
      exact (hcard1 ▸ Finset.card_le_card hsub).trans hcard_g
    have hL2_le : L₂.length ≤ cs.length := by
      have hL2_pair : L₂.Pairwise (fun p q => p.2 ≤ q.1) :=
        List.Pairwise.sublist (List.filter_sublist) hpair
      have hL2_card : ∀ p ∈ L₂,
          2 ≤ (P.roots.toFinset.filter (fun r => (p.1 : ℝ) < r ∧ r ≤ (p.2 : ℝ))).card := by
        intro p hp
        simp only [L₂, List.mem_filter, isGcdRoot, Bool.not_eq_true', decide_eq_false_iff_not] at hp
        obtain ⟨hpL, hgv⟩ := hp
        obtain ⟨huv, hdrop⟩ := hmem p hpL
        rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations] at hdrop
        change 2 ≤ sturmVariations P (p.1 : ℝ) - sturmVariations P (p.2 : ℝ) at hdrop
        have hgu : g.eval (p.1 : ℝ) ≠ 0 := by
          intro hgu0
          rw [sturmVariations_eq_zero_of_gcd_eval_eq_zero hgu0, Nat.zero_sub] at hdrop
          omega
        rw [sturmVariations_sub_eq_card_roots_Ioc_of_gcd_eval_ne_zero hP0
          (Rat.cast_le.mpr huv.le) hgu hgv] at hdrop
        exact hdrop
      have hge := card_rootsInIntervals_ge P L₂ hL2_card hL2_pair
      have hsub : rootsInIntervals P L₂ ⊆ P.roots.toFinset := fun r hr =>
        (mem_rootsInIntervals hr).1
      have hU_le : (rootsInIntervals P L₂).card ≤ cs.length :=
        (Finset.card_le_card hsub).trans
          ((Multiset.toFinset_card_le P.roots).trans ((card_roots' P).trans hP_deg_lt.le))
      omega
    omega

end Cslib.RealRoot
