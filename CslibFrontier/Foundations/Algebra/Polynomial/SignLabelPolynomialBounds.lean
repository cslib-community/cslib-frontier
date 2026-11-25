/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial approximation)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.SignLabelPolynomial
public import CslibFrontier.Foundations.Data.Polynomial.CoeffNorm1
public import Mathlib.Data.Nat.Size
import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignProductBounds

/-!
# Uniform size bounds for integer sign labels

The degree and coefficient norm of the label depend only on the width and
the degree and coefficient norm budgets of the individual tests. Each
denominator and each cleared error term inherits the bounds on the two
compositions of the sign product.

Adapted from `ClearedSignTestBounds`, `RootLabelPolynomialBounds`, and
`FingerprintLabelBounds` in lean-canny at commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Finset

private theorem dyadicSignProduct_sum_sub_comp_bounds (B s : ℕ) (g : ℤ[X]) {D b : ℕ}
    (hD : g.natDegree ≤ D) (hb : g.coeffNorm1 ≤ 2 ^ b) :
    let p := dyadicSignProduct B s
    let a := p.comp g
    let a' := p.comp (-g)
    let n := 2 * s * (2 * B + 1)
    let K := n * D
    let H := n * (2 * B + 1 + b)
    ((a + a').natDegree ≤ K ∧ (a + a').coeffNorm1 ≤ 2 ^ (H + 1)) ∧
      ((a - a').natDegree ≤ K ∧ (a - a').coeffNorm1 ≤ 2 ^ (H + 1)) := by
  intro p a a' n K H
  have hp : a.natDegree ≤ K ∧ a.coeffNorm1 ≤ 2 ^ H :=
    dyadicSignProduct_comp_bounds B s g hD hb
  have hn : a'.natDegree ≤ K ∧ a'.coeffNorm1 ≤ 2 ^ H :=
    dyadicSignProduct_comp_bounds B s (-g)
      (by simpa only [natDegree_neg] using hD) (by simpa only [coeffNorm1_neg] using hb)
  have hsum := (Nat.add_le_add hp.2 hn.2).trans_eq
    (show 2 ^ H + 2 ^ H = 2 ^ (H + 1) by rw [pow_succ, Nat.mul_two])
  exact ⟨⟨(natDegree_add_le _ _).trans (max_le hp.1 hn.1),
      (coeffNorm1_add_le _ _).trans hsum⟩,
    ⟨(natDegree_sub_le _ _).trans (max_le hp.1 hn.1), (coeffNorm1_sub_le _ _).trans hsum⟩⟩

/-- A degree bound for the integer label of `m` tests of degree at most `D`. -/
@[expose] def signLabelDegreeBound (m B D : ℕ) : ℕ :=
  2 * ((m + 1) * ((2 * (m + 1) * (2 * B + 1)) * D))

/-- A base-two coefficient norm exponent for the integer label of `m` tests
whose individual norms are at most `2 ^ b`. -/
@[expose] def signLabelNormExponent (m B b : ℕ) : ℕ :=
  m.size + 2 * ((m + 1) * ((2 * (m + 1) * (2 * B + 1)) * (2 * B + 1 + b) + 2)) + 3

/-- The degree and coefficient budgets hold uniformly for every target sign assignment. -/
theorem signLabelPolynomial_bounds {m : ℕ} (B : ℕ) (g : Fin m → ℤ[X])
    (target : Fin m → SignType) {D b : ℕ}
    (hD : ∀ i, (g i).natDegree ≤ D) (hb : ∀ i, (g i).coeffNorm1 ≤ 2 ^ b) :
    (signLabelPolynomial B g target).natDegree ≤ signLabelDegreeBound m B D ∧
      (signLabelPolynomial B g target).coeffNorm1 ≤ 2 ^ signLabelNormExponent m B b := by
  let n := 2 * (m + 1) * (2 * B + 1)
  let K := n * D
  let H := n * (2 * B + 1 + b)
  let L := (m + 1) * (H + 2)
  let p := dyadicSignProduct B (m + 1)
  let a (i : Fin m) := p.comp (g i)
  let a' (i : Fin m) := p.comp (-g i)
  let d (i : Fin m) := a i + a' i
  let dev (i : Fin m) := a i - a' i - C (target i : ℤ) * d i
  let e (i : Fin m) := dev i * ∏ j ∈ univ.erase i, d j
  let P := ∏ i, d i
  let S := ∑ i, (e i) ^ 2
  have hFactors (i : Fin m) :
      ((d i).natDegree ≤ K ∧ (d i).coeffNorm1 ≤ 2 ^ (H + 1)) ∧
      ((a i - a' i).natDegree ≤ K ∧ (a i - a' i).coeffNorm1 ≤ 2 ^ (H + 1)) :=
    dyadicSignProduct_sum_sub_comp_bounds B (m + 1) (g i) (hD i) (hb i)
  have hdouble (k : ℕ) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_two]
  have hDen (i : Fin m) : (d i).natDegree ≤ K ∧ (d i).coeffNorm1 ≤ 2 ^ (H + 1) :=
    (hFactors i).1
  have hDev (i : Fin m) : (dev i).natDegree ≤ K ∧ (dev i).coeffNorm1 ≤ 2 ^ (H + 2) := by
    obtain ⟨hsubDegree, hsubNorm⟩ := (hFactors i).2
    have ht : (target i : ℤ).natAbs ≤ 1 := by cases target i <;> decide
    refine ⟨(natDegree_sub_le _ _).trans (max_le hsubDegree
      ((natDegree_C_mul_le _ _).trans (hDen i).1)), ?_⟩
    have hct := (coeffNorm1_C_mul_le (target i : ℤ) (d i)).trans
      ((Nat.mul_le_mul ht (hDen i).2).trans_eq (Nat.one_mul _))
    exact (coeffNorm1_sub_le _ _).trans
      ((Nat.add_le_add hsubNorm hct).trans_eq (hdouble (H + 1)))
  have hProd (I : Finset (Fin m)) :
      (∏ i ∈ I, d i).natDegree ≤ m * K ∧ (∏ i ∈ I, d i).coeffNorm1 ≤ 2 ^ (m * (H + 1)) := by
    have hI : I.card ≤ m := by simpa only [Fintype.card_fin] using I.card_le_univ
    constructor
    · refine (natDegree_prod_le _ _).trans (le_trans ?_ (Nat.mul_le_mul_right K hI))
      simpa only [sum_const, nsmul_eq_mul, Nat.cast_id] using
        sum_le_sum (fun i (_ : i ∈ I) => (hDen i).1)
    · refine (coeffNorm1_prod_le _ _).trans ((prod_le_prod fun i _ => (hDen i).2).trans ?_)
      rw [prod_const, ← pow_mul, Nat.mul_comm (H + 1) I.card]
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hI)
  have hE (i : Fin m) : (e i).natDegree ≤ (m + 1) * K ∧ (e i).coeffNorm1 ≤ 2 ^ L := by
    have hp := hProd (univ.erase i)
    refine ⟨natDegree_mul_le.trans ((Nat.add_le_add (hDev i).1 hp.1).trans_eq (by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm])), ?_⟩
    refine (coeffNorm1_mul_le _ _).trans ((Nat.mul_le_mul (hDev i).2 hp.2).trans ?_)
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by
      calc
        H + 2 + m * (H + 1) ≤ H + 2 + m * (H + 2) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left m (by omega)) _
        _ = L := by
          dsimp only [L]
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm])
  have hPdeg : P.natDegree ≤ (m + 1) * K :=
    (hProd univ).1.trans (Nat.mul_le_mul_right K (Nat.le_succ m))
  have hPnorm : P.coeffNorm1 ≤ 2 ^ L :=
    (hProd univ).2.trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul (Nat.le_succ m) (by omega)))
  have hSq (q : ℤ[X]) (hq : q.coeffNorm1 ≤ 2 ^ L) :
      (q ^ 2).coeffNorm1 ≤ 2 ^ (2 * L) :=
    (coeffNorm1_pow_le _ _).trans ((Nat.pow_le_pow_left hq 2).trans_eq (by
      rw [← pow_mul, Nat.mul_comm L 2]))
  have hSdeg : S.natDegree ≤ 2 * ((m + 1) * K) :=
    natDegree_sum_le_of_forall_le _ _ fun i _ =>
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hE i).1)
  have hSnorm : S.coeffNorm1 ≤ 2 ^ (m.size + 2 * L) := by
    refine (coeffNorm1_sum_le _ _).trans ((sum_le_sum fun i _ => hSq (e i) (hE i).2).trans ?_)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact (Nat.mul_le_mul_right _ m.lt_size_self.le).trans_eq (pow_add _ _ _).symm
  change (P ^ 2 - C 4 * S).natDegree ≤ 2 * ((m + 1) * K) ∧
    (P ^ 2 - C 4 * S).coeffNorm1 ≤ 2 ^ (m.size + 2 * L + 3)
  refine ⟨(natDegree_sub_le _ _).trans (max_le
    (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hPdeg))
    ((natDegree_C_mul_le _ _).trans hSdeg)), ?_⟩
  have hscaled : (C 4 * S).coeffNorm1 ≤ 2 ^ (m.size + 2 * L + 2) := by
    refine (coeffNorm1_C_mul_le _ _).trans ((Nat.mul_le_mul_left 4 hSnorm).trans_eq ?_)
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add, Nat.add_comm 2]
  have hfirst := (hSq P hPnorm).trans
    (show 2 ^ (2 * L) ≤ 2 ^ (m.size + 2 * L + 2) from Nat.pow_le_pow_right (by decide) (by omega))
  exact (coeffNorm1_sub_le _ _).trans ((Nat.add_le_add hfirst hscaled).trans_eq
    (by simpa only [Nat.add_assoc] using hdouble (m.size + 2 * L + 2)))

/-- A degree bound for a weighted fingerprint label with `m` weighted tests and one
qualifying test of degree at most `D`, using a total weight budget `M`. -/
@[expose] def fingerprintLabelDegreeBound (m B M D : ℕ) : ℕ :=
  2 * ((m + 1) * ((2 * (M + 1) * (2 * B + 1)) * D))

/-- A base-two coefficient norm exponent for a weighted fingerprint label with
`m` weighted tests and one qualifying test of norm at most `2 ^ b`, when the
total weight and the absolute value of the target are at most `M`. -/
@[expose] def fingerprintLabelNormExponent (m B M b : ℕ) : ℕ :=
  2 * (M.size + (m + 1) * ((2 * (M + 1) * (2 * B + 1)) * (2 * B + 1 + b) + 1) + 1) + 4

/-- Uniform degree and coefficient-norm bounds for the denominator-cleared fingerprint label. -/
theorem fingerprintLabelPolynomial_bounds {m : ℕ} (B M : ℕ) (g : Fin (m + 1) → ℤ[X])
    (w : Fin m → ℕ) (target : ℤ) {D b : ℕ}
    (hD : ∀ i, (g i).natDegree ≤ D) (hb : ∀ i, (g i).coeffNorm1 ≤ 2 ^ b)
    (hw : ∑ i, w i ≤ M) (ht : target.natAbs ≤ M) :
    (fingerprintLabelPolynomial B M g w target).natDegree ≤ fingerprintLabelDegreeBound m B M D ∧
      (fingerprintLabelPolynomial B M g w target).coeffNorm1 ≤
        2 ^ fingerprintLabelNormExponent m B M b := by
  let n := 2 * (M + 1) * (2 * B + 1)
  let K := n * D
  let H := n * (2 * B + 1 + b)
  let L := (m + 1) * (H + 1)
  let U := M.size + L + 1
  let p := dyadicSignProduct B (M + 1)
  let a (i : Fin (m + 1)) := p.comp (g i)
  let a' (i : Fin (m + 1)) := p.comp (-g i)
  let d (i : Fin (m + 1)) := a i + a' i
  let P := ∏ i, d i
  let T (i : Fin (m + 1)) := (a i - a' i) * ∏ j ∈ univ.erase i, d j
  let S := ∑ i, C (w i : ℤ) * T i.succ
  have hdouble (k : ℕ) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_two]
  have hFactors (i : Fin (m + 1)) :
      ((d i).natDegree ≤ K ∧ (d i).coeffNorm1 ≤ 2 ^ (H + 1)) ∧
      ((a i - a' i).natDegree ≤ K ∧ (a i - a' i).coeffNorm1 ≤ 2 ^ (H + 1)) :=
    dyadicSignProduct_sum_sub_comp_bounds B (M + 1) (g i) (hD i) (hb i)
  have hprod (f : Fin (m + 1) → ℤ[X])
      (hf : ∀ i, (f i).natDegree ≤ K ∧ (f i).coeffNorm1 ≤ 2 ^ (H + 1)) :
      (∏ i, f i).natDegree ≤ (m + 1) * K ∧ (∏ i, f i).coeffNorm1 ≤ 2 ^ L := by
    constructor
    · apply (natDegree_prod_le _ _).trans
      simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
        sum_le_sum (fun i (_ : i ∈ univ) => (hf i).1)
    · refine (coeffNorm1_prod_le _ _).trans ((prod_le_prod fun i _ => (hf i).2).trans_eq ?_)
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm (H + 1)]
  have hP := hprod d fun i => (hFactors i).1
  have hT (i : Fin (m + 1)) : (T i).natDegree ≤ (m + 1) * K ∧ (T i).coeffNorm1 ≤ 2 ^ L := by
    let f (j : Fin (m + 1)) := if j = i then a j - a' j else d j
    have hTf : T i = ∏ j, f j := by
      rw [← univ.mul_prod_erase f (mem_univ i)]
      unfold T
      rw [show f i = a i - a' i by simp only [f, ite_eq_left rfl]]
      congr 1
      exact prod_congr rfl fun j hj => by simp only [f, ite_eq_right (mem_erase.mp hj).1]
    rw [hTf]
    exact hprod f fun j => by
      by_cases h : j = i
      · simpa only [f, ite_eq_left h] using (hFactors j).2
      · simpa only [f, ite_eq_right h] using (hFactors j).1
  have hSdeg : S.natDegree ≤ (m + 1) * K :=
    natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_C_mul_le _ _).trans (hT i.succ).1
  have hS : S.coeffNorm1 ≤ 2 ^ (M.size + L) := by
    apply (coeffNorm1_sum_le _ _).trans
    calc
      _ ≤ ∑ i : Fin m, w i * 2 ^ L := by
        refine sum_le_sum fun i _ => (coeffNorm1_C_mul_le _ _).trans ?_
        simpa only [Int.natAbs_natCast] using Nat.mul_le_mul_left (w i) (hT i.succ).2
      _ = (∑ i, w i) * 2 ^ L := (sum_mul _ _ _).symm
      _ ≤ 2 ^ M.size * 2 ^ L := Nat.mul_le_mul_right _ (hw.trans M.lt_size_self.le)
      _ = _ := (pow_add 2 _ _).symm
  have htarget : (C target * P).coeffNorm1 ≤ 2 ^ (M.size + L) :=
    (coeffNorm1_C_mul_le _ _).trans
      ((Nat.mul_le_mul (ht.trans M.lt_size_self.le) hP.2).trans_eq (pow_add 2 _ _).symm)
  have hpad : 2 ^ L ≤ 2 ^ (M.size + L) := Nat.pow_le_pow_right (by decide) (by omega)
  have hweighted : (S - C target * P).coeffNorm1 ≤ 2 ^ U :=
    (coeffNorm1_sub_le _ _).trans ((Nat.add_le_add hS htarget).trans_eq (hdouble _))
  have hqualifier : (T 0 - P).coeffNorm1 ≤ 2 ^ U :=
    (coeffNorm1_sub_le _ _).trans
      ((Nat.add_le_add ((hT 0).2.trans hpad) (hP.2.trans hpad)).trans_eq (hdouble _))
  have hsquare (q : ℤ[X]) (hq : q.coeffNorm1 ≤ 2 ^ U) : (q ^ 2).coeffNorm1 ≤ 2 ^ (2 * U) :=
    (coeffNorm1_pow_le _ _).trans ((Nat.pow_le_pow_left hq 2).trans_eq (by
      rw [← pow_mul, Nat.mul_comm U 2]))
  let Q := (S - C target * P) ^ 2 + (T 0 - P) ^ 2
  have hweightedDegree : (S - C target * P).natDegree ≤ (m + 1) * K :=
    (natDegree_sub_le _ _).trans (max_le hSdeg ((natDegree_C_mul_le _ _).trans hP.1))
  have hqualifierDegree : (T 0 - P).natDegree ≤ (m + 1) * K :=
    (natDegree_sub_le _ _).trans (max_le (hT 0).1 hP.1)
  have hQDegree : Q.natDegree ≤ 2 * ((m + 1) * K) :=
    (natDegree_add_le _ _).trans (max_le
      (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hweightedDegree))
      (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hqualifierDegree)))
  change (P ^ 2 - C 4 * Q).natDegree ≤ 2 * ((m + 1) * K) ∧
    (P ^ 2 - C 4 * Q).coeffNorm1 ≤ 2 ^ (2 * U + 4)
  refine ⟨(natDegree_sub_le _ _).trans (max_le
    (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hP.1))
    ((natDegree_C_mul_le _ _).trans hQDegree)), ?_⟩
  have hQ : Q.coeffNorm1 ≤ 2 ^ (2 * U + 1) :=
    (coeffNorm1_add_le _ _).trans
      ((Nat.add_le_add (hsquare _ hweighted) (hsquare _ hqualifier)).trans_eq (hdouble _))
  have hscaled : (C 4 * Q).coeffNorm1 ≤ 2 ^ (2 * U + 3) := by
    refine (coeffNorm1_C_mul_le _ _).trans ((Nat.mul_le_mul_left 4 hQ).trans_eq ?_)
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    omega
  have hPnorm : P.coeffNorm1 ≤ 2 ^ U :=
    (hP.2.trans hpad).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  have hfirst : (P ^ 2).coeffNorm1 ≤ 2 ^ (2 * U + 3) :=
    (hsquare P hPnorm).trans (Nat.pow_le_pow_right (by decide) (by omega))
  exact (coeffNorm1_sub_le _ _).trans ((Nat.add_le_add hfirst hscaled).trans_eq (hdouble _))

end Polynomial
