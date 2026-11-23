/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, real polynomial roots)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ThomSign
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.NormNum

/-!
# Short derivative fingerprints for real roots

A bounded prime and one field parameter determine weights that compress the positive-order
derivative signs into an integer. The same weights distinguish every real root of a nonzero
polynomial. The fingerprint of any prescribed root can serve as a target for a root label.

Adapted from `LeanCanny.CountingHierarchy.FingerprintRootSelection` and
`LeanCanny.Algebra.FiniteFeatureSeparator` at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open scoped BigOperators

/-- Weight the signs of derivative orders one through `D` by the least residues of powers
of `t` modulo `p`. In particular, order one has weight `1 % p`. -/
@[expose] noncomputable def derivativeFingerprint (q : Polynomial ℝ) (D p t : ℕ) (x : ℝ) : ℤ :=
  ∑ i : Fin D, ((t ^ i.val % p : ℕ) : ℤ) * (q.derivativeSign x (i.val + 1) : ℤ)

/-- At a positive modulus, the target magnitude is at most the degree bound times the modulus. -/
theorem natAbs_derivativeFingerprint_le (q : Polynomial ℝ) (D p t : ℕ) (x : ℝ)
    (hp : 0 < p) : (q.derivativeFingerprint D p t x).natAbs ≤ D * p := by
  rw [derivativeFingerprint]
  apply (Int.natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin D, p := by
      apply Finset.sum_le_sum
      intro i _
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hs : (q.derivativeSign x (i.val + 1) : ℤ).natAbs ≤ 1 := by
        cases q.derivativeSign x (i.val + 1) <;> decide
      exact (Nat.mul_le_mul (Nat.mod_lt _ hp).le hs).trans_eq (Nat.mul_one _)
    _ = D * p := by simp

private theorem exists_injective_powerSum {K τ : Type*} [Field K] [Fintype K] [Fintype τ]
    {D : ℕ} (a : τ → Fin D → K) (ha : Function.Injective a)
    (hK : D * Fintype.card τ ^ 2 < Fintype.card K) :
    ∃ t : K, Function.Injective (fun x => ∑ i, a x i * t ^ i.val) := by
  classical
  let collision (q : τ × τ) : Polynomial K :=
    if q.1 = q.2 then 1 else ofFn D (a q.1 - a q.2)
  have hnonzero (q : τ × τ) : collision q ≠ 0 := by
    by_cases h : q.1 = q.2
    · simp [collision, h]
    · intro he
      dsimp only [collision] at he
      rw [ite_eq_right h, ← (ofFn D).map_zero] at he
      exact h (ha (sub_eq_zero.mp (injective_ofFn D he)))
  have hdegree (q : τ × τ) : (collision q).natDegree ≤ D := by
    by_cases h : q.1 = q.2
    · simp [collision, h]
    · dsimp only [collision]
      rw [ite_eq_right h, natDegree_le_iff_coeff_eq_zero]
      exact fun _ hk => ofFn_coeff_eq_zero_of_ge _ hk.le
  let Q := ∏ q : τ × τ, collision q
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => hnonzero q
  have hdeg : Q.natDegree ≤ D * Fintype.card τ ^ 2 := by
    apply (natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ _ : τ × τ, D := Finset.sum_le_sum fun q _ => hdegree q
      _ = _ := by simp [Fintype.card_prod, pow_two, Nat.mul_comm]
  obtain ⟨t, ht⟩ := exists_eval_ne_zero_of_natDegree_lt_card Q hQ
    (by simpa only [Cardinal.mk_fintype, Nat.cast_lt] using hdeg.trans_lt hK)
  refine ⟨t, fun x y he => ?_⟩
  by_contra hxy
  have hprod : (∏ q : τ × τ, (collision q).eval t) ≠ 0 := by
    simpa only [Q, eval_prod] using ht
  apply (Finset.prod_ne_zero_iff.mp hprod) (x, y) (Finset.mem_univ _)
  simp only [collision, hxy, ite_false, ofFn_eq_sum_monomial, eval_finsetSum, eval_monomial,
    Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, he, sub_self]

/-- A prime and a parameter with bit lengths logarithmic in `D + 2` distinguish all real
roots of a nonzero polynomial of degree at most `D`. Every prescribed real root has a
unique integer fingerprint for this choice of parameters. -/
theorem exists_derivativeFingerprint_injOn_roots (q : Polynomial ℝ) (hq : q ≠ 0) {D : ℕ}
    (hD : q.natDegree ≤ D) :
    ∃ p t : ℕ, p.Prime ∧ 2 < p ∧ p ≤ 2 * (D ^ 3 + 2) ∧ t < p ∧
      Set.InjOn (q.derivativeFingerprint D p t) {x | q.IsRoot x} := by
  classical
  obtain ⟨p, hp, hl, hu⟩ := Nat.exists_prime_lt_and_le_two_mul (D ^ 3 + 2) (by omega)
  let : Fact p.Prime := ⟨hp⟩
  let S := q.roots.toFinset
  have hroots (x : S) : q.IsRoot x := (mem_roots hq).mp (Multiset.mem_toFinset.mp x.property)
  have hcard : Fintype.card S ≤ D := by
    rw [Fintype.card_coe]
    exact (q.roots.toFinset_card_le.trans (card_roots' q)).trans hD
  let signs (x : S) (i : Fin D) : ℤ := q.derivativeSign x (i.val + 1)
  have hb (x : S) (i : Fin D) : -1 ≤ signs x i ∧ signs x i ≤ 1 := by
    dsimp only [signs]
    cases q.derivativeSign x (i.val + 1) <;> decide
  have hcast {u v : ℤ} (hu' : -1 ≤ u ∧ u ≤ 1) (hv : -1 ≤ v ∧ v ≤ 1)
      (he : (u : ZMod p) = (v : ZMod p)) : u = v := by
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub u v p).mp he
    have hs : (v - u).natAbs < (p : ℤ).natAbs := by
      rw [Int.natAbs_natCast]
      omega
    have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hs
    omega
  have hi : Function.Injective (fun x i => (signs x i : ZMod p)) := by
    intro x y he
    apply Subtype.ext
    apply q.injOn_derivativeSign_roots hq hD (hroots x) (hroots y)
    funext i
    have hs := hcast (hb x i) (hb y i) (congrFun he i)
    dsimp only [signs] at hs
    change q.derivativeSign x (i.val + 1) = q.derivativeSign y (i.val + 1)
    generalize q.derivativeSign x (i.val + 1) = s at hs ⊢
    generalize q.derivativeSign y (i.val + 1) = u at hs ⊢
    cases s <;> cases u <;> norm_num at hs <;> rfl
  have hK : D * Fintype.card S ^ 2 < Fintype.card (ZMod p) := by
    rw [ZMod.card]
    have hmul : D * Fintype.card S ^ 2 ≤ D ^ 3 :=
      (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hcard 2)).trans_eq (pow_succ' D 2).symm
    omega
  obtain ⟨t, ht⟩ := exists_injective_powerSum (fun x i => (signs x i : ZMod p)) hi hK
  have hf (x : S) : (q.derivativeFingerprint D p t.val x : ZMod p) =
      ∑ i : Fin D, (signs x i : ZMod p) * t ^ i.val := by
    simp only [derivativeFingerprint, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_mod, Nat.cast_pow, ZMod.natCast_zmod_val, signs]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  refine ⟨p, t.val, hp, by omega, hu, ZMod.val_lt t, fun x hx y hy hxy => ?_⟩
  let x' : S := ⟨x, Multiset.mem_toFinset.mpr ((mem_roots hq).mpr hx)⟩
  let y' : S := ⟨y, Multiset.mem_toFinset.mpr ((mem_roots hq).mpr hy)⟩
  exact congrArg Subtype.val (ht ((hf x').symm.trans
    ((congrArg (Int.castRingHom (ZMod p)) hxy).trans (hf y'))))

end Polynomial
