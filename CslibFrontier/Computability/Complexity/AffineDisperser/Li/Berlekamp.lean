/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryPolynomial
public import CslibFrontier.Foundations.Data.BitString.List.Dot
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import CslibFrontier.Foundations.LinearAlgebra.KernelVector
import CslibFrontier.Foundations.Data.BitString.ZModTwo
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.AdjoinRoot

/-!
# Deterministic Berlekamp polynomial factoring over `𝔽₂`

This module implements explicit coefficient-list arithmetic over `𝔽₂[X]`, Boolean Gaussian
elimination (`kernelVecBits`), and deterministic Berlekamp factorization
(`berlekampIrreducibleFactor`) matching the specifications of `Cslib.polyOfBits`
and `Cslib.LinearAlgebra.kernelVec`.

## Main definitions

* `Cslib.AffineDisperser.Li.polyTrim`, `polyAdd`, `polyMul`, `polyDivMod`, `polyGcd`,
  `polyComposePow`: explicit bit-list operations for `𝔽₂[X]`.
* `Cslib.AffineDisperser.Li.kernelStepBits`, `kernelBasisBits`, `kernelVecBits`:
  explicit `𝔽₂` Gaussian elimination returning a canonical nonzero kernel vector when one exists.
* `Cslib.AffineDisperser.Li.berlekampMatrix`, `berlekampStep`, `berlekampIrreducibleFactor`:
  deterministic Berlekamp factoring algorithm over `𝔽₂`.

## Main results

* `Cslib.AffineDisperser.Li.polyOfBits_polyAdd`, `polyOfBits_polyMul`,
  `polyOfBits_polyDivMod_spec`, `polyOfBits_polyGcd_dvd_left`,
  `polyOfBits_polyGcd_dvd_right`, `dvd_polyOfBits_polyGcd`, `polyOfBits_polyComposePow`:
  correctness of bit-list polynomial arithmetic.
* `Cslib.AffineDisperser.Li.bitsToZModVec_kernelVecBits_eq`,
  `Cslib.AffineDisperser.Li.mulVec_kernelVecBits`,
  `Cslib.AffineDisperser.Li.kernelVecBits_any_of_exists`: equivalence between `kernelVecBits` and
  `Cslib.LinearAlgebra.kernelVec`.
* `Cslib.AffineDisperser.Li.polyOfBits_berlekampIrreducibleFactor_dvd` and
  `Cslib.AffineDisperser.Li.irreducible_polyOfBits_berlekampIrreducibleFactor`: for every
  squarefree binary polynomial `g` of positive degree, `berlekampIrreducibleFactor g` produces an
  irreducible factor dividing `g`.

## References

* [E. R. Berlekamp, *Factoring Polynomials Over Finite Fields*, Bell System Tech. J. 46 (1967)]
* [V. Shoup, *New algorithms for finding irreducible polynomials over finite fields*][Shoup1990]
-/

public section

namespace Cslib.AffineDisperser.Li

open Cslib.BitString Cslib.LinearAlgebra Matrix Polynomial
open scoped Matrix

/-! ### Helper identities -/

private theorem coeff_comp_X_pow (P : (ZMod 2)[X]) {q : ℕ} (hq : 0 < q) (k : ℕ) :
    (P.comp (X ^ q)).coeff k = if q ∣ k then P.coeff (k / q) else 0 := by
  induction P using Polynomial.induction_on' with
  | add P₁ P₂ ih1 ih2 =>
    rw [add_comp, coeff_add, coeff_add, ih1, ih2]
    split_ifs <;> simp
  | monomial n a =>
    rw [monomial_comp, coeff_C_mul, ← pow_mul, coeff_X_pow, coeff_monomial]
    by_cases hdiv : q ∣ k
    · obtain ⟨m, rfl⟩ := hdiv
      rw [ite_eq_left (dvd_mul_right q m), Nat.mul_div_right m hq]
      by_cases hnm : n = m <;> simp [hnm, hq.ne', eq_comm]
    · have hne : q * n ≠ k := fun heq => hdiv ⟨n, heq.symm⟩
      simp [hdiv, hne.symm]

/-! ### Coefficient extraction and trimmed polynomial lists -/

/-- The `i`-th coefficient of `polyOfBits l` is `l.getD i false`. -/
theorem coeff_polyOfBits (l : List Bool) (i : ℕ) :
    (polyOfBits l).coeff i = bitEquiv.symm (l.getD i false) := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rw [polyOfBits_cons, coeff_add, coeff_C]
    cases i with
    | zero => simp
    | succ k => simp [coeff_X_mul, ih k]

/-- Strip trailing `false` entries from a bit-coefficient list. -/
@[expose] def polyTrim (p : List Bool) : List Bool :=
  p.foldr (fun b acc => if b || !acc.isEmpty then b :: acc else []) []

private theorem polyTrim_nil : polyTrim [] = [] := rfl

private theorem polyTrim_cons (b : Bool) (p : List Bool) :
    polyTrim (b :: p) = if b || !(polyTrim p).isEmpty then b :: polyTrim p else [] := rfl

/-- Trimming preserves a list ending in `true`. -/
theorem polyTrim_append_true (l : List Bool) : polyTrim (l ++ [true]) = l ++ [true] := by
  induction l with
  | nil => simp [polyTrim]
  | cons b l ih =>
    rw [List.cons_append, polyTrim_cons, ih]
    have hne : (l ++ [true]).isEmpty = false := by simp
    simp [hne]

/-- Every trimmed coefficient list is either empty or ends in `true`. -/
theorem polyTrim_eq_nil_or_append_true (p : List Bool) :
    polyTrim p = [] ∨ ∃ l, polyTrim p = l ++ [true] := by
  induction p with
  | nil => exact Or.inl rfl
  | cons b p ih =>
    rw [polyTrim_cons]
    rcases ih with h | ⟨l, h⟩
    · rw [h]
      cases b
      · exact Or.inl rfl
      · exact Or.inr ⟨[], rfl⟩
    · rw [h]
      have hne : (l ++ [true]).isEmpty = false := by simp
      simp only [hne, Bool.not_false, Bool.or_true, ↓reduceIte]
      exact Or.inr ⟨b :: l, rfl⟩

/-- `polyTrim` is idempotent. -/
@[simp]
theorem polyTrim_polyTrim (p : List Bool) : polyTrim (polyTrim p) = polyTrim p := by
  rcases polyTrim_eq_nil_or_append_true p with h | ⟨l, h⟩
  · rw [h]; rfl
  · rw [h, polyTrim_append_true]

/-- Trimming never increases list length. -/
theorem length_polyTrim_le (p : List Bool) : (polyTrim p).length ≤ p.length := by
  induction p with
  | nil => simp [polyTrim_nil]
  | cons b p ih =>
    rw [polyTrim_cons]
    split_ifs <;> first | (simp; omega) | simp

/-- Trimming preserves polynomial semantics. -/
@[simp]
theorem polyOfBits_polyTrim (p : List Bool) : polyOfBits (polyTrim p) = polyOfBits p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    rw [polyTrim_cons]
    split_ifs with h
    · rw [polyOfBits_cons, polyOfBits_cons, ih]
    · have hb : b = false := by cases b <;> simp_all
      have hempty : (polyTrim p).isEmpty = true := by
        cases hne : (polyTrim p).isEmpty <;> simp_all
      have hnil : polyTrim p = [] := List.isEmpty_iff.mp hempty
      rw [hnil, polyOfBits_nil] at ih
      rw [polyOfBits_nil, polyOfBits_cons, hb, ← ih]
      simp

/-- `polyTrim p = []` if and only if `polyOfBits p = 0`. -/
@[simp]
theorem polyTrim_eq_nil_iff (p : List Bool) : polyTrim p = [] ↔ polyOfBits p = 0 := by
  constructor
  · intro h
    rw [← polyOfBits_polyTrim, h, polyOfBits_nil]
  · intro h
    rcases polyTrim_eq_nil_or_append_true p with hnil | ⟨l, hl⟩
    · exact hnil
    · have h0 : polyOfBits (l ++ [true]) = 0 := by rw [← hl, polyOfBits_polyTrim, h]
      exact absurd h0 (polyOfBits_ne_zero_of_mem (by simp))

/-- A nonempty trimmed list has degree `p.length - 1`. -/
theorem natDegree_polyOfBits_of_polyTrim {p : List Bool} (hp : polyTrim p = p) (hne : p ≠ []) :
    (polyOfBits p).natDegree = p.length - 1 := by
  rcases polyTrim_eq_nil_or_append_true p with hnil | ⟨l, hl⟩
  · rw [hp] at hnil
    exact absurd hnil hne
  · rw [hp] at hl
    rw [hl, natDegree_polyOfBits_append_true]
    simp

/-- `polyOfBits p ≠ 0` if and only if `polyTrim p ≠ []`. -/
theorem polyOfBits_ne_zero_iff_polyTrim {p : List Bool} : polyOfBits p ≠ 0 ↔ polyTrim p ≠ [] :=
  not_congr (polyTrim_eq_nil_iff p).symm

/-- Vanishing coefficients above `n` bound `(polyTrim p).length ≤ n`. -/
theorem length_polyTrim_le_of_coeff_zero {p : List Bool} {n : ℕ}
    (h : ∀ k ≥ n, (polyOfBits p).coeff k = 0) : (polyTrim p).length ≤ n := by
  rcases polyTrim_eq_nil_or_append_true p with hnil | ⟨l, hl⟩
  · simp [hnil]
  · have hne : polyOfBits (polyTrim p) ≠ 0 := by
      rw [hl]
      exact polyOfBits_ne_zero_of_mem (by simp)
    have hdeg : (polyOfBits (polyTrim p)).natDegree = l.length := by
      rw [hl, natDegree_polyOfBits_append_true]
    by_contra hlt
    push Not at hlt
    have hl_ge : n ≤ l.length := by
      rw [hl, List.length_append, List.length_singleton] at hlt
      omega
    have hzero := h l.length hl_ge
    rw [← polyOfBits_polyTrim, ← hdeg] at hzero
    exact absurd (leadingCoeff_eq_zero.mp hzero) hne

/-! ### Polynomial addition, multiplication, division, GCD, and `X^q`-composition -/

/-- Addition of binary polynomials over `𝔽₂`, returning a trimmed coefficient list. -/
@[expose] def polyAdd (p q : List Bool) : List Bool :=
  polyTrim ((List.range (max p.length q.length)).map fun i =>
    xor (p.getD i false) (q.getD i false))

/-- `polyAdd p q` is always trimmed. -/
@[simp]
theorem polyTrim_polyAdd (p q : List Bool) : polyTrim (polyAdd p q) = polyAdd p q :=
  polyTrim_polyTrim _

/-- Length bound on `polyAdd p q`. -/
theorem length_polyAdd_le (p q : List Bool) : (polyAdd p q).length ≤ max p.length q.length :=
  (length_polyTrim_le _).trans (by simp)

/-- `polyAdd` computes addition in `𝔽₂[X]`. -/
@[simp]
theorem polyOfBits_polyAdd (p q : List Bool) :
    polyOfBits (polyAdd p q) = polyOfBits p + polyOfBits q := by
  rw [polyAdd, polyOfBits_polyTrim]
  ext i
  rw [coeff_polyOfBits, coeff_add, coeff_polyOfBits, coeff_polyOfBits]
  by_cases hi : i < max p.length q.length
  · rw [List.getD_map_range _ false hi, ← Bool.add_eq_xor, map_add]
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default p _ (by omega),
      List.getD_eq_default q _ (by omega)]
    simp

/-- Multiplication of binary polynomials over `𝔽₂`, returning a trimmed coefficient list. -/
@[expose] def polyMul (p q : List Bool) : List Bool :=
  if p.isEmpty || q.isEmpty then []
  else
    polyTrim ((List.range (p.length + q.length)).map fun k =>
      (List.range (k + 1)).foldl
        (fun acc i => xor acc (p.getD i false && q.getD (k - i) false)) false)

/-- `polyMul p q` is always trimmed. -/
@[simp]
theorem polyTrim_polyMul (p q : List Bool) : polyTrim (polyMul p q) = polyMul p q := by
  unfold polyMul
  split_ifs
  · rfl
  · exact polyTrim_polyTrim _

/-- `polyMul` computes multiplication in `𝔽₂[X]`. -/
@[simp]
theorem polyOfBits_polyMul (p q : List Bool) :
    polyOfBits (polyMul p q) = polyOfBits p * polyOfBits q := by
  unfold polyMul
  split_ifs with h
  · simp only [Bool.or_eq_true, List.isEmpty_iff] at h
    rcases h with rfl | rfl <;> simp
  · rw [polyOfBits_polyTrim]
    ext k
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      (polyOfBits p).coeff i * (polyOfBits q).coeff j)]
    simp_rw [coeff_polyOfBits]
    by_cases hk : k < p.length + q.length
    · rw [List.getD_map_range _ false hk, ← List.foldl_map (g := xor)
          (f := fun i => p.getD i false && q.getD (k - i) false),
        bitEquiv_symm_foldl_xor, List.map_map, Function.comp_def, List.sum_map_range_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Bool.mul_eq_and, map_mul]
    · rw [List.getD_eq_default _ _ (by simp; omega), bitEquiv_symm_false]
      symm
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      by_cases hip : i < p.length
      · rw [List.getD_eq_default q _ (by omega), bitEquiv_symm_false, mul_zero]
      · rw [List.getD_eq_default p _ (by omega), bitEquiv_symm_false, zero_mul]

private theorem polyOfBits_replicate_false_append (k : ℕ) (p : List Bool) :
    polyOfBits (List.replicate k false ++ p) = X ^ k * polyOfBits p := by
  rw [polyOfBits_append, polyOfBits_replicate_false, List.length_replicate, zero_add]

/-- One step of binary polynomial long division modulo `b`. -/
@[expose] def polyDivModStep (b : List Bool) (st : List Bool × List Bool) :
    List Bool × List Bool :=
  let r := polyTrim st.2
  if r.length < b.length || b.isEmpty then (polyTrim st.1, r)
  else
    let d := r.length - b.length
    (polyAdd st.1 (List.replicate d false ++ [true]), polyAdd r (List.replicate d false ++ b))

/-- Euclidean division `(quotient, remainder)` of `a` by `b` in `𝔽₂[X]`. -/
@[expose] def polyDivMod (a b : List Bool) : List Bool × List Bool :=
  let bt := polyTrim b
  (polyDivModStep bt)^[a.length] ([], polyTrim a)

/-- Remainder of `a` modulo `b` in `𝔽₂[X]`, as a trimmed list. -/
@[expose] def polyMod (a b : List Bool) : List Bool :=
  (polyDivMod a b).2

/-- Quotient of `a` divided by `b` in `𝔽₂[X]`, as a trimmed list. -/
@[expose] def polyQuot (a b : List Bool) : List Bool :=
  (polyDivMod a b).1

private theorem polyDivModStep_spec {a b : List Bool} (hb_trim : polyTrim b = b)
    (st : List Bool × List Bool)
    (hinv : polyOfBits st.1 * polyOfBits b + polyOfBits st.2 = polyOfBits a)
    (hr_trim : polyTrim st.2 = st.2) :
    let st' := polyDivModStep b st
    polyOfBits st'.1 * polyOfBits b + polyOfBits st'.2 = polyOfBits a ∧
      polyTrim st'.1 = st'.1 ∧
      polyTrim st'.2 = st'.2 ∧
      (st.2.length < b.length ∨ b = [] → st'.2 = st.2) ∧
      (b.length ≤ st.2.length → b ≠ [] → st'.2.length < st.2.length) := by
  dsimp only [polyDivModStep]
  rw [hr_trim]
  split_ifs with h
  · refine ⟨by simpa only [polyOfBits_polyTrim] using hinv, polyTrim_polyTrim _, hr_trim,
      fun _ => rfl, ?_⟩
    intro hle hbne
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
    rcases h with hlt | rfl
    · omega
    · exact absurd rfl hbne
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at h
    rcases h with ⟨hle, hbne_empty⟩
    have hbne : b ≠ [] := by simpa using hbne_empty
    set d := st.2.length - b.length
    have heq_alg :
        polyOfBits (polyAdd st.1 (List.replicate d false ++ [true])) * polyOfBits b +
          polyOfBits (polyAdd st.2 (List.replicate d false ++ b)) = polyOfBits a := by
      have h1 : polyOfBits [true] = 1 := by simp
      rw [polyOfBits_polyAdd, polyOfBits_polyAdd, polyOfBits_replicate_false_append,
        polyOfBits_replicate_false_append, h1, mul_one, add_mul, add_add_add_comm,
        CharTwo.add_self_eq_zero, add_zero, hinv]
    refine ⟨heq_alg, polyTrim_polyAdd _ _, polyTrim_polyAdd _ _,
      fun hstop => hstop.elim (fun hlt => by omega) (fun hnil => absurd hnil hbne), fun _ _ => ?_⟩
    have hb_pos : 0 < b.length := List.length_pos_of_ne_nil hbne
    have hr_ne : st.2 ≠ [] := fun hnil => by simp only [hnil, List.length_nil] at hle; omega
    have hr_pos : 0 < st.2.length := List.length_pos_of_ne_nil hr_ne
    have hne_b : polyOfBits b ≠ 0 :=
      polyOfBits_ne_zero_iff_polyTrim.mpr (by rw [hb_trim]; exact hbne)
    have hne_r : polyOfBits st.2 ≠ 0 :=
      polyOfBits_ne_zero_iff_polyTrim.mpr (by rw [hr_trim]; exact hr_ne)
    have htop_r : (polyOfBits st.2).coeff (st.2.length - 1) = 1 := by
      rw [← natDegree_polyOfBits_of_polyTrim hr_trim hr_ne]
      exact monic_of_ne_zero hne_r
    have htop_b : (X ^ d * polyOfBits b).coeff (st.2.length - 1) = 1 := by
      rw [show st.2.length - 1 = d + (b.length - 1) by omega, coeff_X_pow_mul',
        ite_eq_left (Nat.le_add_right d _), Nat.add_sub_cancel_left,
        ← natDegree_polyOfBits_of_polyTrim hb_trim hbne]
      exact monic_of_ne_zero hne_b
    have hle_lt : ∀ k ≥ st.2.length - 1,
        (polyOfBits (polyAdd st.2 (List.replicate d false ++ b))).coeff k = 0 := by
      intro k hk
      rw [polyOfBits_polyAdd, polyOfBits_replicate_false_append, coeff_add]
      rcases eq_or_lt_of_le hk with rfl | hgt
      · rw [htop_r, htop_b]
        exact CharTwo.add_self_eq_zero 1
      · have hk_r : (polyOfBits st.2).coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt
            (by rw [natDegree_polyOfBits_of_polyTrim hr_trim hr_ne]; exact hgt)
        have hk_b : (X ^ d * polyOfBits b).coeff k = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          have hdeg_le := natDegree_mul_le (p := X ^ d) (q := polyOfBits b)
          rw [natDegree_X_pow, natDegree_polyOfBits_of_polyTrim hb_trim hbne] at hdeg_le
          omega
        rw [hk_r, hk_b, add_zero]
    have hlen_le := length_polyTrim_le_of_coeff_zero hle_lt
    rw [polyTrim_polyAdd] at hlen_le
    exact Nat.lt_of_le_of_lt hlen_le (Nat.sub_lt hr_pos Nat.one_pos)

/-- Length and trimming invariants along iterations of `polyDivModStep`. -/
theorem polyDivMod_iterate_bounds (a b : List Bool) (k : ℕ) :
    let st := (polyDivModStep b)^[k] ([], polyTrim a)
    st.1.length ≤ a.length ∧ st.2.length ≤ a.length ∧ polyTrim st.2 = st.2 := by
  induction k with
  | zero =>
    simp [length_polyTrim_le, polyTrim_polyTrim]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2, htrim⟩ := ih
    dsimp only [polyDivModStep]
    rw [htrim]
    split_ifs with h
    · exact ⟨(length_polyTrim_le _).trans h1, h2, htrim⟩
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at h
      rcases h with ⟨hle, hbne_empty⟩
      have hbne : b ≠ [] := by simpa using hbne_empty
      have hb_pos : 0 < b.length := List.length_pos_of_ne_nil hbne
      have hlen1 : (List.replicate (((polyDivModStep b)^[k] ([], polyTrim a)).2.length - b.length)
          false ++ [true]).length ≤ a.length := by
        simp only [List.length_append, List.length_replicate, List.length_singleton]
        omega
      have hlen2 : (List.replicate (((polyDivModStep b)^[k] ([], polyTrim a)).2.length - b.length)
          false ++ b).length ≤ a.length := by
        simp only [List.length_append, List.length_replicate]
        omega
      refine ⟨(length_polyAdd_le _ _).trans (max_le h1 hlen1),
        (length_polyAdd_le _ _).trans (max_le h2 hlen2), polyTrim_polyAdd _ _⟩

/-- Euclidean division specification for `polyQuot` and `polyMod` when `polyOfBits b ≠ 0`. -/
theorem polyOfBits_polyDivMod_spec {a b : List Bool} (hb : polyOfBits b ≠ 0) :
    polyOfBits (polyQuot a b) * polyOfBits b + polyOfBits (polyMod a b) = polyOfBits a ∧
      (polyMod a b).length < (polyTrim b).length ∧
      polyTrim (polyQuot a b) = polyQuot a b ∧
      polyTrim (polyMod a b) = polyMod a b := by
  set bt := polyTrim b
  have hbt_trim : polyTrim bt = bt := polyTrim_polyTrim b
  have hbt_ne : bt ≠ [] := polyOfBits_ne_zero_iff_polyTrim.mp hb
  have hiter : ∀ k : ℕ,
      let st := (polyDivModStep bt)^[k] ([], polyTrim a)
      polyOfBits st.1 * polyOfBits bt + polyOfBits st.2 = polyOfBits a ∧
        polyTrim st.1 = st.1 ∧ polyTrim st.2 = st.2 ∧
        st.2.length ≤ max (bt.length - 1) (a.length - k) := by
    intro k
    induction k with
    | zero =>
      simp only [Function.iterate_zero, id_eq, polyOfBits_nil, zero_mul, polyOfBits_polyTrim,
        zero_add, polyTrim_nil, polyTrim_polyTrim, Nat.sub_zero, true_and]
      exact (length_polyTrim_le a).trans (le_max_right _ _)
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hinv, h1, h2, hlen⟩ := ih
      obtain ⟨hinv', h1', h2', hstay, hdrop⟩ := polyDivModStep_spec hbt_trim _ hinv h2
      refine ⟨hinv', h1', h2', ?_⟩
      by_cases hlt : ((polyDivModStep bt)^[k] ([], polyTrim a)).2.length < bt.length
      · rw [hstay (Or.inl hlt)]
        exact le_trans (by omega) (le_max_left _ _)
      · have hle : bt.length ≤ ((polyDivModStep bt)^[k] ([], polyTrim a)).2.length := by omega
        have hlt' := hdrop hle hbt_ne
        have hlen' : ((polyDivModStep bt)^[k] ([], polyTrim a)).2.length ≤ a.length - k := by
          rcases max_cases (bt.length - 1) (a.length - k) with ⟨hmax, _⟩ | ⟨hmax, _⟩
          · omega
          · rwa [← hmax]
        have := List.length_pos_of_ne_nil hbt_ne
        omega
  obtain ⟨hinv, hq, hr, hlen⟩ := hiter a.length
  rw [Nat.sub_self] at hlen
  have hbt_pos := List.length_pos_of_ne_nil hbt_ne
  rw [polyOfBits_polyTrim] at hinv
  have hlt : (polyMod a b).length < bt.length := by
    change ((polyDivModStep bt)^[a.length] ([], polyTrim a)).2.length < bt.length
    omega
  exact ⟨hinv, hlt, hq, hr⟩

/-- `polyOfBits b ∣ polyOfBits a` if and only if `polyMod a b = []`. -/
theorem polyOfBits_polyMod_dvd_iff {a b : List Bool} (hb : polyOfBits b ≠ 0) :
    polyOfBits b ∣ polyOfBits a ↔ polyMod a b = [] := by
  obtain ⟨hinv, hlt, -, htrim⟩ := polyOfBits_polyDivMod_spec (a := a) hb
  constructor
  · intro hdvd
    have hrem_dvd : polyOfBits b ∣ polyOfBits (polyMod a b) := by
      have : polyOfBits (polyMod a b) =
          polyOfBits a - polyOfBits (polyQuot a b) * polyOfBits b := by
        rw [← hinv, add_sub_cancel_left]
      rw [this]
      exact dvd_sub hdvd (dvd_mul_left _ _)
    have hdeg_lt : (polyOfBits (polyMod a b)).degree < (polyOfBits b).degree := by
      rcases eq_or_ne (polyMod a b) [] with hnil | hne
      · rw [hnil, polyOfBits_nil, degree_zero]
        rw [degree_eq_natDegree hb]
        exact WithBot.bot_lt_coe _
      · have hzero : polyOfBits (polyMod a b) ≠ 0 :=
          polyOfBits_ne_zero_iff_polyTrim.mpr (by rw [htrim]; exact hne)
        have hbt_ne : polyTrim b ≠ [] := polyOfBits_ne_zero_iff_polyTrim.mp hb
        have hbt_pos : 0 < (polyTrim b).length := List.length_pos_of_ne_nil hbt_ne
        have hne_pos : 0 < (polyMod a b).length := List.length_pos_of_ne_nil hne
        have hdeg_r : (polyOfBits (polyMod a b)).natDegree = (polyMod a b).length - 1 :=
          natDegree_polyOfBits_of_polyTrim htrim hne
        have hdeg_b : (polyOfBits b).natDegree = (polyTrim b).length - 1 := by
          rw [← polyOfBits_polyTrim b]
          exact natDegree_polyOfBits_of_polyTrim (polyTrim_polyTrim b) hbt_ne
        rw [degree_eq_natDegree hzero, degree_eq_natDegree hb, Nat.cast_lt, hdeg_r, hdeg_b]
        omega
    have hrem0 : polyOfBits (polyMod a b) = 0 := eq_zero_of_dvd_of_degree_lt hrem_dvd hdeg_lt
    have hrem_trim := (polyTrim_eq_nil_iff (polyMod a b)).mpr hrem0
    rwa [htrim] at hrem_trim
  · intro hnil
    rw [hnil, polyOfBits_nil, add_zero] at hinv
    rw [← hinv]
    exact dvd_mul_left _ _

/-- One step of the binary Euclidean algorithm for `polyGcd`. -/
@[expose] def polyGcdStep (st : List Bool × List Bool) : List Bool × List Bool :=
  if st.2.isEmpty then st else (st.2, polyMod st.1 st.2)

/-- Greatest common divisor of two binary polynomials over `𝔽₂`, as a trimmed list. -/
@[expose] def polyGcd (a b : List Bool) : List Bool :=
  ((polyGcdStep)^[a.length + b.length + 1] (polyTrim a, polyTrim b)).1

/-- Length and trimming invariants along iterations of `polyGcdStep`. -/
theorem polyGcd_iterate_bounds (a b : List Bool) (k : ℕ) :
    let st := (polyGcdStep)^[k] (polyTrim a, polyTrim b)
    st.1.length ≤ max a.length b.length ∧ st.2.length ≤ max a.length b.length := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    exact ⟨(length_polyTrim_le a).trans (le_max_left _ _),
      (length_polyTrim_le b).trans (le_max_right _ _)⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    dsimp only [polyGcdStep]
    split_ifs
    · exact ih
    · refine ⟨ih.2, ?_⟩
      exact (polyDivMod_iterate_bounds _ _ _).2.1.trans ih.1

private theorem polyGcd_invariant (a b : List Bool) (k : ℕ) :
    let st := (polyGcdStep)^[k] (polyTrim a, polyTrim b)
    polyTrim st.1 = st.1 ∧ polyTrim st.2 = st.2 ∧
      (∀ u : (ZMod 2)[X], (u ∣ polyOfBits st.1 ∧ u ∣ polyOfBits st.2) ↔
        (u ∣ polyOfBits a ∧ u ∣ polyOfBits b)) := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq, polyTrim_polyTrim, polyOfBits_polyTrim, iff_self,
      implies_true, and_self]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨ht1, ht2, hdiv⟩ := ih
    dsimp only [polyGcdStep]
    split_ifs with h
    · exact ⟨ht1, ht2, hdiv⟩
    · simp only [List.isEmpty_iff] at h
      have h2_ne : polyOfBits ((polyGcdStep)^[k] (polyTrim a, polyTrim b)).2 ≠ 0 :=
        polyOfBits_ne_zero_iff_polyTrim.mpr (by rw [ht2]; exact h)
      obtain ⟨hinv, -, -, hrm⟩ := polyOfBits_polyDivMod_spec
        (a := ((polyGcdStep)^[k] (polyTrim a, polyTrim b)).1) h2_ne
      refine ⟨ht2, hrm, fun u => ?_⟩
      rw [← hdiv u]
      constructor
      · rintro ⟨hu2, hur⟩
        refine ⟨?_, hu2⟩
        rw [← hinv]
        exact dvd_add (dvd_mul_of_dvd_right hu2 _) hur
      · rintro ⟨hu1, hu2⟩
        refine ⟨hu2, ?_⟩
        have heq : polyOfBits (polyMod ((polyGcdStep)^[k] (polyTrim a, polyTrim b)).1
            ((polyGcdStep)^[k] (polyTrim a, polyTrim b)).2) =
            polyOfBits ((polyGcdStep)^[k] (polyTrim a, polyTrim b)).1 -
              polyOfBits (polyQuot ((polyGcdStep)^[k] (polyTrim a, polyTrim b)).1
                ((polyGcdStep)^[k] (polyTrim a, polyTrim b)).2) *
              polyOfBits ((polyGcdStep)^[k] (polyTrim a, polyTrim b)).2 := by
          rw [← hinv, add_sub_cancel_left]
        rw [heq]
        exact dvd_sub hu1 (dvd_mul_of_dvd_right hu2 _)

private theorem polyGcd_terminates :
    ∀ (k : ℕ) (x y : List Bool), polyTrim y = y → y.length ≤ k →
      ((polyGcdStep)^[k] (x, y)).2 = []
  | 0, _, y, _, hlen => by
    rw [Function.iterate_zero, id_eq]
    exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
  | k + 1, x, y, hy, hlen => by
    rw [Function.iterate_succ_apply]
    dsimp only [polyGcdStep]
    split_ifs with h
    · rw [List.isEmpty_iff] at h
      subst h
      exact polyGcd_terminates k x [] rfl (by simp)
    · simp only [List.isEmpty_iff] at h
      have hy_ne : polyOfBits y ≠ 0 := polyOfBits_ne_zero_iff_polyTrim.mpr (by rw [hy]; exact h)
      obtain ⟨-, hlt, -, hr⟩ := polyOfBits_polyDivMod_spec (a := x) hy_ne
      rw [hy] at hlt
      exact polyGcd_terminates k y (polyMod x y) hr (by omega)

/-- `polyGcd a b` is always trimmed. -/
@[simp]
theorem polyTrim_polyGcd (a b : List Bool) : polyTrim (polyGcd a b) = polyGcd a b :=
  (polyGcd_invariant a b (a.length + b.length + 1)).1

private theorem polyOfBits_polyGcd_dvd_pair (a b : List Bool) :
    polyOfBits (polyGcd a b) ∣ polyOfBits a ∧ polyOfBits (polyGcd a b) ∣ polyOfBits b := by
  have hnil : ((polyGcdStep)^[a.length + b.length + 1] (polyTrim a, polyTrim b)).2 = [] :=
    polyGcd_terminates (a.length + b.length + 1) (polyTrim a) (polyTrim b)
      (polyTrim_polyTrim b) (by have := length_polyTrim_le b; omega)
  have hdiv := (polyGcd_invariant a b (a.length + b.length + 1)).2.2 (polyOfBits (polyGcd a b))
  rw [hnil, polyOfBits_nil] at hdiv
  exact hdiv.mp ⟨dvd_rfl, dvd_zero _⟩

/-- `polyOfBits (polyGcd a b)` divides `polyOfBits a`. -/
theorem polyOfBits_polyGcd_dvd_left (a b : List Bool) :
    polyOfBits (polyGcd a b) ∣ polyOfBits a :=
  (polyOfBits_polyGcd_dvd_pair a b).1

/-- `polyOfBits (polyGcd a b)` divides `polyOfBits b`. -/
theorem polyOfBits_polyGcd_dvd_right (a b : List Bool) :
    polyOfBits (polyGcd a b) ∣ polyOfBits b :=
  (polyOfBits_polyGcd_dvd_pair a b).2

/-- Common divisors of `polyOfBits a` and `polyOfBits b` divide `polyOfBits (polyGcd a b)`. -/
theorem dvd_polyOfBits_polyGcd {a b : List Bool} {u : (ZMod 2)[X]}
    (ha : u ∣ polyOfBits a) (hb : u ∣ polyOfBits b) :
    u ∣ polyOfBits (polyGcd a b) := by
  have hdiv := (polyGcd_invariant a b (a.length + b.length + 1)).2.2 u
  exact (hdiv.mpr ⟨ha, hb⟩).1

/-- `polyOfBits (polyGcd a b) ≠ 0` whenever either argument is nonzero. -/
theorem polyOfBits_polyGcd_ne_zero {a b : List Bool} (h : polyOfBits a ≠ 0 ∨ polyOfBits b ≠ 0) :
    polyOfBits (polyGcd a b) ≠ 0 := by
  intro h0
  have hdvd_a := polyOfBits_polyGcd_dvd_left a b
  have hdvd_b := polyOfBits_polyGcd_dvd_right a b
  rw [h0, zero_dvd_iff] at hdvd_a hdvd_b
  rcases h with ha | hb
  · exact ha hdvd_a
  · exact hb hdvd_b

/-- Compose a binary polynomial `f` with `X ^ q` (`f(X^q)`), as a trimmed bit list. -/
@[expose] def polyComposePow (q : ℕ) (f : List Bool) : List Bool :=
  if q = 0 then polyTrim [f.foldl xor false]
  else
    polyTrim ((List.range (q * f.length)).map fun j =>
      if j % q == 0 then f.getD (j / q) false else false)

/-- `polyComposePow q f` is always trimmed. -/
@[simp]
theorem polyTrim_polyComposePow (q : ℕ) (f : List Bool) :
    polyTrim (polyComposePow q f) = polyComposePow q f := by
  unfold polyComposePow
  split_ifs <;> exact polyTrim_polyTrim _

/-- `polyComposePow q f` computes polynomial composition with `X ^ q` in `𝔽₂[X]`. -/
theorem polyOfBits_polyComposePow {q : ℕ} (hq : 0 < q) (f : List Bool) :
    polyOfBits (polyComposePow q f) = (polyOfBits f).comp (X ^ q) := by
  rw [polyComposePow, ite_eq_right hq.ne', polyOfBits_polyTrim]
  ext k
  rw [coeff_polyOfBits, coeff_comp_X_pow _ hq, coeff_polyOfBits]
  by_cases hk : k < q * f.length
  · rw [List.getD_map_range _ false hk]
    by_cases hdiv : q ∣ k
    · simp [hdiv, Nat.mod_eq_zero_of_dvd hdiv]
    · have hmod : ¬ k % q = 0 := fun h => hdiv (Nat.dvd_of_mod_eq_zero h)
      simp [hdiv, hmod]
  · rw [List.getD_eq_default _ _ (by simp; omega), bitEquiv_symm_false]
    symm
    split_ifs with hdiv
    · have hle : f.length ≤ k / q := by
        by_contra hlt
        have : q * (k / q) < q * f.length := Nat.mul_lt_mul_of_pos_left (by omega) hq
        rw [Nat.mul_div_cancel' hdiv] at this
        omega
      rw [List.getD_eq_default f _ hle, bitEquiv_symm_false]
    · rfl

/-! ### Boolean Gaussian elimination (`kernelVecBits`) matching `kernelVec` -/

/-- Bit-vector to `Fin n → ZMod 2` interpretation. -/
@[expose] def bitsToZModVec (n : ℕ) (v : List Bool) : Fin n → ZMod 2 :=
  fun i => bitEquiv.symm (v.getD i.1 false)

/-- Row-list to `Matrix (Fin r) (Fin n) (ZMod 2)` interpretation. -/
@[expose] def rowsToZModMatrix (r n : ℕ) (M : List (List Bool)) :
    Matrix (Fin r) (Fin n) (ZMod 2) :=
  fun i => bitsToZModVec n (M.getD i.1 [])

private theorem listDot_eq_dotProduct {n : ℕ} {u v : List Bool}
    (hu : u.length = n) (hv : v.length = n) :
    bitEquiv.symm (listDot u v) = bitsToZModVec n u ⬝ᵥ bitsToZModVec n v := by
  unfold listDot
  have hmap :
      (u.zipWith Bool.and v).map bitEquiv.symm =
        List.ofFn (fun i : Fin n => bitsToZModVec n u i * bitsToZModVec n v i) := by
    refine List.ext_getElem (by simp [hu, hv]) fun i hi _ => ?_
    have hi' : i < n := by simpa [hu, hv] using hi
    simp only [List.getElem_map, List.getElem_zipWith, List.getElem_ofFn, bitsToZModVec]
    rw [List.getD_eq_getElem u false (by omega), List.getD_eq_getElem v false (by omega),
      ← Bool.mul_eq_and, map_mul]
  rw [bitEquiv_symm_foldl_xor, hmap, List.sum_ofFn, dotProduct]

/-- One elimination step on the candidate basis `N` using row `a`. -/
@[expose] def kernelStepBits (a : List Bool) (N : List (List Bool)) : List (List Bool) :=
  let vals := N.map (listDot a)
  let p := vals.idxOf true
  if p < N.length then
    let piv := N.getD p []
    N.map fun v => if listDot a v then v.zipWith xor piv else v
  else N

/-- Basis after processing all rows of `M` starting from `listSingles n`. -/
@[expose] def kernelBasisBits (n : ℕ) (M : List (List Bool)) : List (List Bool) :=
  M.foldl (fun N a => kernelStepBits a N) (listSingles n)

/-- Canonical nonzero kernel vector of `M` over `𝔽₂`, or all `false` if trivial. -/
@[expose] def kernelVecBits (n : ℕ) (M : List (List Bool)) : List Bool :=
  ((kernelBasisBits n M).find? fun v => v.any id).getD (List.replicate n false)

/-- `kernelStepBits` preserves row count and row length `n`. -/
theorem length_kernelStepBits {n : ℕ} {a : List Bool} {N : List (List Bool)}
    (hN_len : N.length = n) (hN_mem : ∀ v ∈ N, v.length = n) :
    (kernelStepBits a N).length = n ∧ ∀ v ∈ kernelStepBits a N, v.length = n := by
  unfold kernelStepBits
  dsimp only
  split_ifs with h
  · refine ⟨by simpa using hN_len, ?_⟩
    rintro w hw
    rw [List.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hv_len : v.length = n := hN_mem v hv
    have hpiv_len : (N.getD ((N.map (listDot a)).idxOf true) []).length = n :=
      hN_mem _ (List.getD_mem [] (by simpa using h))
    split_ifs
    · rw [List.length_zipWith, hv_len, hpiv_len, min_self]
    · exact hv_len
  · exact ⟨hN_len, hN_mem⟩

/-- Prefix folding of `kernelStepBits` preserves row count and row length `n`. -/
theorem length_kernelBasisBits_take {n : ℕ} (M : List (List Bool)) (k : ℕ) :
    ((M.take k).foldl (fun N a => kernelStepBits a N) (listSingles n)).length = n ∧
      ∀ v ∈ (M.take k).foldl (fun N a => kernelStepBits a N) (listSingles n), v.length = n := by
  induction k with
  | zero =>
    simp only [List.take_zero, List.foldl_nil, listSingles, List.length_map, List.length_range,
      List.mem_map, List.mem_range, true_and]
    rintro v ⟨i, _, rfl⟩
    simp [listSingle]
  | succ k ih =>
    by_cases hk : k < M.length
    · rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact length_kernelStepBits ih.1 ih.2
    · have hge : M.length ≤ k := Nat.le_of_not_lt hk
      have h1 : M.take (k + 1) = M := List.take_of_length_le (by omega)
      have h2 : M.take k = M := List.take_of_length_le hge
      rw [h1]
      rwa [h2] at ih

/-- `kernelBasisBits n M` has `n` rows, each of length `n`. -/
theorem length_kernelBasisBits (n : ℕ) (M : List (List Bool)) :
    (kernelBasisBits n M).length = n ∧ ∀ v ∈ kernelBasisBits n M, v.length = n := by
  have h := length_kernelBasisBits_take (n := n) M M.length
  simpa [kernelBasisBits] using h

/-- `kernelVecBits n M` has length `n`. -/
theorem length_kernelVecBits (n : ℕ) (M : List (List Bool)) :
    (kernelVecBits n M).length = n := by
  unfold kernelVecBits
  cases hfind : (kernelBasisBits n M).find? fun v => v.any id with
  | none => simp
  | some v => exact (length_kernelBasisBits n M).2 v (List.mem_of_find?_eq_some hfind)

private theorem sum_firstFlags_smul_eq_of_first {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    {n : ℕ} (b : Fin n → ZMod 2) (g : Fin n → M) {p : Fin n}
    (hp : b p ≠ 0) (hmin : ∀ i < p, b i = 0) :
    ∑ i, firstFlags b i • g i = g p := by
  rcases LinearAlgebra.sum_firstFlags_smul_eq b g with ⟨h0, _⟩ | ⟨j, hj, hlt, hsum⟩
  · exact absurd (congrFun h0 p) hp
  · have hjp : j = p :=
      le_antisymm (not_lt.mp fun h => absurd (hlt p h) hp)
        (not_lt.mp fun h => absurd (hmin j h) hj)
    rwa [hjp] at hsum

/-- `bitsToZModVec n v` vanishes iff no entry of `v` is `true`. -/
theorem bitsToZModVec_eq_zero_iff {n : ℕ} {v : List Bool} (hv : v.length = n) :
    bitsToZModVec n v = 0 ↔ v.any id = false := by
  rw [funext_iff]
  simp only [bitsToZModVec, Pi.zero_apply, map_eq_zero_iff bitEquiv.symm bitEquiv.symm.injective,
    Bool.zero_eq_false, List.any_eq_false, id_eq, Bool.not_eq_true]
  constructor
  · intro h b hb
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    simpa [List.getElem?_eq_getElem hj] using h ⟨j, by omega⟩
  · intro h j
    have hj := h _ (List.getD_mem false (i := j.1) (by omega))
    simpa only [List.getD_eq_getElem?_getD] using hj

private theorem kernelStepBits_eq_kernelStep {n : ℕ} {a : List Bool} {N : List (List Bool)}
    (ha : a.length = n) (hN_len : N.length = n) (hN_mem : ∀ v ∈ N, v.length = n) (i : Fin n) :
    bitsToZModVec n ((kernelStepBits a N).getD i.1 []) =
      kernelStep (bitsToZModVec n a) (fun j => bitsToZModVec n (N.getD j.1 [])) i := by
  let aZ := bitsToZModVec n a
  let NZ : Fin n → Fin n → ZMod 2 := fun j => bitsToZModVec n (N.getD j.1 [])
  have hval : ∀ j : Fin n, rowValues aZ NZ j = bitEquiv.symm (listDot a (N.getD j.1 [])) := by
    intro j
    rw [rowValues, listDot_eq_dotProduct ha (hN_mem _ (List.getD_mem [] (by omega)))]
  unfold kernelStepBits
  dsimp only
  by_cases hp_lt : (N.map (listDot a)).idxOf true < N.length
  · set p := (N.map (listDot a)).idxOf true
    have hp_lt' : p < n := by omega
    have hp_dot : listDot a (N.getD p []) = true := by
      rw [List.getD_eq_getElem N [] hp_lt, ← List.getElem_map (f := listDot a)]
      exact List.getElem_idxOf (by simpa only [List.length_map] using hp_lt)
    have hp_min : ∀ k : Fin n, k < ⟨p, hp_lt'⟩ → rowValues aZ NZ k = 0 := by
      intro k hk
      have hnt := List.not_of_lt_findIdx (p := (· == true)) (xs := N.map (listDot a)) hk
      simp only [List.getElem_map, beq_true] at hnt
      rw [hval k, List.getD_eq_getElem _ _ (by omega), hnt, bitEquiv_symm_false]
    have hpiv_eq : pivotVec aZ NZ = NZ ⟨p, hp_lt'⟩ :=
      sum_firstFlags_smul_eq_of_first (rowValues aZ NZ) NZ
        (by rw [hval ⟨p, hp_lt'⟩, hp_dot]; exact one_ne_zero) hp_min
    have hbeta : aZ ⬝ᵥ pivotVec aZ NZ = 1 := by
      rw [hpiv_eq]
      change rowValues aZ NZ ⟨p, hp_lt'⟩ = 1
      rw [hval ⟨p, hp_lt'⟩, hp_dot, bitEquiv_symm_true]
    rw [ite_eq_left hp_lt, List.getD_eq_getElem _ _ (by simp [hN_len]), List.getElem_map,
      kernelStep, hbeta, div_one, ← List.getD_eq_getElem N [] (by omega)]
    have hi_len : (N.getD i.1 []).length = n := hN_mem _ (List.getD_mem [] (by omega))
    have hpiv_len : (N.getD p []).length = n := hN_mem _ (List.getD_mem [] hp_lt)
    by_cases hdi : listDot a (N.getD i.1 []) = true
    · rw [ite_eq_left hdi, show rowValues aZ NZ i = 1 by rw [hval i, hdi, bitEquiv_symm_true],
        one_smul, hpiv_eq]
      funext k
      simp only [bitsToZModVec, Pi.sub_apply, NZ]
      rw [List.getD_eq_getElem _ _
          (by rw [List.length_zipWith, hi_len, hpiv_len, min_self]; exact k.2),
        List.getElem_zipWith, ← List.getD_eq_getElem _ false (by omega),
        ← List.getD_eq_getElem _ false (by omega), ← Bool.add_eq_xor, map_add, CharTwo.sub_eq_add]
    · rw [ite_eq_right hdi,
        show rowValues aZ NZ i = 0 by
          rw [hval i, Bool.eq_false_of_not_eq_true hdi, bitEquiv_symm_false],
        zero_smul, sub_zero]
  · rw [ite_eq_right hp_lt]
    have hnot : true ∉ N.map (listDot a) := by
      rw [← List.idxOf_lt_length_iff, List.length_map]
      exact hp_lt
    have hrow0 : rowValues aZ NZ = 0 := funext fun j => by
      have hne : listDot a (N.getD j.1 []) ≠ true :=
        fun h => hnot (List.mem_map.mpr ⟨_, List.getD_mem [] (by omega), h⟩)
      rw [hval j, Bool.eq_false_of_not_eq_true hne, bitEquiv_symm_false]
      rfl
    have hpiv0 : pivotVec aZ NZ = 0 := by simp [pivotVec, firstFlags_of_eq_zero hrow0]
    rw [kernelStep, hpiv0, hrow0, Pi.zero_apply, zero_div, zero_smul, sub_zero]

private theorem kernelBasisBits_take_eq {r n : ℕ} (M : List (List Bool)) (hM_len : M.length = r)
    (hM_mem : ∀ a ∈ M, a.length = n) (k : ℕ) (hk : k ≤ r) (i : Fin n) :
    bitsToZModVec n
        (((M.take k).foldl (fun N a => kernelStepBits a N) (listSingles n)).getD i.1 []) =
      kernelBasisUpTo (rowsToZModMatrix r n M) k i := by
  induction k generalizing i with
  | zero =>
    simp only [List.take_zero, List.foldl_nil, kernelBasisUpTo, listSingles]
    rw [List.getD_map_range (listSingle n) [] i.2, listSingle_eq_ofFn_single]
    funext j
    simp only [bitsToZModVec]
    rw [List.getD_ofFn]
    simp only [Pi.single_apply, Fin.ext_iff]
    split_ifs <;> simp
  | succ k ih =>
    have hkr : k < r := by omega
    rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons,
      List.foldl_nil, kernelBasisUpTo, dite_eq_left hkr]
    have hprev := length_kernelBasisBits_take (n := n) M k
    rw [kernelStepBits_eq_kernelStep (hM_mem _ (List.getElem_mem _)) hprev.1 hprev.2 i]
    have hrow : bitsToZModVec n (M[k]'(by omega)) = rowsToZModMatrix r n M ⟨k, hkr⟩ := by
      funext j
      dsimp only [bitsToZModVec, rowsToZModMatrix]
      rw [List.getD_eq_getElem M [] (by omega)]
    rw [hrow, funext fun j => ih (by omega) j]

/-- `kernelBasisBits` agrees with `LinearAlgebra.kernelBasis` under `bitsToZModVec`. -/
theorem bitsToZModVec_kernelBasisBits {r n : ℕ} (M : List (List Bool)) (hM_len : M.length = r)
    (hM_mem : ∀ a ∈ M, a.length = n) (i : Fin n) :
    bitsToZModVec n ((kernelBasisBits n M).getD i.1 []) =
      kernelBasis (rowsToZModMatrix r n M) i := by
  have h := kernelBasisBits_take_eq M hM_len hM_mem r le_rfl i
  have htake : M.take r = M := List.take_of_length_le hM_len.le
  rw [htake] at h
  exact h

/-- `kernelVecBits` agrees with `LinearAlgebra.kernelVec` under `bitsToZModVec`. -/
theorem bitsToZModVec_kernelVecBits_eq {r n : ℕ} (M : List (List Bool)) (hM_len : M.length = r)
    (hM_mem : ∀ a ∈ M, a.length = n) :
    bitsToZModVec n (kernelVecBits n M) = kernelVec (rowsToZModMatrix r n M) := by
  let A := rowsToZModMatrix r n M
  let N := kernelBasisBits n M
  have hN_len : N.length = n := (length_kernelBasisBits n M).1
  have hN_mem : ∀ v ∈ N, v.length = n := (length_kernelBasisBits n M).2
  unfold kernelVecBits
  rw [kernelVec]
  cases hfind : N.find? (fun v => v.any id) with
  | none =>
    simp only [Option.getD_none]
    have hnone : ∀ i : Fin n, kernelBasis A i = 0 := fun i => by
      rw [← bitsToZModVec_kernelBasisBits M hM_len hM_mem i]
      have hi_mem : N.getD i.1 [] ∈ N := List.getD_mem [] (by omega)
      exact (bitsToZModVec_eq_zero_iff (hN_mem _ hi_mem)).mpr
        (Bool.eq_false_of_not_eq_true (List.find?_eq_none.mp hfind _ hi_mem))
    have hflags : (fun i => if kernelBasis A i = 0 then (0 : ZMod 2) else 1) = 0 :=
      funext fun i => by simp [hnone i]
    rw [firstFlags_of_eq_zero hflags]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact (bitsToZModVec_eq_zero_iff List.length_replicate).mpr (by simp)
  | some v =>
    simp only [Option.getD_some]
    obtain ⟨hp_pred, p, hp_lt, hp_get, hp_min⟩ := List.find?_eq_some_iff_getElem.mp hfind
    have hp_lt' : p < n := by omega
    have hv_eq : v = N.getD p [] := by rw [List.getD_eq_getElem _ _ hp_lt, hp_get]
    have hne_p : kernelBasis A ⟨p, hp_lt'⟩ ≠ 0 := by
      rw [← bitsToZModVec_kernelBasisBits M hM_len hM_mem ⟨p, hp_lt'⟩, ← hv_eq,
        Ne, bitsToZModVec_eq_zero_iff (hN_mem v (List.mem_of_find?_eq_some hfind)), hp_pred]
      exact Bool.false_ne_true.symm
    have hlt_p : ∀ i < (⟨p, hp_lt'⟩ : Fin n),
        (if kernelBasis A i = 0 then (0 : ZMod 2) else 1) = 0 := by
      intro i hi
      have hfalse : (N[i.1]'(by omega)).any id = false :=
        Bool.eq_false_of_not_eq_true (by simpa using hp_min i.1 hi)
      have hi0 : kernelBasis A i = 0 := by
        rw [← bitsToZModVec_kernelBasisBits M hM_len hM_mem i, List.getD_eq_getElem N [] (by omega)]
        exact (bitsToZModVec_eq_zero_iff (hN_mem _ (List.getElem_mem _))).mpr hfalse
      simp [hi0]
    rw [sum_firstFlags_smul_eq_of_first _ (kernelBasis A) (by simp [hne_p]) hlt_p,
      hv_eq, bitsToZModVec_kernelBasisBits M hM_len hM_mem ⟨p, hp_lt'⟩]

/-- `kernelVecBits n M` lies in the right kernel of `rowsToZModMatrix r n M`. -/
theorem mulVec_kernelVecBits {r n : ℕ} (M : List (List Bool)) (hM_len : M.length = r)
    (hM_mem : ∀ a ∈ M, a.length = n) :
    rowsToZModMatrix r n M *ᵥ bitsToZModVec n (kernelVecBits n M) = 0 := by
  rw [bitsToZModVec_kernelVecBits_eq M hM_len hM_mem]
  exact mulVec_kernelVec _

/-- If `rowsToZModMatrix r n M` has a nonzero kernel vector, `kernelVecBits n M` has a `true`
bit. -/
theorem kernelVecBits_any_of_exists {r n : ℕ} (M : List (List Bool)) (hM_len : M.length = r)
    (hM_mem : ∀ a ∈ M, a.length = n)
    (hex : ∃ v : Fin n → ZMod 2, v ≠ 0 ∧ rowsToZModMatrix r n M *ᵥ v = 0) :
    (kernelVecBits n M).any id = true := by
  have hne : bitsToZModVec n (kernelVecBits n M) ≠ 0 := by
    rw [bitsToZModVec_kernelVecBits_eq M hM_len hM_mem]
    exact kernelVec_ne_zero _ hex
  rw [Ne, bitsToZModVec_eq_zero_iff (length_kernelVecBits n M)] at hne
  exact Bool.eq_true_of_not_eq_false hne

/-! ### Deterministic Berlekamp factoring over `𝔽₂` -/

/-- Frobenius matrix `Q - I` restricted to polynomials `∑_{k=0}^{d-2} c_k X^{k+1}` of degree `< d`
with zero constant coefficient (`d = g.length - 1`). Has `d` rows and `d - 1` columns. -/
@[expose] def berlekampMatrix (g : List Bool) : List (List Bool) :=
  let d := g.length - 1
  let tab := powerTable g
  (List.range d).map fun i =>
    (List.range (d - 1)).map fun k =>
      let j := k + 1
      xor ((tab.getD (2 * j) []).getD i false) (decide (i == j))

/-- One deterministic Berlekamp splitting step on `g`. -/
@[expose] def berlekampStep (g : List Bool) : List Bool :=
  let gt := polyTrim g
  if gt.length ≤ 2 then gt
  else
    let v := kernelVecBits (gt.length - 2) (berlekampMatrix gt)
    if v.any id then polyGcd gt (false :: v)
    else gt

/-- Deterministic Berlekamp irreducible factor extractor over `𝔽₂`. -/
@[expose] def berlekampIrreducibleFactor (g : List Bool) : List Bool :=
  (berlekampStep)^[g.length] (polyTrim g)

private theorem length_berlekampMatrix (g : List Bool) :
    (berlekampMatrix g).length = g.length - 1 ∧
      ∀ row ∈ berlekampMatrix g, row.length = g.length - 2 := by
  unfold berlekampMatrix
  refine ⟨by simp, ?_⟩
  rintro row hrow
  rw [List.mem_map] at hrow
  obtain ⟨i, _, rfl⟩ := hrow
  simp only [List.length_map, List.length_range]
  omega

private theorem eq_sum_C_mul_X_pow_succ_of_coeff_zero {R : Type*} [Semiring R] {d : ℕ} {h : R[X]}
    (h0 : h.coeff 0 = 0) (hhi : ∀ m, d ≤ m → h.coeff m = 0) :
    h = ∑ k : Fin (d - 1), C (h.coeff (k.1 + 1)) * X ^ (k.1 + 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Finset.sum_eq_zero fun k _ => absurd k.2 (by omega)]
    ext m
    rw [coeff_zero]
    exact hhi m (Nat.zero_le m)
  · have hdeg : h.natDegree < (d - 1) + 1 := by
      rcases eq_or_ne h 0 with rfl | hne
      · simp
      · exact Nat.lt_of_not_le fun hle => hne (leadingCoeff_eq_zero.mp (hhi _ (by omega)))
    conv_lhs => rw [as_sum_range' h ((d - 1) + 1) hdeg]
    rw [Finset.sum_range_succ', h0, monomial_zero_right, add_zero,
      ← Fin.sum_univ_eq_sum_range (fun i => monomial (i + 1) (h.coeff (i + 1)))]
    simp only [C_mul_X_pow_eq_monomial]

private theorem poly_from_berlekampVec {d : ℕ} (v : Fin (d - 1) → ZMod 2) :
    let h := polyOfBits (false :: List.ofFn fun k : Fin (d - 1) => bitEquiv (v k))
    h = ∑ k : Fin (d - 1), C (v k) * X ^ (k.1 + 1) ∧ h.coeff 0 = 0 ∧
      (d ≤ 1 → h = 0) ∧ (h ≠ 0 → h.natDegree < d) := by
  let l := List.ofFn fun k : Fin (d - 1) => bitEquiv (v k)
  let h := polyOfBits (false :: l)
  have h0 : h.coeff 0 = 0 := by simp [h, coeff_polyOfBits]
  have hhi : ∀ m, d ≤ m → h.coeff m = 0 := by
    rintro (_ | m) hm
    · exact h0
    · rw [coeff_polyOfBits, List.getD_cons_succ, List.getD_eq_default _ _ (by simp [l]; omega),
        bitEquiv_symm_false]
  have hsum : h = ∑ k : Fin (d - 1), C (v k) * X ^ (k.1 + 1) := by
    rw [eq_sum_C_mul_X_pow_succ_of_coeff_zero h0 hhi]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_polyOfBits, List.getD_cons_succ, List.getD_ofFn, bitEquiv.symm_apply_apply]
  have hle1 : d ≤ 1 → h = 0 := fun hd => by
    rw [hsum]
    exact Finset.sum_eq_zero fun k _ => by have := k.2; omega
  exact ⟨hsum, h0, hle1, fun hne => Nat.lt_of_not_le fun hle =>
    hne (leadingCoeff_eq_zero.mp (hhi _ hle))⟩

private theorem berlekampMatrix_mulVec_eq_zero_iff {l : List Bool} (hl : 2 ≤ l.length)
    (v : Fin (l.length - 1) → ZMod 2) :
    rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix (l ++ [true])) *ᵥ v = 0 ↔
      polyOfBits (l ++ [true]) ∣
        (∑ k : Fin (l.length - 1), C (v k) * X ^ (k.1 + 1)) ^ 2 -
          ∑ k : Fin (l.length - 1), C (v k) * X ^ (k.1 + 1) := by
  set gt := l ++ [true]
  set h := ∑ k : Fin (l.length - 1), C (v k) * X ^ (k.1 + 1)
  have hgt_ne : polyOfBits gt ≠ 0 := polyOfBits_ne_zero_of_mem (by simp [gt])
  have hdeg_gt : (polyOfBits gt).natDegree = l.length := natDegree_polyOfBits_append_true l
  let pb := AdjoinRoot.powerBasis hgt_ne
  have hpb_dim : pb.dim = l.length := by simp [pb, hdeg_gt]
  let e : Fin pb.dim ≃ Fin l.length :=
    { toFun := Fin.cast hpb_dim
      invFun := Fin.cast hpb_dim.symm
      left_inv := fun _ => Fin.ext rfl
      right_inv := fun _ => Fin.ext rfl }
  have hsq_sub :
      h ^ 2 - h = ∑ k : Fin (l.length - 1), C (v k) * (X ^ (2 * (k.1 + 1)) - X ^ (k.1 + 1)) := by
    rw [CharTwo.sub_eq_add, CharTwo.sum_sq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, ← C_pow, ZMod.pow_card (v k), ← pow_mul, CharTwo.sub_eq_add, mul_add,
      mul_comm (k.1 + 1) 2]
  have hmk : AdjoinRoot.mk (polyOfBits gt) (h ^ 2 - h) =
      ∑ i : Fin l.length,
        (rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix gt) *ᵥ v) i • pb.gen ^ i.1 := by
    rw [hsq_sub, map_sum]
    have hterm : ∀ k : Fin (l.length - 1),
        AdjoinRoot.mk (polyOfBits gt) (C (v k) * (X ^ (2 * (k.1 + 1)) - X ^ (k.1 + 1))) =
          ∑ i : Fin l.length,
            (v k * rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix gt) i k) •
              pb.gen ^ i.1 := by
      intro k
      rw [map_mul, map_sub, AdjoinRoot.mk_C, map_pow, map_pow, AdjoinRoot.mk_X]
      change (algebraMap (ZMod 2) (AdjoinRoot (polyOfBits gt)) (v k)) *
          (pb.gen ^ (2 * (k.1 + 1)) - pb.gen ^ (k.1 + 1)) = _
      have hroot : aeval pb.gen (polyOfBits (l ++ [true])) = 0 := by
        have hgen : pb.gen = AdjoinRoot.root (polyOfBits gt) := AdjoinRoot.powerBasis_gen hgt_ne
        rw [hgen, AdjoinRoot.aeval_eq]
        dsimp only [gt]
        exact AdjoinRoot.mk_self
      have hpow := pow_eq_sum_powerTable l hroot (e := 2 * (k.1 + 1)) (by omega)
      rw [hpow, ← Fin.sum_univ_eq_sum_range (fun i : ℕ =>
        bitEquiv.symm (((powerTable gt).getD (2 * (k.1 + 1)) []).getD i false) • pb.gen ^ i)]
      have hsingle : pb.gen ^ (k.1 + 1) =
          ∑ i : Fin l.length, (if i.1 = k.1 + 1 then (1 : ZMod 2) else 0) • pb.gen ^ i.1 := by
        rw [Finset.sum_eq_single ⟨k.1 + 1, by omega⟩]
        · simp
        · intro i _ hi
          have hne : i.1 ≠ k.1 + 1 := fun heq => hi (Fin.ext heq)
          simp [hne]
        · intro hm
          exact absurd (Finset.mem_univ (⟨k.1 + 1, by omega⟩ : Fin l.length)) hm
      rw [hsingle, ← Finset.sum_sub_distrib, ← Algebra.smul_def, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, smul_smul]
      have hsub_add :
          (bitEquiv.symm (((powerTable gt).getD (2 * (k.1 + 1)) []).getD i.1 false) -
            if i.1 = k.1 + 1 then (1 : ZMod 2) else 0) =
            rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix gt) i k := by
        rw [rowsToZModMatrix, bitsToZModVec, berlekampMatrix]
        dsimp only
        rw [show gt.length - 1 = l.length by simp [gt],
          List.getD_map_range _ [] i.2, List.getD_map_range _ false k.2,
          ← Bool.add_eq_xor, map_add, CharTwo.sub_eq_add]
        congr 1
        by_cases hik : i.1 = k.1 + 1 <;> simp [hik]
      rw [hsub_add]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (v k)]
  rw [← AdjoinRoot.mk_eq_zero, hmk]
  have hli := pb.basis.linearIndependent
  constructor
  · intro h0
    rw [h0]
    exact Finset.sum_eq_zero fun i _ => by simp
  · intro h0
    have h0' : ∑ i : Fin pb.dim,
        (rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix gt) *ᵥ v) (e i) •
          pb.basis i = 0 := by
      have heq : (∑ i : Fin pb.dim,
          (rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix gt) *ᵥ v) (e i) •
            pb.basis i) =
          ∑ i : Fin l.length,
            (rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix gt) *ᵥ v) i •
              pb.gen ^ i.1 := by
        refine Finset.sum_equiv e (fun _ => by simp) fun i _ => ?_
        rw [pb.coe_basis]
        rfl
      rwa [heq]
    have hcoord := linearIndependent_iff'.mp hli Finset.univ
      (fun i => (rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix gt) *ᵥ v) (e i)) h0'
    funext i
    exact hcoord (e.symm i) (Finset.mem_univ _) |>.trans (by simp)

private theorem natDegree_pos_of_ne_zero_of_not_isUnit {p : (ZMod 2)[X]}
    (hp0 : p ≠ 0) (hpnu : ¬ IsUnit p) : 0 < p.natDegree :=
  Nat.pos_of_ne_zero fun h => hpnu (by
    obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp h
    exact isUnit_C.mpr (Ne.isUnit fun hc => hp0 (by rw [hc, C_0])))

private theorem exists_berlekamp_ker_of_not_irreducible {l : List Bool} (hl : 2 ≤ l.length)
    (hsq : Squarefree (polyOfBits (l ++ [true])))
    (hnirr : ¬ Irreducible (polyOfBits (l ++ [true]))) :
    ∃ v : Fin (l.length - 1) → ZMod 2,
      v ≠ 0 ∧
        rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix (l ++ [true])) *ᵥ v = 0 := by
  set gt := l ++ [true]
  set g := polyOfBits gt
  have hg_ne : g ≠ 0 := polyOfBits_ne_zero_of_mem (by simp [gt])
  have hg_deg : g.natDegree = l.length := natDegree_polyOfBits_append_true l
  have hg_nu : ¬ IsUnit g := not_isUnit_of_natDegree_pos g (by omega)
  rw [irreducible_iff] at hnirr
  push Not at hnirr
  obtain ⟨p, q, hpq, hnp, hnq⟩ := hnirr hg_nu
  have hp_ne : p ≠ 0 := fun h => hg_ne (by rw [hpq, h, zero_mul])
  have hq_ne : q ≠ 0 := fun h => hg_ne (by rw [hpq, h, mul_zero])
  have hp_deg : 0 < p.natDegree := natDegree_pos_of_ne_zero_of_not_isUnit hp_ne hnp
  have hq_deg : 0 < q.natDegree := natDegree_pos_of_ne_zero_of_not_isUnit hq_ne hnq
  have hcop : IsCoprime p q := by
    rw [← EuclideanDomain.gcd_isUnit_iff]
    exact hsq (EuclideanDomain.gcd p q)
      (hpq ▸ mul_dvd_mul (EuclideanDomain.gcd_dvd_left p q) (EuclideanDomain.gcd_dvd_right p q))
  obtain ⟨a, b, hab⟩ := hcop
  set u := (a * p) % g
  have hgu_diff : g ∣ a * p - u :=
    ⟨(a * p) / g, (eq_sub_of_add_eq (EuclideanDomain.div_add_mod (a * p) g)).symm⟩
  have hpu : p ∣ u := by
    have hp_diff : p ∣ a * p - u := dvd_trans ⟨q, hpq⟩ hgu_diff
    simpa only [sub_sub_cancel] using dvd_sub (dvd_mul_left p a) hp_diff
  have hq1u : q ∣ 1 - u := by
    have hq_diff : q ∣ a * p - u := dvd_trans ⟨p, by rw [hpq, mul_comm]⟩ hgu_diff
    rw [show (1 : (ZMod 2)[X]) - u = (a * p - u) + b * q by rw [← hab]; ring]
    exact dvd_add hq_diff (dvd_mul_left q b)
  have hu_ne_zero : u ≠ 0 := fun hu0 => by
    rw [hu0, sub_zero] at hq1u
    exact hnq (isUnit_iff_dvd_one.mpr hq1u)
  have hu_ne_one : u ≠ 1 := fun hu1 => by
    rw [hu1] at hpu
    exact hnp (isUnit_iff_dvd_one.mpr hpu)
  have hgu : g ∣ u ^ 2 - u := by
    rw [show u ^ 2 - u = u * (u - 1) by ring, hpq]
    exact mul_dvd_mul hpu (by simpa only [neg_sub] using dvd_neg.mpr hq1u)
  have hu_deg : u.natDegree < l.length := by
    have hlt := Polynomial.degree_mod_lt (a * p) hg_ne
    rwa [degree_eq_natDegree hg_ne, hg_deg, degree_eq_natDegree hu_ne_zero, Nat.cast_lt] at hlt
  set c0 := u.coeff 0
  set h := u - C c0
  have hh0 : h.coeff 0 = 0 := by simp [h, c0]
  have hh_ne : h ≠ 0 := fun hh0' => by
    have hu_eq : u = C c0 := sub_eq_zero.mp hh0'
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c0 with hc | hc
    · exact hu_ne_zero (by rw [hu_eq, hc, C_0])
    · exact hu_ne_one (by rw [hu_eq, hc, C_1])
  have hh_deg : h.natDegree < l.length :=
    (natDegree_sub_le u (C c0)).trans_lt (by simpa using hu_deg)
  have hgh : g ∣ h ^ 2 - h := by
    have hsq_eq : h ^ 2 - h = u ^ 2 - u := by
      rw [show h = u + C c0 from CharTwo.sub_eq_add u (C c0), CharTwo.add_sq, ← C_pow,
        ZMod.pow_card c0, CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_add_add_comm,
        CharTwo.add_self_eq_zero, add_zero]
    exact hsq_eq.symm ▸ hgu
  let v : Fin (l.length - 1) → ZMod 2 := fun k => h.coeff (k.1 + 1)
  have hh_sum : h = ∑ k : Fin (l.length - 1), C (v k) * X ^ (k.1 + 1) :=
    eq_sum_C_mul_X_pow_succ_of_coeff_zero hh0 fun m hm =>
      coeff_eq_zero_of_natDegree_lt (hh_deg.trans_le hm)
  have hv_ne : v ≠ 0 := fun hv0 => hh_ne <| by
    rw [hh_sum]
    exact Finset.sum_eq_zero fun k _ => by simp [congrFun hv0 k]
  refine ⟨v, hv_ne, (berlekampMatrix_mulVec_eq_zero_iff hl v).mpr ?_⟩
  rwa [← hh_sum]

private theorem berlekampStep_invariant (g : List Bool)
    (hgt : polyTrim g = g) (hsq : Squarefree (polyOfBits g)) (hdeg : 0 < (polyOfBits g).natDegree) :
    let g' := berlekampStep g
    polyTrim g' = g' ∧ Squarefree (polyOfBits g') ∧ 0 < (polyOfBits g').natDegree ∧
      polyOfBits g' ∣ polyOfBits g ∧
      (Irreducible (polyOfBits g) → g' = g) ∧
      (¬ Irreducible (polyOfBits g) → g'.length < g.length) := by
  have hg_ne : g ≠ [] := by
    intro hnil
    rw [hnil, polyOfBits_nil, natDegree_zero] at hdeg
    omega
  obtain ⟨l, hl⟩ : ∃ l, g = l ++ [true] := by
    rcases polyTrim_eq_nil_or_append_true g with hnil | ⟨l, hl⟩
    · rw [hgt] at hnil; exact absurd hnil hg_ne
    · rw [hgt] at hl; exact ⟨l, hl⟩
  have hl_pos : 1 ≤ l.length := by
    have := natDegree_polyOfBits_append_true l
    rw [← hl] at this
    omega
  dsimp only [berlekampStep]
  rw [hgt]
  by_cases hlen2 : g.length ≤ 2
  · have hl_1 : l.length = 1 := by
      have : g.length = l.length + 1 := by rw [hl]; simp
      omega
    have hdeg1 : (polyOfBits g).natDegree = 1 := by
      rw [hl, natDegree_polyOfBits_append_true, hl_1]
    have hirr : Irreducible (polyOfBits g) := Polynomial.irreducible_of_degree_eq_one (by
      rw [degree_eq_natDegree
        (polyOfBits_ne_zero_iff_polyTrim.mpr (by rw [hgt]; exact hg_ne)), hdeg1]
      rfl)
    rw [ite_eq_left hlen2]
    exact ⟨hgt, hsq, hdeg, dvd_rfl, fun _ => rfl, fun hnirr => absurd hirr hnirr⟩
  · have hl2 : 2 ≤ l.length := by
      have : g.length = l.length + 1 := by rw [hl]; simp
      omega
    have hgt_len : g.length - 2 = l.length - 1 := by rw [hl]; simp
    obtain ⟨hM_len, hM_mem⟩ := length_berlekampMatrix g
    have hM_len' : (berlekampMatrix g).length = l.length := by rw [hM_len, hl]; simp
    have hM_mem' : ∀ row ∈ berlekampMatrix g, row.length = l.length - 1 := by
      intro row hrow
      rw [hM_mem row hrow, hgt_len]
    rw [ite_eq_right hlen2]
    set vbits := kernelVecBits (g.length - 2) (berlekampMatrix g)
    have hv_len : vbits.length = l.length - 1 := by rw [length_kernelVecBits, hgt_len]
    by_cases hv : vbits.any id = true
    · rw [ite_eq_left hv]
      set f := polyGcd g (false :: vbits)
      have hfdvd : polyOfBits f ∣ polyOfBits g := polyOfBits_polyGcd_dvd_left _ _
      have hfg_ne : polyOfBits g ≠ 0 :=
        polyOfBits_ne_zero_iff_polyTrim.mpr (by rw [hgt]; exact hg_ne)
      have hf_ne : polyOfBits f ≠ 0 := polyOfBits_polyGcd_ne_zero (Or.inl hfg_ne)
      have hfsq : Squarefree (polyOfBits f) := Squarefree.squarefree_of_dvd hfdvd hsq
      let vZ := bitsToZModVec (l.length - 1) vbits
      have hfv_bits_eq : (false :: vbits) =
          (false :: List.ofFn fun k : Fin (l.length - 1) => bitEquiv (vZ k)) := by
        congr 1
        refine (List.ext_getElem (by simp [hv_len]) fun i hi _ => ?_).symm
        simp only [List.getElem_ofFn, vZ, bitsToZModVec, List.getD_eq_getElem _ _ (by omega),
          bitEquiv.apply_symm_apply]
      have hfv_mul :
          rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix (l ++ [true])) *ᵥ vZ = 0 := by
        rw [← hl]
        dsimp only [vZ, vbits]
        simpa only [hgt_len] using mulVec_kernelVecBits (berlekampMatrix g) hM_len' hM_mem'
      have hgh := (berlekampMatrix_mulVec_eq_zero_iff hl2 vZ).mp hfv_mul
      have hh_spec := poly_from_berlekampVec vZ
      rw [← hfv_bits_eq] at hh_spec
      obtain ⟨hh_sum, hh0, -, hh_deg⟩ := hh_spec
      set hp := polyOfBits (false :: vbits)
      have hhp_ne : hp ≠ 0 := by
        obtain ⟨b, hb, hb'⟩ := List.any_eq_true.mp hv
        exact polyOfBits_ne_zero_of_mem (List.mem_cons_of_mem _ (by simpa using hb' ▸ hb))
      have hhp_deg_lt : hp.natDegree < l.length := hh_deg hhp_ne
      have hg_not_dvd_hp : ¬ polyOfBits g ∣ hp := by
        intro hdvd
        have hle := Polynomial.natDegree_le_of_dvd hdvd hhp_ne
        rw [hl, natDegree_polyOfBits_append_true] at hle
        omega
      have hp1_ne : hp - 1 ≠ 0 := fun h1 => by
        have := congrArg (·.coeff 0) (sub_eq_zero.mp h1)
        simp only [hh0, AddMonoidAlgebra.coeff_one_zero] at this
        exact zero_ne_one this
      have hp1_deg_lt : (hp - 1).natDegree < l.length :=
        (natDegree_sub_le hp 1).trans_lt (by simpa using hhp_deg_lt)
      have hg_not_dvd_hp1 : ¬ polyOfBits g ∣ (hp - 1) := by
        intro hdvd
        have hle := Polynomial.natDegree_le_of_dvd hdvd hp1_ne
        rw [hl, natDegree_polyOfBits_append_true] at hle
        omega
      have hprod : polyOfBits g ∣ hp * (hp - 1) := by
        rw [show hp * (hp - 1) = hp ^ 2 - hp by ring, hh_sum, hl]
        exact hgh
      have hirr_false : ¬ Irreducible (polyOfBits g) := fun hirr => by
        rcases (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr).dvd_or_dvd hprod with
            h1 | h2
        · exact hg_not_dvd_hp h1
        · exact hg_not_dvd_hp1 h2
      have hf_not_unit : ¬ IsUnit (polyOfBits f) := fun hunit => by
        have hcop : IsCoprime (polyOfBits g) hp := by
          rw [← EuclideanDomain.gcd_isUnit_iff]
          exact isUnit_of_dvd_unit
            (dvd_polyOfBits_polyGcd (EuclideanDomain.gcd_dvd_left _ _)
              (EuclideanDomain.gcd_dvd_right _ _)) hunit
        exact hg_not_dvd_hp1 (hcop.dvd_of_dvd_mul_left hprod)
      have hf_deg_pos : 0 < (polyOfBits f).natDegree :=
        natDegree_pos_of_ne_zero_of_not_isUnit hf_ne hf_not_unit
      have hf_deg_lt : (polyOfBits f).natDegree < (polyOfBits g).natDegree := by
        have hle1 : (polyOfBits f).natDegree ≤ hp.natDegree :=
          Polynomial.natDegree_le_of_dvd (polyOfBits_polyGcd_dvd_right _ _) hhp_ne
        rw [hl, natDegree_polyOfBits_append_true]
        omega
      have hf_len_lt : f.length < g.length := by
        have hf_nil : f ≠ [] := by
          intro hnil
          rw [hnil, polyOfBits_nil] at hf_ne
          exact hf_ne rfl
        have hf_deg : (polyOfBits f).natDegree = f.length - 1 :=
          natDegree_polyOfBits_of_polyTrim (polyTrim_polyGcd _ _) hf_nil
        have hg_deg : (polyOfBits g).natDegree = g.length - 1 :=
          natDegree_polyOfBits_of_polyTrim hgt hg_ne
        have := List.length_pos_of_ne_nil hf_nil
        omega
      refine ⟨polyTrim_polyGcd _ _, hfsq, hf_deg_pos, hfdvd, fun hirr => absurd hirr hirr_false,
        fun _ => hf_len_lt⟩
    · have hv_false : vbits.any id = false := Bool.eq_false_of_not_eq_true hv
      rw [ite_eq_right hv]
      have hirr : Irreducible (polyOfBits g) := by
        by_contra hnirr
        obtain ⟨v, hv_ne, hmul⟩ := exists_berlekamp_ker_of_not_irreducible hl2
          (by rw [← hl]; exact hsq) (by rw [← hl]; exact hnirr)
        have hex : ∃ w : Fin (l.length - 1) → ZMod 2,
            w ≠ 0 ∧ rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix g) *ᵥ w = 0 :=
          ⟨v, hv_ne, by rw [hl]; exact hmul⟩
        have hany := kernelVecBits_any_of_exists (berlekampMatrix g) hM_len' hM_mem' hex
        rw [← hgt_len] at hany
        change vbits.any id = true at hany
        rw [hv_false] at hany
        exact Bool.false_ne_true hany
      exact ⟨hgt, hsq, hdeg, dvd_rfl, fun _ => rfl, fun hnirr => absurd hirr hnirr⟩

/-- For any squarefree binary polynomial `g` of positive degree, `berlekampIrreducibleFactor g`
produces a trimmed bit list whose polynomial divides `polyOfBits g`. -/
theorem polyTrim_berlekampIrreducibleFactor (g : List Bool) :
    polyTrim (berlekampIrreducibleFactor g) = berlekampIrreducibleFactor g := by
  unfold berlekampIrreducibleFactor
  cases h : g.length with
  | zero =>
    rw [Function.iterate_zero, id_eq]
    exact polyTrim_polyTrim g
  | succ k =>
    rw [Function.iterate_succ_apply']
    dsimp only [berlekampStep]
    split_ifs
    · exact polyTrim_polyTrim _
    · exact polyTrim_polyGcd _ _
    · exact polyTrim_polyTrim _

/-- `berlekampIrreducibleFactor g` produces a divisor of `polyOfBits g`. -/
theorem polyOfBits_berlekampIrreducibleFactor_dvd {g : List Bool}
    (hsq : Squarefree (polyOfBits g)) (hdeg : 0 < (polyOfBits g).natDegree) :
    polyOfBits (berlekampIrreducibleFactor g) ∣ polyOfBits g ∧
      Irreducible (polyOfBits (berlekampIrreducibleFactor g)) ∧
      0 < (polyOfBits (berlekampIrreducibleFactor g)).natDegree := by
  have hgt : ∀ k : ℕ,
      let f := (berlekampStep)^[k] (polyTrim g)
      polyTrim f = f ∧ Squarefree (polyOfBits f) ∧ 0 < (polyOfBits f).natDegree ∧
        polyOfBits f ∣ polyOfBits g ∧
        (¬ Irreducible (polyOfBits f) → f.length + k ≤ (polyTrim g).length) := by
    intro k
    induction k with
    | zero =>
      simp [polyTrim_polyTrim, hsq, hdeg]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨ht, hsqk, hdegk, hdvd, hdec⟩ := ih
      obtain ⟨ht', hsq', hdeg', hdvd', hstay, hshrink⟩ :=
        berlekampStep_invariant _ ht hsqk hdegk
      refine ⟨ht', hsq', hdeg', hdvd'.trans hdvd, ?_⟩
      intro hnirr'
      have hnirr : ¬ Irreducible (polyOfBits ((berlekampStep)^[k] (polyTrim g))) := by
        intro hirr
        rw [hstay hirr] at hnirr'
        exact hnirr' hirr
      have := hdec hnirr
      have := hshrink hnirr
      omega
  obtain ⟨ht, -, hdeg', hdvd, hdec⟩ := hgt g.length
  refine ⟨hdvd, ?_, hdeg'⟩
  by_contra hnirr
  have hle := hdec hnirr
  have hlen_trim := length_polyTrim_le g
  have hf_ne : (berlekampStep)^[g.length] (polyTrim g) ≠ [] := by
    intro hnil
    rw [hnil, polyOfBits_nil, natDegree_zero] at hdeg'
    omega
  have := List.length_pos_of_ne_nil hf_ne
  omega

/-- For squarefree `g` of positive degree, `berlekampIrreducibleFactor g` is irreducible. -/
theorem irreducible_polyOfBits_berlekampIrreducibleFactor {g : List Bool}
    (hsq : Squarefree (polyOfBits g)) (hdeg : 0 < (polyOfBits g).natDegree) :
    Irreducible (polyOfBits (berlekampIrreducibleFactor g)) :=
  (polyOfBits_berlekampIrreducibleFactor_dvd hsq hdeg).2.1

end Cslib.AffineDisperser.Li
