/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Polynomial.CoeffList.Arith
public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# Computable Euclidean division and GCD on polynomial coefficient lists over a field

Over a field `K` with decidable equality, this module defines computable polynomial long division
(`Polynomial.CoeffList.divMod`, `div`, `mod`) and Euclidean greatest common divisor
(`Polynomial.CoeffList.gcd`) on little-endian coefficient lists (`List K`), and proves exact
correspondence with Euclidean division and GCD in `K[X]`.

Division by an empty or all-zero divisor list returns `([], trim a)`, matching `p / 0 = 0` and
`p % 0 = p` in `K[X]`, so `ofCoeffList_div`, `ofCoeffList_mod`, `mod_eq_nil_iff_dvd`, and
`ofCoeffList_gcd` hold unconditionally for all `a b : List K`.

## Main definitions

* `Polynomial.CoeffList.divModStep`, `Polynomial.CoeffList.divMod`: iterative long division on
  coefficient lists over `K`.
* `Polynomial.CoeffList.div`, `Polynomial.CoeffList.mod`, `Polynomial.CoeffList.negMod`: Euclidean
  quotient, remainder, and negated remainder lists.
* `Polynomial.CoeffList.gcdStep`, `Polynomial.CoeffList.gcd`: iterative Euclidean GCD on
  coefficient lists over `K`.

## Main results

* `Polynomial.CoeffList.ofCoeffList_div`, `Polynomial.CoeffList.ofCoeffList_mod`,
  `Polynomial.CoeffList.ofCoeffList_negMod`, `Polynomial.CoeffList.eq_divMod_of_isTrimmed`: `div`,
  `mod`, and `negMod` compute `/`, `%`, and `-(·) % ·` in `K[X]`, with canonical trimmed uniqueness.
* `Polynomial.CoeffList.length_mod_lt`: `(mod a b).length < (trim b).length` when
  `ofCoeffList b ≠ 0`.
* `Polynomial.CoeffList.mod_eq_nil_iff_dvd`: `mod a b = [] ↔ ofCoeffList b ∣ ofCoeffList a`.
* `Polynomial.CoeffList.ofCoeffList_gcd`, `Polynomial.CoeffList.ofCoeffList_gcd_dvd_left`,
  `Polynomial.CoeffList.ofCoeffList_gcd_dvd_right`, `Polynomial.CoeffList.dvd_ofCoeffList_gcd`:
  `gcd` computes `EuclideanDomain.gcd` in `K[X]` and satisfies the universal GCD divisibility laws.
-/

public section

namespace Polynomial.CoeffList

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-! ### Euclidean long division -/

/-- One step of polynomial long division of `(quotient, remainder)` by `b`. -/
@[expose] def divModStep (b : List K) (st : List K × List K) : List K × List K :=
  let r := trim st.2
  if r.length < b.length || b.isEmpty then (trim st.1, r)
  else
    let d := r.length - b.length
    let c := r.getLastD 0 / b.getLastD 0
    (add st.1 (shift d [c]), sub r (smul c (shift d b)))

/-- Computable Euclidean `(quotient, remainder)` of `a` divided by `b` in `K[X]`. -/
@[expose] def divMod (a b : List K) : List K × List K :=
  (divModStep (trim b))^[a.length] ([], trim a)

/-- Computable Euclidean quotient of `a` divided by `b` in `K[X]`, as a trimmed list. -/
@[expose] def div (a b : List K) : List K :=
  (divMod a b).1

/-- Computable Euclidean remainder of `a` modulo `b` in `K[X]`, as a trimmed list. -/
@[expose] def mod (a b : List K) : List K :=
  (divMod a b).2

/-- Length preservation across one step of `divModStep`. -/
theorem length_divModStep_le (b q r : List K) {n : ℕ} (hq : q.length ≤ n) (hr : r.length ≤ n) :
    (divModStep b (q, r)).1.length ≤ n ∧ (divModStep b (q, r)).2.length ≤ n := by
  unfold divModStep; dsimp only
  have hr' : (trim r).length ≤ n := (length_trim_le r).trans hr
  split_ifs with h
  · exact ⟨(length_trim_le q).trans hq, hr'⟩
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt,
      List.isEmpty_eq_false_iff] at h
    have hb_pos := List.length_pos_of_ne_nil h.2
    exact ⟨(length_add_le _ _).trans (max_le hq ((length_shift_le _ _).trans (by simp; omega))),
      (length_sub_le _ _).trans (max_le hr'
        ((length_smul_le _ _).trans ((length_shift_le _ _).trans (by omega))))⟩

/-- Length and trimming invariants along iterations of `divModStep`. -/
theorem divMod_iterate_bounds (a b : List K) (k : ℕ) :
    let st := (divModStep b)^[k] ([], trim a)
    st.1.length ≤ a.length ∧ st.2.length ≤ a.length ∧ IsTrimmed st.1 ∧ IsTrimmed st.2 := by
  induction k with
  | zero => exact ⟨by simp, length_trim_le a, isTrimmed_nil, isTrimmed_trim a⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hlen := length_divModStep_le b _ _ ih.1 ih.2.1
    refine ⟨hlen.1, hlen.2, ?_⟩
    dsimp only [divModStep]
    split_ifs <;> [exact ⟨isTrimmed_trim _, isTrimmed_trim _⟩;
      exact ⟨isTrimmed_add _ _, isTrimmed_sub _ _⟩]

/-- Subtracting the leading-term multiple `smul (r.getLastD 0 / b.getLastD 0) (shift d b)` from a
trimmed dividend `r` (`b.length ≤ r.length`) strictly reduces the trimmed list length. -/
theorem length_sub_smul_shift_lt {r b : List K} (hr_trim : IsTrimmed r) (hb_trim : IsTrimmed b)
    (hbne : b ≠ []) (hle : b.length ≤ r.length) :
    (sub r (smul (r.getLastD 0 / b.getLastD 0) (shift (r.length - b.length) b))).length <
      r.length := by
  set d := r.length - b.length
  set c := r.getLastD 0 / b.getLastD 0
  have hb_pos := List.length_pos_of_ne_nil hbne
  have hr_ne : r ≠ [] := fun hnil => by simp only [hnil, List.length_nil] at hle; omega
  have hlc_b_ne : b.getLastD 0 ≠ 0 := hb_trim.leadingCoeff_ofCoeffList ▸
    leadingCoeff_ne_zero.mpr (hb_trim.ofCoeffList_ne_zero hbne)
  have hcoeff_zero : ∀ k ≥ r.length - 1,
      (ofCoeffList (sub r (smul c (shift d b)))).coeff k = 0 := fun k hk => by
    rw [ofCoeffList_sub, ofCoeffList_smul, ofCoeffList_shift, coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le hk with rfl | hgt
    · have hd : r.length - 1 - d = b.length - 1 := by omega
      rw [coeff_X_pow_mul', ite_eq_left (by omega), hd,
        ← hr_trim.natDegree_ofCoeffList hr_ne, ← hb_trim.natDegree_ofCoeffList hbne]
      change (ofCoeffList r).leadingCoeff - c * (ofCoeffList b).leadingCoeff = 0
      rw [hr_trim.leadingCoeff_ofCoeffList, hb_trim.leadingCoeff_ofCoeffList,
        div_mul_cancel₀ _ hlc_b_ne, sub_self]
    · rw [coeff_ofCoeffList, List.getD_eq_default _ _ (by omega), coeff_X_pow_mul',
        ite_eq_left (by omega), coeff_ofCoeffList, List.getD_eq_default _ _ (by omega),
        mul_zero, sub_self]
  exact Nat.lt_of_le_of_lt
    (by simpa only [trim_sub] using length_trim_le_of_coeff_eq_zero hcoeff_zero)
    (Nat.sub_lt (List.length_pos_of_ne_nil hr_ne) Nat.one_pos)

private theorem divModStep_spec {a b : List K} (hb_trim : IsTrimmed b)
    (st : List K × List K)
    (hinv : ofCoeffList st.1 * ofCoeffList b + ofCoeffList st.2 = ofCoeffList a)
    (hr_trim : IsTrimmed st.2) :
    let st' := divModStep b st
    ofCoeffList st'.1 * ofCoeffList b + ofCoeffList st'.2 = ofCoeffList a ∧
      IsTrimmed st'.1 ∧ IsTrimmed st'.2 ∧
      (st.2.length < b.length ∨ b = [] → st'.2 = st.2) ∧
      (b.length ≤ st.2.length → b ≠ [] → st'.2.length < st.2.length) := by
  dsimp only [divModStep]; rw [hr_trim.trim_eq]
  split_ifs with h
  · simp only [Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
    exact ⟨by simpa only [ofCoeffList_trim] using hinv, isTrimmed_trim _, hr_trim, fun _ => rfl,
      fun hle hbne => by rcases h with hlt | rfl <;> [omega; exact absurd rfl hbne]⟩
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt,
      List.isEmpty_eq_false_iff] at h
    rcases h with ⟨hle, hbne⟩
    set d := st.2.length - b.length
    set c := st.2.getLastD 0 / b.getLastD 0
    have heq_alg :
        ofCoeffList (add st.1 (shift d [c])) * ofCoeffList b +
          ofCoeffList (sub st.2 (smul c (shift d b))) = ofCoeffList a := by
      rw [ofCoeffList_add, ofCoeffList_sub, ofCoeffList_smul, ofCoeffList_shift, ofCoeffList_shift,
        ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero, ← hinv]
      ring
    exact ⟨heq_alg, isTrimmed_add _ _, isTrimmed_sub _ _,
      fun hstop => hstop.elim (by omega) (absurd · hbne),
      fun _ _ => length_sub_smul_shift_lt hr_trim hb_trim hbne hle⟩

/-- `div a b` is trimmed. -/
theorem isTrimmed_div (a b : List K) : IsTrimmed (div a b) :=
  (divMod_iterate_bounds a (trim b) a.length).2.2.1

/-- `mod a b` is trimmed. -/
theorem isTrimmed_mod (a b : List K) : IsTrimmed (mod a b) :=
  (divMod_iterate_bounds a (trim b) a.length).2.2.2

/-- `trim` is the identity on `div a b`. -/
@[simp] theorem trim_div (a b : List K) : trim (div a b) = div a b :=
  (isTrimmed_div a b).trim_eq

/-- `trim` is the identity on `mod a b`. -/
@[simp] theorem trim_mod (a b : List K) : trim (mod a b) = mod a b :=
  (isTrimmed_mod a b).trim_eq

/-- `(div a b).length ≤ a.length`. -/
theorem length_div_le (a b : List K) : (div a b).length ≤ a.length :=
  (divMod_iterate_bounds a (trim b) a.length).1

/-- `(mod a b).length ≤ a.length`. -/
theorem length_mod_le (a b : List K) : (mod a b).length ≤ a.length :=
  (divMod_iterate_bounds a (trim b) a.length).2.1

/-- Division identity
`ofCoeffList (div a b) * ofCoeffList b + ofCoeffList (mod a b) = ofCoeffList a`
for all `a b : List K`. -/
theorem ofCoeffList_div_mul_add_mod (a b : List K) :
    ofCoeffList (div a b) * ofCoeffList b + ofCoeffList (mod a b) = ofCoeffList a := by
  have hiter (k : ℕ) : let st := (divModStep (trim b))^[k] ([], trim a)
      ofCoeffList st.1 * ofCoeffList (trim b) + ofCoeffList st.2 = ofCoeffList a ∧
        IsTrimmed st.2 := by
    induction k with
    | zero => simp [isTrimmed_trim]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hinv, _, h2, -⟩ := divModStep_spec (isTrimmed_trim b) _ ih.1 ih.2
      exact ⟨hinv, h2⟩
  simpa only [div, mod, divMod, ofCoeffList_trim] using (hiter a.length).1

/-- When `ofCoeffList b ≠ 0`, the remainder list `mod a b` is strictly shorter than `trim b`. -/
theorem length_mod_lt {a b : List K} (hb : ofCoeffList b ≠ 0) :
    (mod a b).length < (trim b).length := by
  set bt := trim b
  have hbt_ne : bt ≠ [] := fun hnil => hb ((trim_eq_nil_iff b).mp hnil)
  have hbt_pos := List.length_pos_of_ne_nil hbt_ne
  have hbt_tr : IsTrimmed bt := isTrimmed_trim b
  have hiter (k : ℕ) : let st := (divModStep bt)^[k] ([], trim a)
      ofCoeffList st.1 * ofCoeffList bt + ofCoeffList st.2 = ofCoeffList a ∧
        IsTrimmed st.2 ∧ st.2.length ≤ max (bt.length - 1) (a.length - k) := by
    induction k with
    | zero =>
      simpa only [Function.iterate_zero, id_eq, ofCoeffList_nil, zero_mul, ofCoeffList_trim,
        zero_add, isTrimmed_trim, Nat.sub_zero, true_and] using
        (length_trim_le a).trans (le_max_right _ _)
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hinv', _, h2', hstay, hdrop⟩ := divModStep_spec hbt_tr _ ih.1 ih.2.1
      refine ⟨hinv', h2', ?_⟩
      have hih := ih.2.2
      by_cases hlt : ((divModStep bt)^[k] ([], trim a)).2.length < bt.length
      · rw [hstay (Or.inl hlt)]; omega
      · have := hdrop (by omega) hbt_ne
        omega
  exact (hiter a.length).2.2.trans_lt (by omega)

private theorem divMod_eq_zero_divisor {a b : List K} (hb : ofCoeffList b = 0) :
    div a b = [] ∧ mod a b = trim a := by
  suffices ∀ k, (divModStep ([] : List K))^[k] ([], trim a) = ([], trim a) by
    simp [div, mod, divMod, (trim_eq_nil_iff b).mpr hb, this a.length]
  exact fun k => Nat.rec rfl (fun _ ih => by simp [Function.iterate_succ_apply', ih, divModStep]) k

private theorem ofCoeffList_eq_div_and_mod_of_lt {a b q r : List K} (hb : ofCoeffList b ≠ 0)
    (hr : IsTrimmed r) (hr_lt : r.length < (trim b).length)
    (heq1 : ofCoeffList q * ofCoeffList b + ofCoeffList r = ofCoeffList a) :
    ofCoeffList q = ofCoeffList a / ofCoeffList b ∧
      ofCoeffList r = ofCoeffList a % ofCoeffList b := by
  have hdeg_r : (ofCoeffList r).degree < (ofCoeffList b).degree := by
    rw [← ofCoeffList_trim b]
    exact hr.degree_lt_of_length_lt (isTrimmed_trim b)
      (fun hnil => hb ((trim_eq_nil_iff b).mp hnil)) hr_lt
  have hdiff : ofCoeffList b * (ofCoeffList q - ofCoeffList a / ofCoeffList b) =
      ofCoeffList a % ofCoeffList b - ofCoeffList r := by
    have h12 := heq1.trans (EuclideanDomain.div_add_mod (ofCoeffList a) (ofCoeffList b)).symm
    refine eq_sub_of_add_eq (calc
      ofCoeffList b * (ofCoeffList q - ofCoeffList a / ofCoeffList b) + ofCoeffList r
        = (ofCoeffList q * ofCoeffList b + ofCoeffList r) -
            ofCoeffList b * (ofCoeffList a / ofCoeffList b) := by ring
      _ = ofCoeffList a % ofCoeffList b := by rw [h12]; ring)
  have hq_eq : ofCoeffList q = ofCoeffList a / ofCoeffList b := by
    by_contra hne
    have hle := hdiff ▸ degree_le_mul_left (ofCoeffList b) (sub_ne_zero.mpr hne)
    exact not_lt_of_ge hle ((degree_sub_le _ _).trans_lt
      (max_lt (EuclideanDomain.mod_lt _ hb) hdeg_r))
  exact ⟨hq_eq, (sub_eq_zero.mp (by simpa only [hq_eq, sub_self, mul_zero] using hdiff.symm)).symm⟩

private theorem ofCoeffList_div_and_mod (a b : List K) :
    ofCoeffList (div a b) = ofCoeffList a / ofCoeffList b ∧
      ofCoeffList (mod a b) = ofCoeffList a % ofCoeffList b := by
  by_cases hb : ofCoeffList b = 0
  · obtain ⟨hq, hr⟩ := divMod_eq_zero_divisor (a := a) hb
    simp [hq, hr, hb]
  · exact ofCoeffList_eq_div_and_mod_of_lt hb (isTrimmed_mod a b) (length_mod_lt hb)
      (ofCoeffList_div_mul_add_mod a b)

/-- `div a b` represents Euclidean quotient `ofCoeffList a / ofCoeffList b` in `K[X]`. -/
@[simp] theorem ofCoeffList_div (a b : List K) :
    ofCoeffList (div a b) = ofCoeffList a / ofCoeffList b :=
  (ofCoeffList_div_and_mod a b).1

/-- `mod a b` represents Euclidean remainder `ofCoeffList a % ofCoeffList b` in `K[X]`. -/
@[simp] theorem ofCoeffList_mod (a b : List K) :
    ofCoeffList (mod a b) = ofCoeffList a % ofCoeffList b :=
  (ofCoeffList_div_and_mod a b).2

/-- Uniqueness of Euclidean division on trimmed coefficient lists when `ofCoeffList b ≠ 0`:
any pair of trimmed lists `(q, r)` with `r.length < (trim b).length` and
`ofCoeffList q * ofCoeffList b + ofCoeffList r = ofCoeffList a` equals `divMod a b`. -/
theorem eq_divMod_of_isTrimmed {a b q r : List K} (hb : ofCoeffList b ≠ 0)
    (hq : IsTrimmed q) (hr : IsTrimmed r) (hr_lt : r.length < (trim b).length)
    (heq : ofCoeffList q * ofCoeffList b + ofCoeffList r = ofCoeffList a) :
    (q, r) = divMod a b := by
  obtain ⟨hq_eq, hr_eq⟩ := ofCoeffList_eq_div_and_mod_of_lt hb hr hr_lt heq
  exact Prod.ext
    (hq.eq_of_ofCoeffList_eq (isTrimmed_div a b) (hq_eq.trans (ofCoeffList_div a b).symm))
    (hr.eq_of_ofCoeffList_eq (isTrimmed_mod a b) (hr_eq.trans (ofCoeffList_mod a b).symm))

/-- `mod a b = []` if and only if `ofCoeffList b` divides `ofCoeffList a` in `K[X]`. -/
@[simp] theorem mod_eq_nil_iff_dvd (a b : List K) :
    mod a b = [] ↔ ofCoeffList b ∣ ofCoeffList a := by
  rw [(isTrimmed_mod a b).eq_nil_iff, ofCoeffList_mod, EuclideanDomain.mod_eq_zero]

/-- Computable negated Euclidean remainder `-(ofCoeffList a) % ofCoeffList b` in `K[X]`, as a
trimmed list. -/
@[expose] def negMod (a b : List K) : List K :=
  mod (neg a) b

/-- `negMod a b` is trimmed. -/
theorem isTrimmed_negMod (a b : List K) : IsTrimmed (negMod a b) :=
  isTrimmed_mod _ _

/-- `(negMod a b).length ≤ a.length`. -/
theorem length_negMod_le (a b : List K) : (negMod a b).length ≤ a.length :=
  (length_mod_le _ _).trans (length_neg_le a)

/-- When `ofCoeffList b ≠ 0`, `negMod a b` is strictly shorter than `trim b`. -/
theorem length_negMod_lt {a b : List K} (hb : ofCoeffList b ≠ 0) :
    (negMod a b).length < (trim b).length :=
  length_mod_lt hb

/-- `negMod a b` represents `-(ofCoeffList a) % ofCoeffList b` in `K[X]`. -/
@[simp] theorem ofCoeffList_negMod (a b : List K) :
    ofCoeffList (negMod a b) = -ofCoeffList a % ofCoeffList b := by
  rw [negMod, ofCoeffList_mod, ofCoeffList_neg]

/-! ### Euclidean greatest common divisor -/

/-- One step of the Euclidean algorithm on `(x, y)`. -/
@[expose] def gcdStep (st : List K × List K) : List K × List K :=
  if st.2.isEmpty then st else (st.2, mod st.1 st.2)

/-- Computable Euclidean GCD of two polynomial coefficient lists over `K`, as a trimmed list. -/
@[expose] def gcd (a b : List K) : List K :=
  ((gcdStep)^[a.length + b.length + 1] (trim a, trim b)).1

/-- Length bounds preserved along iterations of `gcdStep`. -/
theorem gcd_iterate_bounds (a b : List K) (k : ℕ) :
    let st := (gcdStep)^[k] (trim a, trim b)
    st.1.length ≤ max a.length b.length ∧ st.2.length ≤ max a.length b.length := by
  induction k with
  | zero =>
    exact ⟨(length_trim_le a).trans (le_max_left _ _),
      (length_trim_le b).trans (le_max_right _ _)⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    dsimp only [gcdStep]
    split_ifs
    · exact ih
    · exact ⟨ih.2, (length_mod_le _ _).trans ih.1⟩

private theorem gcdStep_iterate_spec :
    ∀ (k : ℕ) (x y : List K), IsTrimmed x → IsTrimmed y → y.length ≤ k →
      let st := (gcdStep)^[k] (x, y)
      IsTrimmed st.1 ∧ st.2 = [] ∧
        ofCoeffList st.1 = EuclideanDomain.gcd (ofCoeffList y) (ofCoeffList x)
  | 0, x, y, hx, _, hlen => by
    rcases List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen) with rfl
    simp [hx]
  | k + 1, x, y, hx, hy, hlen => by
    rw [Function.iterate_succ_apply]
    dsimp only [gcdStep]
    split_ifs with h
    · rcases List.isEmpty_iff.mp h with rfl
      exact gcdStep_iterate_spec k x [] hx isTrimmed_nil (Nat.zero_le k)
    · have hlt : (mod x y).length < y.length := by
        simpa only [hy.trim_eq] using
          length_mod_lt (a := x) (hy.ofCoeffList_ne_zero fun hy0 => h (List.isEmpty_iff.mpr hy0))
      obtain ⟨ht, hnil, hgcd⟩ :=
        gcdStep_iterate_spec k y (mod x y) hy (isTrimmed_mod x y) (by omega)
      exact ⟨ht, hnil, by rw [hgcd, ofCoeffList_mod, ← EuclideanDomain.gcd_val]⟩

/-- `gcd a b` is trimmed. -/
theorem isTrimmed_gcd (a b : List K) : IsTrimmed (gcd a b) :=
  (gcdStep_iterate_spec (a.length + b.length + 1) (trim a) (trim b)
    (isTrimmed_trim a) (isTrimmed_trim b) (by have := length_trim_le b; omega)).1

/-- `trim` is the identity on `gcd a b`. -/
@[simp] theorem trim_gcd (a b : List K) : trim (gcd a b) = gcd a b :=
  (isTrimmed_gcd a b).trim_eq

/-- `(gcd a b).length ≤ max a.length b.length`. -/
theorem length_gcd_le (a b : List K) : (gcd a b).length ≤ max a.length b.length :=
  (gcd_iterate_bounds a b (a.length + b.length + 1)).1

/-- `gcd a b` computes `EuclideanDomain.gcd (ofCoeffList b) (ofCoeffList a)` in `K[X]`. -/
@[simp] theorem ofCoeffList_gcd (a b : List K) :
    ofCoeffList (gcd a b) = EuclideanDomain.gcd (ofCoeffList b) (ofCoeffList a) := by
  simpa only [gcd, ofCoeffList_trim] using (gcdStep_iterate_spec (a.length + b.length + 1)
    (trim a) (trim b) (isTrimmed_trim a) (isTrimmed_trim b)
    ((length_trim_le b).trans (by omega))).2.2

/-- `ofCoeffList (gcd a b)` divides `ofCoeffList a`. -/
theorem ofCoeffList_gcd_dvd_left (a b : List K) :
    ofCoeffList (gcd a b) ∣ ofCoeffList a :=
  ofCoeffList_gcd a b ▸ EuclideanDomain.gcd_dvd_right _ _

/-- `ofCoeffList (gcd a b)` divides `ofCoeffList b`. -/
theorem ofCoeffList_gcd_dvd_right (a b : List K) :
    ofCoeffList (gcd a b) ∣ ofCoeffList b :=
  ofCoeffList_gcd a b ▸ EuclideanDomain.gcd_dvd_left _ _

/-- Every common divisor of `ofCoeffList a` and `ofCoeffList b` divides `ofCoeffList (gcd a b)`. -/
theorem dvd_ofCoeffList_gcd {a b : List K} {u : K[X]}
    (ha : u ∣ ofCoeffList a) (hb : u ∣ ofCoeffList b) :
    u ∣ ofCoeffList (gcd a b) :=
  ofCoeffList_gcd a b ▸ EuclideanDomain.dvd_gcd hb ha

/-- `ofCoeffList (gcd a b) ≠ 0` whenever either input represents a nonzero polynomial. -/
theorem ofCoeffList_gcd_ne_zero {a b : List K} (h : ofCoeffList a ≠ 0 ∨ ofCoeffList b ≠ 0) :
    ofCoeffList (gcd a b) ≠ 0 := by
  rw [ofCoeffList_gcd, ne_eq, EuclideanDomain.gcd_eq_zero_iff]
  exact h.elim (fun ha ⟨_, ha0⟩ => ha ha0) (fun hb ⟨hb0, _⟩ => hb hb0)

end Polynomial.CoeffList
