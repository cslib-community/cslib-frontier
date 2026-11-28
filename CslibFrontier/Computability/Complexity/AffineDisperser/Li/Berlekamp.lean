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
public import CslibFrontier.Foundations.Data.Polynomial.CoeffList.DivMod
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
  | add _ _ ih1 ih2 => rw [add_comp, coeff_add, coeff_add, ih1, ih2]; split_ifs <;> simp
  | monomial n a =>
    rw [monomial_comp, coeff_C_mul, ← pow_mul, coeff_X_pow, coeff_monomial]
    by_cases hdiv : q ∣ k
    · obtain ⟨m, rfl⟩ := hdiv
      rw [ite_eq_left (dvd_mul_right q m), Nat.mul_div_right m hq]
      by_cases hnm : n = m <;> simp [hnm, hq.ne', eq_comm]
    · have hne : k ≠ q * n := fun heq => hdiv ⟨n, heq⟩
      simp [hdiv, hne]

/-! ### Coefficient extraction and trimmed polynomial lists -/

/-- `polyOfBits` agrees with `Polynomial.ofCoeffList` under `bitEquiv.symm : Bool → ZMod 2`. -/
theorem polyOfBits_eq_ofCoeffList (l : List Bool) :
    polyOfBits l = ofCoeffList (l.map bitEquiv.symm) := by
  induction l with
  | nil => simp
  | cons b l ih => rw [polyOfBits_cons, List.map_cons, ofCoeffList_cons, ih]

@[simp]
private theorem bitEquiv_symm_comp_bitEquiv : ⇑bitEquiv.symm ∘ ⇑bitEquiv = id :=
  funext bitEquiv.symm_apply_apply

@[simp]
private theorem bitEquiv_comp_bitEquiv_symm : ⇑bitEquiv ∘ ⇑bitEquiv.symm = id :=
  funext bitEquiv.apply_symm_apply

private theorem map_bitEquiv_map_bitEquiv_symm (l : List Bool) :
    (l.map bitEquiv.symm).map bitEquiv = l := by
  simp

@[simp]
private theorem polyOfBits_map_bitEquiv (l : List (ZMod 2)) :
    polyOfBits (l.map bitEquiv) = ofCoeffList l := by
  simp [polyOfBits_eq_ofCoeffList]

/-- The `i`-th coefficient of `polyOfBits l` is `l.getD i false`. -/
theorem coeff_polyOfBits (l : List Bool) (i : ℕ) :
    (polyOfBits l).coeff i = bitEquiv.symm (l.getD i false) := by
  rw [polyOfBits_eq_ofCoeffList, coeff_ofCoeffList]
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]
  · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ hi,
      bitEquiv_symm_false]

/-- Strip trailing `false` entries from a bit-coefficient list. -/
@[expose] def polyTrim (p : List Bool) : List Bool :=
  p.foldr (fun b acc => if b || !acc.isEmpty then b :: acc else []) []

/-- `polyTrim` coincides with `Polynomial.CoeffList.trim` transported along `bitEquiv`. -/
theorem polyTrim_eq_coeffList (p : List Bool) :
    polyTrim p = (CoeffList.trim (p.map bitEquiv.symm)).map bitEquiv := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    change (if b || !(polyTrim p).isEmpty then b :: polyTrim p else []) = _
    simp only [List.map_cons, CoeffList.trim_cons, ih, List.isEmpty_map]
    cases b <;> cases (CoeffList.trim (p.map bitEquiv.symm)).isEmpty <;>
      simp [bitEquiv_symm_false, bitEquiv_symm_true, Bool.zero_eq_false, Bool.one_eq_true]

@[simp]
private theorem map_bitEquiv_symm_polyTrim (p : List Bool) :
    (polyTrim p).map bitEquiv.symm = CoeffList.trim (p.map bitEquiv.symm) := by
  simp [polyTrim_eq_coeffList]

private theorem isTrimmed_of_polyTrim_eq {p : List Bool} (hp : polyTrim p = p) :
    CoeffList.IsTrimmed (p.map bitEquiv.symm) := by
  rw [← CoeffList.trim_eq_self_iff, ← map_bitEquiv_symm_polyTrim, hp]

/-- Trimming preserves a list ending in `true`. -/
theorem polyTrim_append_true (l : List Bool) : polyTrim (l ++ [true]) = l ++ [true] := by
  simp [polyTrim_eq_coeffList, CoeffList.trim_append_singleton, Bool.one_eq_true]

/-- Appending a trailing `false` does not change `polyTrim`. -/
@[simp]
theorem polyTrim_append_false (l : List Bool) : polyTrim (l ++ [false]) = polyTrim l := by
  simp [polyTrim_eq_coeffList]

/-- Every trimmed coefficient list is either empty or ends in `true`. -/
theorem polyTrim_eq_nil_or_append_true (p : List Bool) :
    polyTrim p = [] ∨ ∃ l, polyTrim p = l ++ [true] := by
  rcases eq_or_ne (CoeffList.trim (p.map bitEquiv.symm)) [] with hnil | hne
  · exact Or.inl (by simp [polyTrim_eq_coeffList, hnil])
  · obtain ⟨l, a, ha, heq⟩ :=
      (CoeffList.isTrimmed_trim (p.map bitEquiv.symm)).exists_append_singleton hne
    have ha1 : bitEquiv a = true := (by decide : ∀ x : ZMod 2, x ≠ 0 → bitEquiv x = true) a ha
    exact Or.inr ⟨l.map bitEquiv, by simp [polyTrim_eq_coeffList, heq, ha1]⟩

/-- `polyTrim` is idempotent. -/
@[simp]
theorem polyTrim_polyTrim (p : List Bool) : polyTrim (polyTrim p) = polyTrim p := by
  simp [polyTrim_eq_coeffList]

/-- Trimming never increases list length. -/
theorem length_polyTrim_le (p : List Bool) : (polyTrim p).length ≤ p.length := by
  simpa [polyTrim_eq_coeffList] using CoeffList.length_trim_le (p.map bitEquiv.symm)

/-- Trimming preserves polynomial semantics. -/
@[simp]
theorem polyOfBits_polyTrim (p : List Bool) : polyOfBits (polyTrim p) = polyOfBits p := by
  simp [polyTrim_eq_coeffList, polyOfBits_eq_ofCoeffList]

/-- `polyTrim p = []` if and only if `polyOfBits p = 0`. -/
@[simp]
theorem polyTrim_eq_nil_iff (p : List Bool) : polyTrim p = [] ↔ polyOfBits p = 0 := by
  simp [polyTrim_eq_coeffList, polyOfBits_eq_ofCoeffList]

/-- Two `polyTrim`-fixed bit lists with the same `polyOfBits` are equal. -/
theorem eq_of_polyTrim_eq_of_polyOfBits_eq {p q : List Bool}
    (hp : polyTrim p = p) (hq : polyTrim q = q) (h : polyOfBits p = polyOfBits q) : p = q := by
  rw [← map_bitEquiv_map_bitEquiv_symm p, ← map_bitEquiv_map_bitEquiv_symm q]
  refine congrArg (List.map bitEquiv) ?_
  exact (isTrimmed_of_polyTrim_eq hp).eq_of_ofCoeffList_eq (isTrimmed_of_polyTrim_eq hq)
    (by simpa only [polyOfBits_eq_ofCoeffList] using h)

/-- A nonempty trimmed list has degree `p.length - 1`. -/
theorem natDegree_polyOfBits_of_polyTrim {p : List Bool} (hp : polyTrim p = p) (hne : p ≠ []) :
    (polyOfBits p).natDegree = p.length - 1 := by
  rw [polyOfBits_eq_ofCoeffList,
    (isTrimmed_of_polyTrim_eq hp).natDegree_ofCoeffList (by simpa using hne), List.length_map]

/-- `polyOfBits p ≠ 0` if and only if `polyTrim p ≠ []`. -/
theorem polyOfBits_ne_zero_iff_polyTrim {p : List Bool} : polyOfBits p ≠ 0 ↔ polyTrim p ≠ [] :=
  not_congr (polyTrim_eq_nil_iff p).symm

/-! ### Polynomial addition, multiplication, division, GCD, and `X^q`-composition -/

/-- Addition of binary polynomials over `𝔽₂`, returning a trimmed coefficient list. -/
@[expose] def polyAdd (p q : List Bool) : List Bool :=
  polyTrim ((List.range (max p.length q.length)).map fun i =>
    xor (p.getD i false) (q.getD i false))

/-- `polyAdd p q` is always trimmed. -/
@[simp]
theorem polyTrim_polyAdd (p q : List Bool) : polyTrim (polyAdd p q) = polyAdd p q :=
  polyTrim_polyTrim _

/-- `polyAdd` coincides with `Polynomial.CoeffList.add` transported along `bitEquiv`. -/
theorem polyAdd_eq_coeffList (p q : List Bool) :
    polyAdd p q = (CoeffList.add (p.map bitEquiv.symm) (q.map bitEquiv.symm)).map bitEquiv := by
  refine eq_of_polyTrim_eq_of_polyOfBits_eq (polyTrim_polyAdd p q)
    (by simp [polyTrim_eq_coeffList]) ?_
  rw [polyAdd, polyOfBits_polyTrim, polyOfBits_map_bitEquiv, CoeffList.ofCoeffList_add,
    ← polyOfBits_eq_ofCoeffList, ← polyOfBits_eq_ofCoeffList]
  ext i
  rw [coeff_polyOfBits, coeff_add, coeff_polyOfBits, coeff_polyOfBits]
  by_cases hi : i < max p.length q.length
  · rw [List.getD_map_range _ false hi, ← Bool.add_eq_xor, map_add]
  · rw [List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega),
      List.getD_eq_default p _ (by omega), List.getD_eq_default q _ (by omega)]
    simp

/-- Length bound on `polyAdd p q`. -/
theorem length_polyAdd_le (p q : List Bool) : (polyAdd p q).length ≤ max p.length q.length := by
  simpa [polyAdd_eq_coeffList] using
    CoeffList.length_add_le (p.map bitEquiv.symm) (q.map bitEquiv.symm)

/-- `polyAdd` computes addition in `𝔽₂[X]`. -/
@[simp]
theorem polyOfBits_polyAdd (p q : List Bool) :
    polyOfBits (polyAdd p q) = polyOfBits p + polyOfBits q := by
  simp [polyAdd_eq_coeffList, polyOfBits_eq_ofCoeffList]

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

/-- `polyMul` coincides with `Polynomial.CoeffList.mul` transported along `bitEquiv`. -/
theorem polyMul_eq_coeffList (p q : List Bool) :
    polyMul p q = (CoeffList.mul (p.map bitEquiv.symm) (q.map bitEquiv.symm)).map bitEquiv := by
  unfold polyMul
  split_ifs with h
  · simp only [Bool.or_eq_true, List.isEmpty_iff] at h
    rcases h with rfl | rfl <;> simp [CoeffList.mul]
  · refine eq_of_polyTrim_eq_of_polyOfBits_eq (polyTrim_polyTrim _)
      (by simp [polyTrim_eq_coeffList]) ?_
    rw [polyOfBits_polyTrim, polyOfBits_map_bitEquiv]
    ext k
    rw [coeff_polyOfBits, coeff_ofCoeffList]
    by_cases hk : k < p.length + q.length
    · rw [List.getD_map_range _ false hk, ← List.foldl_map (g := xor)
          (f := fun i => p.getD i false && q.getD (k - i) false),
        bitEquiv_symm_foldl_xor, List.map_map, Function.comp_def, List.sum_map_range_eq_sum_range,
        ← coeff_ofCoeffList, CoeffList.ofCoeffList_mul, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => (ofCoeffList (p.map bitEquiv.symm)).coeff i *
            (ofCoeffList (q.map bitEquiv.symm)).coeff j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← polyOfBits_eq_ofCoeffList, ← polyOfBits_eq_ofCoeffList, coeff_polyOfBits,
        coeff_polyOfBits, ← Bool.mul_eq_and, map_mul]
    · rw [List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega),
        bitEquiv_symm_false, List.getD_eq_default (CoeffList.mul _ _) _ (by
          have := CoeffList.length_mul_le (p.map bitEquiv.symm) (q.map bitEquiv.symm)
          simp only [List.length_map] at this; omega)]

/-- Length bound on `polyMul p q`. -/
theorem length_polyMul_le (p q : List Bool) : (polyMul p q).length ≤ p.length + q.length - 1 := by
  simpa [polyMul_eq_coeffList] using
    CoeffList.length_mul_le (p.map bitEquiv.symm) (q.map bitEquiv.symm)

/-- `polyMul` computes multiplication in `𝔽₂[X]`. -/
@[simp]
theorem polyOfBits_polyMul (p q : List Bool) :
    polyOfBits (polyMul p q) = polyOfBits p * polyOfBits q := by
  simp [polyMul_eq_coeffList, polyOfBits_eq_ofCoeffList]

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

/-- `polyDivMod` coincides with `Polynomial.CoeffList.divMod` transported along `bitEquiv`. -/
theorem polyDivMod_eq_coeffList (a b : List Bool) :
    polyDivMod a b =
      let res := CoeffList.divMod (a.map bitEquiv.symm) (b.map bitEquiv.symm)
      (res.1.map bitEquiv, res.2.map bitEquiv) := by
  have hstep : ∀ st : List (ZMod 2) × List (ZMod 2),
      let bt' := CoeffList.trim (b.map bitEquiv.symm)
      let res := CoeffList.divModStep bt' st
      polyDivModStep (bt'.map bitEquiv) (st.1.map bitEquiv, st.2.map bitEquiv) =
        (res.1.map bitEquiv, res.2.map bitEquiv) := by
    intro st bt'
    dsimp only [CoeffList.divModStep, polyDivModStep]
    have hr : polyTrim (st.2.map bitEquiv) = (CoeffList.trim st.2).map bitEquiv := by
      simp [polyTrim_eq_coeffList]
    have hq : polyTrim (st.1.map bitEquiv) = (CoeffList.trim st.1).map bitEquiv := by
      simp [polyTrim_eq_coeffList]
    rw [hr, hq]
    have hcond : ((CoeffList.trim st.2).length < bt'.length || bt'.isEmpty) =
        (((CoeffList.trim st.2).map bitEquiv).length < (bt'.map bitEquiv).length ||
          (bt'.map bitEquiv).isEmpty) := by simp
    rw [← hcond]
    split_ifs with hc
    · rfl
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt,
        List.isEmpty_eq_false_iff] at hc
      rcases hc with ⟨hle, hbne⟩
      have hb_pos := List.length_pos_of_ne_nil hbne
      have hr_ne : CoeffList.trim st.2 ≠ [] :=
        fun h0 => by simp only [h0, List.length_nil] at hle; omega
      have hlc (l : List (ZMod 2)) (hl : CoeffList.trim l ≠ []) :
          (CoeffList.trim l).getLastD 0 = 1 := by
        obtain ⟨l', x, hx, heq⟩ := (CoeffList.isTrimmed_trim _).exists_append_singleton hl
        rw [heq, List.getLastD_concat]
        exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) x hx
      rw [hlc _ hr_ne, hlc _ hbne, div_one]
      set d := (CoeffList.trim st.2).length - bt'.length
      have hd : ((CoeffList.trim st.2).map bitEquiv).length - (bt'.map bitEquiv).length = d := by
        simp [d]
      rw [hd]
      refine Prod.ext ?_ ?_
      · refine eq_of_polyTrim_eq_of_polyOfBits_eq (polyTrim_polyAdd _ _)
          (by simp [polyTrim_eq_coeffList]) ?_
        simp [polyOfBits_append, bitEquiv_symm_true, ofCoeffList_cons]
      · refine eq_of_polyTrim_eq_of_polyOfBits_eq (polyTrim_polyAdd _ _)
          (by simp [polyTrim_eq_coeffList]) ?_
        simp [polyOfBits_append, CharTwo.sub_eq_add]
  have hsemi : Function.Semiconj
      (fun st : List (ZMod 2) × List (ZMod 2) => (st.1.map bitEquiv, st.2.map bitEquiv))
      (CoeffList.divModStep (CoeffList.trim (b.map bitEquiv.symm)))
      (polyDivModStep ((CoeffList.trim (b.map bitEquiv.symm)).map bitEquiv)) :=
    fun st => (hstep st).symm
  simpa [polyDivMod, CoeffList.divMod, polyTrim_eq_coeffList] using
    (hsemi.iterate_right a.length ([], CoeffList.trim (a.map bitEquiv.symm))).symm

private theorem polyQuot_eq_coeffList (a b : List Bool) :
    polyQuot a b = (CoeffList.div (a.map bitEquiv.symm) (b.map bitEquiv.symm)).map bitEquiv :=
  congrArg Prod.fst (polyDivMod_eq_coeffList a b)

private theorem polyMod_eq_coeffList (a b : List Bool) :
    polyMod a b = (CoeffList.mod (a.map bitEquiv.symm) (b.map bitEquiv.symm)).map bitEquiv :=
  congrArg Prod.snd (polyDivMod_eq_coeffList a b)

/-- `(polyMod a b).length ≤ a.length`. -/
theorem length_polyMod_le (a b : List Bool) : (polyMod a b).length ≤ a.length := by
  simpa [polyMod_eq_coeffList] using
    CoeffList.length_mod_le (a.map bitEquiv.symm) (b.map bitEquiv.symm)

/-- Euclidean division specification for `polyQuot` and `polyMod` when `polyOfBits b ≠ 0`. -/
theorem polyOfBits_polyDivMod_spec {a b : List Bool} (hb : polyOfBits b ≠ 0) :
    polyOfBits (polyQuot a b) * polyOfBits b + polyOfBits (polyMod a b) = polyOfBits a ∧
      (polyMod a b).length < (polyTrim b).length ∧
      polyTrim (polyQuot a b) = polyQuot a b ∧
      polyTrim (polyMod a b) = polyMod a b := by
  have hb' : ofCoeffList (b.map bitEquiv.symm) ≠ 0 := by
    rwa [← polyOfBits_eq_ofCoeffList]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [polyQuot_eq_coeffList, polyMod_eq_coeffList, polyOfBits_eq_ofCoeffList]
      using CoeffList.ofCoeffList_div_mul_add_mod (a.map bitEquiv.symm) (b.map bitEquiv.symm)
  · simpa [polyMod_eq_coeffList, polyTrim_eq_coeffList] using
      CoeffList.length_mod_lt (a := a.map bitEquiv.symm) hb'
  · simp [polyQuot_eq_coeffList, polyTrim_eq_coeffList]
  · simp [polyMod_eq_coeffList, polyTrim_eq_coeffList]

/-- `polyOfBits b ∣ polyOfBits a` if and only if `polyMod a b = []`. -/
theorem polyOfBits_polyMod_dvd_iff {a b : List Bool} :
    polyOfBits b ∣ polyOfBits a ↔ polyMod a b = [] := by
  simp [polyMod_eq_coeffList, polyOfBits_eq_ofCoeffList]

/-- One step of the binary Euclidean algorithm for `polyGcd`. -/
@[expose] def polyGcdStep (st : List Bool × List Bool) : List Bool × List Bool :=
  if st.2.isEmpty then st else (st.2, polyMod st.1 st.2)

/-- Greatest common divisor of two binary polynomials over `𝔽₂`, as a trimmed list. -/
@[expose] def polyGcd (a b : List Bool) : List Bool :=
  ((polyGcdStep)^[a.length + b.length + 1] (polyTrim a, polyTrim b)).1

/-- `polyGcd` coincides with `Polynomial.CoeffList.gcd` transported along `bitEquiv`. -/
theorem polyGcd_eq_coeffList (a b : List Bool) :
    polyGcd a b = (CoeffList.gcd (a.map bitEquiv.symm) (b.map bitEquiv.symm)).map bitEquiv := by
  have hiter : ∀ (k : ℕ) (st : List (ZMod 2) × List (ZMod 2)),
      let res := (CoeffList.gcdStep)^[k] st
      (polyGcdStep)^[k] (st.1.map bitEquiv, st.2.map bitEquiv) =
        (res.1.map bitEquiv, res.2.map bitEquiv) := by
    intro k
    induction k with
    | zero => intro st; rfl
    | succ k ih =>
      intro st
      dsimp only
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      dsimp only [CoeffList.gcdStep, polyGcdStep]
      rw [List.isEmpty_map]
      split_ifs
      · exact ih st
      · simpa [polyMod_eq_coeffList] using ih (st.2, CoeffList.mod st.1 st.2)
  have h := congrArg Prod.fst
    (hiter (a.length + b.length + 1)
      (CoeffList.trim (a.map bitEquiv.symm), CoeffList.trim (b.map bitEquiv.symm)))
  simpa [polyGcd, CoeffList.gcd, polyTrim_eq_coeffList] using h

/-- `polyGcd a b` is always trimmed. -/
@[simp]
theorem polyTrim_polyGcd (a b : List Bool) : polyTrim (polyGcd a b) = polyGcd a b := by
  simp [polyTrim_eq_coeffList, polyGcd_eq_coeffList]

/-- `(polyGcd a b).length ≤ max a.length b.length`. -/
theorem length_polyGcd_le (a b : List Bool) : (polyGcd a b).length ≤ max a.length b.length := by
  simpa [polyGcd_eq_coeffList] using
    CoeffList.length_gcd_le (a.map bitEquiv.symm) (b.map bitEquiv.symm)

/-- `polyOfBits (polyGcd a b)` divides `polyOfBits a`. -/
theorem polyOfBits_polyGcd_dvd_left (a b : List Bool) :
    polyOfBits (polyGcd a b) ∣ polyOfBits a := by
  simpa [polyGcd_eq_coeffList, polyOfBits_eq_ofCoeffList] using
    CoeffList.ofCoeffList_gcd_dvd_left (a.map bitEquiv.symm) (b.map bitEquiv.symm)

/-- `polyOfBits (polyGcd a b)` divides `polyOfBits b`. -/
theorem polyOfBits_polyGcd_dvd_right (a b : List Bool) :
    polyOfBits (polyGcd a b) ∣ polyOfBits b := by
  simpa [polyGcd_eq_coeffList, polyOfBits_eq_ofCoeffList] using
    CoeffList.ofCoeffList_gcd_dvd_right (a.map bitEquiv.symm) (b.map bitEquiv.symm)

/-- Common divisors of `polyOfBits a` and `polyOfBits b` divide `polyOfBits (polyGcd a b)`. -/
theorem dvd_polyOfBits_polyGcd {a b : List Bool} {u : (ZMod 2)[X]}
    (ha : u ∣ polyOfBits a) (hb : u ∣ polyOfBits b) :
    u ∣ polyOfBits (polyGcd a b) := by
  rw [polyGcd_eq_coeffList, polyOfBits_map_bitEquiv]
  exact CoeffList.dvd_ofCoeffList_gcd
    (by rwa [← polyOfBits_eq_ofCoeffList]) (by rwa [← polyOfBits_eq_ofCoeffList])

/-- `polyOfBits (polyGcd a b) ≠ 0` whenever either argument is nonzero. -/
theorem polyOfBits_polyGcd_ne_zero {a b : List Bool} (h : polyOfBits a ≠ 0 ∨ polyOfBits b ≠ 0) :
    polyOfBits (polyGcd a b) ≠ 0 := by
  rw [polyGcd_eq_coeffList, polyOfBits_map_bitEquiv]
  exact CoeffList.ofCoeffList_gcd_ne_zero (by simpa [polyOfBits_eq_ofCoeffList] using h)

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
    · simp [hdiv, show k % q ≠ 0 from fun h => hdiv (Nat.dvd_of_mod_eq_zero h)]
  · rw [List.getD_eq_default _ _ (by simp; omega), bitEquiv_symm_false]
    symm; split_ifs with hdiv
    · rw [List.getD_eq_default f _ (Nat.le_of_not_lt fun hlt => hk <| by
        simpa only [Nat.mul_div_cancel' hdiv] using Nat.mul_lt_mul_of_pos_left hlt hq),
        bitEquiv_symm_false]
    · rfl

/-! ### Boolean Gaussian elimination (`kernelVecBits`) matching `kernelVec` -/

/-- Bit-vector to `Fin n → ZMod 2` interpretation. -/
@[expose] def bitsToZModVec (n : ℕ) (v : List Bool) : Fin n → ZMod 2 :=
  fun i => bitEquiv.symm (v.getD i.val false)

/-- Row-list to `Matrix (Fin r) (Fin n) (ZMod 2)` interpretation. -/
@[expose] def rowsToZModMatrix (r n : ℕ) (M : List (List Bool)) :
    Matrix (Fin r) (Fin n) (ZMod 2) :=
  fun i => bitsToZModVec n (M.getD i.val [])

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
  unfold kernelStepBits; dsimp only
  split_ifs with h
  · refine ⟨by simpa using hN_len, ?_⟩
    rintro _ hw; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    have hpiv := hN_mem _ (List.getD_mem [] h)
    split_ifs
    · rw [List.length_zipWith, hN_mem v hv, hpiv, min_self]
    · exact hN_mem v hv
  · exact ⟨hN_len, hN_mem⟩

/-- Prefix folding of `kernelStepBits` preserves row count and row length `n`. -/
theorem length_kernelBasisBits_take {n : ℕ} (M : List (List Bool)) (k : ℕ) :
    ((M.take k).foldl (fun N a => kernelStepBits a N) (listSingles n)).length = n ∧
      ∀ v ∈ (M.take k).foldl (fun N a => kernelStepBits a N) (listSingles n), v.length = n := by
  induction k with
  | zero =>
    simp only [List.take_zero, List.foldl_nil, listSingles, List.length_map, List.length_range,
      List.mem_map, List.mem_range, true_and]
    rintro _ ⟨i, _, rfl⟩; simp [listSingle]
  | succ k ih =>
    by_cases hk : k < M.length
    · rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact length_kernelStepBits ih.1 ih.2
    · rwa [List.take_of_length_le (by omega), ← List.take_of_length_le (Nat.le_of_not_lt hk)]

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
    have hj := h _ (List.getD_mem false (i := j.val) (by omega))
    simpa only [List.getD_eq_getElem?_getD] using hj

private theorem kernelStepBits_eq_kernelStep {n : ℕ} {a : List Bool} {N : List (List Bool)}
    (ha : a.length = n) (hN_len : N.length = n) (hN_mem : ∀ v ∈ N, v.length = n) (i : Fin n) :
    bitsToZModVec n ((kernelStepBits a N).getD i.val []) =
      kernelStep (bitsToZModVec n a) (fun j => bitsToZModVec n (N.getD j.val [])) i := by
  let aZ := bitsToZModVec n a
  let NZ : Fin n → Fin n → ZMod 2 := fun j => bitsToZModVec n (N.getD j.val [])
  have hval : ∀ j : Fin n, rowValues aZ NZ j = bitEquiv.symm (listDot a (N.getD j.val [])) :=
    fun j => listDot_eq_dotProduct ha (hN_mem _ (List.getD_mem [] (by omega))) |>.symm
  unfold kernelStepBits; dsimp only
  by_cases hp_lt : (N.map (listDot a)).idxOf true < N.length
  · set p := (N.map (listDot a)).idxOf true
    have hp_lt' : p < n := by omega
    have hp_dot : listDot a (N.getD p []) = true := by
      rw [List.getD_eq_getElem N [] hp_lt, ← List.getElem_map (f := listDot a)]
      exact List.getElem_idxOf (by simpa only [List.length_map] using hp_lt)
    have hpiv_eq : pivotVec aZ NZ = NZ ⟨p, hp_lt'⟩ :=
      sum_firstFlags_smul_eq_of_first (rowValues aZ NZ) NZ
        (by rw [hval ⟨p, hp_lt'⟩, hp_dot]; exact one_ne_zero) fun k hk => by
          have hnt := List.not_of_lt_findIdx (p := (· == true)) (xs := N.map (listDot a)) hk
          simp only [List.getElem_map, beq_true] at hnt
          rw [hval k, List.getD_eq_getElem _ _ (by omega), hnt, bitEquiv_symm_false]
    have hbeta : aZ ⬝ᵥ pivotVec aZ NZ = 1 :=
      hpiv_eq ▸ (hval ⟨p, hp_lt'⟩).trans (by rw [hp_dot, bitEquiv_symm_true])
    rw [ite_eq_left hp_lt, List.getD_eq_getElem _ _ (by simp [hN_len]), List.getElem_map,
      kernelStep, hbeta, div_one, ← List.getD_eq_getElem N [] (by omega)]
    have hi_len : (N.getD i.val []).length = n := hN_mem _ (List.getD_mem [] (by omega))
    have hpiv_len : (N.getD p []).length = n := hN_mem _ (List.getD_mem [] hp_lt)
    by_cases hdi : listDot a (N.getD i.val []) = true
    · rw [ite_eq_left hdi, show rowValues aZ NZ i = 1 by rw [hval i, hdi, bitEquiv_symm_true],
        one_smul, hpiv_eq]
      funext k; simp only [bitsToZModVec, Pi.sub_apply, NZ]
      have hk_zip : k.val < (List.zipWith Bool.xor (N.getD i.val []) (N.getD p [])).length := by
        rw [List.length_zipWith, hi_len, hpiv_len, min_self]; exact k.isLt
      rw [List.getD_eq_getElem _ _ hk_zip, List.getElem_zipWith,
        ← List.getD_eq_getElem _ false (by rw [hi_len]; exact k.isLt),
        ← List.getD_eq_getElem _ false (by rw [hpiv_len]; exact k.isLt),
        ← Bool.add_eq_xor, map_add, CharTwo.sub_eq_add]
    · rw [ite_eq_right hdi,
        show rowValues aZ NZ i = 0 by rw [hval i, Bool.eq_false_of_not_eq_true hdi]; rfl,
        zero_smul, sub_zero]
  · rw [ite_eq_right hp_lt]
    have hnot : true ∉ N.map (listDot a) := by
      rwa [← List.idxOf_lt_length_iff, List.length_map]
    have hrow0 : rowValues aZ NZ = 0 := funext fun j => by
      have hne : listDot a (N.getD j.val []) ≠ true :=
        fun h => hnot (List.mem_map.mpr ⟨_, List.getD_mem [] (by omega), h⟩)
      exact (hval j).trans (by rw [Bool.eq_false_of_not_eq_true hne]; rfl)
    rw [kernelStep, show pivotVec aZ NZ = 0 by simp [pivotVec, firstFlags_of_eq_zero hrow0],
      hrow0, Pi.zero_apply, zero_div, zero_smul, sub_zero]

private theorem kernelBasisBits_take_eq {r n : ℕ} (M : List (List Bool)) (hM_len : M.length = r)
    (hM_mem : ∀ a ∈ M, a.length = n) (k : ℕ) (hk : k ≤ r) (i : Fin n) :
    bitsToZModVec n
        (((M.take k).foldl (fun N a => kernelStepBits a N) (listSingles n)).getD i.val []) =
      kernelBasisUpTo (rowsToZModMatrix r n M) k i := by
  induction k generalizing i with
  | zero =>
    simp only [List.take_zero, List.foldl_nil, kernelBasisUpTo, listSingles]
    rw [List.getD_map_range (listSingle n) [] i.isLt, listSingle_eq_ofFn_single]
    funext j; simp only [bitsToZModVec, List.getD_ofFn, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> simp
  | succ k ih =>
    have hkr : k < r := by omega
    rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons,
      List.foldl_nil, kernelBasisUpTo, dite_eq_left hkr]
    have hprev := length_kernelBasisBits_take (n := n) M k
    rw [kernelStepBits_eq_kernelStep (hM_mem _ (List.getElem_mem _)) hprev.1 hprev.2 i,
      show bitsToZModVec n (M[k]'(by omega)) = rowsToZModMatrix r n M ⟨k, hkr⟩ from funext fun j =>
        by dsimp only [bitsToZModVec, rowsToZModMatrix]; rw [List.getD_eq_getElem M [] (by omega)],
      funext fun j => ih (by omega) j]

/-- `kernelBasisBits` agrees with `LinearAlgebra.kernelBasis` under `bitsToZModVec`. -/
theorem bitsToZModVec_kernelBasisBits {r n : ℕ} (M : List (List Bool)) (hM_len : M.length = r)
    (hM_mem : ∀ a ∈ M, a.length = n) (i : Fin n) :
    bitsToZModVec n ((kernelBasisBits n M).getD i.val []) =
      kernelBasis (rowsToZModMatrix r n M) i := by
  simpa only [kernelBasisBits, kernelBasis, List.take_of_length_le hM_len.le] using
    kernelBasisBits_take_eq M hM_len hM_mem r le_rfl i

/-- `kernelVecBits` agrees with `LinearAlgebra.kernelVec` under `bitsToZModVec`. -/
theorem bitsToZModVec_kernelVecBits_eq {r n : ℕ} (M : List (List Bool)) (hM_len : M.length = r)
    (hM_mem : ∀ a ∈ M, a.length = n) :
    bitsToZModVec n (kernelVecBits n M) = kernelVec (rowsToZModMatrix r n M) := by
  let A := rowsToZModMatrix r n M
  let N := kernelBasisBits n M
  obtain ⟨hN_len, hN_mem⟩ := length_kernelBasisBits n M
  have hN_len' : N.length = n := hN_len
  unfold kernelVecBits; rw [kernelVec]
  cases hfind : N.find? (fun v => v.any id) with
  | none =>
    simp only [Option.getD_none]
    have hnone : ∀ i : Fin n, kernelBasis A i = 0 := fun i => by
      have hi := List.getD_mem (l := N) [] (show i.val < N.length by rw [hN_len']; exact i.isLt)
      rw [← bitsToZModVec_kernelBasisBits M hM_len hM_mem i]
      exact (bitsToZModVec_eq_zero_iff (hN_mem _ hi)).mpr
        (Bool.eq_false_of_not_eq_true (List.find?_eq_none.mp hfind _ hi))
    have hflags : (fun i => if kernelBasis A i = 0 then (0 : ZMod 2) else 1) = 0 :=
      funext fun i => by simp [hnone i]
    rw [firstFlags_of_eq_zero hflags]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact (bitsToZModVec_eq_zero_iff List.length_replicate).mpr (by simp)
  | some v =>
    simp only [Option.getD_some]
    obtain ⟨hp_pred, p, hp_lt, hp_get, hp_min⟩ := List.find?_eq_some_iff_getElem.mp hfind
    have hp_n : p < n := by rw [← hN_len']; exact hp_lt
    have hv_eq : v = N.getD p [] := by rw [List.getD_eq_getElem _ _ hp_lt, hp_get]
    have hne_p : kernelBasis A ⟨p, hp_n⟩ ≠ 0 := by
      rw [← bitsToZModVec_kernelBasisBits M hM_len hM_mem ⟨p, hp_n⟩, ← hv_eq, Ne,
        bitsToZModVec_eq_zero_iff (hN_mem v (List.mem_of_find?_eq_some hfind)), hp_pred]
      exact Bool.false_ne_true.symm
    have hlt_p : ∀ i < (⟨p, hp_n⟩ : Fin n),
        (if kernelBasis A i = 0 then (0 : ZMod 2) else 1) = 0 := fun i hi => by
      have hi0 : kernelBasis A i = 0 := by
        rw [← bitsToZModVec_kernelBasisBits M hM_len hM_mem i,
          List.getD_eq_getElem N [] (show i.val < N.length by rw [hN_len']; exact i.isLt)]
        exact (bitsToZModVec_eq_zero_iff (hN_mem _ (List.getElem_mem _))).mpr
          (Bool.eq_false_of_not_eq_true (by simpa using hp_min i.val hi))
      simp [hi0]
    rw [sum_firstFlags_smul_eq_of_first _ (kernelBasis A) (by simp [hne_p]) hlt_p,
      hv_eq, bitsToZModVec_kernelBasisBits M hM_len hM_mem ⟨p, hp_n⟩]

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
    h = ∑ k : Fin (d - 1), C (h.coeff (k.val + 1)) * X ^ (k.val + 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)]
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
    h = ∑ k : Fin (d - 1), C (v k) * X ^ (k.val + 1) ∧ h.coeff 0 = 0 ∧
      (d ≤ 1 → h = 0) ∧ (h ≠ 0 → h.natDegree < d) := by
  let l := List.ofFn fun k : Fin (d - 1) => bitEquiv (v k)
  let h := polyOfBits (false :: l)
  have h0 : h.coeff 0 = 0 := by simp [h, coeff_polyOfBits]
  have hhi : ∀ m, d ≤ m → h.coeff m = 0 := by
    rintro (_ | m) hm
    · exact h0
    · rw [coeff_polyOfBits, List.getD_cons_succ, List.getD_eq_default _ _ (by simp [l]; omega),
        bitEquiv_symm_false]
  have hsum : h = ∑ k : Fin (d - 1), C (v k) * X ^ (k.val + 1) := by
    rw [eq_sum_C_mul_X_pow_succ_of_coeff_zero h0 hhi]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_polyOfBits, List.getD_cons_succ, List.getD_ofFn, bitEquiv.symm_apply_apply]
  have hle1 : d ≤ 1 → h = 0 := fun hd => by
    rw [hsum]
    exact Finset.sum_eq_zero fun k _ => by have := k.isLt; omega
  exact ⟨hsum, h0, hle1, fun hne => Nat.lt_of_not_le fun hle =>
    hne (leadingCoeff_eq_zero.mp (hhi _ hle))⟩

private theorem berlekampMatrix_col_mk {l : List Bool}
    (hgt_ne : polyOfBits (l ++ [true]) ≠ 0) (k : Fin (l.length - 1)) (c : ZMod 2) :
    let pb := AdjoinRoot.powerBasis hgt_ne
    AdjoinRoot.mk (polyOfBits (l ++ [true])) (C c * (X ^ (2 * (k.val + 1)) - X ^ (k.val + 1))) =
      ∑ i : Fin l.length,
        (c * rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix (l ++ [true])) i k) •
          pb.gen ^ i.val := by
  intro pb
  have hroot : aeval pb.gen (polyOfBits (l ++ [true])) = 0 := by
    rw [AdjoinRoot.powerBasis_gen hgt_ne, AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  have hpow := pow_eq_sum_powerTable l hroot (e := 2 * (k.val + 1)) (by omega)
  have hsingle : pb.gen ^ (k.val + 1) =
      ∑ i : Fin l.length, (if i.val = k.val + 1 then (1 : ZMod 2) else 0) • pb.gen ^ i.val := by
    rw [Finset.sum_eq_single ⟨k.val + 1, by omega⟩] <;> simp +contextual [Fin.ext_iff]
  rw [map_mul, map_sub, AdjoinRoot.mk_C, map_pow, map_pow, AdjoinRoot.mk_X]
  change (algebraMap (ZMod 2) _ c) * (pb.gen ^ (2 * (k.val + 1)) - pb.gen ^ (k.val + 1)) = _
  rw [hpow, ← Fin.sum_univ_eq_sum_range, hsingle, ← Finset.sum_sub_distrib, ← Algebra.smul_def,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_smul, smul_smul]
  congr 1; congr 1
  rw [rowsToZModMatrix, bitsToZModVec, berlekampMatrix]
  dsimp only
  rw [show (l ++ [true]).length - 1 = l.length by simp, List.getD_map_range _ [] i.isLt,
    List.getD_map_range _ false k.isLt, ← Bool.add_eq_xor, map_add, CharTwo.sub_eq_add]
  congr 1; by_cases hik : i.val = k.val + 1 <;> simp [hik]

private theorem berlekampMatrix_mulVec_eq_zero_iff {l : List Bool}
    (v : Fin (l.length - 1) → ZMod 2) :
    rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix (l ++ [true])) *ᵥ v = 0 ↔
      polyOfBits (l ++ [true]) ∣
        (∑ k : Fin (l.length - 1), C (v k) * X ^ (k.val + 1)) ^ 2 -
          ∑ k : Fin (l.length - 1), C (v k) * X ^ (k.val + 1) := by
  set gt := l ++ [true]
  set h := ∑ k : Fin (l.length - 1), C (v k) * X ^ (k.val + 1)
  have hgt_ne : polyOfBits gt ≠ 0 := polyOfBits_ne_zero_of_mem (by simp [gt])
  let pb := AdjoinRoot.powerBasis hgt_ne
  have hpb_dim : pb.dim = l.length := by
    rw [AdjoinRoot.powerBasis_dim hgt_ne]; exact natDegree_polyOfBits_append_true l
  have hsq_sub : h ^ 2 - h =
      ∑ k : Fin (l.length - 1), C (v k) * (X ^ (2 * (k.val + 1)) - X ^ (k.val + 1)) := by
    rw [CharTwo.sub_eq_add, CharTwo.sum_sq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by
      rw [mul_pow, ← C_pow, ZMod.pow_card, ← pow_mul, CharTwo.sub_eq_add, mul_add, mul_comm _ 2]
  have hmk : AdjoinRoot.mk (polyOfBits gt) (h ^ 2 - h) =
      ∑ i : Fin l.length,
        (rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix gt) *ᵥ v) i •
          pb.gen ^ i.val := by
    rw [hsq_sub, map_sum]
    have hcol : ∀ k : Fin (l.length - 1),
        AdjoinRoot.mk (polyOfBits gt) (C (v k) * (X ^ (2 * (k.val + 1)) - X ^ (k.val + 1))) =
          ∑ i : Fin l.length, (v k * rowsToZModMatrix l.length (l.length - 1)
            (berlekampMatrix gt) i k) • pb.gen ^ i.val :=
      fun k => berlekampMatrix_col_mk hgt_ne k (v k)
    simp_rw [hcol]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => by
      rw [mulVec, dotProduct, Finset.sum_smul]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm (v k)]
  rw [← AdjoinRoot.mk_eq_zero, hmk]
  refine ⟨fun h0 => by simp [h0], fun h0 => funext fun i => ?_⟩
  let e := finCongr hpb_dim
  have h0' : ∑ j : Fin pb.dim,
      (rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix gt) *ᵥ v) (e j) •
        pb.basis j = 0 := by
    rw [← h0]; exact Finset.sum_equiv e (by simp) fun j _ => by rw [pb.coe_basis]; rfl
  simpa using linearIndependent_iff'.mp pb.basis.linearIndependent Finset.univ _ h0' (e.symm i)
    (Finset.mem_univ _)

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
  set g := polyOfBits (l ++ [true])
  have hg_ne : g ≠ 0 := polyOfBits_ne_zero_of_mem (by simp)
  have hg_deg : g.natDegree = l.length := natDegree_polyOfBits_append_true l
  rw [irreducible_iff] at hnirr; push Not at hnirr
  obtain ⟨p, q, hpq, hnp, hnq⟩ := hnirr (not_isUnit_of_natDegree_pos g (by omega))
  have hcop : IsCoprime p q := EuclideanDomain.gcd_isUnit_iff.mp <|
    hsq _ (hpq ▸ mul_dvd_mul (EuclideanDomain.gcd_dvd_left p q) (EuclideanDomain.gcd_dvd_right p q))
  obtain ⟨a, b, hab⟩ := hcop
  set u := (a * p) % g
  have hgu_diff : g ∣ a * p - u :=
    ⟨(a * p) / g, (eq_sub_of_add_eq (EuclideanDomain.div_add_mod (a * p) g)).symm⟩
  have hpu : p ∣ u := by
    simpa only [sub_sub_cancel] using dvd_sub (dvd_mul_left p a) (dvd_trans ⟨q, hpq⟩ hgu_diff)
  have hq1u : q ∣ 1 - u := by
    rw [show (1 : (ZMod 2)[X]) - u = (a * p - u) + b * q by rw [← hab]; ring]
    exact dvd_add (dvd_trans ⟨p, by rw [hpq, mul_comm]⟩ hgu_diff) (dvd_mul_left q b)
  have hu0 : u ≠ 0 := fun h => hnq (isUnit_iff_dvd_one.mpr (by simpa [h] using hq1u))
  have hu1 : u ≠ 1 := fun h => hnp (isUnit_iff_dvd_one.mpr (h ▸ hpu))
  have hgu : g ∣ u ^ 2 - u := by
    rw [show u ^ 2 - u = u * (u - 1) by ring, hpq]
    exact mul_dvd_mul hpu (by simpa only [neg_sub] using dvd_neg.mpr hq1u)
  have hu_deg : u.natDegree < l.length := by
    have hlt := Polynomial.degree_mod_lt (a * p) hg_ne
    rwa [degree_eq_natDegree hg_ne, hg_deg, degree_eq_natDegree hu0, Nat.cast_lt] at hlt
  set h := u - C (u.coeff 0)
  have hh_ne : h ≠ 0 := fun hh => by
    have heq := sub_eq_zero.mp hh
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (u.coeff 0) with hc | hc
    · exact hu0 (by simpa [hc] using heq)
    · exact hu1 (by simpa [hc] using heq)
  have hh_deg : h.natDegree < l.length := (natDegree_sub_le u _).trans_lt (by simpa using hu_deg)
  have hh_sum : h = ∑ k : Fin (l.length - 1), C (h.coeff (k.val + 1)) * X ^ (k.val + 1) :=
    eq_sum_C_mul_X_pow_succ_of_coeff_zero (by simp [h]) fun m hm =>
      coeff_eq_zero_of_natDegree_lt (hh_deg.trans_le hm)
  have hgh : g ∣ h ^ 2 - h := by
    rwa [show h ^ 2 - h = u ^ 2 - u by
      rw [show h = u + C (u.coeff 0) from CharTwo.sub_eq_add .., CharTwo.add_sq, ← C_pow,
        ZMod.pow_card, CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_add_add_comm,
        CharTwo.add_self_eq_zero, add_zero]]
  refine ⟨fun k => h.coeff (k.val + 1), fun hv0 => hh_ne <| by
    rw [hh_sum]; exact Finset.sum_eq_zero fun k _ => by simp [congrFun hv0 k],
    (berlekampMatrix_mulVec_eq_zero_iff _).mpr (hh_sum ▸ hgh)⟩

/-- Core splitting property: when `kernelVecBits` finds a nontrivial Berlekamp vector `vbits` for
`g = l ++ [true]`, `polyGcd g (false :: vbits)` is a proper positive-degree squarefree divisor of
`g` and `g` is reducible. -/
private theorem berlekampStep_split_spec {l vbits : List Bool}
    (hsq : Squarefree (polyOfBits (l ++ [true])))
    (hv_len : vbits.length = l.length - 1) (hv : vbits.any id = true)
    (hmul : rowsToZModMatrix l.length (l.length - 1) (berlekampMatrix (l ++ [true])) *ᵥ
      bitsToZModVec (l.length - 1) vbits = 0) :
    let g := l ++ [true]
    let f := polyGcd g (false :: vbits)
    Squarefree (polyOfBits f) ∧ 0 < (polyOfBits f).natDegree ∧
      polyOfBits f ∣ polyOfBits g ∧ ¬ Irreducible (polyOfBits g) ∧ f.length < g.length := by
  let g := l ++ [true]; let f := polyGcd g (false :: vbits)
  let hp := polyOfBits (false :: vbits)
  have hfdvd : polyOfBits f ∣ polyOfBits g := polyOfBits_polyGcd_dvd_left _ _
  have hne_g : polyOfBits g ≠ 0 := polyOfBits_ne_zero_of_mem (by simp [g])
  have hne_f : polyOfBits f ≠ 0 := polyOfBits_polyGcd_ne_zero (Or.inl hne_g)
  have hfv_eq : false :: vbits =
      false :: List.ofFn fun k : Fin (l.length - 1) =>
        bitEquiv (bitsToZModVec (l.length - 1) vbits k) := congrArg (false :: ·) <|
    (List.ext_getElem (by simp [hv_len]) fun i hi _ => by
      simp only [List.getElem_ofFn, bitsToZModVec, bitEquiv.apply_symm_apply]
      exact List.getD_eq_getElem vbits false (by simpa [hv_len] using hi)).symm
  have hh_spec := poly_from_berlekampVec (bitsToZModVec (l.length - 1) vbits)
  rw [← hfv_eq] at hh_spec
  obtain ⟨hh_sum, hh0, -, hh_deg⟩ := hh_spec
  have hhp_ne : hp ≠ 0 := by
    obtain ⟨b, hb, hb'⟩ := List.any_eq_true.mp hv
    simp only [id_eq] at hb'
    exact polyOfBits_ne_zero_of_mem (List.mem_cons_of_mem _ (hb' ▸ hb))
  have hdeg_g : (polyOfBits g).natDegree = l.length := natDegree_polyOfBits_append_true l
  have hhp_deg : hp.natDegree < l.length := hh_deg hhp_ne
  have hp1_ne : hp - 1 ≠ 0 := fun h1 => by
    have hcoeff := congrArg (·.coeff 0) (sub_eq_zero.mp h1)
    rw [show hp.coeff 0 = 0 from hh0, coeff_one] at hcoeff
    simp at hcoeff
  have hnot_dvd : ∀ q : (ZMod 2)[X], q ≠ 0 → q.natDegree < l.length → ¬ polyOfBits g ∣ q :=
    fun q hq hql hd => by have := Polynomial.natDegree_le_of_dvd hd hq; omega
  have hprod : polyOfBits g ∣ hp * (hp - 1) := by
    rw [show hp * (hp - 1) = hp ^ 2 - hp by ring, show hp = _ from hh_sum]
    exact (berlekampMatrix_mulVec_eq_zero_iff _).mp hmul
  have hnot_hp := hnot_dvd hp hhp_ne hhp_deg
  have hnot_hp1 := hnot_dvd (hp - 1) hp1_ne <| (natDegree_sub_le hp 1).trans_lt
    (by simpa only [natDegree_one, max_eq_left (Nat.zero_le _)] using hhp_deg)
  have hf_nu : ¬ IsUnit (polyOfBits f) := fun hu => hnot_hp1 <|
    (EuclideanDomain.gcd_isUnit_iff.mp <| isUnit_of_dvd_unit (dvd_polyOfBits_polyGcd
      (EuclideanDomain.gcd_dvd_left _ _)
      (EuclideanDomain.gcd_dvd_right _ _)) hu).dvd_of_dvd_mul_left hprod
  have hf_nil : f ≠ [] := fun h => hne_f (h ▸ polyOfBits_nil)
  have hf_deg_lt : (polyOfBits f).natDegree < l.length :=
    (Polynomial.natDegree_le_of_dvd (polyOfBits_polyGcd_dvd_right _ _) hhp_ne).trans_lt hhp_deg
  refine ⟨hsq.squarefree_of_dvd hfdvd, natDegree_pos_of_ne_zero_of_not_isUnit hne_f hf_nu, hfdvd,
    fun hirr => ((UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr).dvd_or_dvd hprod).elim
      hnot_hp hnot_hp1, ?_⟩
  have hfd : (polyOfBits f).natDegree = f.length - 1 :=
    natDegree_polyOfBits_of_polyTrim (polyTrim_polyGcd g (false :: vbits)) hf_nil
  have hpos : 0 < f.length := List.length_pos_of_ne_nil hf_nil
  change f.length < (l ++ [true]).length
  rw [List.length_append, List.length_singleton]; omega

private theorem berlekampStep_invariant (g : List Bool)
    (hgt : polyTrim g = g) (hsq : Squarefree (polyOfBits g)) (hdeg : 0 < (polyOfBits g).natDegree) :
    let g' := berlekampStep g
    polyTrim g' = g' ∧ Squarefree (polyOfBits g') ∧ 0 < (polyOfBits g').natDegree ∧
      polyOfBits g' ∣ polyOfBits g ∧
      (Irreducible (polyOfBits g) → g' = g) ∧
      (¬ Irreducible (polyOfBits g) → g'.length < g.length) := by
  have hg_ne : g ≠ [] := fun h => by rw [h, polyOfBits_nil, natDegree_zero] at hdeg; omega
  obtain ⟨l, rfl⟩ : ∃ l, g = l ++ [true] := by
    rcases polyTrim_eq_nil_or_append_true g with h | ⟨l, h⟩
    · exact absurd (hgt ▸ h) hg_ne
    · exact ⟨l, hgt ▸ h⟩
  have hdeg_l : l.length = (polyOfBits (l ++ [true])).natDegree :=
    (natDegree_polyOfBits_append_true l).symm
  dsimp only [berlekampStep]; rw [hgt]
  by_cases hlen2 : (l ++ [true]).length ≤ 2
  · have hirr : Irreducible (polyOfBits (l ++ [true])) :=
      Polynomial.irreducible_of_degree_eq_one <| by
        rw [degree_eq_natDegree (polyOfBits_ne_zero_of_mem (by simp)),
          natDegree_polyOfBits_append_true]
        simp only [List.length_append, List.length_singleton] at hlen2
        rw [show l.length = 1 by omega]; rfl
    rw [ite_eq_left hlen2]
    exact ⟨hgt, hsq, hdeg, dvd_rfl, fun _ => rfl, fun h => absurd hirr h⟩
  · have hl2 : 2 ≤ l.length := by simp at hlen2; omega
    obtain ⟨hM_len, hM_mem⟩ := length_berlekampMatrix (l ++ [true])
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hM_len hM_mem
    have hgt_len : (l ++ [true]).length - 2 = l.length - 1 := by simp
    set vbits := kernelVecBits ((l ++ [true]).length - 2) (berlekampMatrix (l ++ [true]))
    rw [ite_eq_right hlen2]
    by_cases hv : vbits.any id = true
    · rw [ite_eq_left hv]
      have hmul : rowsToZModMatrix l.length (l.length - 1)
          (berlekampMatrix (l ++ [true])) *ᵥ bitsToZModVec (l.length - 1) vbits = 0 := by
        simpa only [vbits, hgt_len] using
          mulVec_kernelVecBits _ hM_len (by simpa [Nat.add_sub_assoc] using hM_mem)
      obtain ⟨hfsq, hfdeg, hfdvd, hnirr, hflt⟩ :=
        berlekampStep_split_spec hsq (by rw [length_kernelVecBits, hgt_len]) hv hmul
      exact ⟨polyTrim_polyGcd _ _, hfsq, hfdeg, hfdvd, fun h => absurd h hnirr, fun _ => hflt⟩
    · rw [ite_eq_right hv]
      have hirr : Irreducible (polyOfBits (l ++ [true])) := by
        by_contra hnirr
        obtain ⟨v, hv_ne, hmul⟩ := exists_berlekamp_ker_of_not_irreducible hl2 hsq hnirr
        have hany := kernelVecBits_any_of_exists (berlekampMatrix (l ++ [true])) hM_len
          (by simpa [Nat.add_sub_assoc] using hM_mem) ⟨v, hv_ne, hmul⟩
        exact hv (by simpa only [vbits, hgt_len] using hany)
      exact ⟨hgt, hsq, hdeg, dvd_rfl, fun _ => rfl, fun h => absurd hirr h⟩

/-- For any squarefree binary polynomial `g` of positive degree, `berlekampIrreducibleFactor g`
produces a trimmed bit list whose polynomial divides `polyOfBits g`. -/
theorem polyTrim_berlekampIrreducibleFactor (g : List Bool) :
    polyTrim (berlekampIrreducibleFactor g) = berlekampIrreducibleFactor g := by
  unfold berlekampIrreducibleFactor
  cases g.length with
  | zero => exact polyTrim_polyTrim g
  | succ k =>
    rw [Function.iterate_succ_apply']; dsimp only [berlekampStep]
    split_ifs <;> first | exact polyTrim_polyGcd _ _ | exact polyTrim_polyTrim _

/-- `berlekampIrreducibleFactor g` produces a divisor of `polyOfBits g`. -/
theorem polyOfBits_berlekampIrreducibleFactor_dvd {g : List Bool}
    (hsq : Squarefree (polyOfBits g)) (hdeg : 0 < (polyOfBits g).natDegree) :
    polyOfBits (berlekampIrreducibleFactor g) ∣ polyOfBits g ∧
      Irreducible (polyOfBits (berlekampIrreducibleFactor g)) ∧
      0 < (polyOfBits (berlekampIrreducibleFactor g)).natDegree := by
  have hgt : ∀ k : ℕ, let f := (berlekampStep)^[k] (polyTrim g)
      polyTrim f = f ∧ Squarefree (polyOfBits f) ∧ 0 < (polyOfBits f).natDegree ∧
        polyOfBits f ∣ polyOfBits g ∧
        (¬ Irreducible (polyOfBits f) → f.length + k ≤ (polyTrim g).length) := fun k => by
    induction k with
    | zero => simp [polyTrim_polyTrim, hsq, hdeg]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨ht, hsqk, hdegk, hdvd, hdec⟩ := ih
      obtain ⟨ht', hsq', hdeg', hdvd', hstay, hshrink⟩ := berlekampStep_invariant _ ht hsqk hdegk
      refine ⟨ht', hsq', hdeg', hdvd'.trans hdvd, fun hnirr' => ?_⟩
      have hnirr : ¬ Irreducible (polyOfBits ((berlekampStep)^[k] (polyTrim g))) :=
        fun hirr => hnirr' (by rw [hstay hirr]; exact hirr)
      have := hdec hnirr; have := hshrink hnirr; omega
  obtain ⟨-, -, hdeg', hdvd, hdec⟩ := hgt g.length
  refine ⟨hdvd, ?_, hdeg'⟩
  by_contra hnirr
  have hpos := List.length_pos_of_ne_nil (fun hnil : (berlekampStep)^[g.length] (polyTrim g) = [] =>
    by rw [hnil, polyOfBits_nil, natDegree_zero] at hdeg'; omega)
  have := hdec hnirr; have := length_polyTrim_le g; omega

/-- For squarefree `g` of positive degree, `berlekampIrreducibleFactor g` is irreducible. -/
theorem irreducible_polyOfBits_berlekampIrreducibleFactor {g : List Bool}
    (hsq : Squarefree (polyOfBits g)) (hdeg : 0 < (polyOfBits g).natDegree) :
    Irreducible (polyOfBits (berlekampIrreducibleFactor g)) :=
  (polyOfBits_berlekampIrreducibleFactor_dvd hsq hdeg).2.1

end Cslib.AffineDisperser.Li
