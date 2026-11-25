/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Relations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finset.Max

/-!
# Normal-monomial bases of pure-power quotients

For `ell ≥ 1` and lower parts `r i` of total degree below `ell`, the quotient by
`X i ^ ell - r i` has the concrete basis `normalBasis`, indexed by `Fin n → Fin ell`.
Thus it is finite free over the original commutative coefficient ring, with `ell ^ n`
normal monomials. There is no field, reducedness, or simple-root hypothesis.

Degree induction proves spanning by replacing a divisible pure power with its lower part.
The residue pairing detects a coefficient of maximal total degree in any proposed dependence,
proving independence. `quotientFunctional` descends the residue to the actual relation ideal;
it is used in the subsequent multiplication-trace construction.

Ported from `LeanCanny.CountingHierarchy.PurePowerQuotient` and `PurePowerBasis` at lean-canny
commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`, as an algebraic step toward counting bounds.
-/

public section

namespace MvPolynomial.PurePower

open Module
open scoped BigOperators

variable {S : Type*} [CommRing S] {n ell : ℕ}
/-- Quotient by the relations `X i ^ ell - r i`. -/
abbrev QuotientAlgebra (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) :=
  MvPolynomial (Fin n) S ⧸ relationIdeal ell r

/-- The canonical coefficient-algebra map into the pure-power quotient. -/
@[expose] noncomputable def projection (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) :
    MvPolynomial (Fin n) S →ₐ[S] QuotientAlgebra ell r :=
  Ideal.Quotient.mkₐ S (relationIdeal ell r)

/-- The defining pure-power reductions hold in the quotient. -/
theorem projection_X_pow (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) (i : Fin n) :
    (projection ell r (X i)) ^ ell = projection ell r (r i) := by
  rw [← sub_eq_zero, ← map_pow, ← map_sub]
  change Ideal.Quotient.mk (relationIdeal ell r) (X i ^ ell - r i) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

/-- The residue on the actual quotient, using its proved ideal vanishing. -/
@[expose] noncomputable def quotientFunctional {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    QuotientAlgebra ell r →ₗ[S] S :=
  ((relationIdeal ell r).restrictScalars S).liftQ (linear hell r hr)
    (fun q hq => linear_mem_ideal hell r hr q hq)

@[simp] theorem quotientFunctional_projection {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) :
    quotientFunctional hell r hr (projection ell r v) = residue ell r v := rfl

/-- Coordinate exponents of the normal monomials are all strictly below `ell`. -/
abbrev NormalIndex (n ell : ℕ) := Fin n → Fin ell

/-- View the bounded coordinate exponents as a monomial exponent. -/
@[expose] noncomputable def boxExponent {ell : ℕ} (a : NormalIndex n ell) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i).val)

@[simp] theorem boxExponent_apply {ell : ℕ} (a : NormalIndex n ell) (i : Fin n) :
    boxExponent a i = (a i).val := rfl

/-- The quotient class of a monomial whose exponents are below `ell`. -/
@[expose] noncomputable def normalClass (ell : ℕ)
    (r : Fin n → MvPolynomial (Fin n) S) (a : NormalIndex n ell) : QuotientAlgebra ell r :=
  projection ell r (monomial (boxExponent a) 1)

private theorem projection_monomial_smul (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (e : Fin n →₀ ℕ) (c : S) :
    projection ell r (monomial e c) = c • projection ell r (monomial e 1) := by
  rw [← map_smul]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

/-- Degree induction expresses every monomial through normal classes. -/
private theorem monomial_mem_normal_span {ell : ℕ}
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (e : Fin n →₀ ℕ) :
    projection ell r (monomial e 1) ∈ Submodule.span S (Set.range (normalClass ell r)) := by
  let U := Submodule.span S (Set.range (normalClass ell r))
  by_cases hnormal : ∀ i, e i < ell
  · let a : NormalIndex n ell := fun i => ⟨e i, hnormal i⟩
    have ha : boxExponent a = e := by ext i; rfl
    exact Submodule.subset_span ⟨a, by rw [normalClass, ha]⟩
  · obtain ⟨i, hi⟩ : ∃ i, ell ≤ e i := by
      simpa only [not_forall, not_lt] using hnormal
    let e' := e - Finsupp.single i ell
    let q : MvPolynomial (Fin n) S := monomial e' 1 * r i
    have hdeg : q.totalDegree < e.degree := by
      have hmul := MvPolynomial.totalDegree_mul (monomial e' (1 : S)) (r i)
      have hmono : (monomial e' (1 : S)).totalDegree ≤ e'.degree :=
        MvPolynomial.totalDegree_monomial_le _ _
      have hres : e'.degree + ell = e.degree := by
        simpa only [map_add, Finsupp.degree_single] using
          congrArg Finsupp.degree
            (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi))
      have hlo := hr i
      dsimp only [q]
      omega
    have hm : monomial e' (1 : S) * X i ^ ell = monomial e 1 := by
      rw [← monomial_add_single]
      exact congrArg (fun a => monomial a (1 : S))
        (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi))
    have hp : projection ell r (monomial e 1) = projection ell r q := by
      rw [← hm, map_mul, map_pow, projection_X_pow, ← map_mul]
    rw [hp, q.as_sum, map_sum]
    refine U.sum_mem fun m hm => ?_
    have hmdeg : m.degree < e.degree := (MvPolynomial.le_totalDegree hm).trans_lt hdeg
    rw [projection_monomial_smul]
    exact U.smul_mem (q.coeff m) (monomial_mem_normal_span r hr m)
termination_by e.degree

/-- Normal monomials span the whole quotient over the original coefficient ring. -/
theorem normal_span_eq_top {ell : ℕ}
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    Submodule.span S (Set.range (normalClass ell r)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun a => ?_
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective a
  change projection ell r v ∈ Submodule.span S (Set.range (normalClass ell r))
  induction v using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [projection_monomial_smul]
    exact Submodule.smul_mem _ c (monomial_mem_normal_span r hr e)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

private def normalDegree (a : NormalIndex n ell) : ℕ := ∑ i, (a i).val

private noncomputable def complementExponent (b : NormalIndex n ell) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => ell - 1 - (b i).val)

private theorem boxExponent_degree (a : NormalIndex n ell) :
    (boxExponent a).sum (fun _ e => e) = normalDegree a := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  rfl

private theorem complement_degree (b : NormalIndex n ell) :
    normalDegree b + (complementExponent b).sum (fun _ e => e) = n * (ell - 1) := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  change (∑ i, (b i).val) + (∑ i, (ell - 1 - (b i).val)) = _
  have hi (i : Fin n) : (b i).val + (ell - 1 - (b i).val) = ell - 1 :=
    Nat.add_sub_cancel' (Nat.le_sub_one_of_lt (b i).isLt)
  simp [← Finset.sum_add_distrib, hi]

private theorem box_add_complement_iff (a b : NormalIndex n ell) :
    boxExponent a + complementExponent b = Finsupp.equivFunOnFinite.symm (fun _ => ell - 1) ↔
      a = b := by
  refine ⟨fun h => funext fun i => Fin.ext ?_, ?_⟩
  · have hh := congrArg (fun e : Fin n →₀ ℕ => e i) h
    simp only [Finsupp.add_apply, boxExponent_apply, complementExponent,
      Finsupp.coe_equivFunOnFinite_symm] at hh
    have := (b i).isLt
    omega
  · rintro rfl
    ext i
    simp only [Finsupp.add_apply, boxExponent_apply, complementExponent,
      Finsupp.coe_equivFunOnFinite_symm]
    have := (a i).isLt
    omega

/-- Below the maximal-degree block the residue pairing is the identity matrix. -/
private theorem residue_normal_pair (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (a b : NormalIndex n ell) (hab : normalDegree a ≤ normalDegree b) :
    residue ell r (monomial (boxExponent a) 1 * monomial (complementExponent b) 1) =
      if a = b then 1 else 0 := by
  have ha : (monomial (boxExponent a) (1 : S)).totalDegree ≤ normalDegree a :=
    (MvPolynomial.totalDegree_monomial_le _ _).trans_eq (boxExponent_degree a)
  have hb : (monomial (complementExponent b) (1 : S)).totalDegree ≤
      (complementExponent b).sum (fun _ e => e) :=
    MvPolynomial.totalDegree_monomial_le _ _
  have hd := MvPolynomial.totalDegree_mul
    (monomial (boxExponent a) (1 : S)) (monomial (complementExponent b) 1)
  have hcomp := complement_degree b
  rw [residue_low_degree hell r hr _ (by omega)]
  simp only [MvPolynomial.monomial_mul_monomial, one_mul, MvPolynomial.coeff_monomial,
    box_add_complement_iff]

/-- No nonzero relation can have a coefficient of maximal monomial degree. -/
theorem normalClass_linearIndependent (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    LinearIndependent S (normalClass ell r) := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c hc a => ?_
  by_contra hca
  let s : Finset (NormalIndex n ell) := Finset.univ.filter (fun b => c b ≠ 0)
  have hs : s.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca⟩⟩
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image s normalDegree hs
  have hcb : c b ≠ 0 := (Finset.mem_filter.mp hb).2
  let q : MvPolynomial (Fin n) S := ∑ j, c j • monomial (boxExponent j) 1
  have hp : projection ell r q = 0 := by
    simpa only [q, map_sum, map_smul, normalClass] using hc
  have hq : q ∈ relationIdeal ell r := Ideal.Quotient.eq_zero_iff_mem.mp hp
  let m : MvPolynomial (Fin n) S := monomial (complementExponent b) 1
  have hz : linear hell r hr (q * m) = 0 := mul_comm m q ▸ linear_mul_mem_ideal hell r hr q hq m
  have hterm (j : NormalIndex n ell) :
      linear hell r hr ((c j • monomial (boxExponent j) 1) * m) =
        c j * (if j = b then 1 else 0) := by
    by_cases hcj : c j = 0
    · simp only [hcj, zero_smul, zero_mul, map_zero]
    · have hj : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩
      rw [smul_mul_assoc, map_smul, linear_apply, show m = monomial (complementExponent b) (1 : S)
        from rfl, residue_normal_pair hell r hr j b (hmax j hj), smul_eq_mul]
  have hsum : linear hell r hr (q * m) = c b := by
    simp only [q, Finset.sum_mul, map_sum, hterm]
    simp
  exact hcb (hsum.symm.trans hz)

/-- The concrete normal-monomial basis of the pure-power quotient. -/
@[expose] noncomputable def normalBasis (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    Basis (NormalIndex n ell) S (QuotientAlgebra ell r) :=
  Basis.mk (normalClass_linearIndependent hell r hr) (by rw [normal_span_eq_top r hr])

@[simp] theorem normalBasis_apply (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (a : NormalIndex n ell) : normalBasis hell r hr a = normalClass ell r a :=
  Basis.mk_apply _ _ a

end MvPolynomial.PurePower
