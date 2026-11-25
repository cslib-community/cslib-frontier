/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib / Cslib, Cauchy rational-function and Cauchy reconstruction)

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rational-function and Cauchy reconstruction over fields and finite fields

Implements extended-Euclidean rational-function reconstruction (`Polynomial.PolyRat.reconstruct`)
over `F[X] / (M)` for an arbitrary field `F` (including finite fields such as `ZMod p`), together
with degree-based height and denominator bounds, modular uniqueness, completeness under
`N + D < M.natDegree`, and Cauchy rational-function interpolation (`Polynomial.PolyRat.cauchy`)
from evaluation points via `Lagrange.interpolate`.

## Main definitions

* `Polynomial.PolyRat`: documented fraction pair `{ num, den : F[X] }`.
* `Polynomial.PolyRat.height`: degree height `max num.natDegree den.natDegree`.
* `Polynomial.PolyRat.reconstruct`: extended-Euclidean rational-function reconstruction modulo
  `M : F[X]` with numerator degree bound `N` and denominator degree bound `D`.
* `Polynomial.PolyRat.cauchy`: Cauchy rational-function interpolation from evaluations on a finset
  `s : Finset F`.

## Main results

* `Polynomial.PolyRat.mul_eq_mul_of_dvd_sub_of_degree_lt`,
  `Polynomial.PolyRat.eq_of_isCoprime_of_monic`, `Polynomial.PolyRat.eq_of_dvd_sub_of_bounds`,
  `Polynomial.PolyRat.eq_of_dvd_sub_of_height_lt`: modular uniqueness under degree and height
  bounds.
* `Polynomial.PolyRat.reconstruct_eq_some`: soundness (monicity, degree/denominator bounds,
  coprimality, and modular congruence).
* `Polynomial.PolyRat.reconstruct_of_eq`: completeness (recovering `some p` whenever
  `N + D < M.natDegree`, `p.den.Monic`, `IsCoprime p.num p.den`, and `IsCoprime p.den M`).
* `Polynomial.PolyRat.cauchy_eq_some`, `Polynomial.PolyRat.cauchy_of_eq`: soundness and recovery
  for Cauchy rational-function interpolation at evaluations on `s : Finset F`.

## References

* [J. von zur Gathen, J. Gerhard, *Modern Computer Algebra*][vonZurGathenGerhard2013], §§5.7–5.8
  (§5.7, p. 115 for rational function reconstruction; §5.8, p. 118 for Cauchy interpolation).
-/

public section

namespace Polynomial

open Finset

/-- A rational-function numerator-denominator pair `num / den` over `F[X]`. -/
@[ext]
structure PolyRat (F : Type*) [Semiring F] where
  /-- Numerator polynomial. -/
  num : F[X]
  /-- Denominator polynomial. -/
  den : F[X]

namespace PolyRat

noncomputable section

section HeightAndUniqueness

variable {F : Type*}

/-- Polynomial degree height `max num.natDegree den.natDegree`. -/
@[expose] def height [Semiring F] (p : PolyRat F) : ℕ :=
  max p.num.natDegree p.den.natDegree

theorem height_def [Semiring F] (p : PolyRat F) :
    p.height = max p.num.natDegree p.den.natDegree :=
  rfl

theorem natDegree_num_le_height [Semiring F] (p : PolyRat F) : p.num.natDegree ≤ p.height :=
  le_max_left _ _

theorem natDegree_den_le_height [Semiring F] (p : PolyRat F) : p.den.natDegree ≤ p.height :=
  le_max_right _ _

/-- Cross-multiplication uniqueness modulo `M`: if `M ∣ p.num - p.den * u`,
`M ∣ q.num - q.den * u`, `(p.num.degree + q.den.degree < M.degree)`, and
`(q.num.degree + p.den.degree < M.degree)`, then `p.num * q.den = q.num * p.den`. -/
theorem mul_eq_mul_of_dvd_sub_of_degree_lt [Field F] {M u : F[X]} {p q : PolyRat F}
    (hp : M ∣ p.num - p.den * u) (hq : M ∣ q.num - q.den * u)
    (hdeg₁ : p.num.degree + q.den.degree < M.degree)
    (hdeg₂ : q.num.degree + p.den.degree < M.degree) :
    p.num * q.den = q.num * p.den := by
  have hdvd : M ∣ p.num * q.den - q.num * p.den := by
    convert dvd_sub (dvd_mul_of_dvd_left hp q.den) (dvd_mul_of_dvd_left hq p.den) using 1
    ring
  refine sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hdvd ?_)
  exact (degree_sub_le _ _).trans_lt
    (max_lt ((degree_mul_le _ _).trans_lt hdeg₁) ((degree_mul_le _ _).trans_lt hdeg₂))

/-- Two reduced monic pairs with the same cross-product are equal. -/
theorem eq_of_isCoprime_of_monic [Field F] {p q : PolyRat F} (hmul : p.num * q.den = q.num * p.den)
    (hcp : IsCoprime p.num p.den) (hcq : IsCoprime q.num q.den) (hmp : p.den.Monic)
    (hmq : q.den.Monic) : p = q := by
  have hden : p.den = q.den := eq_of_monic_of_associated hmp hmq <| associated_of_dvd_dvd
    (hcp.symm.dvd_of_dvd_mul_left ⟨q.num, by rw [hmul, mul_comm]⟩)
    (hcq.symm.dvd_of_dvd_mul_left ⟨p.num, by rw [← hmul, mul_comm]⟩)
  rw [hden] at hmul
  exact PolyRat.ext (mul_right_cancel₀ hmq.ne_zero hmul) hden

/-- `mul_eq_mul_of_dvd_sub_of_degree_lt` under numerator and denominator degree bounds. -/
private theorem mul_eq_mul_of_dvd_sub_of_bounds [Field F] {M u : F[X]} {Np Dp Nq Dq : ℕ}
    {p q : PolyRat F} (hp : M ∣ p.num - p.den * u) (hq : M ∣ q.num - q.den * u)
    (hpn : p.num.degree ≤ Np) (hqn : q.num.degree ≤ Nq) (hpd : p.den.natDegree ≤ Dp)
    (hqd : q.den.natDegree ≤ Dq) (h1 : Np + Dq < M.natDegree) (h2 : Nq + Dp < M.natDegree) :
    p.num * q.den = q.num * p.den := by
  have hM : M ≠ 0 := fun h0 => by simp [h0] at h1
  have hlt {a b : F[X]} {n m : ℕ} (ha : a.degree ≤ n) (hb : b.natDegree ≤ m)
      (h : n + m < M.natDegree) : a.degree + b.degree < M.degree :=
    (add_le_add ha (degree_le_of_natDegree_le hb)).trans_lt <| by
      rw [degree_eq_natDegree hM]
      exact_mod_cast h
  exact mul_eq_mul_of_dvd_sub_of_degree_lt hp hq (hlt hpn hqd h1) (hlt hqn hpd h2)

/-- Modular uniqueness of reduced monic pairs under numerator/denominator degree bounds
`N + D < M.natDegree`. -/
theorem eq_of_dvd_sub_of_bounds [Field F] {M u : F[X]} {N D : ℕ} {p q : PolyRat F}
    (hMp : p.den.Monic) (hMq : q.den.Monic) (hcp : IsCoprime p.num p.den)
    (hcq : IsCoprime q.num q.den) (hpn : p.num.degree ≤ N) (hqn : q.num.degree ≤ N)
    (hpd : p.den.natDegree ≤ D) (hqd : q.den.natDegree ≤ D) (hMdeg : N + D < M.natDegree)
    (hp : M ∣ p.num - p.den * u) (hq : M ∣ q.num - q.den * u) : p = q :=
  eq_of_isCoprime_of_monic (mul_eq_mul_of_dvd_sub_of_bounds hp hq hpn hqn hpd hqd hMdeg hMdeg)
    hcp hcq hMp hMq

/-- Modular uniqueness of reduced monic pairs under `PolyRat.height`: if `M ∣ p.num - p.den * u`,
`M ∣ q.num - q.den * u`, and `p.height + q.height < M.natDegree`, then `p = q`. -/
theorem eq_of_dvd_sub_of_height_lt [Field F] {M u : F[X]} {p q : PolyRat F}
    (hMp : p.den.Monic) (hMq : q.den.Monic) (hcp : IsCoprime p.num p.den)
    (hcq : IsCoprime q.num q.den) (hMdeg : p.height + q.height < M.natDegree)
    (hp : M ∣ p.num - p.den * u) (hq : M ∣ q.num - q.den * u) : p = q :=
  eq_of_isCoprime_of_monic (mul_eq_mul_of_dvd_sub_of_bounds hp hq
    (degree_le_of_natDegree_le p.natDegree_num_le_height)
    (degree_le_of_natDegree_le q.natDegree_num_le_height) p.natDegree_den_le_height
    q.natDegree_den_le_height hMdeg (by omega)) hcp hcq hMp hMq

end HeightAndUniqueness

section EuclideanReconstruction

variable {F : Type*} [Field F]

private structure PolyEuclidState (F : Type*) [Field F] where
  r0 : F[X]
  t0 : F[X]
  r1 : F[X]
  t1 : F[X]

private lemma polyMeasure_mod_lt {r0 r1 : F[X]} (hr1 : r1 ≠ 0) :
    letI := Classical.decEq F
    (r0 % r1).natDegree + (if r0 % r1 = 0 then 0 else 1) <
      r1.natDegree + (if r1 = 0 then 0 else 1) := by
  classical
  by_cases hr2 : r0 % r1 = 0
  · simp [hr1, hr2]
  · have := natDegree_lt_natDegree hr2 (degree_mod_lt r0 hr1)
    simp only [hr1, hr2, ↓reduceIte]
    omega

open Classical in
private def polyLoop (N : ℕ) (r0 t0 r1 t1 : F[X]) : PolyEuclidState F :=
  if _h : (N : WithBot ℕ) < r1.degree then
    let q := r0 / r1
    let r2 := r0 % r1
    let t2 := t0 - q * t1
    polyLoop N r1 t1 r2 t2
  else
    ⟨r0, t0, r1, t1⟩
termination_by r1.natDegree + (if r1 = 0 then 0 else 1)
decreasing_by
  have hr1 : r1 ≠ 0 := fun h0 => by simp [h0] at _h
  have hlt := polyMeasure_mod_lt (r0 := r0) hr1
  simpa only [EuclideanDomain.mod_eq_zero] using hlt

private structure PolyStepInv (M u r0 t0 r1 t1 : F[X]) : Prop where
  r0_ne : r0 ≠ 0
  r1_lt : r1.degree < r0.degree
  mod0 : M ∣ r0 - t0 * u
  mod1 : M ∣ r1 - t1 * u
  t_deg : t0.degree < t1.degree
  t1_ne : t1 ≠ 0
  bezout : ∃ s : ℤ, s * s = 1 ∧ r0 * t1 - r1 * t0 = (s : F[X]) * M

private theorem polyStepInv_step {M u r0 t0 r1 t1 : F[X]} {N : ℕ}
    (hinv : PolyStepInv M u r0 t0 r1 t1) (hlt : (N : WithBot ℕ) < r1.degree) :
    PolyStepInv M u r1 t1 (r0 % r1) (t0 - (r0 / r1) * t1) := by
  have hr1_nz : r1 ≠ 0 := fun h0 => by simp [h0] at hlt
  have hmod_eq : r0 % r1 = r0 - r1 * (r0 / r1) := EuclideanDomain.mod_eq_sub_mul_div r0 r1
  have hq_nz : r0 / r1 ≠ 0 := by
    rw [ne_eq, Polynomial.div_eq_zero_iff hr1_nz]
    exact not_lt_of_gt hinv.r1_lt
  have hq_nat : 0 < (r0 / r1).natDegree := by
    have h := degree_add_div hr1_nz hinv.r1_lt.le
    rw [degree_eq_natDegree hr1_nz, degree_eq_natDegree hinv.r0_ne,
      degree_eq_natDegree hq_nz] at h
    have h' : r1.natDegree + (r0 / r1).natDegree = r0.natDegree := by exact_mod_cast h
    have := natDegree_lt_natDegree hr1_nz hinv.r1_lt
    omega
  have ht_mul : t1.degree < (r0 / r1 * t1).degree :=
    degree_lt_degree (by rw [natDegree_mul hq_nz hinv.t1_ne]; omega)
  have ht2 : t1.degree < (t0 - (r0 / r1) * t1).degree := by
    rwa [degree_sub_eq_right_of_degree_lt (hinv.t_deg.trans ht_mul)]
  refine
    { r0_ne := hr1_nz
      r1_lt := degree_mod_lt r0 hr1_nz
      mod0 := hinv.mod1
      mod1 := ?_
      t_deg := ht2
      t1_ne := ne_zero_of_degree_gt ht2
      bezout := ?_ }
  · rw [hmod_eq]
    convert dvd_sub hinv.mod0 (dvd_mul_of_dvd_right hinv.mod1 (r0 / r1)) using 1
    ring
  · obtain ⟨s, hs1, hs2⟩ := hinv.bezout
    refine ⟨-s, by linear_combination hs1, ?_⟩
    rw [hmod_eq]
    push_cast
    linear_combination -hs2

open Classical in
private theorem polyLoop_spec {M u r0 t0 r1 t1 : F[X]} {N : ℕ}
    (hinv : PolyStepInv M u r0 t0 r1 t1) :
    let st := polyLoop N r0 t0 r1 t1
    PolyStepInv M u st.r0 st.t0 st.r1 st.t1 ∧ st.r1.degree ≤ (N : WithBot ℕ) ∧
      ((N : WithBot ℕ) < r0.degree → (N : WithBot ℕ) < st.r0.degree) := by
  dsimp only
  rw [polyLoop]
  by_cases hlt : (N : WithBot ℕ) < r1.degree
  · simp only [hlt, ↓reduceDIte]
    obtain ⟨hs, hle, hor⟩ := polyLoop_spec (M := M) (u := u) (N := N) (polyStepInv_step hinv hlt)
    exact ⟨hs, hle, fun _ => hor hlt⟩
  · simp only [hlt, ↓reduceDIte]
    exact ⟨hinv, not_lt.mp hlt, id⟩
termination_by r1.natDegree + (if r1 = 0 then 0 else 1)
decreasing_by
  have hr1 : r1 ≠ 0 := fun h0 => by simp [h0] at hlt
  have hlt' := polyMeasure_mod_lt (r0 := r0) hr1
  simpa only [EuclideanDomain.mod_eq_zero] using hlt'

open Classical in
/-- Extended-Euclidean rational-function reconstruction over `F[X]` modulo `M`. Returns `some p`
with `p.den.Monic`, `p.num.degree ≤ N`, `p.den.natDegree ≤ D`, `IsCoprime p.num p.den`,
`IsCoprime p.den M`, and `M ∣ p.num - p.den * u`, when the Euclidean sequence meets the bounds. -/
def reconstruct (M u : F[X]) (N D : ℕ) : Option (PolyRat F) :=
  if M = 0 then none
  else
    let st := polyLoop N M 0 (u % M) 1
    if st.t1.natDegree ≤ D ∧ IsUnit (EuclideanDomain.gcd st.t1 M) then
      let c := st.t1.leadingCoeff⁻¹
      some ⟨Polynomial.C c * st.r1, Polynomial.C c * st.t1⟩
    else
      none

private theorem initial_polyStepInv {M : F[X]} (hM : M ≠ 0) (u : F[X]) :
    PolyStepInv M u M 0 (u % M) 1 := by
  refine
    { r0_ne := hM
      r1_lt := Polynomial.degree_mod_lt u hM
      mod0 := by simp
      mod1 := ?_
      t_deg := by simp
      t1_ne := one_ne_zero
      bezout := ⟨1, rfl, by simp⟩ }
  rw [one_mul, EuclideanDomain.mod_eq_sub_mul_div u M, sub_sub_cancel_left]
  exact dvd_neg.mpr (dvd_mul_right M _)

open Classical in
/-- Soundness of `PolyRat.reconstruct`. -/
theorem reconstruct_eq_some {M u : F[X]} {N D : ℕ} {p : PolyRat F}
    (hp : reconstruct M u N D = some p) :
    M ≠ 0 ∧ p.den.Monic ∧ p.num.degree ≤ N ∧ p.den.natDegree ≤ D ∧
      IsCoprime p.num p.den ∧ IsCoprime p.den M ∧ M ∣ p.num - p.den * u := by
  by_cases hM : M = 0
  · simp [reconstruct, hM] at hp
  obtain ⟨hinv, hrN, -⟩ := polyLoop_spec (M := M) (u := u) (N := N) (initial_polyStepInv hM u)
  simp only [reconstruct, hM, ↓reduceIte] at hp
  set st := polyLoop N M 0 (u % M) 1
  split_ifs at hp with hcond
  obtain ⟨htD, hgcd⟩ := hcond
  cases hp
  have hlc : st.t1.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hinv.t1_ne
  have hc_ne : st.t1.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero hlc
  have hCunit : IsUnit (C st.t1.leadingCoeff⁻¹) := isUnit_C.mpr hc_ne.isUnit
  have hcop_tM : IsCoprime st.t1 M := EuclideanDomain.gcd_isUnit_iff.mp hgcd
  -- the Bezout relation `r₀ t₁ - r₁ t₀ = ± M` makes `r₁` and `t₁` coprime
  have hcop_rt : IsCoprime st.r1 st.t1 := by
    obtain ⟨a, b, hab⟩ := hcop_tM
    obtain ⟨s, hs1, hs2⟩ := hinv.bezout
    have hss : (s : F[X]) * s = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → F[X]) hs1
    exact ⟨-(b * s * st.t0), a + b * s * st.r0,
      by linear_combination hab + b * s * hs2 + b * M * hss⟩
  refine ⟨hM, monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc),
    (degree_C_mul hc_ne).trans_le hrN, (natDegree_C_mul hc_ne).trans_le htD,
    (isCoprime_mul_unit_left hCunit _ _).mpr hcop_rt,
    (isCoprime_mul_unit_left_left hCunit _ _).mpr hcop_tM, ?_⟩
  rw [mul_assoc, ← mul_sub]
  exact dvd_mul_of_dvd_right hinv.mod1 _

open Classical in
/-- Completeness of `PolyRat.reconstruct`: recovers `some p` whenever `N + D < M.natDegree`,
`p.den.Monic`, `IsCoprime p.num p.den`, `IsCoprime p.den M`, `p.num.degree ≤ N`,
`p.den.natDegree ≤ D`, and `M ∣ p.num - p.den * u`. -/
theorem reconstruct_of_eq {M u : F[X]} {N D : ℕ} {p : PolyRat F}
    (hMp : p.den.Monic) (hcp : IsCoprime p.num p.den) (hcM : IsCoprime p.den M)
    (hpn : p.num.degree ≤ N) (hpd : p.den.natDegree ≤ D) (hMdeg : N + D < M.natDegree)
    (hmod : M ∣ p.num - p.den * u) : reconstruct M u N D = some p := by
  have hM : M ≠ 0 := fun h0 => by simp [h0] at hMdeg
  obtain ⟨hinv, hrN, hcase⟩ := polyLoop_spec (M := M) (u := u) (N := N) (initial_polyStepInv hM u)
  simp only [reconstruct, hM, ↓reduceIte]
  set st := polyLoop N M 0 (u % M) 1
  -- the loop stops with `st.r1.degree ≤ N < st.r0.degree`
  have hr0 : N < st.r0.natDegree := coe_lt_degree.1 (hcase (coe_lt_degree.2 (by omega)))
  -- Cramer's rule: the Bezout matrix of the last two rows has determinant `± M`
  obtain ⟨s, hs1, hs2⟩ := hinv.bezout
  have hss : (s : F[X]) * s = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → F[X]) hs1
  obtain ⟨x, hx⟩ : M ∣ s * (p.num * st.t1 - p.den * st.r1) := by
    refine dvd_mul_of_dvd_right ?_ _
    convert dvd_sub (dvd_mul_of_dvd_left hmod st.t1) (dvd_mul_of_dvd_right hinv.mod1 p.den)
      using 1
    ring
  obtain ⟨y, hy⟩ : M ∣ s * (p.den * st.r0 - p.num * st.t0) := by
    refine dvd_mul_of_dvd_right ?_ _
    convert dvd_sub (dvd_mul_of_dvd_right hinv.mod0 p.den) (dvd_mul_of_dvd_left hmod st.t0)
      using 1
    ring
  have ha : p.num = x * st.r0 + y * st.r1 := mul_left_cancel₀ hM <| by
    linear_combination st.r0 * hx + st.r1 * hy - (s : F[X]) * p.num * hs2 - M * p.num * hss
  have hb : p.den = x * st.t0 + y * st.t1 := mul_left_cancel₀ hM <| by
    linear_combination st.t0 * hx + st.t1 * hy - (s : F[X]) * p.den * hs2 - M * p.den * hss
  -- `x = 0`: otherwise `st.t1.natDegree ≤ p.den.natDegree`, so the cross product vanishes
  have hx0 : x = 0 := by
    by_contra hx0
    have hxr : p.num.degree < (x * st.r0).degree :=
      hpn.trans_lt (coe_lt_degree.2 (by rw [natDegree_mul hx0 hinv.r0_ne]; omega))
    have hyr : (y * st.r1).degree = (x * st.r0).degree := by
      rw [show y * st.r1 = p.num - x * st.r0 by rw [ha]; ring]
      exact degree_sub_eq_right_of_degree_lt hxr
    obtain ⟨hy0, hr1⟩ := mul_ne_zero_iff.1 (ne_zero_of_degree_gt (hyr ▸ hxr))
    have h1 := natDegree_eq_of_degree_eq hyr
    rw [natDegree_mul hy0 hr1, natDegree_mul hx0 hinv.r0_ne] at h1
    have h2 := natDegree_lt_natDegree hr1 hinv.r1_lt
    have h3 := natDegree_le_natDegree hinv.t_deg.le
    have h4 := natDegree_mul_le (p := x) (q := st.t0)
    have hden := natDegree_add_eq_right_of_degree_lt (p := x * st.t0) (q := y * st.t1)
      (degree_lt_degree (by rw [natDegree_mul hy0 hinv.t1_ne]; omega))
    rw [← hb, natDegree_mul hy0 hinv.t1_ne] at hden
    have hcross : p.num * st.t1 = st.r1 * p.den :=
      mul_eq_mul_of_dvd_sub_of_bounds (q := ⟨st.r1, st.t1⟩) hmod hinv.mod1 hpn hrN hpd
        (by dsimp only; omega) hMdeg hMdeg
    refine hx0 ((mul_eq_zero.1 ?_).resolve_left hM)
    rw [← hx, hcross]
    ring
  rw [hx0, zero_mul, zero_add] at ha hb
  obtain ⟨c, hc, rfl⟩ := isUnit_iff.1 (hcp.isUnit_of_dvd' ⟨_, ha⟩ ⟨_, hb⟩)
  have hlead : c * st.t1.leadingCoeff = 1 := by
    rw [← leadingCoeff_C_mul_of_isUnit hc, ← hb]
    exact hMp
  rw [hb] at hcM hpd
  rw [natDegree_C_mul hc.ne_zero] at hpd
  rw [ite_eq_left ⟨hpd, EuclideanDomain.gcd_isUnit_iff.mpr hcM.of_mul_left_right⟩,
    inv_eq_of_mul_eq_one_left hlead]
  exact congrArg some (PolyRat.ext ha.symm hb.symm)

end EuclideanReconstruction

section CauchyAndFiniteField

variable {F : Type*} [Field F]

open Classical in
/-- Cauchy rational-function interpolation from evaluations `vals : F → F` at nodes `s : Finset F`
via `Lagrange.interpolate` and `PolyRat.reconstruct`. -/
def cauchy (s : Finset F) (vals : F → F) (N D : ℕ) : Option (PolyRat F) :=
  reconstruct (∏ a ∈ s, (X - C a)) (Lagrange.interpolate s id vals) N D

open scoped Function in
open Classical in
private theorem dvd_prod_X_sub_C_iff {s : Finset F} {f : F[X]} :
    (∏ a ∈ s, (X - C a)) ∣ f ↔ ∀ a ∈ s, f.eval a = 0 := by
  refine ⟨fun hdvd a ha => Polynomial.dvd_iff_isRoot.mp
    (dvd_trans (Finset.dvd_prod_of_mem (fun x => X - C x) ha) hdvd), fun h => ?_⟩
  exact Finset.prod_dvd_of_coprime
    ((Polynomial.pairwise_coprime_X_sub_C Function.injective_id).set_pairwise _)
    fun a ha => Polynomial.dvd_iff_isRoot.mpr (h a ha)

open Classical in
private theorem isCoprime_prod_X_sub_C_iff {s : Finset F} {b : F[X]} :
    IsCoprime b (∏ a ∈ s, (X - C a)) ↔ ∀ a ∈ s, b.eval a ≠ 0 := by
  rw [IsCoprime.prod_right_iff]
  exact forall₂_congr fun a _ => isCoprime_comm.trans <|
    (irreducible_X_sub_C a).coprime_iff_not_dvd.trans (not_congr dvd_iff_isRoot)

open Classical in
/-- Soundness of `PolyRat.cauchy`: any output `p` satisfies `p.den.Monic`, `p.num.degree ≤ N`,
`p.den.natDegree ≤ D`, `p.den.eval a ≠ 0` and `p.num.eval a / p.den.eval a = vals a` for all
`a ∈ s`. -/
theorem cauchy_eq_some {s : Finset F} {vals : F → F} {N D : ℕ} {p : PolyRat F}
    (hp : cauchy s vals N D = some p) :
    p.den.Monic ∧ p.num.degree ≤ N ∧ p.den.natDegree ≤ D ∧ IsCoprime p.num p.den ∧
      ∀ a ∈ s, p.den.eval a ≠ 0 ∧ p.num.eval a / p.den.eval a = vals a := by
  obtain ⟨-, hmonic, hdegN, hdegD, hcop, hcM, hmod⟩ := reconstruct_eq_some hp
  refine ⟨hmonic, hdegN, hdegD, hcop, fun a ha => ?_⟩
  have hda : p.den.eval a ≠ 0 := isCoprime_prod_X_sub_C_iff.mp hcM a ha
  have hev := dvd_prod_X_sub_C_iff.mp hmod a ha
  have hlag : (Lagrange.interpolate s id vals).eval a = vals a :=
    Lagrange.eval_interpolate_at_node vals Function.injective_id.injOn ha
  rw [eval_sub, eval_mul, hlag, sub_eq_zero] at hev
  exact ⟨hda, by rw [hev, mul_div_cancel_left₀ _ hda]⟩

open Classical in
/-- Completeness of `PolyRat.cauchy`: if `N + D < s.card`, `p.den.Monic`, `IsCoprime p.num p.den`,
`p.num.degree ≤ N`, `p.den.natDegree ≤ D`, and `p.den.eval a ≠ 0` with
`p.num.eval a / p.den.eval a = vals a` on all `a ∈ s`, then `cauchy s vals N D = some p`. -/
theorem cauchy_of_eq {s : Finset F} {vals : F → F} {N D : ℕ} {p : PolyRat F}
    (hMp : p.den.Monic) (hcp : IsCoprime p.num p.den) (hpn : p.num.degree ≤ N)
    (hpd : p.den.natDegree ≤ D) (hs : N + D < s.card)
    (heval : ∀ a ∈ s, p.den.eval a ≠ 0 ∧ p.num.eval a / p.den.eval a = vals a) :
    cauchy s vals N D = some p := by
  have hcM : IsCoprime p.den (∏ a ∈ s, (X - C a)) :=
    isCoprime_prod_X_sub_C_iff.mpr fun a ha => (heval a ha).1
  have hmod : (∏ a ∈ s, (X - C a)) ∣ p.num - p.den * Lagrange.interpolate s id vals :=
    dvd_prod_X_sub_C_iff.mpr fun a ha => by
      obtain ⟨hda, hdiv⟩ := heval a ha
      have hlag : (Lagrange.interpolate s id vals).eval a = vals a :=
        Lagrange.eval_interpolate_at_node vals Function.injective_id.injOn ha
      rw [eval_sub, eval_mul, hlag, ← hdiv, mul_div_cancel₀ _ hda, sub_self]
  have hdegM : (∏ a ∈ s, (X - C a)).natDegree = s.card :=
    (natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C a).trans (by simp)
  exact reconstruct_of_eq hMp hcp hcM hpn hpd (hdegM ▸ hs) hmod

/-- Finite-field specialization of `PolyRat.reconstruct` over `(ZMod p)[X]` for prime `p`. -/
theorem reconstruct_zmod_of_eq {p : ℕ} [Fact p.Prime] {M u : (ZMod p)[X]} {N D : ℕ}
    {q : PolyRat (ZMod p)} (hMq : q.den.Monic) (hcq : IsCoprime q.num q.den)
    (hcM : IsCoprime q.den M) (hqn : q.num.degree ≤ N) (hqd : q.den.natDegree ≤ D)
    (hMdeg : N + D < M.natDegree) (hmod : M ∣ q.num - q.den * u) :
    reconstruct M u N D = some q :=
  reconstruct_of_eq hMq hcq hcM hqn hqd hMdeg hmod

end CauchyAndFiniteField

end

end PolyRat

end Polynomial
