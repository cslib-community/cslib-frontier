/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap

/-!
# Shared Degree Bounds and Variable-Specialization Helpers

Internal foundation for the Johnson-bound proximity-gap split: the `Z`-degree measures `degZ₂`
and `degZ`, the subadditive `DegBound` resultant-degree bundler, the curve polynomial `curveWord`,
and specialization homomorphisms `evZ`, `evZ₁`, and `evZ₂`. Imported privately by the sibling
submodules under `CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson`.

## Main definitions

* `Cslib.Code.ProximityGap.degZ₂`, `Cslib.Code.ProximityGap.degZ`: `Z`-degree measures.
* `Cslib.Code.ProximityGap.DegBound`: generic degree-bound interface used for resultant bounds.
* `Cslib.Code.ProximityGap.curveWord`: degree-`r` curve polynomial `w_i(Z)`.
* `Cslib.Code.ProximityGap.evZ`, `Cslib.Code.ProximityGap.evZ₁`, `Cslib.Code.ProximityGap.evZ₂`:
  specialization homomorphisms `Z ↦ z`.
-/

public section

namespace Cslib.Code.ProximityGap

open Finset Polynomial Polynomial.Bivariate

/-- Ring equivalence moving the innermost variable `Z` of `R[Z][X][Y]` to the outermost position
`(R[X][Y])[Z]`. -/
private noncomputable def toOuterZ (R : Type*) [CommSemiring R] : R[X][X][X] ≃+* R[X][X][X] :=
  (Polynomial.mapEquiv (Bivariate.swap (R := R)).toRingEquiv).trans
    (Bivariate.swap (R := R[X])).toRingEquiv

private theorem coeff_coeff_coeff_toOuterZ {R : Type*} [CommSemiring R] (Q : R[X][X][X])
    (t a b : ℕ) :
    ((((toOuterZ R Q).coeff t).coeff b).coeff a) = ((Q.coeff b).coeff a).coeff t := by
  change (((Bivariate.swap (Q.map (Bivariate.swap (R := R)).toRingEquiv.toRingHom)).coeff t).coeff
    b).coeff a = _
  rw [coeff_coeff_swap, coeff_map]
  exact coeff_coeff_swap (Q.coeff b) t a

/-- `Z`-degree of `f ∈ R[Z][X]`. -/
noncomputable def degZ₂ {R : Type*} [CommSemiring R] (f : R[X][X]) : ℕ :=
  (Bivariate.swap f).natDegree

theorem degZ₂_mul {R : Type*} [CommRing R] [IsDomain R] {f g : R[X][X]}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    degZ₂ (f * g) = degZ₂ f + degZ₂ g := by
  rw [degZ₂, map_mul, natDegree_mul ((map_ne_zero_iff _ Bivariate.swap.injective).2 hf)
    ((map_ne_zero_iff _ Bivariate.swap.injective).2 hg)]
  rfl

theorem degZ₂_le_iff {R : Type*} [CommSemiring R] {f : R[X][X]} {B : ℕ} :
    degZ₂ f ≤ B ↔ ∀ a, (f.coeff a).natDegree ≤ B :=
  Bivariate.natDegree_swap_le_iff f B

theorem degZ₂_C {R : Type*} [CommSemiring R] (p : R[X]) :
    degZ₂ (C p) = p.natDegree :=
  le_antisymm (degZ₂_le_iff.2 fun a => by rw [coeff_C]; split_ifs <;> simp)
    (by simpa using degZ₂_le_iff.1 (le_refl (degZ₂ (C p))) 0)

theorem degZ₂_X {R : Type*} [CommSemiring R] :
    degZ₂ (X : R[X][X]) = 0 :=
  Nat.eq_zero_of_le_zero (degZ₂_le_iff.2 fun a => by rw [coeff_X]; split_ifs <;> simp)

theorem degZ₂_hasseDeriv_le {R : Type*} [CommSemiring R] (j : ℕ) (f : R[X][X]) :
    degZ₂ (hasseDeriv j f) ≤ degZ₂ f :=
  degZ₂_le_iff.2 fun a => by
    rw [hasseDeriv_coeff,
      show (((a + j).choose j : ℕ) : R[X]) = C (((a + j).choose j : ℕ) : R) by simp]
    exact natDegree_C_mul_le _ _ |>.trans (degZ₂_le_iff.1 le_rfl (a + j))

theorem degZ₂_derivative_le {R : Type*} [CommSemiring R] (f : R[X][X]) :
    degZ₂ f.derivative ≤ degZ₂ f :=
  hasseDeriv_one' (f := f) ▸ degZ₂_hasseDeriv_le 1 f

theorem natDegree_eval_C_le_degZ₂ {R : Type*} [CommSemiring R] (f : R[X][X]) (x : R) :
    (f.eval (C x)).natDegree ≤ degZ₂ f := by
  rw [eval_eq_sum_range]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun a _ => natDegree_mul_le.trans ?_)
  rw [← C_pow, natDegree_C, add_zero]
  exact degZ₂_le_iff.1 le_rfl a

theorem degZ₂_taylor_C_le {R : Type*} [CommRing R] (f : R[X][X]) (x : R) :
    degZ₂ (taylor (C x) f) ≤ degZ₂ f :=
  degZ₂_le_iff.2 fun a => by
    rw [taylor_coeff]
    exact (natDegree_eval_C_le_degZ₂ _ x).trans (degZ₂_hasseDeriv_le a f)

/-- `Z`-degree of `Q ∈ R[Z][X][Y]`. -/
noncomputable def degZ {R : Type*} [CommSemiring R] (Q : R[X][X][X]) : ℕ :=
  (toOuterZ R Q).natDegree

theorem degZ_le_iff {R : Type*} [CommSemiring R] {Q : R[X][X][X]} {B : ℕ} :
    degZ Q ≤ B ↔ ∀ a b, ((Q.coeff b).coeff a).natDegree ≤ B := by
  rw [degZ, natDegree_le_iff_coeff_eq_zero]
  refine ⟨fun h a b => natDegree_le_iff_coeff_eq_zero.2 fun t ht => by
    simpa [coeff_coeff_coeff_toOuterZ] using
      congrArg (fun p : R[X][X] => (p.coeff b).coeff a) (h t ht),
    fun h t ht => by
      ext b a; rw [coeff_coeff_coeff_toOuterZ, coeff_zero, coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt ((h a b).trans_lt ht)⟩

private theorem degZ_mul {R : Type*} [CommRing R] [IsDomain R] {A B : R[X][X][X]}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    degZ (A * B) = degZ A + degZ B := by
  rw [degZ, map_mul, natDegree_mul ((map_ne_zero_iff _ (toOuterZ R).injective).2 hA)
    ((map_ne_zero_iff _ (toOuterZ R).injective).2 hB)]
  rfl

theorem degZ_le_of_dvd {R : Type*} [CommRing R] [IsDomain R] {A B : R[X][X][X]}
    (hB : B ≠ 0) (hdvd : A ∣ B) :
    degZ A ≤ degZ B := by
  rcases hdvd with ⟨C, rfl⟩
  rw [degZ_mul (left_ne_zero_of_mul hB) (right_ne_zero_of_mul hB)]
  exact Nat.le_add_right _ _

theorem degZ₂_coeff_le_degZ {R : Type*} [CommSemiring R] (Q : R[X][X][X]) (b : ℕ) :
    degZ₂ (Q.coeff b) ≤ degZ Q :=
  degZ₂_le_iff.2 fun a => degZ_le_iff.1 le_rfl a b

/-- Bundler for subadditive degree-like measures `deg : R → ℕ` (covers `natDegree` in `R[X]` and
`degZ₂` in `R[X][X]`). -/
structure DegBound (R : Type*) [CommRing R] where
  /-- Degree function mapping ring elements to `ℕ`. -/
  deg : R → ℕ
  /-- Degree of `0` is `0`. -/
  zero : deg 0 = 0
  /-- Degree of `1` is `0`. -/
  one : deg 1 = 0
  /-- Negation preserves degree. -/
  neg : ∀ x, deg (-x) = deg x
  /-- Subadditivity under addition. -/
  add_le : ∀ x y, deg (x + y) ≤ max (deg x) (deg y)
  /-- Subadditivity under multiplication. -/
  mul_le : ∀ x y, deg (x * y) ≤ deg x + deg y

/-- Standard polynomial degree packaged as a `DegBound` on `R[X]`. -/
@[expose] noncomputable def DegBound.natDegree (R : Type*) [CommRing R] : DegBound R[X] where
  deg := Polynomial.natDegree
  zero := natDegree_zero
  one := natDegree_one
  neg := natDegree_neg
  add_le := natDegree_add_le
  mul_le := fun _ _ => natDegree_mul_le

/-- `Z`-degree packaged as a `DegBound` on `R[X][X]`. -/
@[expose] noncomputable def DegBound.degZ₂ (R : Type*) [CommRing R] : DegBound R[X][X] where
  deg := ProximityGap.degZ₂
  zero := by simp [ProximityGap.degZ₂]
  one := by simp [ProximityGap.degZ₂]
  neg _ := by simp [ProximityGap.degZ₂]
  add_le f g := by
    simpa only [ProximityGap.degZ₂, map_add] using
      natDegree_add_le (Bivariate.swap f) (Bivariate.swap g)
  mul_le f g := by
    simpa only [ProximityGap.degZ₂, map_mul] using
      (natDegree_mul_le (p := Bivariate.swap f) (q := Bivariate.swap g))

theorem DegBound.sub_le {R : Type*} [CommRing R] (db : DegBound R) (x y : R) :
    db.deg (x - y) ≤ max (db.deg x) (db.deg y) :=
  sub_eq_add_neg x y ▸ (db.add_le x (-y)).trans_eq (by rw [db.neg])

theorem DegBound.sum_le {R : Type*} [CommRing R] (db : DegBound R) {α : Type*}
    (s : Finset α) (u : α → R) {B : ℕ} (h : ∀ i ∈ s, db.deg (u i) ≤ B) :
    db.deg (∑ i ∈ s, u i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [db.zero]
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (db.add_le _ _).trans
      (max_le (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi)))

theorem DegBound.pow_le {R : Type*} [CommRing R] (db : DegBound R) (x : R) (n : ℕ) :
    db.deg (x ^ n) ≤ n * db.deg x := by
  induction n with
  | zero => simp [db.one]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (db.mul_le _ _).trans (Nat.add_le_add_right ih _)

private theorem DegBound.prod_le {R : Type*} [CommRing R] (db : DegBound R) {α : Type*}
    (s : Finset α) (u : α → R) (B : α → ℕ) (h : ∀ i ∈ s, db.deg (u i) ≤ B i) :
    db.deg (∏ i ∈ s, u i) ≤ ∑ i ∈ s, B i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [db.one]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (db.mul_le _ _).trans
      (Nat.add_le_add (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi)))

private theorem DegBound.natCast_eq_zero {R : Type*} [CommRing R] (db : DegBound R) (n : ℕ) :
    db.deg n = 0 := by
  induction n with
  | zero => simpa using db.zero
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Nat.eq_zero_of_le_zero ((db.add_le n 1).trans (by simp [ih, db.one]))

private theorem DegBound.derivative_coeff_le {R : Type*} [CommRing R] (db : DegBound R)
    {f : R[X]} {B : ℕ} (hf : ∀ b, db.deg (f.coeff b) ≤ B) (b : ℕ) :
    db.deg (f.derivative.coeff b) ≤ B := by
  rw [coeff_derivative]
  refine (db.mul_le _ _).trans ?_
  rw [← Nat.cast_succ, db.natCast_eq_zero (b + 1), add_zero]
  exact hf (b + 1)

theorem DegBound.resultant_le {R : Type*} [CommRing R] (db : DegBound R)
    {f g : R[X]} (m n : ℕ) {Bf Bg : ℕ}
    (hf : ∀ i, db.deg (f.coeff i) ≤ Bf) (hg : ∀ i, db.deg (g.coeff i) ≤ Bg) :
    db.deg (Polynomial.resultant f g m n) ≤ m * Bg + n * Bf := by
  rw [Polynomial.resultant, Matrix.det_apply]
  refine db.sum_le _ _ fun σ _ => ?_
  have hz : ∀ (s : ℤˣ) (x : R), db.deg (s • x) = db.deg x := fun s x => by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp [Units.smul_def, db.neg]
  rw [hz]
  let bnd : Fin (m + n) → ℕ := Fin.addCases (fun _ => Bg) (fun _ => Bf)
  refine (db.prod_le Finset.univ _ bnd fun j _ => ?_).trans_eq (by simp [bnd, Fin.sum_univ_add])
  induction j using Fin.addCases with
  | left j =>
    simp only [bnd, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs <;> [exact hg _; exact db.zero ▸ Nat.zero_le _]
  | right j =>
    simp only [bnd, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs <;> [exact hf _; exact db.zero ▸ Nat.zero_le _]

theorem DegBound.leadingCoeff_mul_resultant_derivative_le {R : Type*} [CommRing R]
    (db : DegBound R) {f : R[X]} (hf_deg : 1 ≤ f.natDegree) {B : ℕ}
    (hf : ∀ b, db.deg (f.coeff b) ≤ B) :
    db.deg (f.leadingCoeff *
        Polynomial.resultant f f.derivative f.natDegree f.derivative.natDegree) ≤
      2 * f.natDegree * B := by
  have hf'_deg := Polynomial.natDegree_derivative_le f
  refine (db.mul_le _ _).trans <| (Nat.add_le_add (hf f.natDegree)
    (db.resultant_le f.natDegree f.derivative.natDegree hf (db.derivative_coeff_le hf))).trans ?_
  rw [← add_mul, show B + (f.natDegree + f.derivative.natDegree) * B =
    (1 + (f.natDegree + f.derivative.natDegree)) * B by ring]
  exact Nat.mul_le_mul_right B (by omega)

/-- Shared root-counting and resultant helpers. -/
theorem card_filter_eval_eq_zero_le {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] {p : R[X]} (hp : p ≠ 0) (T : Finset R) :
    #(T.filter fun z => p.eval z = 0) ≤ p.natDegree :=
  (card_le_card fun _ hz => Multiset.mem_toFinset.2 ((mem_roots hp).2 (mem_filter.1 hz).2)).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))

theorem resultant_ne_zero_of_isCoprime_map {R K : Type*} [CommRing R]
    [Field K] (φ : R →+* K) (hφ : Function.Injective φ) {f g : R[X]}
    (hcop : IsCoprime (f.map φ) (g.map φ)) :
    Polynomial.resultant f g f.natDegree g.natDegree ≠ 0 := fun h0 =>
  (Polynomial.resultant_eq_zero_iff.1 (by
    change Polynomial.resultant (f.map φ) (g.map φ) (f.map φ).natDegree (g.map φ).natDegree = 0
    rw [Polynomial.natDegree_map_eq_of_injective hφ, Polynomial.natDegree_map_eq_of_injective hφ,
      Polynomial.resultant_map_map, h0, map_zero])).2 hcop

theorem coeff_sum_Icc_C_mul_X_pow {R : Type*} [Semiring R] (a b k : ℕ) (f : ℕ → R) :
    (∑ j ∈ Icc a b, C (f j) * X ^ j).coeff k = if a ≤ k ∧ k ≤ b then f k else 0 := by
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_congr rfl fun j (_ : j ∈ Icc a b) => if_congr (eq_comm (a := k) (b := j)) rfl rfl,
    Finset.sum_ite_eq', mem_Icc]

section CurveEval

variable {F : Type*} [Field F]

/-- Curve polynomial `w_i(Z) = ∑_j u_j(i) Z^j ∈ F[Z]`, built via `Polynomial.ofFn`. -/
noncomputable abbrev curveWord [DecidableEq F] {ι : Type*} {r : ℕ}
    (u : Fin (r + 1) → (ι → F)) (i : ι) : F[X] :=
  Polynomial.ofFn (r + 1) (fun j => u j i)

/-- Specialization `Z ↦ z` on `F[Z]`. -/
@[expose] noncomputable def evZ (z : F) : F[X] →+* F := Polynomial.evalRingHom z

/-- Specialization `Z ↦ z` on `F[Z][X]`. -/
@[expose] noncomputable def evZ₁ (z : F) : F[X][X] →+* F[X] := Polynomial.mapRingHom (evZ z)

/-- Specialization `Z ↦ z` on `F[Z][X][Y]`. -/
@[expose] noncomputable def evZ₂ (z : F) : F[X][X][X] →+* F[X][X] := Polynomial.mapRingHom (evZ₁ z)

theorem exists_mem_eval_map_eq_zero {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (ms : Multiset R[X]) (y : S) (h : (ms.prod.map φ).eval y = 0) :
    ∃ f ∈ ms, (f.map φ).eval y = 0 :=
  Multiset.mem_map.1 <| Multiset.prod_eq_zero_iff.1 <| by
    rwa [Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map] at h

theorem ceil_div_le_card_of_sum_le {ι : Type*} {W : ι → ℕ} {M B_W : ℕ} (hM : 0 < M)
    (hW_le : ∀ i, W i ≤ M) {A : Finset ι} (hsum : B_W ≤ ∑ i ∈ A, W i) :
    (B_W + M - 1) / M ≤ #A := by
  have h1 : B_W ≤ #A * M := hsum.trans ((Finset.sum_le_sum fun i _ => hW_le i).trans (by simp))
  exact Nat.le_of_lt_succ (show (B_W + M - 1) / M < #A + 1 from
    (Nat.div_lt_iff_lt_mul hM).2 (by rw [add_mul, one_mul]; omega))

end CurveEval

end Cslib.Code.ProximityGap
