/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.DegZ
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap

/-!
# Step 5: Universal Power-Series-Free Taylor Recurrence (`recPoly`)

Defines the `γ²`-scaled Hensel-lift recurrence polynomials `N_n(Z, Y) ∈ F[Z][Y]` (`recPoly`)
without `PowerSeries` imports, proves weighted/total `Z`-degree and `Y`-degree bounds using
`DegBound`, and establishes exact coefficient specialization for polynomial roots of `S`.

## Main definitions and results

* `Cslib.Code.ProximityGap.shiftedCoeff`: Taylor coefficient `S̃_a(Z, Y)` of `(X - x₀)^a`.
* `Cslib.Code.ProximityGap.recPoly`: `γ²`-scaled universal Hensel recurrence polynomial.
* `Cslib.Code.ProximityGap.coeff_eq_map_recPoly`: root-expansion specialization identity.
-/

public section

namespace Cslib.Code.ProximityGap

open Finset Polynomial Polynomial.Bivariate

variable {F : Type*} [Field F]

/-- Finite Taylor expansion in arbitrary characteristic via Hasse derivatives. -/
private theorem eval₂_add_eq_sum_hasseDeriv {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (p : R[X]) {s : ℕ} (hs : p.natDegree ≤ s) (y u : A) :
    p.eval₂ f (y + u) = ∑ j ∈ range (s + 1), (hasseDeriv j p).eval₂ f y * u ^ j := by
  rw [← Polynomial.eval_map, add_comm y u, ← Polynomial.taylor_eval y (p.map f) u]
  have hdeg : (taylor y (p.map f)).natDegree < s + 1 :=
    Nat.lt_succ_of_le (by rw [natDegree_taylor]; exact Polynomial.natDegree_map_le.trans hs)
  rw [eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [taylor_coeff, hasseDeriv_map, Polynomial.eval_map]

private theorem coeff_pow_eq_zero_of_lt_of_coeff_zero {R : Type*} [CommSemiring R] {p : R[X]}
    (hp0 : p.coeff 0 = 0) : ∀ j k, k < j → (p ^ j).coeff k = 0 :=
  fun j k hk => X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hp0) j) k hk

private theorem coeff_pow_eq_of_coeff_eq_of_coeff_zero {R : Type*} [CommSemiring R] {p q : R[X]}
    (hp0 : p.coeff 0 = 0) (hq0 : q.coeff 0 = 0) {m : ℕ}
    (heq : ∀ k ≤ m, p.coeff k = q.coeff k) :
    ∀ j, 1 ≤ j → ∀ k ≤ m + j - 1, (p ^ j).coeff k = (q ^ j).coeff k := by
  intro j
  induction j with
  | zero =>
    intro hj
    omega
  | succ j ih =>
    intro _ k hk
    cases j with
    | zero =>
      rw [pow_one, pow_one]
      exact heq k (by omega)
    | succ j =>
      rw [pow_succ p (j + 1), pow_succ q (j + 1), coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hsum : x.1 + x.2 = k := Finset.mem_antidiagonal.1 hx
      by_cases hx2 : x.2 = 0
      · rw [hx2, hp0, hq0, mul_zero, mul_zero]
      · by_cases hx1 : x.1 < j + 1
        · rw [coeff_pow_eq_zero_of_lt_of_coeff_zero hp0 (j + 1) x.1 hx1,
            coeff_pow_eq_zero_of_lt_of_coeff_zero hq0 (j + 1) x.1 hx1, zero_mul, zero_mul]
        · rw [ih (by omega) x.1 (by omega), heq x.2 (by omega)]

/-- Coefficient `S̃_a(Z, Y) ∈ F[Z][Y]` of `(X - x₀)^a` in `S(Z, X + x₀, Y)`. -/
noncomputable def shiftedCoeff (S : F[X][X][X]) (x₀ : F) (a : ℕ) : F[X][X] :=
  (Bivariate.swap (S.map (Polynomial.taylorAlgHom (C x₀)).toRingHom)).coeff a

private theorem coeff_shiftedCoeff (S : F[X][X][X]) (x₀ : F) (a b : ℕ) :
    (shiftedCoeff S x₀ a).coeff b = (taylor (C x₀) (S.coeff b)).coeff a := by
  rw [shiftedCoeff, coeff_coeff_swap, coeff_map]
  rfl

theorem shiftedCoeff_zero (S : F[X][X][X]) (x₀ : F) :
    shiftedCoeff S x₀ 0 = S.map (Polynomial.evalRingHom (C x₀)) := by
  ext b : 2
  rw [coeff_shiftedCoeff, taylor_coeff_zero, coeff_map]
  rfl

theorem degZ₂_shiftedCoeff_le (S : F[X][X][X]) (x₀ : F) (a : ℕ) :
    degZ₂ (shiftedCoeff S x₀ a) ≤ degZ S := by
  rw [degZ₂_le_iff]
  intro b
  rw [coeff_shiftedCoeff]
  exact (degZ₂_le_iff.1 (degZ₂_taylor_C_le (S.coeff b) x₀) a).trans (degZ₂_coeff_le_degZ S b)

private theorem natDegree_shiftedCoeff_le (S : F[X][X][X]) (x₀ : F) (a : ℕ) :
    (shiftedCoeff S x₀ a).natDegree ≤ S.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro b hb
  rw [coeff_shiftedCoeff, coeff_eq_zero_of_natDegree_lt hb, map_zero, coeff_zero]

private theorem shiftedCoeff_weighted_le {S : F[X][X][X]} {x₀ : F} {w D : ℕ}
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D)
    {a b : ℕ} (hab : (shiftedCoeff S x₀ a).coeff b ≠ 0) :
    a + w * b ≤ D := by
  rw [coeff_shiftedCoeff] at hab
  have ha_le : a ≤ (S.coeff b).natDegree := by
    simpa only [natDegree_taylor] using le_natDegree_of_ne_zero hab
  have hSb_ne : S.coeff b ≠ 0 := fun h0 => hab (by rw [h0, map_zero, coeff_zero])
  have hle := hS_wd (S.coeff b).natDegree b (leadingCoeff_ne_zero.2 hSb_ne)
  omega

private theorem shiftedCoeff_eq_zero_of_gt {S : F[X][X][X]} {x₀ : F} {w D : ℕ}
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D)
    {a : ℕ} (ha : D < a) :
    shiftedCoeff S x₀ a = 0 := by
  ext b : 2
  rw [coeff_zero]
  by_contra hne
  have hle := shiftedCoeff_weighted_le hS_wd hne
  omega

/-- Expanding `S(Z, X + x₀, Y)` mapped under `ψ : F[Z] →+* A` and evaluated at `W ∈ A[X]`. -/
private theorem eval_map_shifted_eq_sum {A : Type*} [CommRing A]
    (ψ : F[X] →+* A) (S : F[X][X][X]) (x₀ : F) {w D : ℕ}
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D) (W : A[X]) :
    ((S.map (Polynomial.taylorAlgHom (C x₀)).toRingHom).map (Polynomial.mapRingHom ψ)).eval W =
      ∑ a ∈ range (D + 1), (shiftedCoeff S x₀ a).eval₂ (C.comp ψ) W * X ^ a := by
  set Sshift : F[X][X][X] := S.map (Polynomial.taylorAlgHom (C x₀)).toRingHom
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le
    (Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le))]
  have hinner (b : ℕ) : (Sshift.map (Polynomial.mapRingHom ψ)).coeff b =
      ∑ a ∈ range (D + 1), C (ψ ((shiftedCoeff S x₀ a).coeff b)) * X ^ a := by
    have hSc : Sshift.coeff b = taylor (C x₀) (S.coeff b) := by rw [coeff_map]; rfl
    have hdegX : ((Sshift.coeff b).map ψ).natDegree < D + 1 := Nat.lt_succ_of_le <|
      Polynomial.natDegree_map_le.trans <| natDegree_le_iff_coeff_eq_zero.2 fun a ha =>
        by_contra fun hne => by
          have := shiftedCoeff_weighted_le hS_wd (a := a) (b := b)
            (by rw [coeff_shiftedCoeff, ← hSc]; exact hne)
          omega
    rw [coeff_map]
    change (Sshift.coeff b).map ψ = _
    rw [Polynomial.as_sum_range' _ (D + 1) hdegX]
    exact Finset.sum_congr rfl fun a _ => by
      rw [coeff_map, ← C_mul_X_pow_eq_monomial, coeff_shiftedCoeff, hSc]
  calc ∑ b ∈ range (S.natDegree + 1), (Sshift.map (Polynomial.mapRingHom ψ)).coeff b * W ^ b
      = ∑ b ∈ range (S.natDegree + 1),
          ∑ a ∈ range (D + 1), (C (ψ ((shiftedCoeff S x₀ a).coeff b)) * W ^ b) * X ^ a :=
        Finset.sum_congr rfl fun b _ => by
          rw [hinner b, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ a ∈ range (D + 1),
          ∑ b ∈ range (S.natDegree + 1), (C (ψ ((shiftedCoeff S x₀ a).coeff b)) * W ^ b) * X ^ a :=
        Finset.sum_comm
    _ = ∑ a ∈ range (D + 1), (shiftedCoeff S x₀ a).eval₂ (C.comp ψ) W * X ^ a :=
        Finset.sum_congr rfl fun a _ => by
          rw [← Finset.sum_mul,
            eval₂_eq_sum_range' (C.comp ψ) (Nat.lt_succ_of_le (natDegree_shiftedCoeff_le S x₀ a)) W]
          rfl

/-- Shifting `S(Z, X, P(X))` by `x₀` after mapping `F[Z] →+* A` matches evaluating `Sshift` at
`taylor (ψ (C x₀)) P`. -/
theorem taylor_eval_map_eq_sum {A : Type*} [CommRing A]
    (ψ : F[X] →+* A) (S : F[X][X][X]) (x₀ : F) {w D : ℕ}
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D) (P : A[X]) :
    taylor (ψ (C x₀)) ((S.map (Polynomial.mapRingHom ψ)).eval P) =
      ∑ a ∈ range (D + 1),
        (shiftedCoeff S x₀ a).eval₂ (C.comp ψ) (taylor (ψ (C x₀)) P) * X ^ a := by
  let τ : A[X] →+* A[X] := (Polynomial.taylorAlgHom (ψ (C x₀))).toRingHom
  have hcomm : τ.comp (Polynomial.mapRingHom ψ) =
      (Polynomial.mapRingHom ψ).comp (Polynomial.taylorAlgHom (C x₀)).toRingHom := by
    apply Polynomial.ringHom_ext'
    · apply RingHom.ext; intro p
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, τ,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change taylor (ψ (C x₀)) (C (ψ p)) = (taylor (C x₀) (C p)).map ψ
      rw [taylor_C, taylor_C, Polynomial.map_C]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, τ,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change taylor (ψ (C x₀)) X = (taylor (C x₀) X).map ψ
      rw [taylor_X, taylor_X, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  have h1 : τ ((S.map (Polynomial.mapRingHom ψ)).eval P) =
      ((S.map (Polynomial.taylorAlgHom (C x₀)).toRingHom).map (Polynomial.mapRingHom ψ)).eval
        (τ P) := by
    have hhom := Polynomial.hom_eval₂ (S.map (Polynomial.mapRingHom ψ)) (RingHom.id A[X]) τ P
    rw [RingHom.comp_id, Polynomial.eval₂_id] at hhom
    rw [hhom, Polynomial.eval₂_map, hcomm, ← Polynomial.eval₂_map, ← Polynomial.eval_map,
      Polynomial.map_map]
  change τ ((S.map (Polynomial.mapRingHom ψ)).eval P) = _
  rw [h1]
  exact eval_map_shifted_eq_sum ψ S x₀ hS_wd (τ P)

/-- Universal `γ²`-scaled Taylor recurrence polynomials `N_n(Z, Y) ∈ F[Z][Y]` (zero `PowerSeries`).
-/
noncomputable def recPoly (S : F[X][X][X]) (x₀ : F) (s : ℕ) : ℕ → F[X][X]
  | 0 => X
  | n + 1 =>
    let S₀ := S.map (Polynomial.evalRingHom (C x₀))
    let γ := S₀.derivative
    let U : (F[X][X])[X] := ∑ k ∈ (Icc 1 n).attach, C (recPoly S x₀ s k.1) * X ^ k.1
    Neg.neg (∑ a ∈ range (n + 2), ∑ j ∈ range (s + 1),
      if (a = 0 ∧ j = 0) ∨ (a = 0 ∧ j = 1) then 0
      else hasseDeriv j (shiftedCoeff S x₀ a) * γ ^ (2 * a + j - 2) *
        (U ^ j).coeff (n + 1 - a))
termination_by n => n
decreasing_by
  have := (Finset.mem_Icc.1 k.2).2
  omega

/-- Truncated universal series `U_M(T) = ∑_{k=1}^M N_k(Z, Y) T^k ∈ (F[Z][Y])[T]`. -/
private noncomputable def recU (S : F[X][X][X]) (x₀ : F) (s M : ℕ) : (F[X][X])[X] :=
  ∑ k ∈ Icc 1 M, C (recPoly S x₀ s k) * X ^ k

private theorem coeff_recU_zero (S : F[X][X][X]) (x₀ : F) (s M : ℕ) :
    (recU S x₀ s M).coeff 0 = 0 := by
  rw [recU, coeff_sum_Icc_C_mul_X_pow, ite_eq_right (by omega)]

private theorem coeff_recU (S : F[X][X][X]) (x₀ : F) (s M k : ℕ) :
    (recU S x₀ s M).coeff k = if 1 ≤ k ∧ k ≤ M then recPoly S x₀ s k else 0 :=
  coeff_sum_Icc_C_mul_X_pow 1 M k (recPoly S x₀ s)

private theorem recPoly_succ (S : F[X][X][X]) (x₀ : F) (s n : ℕ) :
    recPoly S x₀ s (n + 1) =
      -(∑ a ∈ range (n + 2), ∑ j ∈ range (s + 1),
        if (a = 0 ∧ j = 0) ∨ (a = 0 ∧ j = 1) then 0
        else hasseDeriv j (shiftedCoeff S x₀ a) *
          (S.map (Polynomial.evalRingHom (C x₀))).derivative ^ (2 * a + j - 2) *
          ((recU S x₀ s n) ^ j).coeff (n + 1 - a)) := by
  rw [recPoly]
  rw [Finset.sum_attach (Icc 1 n) (fun k => C (recPoly S x₀ s k) * X ^ k)]
  rfl

/-- Degree bound on coefficients of `U ^ j` when `U.coeff 0 = 0` and
`deg (U.coeff k) ≤ (2 * k - 1) * B` for all `k ≥ 1`. -/
private theorem deg_pow_coeff_le {R : Type*} [CommRing R] (db : DegBound R)
    {U : R[X]} {B : ℕ} (hU0 : U.coeff 0 = 0)
    (hUk : ∀ k, 1 ≤ k → U.coeff k ≠ 0 → db.deg (U.coeff k) ≤ (2 * k - 1) * B) :
    ∀ j, 1 ≤ j → ∀ t, (U ^ j).coeff t ≠ 0 →
      j ≤ t ∧ db.deg ((U ^ j).coeff t) ≤ (2 * t - j) * B := by
  intro j
  induction j with
  | zero => intro hj; omega
  | succ j ihj =>
    intro _ t hne
    cases j with
    | zero =>
      rw [pow_one] at hne ⊢
      have ht : 1 ≤ t := Nat.pos_of_ne_zero fun h0 => by subst h0; exact hne hU0
      exact ⟨ht, hUk t ht hne⟩
    | succ j =>
      have ht_ge : j + 2 ≤ t := by_contra fun hlt =>
        hne (coeff_pow_eq_zero_of_lt_of_coeff_zero hU0 (j + 2) t (by omega))
      refine ⟨ht_ge, ?_⟩
      rw [pow_succ, coeff_mul]
      refine db.sum_le _ _ fun x hx => ?_
      have hxsum : x.1 + x.2 = t := Finset.mem_antidiagonal.1 hx
      by_cases h1 : (U ^ (j + 1)).coeff x.1 = 0
      · rw [h1, zero_mul, db.zero]; exact Nat.zero_le _
      · by_cases h2 : U.coeff x.2 = 0
        · rw [h2, mul_zero, db.zero]; exact Nat.zero_le _
        · have hx2 : 1 ≤ x.2 := Nat.pos_of_ne_zero fun h0 => h2 (h0 ▸ hU0)
          have hIH1 := ihj (by omega) x.1 h1
          refine (db.mul_le _ _).trans <| (Nat.add_le_add hIH1.2 (hUk x.2 hx2 h2)).trans_eq ?_
          rw [← add_mul]; congr 1; omega

/-- Generic degree bound for `recPoly` under any `DegBound` on `F[Z][Y]`. -/
private theorem deg_recPoly_le (db : DegBound F[X][X])
    {S : F[X][X][X]} {x₀ : F} {s B : ℕ}
    (hS : ∀ a j, db.deg (hasseDeriv j (shiftedCoeff S x₀ a)) ≤ B)
    (hγ : db.deg (S.map (Polynomial.evalRingHom (C x₀))).derivative ≤ B) :
    ∀ n, 1 ≤ n → db.deg (recPoly S x₀ s n) ≤ (2 * n - 1) * B := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    cases n with
    | zero => omega
    | succ m =>
      have hUpow := deg_pow_coeff_le db (coeff_recU_zero S x₀ s m) (B := B) fun k hk hne => by
        rw [coeff_recU] at hne ⊢
        split_ifs at hne ⊢ with hkm
        · exact ih k (by omega) hkm.1
        · exact absurd rfl hne
      rw [recPoly_succ, db.neg]
      refine db.sum_le _ _ fun a ha => db.sum_le _ _ fun j _ => ?_
      have ha_le : a ≤ m + 1 := Nat.lt_succ_iff.1 (mem_range.1 ha)
      split_ifs with hskip
      · rw [db.zero]; exact Nat.zero_le _
      · by_cases hj0 : j = 0
        · subst hj0
          by_cases han : a = m + 1
          · subst han
            rw [Nat.sub_self, pow_zero, coeff_one, ite_eq_left rfl, mul_one]
            refine (db.mul_le _ _).trans <|
              (Nat.add_le_add (hS (m + 1) 0) ((db.pow_le _ _).trans
                (Nat.mul_le_mul_left _ hγ))).trans_eq ?_
            rw [← one_add_mul]; congr 1; omega
          · rw [pow_zero, coeff_one, ite_eq_right (by omega), mul_zero, db.zero]
            exact Nat.zero_le _
        · by_cases hU0 : ((recU S x₀ s m) ^ j).coeff (m + 1 - a) = 0
          · rw [hU0, mul_zero, db.zero]; exact Nat.zero_le _
          · have hUdeg := hUpow j (by omega) (m + 1 - a) hU0
            refine (db.mul_le _ _).trans <| (Nat.add_le_add (db.mul_le _ _) le_rfl).trans ?_
            have h1 := hS a j
            have h2 := (db.pow_le _ (2 * a + j - 2)).trans (Nat.mul_le_mul_left _ hγ)
            have hle := Nat.add_le_add (Nat.add_le_add h1 h2) hUdeg.2
            refine hle.trans_eq ?_
            rw [← one_add_mul, ← add_mul]; congr 1; have := hUdeg.1; omega

theorem degZ₂_recPoly_le {S : F[X][X][X]} {x₀ : F} {s B_Z : ℕ}
    (hS_degZ : degZ S ≤ B_Z) :
    ∀ n, 1 ≤ n → degZ₂ (recPoly S x₀ s n) ≤ (2 * n - 1) * B_Z :=
  deg_recPoly_le (DegBound.degZ₂ F)
    (fun a j => (degZ₂_hasseDeriv_le j _).trans ((degZ₂_shiftedCoeff_le S x₀ a).trans hS_degZ))
    ((degZ₂_derivative_le _).trans (by
      rw [← shiftedCoeff_zero]; exact (degZ₂_shiftedCoeff_le S x₀ 0).trans hS_degZ))

theorem natDegree_recPoly_le {S : F[X][X][X]} {x₀ : F} {s : ℕ}
    (hS_deg : S.natDegree ≤ s) :
    ∀ n, 1 ≤ n → (recPoly S x₀ s n).natDegree ≤ (2 * n - 1) * s := by
  refine deg_recPoly_le (DegBound.natDegree F[X]) (fun a j => ?_) ?_
  · exact (Polynomial.natDegree_hasseDeriv_le _ j).trans
      ((Nat.sub_le _ _).trans ((natDegree_shiftedCoeff_le S x₀ a).trans hS_deg))
  · exact (Polynomial.natDegree_derivative_le _).trans
      ((Nat.sub_le _ _).trans (Polynomial.natDegree_map_le.trans hS_deg))

private theorem eval₂_shifted_comp_mul_X_coeff {A : Type*} [CommRing A]
    (S : F[X][X][X]) (x₀ : F) {s : ℕ} (hS_deg : S.natDegree ≤ s)
    (φ : F[X][X] →+* A) (g : A) (U : A[X]) {a n : ℕ} (han : a ≤ n) :
    (((shiftedCoeff S x₀ a).eval₂ (C.comp (φ.comp C)) (C (φ X) + C g * U)) *
      (C (g ^ 2) * X) ^ a).coeff n =
      ∑ j ∈ range (s + 1),
        φ (hasseDeriv j (shiftedCoeff S x₀ a)) * g ^ (2 * a + j) * (U ^ j).coeff (n - a) := by
  rw [mul_pow, ← C_pow, ← mul_assoc, coeff_mul_X_pow', ite_eq_left han,
    eval₂_add_eq_sum_hasseDeriv (C.comp (φ.comp C)) _
      ((natDegree_shiftedCoeff_le S x₀ a).trans hS_deg) (C (φ X)) (C g * U),
    Finset.sum_mul, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hev : (hasseDeriv j (shiftedCoeff S x₀ a)).eval₂ (C.comp (φ.comp C)) (C (φ X)) =
      C (φ (hasseDeriv j (shiftedCoeff S x₀ a))) := by
    rw [← Polynomial.hom_eval₂ _ (φ.comp C) (C : A →+* A[X]) (φ X)]
    congr 1
    simpa only [Polynomial.eval₂_C_X] using
      (Polynomial.hom_eval₂ (hasseDeriv j (shiftedCoeff S x₀ a)) C φ X).symm
  rw [hev, mul_pow, ← C_pow,
    show C (φ (hasseDeriv j (shiftedCoeff S x₀ a))) * (C (g ^ j) * U ^ j) * C ((g ^ 2) ^ a) =
      C (φ (hasseDeriv j (shiftedCoeff S x₀ a)) * g ^ (2 * a + j)) * U ^ j by
      rw [pow_add, pow_mul, map_mul, map_mul]; ring,
    coeff_C_mul]

/-- Specialization uniqueness: for any domain homomorphism `φ : F[Z][Y] →+* A` with `φ S₀ = 0`
and `φ γ ≠ 0`, any polynomial `W ∈ A[X]` solving `∑_a S̃_a(W) X^a = 0` with `W(0) = φ Y`
satisfies `(φ γ)^(2 n - 1) * W.coeff n = φ (N_n)` for every `n ≥ 1`. -/
theorem coeff_eq_map_recPoly {A : Type*} [CommRing A] [IsDomain A]
    {S : F[X][X][X]} {x₀ : F} {s w D : ℕ}
    (hs1 : 1 ≤ s) (hS_deg : S.natDegree ≤ s)
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D)
    (φ : F[X][X] →+* A)
    (hγ_ne : φ (S.map (Polynomial.evalRingHom (C x₀))).derivative ≠ 0)
    {W : A[X]} (hW0 : W.coeff 0 = φ X)
    (hWeq : ∑ a ∈ range (D + 1), (shiftedCoeff S x₀ a).eval₂ (C.comp (φ.comp C)) W * X ^ a = 0) :
    ∀ n, 1 ≤ n →
      (φ (S.map (Polynomial.evalRingHom (C x₀))).derivative) ^ (2 * n - 1) * W.coeff n =
      φ (recPoly S x₀ s n) := by
  set S₀ := S.map (Polynomial.evalRingHom (C x₀))
  set γ := S₀.derivative
  set g : A := φ γ
  set U_W : A[X] := ∑ k ∈ Icc 1 W.natDegree, C (g ^ (2 * k - 1) * W.coeff k) * X ^ k
  have hU_W_zero : U_W.coeff 0 = 0 := by
    rw [coeff_sum_Icc_C_mul_X_pow, ite_eq_right (by omega)]
  have hU_W_coeff : ∀ k, 1 ≤ k → U_W.coeff k = g ^ (2 * k - 1) * W.coeff k := fun k hk1 => by
    rw [coeff_sum_Icc_C_mul_X_pow]
    split_ifs with hk
    · rfl
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  have hW_comp : W.comp (C (g ^ 2) * X) = C (φ X) + C g * U_W := by
    ext k
    rw [Polynomial.comp_C_mul_X_coeff, coeff_add, coeff_C_mul]
    cases k with
    | zero => rw [pow_zero, mul_one, coeff_C_zero, hU_W_zero, mul_zero, add_zero, hW0]
    | succ k =>
      rw [coeff_C_succ, zero_add, hU_W_coeff (k + 1) (by omega), ← pow_mul,
        mul_comm (W.coeff (k + 1)), ← mul_assoc, ← pow_succ']
      rfl
  have hcomp0 : ∑ a ∈ range (D + 1),
      ((shiftedCoeff S x₀ a).eval₂ (C.comp (φ.comp C)) (C (φ X) + C g * U_W)) *
        (C (g ^ 2) * X) ^ a = 0 := by
    have hc := congrArg (fun p : A[X] => p.comp (C (g ^ 2) * X)) hWeq
    rw [Polynomial.zero_comp, Polynomial.sum_comp] at hc
    refine (Finset.sum_congr rfl fun a _ => ?_).symm.trans hc
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, ← hW_comp]
    congr 1
    have hfc : (Polynomial.compRingHom (C (g ^ 2) * X)).comp (C.comp (φ.comp C)) =
        C.comp (φ.comp C) := RingHom.ext fun c => by simp [Polynomial.compRingHom]
    have hhom := Polynomial.hom_eval₂ (shiftedCoeff S x₀ a) (C.comp (φ.comp C))
      (Polynomial.compRingHom (C (g ^ 2) * X)) W
    rw [hfc] at hhom; exact hhom
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    cases n with
    | zero => omega
    | succ m =>
      have hc0 := congrArg (fun p : A[X] => p.coeff (m + 1)) hcomp0
      rw [coeff_zero, finsetSum_coeff] at hc0
      set term : ℕ → A := fun a => ∑ j ∈ range (s + 1),
        φ (hasseDeriv j (shiftedCoeff S x₀ a)) * g ^ (2 * a + j) * (U_W ^ j).coeff (m + 1 - a)
      have hmin_eq : ∑ a ∈ range (min D (m + 1) + 1), term a = 0 := by
        have hsub : ∑ a ∈ range (min D (m + 1) + 1),
            (((shiftedCoeff S x₀ a).eval₂ (C.comp (φ.comp C)) (C (φ X) + C g * U_W)) *
              (C (g ^ 2) * X) ^ a).coeff (m + 1) = 0 :=
          (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_left _ _)))
            fun a ha ha_not => by
              rw [mem_range] at ha ha_not
              rw [mul_pow, ← C_pow, ← mul_assoc, coeff_mul_X_pow',
                ite_eq_right (by omega : ¬ a ≤ m + 1)]).trans hc0
        exact (Finset.sum_congr rfl fun a ha =>
          eval₂_shifted_comp_mul_X_coeff S x₀ hS_deg φ g U_W
            (by rw [mem_range] at ha; omega)).symm.trans hsub
      have hsum_eq : ∑ a ∈ range (m + 2), term a = 0 :=
        (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_right _ _)))
          fun a ha ha_not => Finset.sum_eq_zero fun j _ => by
            rw [mem_range] at ha ha_not
            rw [shiftedCoeff_eq_zero_of_gt hS_wd (by omega),
              map_zero, map_zero, zero_mul, zero_mul]).symm.trans hmin_eq
      set U_map : A[X] := (recU S x₀ s m).map φ
      have hU_map_zero : U_map.coeff 0 = 0 := by rw [coeff_map, coeff_recU_zero, map_zero]
      have hagree : ∀ k ≤ m, U_W.coeff k = U_map.coeff k := fun k hk => by
        rw [coeff_map, coeff_recU]
        by_cases hk1 : 1 ≤ k
        · rw [ite_eq_left ⟨hk1, hk⟩, hU_W_coeff k hk1]; exact ih k (by omega) hk1
        · have hk0 : k = 0 := by omega
          subst hk0; rw [ite_eq_right (by omega), hU_W_zero, map_zero]
      have hsplit : ∀ a ∈ range (m + 2), ∀ j ∈ range (s + 1),
          φ (hasseDeriv j (shiftedCoeff S x₀ a)) * g ^ (2 * a + j) * (U_W ^ j).coeff (m + 1 - a) =
          (if a = 0 ∧ j = 1 then g ^ 2 * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1)) else 0) +
          g ^ 2 * φ (if (a = 0 ∧ j = 0) ∨ (a = 0 ∧ j = 1) then 0
            else hasseDeriv j (shiftedCoeff S x₀ a) * γ ^ (2 * a + j - 2) *
              ((recU S x₀ s m) ^ j).coeff (m + 1 - a)) := fun a ha j _ => by
        have ha_le : a ≤ m + 1 := Nat.lt_succ_iff.1 (mem_range.1 ha)
        by_cases h00 : a = 0 ∧ j = 0
        · rcases h00 with ⟨rfl, rfl⟩
          simp [coeff_one]
        · by_cases h01 : a = 0 ∧ j = 1
          · rcases h01 with ⟨rfl, rfl⟩
            simp only [and_self, ↓reduceIte, or_true, map_zero, mul_zero, add_zero, Nat.sub_zero,
              pow_one, shiftedCoeff_zero, hasseDeriv_one', hU_W_coeff (m + 1) (by omega),
              mul_zero, zero_add]
            change g * g * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1)) = _
            ring
          · rw [ite_eq_right h01, zero_add, ite_eq_right (by tauto : ¬ ((a = 0 ∧ j = 0) ∨ _))]
            have hpow : g ^ (2 * a + j) = g ^ 2 * g ^ (2 * a + j - 2) := by
              rw [← pow_add]; congr 1; omega
            have hUeq : (U_W ^ j).coeff (m + 1 - a) =
                φ (((recU S x₀ s m) ^ j).coeff (m + 1 - a)) := by
              rw [← coeff_map, Polynomial.map_pow]
              rcases eq_or_ne j 0 with rfl | hj0
              · simp
              · exact coeff_pow_eq_of_coeff_eq_of_coeff_zero hU_W_zero hU_map_zero hagree j
                  (by omega) (m + 1 - a) (by omega)
            rw [hpow, hUeq, map_mul, map_mul, map_pow]
            change _ = g ^ 2 * (φ _ * g ^ (2 * a + j - 2) * φ _); ring
      have hsum_split : (∑ a ∈ range (m + 2), ∑ j ∈ range (s + 1),
          if a = 0 ∧ j = 1 then g ^ 2 * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1)) else 0) +
          g ^ 2 * φ (-recPoly S x₀ s (m + 1)) = 0 := by
        rw [recPoly_succ, neg_neg, map_sum, Finset.mul_sum]
        simp_rw [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact (Finset.sum_congr rfl fun a ha =>
          Finset.sum_congr rfl fun j hj => hsplit a ha j hj).symm.trans hsum_eq
      have hmain : (∑ a ∈ range (m + 2), ∑ j ∈ range (s + 1),
          if a = 0 ∧ j = 1 then g ^ 2 * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1)) else 0) =
          g ^ 2 * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1)) := by
        rw [Finset.sum_eq_single 0 (fun a _ ha0 => Finset.sum_eq_zero fun _ _ => by simp [ha0])
          (fun h => absurd (mem_range.2 (by omega)) h),
          Finset.sum_eq_single 1 (fun j _ hj1 => by simp [hj1])
          (fun h => absurd (mem_range.2 (by omega)) h)]
        simp
      rw [hmain, map_neg] at hsum_split
      have hfac : g ^ 2 * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1) -
          φ (recPoly S x₀ s (m + 1))) = 0 := by linear_combination hsum_split
      exact sub_eq_zero.1 ((mul_eq_zero.1 hfac).resolve_left (pow_ne_zero 2 hγ_ne))

end Cslib.Code.ProximityGap
