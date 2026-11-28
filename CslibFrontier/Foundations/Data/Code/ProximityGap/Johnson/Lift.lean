/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.DegZ
public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.Recurrence
import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.Separable
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Step 6: Resultant Kill and Algebraic-Closure Root Lift

Eliminates mismatch polynomials via `resultant` degree bounds and lifts the contracted
separable factor over the algebraic closure of `FractionRing F[Z]` into low-degree Reed–Solomon
candidate polynomial coefficients (handling both zero and positive characteristic).

## Main results

* `Cslib.Code.ProximityGap.exists_lifted_poly_and_mismatch_bound`: extracts the global polynomial
  lift and surviving agreement scalar set `T''`.
-/

public section

namespace Cslib.Code.ProximityGap

open Cslib.Code Finset Polynomial Polynomial.Bivariate

variable {F : Type*} [Field F]

private theorem eval_resultant_eq_zero_of_common_root
    {f g : F[X][X]} (hf : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) {z y : F}
    (hf0 : (f.map (evZ z)).eval y = 0) (hg0 : (g.map (evZ z)).eval y = 0) :
    (Polynomial.resultant f g f.natDegree g.natDegree).eval z = 0 := by
  obtain ⟨U, V, _, _, hbez⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl hf
  have hmap := congrArg (fun p : F[X][X] => (p.map (evZ z)).eval y) hbez
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
    eval_add, eval_mul, eval_mul, eval_C, hf0, hg0, zero_mul, zero_mul, add_zero] at hmap
  exact hmap.symm

/-- In prime characteristic `p`, `(Q ^ (p ^ e)).coeff n = 0` whenever `¬ p ^ e ∣ n`. -/
private theorem coeff_pow_prime_pow_eq_zero_of_not_dvd {R : Type*} [CommRing R] {p e : ℕ}
    [CharP R p] (hp : p.Prime) (Q : R[X]) {n : ℕ} (hndiv : ¬ p ^ e ∣ n) :
    (Q ^ (p ^ e)).coeff n = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Polynomial.map_iterateFrobenius_expand p Q e, coeff_map,
    coeff_expand_eq_zero_of_not_dvd (pow_pos hp.pos e) Q hndiv, map_zero]

/-- In a domain whose characteristic matches `μ`, `a ^ μ = b ^ μ → a = b`. -/
private theorem eq_of_pow_eq_of_char_pow {A : Type*} [CommRing A] [IsDomain A] {μ : ℕ}
    (hμ : μ = 1 ∨ ∃ (p e : ℕ), CharP A p ∧ p.Prime ∧ μ = p ^ e) {a b : A} (h : a ^ μ = b ^ μ) :
    a = b := by
  rcases hμ with rfl | ⟨p, e, hcp, hp, rfl⟩
  · simpa using h
  · have : Fact p.Prime := ⟨hp⟩
    exact iterateFrobenius_inj A p e (by simpa only [iterateFrobenius_def] using h)

/-- Evaluation mismatch polynomial `E_i(Z, Y) ∈ F[Z][Y]` capturing
`P*(α i)^μ - w_i(Z)^μ` cleared by `γ^(2 μ d - 1)` (or `Y - w_i(Z)^μ` when `μ * d = 0`). -/
private noncomputable def evalMismatchPoly (S : F[X][X][X]) (x₀ : F) (s μ d : ℕ)
    (a : F) (w : F[X]) : F[X][X] :=
  let γ := (S.map (Polynomial.evalRingHom (C x₀))).derivative
  if μ * d = 0 then
    X - C (w ^ μ)
  else
    X * γ ^ (2 * (μ * d) - 1) +
      (∑ k ∈ Icc 1 (μ * d),
        recPoly S x₀ s k * γ ^ (2 * (μ * d - k)) * C (C ((a - x₀) ^ k))) -
      C (w ^ μ) * γ ^ (2 * (μ * d) - 1)

private theorem deg_evalMismatchPoly_le (db : DegBound F[X][X])
    {S : F[X][X][X]} {x₀ : F} {s μ d Bx B Bw : ℕ}
    (hX : db.deg X ≤ Bx) (hBx : Bx ≤ B)
    (hCC : ∀ c : F, db.deg (C (C c)) = 0)
    (a : F) (w : F[X]) (hw : db.deg (C (w ^ μ)) ≤ Bw)
    (hγ : db.deg (S.map (Polynomial.evalRingHom (C x₀))).derivative ≤ B)
    (hrec : ∀ k, 1 ≤ k → db.deg (recPoly S x₀ s k) ≤ (2 * k - 1) * B) :
    db.deg (evalMismatchPoly S x₀ s μ d a w) ≤
      if μ * d = 0 then max Bx Bw else 2 * (μ * d) * B + Bw := by
  set γ := (S.map (Polynomial.evalRingHom (C x₀))).derivative
  rw [evalMismatchPoly]
  split_ifs with h0
  · exact (db.sub_le _ _).trans (max_le (hX.trans (le_max_left _ _)) (hw.trans (le_max_right _ _)))
  · have hγp (e : ℕ) : db.deg (γ ^ e) ≤ e * B := (db.pow_le _ _).trans (Nat.mul_le_mul_left _ hγ)
    have hmul_sub : B + (2 * (μ * d) - 1) * B = 2 * (μ * d) * B := by
      calc B + (2 * (μ * d) - 1) * B = (1 + (2 * (μ * d) - 1)) * B := by ring
        _ = 2 * (μ * d) * B := by congr 1; omega
    refine (db.sub_le _ _).trans (max_le ((db.add_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact (db.mul_le _ _).trans (by
        have h1 := hγp (2 * (μ * d) - 1)
        exact (Nat.add_le_add (hX.trans hBx) h1).trans (by omega))
    · refine db.sum_le _ _ fun k hk => (db.mul_le _ _).trans ?_
      rw [hCC, add_zero]
      refine (db.mul_le _ _).trans ?_
      have hk_mem := mem_Icc.1 hk
      have h1 := hrec k hk_mem.1; have h2 := hγp (2 * (μ * d - k))
      have hle : (2 * k - 1) * B + 2 * (μ * d - k) * B ≤ 2 * (μ * d) * B := by
        rw [← add_mul]; exact Nat.mul_le_mul_right B (by omega)
      exact (Nat.add_le_add h1 h2).trans (hle.trans (Nat.le_add_right _ _))
    · have h1 := hγp (2 * (μ * d) - 1)
      have hle : (2 * (μ * d) - 1) * B ≤ 2 * (μ * d) * B :=
        Nat.mul_le_mul_right B (by omega)
      exact (db.mul_le _ _).trans ((Nat.add_le_add hw (h1.trans hle)).trans_eq (add_comm _ _))

/-- Evaluating `evalMismatchPoly` under any hom `φ : F[Z][Y] →+* A` matching the recurrence
coefficients of a polynomial `W ∈ A[X]` of degree `≤ μ * d`. -/
private theorem map_evalMismatchPoly {A : Type*} [CommRing A]
    {S : F[X][X][X]} {x₀ : F} {s μ d : ℕ} (a : F) (w : F[X])
    (φ : F[X][X] →+* A) {W : A[X]}
    (hW_deg : W.natDegree ≤ μ * d) (hW0 : W.coeff 0 = φ X)
    (hWk : ∀ k ∈ Icc 1 (μ * d),
      (φ (S.map (Polynomial.evalRingHom (C x₀))).derivative) ^ (2 * k - 1) * W.coeff k =
      φ (recPoly S x₀ s k)) :
    φ (evalMismatchPoly S x₀ s μ d a w) =
      (φ (S.map (Polynomial.evalRingHom (C x₀))).derivative) ^
          (if μ * d = 0 then 0 else 2 * (μ * d) - 1) *
        (W.eval (φ (C (C (a - x₀)))) - (φ (C w)) ^ μ) := by
  set γ := (S.map (Polynomial.evalRingHom (C x₀))).derivative
  set g := φ γ
  rw [evalMismatchPoly]
  split_ifs with h0
  · rw [pow_zero, one_mul, map_sub, C_pow, map_pow,
      Polynomial.eq_C_of_natDegree_eq_zero (p := W) (by omega), hW0, eval_C]
  · have hWeval : g ^ (2 * (μ * d) - 1) * W.eval (φ (C (C (a - x₀)))) =
        φ X * g ^ (2 * (μ * d) - 1) +
          ∑ k ∈ Icc 1 (μ * d),
            φ (recPoly S x₀ s k) * g ^ (2 * (μ * d - k)) * φ (C (C ((a - x₀) ^ k))) := by
      rw [eval_eq_sum_range' (Nat.lt_succ_of_le hW_deg), Finset.mul_sum, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot (Nat.zero_lt_succ (μ * d)), pow_zero, mul_one, hW0,
        mul_comm (g ^ _), show Finset.Ico 1 (μ * d + 1) = Icc 1 (μ * d) by ext; simp]
      refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
      have ⟨hk1, hkle⟩ := mem_Icc.1 hk
      rw [show g ^ (2 * (μ * d) - 1) = g ^ (2 * (μ * d - k)) * g ^ (2 * k - 1) by
          rw [← pow_add]; congr 1; omega,
        show φ (C (C (a - x₀))) ^ k = φ (C (C ((a - x₀) ^ k))) by rw [← map_pow, ← C_pow, ← C_pow],
        ← hWk k hk]
      ring
    simp only [map_sub, map_add, map_mul, map_pow, map_sum] at hWeval ⊢
    linear_combination -hWeval

private theorem spec_recPoly_at_point {S : F[X][X][X]} {x₀ : F} {w D μ : ℕ}
    (hS_deg : 1 ≤ S.natDegree)
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D)
    {z : F} {P : F[X]} (hS_eval0 : (evZ₂ z S).eval (P ^ μ) = 0)
    (hγ_ne : ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
      ((P ^ μ).eval x₀) ≠ 0) :
    ∀ n, 1 ≤ n →
      (((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
        ((P ^ μ).eval x₀)) ^ (2 * n - 1) * (taylor x₀ (P ^ μ)).coeff n =
      ((recPoly S x₀ S.natDegree n).map (evZ z)).eval ((P ^ μ).eval x₀) := by
  let φz : F[X][X] →+* F := Polynomial.eval₂RingHom (evZ z) ((P ^ μ).eval x₀)
  have hφz_eq : ∀ f : F[X][X], φz f = (f.map (evZ z)).eval ((P ^ μ).eval x₀) := fun f => by
    simp [φz, Polynomial.eval_map]
  have hWeq : ∑ a ∈ range (D + 1),
      (shiftedCoeff S x₀ a).eval₂ (C.comp (φz.comp C)) (taylor x₀ (P ^ μ)) * X ^ a = 0 := by
    rw [show φz.comp C = evZ z from RingHom.ext fun p => by simp [φz]]
    have ht := taylor_eval_map_eq_sum (evZ z) S x₀ hS_wd (P ^ μ)
    rw [show (evZ z) (C x₀) = x₀ by simp [evZ]] at ht
    change _ = 0; rw [← ht]
    change taylor x₀ ((evZ₂ z S).eval (P ^ μ)) = 0
    rw [hS_eval0, map_zero]
  intro n hn
  have hrec := coeff_eq_map_recPoly hS_deg le_rfl hS_wd φz (by rwa [hφz_eq])
    (by rw [taylor_coeff_zero]; simp [φz]) hWeq n hn
  change (φz _ ^ (2 * n - 1)) * (taylor x₀ (P ^ μ)).coeff n = φz _ at hrec
  rwa [hφz_eq, hφz_eq] at hrec

private theorem exists_pow_eq_poly_of_not_dvd {L : Type*} [Field L] [IsAlgClosed L]
    {μ d : ℕ} (hμ_pos : 1 ≤ μ)
    (hμ_char : μ = 1 ∨ ∃ (p e : ℕ), CharP L p ∧ p.Prime ∧ μ = p ^ e)
    {Ψ : L[X]} (hΨ_deg : Ψ.natDegree ≤ μ * d) (hndiv : ∀ k, ¬ μ ∣ k → Ψ.coeff k = 0) :
    ∃ Ptilde : L[X], Ptilde.natDegree ≤ d ∧ Ptilde ^ μ = Ψ := by
  classical
  rcases hμ_char with rfl | ⟨p, e, _, hp, rfl⟩
  · exact ⟨Ψ, by simpa only [one_mul] using hΨ_deg, pow_one Ψ⟩
  · have : Fact p.Prime := ⟨hp⟩
    choose c hc using fun m : Fin (d + 1) =>
      IsAlgClosed.exists_pow_nat_eq (Ψ.coeff (m.val * p ^ e)) (pow_pos hp.pos e)
    refine ⟨Polynomial.ofFn (d + 1) c,
      Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos d) c), ?_⟩
    rw [← Polynomial.map_iterateFrobenius_expand p (Polynomial.ofFn (d + 1) c) e]
    ext k
    rw [coeff_map, iterateFrobenius_def, Polynomial.coeff_expand (pow_pos hp.pos e)]
    split_ifs with hdiv
    · by_cases hm : k / p ^ e < d + 1
      · rw [Polynomial.ofFn_coeff_eq_val_of_lt c hm, hc ⟨k / p ^ e, hm⟩, Nat.div_mul_cancel hdiv]
      · rw [Polynomial.ofFn_coeff_eq_zero_of_ge c (by omega), zero_pow (by omega)]
        have hmul : (d + 1) * p ^ e ≤ k := (Nat.le_div_iff_mul_le hμ_pos).1 (by omega)
        have hadd : p ^ e * d + p ^ e = (d + 1) * p ^ e := by ring
        exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
    · rw [zero_pow (by omega), hndiv k hdiv]

private theorem resultant_evalMismatch_natDegree_le {ι : Type*} [DecidableEq F]
    {r d D B_Z D_Y μ : ℕ} {S : F[X][X][X]} {Fstar : F[X][X]} {x₀ : F}
    {u : Fin (r + 1) → (ι → F)} (α : ι → F) (i : ι)
    (hμ_pos : 1 ≤ μ) (hS_deg : 1 ≤ S.natDegree) (hDY_pos : 1 ≤ D_Y) (hD_pos : 1 ≤ D)
    (hμs_le : μ * S.natDegree ≤ D_Y) (hμd_le : μ * d ≤ D) (hS_degZ : degZ S ≤ B_Z)
    (hF_deg_le : Fstar.natDegree ≤ S.natDegree) (hF_degZ : degZ₂ Fstar ≤ B_Z) :
    let Ei := evalMismatchPoly S x₀ S.natDegree μ d (α i) (curveWord u i)
    (Polynomial.resultant Fstar Ei Fstar.natDegree Ei.natDegree).natDegree ≤
      4 * D * D_Y * B_Z + r * D_Y ^ 2 := by
  intro Ei
  have hs_le_DY : S.natDegree ≤ D_Y := (Nat.le_mul_of_pos_left _ hμ_pos).trans hμs_le
  have hF_le_DY : Fstar.natDegree ≤ D_Y := hF_deg_le.trans hs_le_DY
  have hμF_sq : Fstar.natDegree * (μ * r) ≤ r * D_Y ^ 2 :=
    calc Fstar.natDegree * (μ * r) = r * (μ * Fstar.natDegree) := by ring
      _ ≤ r * D_Y ^ 2 := Nat.mul_le_mul_left r <|
        ((Nat.mul_le_mul_left μ hF_deg_le).trans hμs_le).trans (Nat.le_self_pow two_ne_zero _)
  have hw_degZ : degZ₂ (C ((curveWord u i) ^ μ)) ≤ μ * r := by
    rw [degZ₂_C]
    exact natDegree_pow_le.trans (Nat.mul_le_mul_left μ
      (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos r) _)))
  have hγ_degZ : degZ₂ (S.map (Polynomial.evalRingHom (C x₀))).derivative ≤ B_Z :=
    (degZ₂_derivative_le _).trans (by
      rw [← shiftedCoeff_zero]; exact (degZ₂_shiftedCoeff_le S x₀ 0).trans hS_degZ)
  have hEi_degZ := deg_evalMismatchPoly_le (DegBound.degZ₂ F) (s := S.natDegree) (μ := μ)
    (d := d) degZ₂_X.le (Nat.zero_le B_Z)
    (fun c => by change degZ₂ (C (C c)) = 0; rw [degZ₂_C, natDegree_C])
    (α i) (curveWord u i) hw_degZ hγ_degZ (degZ₂_recPoly_le hS_degZ)
  have hγ_degY : (S.map (Polynomial.evalRingHom (C x₀))).derivative.natDegree ≤ S.natDegree :=
    (Polynomial.natDegree_derivative_le _).trans
      ((Nat.sub_le _ _).trans Polynomial.natDegree_map_le)
  have hEi_degY := deg_evalMismatchPoly_le (DegBound.natDegree F[X]) (S := S) (x₀ := x₀)
    (s := S.natDegree) (μ := μ) (d := d) natDegree_X_le hS_deg (fun c => natDegree_C _)
    (α i) (curveWord u i) (by change (C (curveWord u i ^ μ)).natDegree ≤ 0; rw [natDegree_C])
    hγ_degY (natDegree_recPoly_le le_rfl)
  have hres := (DegBound.natDegree F).resultant_le Fstar.natDegree Ei.natDegree
    (degZ₂_le_iff.1 hF_degZ) (degZ₂_le_iff.1 hEi_degZ)
  split_ifs at hres hEi_degZ hEi_degY with h0
  · rw [Nat.zero_max] at hres; rw [Nat.max_zero] at hEi_degY
    have h2 : Ei.natDegree * B_Z ≤ 4 * D * D_Y * B_Z :=
      Nat.mul_le_mul_right B_Z (hEi_degY.trans (Nat.mul_pos (by omega) hDY_pos))
    exact hres.trans ((Nat.add_le_add hμF_sq h2).trans_eq (add_comm _ _))
  · have ha : Fstar.natDegree * (2 * (μ * d) * B_Z) ≤ 2 * D * D_Y * B_Z :=
      (Nat.mul_le_mul hF_le_DY
        (Nat.mul_le_mul_right B_Z (show 2 * (μ * d) ≤ 2 * D by omega))).trans_eq (by ring)
    have h2 : Ei.natDegree * B_Z ≤ 2 * D * D_Y * B_Z := Nat.mul_le_mul_right B_Z <|
      hEi_degY.trans (by rw [add_zero]; exact Nat.mul_le_mul (by omega) hs_le_DY)
    rw [mul_add] at hres
    exact hres.trans (by linarith [ha, hμF_sq, h2])

private theorem map_recPoly_dvd_of_kill {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} {r d D B_Z D_Y W_tot B_W μ : ℕ}
    {W : ι → ℕ} {u : Fin (r + 1) → (ι → F)}
    {S : F[X][X][X]} {Fstar : F[X][X]} {x₀ : F} {T'' : Finset F}
    (hμ_char : μ = 1 ∨ ∃ (p e : ℕ), CharP F p ∧ p.Prime ∧ μ = p ^ e)
    (hS_deg : 1 ≤ S.natDegree) (hs_le_DY : S.natDegree ≤ D_Y) (hW_tot_pos : 1 ≤ W_tot)
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + (μ * d) * b ≤ D) (hS_degZ : degZ S ≤ B_Z)
    (hF_irred : Irreducible Fstar) (hF_prim : Fstar.IsPrimitive)
    (hF_deg1 : 1 ≤ Fstar.natDegree) (hF_deg_le : Fstar.natDegree ≤ S.natDegree)
    (hF_degZ : degZ₂ Fstar ≤ B_Z)
    (hT''_card : W_tot * D_Y * (4 * D * B_Z + r * D_Y) < #T'')
    (hT''_mem : ∀ z ∈ T'', ∃ P : F[X], P.natDegree ≤ d ∧ (evZ₂ z S).eval (P ^ μ) = 0 ∧
      (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
      ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
        ((P ^ μ).eval x₀) ≠ 0 ∧
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i)
    {n : ℕ} (hn1 : 1 ≤ n) (hnD : n ≤ D) (hcond : μ * d < n ∨ ¬ μ ∣ n) :
    Fstar.map (algebraMap F[X] (FractionRing F[X])) ∣
      (recPoly S x₀ S.natDegree n).map (algebraMap F[X] (FractionRing F[X])) := by
  let K := FractionRing F[X]
  let ι_K : F[X] →+* K := algebraMap F[X] K
  set Nn := recPoly S x₀ S.natDegree n
  by_cases hNn0 : Nn = 0
  · rw [hNn0, Polynomial.map_zero]; exact dvd_zero _
  · set Res_n : F[X] := Polynomial.resultant Fstar Nn Fstar.natDegree Nn.natDegree
    have hRes_van : ∀ z ∈ T'', Res_n.eval z = 0 := fun z hz => by
      obtain ⟨P, hP_deg, hS_ev0, hF_ev0, hγ_ev_ne, _⟩ := hT''_mem z hz
      have hrec := spec_recPoly_at_point hS_deg hS_wd hS_ev0 hγ_ev_ne n hn1
      have hW0 : (taylor x₀ (P ^ μ)).coeff n = 0 := by
        rcases hcond with hgt | hndiv
        · exact coeff_eq_zero_of_natDegree_lt (by
            rw [natDegree_taylor]
            exact (natDegree_pow_le.trans (Nat.mul_le_mul_left μ hP_deg)).trans_lt hgt)
        · rcases hμ_char with rfl | ⟨p, e, _, hp, rfl⟩
          · exact absurd (one_dvd n) hndiv
          · have ht_pow : taylor x₀ (P ^ p ^ e) = (taylor x₀ P) ^ p ^ e :=
              map_pow (Polynomial.taylorAlgHom x₀) P (p ^ e)
            rw [ht_pow]
            exact coeff_pow_prime_pow_eq_zero_of_not_dvd hp (taylor x₀ P) hndiv
      rw [hW0, mul_zero] at hrec
      exact eval_resultant_eq_zero_of_common_root (Or.inl (by omega)) hF_ev0 hrec.symm
    have hNn_degZ : degZ₂ Nn ≤ (2 * n - 1) * B_Z := degZ₂_recPoly_le hS_degZ n hn1
    have hres := (DegBound.natDegree F).resultant_le Fstar.natDegree Nn.natDegree
      (degZ₂_le_iff.1 hF_degZ) (degZ₂_le_iff.1 hNn_degZ)
    have h1 : Fstar.natDegree * ((2 * n - 1) * B_Z) ≤ 2 * D * D_Y * B_Z :=
      (Nat.mul_le_mul (hF_deg_le.trans hs_le_DY)
        (Nat.mul_le_mul_right B_Z (show 2 * n - 1 ≤ 2 * D by omega))).trans_eq (by ring)
    have h2 : Nn.natDegree * B_Z ≤ 2 * D * D_Y * B_Z := Nat.mul_le_mul_right B_Z <|
      (natDegree_recPoly_le le_rfl n hn1).trans (Nat.mul_le_mul (by omega) hs_le_DY)
    have hlt : Res_n.natDegree < #T'' := by
      have htot : 1 * D_Y * (4 * D * B_Z) ≤ W_tot * D_Y * (4 * D * B_Z + r * D_Y) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right D_Y hW_tot_pos) (Nat.le_add_right _ _)
      have : Res_n.natDegree ≤ 4 * D * D_Y * B_Z :=
        hres.trans ((Nat.add_le_add h1 h2).trans_eq (by ring))
      linarith [show 4 * D * D_Y * B_Z = 1 * D_Y * (4 * D * B_Z) by ring]
    by_contra hndvd
    exact resultant_ne_zero_of_isCoprime_map ι_K (IsFractionRing.injective F[X] K)
      (((hF_prim.irreducible_iff_irreducible_map_fraction_map (K := K)).1 hF_irred
        ).coprime_iff_not_dvd.2 hndvd)
      (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Res_n T'' hRes_van hlt)

/-- Step 6: Resultant-kill excess and non-`μ`-divisible recurrence polynomials, lift to
`L := AlgebraicClosure (FractionRing F[Z])`, truncate to a polynomial root `Ψ_trunc`, extract
its Frobenius `μ`-th root `P* ∈ L[X]`, and package the mismatch resultant bounds for Step 7. -/
theorem exists_lifted_poly_and_mismatch_bound {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} {r d D B_Z D_Y W_tot B_W μ : ℕ}
    {W : ι → ℕ} {u : Fin (r + 1) → (ι → F)}
    {R S : F[X][X][X]} {Δ Fstar : F[X][X]} {x₀ : F} {T'' : Finset F}
    (hμ_char : μ = 1 ∨ ∃ (p e : ℕ), CharP F p ∧ p.Prime ∧ μ = p ^ e)
    (hμ_pos : 1 ≤ μ)
    (hS_deg : 1 ≤ S.natDegree)
    (hdeg_mul : μ * S.natDegree = R.natDegree)
    (hR_deg_le : R.natDegree ≤ D_Y)
    (hDY_pos : 1 ≤ D_Y) (hD_pos : 1 ≤ D) (hW_tot_pos : 1 ≤ W_tot)
    (hμd_le : μ * d ≤ D)
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + (μ * d) * b ≤ D)
    (hS_degZ : degZ S ≤ B_Z)
    (hΔ_x₀_ne : Δ.eval (C x₀) ≠ 0)
    (hbez₀ : ∃ A₀ B₀ : F[X][X],
      (S.map (Polynomial.evalRingHom (C x₀))) * A₀ +
        (S.map (Polynomial.evalRingHom (C x₀))).derivative * B₀ = C (Δ.eval (C x₀)))
    (hF_irred : Irreducible Fstar)
    (hF_prim : Fstar.IsPrimitive)
    (hF_deg1 : 1 ≤ Fstar.natDegree)
    (hF_deg_le : Fstar.natDegree ≤ S.natDegree)
    (hF_degZ : degZ₂ Fstar ≤ B_Z)
    (hF_dvd : Fstar ∣ S.map (Polynomial.evalRingHom (C x₀)))
    (hT''_card : W_tot * D_Y * (4 * D * B_Z + r * D_Y) < #T'')
    (hT''_mem : ∀ z ∈ T'',
      ∃ P : F[X], P.natDegree ≤ d ∧
        (evZ₂ z S).eval (P ^ μ) = 0 ∧
        (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
        ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
          ((P ^ μ).eval x₀) ≠ 0 ∧
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i) :
    let K := FractionRing F[X]
    let L := AlgebraicClosure K
    let j_L : F[X] →+* L := (algebraMap K L).comp (algebraMap F[X] K)
    ∃ (Pstar : L[X]) (Istar : Finset ι),
      Pstar.natDegree ≤ d ∧
      (∀ i ∈ Istar, Pstar.eval (j_L (C (α i))) = j_L (curveWord u i)) ∧
      (∀ i ∉ Istar, ∃ res : F[X], res ≠ 0 ∧
        res.natDegree ≤ 4 * D * D_Y * B_Z + r * D_Y ^ 2 ∧
        ∀ z ∈ T'', ∀ P : F[X], P.natDegree ≤ d →
          (evZ₂ z S).eval (P ^ μ) = 0 →
          (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 →
          ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
            ((P ^ μ).eval x₀) ≠ 0 →
          P.eval (α i) = (curveWord u i).eval z → res.eval z = 0) := by
  classical
  set s := S.natDegree
  set γ := (S.map (Polynomial.evalRingHom (C x₀))).derivative
  have hs_le_DY : s ≤ D_Y := (Nat.le_mul_of_pos_left s hμ_pos).trans (hdeg_mul.trans_le hR_deg_le)
  let K := FractionRing F[X]; let L := AlgebraicClosure K
  let ι_K : F[X] →+* K := algebraMap F[X] K; let ι_L : K →+* L := algebraMap K L
  let j_L : F[X] →+* L := ι_L.comp ι_K
  have hι_K_inj : Function.Injective ι_K := IsFractionRing.injective F[X] K
  have hj_L_inj : Function.Injective j_L := (RingHom.injective ι_L).comp hι_K_inj
  obtain ⟨ystar, hystar⟩ := IsAlgClosed.exists_root (Fstar.map j_L) <| by
    rw [degree_map_eq_of_injective hj_L_inj]; exact (natDegree_pos_iff_degree_pos.1 hF_deg1).ne'
  let φstar : F[X][X] →+* L := Polynomial.eval₂RingHom j_L ystar
  have hφstar_eq (f : F[X][X]) : φstar f = (f.map j_L).eval ystar := by
    simp [φstar, Polynomial.eval_map]
  have hφstar_dvd_zero {g : F[X][X]} (hd : Fstar.map ι_K ∣ g.map ι_K) : φstar g = 0 := by
    rcases hd with ⟨qK, hqK⟩
    have hm := congrArg (Polynomial.map ι_L) hqK
    rw [Polynomial.map_mul, Polynomial.map_map, Polynomial.map_map] at hm
    rw [hφstar_eq, hm, eval_mul, hystar, zero_mul]
  have hφstar_γ : φstar γ ≠ 0 := fun h0 => by
    obtain ⟨A₀, B₀, hAB⟩ := hbez₀
    have hF0 : φstar Fstar = 0 := by rw [hφstar_eq]; exact hystar
    rcases hF_dvd with ⟨Q', hQ'⟩
    have hS0 : φstar (S.map (Polynomial.evalRingHom (C x₀))) = 0 := by
      rw [hQ', map_mul, hF0, zero_mul]
    have hm := congrArg φstar hAB
    simp only [map_add, map_mul, hS0, zero_mul, zero_add, h0] at hm
    exact hΔ_x₀_ne (hj_L_inj (by simpa [φstar] using hm.symm))
  set gstar : L := φstar γ
  set Ψ_trunc : L[X] := C ystar + ∑ k ∈ Icc 1 (μ * d),
    C (φstar (recPoly S x₀ s k) / gstar ^ (2 * k - 1)) * X ^ k
  have hΨ_deg : Ψ_trunc.natDegree ≤ μ * d :=
    (natDegree_add_le _ _).trans <| max_le (by simp) <| (natDegree_sum_le _ _).trans <|
      Finset.sup_le fun k hk => natDegree_mul_le.trans (by
        rw [natDegree_C, zero_add, natDegree_X_pow]; exact (mem_Icc.1 hk).2)
  have hΨ_coeff0 : Ψ_trunc.coeff 0 = ystar := by
    rw [coeff_add, coeff_C_zero, coeff_sum_Icc_C_mul_X_pow, ite_eq_right (by omega), add_zero]
  have hΨ_coeff (k : ℕ) (hk1 : 1 ≤ k) : Ψ_trunc.coeff k =
      if k ≤ μ * d then φstar (recPoly S x₀ s k) / gstar ^ (2 * k - 1) else 0 := by
    rw [coeff_add, coeff_C, ite_eq_right (by omega), zero_add, coeff_sum_Icc_C_mul_X_pow]
    simp [hk1]
  have hμ_char_L : μ = 1 ∨ ∃ (p e : ℕ), CharP L p ∧ p.Prime ∧ μ = p ^ e :=
    hμ_char.imp_right fun ⟨p, e, _, hp, he⟩ =>
      ⟨p, e, charP_of_injective_ringHom (f := j_L.comp C) (hj_L_inj.comp C_injective) p, hp, he⟩
  obtain ⟨Ptilde, hPtilde_deg, hPtilde_pow⟩ := exists_pow_eq_poly_of_not_dvd hμ_pos hμ_char_L
    hΨ_deg fun k hndiv => by
      have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h0 => hndiv (h0 ▸ dvd_zero μ)
      rw [hΨ_coeff k hk1]
      split_ifs with hkle
      · rw [hφstar_dvd_zero (map_recPoly_dvd_of_kill hμ_char hS_deg hs_le_DY hW_tot_pos hS_wd
          hS_degZ hF_irred hF_prim hF_deg1 hF_deg_le hF_degZ hT''_card hT''_mem hk1
          (hkle.trans hμd_le) (Or.inr hndiv)), zero_div]
      · rfl
  set Pstar : L[X] := taylor (-j_L (C x₀)) Ptilde
  let Istar : Finset ι := Finset.univ.filter fun i =>
    Pstar.eval (j_L (C (α i))) = j_L (curveWord u i)
  refine ⟨Pstar, Istar, by rwa [natDegree_taylor], fun i hi => (mem_filter.1 hi).2,
    fun i hi_not => ?_⟩
  set Ei : F[X][X] := evalMismatchPoly S x₀ s μ d (α i) (curveWord u i)
  have hφstar_Ei_ne : φstar Ei ≠ 0 := by
    have hmap := map_evalMismatchPoly (α i) (curveWord u i) φstar hΨ_deg
      (by rw [hΨ_coeff0]; simp [φstar]) fun k hk => by
        rw [hΨ_coeff k (mem_Icc.1 hk).1, ite_eq_left (mem_Icc.1 hk).2]
        exact mul_div_cancel₀ _ (pow_ne_zero _ hφstar_γ)
    have hPstar_pow : Pstar ^ μ = taylor (-j_L (C x₀)) Ψ_trunc := by
      rw [← hPtilde_pow]; exact (map_pow (Polynomial.taylorAlgHom (-j_L (C x₀))) Ptilde μ).symm
    rw [show φstar (C (C (α i - x₀))) = j_L (C (α i)) - j_L (C x₀) by simp [φstar, map_sub],
      show φstar (C (curveWord u i)) = j_L (curveWord u i) by simp [φstar],
      show Ψ_trunc.eval (j_L (C (α i)) - j_L (C x₀)) = (Pstar.eval (j_L (C (α i)))) ^ μ by
        rw [← eval_pow, hPstar_pow, Polynomial.taylor_eval, sub_eq_add_neg]] at hmap
    rw [hmap]
    exact mul_ne_zero (pow_ne_zero _ hφstar_γ) fun h0 =>
      hi_not (mem_filter.2 ⟨mem_univ i, eq_of_pow_eq_of_char_pow hμ_char_L (sub_eq_zero.1 h0)⟩)
  have hcop : IsCoprime (Fstar.map ι_K) (Ei.map ι_K) :=
    ((hF_prim.irreducible_iff_irreducible_map_fraction_map (K := K)).1 hF_irred
      ).coprime_iff_not_dvd.2 fun hd => hφstar_Ei_ne (hφstar_dvd_zero hd)
  refine ⟨Polynomial.resultant Fstar Ei Fstar.natDegree Ei.natDegree,
    resultant_ne_zero_of_isCoprime_map ι_K hι_K_inj hcop,
    resultant_evalMismatch_natDegree_le α i hμ_pos hS_deg hDY_pos hD_pos
      (hdeg_mul.trans_le hR_deg_le) hμd_le hS_degZ hF_deg_le hF_degZ,
    fun z _ P hP_deg hS_ev0 hF_ev0 hγ_ev_ne hagree => ?_⟩
  let φz : F[X][X] →+* F := Polynomial.eval₂RingHom (evZ z) ((P ^ μ).eval x₀)
  have hφz_eq (f : F[X][X]) : φz f = (f.map (evZ z)).eval ((P ^ μ).eval x₀) := by
    simp [φz, Polynomial.eval_map]
  have hEi_z0 : (Ei.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 := by
    rw [← hφz_eq, map_evalMismatchPoly (α i) (curveWord u i) φz (W := taylor x₀ (P ^ μ))
      (by rw [natDegree_taylor]; exact natDegree_pow_le.trans (Nat.mul_le_mul_left μ hP_deg))
      (by rw [taylor_coeff_zero]; simp [φz]) fun k hk => by
        have hrec := spec_recPoly_at_point hS_deg hS_wd hS_ev0 hγ_ev_ne k (mem_Icc.1 hk).1
        rwa [← hφz_eq, ← hφz_eq] at hrec]
    rw [show φz (C (C (α i - x₀))) = α i - x₀ by simp [φz, evZ],
      show φz (C (curveWord u i)) = (curveWord u i).eval z by simp [φz, evZ],
      Polynomial.taylor_eval, sub_add_cancel, eval_pow, hagree, sub_self, mul_zero]
  exact eval_resultant_eq_zero_of_common_root (Or.inl (by omega)) hF_ev0 hEi_z0

end Cslib.Code.ProximityGap
