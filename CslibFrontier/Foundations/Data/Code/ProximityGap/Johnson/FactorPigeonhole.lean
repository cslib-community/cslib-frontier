/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.Bounds
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.DegZ
public import CslibFrontier.Foundations.Data.Code.ReedSolomon
import CslibFrontier.Foundations.Data.Code.GuruswamiSudan
import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.Siegel
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Step 2: Irreducible Factor Extraction and Pigeonhole Selection

Factors the Siegel interpolant `Q(Z, X, Y)` over the UFD `F[Z][X][Y]` and applies a
weighted pigeonhole / Guruswami–Sudan root-multiplicity argument to select a single
irreducible factor `R(Z, X, Y)` explaining at least `|T| / maxYDeg` close curve points.

## Main results

* `Cslib.Code.ProximityGap.exists_irreducible_factor_pigeonhole`: extracts a `Y`-positive-degree
  irreducible factor `R` matching a large scalar set `T₁ ⊆ T`.
-/

public section

namespace Cslib.Code.ProximityGap

open Cslib.Code Cslib.Code.GuruswamiSudan Finset Polynomial Polynomial.Bivariate

variable {F : Type*} [Field F]

private theorem eval_curveWord [DecidableEq F] {ι : Type*} {r : ℕ}
    (u : Fin (r + 1) → (ι → F)) (i : ι) (z : F) :
    (curveWord u i).eval z = ∑ j : Fin (r + 1), z ^ (j : ℕ) * u j i := by
  rw [curveWord, Polynomial.ofFn_eq_sum_monomial, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_monomial, mul_comm]

private theorem exists_eq_C_mul_prod_irreducible_of_ufd {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {Q : R[X]} (hQ : Q ≠ 0) :
    ∃ (c : R) (fs : Multiset R[X]),
      c ≠ 0 ∧
      (∀ f ∈ fs, Irreducible f ∧ 1 ≤ f.natDegree) ∧
      Q = C c * fs.prod := by
  classical
  let all := UniqueFactorizationMonoid.factors Q
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hQ
  let fs₀ := all.filter (fun f => f.natDegree = 0)
  let fs := all.filter (fun f => ¬ f.natDegree = 0)
  have hsplit : all = fs₀ + fs := (Multiset.filter_add_not _ all).symm
  have hirred : ∀ f ∈ all, Irreducible f := UniqueFactorizationMonoid.irreducible_of_factor
  have hfs₀_deg : fs₀.prod.natDegree = 0 := by
    have hne : ∀ f ∈ fs₀, f ≠ 0 := fun f hf =>
      (hirred f (Multiset.mem_of_mem_filter hf)).ne_zero
    rw [Polynomial.natDegree_multiset_prod fs₀ (fun h0 => hne 0 h0 rfl)]
    exact Multiset.sum_eq_zero fun n hn => by
      obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.1 hn
      exact (Multiset.mem_filter.1 hf).2
  have hu_deg : (u : R[X]).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit u.isUnit
  have hQ_eq : Q = C (fs₀.prod.coeff 0 * (u : R[X]).coeff 0) * fs.prod := by
    rw [C_mul, ← Polynomial.eq_C_of_natDegree_eq_zero hfs₀_deg,
      ← Polynomial.eq_C_of_natDegree_eq_zero hu_deg, ← hu]
    change (all.prod * (u : R[X])) = _
    rw [hsplit, Multiset.prod_add]
    ring
  have hc0 : fs₀.prod.coeff 0 * (u : R[X]).coeff 0 ≠ 0 := fun h0 =>
    hQ (by rw [hQ_eq, h0, map_zero, zero_mul])
  exact ⟨_, fs, hc0, fun f hf => ⟨hirred f (Multiset.mem_of_mem_filter hf),
    Nat.one_le_iff_ne_zero.2 (Multiset.mem_filter.1 hf).2⟩, hQ_eq⟩

private theorem weightedDegree_evZ₂_le {d : ℕ} (z : F) (Q : F[X][X][X]) :
    weightedDegree d (evZ₂ z Q) ≤ weightedDegree d Q :=
  weightedDegree_map_le (evZ z) d Q

private theorem card_filter_evZ₂_eq_zero_le [DecidableEq F] {Q : F[X][X][X]} (hQ : Q ≠ 0)
    (T : Finset F) :
    #(T.filter fun z => evZ₂ z Q = 0) ≤ degZ Q := by
  classical
  obtain ⟨b, a, hab⟩ : ∃ b a, (Q.coeff b).coeff a ≠ 0 := by
    by_contra! hall
    exact hQ (by ext b a : 4; simpa using hall b a)
  set c₀ : F[X] := (Q.coeff b).coeff a
  have hsub : T.filter (fun z => evZ₂ z Q = 0) ⊆ T.filter (fun z => c₀.eval z = 0) :=
    Finset.monotone_filter_right T fun z _ hz => by
      simpa [evZ₂, evZ₁, evZ, c₀] using congrArg (fun R : F[X][X] => (R.coeff b).coeff a) hz
  exact (card_le_card hsub).trans
    ((card_filter_eval_eq_zero_le hab T).trans (degZ_le_iff.1 le_rfl a b))

/-- Helper: a single weighted close point forces `1 ≤ W_tot` and `1 ≤ D` under the interpolation
condition `|ι| * (m * (m + 1) / 2) < #(Sudan.monomials d D)`. -/
private theorem pos_params_of_interpolation {ι : Type*} [Fintype ι] {W : ι → ℕ}
    {k m d D M W_tot B_W : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials d D))
    {A : Finset ι} (hA : B_W ≤ ∑ i ∈ A, W i) :
    1 ≤ W_tot ∧ 1 ≤ D := by
  have hB_pos : 1 ≤ B_W := by
    by_contra h0
    have hdiv : (B_W + M - 1) / M = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hcard_pos : 1 ≤ Fintype.card ι :=
    (hk.trans hk_le_t).trans ((ceil_div_le_card_of_sum_le hM hW_le hA).trans (card_le_univ _))
  refine ⟨hB_pos.trans (hA.trans ((sum_le_sum_of_subset (subset_univ _)).trans hW_sum)), ?_⟩
  by_contra h0
  obtain rfl : D = 0 := by omega
  have hpos : 0 < Fintype.card ι * (m * (m + 1) / 2) := Nat.mul_pos hcard_pos
    (Nat.div_pos ((Nat.succ_le_succ hm).trans (Nat.le_mul_of_pos_left _ hm)) zero_lt_two)
  have hmon0 : #(Sudan.monomials d 0) ≤ 1 := card_le_one.2 fun a ha b hb => by
    obtain ⟨ha1, ha2, _⟩ := Sudan.mem_monomials.1 ha
    obtain ⟨hb1, hb2, _⟩ := Sudan.mem_monomials.1 hb
    exact Prod.ext (by omega) (by omega)
  omega

/-- Step 2 (UFD factorization in `F[Z][X][Y]` and pigeonhole onto a single irreducible factor `R`).
-/
theorem exists_irreducible_factor_pigeonhole {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k r m D M W_tot B_W : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * ((B_W + M - 1) / M))
    (u : Fin (r + 1) → (ι → F))
    {T : Finset F}
    (hT : johnsonCurveBound (Fintype.card ι) m (k - 1) D r W_tot < #T)
    (hclose : ∀ z ∈ T, ∃ v ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) * u j i) = v i),
        W i) :
    ∃ (R : F[X][X][X]) (T_R : Finset F),
      Irreducible R ∧ 1 ≤ R.natDegree ∧
      R.natDegree ≤ maxYDeg (k - 1) D ∧
      weightedDegree (k - 1) R ≤ D ∧
      degZ R ≤ siegelZDeg (Fintype.card ι) m (k - 1) D r ∧
      1 ≤ maxYDeg (k - 1) D ∧ 1 ≤ D ∧ 1 ≤ W_tot ∧
      T_R ⊆ T ∧
      2 * R.natDegree * (D + siegelZDeg (Fintype.card ι) m (k - 1) D r) +
        W_tot * R.natDegree * maxYDeg (k - 1) D *
          (4 * D * siegelZDeg (Fintype.card ι) m (k - 1) D r + r * maxYDeg (k - 1) D) < #T_R ∧
      (∀ z ∈ T_R, ∃ P : F[X], P.natDegree ≤ k - 1 ∧ (evZ₂ z R).eval P = 0 ∧
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z),
          W i) := by
  classical
  set d := k - 1; set D_Y := maxYDeg d D; set B_Z := siegelZDeg (Fintype.card ι) m d D r
  obtain ⟨z₀, hz₀⟩ := Finset.card_pos.1 (Nat.zero_lt_of_lt hT)
  obtain ⟨v₀, _, hv₀⟩ := hclose z₀ hz₀
  obtain ⟨hW_tot_pos, hD_pos⟩ :=
    pos_params_of_interpolation hk hm hM hW_le hW_sum hk_le_t hinterp hv₀
  obtain ⟨Q, hQ0, hQwd, hQdeg, hQdegZ, hQvan⟩ := exists_siegel_interpolant α u hinterp
  obtain ⟨c, fs, _, hfs_prop, hQ_eq⟩ := exists_eq_C_mul_prod_irreducible_of_ufd hQ0
  have hsum_deg : ∑ R ∈ fs.toFinset, R.natDegree ≤ D_Y := by
    rw [← Polynomial.natDegree_prod _ _ fun R hR =>
      (hfs_prop R (Multiset.mem_toFinset.1 hR)).1.ne_zero]
    exact (Polynomial.natDegree_le_of_dvd
      ((Multiset.toFinset_prod_dvd_prod fs).trans ⟨C c, by rw [hQ_eq, mul_comm]⟩) hQ0).trans hQdeg
  let T_nz := T.filter fun z => evZ₂ z Q ≠ 0
  have hT_nz_card : #T - B_Z ≤ #T_nz := by
    have h := Finset.card_filter_add_card_filter_not (s := T) (p := fun z => evZ₂ z Q = 0)
    have hbad := (card_filter_evZ₂_eq_zero_le hQ0 T).trans hQdegZ
    change #(T.filter fun z => evZ₂ z Q = 0) + #T_nz = #T at h
    omega
  let T_of : F[X][X][X] → Finset F := fun R =>
    T.filter fun z => ∃ P : F[X], P.natDegree ≤ d ∧ (evZ₂ z R).eval P = 0 ∧
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i
  have hcover : T_nz ⊆ fs.toFinset.biUnion T_of := fun z hz => by
    obtain ⟨hzT, hQz_ne⟩ := mem_filter.1 hz
    obtain ⟨v, hv_rs, hv_agree⟩ := hclose z hzT
    obtain ⟨P, hP_deg, rfl⟩ := mem_reedSolomon.1 hv_rs
    have hP_natDeg : P.natDegree ≤ d := by
      by_cases hP0 : P = 0
      · simp [hP0]
      · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).2 hP_deg; omega
    have hW_P : B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z),
        W i := by
      simpa only [eval_curveWord, eq_comm] using hv_agree
    have hQz_interp : IsInterpolant α (fun i => (curveWord u i).eval z) m d D (evZ₂ z Q) :=
      ⟨hQz_ne,
        Polynomial.Bivariate.weightedDegree_le_iff.1 ((weightedDegree_evZ₂_le z Q).trans hQwd),
        fun i => by simpa [evZ₂, evZ₁, evZ] using (hQvan i).map (evZ z)⟩
    have heval0 : (evZ₂ z Q).eval P = 0 := hQz_interp.eval_eq_zero hα hP_natDeg
      (hroot.trans_le (Nat.mul_le_mul_left m (ceil_div_le_card_of_sum_le hM hW_le hW_P)))
    have hc_ev_ne : evZ₁ z c ≠ 0 := fun h0 => hQz_ne <| by
      rw [hQ_eq, map_mul, evZ₂, Polynomial.coe_mapRingHom, Polynomial.map_C, h0, map_zero, zero_mul]
    rw [hQ_eq, map_mul, eval_mul, evZ₂, Polynomial.coe_mapRingHom, Polynomial.map_C, eval_C]
      at heval0
    obtain ⟨R, hR_mem, hp0⟩ :=
      exists_mem_eval_map_eq_zero (evZ₁ z) fs P ((mul_eq_zero.1 heval0).resolve_left hc_ev_ne)
    exact mem_biUnion.2 ⟨R, Multiset.mem_toFinset.2 hR_mem,
      mem_filter.2 ⟨hzT, P, hP_natDeg, hp0, hW_P⟩⟩
  let B_of : F[X][X][X] → ℕ := fun R =>
    2 * R.natDegree * (D + B_Z) + W_tot * R.natDegree * D_Y * (4 * D * B_Z + r * D_Y)
  have hsum_B : ∑ R ∈ fs.toFinset, B_of R < #T_nz := by
    have h1 : ∑ R ∈ fs.toFinset, B_of R =
        (∑ R ∈ fs.toFinset, R.natDegree) *
          (2 * (D + B_Z) + W_tot * D_Y * (4 * D * B_Z + r * D_Y)) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun R _ => by dsimp only [B_of]; ring
    have h2 : ∑ R ∈ fs.toFinset, B_of R ≤
        2 * D_Y * (D + B_Z) + W_tot * D_Y ^ 2 * (4 * D * B_Z + r * D_Y) :=
      h1 ▸ (Nat.mul_le_mul_right _ hsum_deg).trans_eq (by ring)
    have h3 : B_Z + (2 * D_Y * (D + B_Z) + W_tot * D_Y ^ 2 * (4 * D * B_Z + r * D_Y)) < #T := by
      simpa [johnsonCurveBound, D_Y, B_Z, add_assoc] using hT
    omega
  obtain ⟨R, hR_fin, hR_card⟩ :=
    Finset.exists_lt_of_sum_lt <|
      hsum_B.trans_le ((card_le_card hcover).trans Finset.card_biUnion_le)
  have hR_mem := Multiset.mem_toFinset.1 hR_fin
  obtain ⟨hR_irred, hR_deg⟩ := hfs_prop R hR_mem
  have hR_dvd : R ∣ Q := (Multiset.dvd_prod hR_mem).trans ⟨C c, by rw [hQ_eq, mul_comm]⟩
  have hR_deg_le : R.natDegree ≤ D_Y := (Polynomial.natDegree_le_of_dvd hR_dvd hQ0).trans hQdeg
  exact ⟨R, T_of R, hR_irred, hR_deg, hR_deg_le, (weightedDegree_le_of_dvd hQ0 hR_dvd).trans hQwd,
    (degZ_le_of_dvd hQ0 hR_dvd).trans hQdegZ, hR_deg.trans hR_deg_le, hD_pos, hW_tot_pos,
    Finset.filter_subset _ _, hR_card, fun z hz => (mem_filter.1 hz).2⟩

end Cslib.Code.ProximityGap
