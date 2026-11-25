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
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap

/-!
# Step 4: Choosing a Non-Degenerate Evaluation Point and Factor Shift

Selects an evaluation coordinate `x₀ ∈ F` where the discriminant / resultant polynomial `Δ`
does not vanish identically and refines the close scalar subset `T₁` to `T'` avoiding the zero
locus of `Δ(Z, x₀)`.

## Main results

* `Cslib.Code.ProximityGap.exists_good_shift_and_factor`: finds a good shift `x₀` and surviving
  scalar set `T'`.
-/

public section

namespace Cslib.Code.ProximityGap

open Cslib.Code Finset Polynomial Polynomial.Bivariate

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι]

private theorem exists_eval_ne_zero_of_natDegree_lt_card {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : p ≠ 0) {T : Finset R} (hlt : p.natDegree < #T) :
    ∃ x ∈ T, p.eval x ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p T hall hlt)

private theorem exists_eval_C_ne_zero {F : Type*} [Field F] {H : F[X][X]} (hH : H ≠ 0)
    {T : Finset F} (hT : H.natDegree < #T) :
    ∃ x₀ ∈ T, H.eval (C x₀) ≠ 0 := by
  have hex_j : ∃ j, (Bivariate.swap H).coeff j ≠ 0 := by
    by_contra hall; push Not at hall
    exact (map_ne_zero_iff _ Bivariate.swap.injective).2 hH (by ext j : 2; simpa using hall j)
  obtain ⟨j, hj_ne⟩ := hex_j
  have hdeg : ((Bivariate.swap H).coeff j).natDegree ≤ H.natDegree := by
    simpa only [Bivariate.swap_swap_apply] using
      Bivariate.natDegree_coeff_le_natDegree_swap (Bivariate.swap H) j
  obtain ⟨x₀, hx₀, hne⟩ := exists_eval_ne_zero_of_natDegree_lt_card hj_ne (hdeg.trans_lt hT)
  refine ⟨x₀, hx₀, fun hH0 => hne ?_⟩
  have hc := congrArg (fun p : F[X] => p.coeff j) hH0
  rw [eval_eq_sum_range, finsetSum_coeff, coeff_zero] at hc
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), ← hc]
  exact Finset.sum_congr rfl fun a _ => by
    rw [← C_pow, mul_comm (H.coeff a), coeff_C_mul, coeff_coeff_swap, mul_comm]

/-- Step 4: Pick a good shift point `x₀ ∈ T_R` with `(S.leadingCoeff * Δ)(Z, x₀) ≠ 0`, and
pigeonhole onto a primitive irreducible factor `F_* ∈ F[Z][Y]` of `S₀(Z, Y) = S(Z, x₀, Y)`. -/
theorem exists_good_shift_and_factor
    {α : ι → F} {r d D B_Z D_Y W_tot B_W μ : ℕ}
    {W : ι → ℕ} {u : Fin (r + 1) → (ι → F)}
    {R S A_bez B_bez : F[X][X][X]} {Δ : F[X][X]} {T_R : Finset F}
    (hμ_pos : 1 ≤ μ)
    (hexp_S : Polynomial.expand (F[X][X]) μ S = R)
    (hS_deg : 1 ≤ S.natDegree)
    (hdeg_mul : μ * S.natDegree = R.natDegree)
    (hS_degZ : degZ S ≤ B_Z)
    (hΔ_ne : Δ ≠ 0)
    (hbez : S * A_bez + S.derivative * B_bez = C Δ)
    (hH_degX : (S.leadingCoeff * Δ).natDegree ≤ 2 * S.natDegree * D)
    (hH_degZ : degZ₂ (S.leadingCoeff * Δ) ≤ 2 * S.natDegree * B_Z)
    (hTR_card : 2 * R.natDegree * (D + B_Z) +
        W_tot * R.natDegree * D_Y * (4 * D * B_Z + r * D_Y) < #T_R)
    (hTR_mem : ∀ z ∈ T_R, ∃ P : F[X], P.natDegree ≤ d ∧ (evZ₂ z R).eval P = 0 ∧
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i) :
    ∃ (x₀ : F) (Fstar : F[X][X]) (T'' : Finset F),
      (S.map (Polynomial.evalRingHom (C x₀))).natDegree = S.natDegree ∧
      degZ₂ (S.map (Polynomial.evalRingHom (C x₀))) ≤ B_Z ∧
      Δ.eval (C x₀) ≠ 0 ∧
      (∃ A₀ B₀ : F[X][X],
        (S.map (Polynomial.evalRingHom (C x₀))) * A₀ +
          (S.map (Polynomial.evalRingHom (C x₀))).derivative * B₀ = C (Δ.eval (C x₀))) ∧
      Irreducible Fstar ∧
      Fstar.IsPrimitive ∧
      1 ≤ Fstar.natDegree ∧
      Fstar.natDegree ≤ S.natDegree ∧
      degZ₂ Fstar ≤ B_Z ∧
      Fstar ∣ S.map (Polynomial.evalRingHom (C x₀)) ∧
      T'' ⊆ T_R ∧
      W_tot * D_Y * (4 * D * B_Z + r * D_Y) < #T'' ∧
      (∀ z ∈ T'',
        (S.leadingCoeff.eval (C x₀)).eval z ≠ 0 ∧
        (Δ.eval (C x₀)).eval z ≠ 0 ∧
        ∃ P : F[X], P.natDegree ≤ d ∧
          (evZ₂ z S).eval (P ^ μ) = 0 ∧
          (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
          ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
            ((P ^ μ).eval x₀) ≠ 0 ∧
          B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z),
            W i) := by
  classical
  set s := S.natDegree
  have hs_le_dR : s ≤ R.natDegree := by
    have := Nat.mul_le_mul_right s hμ_pos; omega
  set H : F[X][X] := S.leadingCoeff * Δ
  have hH_ne : H ≠ 0 := mul_ne_zero (leadingCoeff_ne_zero.2 fun h => by simp [s, h] at hS_deg) hΔ_ne
  obtain ⟨x₀, _, hHx₀_ne⟩ := exists_eval_C_ne_zero (T := T_R) hH_ne (hH_degX.trans_lt <|
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hs_le_dR) (Nat.le_add_right D B_Z)).trans_lt
      ((Nat.le_add_right _ _).trans_lt hTR_card))
  have hlc_x₀_ne : S.leadingCoeff.eval (C x₀) ≠ 0 := fun h0 => hHx₀_ne (by simp [H, h0])
  have hΔ_x₀_ne : Δ.eval (C x₀) ≠ 0 := fun h0 => hHx₀_ne (by simp [H, h0])
  let φx₀ : F[X][X] →+* F[X] := Polynomial.evalRingHom (C x₀)
  set S₀ : F[X][X] := S.map φx₀
  have hS₀_deg : S₀.natDegree = s := le_antisymm Polynomial.natDegree_map_le
    (le_natDegree_of_ne_zero (by rw [coeff_map]; exact hlc_x₀_ne))
  have hS₀_ne : S₀ ≠ 0 := fun h => by simp [h] at hS₀_deg; omega
  have hS₀_degZ : degZ₂ S₀ ≤ B_Z := degZ₂_le_iff.2 fun b => by
    rw [coeff_map]
    exact (natDegree_eval_C_le_degZ₂ (S.coeff b) x₀).trans ((degZ₂_coeff_le_degZ S b).trans hS_degZ)
  have hbez₀ : ∃ A₀ B₀ : F[X][X], S₀ * A₀ + S₀.derivative * B₀ = C (Δ.eval (C x₀)) :=
    ⟨A_bez.map φx₀, B_bez.map φx₀, by
      simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        ← Polynomial.derivative_map, φx₀, coe_evalRingHom] using congrArg (Polynomial.map φx₀) hbez⟩
  let T'_R := T_R.filter fun z => (H.eval (C x₀)).eval z ≠ 0
  have hT'_card : #T_R - 2 * s * B_Z ≤ #T'_R := by
    have h := Finset.card_filter_add_card_filter_not (s := T_R)
      (p := fun z => (H.eval (C x₀)).eval z = 0)
    have hbad := (card_filter_eval_eq_zero_le hHx₀_ne T_R).trans
      ((natDegree_eval_C_le_degZ₂ H x₀).trans hH_degZ)
    change #(T_R.filter fun z => (H.eval (C x₀)).eval z = 0) + #T'_R = #T_R at h
    omega
  obtain ⟨c₀, gs, _, hgs_prop, hS₀_eq, _⟩ :=
    Polynomial.Bivariate.exists_eq_C_mul_prod_irreducible hS₀_ne
  have hgs_card : #gs.toFinset ≤ s := by
    have hdvd : ∏ G ∈ gs.toFinset, G ∣ S₀ :=
      (Multiset.toFinset_prod_dvd_prod gs).trans ⟨C c₀, by rw [hS₀_eq, mul_comm]⟩
    calc #gs.toFinset = ∑ _G ∈ gs.toFinset, 1 := by simp
      _ ≤ ∑ G ∈ gs.toFinset, G.natDegree :=
          Finset.sum_le_sum fun G hG => (hgs_prop G (Multiset.mem_toFinset.1 hG)).2.2
      _ = (∏ G ∈ gs.toFinset, G).natDegree := (Polynomial.natDegree_prod _ _ fun G hG =>
          (hgs_prop G (Multiset.mem_toFinset.1 hG)).1.ne_zero).symm
      _ ≤ s := hS₀_deg ▸ Polynomial.natDegree_le_of_dvd hdvd hS₀_ne
  have hS₀_map_evZ (z : F) : S₀.map (evZ z) = (evZ₂ z S).map (Polynomial.evalRingHom x₀) := by
    rw [Polynomial.map_map, evZ₂, Polynomial.coe_mapRingHom, Polynomial.map_map]
    congr 1; apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext' <;> [ext c; skip] <;> simp [evZ, evZ₁, φx₀]
    · simp [evZ, evZ₁, φx₀]
  let T_ofG : F[X][X] → Finset F := fun G => T'_R.filter fun z =>
    ∃ P : F[X], P.natDegree ≤ d ∧ (evZ₂ z S).eval (P ^ μ) = 0 ∧
      (G.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
      (S₀.derivative.map (evZ z)).eval ((P ^ μ).eval x₀) ≠ 0 ∧
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i
  have hcover' : T'_R ⊆ gs.toFinset.biUnion T_ofG := fun z hz => by
    obtain ⟨hz_TR, hHz_ne⟩ := mem_filter.1 hz
    obtain ⟨P, hP_deg, hR_eval0, hW_P⟩ := hTR_mem z hz_TR
    have hS_eval0 : (evZ₂ z S).eval (P ^ μ) = 0 := by
      have hmap : evZ₂ z R = Polynomial.expand F[X] μ (evZ₂ z S) := by
        rw [← hexp_S, evZ₂, Polynomial.coe_mapRingHom, Polynomial.map_expand]
      rwa [hmap, Polynomial.expand_eval] at hR_eval0
    set yz : F := (P ^ μ).eval x₀
    have hS₀_eval0 : (S₀.map (evZ z)).eval yz = 0 := by
      rw [hS₀_map_evZ z, Polynomial.eval_map]
      have hhom := Polynomial.hom_eval₂ (evZ₂ z S) (RingHom.id F[X])
        (Polynomial.evalRingHom x₀) (P ^ μ)
      rw [RingHom.comp_id, Polynomial.eval₂_id] at hhom
      change (evZ₂ z S).eval₂ (Polynomial.evalRingHom x₀) (Polynomial.evalRingHom x₀ (P ^ μ)) = 0
      rw [← hhom, hS_eval0, map_zero]
    have hγ_eval_ne : (S₀.derivative.map (evZ z)).eval yz ≠ 0 := fun hγ0 => by
      obtain ⟨A₀, B₀, hAB⟩ := hbez₀
      have hm := congrArg (fun p : F[X][X] => (p.map (evZ z)).eval yz) hAB
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, eval_add, eval_mul,
        eval_C, hS₀_eval0, zero_mul, zero_add, hγ0] at hm
      exact hHz_ne (by
        have hΔ0 : (Δ.eval (C x₀)).eval z = 0 := by simpa only [evZ, coe_evalRingHom] using hm.symm
        simp only [H, eval_mul, hΔ0, mul_zero])
    have hc₀_z_ne : c₀.eval z ≠ 0 := fun h0 => hHz_ne <| by
      have hlc : S.leadingCoeff.eval (C x₀) = c₀ * gs.prod.leadingCoeff := by
        calc S.leadingCoeff.eval (C x₀) = S₀.coeff S₀.natDegree := by
              rw [hS₀_deg, coeff_map]; rfl
          _ = c₀ * gs.prod.leadingCoeff := by
              change S₀.leadingCoeff = _
              rw [hS₀_eq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      simp only [H, eval_mul, hlc, eval_mul, h0, zero_mul]
    rw [hS₀_eq, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C] at hS₀_eval0
    obtain ⟨G, hG_mem, hv0⟩ :=
      exists_mem_eval_map_eq_zero (evZ z) gs yz ((mul_eq_zero.1 hS₀_eval0).resolve_left hc₀_z_ne)
    exact mem_biUnion.2 ⟨G, Multiset.mem_toFinset.2 hG_mem,
      mem_filter.2 ⟨hz, P, hP_deg, hS_eval0, hv0, hγ_eval_ne, hW_P⟩⟩
  set B_step := W_tot * D_Y * (4 * D * B_Z + r * D_Y)
  have hsum_G : ∑ _G ∈ gs.toFinset, B_step < ∑ G ∈ gs.toFinset, #(T_ofG G) := by
    have h1 : 2 * s * B_Z ≤ 2 * R.natDegree * (D + B_Z) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hs_le_dR) (Nat.le_add_left B_Z D)
    have h2 : s * B_step ≤ W_tot * R.natDegree * D_Y * (4 * D * B_Z + r * D_Y) := by
      rw [show s * B_step = W_tot * s * D_Y * (4 * D * B_Z + r * D_Y) by dsimp [B_step]; ring]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs_le_dR))
    have h3 : ∑ _G ∈ gs.toFinset, B_step ≤ s * B_step := by
      rw [Finset.sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right B_step hgs_card
    have h4 : #T'_R ≤ ∑ G ∈ gs.toFinset, #(T_ofG G) :=
      (card_le_card hcover').trans Finset.card_biUnion_le
    omega
  obtain ⟨Fstar, hF_fin, hF_card⟩ := Finset.exists_lt_of_sum_lt hsum_G
  have hF_mem := Multiset.mem_toFinset.1 hF_fin
  obtain ⟨hF_irred, hF_prim, hF_deg1⟩ := hgs_prop Fstar hF_mem
  have hF_dvd : Fstar ∣ S₀ := (Multiset.dvd_prod hF_mem).trans ⟨C c₀, by rw [hS₀_eq, mul_comm]⟩
  have hF_degZ : degZ₂ Fstar ≤ B_Z := by
    obtain ⟨Q', hQ'⟩ := hF_dvd
    have hQ'0 : Q' ≠ 0 := fun h => hS₀_ne (by rw [hQ', h, mul_zero])
    have hmul := degZ₂_mul hF_irred.ne_zero hQ'0
    rw [← hQ'] at hmul; omega
  exact ⟨x₀, Fstar, T_ofG Fstar, hS₀_deg, hS₀_degZ, hΔ_x₀_ne, hbez₀, hF_irred, hF_prim, hF_deg1,
    (Polynomial.natDegree_le_of_dvd hF_dvd hS₀_ne).trans hS₀_deg.le, hF_degZ, hF_dvd,
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _), hF_card, fun z hz =>
    let hz1 := mem_filter.1 hz; let hz2 := mem_filter.1 hz1.1
    ⟨fun h0 => hz2.2 (by simp [H, h0]), fun h0 => hz2.2 (by simp [H, h0]), hz1.2⟩⟩

end Cslib.Code.ProximityGap
