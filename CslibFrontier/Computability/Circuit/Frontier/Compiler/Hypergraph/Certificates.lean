/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Verified rational dual-LP certificates for bounded-fan-in hypergraphs

This module constructs six explicit `HyperDualCert` witnesses for bounded-fan-in circuits across
`r ∈ {3, 4, 8, 16, 64}`, combining all four straddling-probability regimes of
`CslibFrontier/Computability/Circuit/Frontier/Compiler/Hypergraph/Gaussian.lean`:

1. `cert_r3_sheppard` (`r = 3`, pure Sheppard + star-cone): `hyperCoeff > 44011 / 10000`, with
   `b < 0` (worst-case, average-case, and nondeterministic).
2. `cert_r3_slepian` (`r = 3`, Slepian + star-cone): `hyperCoeff > 44199 / 10000`, with `b < 0`
   (worst-case, average-case, and nondeterministic).
3. `cert_r4_sheppard` (`r = 4`, Sheppard + star-cone): `hyperCoeff > 44792 / 10000`, with `b < 0`
   (worst-case, average-case, and nondeterministic).
4. `cert_r8_slepian` (`r = 8`, Slepian + star-cone): `hyperCoeff > 46666 / 10000`, with `b = 0`
   (worst-case, average-case, and nondeterministic).
5. `cert_r16_slepian` (`r = 16`, Slepian + star-cone): `hyperCoeff > 49798 / 10000`
   (worst-case and average-case).
6. `cert_r64_slepian` (`r = 64`, Slepian): `hyperCoeff > 60012 / 10000`
   (worst-case and average-case).

Every numerical inequality is proved over `ℤ`, `ℚ`, and `ℝ` from `Real.cos_bound_ten`,
`Real.pi_gt_d20`, `Real.pi_lt_d20`, and `ProbabilityTheory.equicorrStraddle_le_of_poly` without
`native_decide`.

## Main results

* `Cslib.Circuits.Frontier.Hypergraph.cert_r3_sheppard`, `cert_r3_slepian`, `cert_r4_sheppard`,
  `cert_r8_slepian`, `cert_r16_slepian`, `cert_r64_slepian`: verified `HyperDualCert` witnesses.
-/

public section

namespace Cslib.Circuits.Frontier.Hypergraph

open ProbabilityTheory Real Set

/-! ### Rational `π`, `cos`, and `arccos / π` upper bounds -/

private abbrev piLo : ℚ := 314159265358979323846 / 10 ^ 20

private abbrev sqrtTwoPiHi : ℚ := 25066282747 / 10 ^ 10

private theorem piLo_lt_pi : (piLo : ℝ) < π := by
  have h := Real.pi_gt_d20
  push_cast [piLo]
  norm_num at h ⊢
  linarith

private theorem two_mul_pi_le_sq_sqrtTwoPiHi : 2 * π ≤ (sqrtTwoPiHi : ℝ) ^ 2 := by
  have h := Real.pi_lt_d20
  push_cast [sqrtTwoPiHi]
  norm_num at h ⊢
  linarith

private def qCosPoly (x : ℚ) : ℚ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320

private def qCosErr (x : ℚ) : ℚ :=
  x ^ 10 * (11 / 36288000)

private def qCosUpper (θ : ℚ) : ℚ :=
  if θ ≤ 7 / 10 then qCosPoly θ + qCosErr θ
  else 2 * (qCosPoly (θ / 2) + qCosErr (θ / 2)) ^ 2 - 1

private theorem cos_bounds_of_rat {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((qCosPoly x - qCosErr x : ℚ) : ℝ) ≤ cos (x : ℝ) ∧
      cos (x : ℝ) ≤ ((qCosPoly x + qCosErr x : ℚ) : ℝ) := by
  have hx0R : 0 ≤ (x : ℝ) := Rat.cast_nonneg.mpr hx0
  have habs : |(x : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg hx0R]
    exact_mod_cast hx1
  have hb := Real.cos_bound_ten habs
  rw [abs_of_nonneg hx0R, abs_le] at hb
  push_cast [qCosPoly, qCosErr]
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

private theorem cos_le_qCosUpper {θ : ℚ} (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hpos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2)) :
    cos (θ : ℝ) ≤ (qCosUpper θ : ℝ) := by
  unfold qCosUpper
  split_ifs with h7
  · exact (cos_bounds_of_rat hθ0 (h7.trans (by norm_num))).2
  · have hh0 : 0 ≤ θ / 2 := by linarith
    have hh1 : θ / 2 ≤ 1 := by linarith
    obtain ⟨hlo, hhi⟩ := cos_bounds_of_rat hh0 hh1
    have hcos_nn : 0 ≤ cos ((θ / 2 : ℚ) : ℝ) := (Rat.cast_nonneg.mpr hpos).trans hlo
    have hsq : cos ((θ / 2 : ℚ) : ℝ) ^ 2 ≤
        ((qCosPoly (θ / 2) + qCosErr (θ / 2) : ℚ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ hcos_nn hhi 2
    have h2mul : cos (θ : ℝ) = 2 * cos ((θ / 2 : ℚ) : ℝ) ^ 2 - 1 := by
      rw [show (θ : ℝ) = 2 * ((θ / 2 : ℚ) : ℝ) by push_cast; ring, Real.cos_two_mul]
    push_cast at h2mul hsq ⊢
    linarith

private theorem arccos_div_pi_le_of_qCosUpper {θ ρ_lo : ℚ} {ρ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hpos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2))
    (hcu : qCosUpper θ ≤ ρ_lo) (hρ_m1 : -1 ≤ ρ_lo)
    (hρ_lo : (ρ_lo : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1) :
    arccos ρ / π ≤ ((θ / piLo : ℚ) : ℝ) := by
  have hcos_le : cos (θ : ℝ) ≤ ρ :=
    (cos_le_qCosUpper hθ0 hθ2 hpos).trans ((Rat.cast_le.mpr hcu).trans hρ_lo)
  have hρ_ge : -1 ≤ ρ := (by exact_mod_cast hρ_m1 : (-1 : ℝ) ≤ ρ_lo).trans hρ_lo
  rw [← cos_arccos hρ_ge hρ1] at hcos_le
  have hθ_pi : (θ : ℝ) ≤ π := ((Rat.cast_le.mpr hθ2).trans (by norm_num)).trans Real.two_le_pi
  have hθ_mem : (θ : ℝ) ∈ Icc 0 π := ⟨Rat.cast_nonneg.mpr hθ0, hθ_pi⟩
  have harc_mem : arccos ρ ∈ Icc 0 π := ⟨arccos_nonneg ρ, arccos_le_pi ρ⟩
  have harc_le : arccos ρ ≤ (θ : ℝ) := by
    by_contra! hlt
    exact absurd (strictAntiOn_cos hθ_mem harc_mem hlt) (not_lt.mpr hcos_le)
  have hpiLo_pos : 0 < (piLo : ℝ) := by norm_num [piLo]
  calc arccos ρ / π ≤ (θ : ℝ) / π := div_le_div_of_nonneg_right harc_le pi_pos.le
    _ ≤ (θ : ℝ) / (piLo : ℝ) :=
        div_le_div_of_nonneg_left (Rat.cast_nonneg.mpr hθ0) hpiLo_pos piLo_lt_pi.le
    _ = ((θ / piLo : ℚ) : ℝ) := by push_cast; rfl

/-! ### Scaled integer evaluators for `qCosUpper` and `qMomentLower` -/

private def zCosPolyScale (xn : ℤ) (xd : ℕ) : ℤ :=
  let d : ℤ := xd
  36288000 * d ^ 10 - 18144000 * xn ^ 2 * d ^ 8 + 1512000 * xn ^ 4 * d ^ 6 -
    50400 * xn ^ 6 * d ^ 4 + 900 * xn ^ 8 * d ^ 2

private def zCosErrScale (xn : ℤ) : ℤ :=
  11 * xn ^ 10

private theorem zCosPolyScale_div {xn : ℤ} {xd : ℕ} (hxd : xd ≠ 0) :
    (zCosPolyScale xn xd : ℚ) / (36288000 * (xd : ℚ) ^ 10) = qCosPoly ((xn : ℚ) / (xd : ℚ)) := by
  have hd : (xd : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hxd
  unfold zCosPolyScale qCosPoly
  push_cast
  field_simp [hd]
  ring

private theorem zCosErrScale_div {xn : ℤ} {xd : ℕ} (hxd : xd ≠ 0) :
    (zCosErrScale xn : ℚ) / (36288000 * (xd : ℚ) ^ 10) = qCosErr ((xn : ℚ) / (xd : ℚ)) := by
  have hd : (xd : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hxd
  unfold zCosErrScale qCosErr
  push_cast
  field_simp [hd]

private def checkCosBounds (θn : ℤ) (θd : ℕ) (rn : ℤ) (rd : ℕ) : Bool :=
  decide (0 ≤ zCosPolyScale θn (2 * θd) - zCosErrScale θn) &&
    if 10 * θn ≤ 7 * (θd : ℤ) then
      decide ((zCosPolyScale θn θd + zCosErrScale θn) * (rd : ℤ) ≤
        rn * (36288000 * (θd : ℤ) ^ 10))
    else
      let S : ℤ := 36288000 * (2 * (θd : ℤ)) ^ 10
      decide ((2 * (zCosPolyScale θn (2 * θd) + zCosErrScale θn) ^ 2 - S ^ 2) * (rd : ℤ) ≤
        rn * S ^ 2)

private theorem cosBounds_of_check {θn rn : ℤ} {θd rd : ℕ} (hθd : 0 < θd) (hrd : 0 < rd)
    (hc : checkCosBounds θn θd rn rd = true) :
    0 ≤ qCosPoly (((θn : ℚ) / (θd : ℚ)) / 2) - qCosErr (((θn : ℚ) / (θd : ℚ)) / 2) ∧
      qCosUpper ((θn : ℚ) / (θd : ℚ)) ≤ (rn : ℚ) / (rd : ℚ) := by
  unfold checkCosBounds at hc
  rcases Bool.and_eq_true_iff.mp hc with ⟨hc1, hc2⟩
  have h1 : 0 ≤ zCosPolyScale θn (2 * θd) - zCosErrScale θn := of_decide_eq_true hc1
  have hhalf : (((θn : ℚ) / (θd : ℚ)) / 2) = (θn : ℚ) / ((2 * θd : ℕ) : ℚ) := by
    push_cast; ring
  have h2θd : 2 * θd ≠ 0 := by omega
  have hθd0 : θd ≠ 0 := by omega
  have hpos : 0 ≤ qCosPoly (((θn : ℚ) / (θd : ℚ)) / 2) -
      qCosErr (((θn : ℚ) / (θd : ℚ)) / 2) := by
    rw [hhalf, ← zCosPolyScale_div h2θd, ← zCosErrScale_div h2θd, ← sub_div]
    refine div_nonneg ?_ (by positivity)
    exact_mod_cast h1
  refine ⟨hpos, ?_⟩
  unfold qCosUpper
  have hiff : ((θn : ℚ) / (θd : ℚ) ≤ 7 / 10) ↔ 10 * θn ≤ 7 * (θd : ℤ) := by
    have hθdQ : (0 : ℚ) < θd := Nat.cast_pos.mpr hθd
    rw [div_le_div_iff₀ hθdQ (by norm_num)]
    constructor
    · intro h
      have h' : (10 : ℚ) * θn ≤ 7 * θd := by linarith
      exact_mod_cast h'
    · intro h
      have h' : (10 : ℚ) * θn ≤ 7 * θd := by exact_mod_cast h
      linarith
  by_cases h7 : 10 * θn ≤ 7 * (θd : ℤ)
  · rw [ite_eq_left (hiff.mpr h7)]
    rw [ite_eq_left h7] at hc2
    have hle : (zCosPolyScale θn θd + zCosErrScale θn) * (rd : ℤ) ≤
        rn * (36288000 * (θd : ℤ) ^ 10) := of_decide_eq_true hc2
    rw [← zCosPolyScale_div hθd0, ← zCosErrScale_div hθd0, ← add_div,
      div_le_div_iff₀ (by positivity) (Nat.cast_pos.mpr hrd)]
    exact_mod_cast hle
  · rw [ite_eq_right (mt hiff.mp h7)]
    rw [ite_eq_right h7] at hc2
    have hle : (2 * (zCosPolyScale θn (2 * θd) + zCosErrScale θn) ^ 2 -
        (36288000 * (2 * (θd : ℤ)) ^ 10) ^ 2) * (rd : ℤ) ≤
        rn * (36288000 * (2 * (θd : ℤ)) ^ 10) ^ 2 := of_decide_eq_true hc2
    rw [hhalf, ← zCosPolyScale_div h2θd, ← zCosErrScale_div h2θd, ← add_div]
    set S : ℚ := 36288000 * ((2 * θd : ℕ) : ℚ) ^ 10
    have hS0 : 0 < S := by positivity
    have hrew : 2 * (((zCosPolyScale θn (2 * θd) : ℚ) + zCosErrScale θn) / S) ^ 2 - 1 =
        (2 * ((zCosPolyScale θn (2 * θd) : ℚ) + zCosErrScale θn) ^ 2 - S ^ 2) / S ^ 2 := by
      field_simp [hS0.ne']
    rw [hrew, div_le_div_iff₀ (sq_pos_of_pos hS0) (Nat.cast_pos.mpr hrd)]
    dsimp only [S]
    push_cast at hle ⊢
    exact_mod_cast hle

private theorem cosBounds_of_check_le (θn : ℤ) (θd : ℕ) (rn : ℤ) (rd : ℕ) {θ ρ_lo : ℚ}
    (hθ : θ = (θn : ℚ) / (θd : ℚ) := by norm_num) (hθd : 0 < θd := by decide)
    (hrd : 0 < rd := by decide) (hc : checkCosBounds θn θd rn rd = true := by decide)
    (hρ : (rn : ℚ) / (rd : ℚ) ≤ ρ_lo := by norm_num) :
    0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2) ∧ qCosUpper θ ≤ ρ_lo := by
  subst hθ
  obtain ⟨h1, h2⟩ := cosBounds_of_check hθd hrd hc
  exact ⟨h1, h2.trans hρ⟩

private def zToQ (s : ℚ) (p : List ℤ) : List ℚ :=
  p.map fun c : ℤ => (c : ℚ) * s

private def zPolyAdd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: zPolyAdd p q

private def zPolyScale (c : ℤ) : List ℤ → List ℤ :=
  List.map (c * ·)

private def zPolyMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | c :: cs, q => zPolyAdd (zPolyScale c q) (0 :: zPolyMul cs q)

private def zPolyPow (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => zPolyMul p (zPolyPow p n)

private theorem zToQ_zPolyAdd (s : ℚ) (p q : List ℤ) :
    zToQ s (zPolyAdd p q) = qPolyAdd (zToQ s p) (zToQ s q) := by
  induction p generalizing q with
  | nil => simp [zToQ, zPolyAdd, qPolyAdd]
  | cons a p ih =>
    cases q with
    | nil => simp [zToQ, zPolyAdd, qPolyAdd]
    | cons b q =>
      rw [zPolyAdd, zToQ, List.map_cons, ← zToQ, ih]
      simp [zToQ, qPolyAdd, add_mul]

private theorem zToQ_zPolyMul (s t : ℚ) (p q : List ℤ) :
    zToQ (s * t) (zPolyMul p q) = qPolyMul (zToQ s p) (zToQ t q) := by
  induction p with
  | nil => simp [zToQ, zPolyMul, qPolyMul]
  | cons c cs ih =>
    have hsc : zToQ (s * t) (zPolyScale c q) = qPolyScale ((c : ℚ) * s) (zToQ t q) := by
      simp only [zToQ, zPolyScale, qPolyScale, List.map_map, Function.comp_def, Int.cast_mul]
      congr 1; ext x; ring
    have hcons : zToQ (s * t) (0 :: zPolyMul cs q) = 0 :: zToQ (s * t) (zPolyMul cs q) := by
      simp [zToQ]
    rw [zPolyMul, zToQ_zPolyAdd, hsc, hcons, ih]
    rfl

private theorem zToQ_zPolyPow (s : ℚ) (p : List ℤ) (n : ℕ) :
    zToQ (s ^ n) (zPolyPow p n) = qPolyPow (zToQ s p) n := by
  induction n with
  | zero => simp [zToQ, zPolyPow, qPolyPow]
  | succ n ih => rw [pow_succ', zPolyPow, qPolyPow, ← ih, zToQ_zPolyMul]

private def oddProd : ℕ → ℕ
  | 0 => 1
  | n + 1 => oddProd n * (2 * n + 1)

private theorem oddProd_pos (n : ℕ) : 0 < oddProd n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos ih (by omega)

private def oddSkip (j : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => if n = j then oddSkip j n else oddSkip j n * (2 * n + 1)

private theorem oddSkip_eq_oddProd {j n : ℕ} (h : n ≤ j) : oddSkip j n = oddProd n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [oddSkip, oddProd, show n ≠ j by omega, ↓reduceIte, ih (by omega)]

private theorem mul_oddSkip_eq_oddProd {j n : ℕ} (h : j < n) :
    (2 * j + 1) * oddSkip j n = oddProd n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [oddSkip, oddProd]
    by_cases hnj : n = j
    · subst hnj
      rw [ite_eq_left rfl, oddSkip_eq_oddProd le_rfl, mul_comm]
    · rw [ite_eq_right hnj, ← mul_assoc, ih (by omega)]

private def zExpOddPoly (m : ℕ) (an : ℤ) (ad : ℕ) : List ℤ :=
  let M := 2 * m + 1
  (List.range (M + 1)).map fun j =>
    (-an) ^ j * ((ad ^ (M - j) * (j + 1).ascFactorial (M - j) : ℕ) : ℤ)

private theorem zToQ_zExpOddPoly (m : ℕ) (an : ℤ) {ad : ℕ} (had : ad ≠ 0) :
    zToQ (1 / ((ad ^ (2 * m + 1) * (2 * m + 1).factorial : ℕ) : ℚ)) (zExpOddPoly m an ad) =
      qExpOddPoly m ((an : ℚ) / (ad : ℚ)) := by
  unfold zToQ zExpOddPoly qExpOddPoly
  dsimp only
  rw [List.map_map]
  set M := 2 * m + 1
  rw [show 2 * m + 2 = M + 1 by omega]
  refine List.map_congr_left fun j hj => ?_
  simp only [Function.comp_apply]
  have hjM : j ≤ M := Nat.lt_succ_iff.mp (List.mem_range.mp hj)
  have hfact :
      (M.factorial : ℚ) = (j.factorial : ℚ) * ((j + 1).ascFactorial (M - j) : ℚ) := by
    exact_mod_cast (Nat.add_sub_of_le hjM ▸ (j.factorial_mul_ascFactorial (M - j)).symm)
  have hpow : (ad : ℚ) ^ M = (ad : ℚ) ^ j * (ad : ℚ) ^ (M - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjM]
  have hadQ : (ad : ℚ) ^ j ≠ 0 := pow_ne_zero j (Nat.cast_ne_zero.mpr had)
  have hadM : (ad : ℚ) ^ (M - j) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr had)
  have hjf : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hrf : ((j + 1).ascFactorial (M - j) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (j.ascFactorial_pos (M - j)).ne'
  rw [← neg_div, div_pow]
  push_cast
  rw [hfact, hpow]
  field_simp [hadQ, hadM, hjf, hrf]

private def zInnerPoly (m : ℕ) (gn : ℤ) (gd : ℕ) : List ℤ :=
  let M := 2 * m + 1
  let ad := 2 * gd ^ 2
  (List.range (M + 1)).map fun j =>
    gn * (-gn ^ 2) ^ j *
      ((ad ^ (M - j) * (j + 1).ascFactorial (M - j) * oddSkip j (M + 1) : ℕ) : ℤ)

private theorem zToQ_zInnerPoly (m : ℕ) (gn : ℤ) {gd : ℕ} (hgd : gd ≠ 0) :
    zToQ (1 / ((gd * (2 * gd ^ 2) ^ (2 * m + 1) * (2 * m + 1).factorial *
        oddProd (2 * m + 2) : ℕ) : ℚ)) (zInnerPoly m gn gd) =
      qInnerPoly m ((gn : ℚ) / (gd : ℚ)) := by
  unfold zToQ zInnerPoly qInnerPoly
  dsimp only
  rw [List.map_map]
  set M := 2 * m + 1
  set ad := 2 * gd ^ 2
  rw [show 2 * m + 2 = M + 1 by omega]
  refine List.map_congr_left fun j hj => ?_
  simp only [Function.comp_apply]
  have hj_lt : j < M + 1 := List.mem_range.mp hj
  have hjM : j ≤ M := Nat.lt_succ_iff.mp hj_lt
  have hfact :
      (M.factorial : ℚ) = (j.factorial : ℚ) * ((j + 1).ascFactorial (M - j) : ℚ) := by
    exact_mod_cast (Nat.add_sub_of_le hjM ▸ (j.factorial_mul_ascFactorial (M - j)).symm)
  have hodd : (oddProd (M + 1) : ℚ) = ((2 * j + 1 : ℕ) : ℚ) * (oddSkip j (M + 1) : ℚ) := by
    exact_mod_cast (mul_oddSkip_eq_oddProd hj_lt).symm
  have hpow : (ad : ℚ) ^ M = (ad : ℚ) ^ j * (ad : ℚ) ^ (M - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjM]
  have hgdQ : (gd : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hgd
  have had_ne : (ad : ℚ) ≠ 0 := by dsimp only [ad]; positivity
  have hadj : (ad : ℚ) ^ j ≠ 0 := pow_ne_zero j had_ne
  have hadM : (ad : ℚ) ^ (M - j) ≠ 0 := pow_ne_zero _ had_ne
  have hjf : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hrf : ((j + 1).ascFactorial (M - j) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (j.ascFactorial_pos (M - j)).ne'
  have h2j1 : (2 * (j : ℚ) + 1) ≠ 0 := by positivity
  have hos : (oddSkip j (M + 1) : ℚ) ≠ 0 := by
    intro h0
    have hposQ : (0 : ℚ) < oddProd (M + 1) := Nat.cast_pos.mpr (oddProd_pos (M + 1))
    rw [hodd, h0, mul_zero] at hposQ
    exact lt_irrefl 0 hposQ
  have hrew : -(((gn : ℚ) / (gd : ℚ)) ^ 2 / 2) = (-(gn : ℚ) ^ 2) / (ad : ℚ) := by
    dsimp only [ad]; push_cast; field_simp [hgdQ]
  rw [hrew, div_pow]
  push_cast
  rw [hfact, hodd, hpow]
  push_cast
  field_simp [hgdQ, hadj, hadM, hjf, hrf, h2j1, hos]

private def zEvalHom : List ℤ → ℤ → ℕ → ℤ × ℕ
  | [], _, _ => (0, 1)
  | c :: cs, un, ud =>
    let r := zEvalHom cs un ud
    (c * (ud : ℤ) * (r.2 : ℤ) + un * r.1, ud * r.2)

private theorem zEvalHom_spec (s : ℚ) (p : List ℤ) (un : ℤ) {ud : ℕ} (hud : ud ≠ 0) :
    (zEvalHom p un ud).2 ≠ 0 ∧
      qEval (zToQ s p) ((un : ℚ) / (ud : ℚ)) =
        s * ((zEvalHom p un ud).1 : ℚ) / ((zEvalHom p un ud).2 : ℚ) := by
  induction p with
  | nil => simp [zEvalHom, zToQ, qEval]
  | cons c cs ih =>
    obtain ⟨hr0, hreq⟩ := ih
    have hd2 : ud * (zEvalHom cs un ud).2 ≠ 0 := Nat.mul_ne_zero hud hr0
    refine ⟨hd2, ?_⟩
    rw [zToQ, List.map_cons, ← zToQ, qEval, hreq, zEvalHom]
    have hudQ : (ud : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hud
    have hrQ : ((zEvalHom cs un ud).2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
    push_cast
    field_simp [hudQ, hrQ]

private theorem qEval_qExpOddPoly_nonneg {m : ℕ} (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) {a B : ℚ}
    (ha : a = (an : ℚ) / (ad : ℚ) := by norm_num)
    (hB : B = (bn : ℚ) / (bd : ℚ) := by norm_num)
    (had : 0 < ad := by decide) (hbd : 0 < bd := by decide)
    (hc : decide (0 ≤ (zEvalHom (zExpOddPoly m an ad) (bn ^ 2) (bd ^ 2)).1) = true := by decide) :
    0 ≤ qEval (qExpOddPoly m a) (B ^ 2) := by
  subst ha hB
  set D : ℕ := ad ^ (2 * m + 1) * (2 * m + 1).factorial
  have hD : 0 < D := Nat.mul_pos (pow_pos had _) (2 * m + 1).factorial_pos
  have hbd2 : bd ^ 2 ≠ 0 := pow_ne_zero 2 hbd.ne'
  obtain ⟨he0, hev⟩ := zEvalHom_spec (1 / (D : ℚ)) (zExpOddPoly m an ad) (bn ^ 2) hbd2
  have hB2 : (((bn : ℚ) / (bd : ℚ)) ^ 2) = ((bn ^ 2 : ℤ) : ℚ) / ((bd ^ 2 : ℕ) : ℚ) := by
    push_cast; rw [div_pow]
  rw [← zToQ_zExpOddPoly m an had.ne', hB2, hev]
  have h1 : (0 : ℚ) ≤ (zEvalHom (zExpOddPoly m an ad) (bn ^ 2) (bd ^ 2)).1 := by
    exact_mod_cast of_decide_eq_true hc
  have h2 : 0 < ((zEvalHom (zExpOddPoly m an ad) (bn ^ 2) (bd ^ 2)).2 : ℚ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero he0)
  positivity

private def fracAdd (a b : ℤ × ℕ) : ℤ × ℕ :=
  (a.1 * (b.2 : ℤ) + b.1 * (a.2 : ℤ), a.2 * b.2)

private def fracVal (x : ℤ × ℕ) : ℚ :=
  (x.1 : ℚ) / (x.2 : ℚ)

private theorem fracAdd_spec {a b : ℤ × ℕ} (ha : a.2 ≠ 0) (hb : b.2 ≠ 0) :
    (fracAdd a b).2 ≠ 0 ∧ fracVal (fracAdd a b) = fracVal a + fracVal b := by
  refine ⟨Nat.mul_ne_zero ha hb, ?_⟩
  simp only [fracVal, fracAdd]
  have haQ : (a.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hbQ : (b.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  push_cast
  field_simp [haQ, hbQ]

private def pairStep : List (ℤ × ℕ) → List (ℤ × ℕ)
  | [] => []
  | [x] => [x]
  | x :: y :: xs => fracAdd x y :: pairStep xs

private theorem pairStep_spec :
    ∀ {xs : List (ℤ × ℕ)}, (∀ x ∈ xs, x.2 ≠ 0) →
      (∀ y ∈ pairStep xs, y.2 ≠ 0) ∧ ((pairStep xs).map fracVal).sum = (xs.map fracVal).sum
  | [] => fun _ => And.intro (fun _ h => nomatch h) rfl
  | [_] => fun h => And.intro h rfl
  | x :: y :: xs => fun h => by
    have hx := h x List.mem_cons_self
    have hy := h y (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨hxy0, hxyv⟩ := fracAdd_spec hx hy
    obtain ⟨hrest0, hrestv⟩ := pairStep_spec (fun z hz =>
      h z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)))
    refine ⟨fun z hz => ?_, ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz'
      · exact hxy0
      · exact hrest0 z hz'
    · simp only [pairStep, List.map_cons, List.sum_cons, hxyv, hrestv, add_assoc]

private theorem foldl_fracAdd_spec (xs : List (ℤ × ℕ)) :
    ∀ {acc : ℤ × ℕ}, acc.2 ≠ 0 → (∀ x ∈ xs, x.2 ≠ 0) →
      (xs.foldl fracAdd acc).2 ≠ 0 ∧
        fracVal (xs.foldl fracAdd acc) = fracVal acc + (xs.map fracVal).sum := by
  induction xs with
  | nil => intro acc hacc _; simp [hacc]
  | cons x xs ih =>
    intro acc hacc hxs
    obtain ⟨hax0, haxv⟩ := fracAdd_spec hacc (hxs x List.mem_cons_self)
    obtain ⟨h0, hv⟩ := ih hax0 (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    exact ⟨h0, by simp only [List.foldl_cons, List.map_cons, List.sum_cons, hv, haxv, add_assoc]⟩

private def treeFold : ℕ → List (ℤ × ℕ) → ℤ × ℕ
  | _, [] => (0, 1)
  | _, [x] => x
  | 0, x :: xs => xs.foldl fracAdd x
  | fuel + 1, xs => treeFold fuel (pairStep xs)

private theorem treeFold_spec (fuel : ℕ) :
    ∀ {xs : List (ℤ × ℕ)}, (∀ x ∈ xs, x.2 ≠ 0) →
      (treeFold fuel xs).2 ≠ 0 ∧ fracVal (treeFold fuel xs) = (xs.map fracVal).sum := by
  induction fuel with
  | zero =>
    intro xs hxs
    cases xs with
    | nil => simp [treeFold, fracVal]
    | cons x xs =>
      cases xs with
      | nil => simp [treeFold, hxs x List.mem_cons_self]
      | cons y ys =>
        simpa only [treeFold, List.map_cons, List.sum_cons] using
          foldl_fracAdd_spec (y :: ys) (hxs x List.mem_cons_self)
            (fun z hz => hxs z (List.mem_cons_of_mem _ hz))
  | succ fuel ih =>
    intro xs hxs
    cases xs with
    | nil => simp [treeFold, fracVal]
    | cons x xs =>
      cases xs with
      | nil => simp [treeFold, hxs x List.mem_cons_self]
      | cons y ys =>
        obtain ⟨hp0, hpv⟩ := pairStep_spec hxs
        obtain ⟨h0, hv⟩ := ih hp0
        exact ⟨h0, hv.trans hpv⟩

private def zIntOddTerms (bn : ℤ) (bd : ℕ) : List ℤ → ℕ → List (ℤ × ℕ)
  | [], _ => []
  | c :: cs, d =>
    (c * bn ^ (d + 1) * ((bd ^ (2 * cs.length + 1) : ℕ) : ℤ), d + 1) ::
      zIntOddTerms bn bd cs (d + 2)

private theorem zIntOddTerms_spec (s : ℚ) (bn : ℤ) {bd : ℕ} (hbd : bd ≠ 0) (p : List ℤ) :
    ∀ (d : ℕ), (∀ x ∈ zIntOddTerms bn bd p d, x.2 ≠ 0) ∧
      qIntOdd (zToQ s p) d ((bn : ℚ) / (bd : ℚ)) =
        s * (((zIntOddTerms bn bd p d).map fracVal).sum / (bd : ℚ) ^ (d + 2 * p.length)) := by
  induction p with
  | nil => intro d; simp [zIntOddTerms, zToQ, qIntOdd]
  | cons c cs ih =>
    intro d
    obtain ⟨h0, hv⟩ := ih (d + 2)
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.succ_ne_zero d
      · exact h0 x hx'
    · rw [zToQ, List.map_cons, ← zToQ, qIntOdd, hv]
      simp only [zIntOddTerms, List.map_cons, List.sum_cons, fracVal, List.length_cons]
      have hexp : d + 2 + 2 * cs.length = d + 2 * (cs.length + 1) := by omega
      rw [hexp]
      have hpow : (bd : ℚ) ^ (d + 2 * (cs.length + 1)) =
          (bd : ℚ) ^ (d + 1) * (bd : ℚ) ^ (2 * cs.length + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hbdQ : (bd : ℚ) ^ (d + 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hbd)
      have hbdM : (bd : ℚ) ^ (2 * cs.length + 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hbd)
      have hd1 : ((d : ℚ) + 1) ≠ 0 := by positivity
      rw [div_pow]
      push_cast
      rw [hpow]
      field_simp [hbdQ, hbdM, hd1]

private def checkMomentLower (lo_n : ℤ) (lo_d : ℕ)
    (d m_in m_out S_out : ℕ) (gn : ℤ) (gd : ℕ) (bn : ℤ) (bd : ℕ) (sn : ℤ) (sd : ℕ) : Bool :=
  let M_out := 2 * m_out + 1
  let ad_out := 2 * S_out
  let D_out : ℕ := ad_out ^ M_out * M_out.factorial
  let s_out_d : ℕ := D_out ^ S_out
  let M_in := 2 * m_in + 1
  let s_in_d : ℕ := gd * (2 * gd ^ 2) ^ M_in * M_in.factorial * oddProd (M_in + 1)
  let p_out := zPolyPow (zExpOddPoly m_out 1 ad_out) S_out
  let q_in := zInnerPoly m_in gn gd
  let prod_p := zPolyMul p_out (zPolyPow q_in d)
  let main_t := treeFold 10 (zIntOddTerms bn bd prod_p d)
  let main_num : ℤ := main_t.1 * (sd : ℤ) ^ (d + 1)
  let main_den : ℤ := (s_out_d : ℤ) * (s_in_d : ℤ) ^ d * (main_t.2 : ℤ) *
    (bd : ℤ) ^ (d + 2 * prod_p.length) * sn ^ (d + 1)
  let q_ev := zEvalHom q_in (bn ^ 2) (bd ^ 2)
  let p_ev := zEvalHom (zExpOddPoly m_out 1 ad_out) (bn ^ 2) (bd ^ 2)
  let tail_num : ℤ := (bn * q_ev.1) ^ d * (sd : ℤ) ^ (d + 1) * (bn * (bd : ℤ)) * p_ev.1 ^ S_out
  let tail_den : ℤ := ((bd : ℤ) * (s_in_d : ℤ) * (q_ev.2 : ℤ)) ^ d * sn ^ (d + 1) *
    (bn ^ 2 + (bd : ℤ) ^ 2) * (s_out_d : ℤ) * (p_ev.2 : ℤ) ^ S_out
  let rhs_num : ℤ := 2 * (main_num * tail_den + tail_num * main_den)
  let rhs_den : ℤ := main_den * tail_den
  decide (lo_n * rhs_den ≤ rhs_num * (lo_d : ℤ))

private theorem le_qMomentLower_of_check (lo_n : ℤ) (lo_d : ℕ) (gn : ℤ) (gd : ℕ)
    (bn : ℤ) (bd : ℕ) {d m_in m_out S_out : ℕ} {lo γ_lo B : ℚ}
    (hlo : lo = (lo_n : ℚ) / (lo_d : ℚ) := by norm_num)
    (hγ : γ_lo = (gn : ℚ) / (gd : ℚ) := by norm_num)
    (hB : B = (bn : ℚ) / (bd : ℚ) := by norm_num)
    (hlo_d : 0 < lo_d := by decide) (hS : 1 ≤ S_out := by decide)
    (hgd : 0 < gd := by decide) (hbd : 0 < bd := by decide)
    (hc : checkMomentLower lo_n lo_d d m_in m_out S_out gn gd bn bd 25066282747 (10 ^ 10) =
      true := by decide) :
    lo ≤ qMomentLower d m_in m_out S_out γ_lo B sqrtTwoPiHi := by
  subst hlo hγ hB
  set sn : ℤ := 25066282747
  set sd : ℕ := 10 ^ 10
  have hsn : 0 < sn := by decide
  have hsd : 0 < sd := by decide
  have hsqrt : sqrtTwoPiHi = (sn : ℚ) / (sd : ℚ) := by norm_num [sqrtTwoPiHi, sn, sd]
  rw [hsqrt]
  have hle : _ := of_decide_eq_true hc
  set M_out := 2 * m_out + 1
  set ad_out := 2 * S_out
  set D_out : ℕ := ad_out ^ M_out * M_out.factorial
  set s_out_d : ℕ := D_out ^ S_out
  set M_in := 2 * m_in + 1
  set s_in_d : ℕ := gd * (2 * gd ^ 2) ^ M_in * M_in.factorial * oddProd (M_in + 1)
  set p_out := zPolyPow (zExpOddPoly m_out 1 ad_out) S_out
  set q_in := zInnerPoly m_in gn gd
  set prod_p := zPolyMul p_out (zPolyPow q_in d)
  set main_t := treeFold 10 (zIntOddTerms bn bd prod_p d)
  set q_ev := zEvalHom q_in (bn ^ 2) (bd ^ 2)
  set p_ev := zEvalHom (zExpOddPoly m_out 1 ad_out) (bn ^ 2) (bd ^ 2)
  have had_out : ad_out ≠ 0 := by dsimp only [ad_out]; omega
  have hD_out_pos : 0 < D_out := Nat.mul_pos (pow_pos (by omega) _) M_out.factorial_pos
  have hs_out_pos : 0 < s_out_d := pow_pos hD_out_pos _
  have hs_in_pos : 0 < s_in_d := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hgd
    (pow_pos (by positivity) _)) M_in.factorial_pos) (oddProd_pos _)
  have hp_exp : qExpOddPoly m_out (1 / (2 * (S_out : ℚ))) =
      zToQ (1 / (D_out : ℚ)) (zExpOddPoly m_out 1 ad_out) := by
    have h1 : (1 : ℚ) / (2 * (S_out : ℚ)) = ((1 : ℤ) : ℚ) / (ad_out : ℚ) := by
      dsimp only [ad_out]; push_cast; rfl
    rw [h1, ← zToQ_zExpOddPoly m_out 1 had_out]
  have hp_out_eq : qPolyPow (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) S_out =
      zToQ (1 / (s_out_d : ℚ)) p_out := by
    rw [hp_exp, ← zToQ_zPolyPow, one_div_pow]
    dsimp only [s_out_d, p_out]; push_cast; rfl
  have hq_in_eq : qInnerPoly m_in ((gn : ℚ) / (gd : ℚ)) = zToQ (1 / (s_in_d : ℚ)) q_in := by
    simpa only [s_in_d, q_in, M_in] using (zToQ_zInnerPoly m_in gn hgd.ne').symm
  have hprod_eq : qPolyMul (qPolyPow (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) S_out)
      (qPolyPow (qInnerPoly m_in ((gn : ℚ) / (gd : ℚ))) d) =
      zToQ ((1 / (s_out_d : ℚ)) * (1 / (s_in_d : ℚ)) ^ d) prod_p := by
    rw [hp_out_eq, hq_in_eq, ← zToQ_zPolyPow, ← zToQ_zPolyMul]
  obtain ⟨ht0, htv⟩ := zIntOddTerms_spec ((1 / (s_out_d : ℚ)) * (1 / (s_in_d : ℚ)) ^ d)
    bn hbd.ne' prod_p d
  obtain ⟨hmt0, hmtv⟩ := treeFold_spec 10 ht0
  have hbd2 : bd ^ 2 ≠ 0 := pow_ne_zero 2 hbd.ne'
  obtain ⟨hqe0, hqev⟩ := zEvalHom_spec (1 / (s_in_d : ℚ)) q_in (bn ^ 2) hbd2
  obtain ⟨hpe0, hpev⟩ := zEvalHom_spec (1 / (D_out : ℚ)) (zExpOddPoly m_out 1 ad_out) (bn ^ 2) hbd2
  have hB2 : (((bn : ℚ) / (bd : ℚ)) ^ 2) = ((bn ^ 2 : ℤ) : ℚ) / ((bd ^ 2 : ℕ) : ℚ) := by
    push_cast; rw [div_pow]
  unfold qMomentLower
  dsimp only
  rw [hprod_eq, htv, ← hmtv, hB2, hq_in_eq, hqev, hp_exp, hpev]
  set main_num : ℤ := main_t.1 * (sd : ℤ) ^ (d + 1)
  set main_den : ℤ := (s_out_d : ℤ) * (s_in_d : ℤ) ^ d * (main_t.2 : ℤ) *
    (bd : ℤ) ^ (d + 2 * prod_p.length) * sn ^ (d + 1)
  set tail_num : ℤ := (bn * q_ev.1) ^ d * (sd : ℤ) ^ (d + 1) * (bn * (bd : ℤ)) * p_ev.1 ^ S_out
  set tail_den : ℤ := ((bd : ℤ) * (s_in_d : ℤ) * (q_ev.2 : ℤ)) ^ d * sn ^ (d + 1) *
    (bn ^ 2 + (bd : ℤ) ^ 2) * (s_out_d : ℤ) * (p_ev.2 : ℤ) ^ S_out
  have hmain_den_pos : (0 : ℚ) < main_den := by
    dsimp only [main_den]
    have : 0 < main_t.2 := Nat.pos_of_ne_zero hmt0
    push_cast; positivity
  have htail_den_pos : (0 : ℚ) < tail_den := by
    dsimp only [tail_den]
    have : 0 < q_ev.2 := Nat.pos_of_ne_zero hqe0
    have : 0 < p_ev.2 := Nat.pos_of_ne_zero hpe0
    have hbb : (0 : ℚ) < (bn : ℚ) ^ 2 + (bd : ℚ) ^ 2 := by positivity
    push_cast; positivity
  have hrhs_eq :
      2 * ((1 / (s_out_d : ℚ) * (1 / (s_in_d : ℚ)) ^ d *
          (fracVal main_t / (bd : ℚ) ^ (d + 2 * prod_p.length))) / ((sn : ℚ) / (sd : ℚ)) ^ (d + 1) +
        (((bn : ℚ) / (bd : ℚ) * (1 / (s_in_d : ℚ) * (q_ev.1 : ℚ) / (q_ev.2 : ℚ))) ^ d /
          ((sn : ℚ) / (sd : ℚ)) ^ d) *
          (((bn : ℚ) / (bd : ℚ) / (((bn : ℤ) ^ 2 : ℤ) / ((bd ^ 2 : ℕ) : ℚ) + 1)) *
            ((1 / (D_out : ℚ) * (p_ev.1 : ℚ) / (p_ev.2 : ℚ)) ^ S_out /
              ((sn : ℚ) / (sd : ℚ))))) =
        ((2 * (main_num * tail_den + tail_num * main_den) : ℤ) : ℚ) /
          ((main_den : ℚ) * (tail_den : ℚ)) := by
    simp only [fracVal, main_num, main_den, tail_num, tail_den, s_out_d, div_pow, mul_pow]
    have h1 : (D_out : ℚ) ^ S_out ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hD_out_pos.ne')
    have h2 : (s_in_d : ℚ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hs_in_pos.ne')
    have h3 : (main_t.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hmt0
    have h4 : (bd : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hbd.ne'
    have h4d : (bd : ℚ) ^ d ≠ 0 := pow_ne_zero _ h4
    have h4p : (bd : ℚ) ^ (d + 2 * prod_p.length) ≠ 0 := pow_ne_zero _ h4
    have h5 : (sn : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hsn.ne'
    have h5d : (sn : ℚ) ^ d ≠ 0 := pow_ne_zero _ h5
    have h5d1 : (sn : ℚ) ^ (d + 1) ≠ 0 := pow_ne_zero _ h5
    have h6 : (sd : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsd.ne'
    have h6d : (sd : ℚ) ^ d ≠ 0 := pow_ne_zero _ h6
    have h6d1 : (sd : ℚ) ^ (d + 1) ≠ 0 := pow_ne_zero _ h6
    have h7 : (q_ev.2 : ℚ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hqe0)
    have h8 : (p_ev.2 : ℚ) ^ S_out ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hpe0)
    have h9 : (bn : ℚ) ^ 2 + (bd : ℚ) ^ 2 ≠ 0 := (by positivity : (0 : ℚ) < _).ne'
    push_cast
    field_simp [h1, h2, h3, h4, h4d, h4p, h5, h5d, h5d1, h6, h6d, h6d1, h7, h8, h9]
    ring
  rw [hrhs_eq, div_le_div_iff₀ (Nat.cast_pos.mpr hlo_d) (mul_pos hmain_den_pos htail_den_pos)]
  exact_mod_cast hle

/-! ### Algebraic bridges for `HyperEdgeBound` constructors -/

private theorem cast_mul_pred_eq {r k : ℕ} (hk : 1 ≤ k) :
    (r : ℝ) * ((k : ℝ) - 1) = ((r * (k - 1) : ℕ) : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_one]

private theorem rat_cast_linear_le {k : ℕ} {q a b : ℚ} (hp : q ≤ a * (k : ℕ) + b) :
    (q : ℝ) ≤ (a : ℝ) * (k : ℕ) + (b : ℝ) := by
  have hR : (q : ℝ) ≤ ((a * (k : ℕ) + b : ℚ) : ℝ) := Rat.cast_le.mpr hp
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] using hR

private theorem twoStepCorr_eq {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) :
    twoStepCorr r k = 2 * √((r * (k - 1) : ℕ) : ℝ) / (((r * (k - 1) : ℕ) : ℝ) + 1) := by
  set m : ℕ := r * (k - 1)
  have hm_eq : (r : ℝ) * ((k : ℝ) - 1) = (m : ℝ) := cast_mul_pred_eq (by omega)
  have hm_pos : 0 < (m : ℝ) := by
    dsimp only [m]
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hsq_ne : √(m : ℝ) ≠ 0 := (sqrt_pos.mpr hm_pos).ne'
  unfold twoStepCorr
  rw [hm_eq]
  field_simp [hsq_ne]
  rw [sq_sqrt hm_pos.le]

private theorem le_twoStepCorr_and_lt_one {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) {s_lo : ℚ}
    (hs0 : 0 ≤ s_lo) (hsq : s_lo ^ 2 ≤ ((r * (k - 1) : ℕ) : ℚ)) :
    ((2 * s_lo / ((r * (k - 1) : ℕ) + 1) : ℚ) : ℝ) ≤ twoStepCorr r k ∧
      twoStepCorr r k < 1 := by
  rw [twoStepCorr_eq hr hk]
  set m : ℕ := r * (k - 1)
  have hm2 : 2 ≤ m :=
    le_trans (by decide : 2 ≤ 2 * 1) (Nat.mul_le_mul hr (by omega))
  have hs_le : (s_lo : ℝ) ≤ √(m : ℝ) := by
    rw [← sq_le_sq₀ (Rat.cast_nonneg.mpr hs0) (sqrt_nonneg _), sq_sqrt (Nat.cast_nonneg m)]
    exact_mod_cast hsq
  refine ⟨?_, ?_⟩
  · push_cast
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · rw [div_lt_one (by positivity)]
    have hmR : (2 : ℝ) ≤ m := Nat.ofNat_le_cast.mpr hm2
    have h1 : 1 < √(m : ℝ) := (lt_sqrt zero_le_one).mpr (by linarith)
    nlinarith [sq_pos_of_pos (sub_pos.mpr h1), sq_sqrt (Nat.cast_nonneg (α := ℝ) m)]

private theorem coneMeanSq_and_coneCorr_eq {r k : ℕ} (hr : 2 ≤ r) (hk : 3 ≤ k) :
    coneMeanSq r k = (((r + 1 : ℚ) / (r * k) : ℚ) : ℝ) ∧
      coneCorr r k =
        (2 * √((r * (k - 1) : ℕ) : ℝ) + ((k : ℝ) - 2)) /
          (((r * (k - 1) : ℕ) : ℝ) + (k : ℝ) - 1) := by
  set m : ℕ := r * (k - 1)
  have hm_eq : (r : ℝ) * ((k : ℝ) - 1) = (m : ℝ) := cast_mul_pred_eq (by omega)
  have hm_pos : 0 < (m : ℝ) := by
    dsimp only [m]
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hsq_ne : √(m : ℝ) ≠ 0 := (sqrt_pos.mpr hm_pos).ne'
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk1_ne : ((k : ℝ) - 1) ≠ 0 := by
    have : (3 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
    linarith
  refine ⟨?_, ?_⟩
  · unfold coneMeanSq
    rw [hm_eq, div_pow, one_pow, sq_sqrt hm_pos.le, ← hm_eq]
    push_cast
    field_simp [hr_ne, hk_ne, hk1_ne]
  · unfold coneCorr
    dsimp only
    rw [hm_eq]
    field_simp [hsq_ne]
    rw [sq_sqrt hm_pos.le]
    ring

private theorem mul_arccos_le_of_qCosUpper {k : ℕ} {θ ρ_lo a b : ℚ} {ρ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hcos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2) ∧ qCosUpper θ ≤ ρ_lo)
    (hρ_m1 : -1 ≤ ρ_lo) (hρ_lo : (ρ_lo : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hp : (k : ℚ) / 2 * (θ / piLo) ≤ a * (k : ℕ) + b) :
    (k : ℝ) / (2 * π) * arccos ρ ≤ (a : ℝ) * (k : ℕ) + (b : ℝ) := by
  have harc := arccos_div_pi_le_of_qCosUpper hθ0 hθ2 hcos.1 hcos.2 hρ_m1 hρ_lo hρ1
  calc (k : ℝ) / (2 * π) * arccos ρ
      = ((k : ℝ) / 2) * (arccos ρ / π) := by ring
    _ ≤ ((k : ℝ) / 2) * ((θ / piLo : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left harc (by positivity)
    _ = (((k : ℚ) / 2 * (θ / piLo) : ℚ) : ℝ) := by
        push_cast
        ring
    _ ≤ (a : ℝ) * (k : ℕ) + (b : ℝ) := rat_cast_linear_le hp

private theorem hyperEdgeBound_pairwise_three_two {a b : ℚ} (hp : 1 / 6 ≤ a * (2 : ℕ) + b) :
    HyperEdgeBound 3 2 ((a : ℝ) * (2 : ℕ) + (b : ℝ)) := by
  refine HyperEdgeBound.pairwise ?_
  have hcorr : twoStepCorr 3 2 = cos (π / 6) := by
    rw [twoStepCorr_eq (by decide) (by decide), cos_pi_div_six]
    norm_num
    ring
  rw [hcorr, arccos_cos (by positivity) (by linarith [pi_pos])]
  have hsimp : ((2 : ℕ) : ℝ) / (2 * π) * (π / 6) = ((1 / 6 : ℚ) : ℝ) := by
    have hpi : π ≠ 0 := pi_ne_zero
    push_cast
    field_simp [hpi]
  rw [hsimp]
  exact rat_cast_linear_le hp

private theorem hyperEdgeBound_pairwise_of_rat {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {s_lo θ a b : ℚ} (hs0 : 0 ≤ s_lo) (hsq : s_lo ^ 2 ≤ ((r * (k - 1) : ℕ) : ℚ))
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hcos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2) ∧
      qCosUpper θ ≤ 2 * s_lo / ((r * (k - 1) : ℕ) + 1))
    (hp : (k : ℚ) / 2 * (θ / piLo) ≤ a * (k : ℕ) + b) :
    HyperEdgeBound r k ((a : ℝ) * (k : ℕ) + (b : ℝ)) := by
  obtain ⟨hρ_lo, hρ_lt⟩ := le_twoStepCorr_and_lt_one hr hk hs0 hsq
  have hρ_m1 : (-1 : ℚ) ≤ 2 * s_lo / ((r * (k - 1) : ℕ) + 1) :=
    le_trans (b := 0) (by norm_num) (by positivity)
  exact HyperEdgeBound.pairwise
    (mul_arccos_le_of_qCosUpper hθ0 hθ2 hcos hρ_m1 hρ_lo hρ_lt.le hp)

private theorem hyperEdgeBound_starCone_of_rat {r k : ℕ} (hr : 2 ≤ r) (hk : 3 ≤ k)
    {s_lo s_hi θ a b : ℚ} (hs0 : 0 ≤ s_lo) (hsq_lo : s_lo ^ 2 ≤ ((r * (k - 1) : ℕ) : ℚ))
    (hshi0 : 0 < s_hi) (hsq_hi : ((r * (k - 1) : ℕ) : ℚ) ≤ s_hi ^ 2)
    (hcone_lo : 1 < ((r + 1 : ℚ) / (r * k)) ^ 2 * ((r * (k - 1) : ℕ) : ℚ))
    (hcone_hi : max 0 (((r + 1 : ℚ) / (r * k)) * s_hi - 1) ^ 2 <
      4 * ((r + 1 : ℚ) / (r * k)))
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hcos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2) ∧
      qCosUpper θ ≤ (2 * s_lo + ((k : ℚ) - 2)) / (((r * (k - 1) : ℕ) : ℚ) + k - 1))
    (hp : (k : ℚ) / 2 * (θ / piLo) ≤ a * (k : ℕ) + b) :
    HyperEdgeBound r k ((a : ℝ) * (k : ℕ) + (b : ℝ)) := by
  obtain ⟨hQ_eq, hC_eq⟩ := coneMeanSq_and_coneCorr_eq hr hk
  set m : ℕ := r * (k - 1)
  have hm_eq : (r : ℝ) * ((k : ℝ) - 1) = (m : ℝ) := cast_mul_pred_eq (by omega)
  have hm2 : 2 ≤ m :=
    le_trans (by decide : 2 ≤ 2 * 1) (Nat.mul_le_mul hr (by omega))
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  set Q₀ : ℚ := (r + 1 : ℚ) / (r * k)
  have hQ₀_pos : 0 < Q₀ := by
    dsimp only [Q₀]
    positivity
  refine HyperEdgeBound.starCone hk ?_ ?_ ?_
  · rw [hm_eq, hQ_eq]
    have h1 : 1 < (Q₀ : ℝ) ^ 2 * (m : ℝ) := by exact_mod_cast hcone_lo
    have hsq_pos : 0 < √(m : ℝ) := sqrt_pos.mpr hm_pos
    rw [div_lt_iff₀ hsq_pos]
    have h2 : 1 ^ 2 < ((Q₀ : ℝ) * √(m : ℝ)) ^ 2 := by
      rw [mul_pow, sq_sqrt hm_pos.le]
      linarith [h1]
    nlinarith [mul_pos (Rat.cast_pos.mpr hQ₀_pos) hsq_pos]
  · rw [hm_eq, hQ_eq]
    have hsm_le : √(m : ℝ) ≤ (s_hi : ℝ) := by
      rw [← sq_le_sq₀ (sqrt_nonneg _) (Rat.cast_nonneg.mpr hshi0.le), sq_sqrt hm_pos.le]
      exact_mod_cast hsq_hi
    have hq_ge : 1 / (s_hi : ℝ) ≤ 1 / √(m : ℝ) :=
      one_div_le_one_div_of_le (sqrt_pos.mpr hm_pos) hsm_le
    have hstep : (Q₀ : ℝ) - 1 / (s_hi : ℝ) < 2 * (1 / (s_hi : ℝ)) * √(Q₀ : ℝ) := by
      have hshiR : 0 < (s_hi : ℝ) := Rat.cast_pos.mpr hshi0
      have hmul_lt : (Q₀ : ℝ) * (s_hi : ℝ) - 1 < 2 * √(Q₀ : ℝ) := by
        by_cases hneg : (Q₀ : ℝ) * (s_hi : ℝ) - 1 ≤ 0
        · exact hneg.trans_lt (mul_pos two_pos (sqrt_pos.mpr (Rat.cast_pos.mpr hQ₀_pos)))
        · push Not at hneg
          have hsq : ((Q₀ : ℝ) * (s_hi : ℝ) - 1) ^ 2 < (2 * √(Q₀ : ℝ)) ^ 2 := by
            rw [mul_pow, sq_sqrt (Rat.cast_nonneg.mpr hQ₀_pos.le)]
            have hq : (Q₀ * s_hi - 1) ^ 2 < 4 * Q₀ := by
              have hmax : Q₀ * s_hi - 1 ≤ max 0 (Q₀ * s_hi - 1) := le_max_right _ _
              have h0 : 0 < Q₀ * s_hi - 1 := by exact_mod_cast hneg
              exact (pow_le_pow_left₀ h0.le hmax 2).trans_lt hcone_hi
            exact_mod_cast hq
          nlinarith [sqrt_nonneg (Q₀ : ℝ)]
      have hdiv := div_lt_div_of_pos_right hmul_lt hshiR
      have hlhs : ((Q₀ : ℝ) * (s_hi : ℝ) - 1) / (s_hi : ℝ) = (Q₀ : ℝ) - 1 / (s_hi : ℝ) := by
        field_simp [hshiR.ne']
      have hrhs : 2 * √(Q₀ : ℝ) / (s_hi : ℝ) = 2 * (1 / (s_hi : ℝ)) * √(Q₀ : ℝ) := by ring
      linarith
    have hsqrt_nn : 0 ≤ √(Q₀ : ℝ) := sqrt_nonneg _
    linarith [mul_le_mul_of_nonneg_right hq_ge hsqrt_nn]
  · have hs_le : (s_lo : ℝ) ≤ √(m : ℝ) := by
      rw [← sq_le_sq₀ (Rat.cast_nonneg.mpr hs0) (sqrt_nonneg _), sq_sqrt hm_pos.le]
      exact_mod_cast hsq_lo
    have hρ_lo : (((2 * s_lo + ((k : ℚ) - 2)) / ((m : ℚ) + k - 1) : ℚ) : ℝ) ≤ coneCorr r k := by
      rw [hC_eq]
      push_cast
      exact div_le_div_of_nonneg_right (by linarith) (by
        have : (3 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
        linarith)
    have hρ_le1 : coneCorr r k ≤ 1 := by
      rw [hC_eq, div_le_one (by
        have : (3 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
        linarith)]
      nlinarith [sq_nonneg (√(m : ℝ) - 1), sq_sqrt hm_pos.le]
    have hρ_m1 : (-1 : ℚ) ≤ (2 * s_lo + ((k : ℚ) - 2)) / ((m : ℚ) + k - 1) := by
      have : (3 : ℚ) ≤ k := Nat.ofNat_le_cast.mpr hk
      have : (0 : ℚ) ≤ m := Nat.cast_nonneg m
      exact le_trans (by norm_num) (div_nonneg (by linarith) (by linarith))
    exact mul_arccos_le_of_qCosUpper hθ0 hθ2 hcos hρ_m1 hρ_lo hρ_le1 hp

private theorem hyperEdgeBound_cap_of_rat {r k : ℕ} (hr : 2 ≤ r) (hk : 3 ≤ k)
    {s_hi θ a b : ℚ} (hshi1 : 1 ≤ s_hi) (hsq_hi : ((r * (k - 1) : ℕ) : ℚ) ≤ s_hi ^ 2)
    (hcap_gt : 1 / 2 < 4 * s_hi / (s_hi + 1) ^ 2)
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hcos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2) ∧
      qCosUpper θ ≤ ((k : ℚ) * (4 * s_hi / (s_hi + 1) ^ 2) - 1) / ((k : ℚ) - 1))
    (hp : (k : ℚ) / 2 * (θ / piLo) ≤ a * (k : ℕ) + b) :
    HyperEdgeBound r k ((a : ℝ) * (k : ℕ) + (b : ℝ)) := by
  set m : ℕ := r * (k - 1)
  have hm_eq : (r : ℝ) * ((k : ℝ) - 1) = (m : ℝ) := cast_mul_pred_eq (by omega)
  have hm2 : 2 ≤ m :=
    le_trans (by decide : 2 ≤ 2 * 1) (Nat.mul_le_mul hr (by omega))
  have hm1 : (1 : ℝ) ≤ √(m : ℝ) :=
    (le_sqrt zero_le_one (Nat.cast_nonneg m)).mpr (by
      have : (2 : ℝ) ≤ m := Nat.ofNat_le_cast.mpr hm2
      linarith)
  have hshiR1 : 1 ≤ (s_hi : ℝ) := by exact_mod_cast hshi1
  have hsm_le : √(m : ℝ) ≤ (s_hi : ℝ) := by
    rw [← sq_le_sq₀ (sqrt_nonneg _) (by linarith), sq_sqrt (Nat.cast_nonneg m)]
    exact_mod_cast hsq_hi
  have hcap_ge : ((4 * s_hi / (s_hi + 1) ^ 2 : ℚ) : ℝ) ≤ capSq r k := by
    unfold capSq
    rw [hm_eq]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hid : 4 * √(m : ℝ) * ((s_hi : ℝ) + 1) ^ 2 - 4 * (s_hi : ℝ) * (√(m : ℝ) + 1) ^ 2 =
        4 * ((s_hi : ℝ) - √(m : ℝ)) * (√(m : ℝ) * (s_hi : ℝ) - 1) := by ring
    have hprod : 0 ≤ ((s_hi : ℝ) - √(m : ℝ)) * (√(m : ℝ) * (s_hi : ℝ) - 1) :=
      mul_nonneg (sub_nonneg.mpr hsm_le) (by nlinarith)
    linarith
  have hcap_le1 : capSq r k ≤ 1 := by
    unfold capSq
    rw [hm_eq, div_le_one (by positivity)]
    nlinarith [sq_nonneg (√(m : ℝ) - 1)]
  have hcap_half : 1 / 2 < capSq r k := by
    have h12 : (1 / 2 : ℝ) < ((4 * s_hi / (s_hi + 1) ^ 2 : ℚ) : ℝ) := by
      have hq : ((1 / 2 : ℚ) : ℝ) < ((4 * s_hi / (s_hi + 1) ^ 2 : ℚ) : ℝ) :=
        Rat.cast_lt.mpr hcap_gt
      norm_num at hq ⊢
      exact hq
    exact h12.trans_le hcap_ge
  refine HyperEdgeBound.cap hcap_half ?_
  have hk3R : (3 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
  have hρ_lo : ((((k : ℚ) * (4 * s_hi / (s_hi + 1) ^ 2) - 1) / ((k : ℚ) - 1) : ℚ) : ℝ) ≤
      capCorr r k := by
    unfold capCorr
    push_cast at hcap_ge ⊢
    exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)
  have hρ_le1 : capCorr r k ≤ 1 := by
    unfold capCorr
    rw [div_le_one (by linarith)]
    nlinarith
  have hρ_m1 : (-1 : ℚ) ≤ ((k : ℚ) * (4 * s_hi / (s_hi + 1) ^ 2) - 1) / ((k : ℚ) - 1) := by
    have hk3Q : (3 : ℚ) ≤ k := Nat.ofNat_le_cast.mpr hk
    exact le_trans (by norm_num) (div_nonneg (by nlinarith) (by linarith))
  exact mul_arccos_le_of_qCosUpper hθ0 hθ2 hcos hρ_m1 hρ_lo hρ_le1 hp

private theorem hyperEdgeBound_slepian_three_of_rat {r : ℕ} (hr : 2 ≤ r)
    {s_lo θ a b : ℚ} (hs0 : 0 ≤ s_lo) (hsq : s_lo ^ 2 ≤ ((r * 2 : ℕ) : ℚ))
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hcos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2) ∧
      qCosUpper θ ≤ 2 * s_lo / ((r * 2 : ℕ) + 1))
    (hp : 3 / 2 * (θ / piLo) ≤ a * (3 : ℕ) + b) :
    HyperEdgeBound r 3 ((a : ℝ) * (3 : ℕ) + (b : ℝ)) := by
  obtain ⟨hρ_lo, hρ_lt⟩ := le_twoStepCorr_and_lt_one hr (k := 3) (by decide) hs0 hsq
  have hρ0 : 0 ≤ twoStepCorr r 3 :=
    le_trans (by positivity) hρ_lo
  have hρ_m1 : (-1 : ℚ) ≤ 2 * s_lo / ((r * 2 : ℕ) + 1) :=
    le_trans (b := 0) (by norm_num) (by positivity)
  refine HyperEdgeBound.slepian ?_
  rw [equicorrStraddle_three hρ0 hρ_lt]
  simpa only [Nat.cast_ofNat] using
    mul_arccos_le_of_qCosUpper (k := 3) hθ0 hθ2 hcos hρ_m1 hρ_lo hρ_lt.le
      (by simpa only [Nat.cast_ofNat] using hp)

private theorem hyperEdgeBound_slepian_of_rat {r k m_in m_out S_out : ℕ}
    (hr : 2 ≤ r) (hk4 : 4 ≤ k) (hk7 : k ≤ 7) (hS : 1 ≤ S_out)
    {s_lo θ γ_lo B I4_lo I6_lo a b : ℚ}
    (hs0 : 0 < s_lo) (hsq : s_lo ^ 2 ≤ ((r * (k - 1) : ℕ) : ℚ))
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hcos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2) ∧
      qCosUpper θ ≤ 2 * s_lo / ((r * (k - 1) : ℕ) + 1))
    (hγ0 : 0 ≤ γ_lo)
    (hγ : γ_lo ^ 2 * (1 - 2 * s_lo / ((r * (k - 1) : ℕ) + 1)) ≤
      2 * s_lo / ((r * (k - 1) : ℕ) + 1))
    (hB : 0 < B)
    (hin_pos : 0 ≤ qEval (qExpOddPoly m_in (γ_lo ^ 2 / 2)) (B ^ 2))
    (hout_pos : 0 ≤ qEval (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) (B ^ 2))
    (hI4 : I4_lo ≤ qMomentLower 4 m_in m_out S_out γ_lo B sqrtTwoPiHi)
    (hI6 : 6 ≤ k → I6_lo ≤ qMomentLower 6 m_in m_out S_out γ_lo B sqrtTwoPiHi)
    (hp : 1 - (1 / 2 ^ (k - 1) +
      2 * (k.choose 2 : ℚ) / 2 ^ (k - 2) * (1 / 4 - (θ / piLo) / 2) +
      2 * (k.choose 4 : ℚ) / 2 ^ (k - 4) * I4_lo +
      (if 6 ≤ k then 2 * (k.choose 6 : ℚ) / 2 ^ (k - 6) * I6_lo else 0)) ≤
        a * (k : ℕ) + b) :
    HyperEdgeBound r k ((a : ℝ) * (k : ℕ) + (b : ℝ)) := by
  have hk2 : 2 ≤ k := by omega
  obtain ⟨hρ_lo, hρ_lt⟩ := le_twoStepCorr_and_lt_one hr hk2 hs0.le hsq
  set ρ_lo_q : ℚ := 2 * s_lo / ((r * (k - 1) : ℕ) + 1)
  have hρ_lo_pos : 0 < (ρ_lo_q : ℝ) := by
    dsimp only [ρ_lo_q]
    have : 0 < (s_lo : ℝ) := Rat.cast_pos.mpr hs0
    push_cast
    positivity
  have hρ_pos : 0 < twoStepCorr r k := hρ_lo_pos.trans_le hρ_lo
  have hρ_m1 : (-1 : ℚ) ≤ ρ_lo_q := le_trans (by norm_num) (Rat.cast_nonneg.mp hρ_lo_pos.le)
  have harc := arccos_div_pi_le_of_qCosUpper hθ0 hθ2 hcos.1 hcos.2 hρ_m1 hρ_lo hρ_lt.le
  have hγR : (γ_lo : ℝ) ^ 2 * (1 - twoStepCorr r k) ≤ twoStepCorr r k := by
    have hγ_q : (γ_lo : ℝ) ^ 2 * (1 - (ρ_lo_q : ℝ)) ≤ (ρ_lo_q : ℝ) := by exact_mod_cast hγ
    have hsq_nn : 0 ≤ (γ_lo : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hsl := equicorrStraddle_le_of_poly hk4 hk7 hS hρ_pos hρ_lt harc hγ0 hγR hB
    (by norm_num [sqrtTwoPiHi]) two_mul_pi_le_sq_sqrtTwoPiHi hin_pos hout_pos
  have hcert_le :
      qEquicorrUpperCert k m_in m_out S_out (θ / piLo) γ_lo B sqrtTwoPiHi ≤ a * (k : ℕ) + b := by
    unfold qEquicorrUpperCert
    dsimp only
    have hc4 : 0 ≤ 2 * (k.choose 4 : ℚ) / 2 ^ (k - 4) := by positivity
    have hm4 := mul_le_mul_of_nonneg_left hI4 hc4
    by_cases hk6 : 6 ≤ k
    · simp only [hk6, ↓reduceIte] at hp ⊢
      have hc6 : 0 ≤ 2 * (k.choose 6 : ℚ) / 2 ^ (k - 6) := by positivity
      have hm6 := mul_le_mul_of_nonneg_left (hI6 hk6) hc6
      linarith
    · simp only [hk6, ↓reduceIte] at hp ⊢
      linarith
  exact HyperEdgeBound.slepian (hsl.trans (rat_cast_linear_le hcert_le))

/-! ### The six verified `HyperDualCert` theorems -/

private theorem hedge_six {r : ℕ} {a b : ℚ}
    (h2 : HyperEdgeBound r 2 ((a : ℝ) * (2 : ℕ) + (b : ℝ)))
    (h3 : HyperEdgeBound r 3 ((a : ℝ) * (3 : ℕ) + (b : ℝ)))
    (h4 : HyperEdgeBound r 4 ((a : ℝ) * (4 : ℕ) + (b : ℝ)))
    (h5 : HyperEdgeBound r 5 ((a : ℝ) * (5 : ℕ) + (b : ℝ)))
    (h6 : HyperEdgeBound r 6 ((a : ℝ) * (6 : ℕ) + (b : ℝ))) :
    ∀ k ∈ Finset.Icc 2 6, HyperEdgeBound r k ((a : ℝ) * (k : ℕ) + (b : ℝ)) := by
  intro k hk
  rcases Finset.mem_Icc.mp hk with ⟨hk2, hkK⟩
  interval_cases k
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

private theorem edge_starCone_r3_k3 {a b : ℚ}
    (hp : (3 : ℚ) / 2 * ((9270307 / 12500000) / piLo) ≤ a * (3 : ℕ) + b) :
    HyperEdgeBound 3 3 ((a : ℝ) * (3 : ℕ) + (b : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := (122474487139 / 50000000000)) (s_hi := (244948974279 / 100000000000))
    (θ := (9270307 / 12500000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 9270307 12500000 147474487139 200000000000)
    hp

private theorem edge_sheppard_r3_k2 :
    HyperEdgeBound 3 2
      (((18389141 / 100000000 : ℚ) : ℝ) * (2 : ℕ) + ((-19757453 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_three_two (by norm_num)

private theorem edge_sheppard_r3_k3 :
    HyperEdgeBound 3 3
      (((18389141 / 100000000 : ℚ) : ℝ) * (3 : ℕ) + ((-19757453 / 100000000 : ℚ) : ℝ)) :=
  edge_starCone_r3_k3 (by norm_num [piLo])

private theorem edge_sheppard_r3_k4 :
    HyperEdgeBound 3 4
      (((18389141 / 100000000 : ℚ) : ℝ) * (4 : ℕ) + ((-19757453 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_cap_of_rat (by decide) (by decide)
    (s_hi := 3) (θ := (21026727 / 25000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 21026727 25000000 2 3)
    (by norm_num [piLo])

private theorem edge_sheppard_r3_k5 :
    HyperEdgeBound 3 5
      (((18389141 / 100000000 : ℚ) : ℝ) * (5 : ℕ) + ((-19757453 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_cap_of_rat (by decide) (by decide)
    (s_hi := (173205080757 / 50000000000)) (θ := (18062853 / 20000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 18062853 20000000 123384572681261108306951 199282032302955566772196)
    (by norm_num [piLo])

private theorem edge_sheppard_r3_k6 :
    HyperEdgeBound 3 6
      (((18389141 / 100000000 : ℚ) : ℝ) * (6 : ℕ) + ((-19757453 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_cap_of_rat (by decide) (by decide)
    (s_hi := (387298334621 / 100000000000)) (θ := (47426207 / 50000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 47426207 50000000 230685445388666637595453 395766111540666812022735)
    (by norm_num [piLo])

/-- Verified dual-LP certificate at `r = 3` (`K₀ = 6`). -/
theorem cert_r3_sheppard :
    HyperDualCert 3 6 (18389141 / 100000000 : ℚ) (-19757453 / 100000000 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := hedge_six edge_sheppard_r3_k2 edge_sheppard_r3_k3 edge_sheppard_r3_k4
    edge_sheppard_r3_k5 edge_sheppard_r3_k6

private theorem edge_slepian_r3_k2 :
    HyperEdgeBound 3 2
      (((17970677 / 100000000 : ℚ) : ℝ) * (2 : ℕ) + ((-18502061 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_three_two (by norm_num)

private theorem edge_slepian_r3_k3 :
    HyperEdgeBound 3 3
      (((17970677 / 100000000 : ℚ) : ℝ) * (3 : ℕ) + ((-18502061 / 100000000 : ℚ) : ℝ)) :=
  edge_starCone_r3_k3 (by norm_num [piLo])

private theorem mom4_slepian_r3_k4 :
    ((42647757861 / 2500000000000) : ℚ) ≤
      qMomentLower 4 4 2 2 (61237 / 50000) 2 sqrtTwoPiHi :=
  le_qMomentLower_of_check 42647757861 2500000000000 61237 50000 2 1

private theorem edge_slepian_r3_k4 :
    HyperEdgeBound 3 4
      (((17970677 / 100000000 : ℚ) : ℝ) * (4 : ℕ) + ((-18502061 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 4) (m_out := 2) (S_out := 2)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := 3) (θ := (46364781 / 50000000))
    (γ_lo := (61237 / 50000)) (B := 2)
    (I4_lo := (42647757861 / 2500000000000)) (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 46364781 50000000 3 5)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 3749970169 5000000000 2 1)
    (qEval_qExpOddPoly_nonneg 1 4 2 1)
    mom4_slepian_r3_k4
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r3_k5 :
    ((12611397757 / 10000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (106819 / 100000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 12611397757 10000000000000 106819 100000 3 5

private theorem edge_slepian_r3_k5 :
    HyperEdgeBound 3 5
      (((17970677 / 100000000 : ℚ) : ℝ) * (5 : ℕ) + ((-18502061 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (346410161513 / 100000000000)) (θ := (100872693 / 100000000))
    (γ_lo := (106819 / 100000)) (B := (3 / 5))
    (I4_lo := (12611397757 / 10000000000000)) (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 100872693 100000000 26646935501 50000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 11410298761 20000000000 3 5)
    (qEval_qExpOddPoly_nonneg 1 2 3 5)
    mom4_slepian_r3_k5
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r3_k6 :
    ((8905614613 / 10000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (96873 / 100000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 8905614613 10000000000000 96873 100000 3 5

private theorem mom6_slepian_r3_k6 :
    ((400160759 / 10000000000000) : ℚ) ≤
      qMomentLower 6 1 1 1 (96873 / 100000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 400160759 10000000000000 96873 100000 3 5

private theorem edge_slepian_r3_k6 :
    HyperEdgeBound 3 6
      (((17970677 / 100000000 : ℚ) : ℝ) * (6 : ℕ) + ((-18502061 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (19364916731 / 5000000000)) (θ := (53271811 / 50000000))
    (γ_lo := (96873 / 100000)) (B := (3 / 5))
    (I4_lo := (8905614613 / 10000000000000)) (I6_lo := (400160759 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 53271811 50000000 19364916731 40000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 9384378129 20000000000 3 5)
    (qEval_qExpOddPoly_nonneg 1 2 3 5)
    mom4_slepian_r3_k6
    (fun _ => mom6_slepian_r3_k6)
    (by norm_num [Nat.choose, piLo])

/-- Verified dual-LP certificate at `r = 3` (`K₀ = 6`). -/
theorem cert_r3_slepian :
    HyperDualCert 3 6 (17970677 / 100000000 : ℚ) (-18502061 / 100000000 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := hedge_six edge_slepian_r3_k2 edge_slepian_r3_k3 edge_slepian_r3_k4
    edge_slepian_r3_k5 edge_slepian_r3_k6

private theorem edge_sheppard_r4_k2 :
    HyperEdgeBound 4 2
      (((19737623 / 100000000 : ℚ) : ℝ) * (2 : ℕ) + ((-18991953 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_of_rat (by decide) (by decide)
    (s_lo := 2) (θ := (64350151 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 64350151 100000000 4 5)
    (by norm_num [piLo])

private theorem edge_sheppard_r4_k3 :
    HyperEdgeBound 4 3
      (((19737623 / 100000000 : ℚ) : ℝ) * (3 : ℕ) + ((-18991953 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := (141421356237 / 50000000000)) (s_hi := (11313708499 / 4000000000))
    (θ := (42119239 / 50000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 42119239 50000000 166421356237 250000000000)
    (by norm_num [piLo])

private theorem edge_sheppard_r4_k4 :
    HyperEdgeBound 4 4
      (((19737623 / 100000000 : ℚ) : ℝ) * (4 : ℕ) + ((-18991953 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := (346410161513 / 100000000000)) (s_hi := (173205080757 / 50000000000))
    (θ := (11665817 / 12500000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 11665817 12500000 148803387171 250000000000)
    (by norm_num [piLo])

private theorem edge_sheppard_r4_k5 :
    HyperEdgeBound 4 5
      (((19737623 / 100000000 : ℚ) : ℝ) * (5 : ℕ) + ((-18991953 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_cap_of_rat (by decide) (by decide)
    (s_hi := 4) (θ := (98843249 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 98843249 100000000 11 20)
    (by norm_num [piLo])

private theorem edge_sheppard_r4_k6 :
    HyperEdgeBound 4 6
      (((19737623 / 100000000 : ℚ) : ℝ) * (6 : ℕ) + ((-18991953 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_cap_of_rat (by decide) (by decide)
    (s_hi := (894427191 / 200000000)) (θ := (102760211 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 102760211 100000000 3095479640399849519 5988854382000752405)
    (by norm_num [piLo])

/-- Verified dual-LP certificate at `r = 4` (`K₀ = 6`). -/
theorem cert_r4_sheppard :
    HyperDualCert 4 6 (19737623 / 100000000 : ℚ) (-18991953 / 100000000 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := hedge_six edge_sheppard_r4_k2 edge_sheppard_r4_k3 edge_sheppard_r4_k4
    edge_sheppard_r4_k5 edge_sheppard_r4_k6

private theorem edge_slepian_r8_k2 :
    HyperEdgeBound 8 2
      (((666667 / 4000000 : ℚ) : ℝ) * (2 : ℕ) + ((0 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_of_rat (by decide) (by decide)
    (s_lo := (141421356237 / 50000000000)) (θ := (89112291 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 89112291 100000000 47140452079 75000000000)
    (by norm_num [piLo])

private theorem edge_slepian_r8_k3 :
    HyperEdgeBound 8 3
      (((666667 / 4000000 : ℚ) : ℝ) * (3 : ℕ) + ((0 : ℚ) : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := 4) (s_hi := 4)
    (θ := (26179949 / 25000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 26179949 25000000 1 2)
    (by norm_num [piLo])

private theorem mom4_slepian_r8_k4 :
    ((40268530757 / 5000000000000) : ℚ) ≤
      qMomentLower 4 3 3 2 (80281 / 100000) (5 / 2) sqrtTwoPiHi :=
  le_qMomentLower_of_check 40268530757 5000000000000 80281 100000 5 2

private theorem edge_slepian_r8_k4 :
    HyperEdgeBound 8 4
      (((666667 / 4000000 : ℚ) : ℝ) * (4 : ℕ) + ((0 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 3) (m_out := 3) (S_out := 2)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (122474487139 / 25000000000)) (θ := (116808089 / 100000000))
    (γ_lo := (80281 / 100000)) (B := (5 / 2))
    (I4_lo := (40268530757 / 5000000000000)) (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 116808089 100000000 122474487139 312500000000)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 6445038961 20000000000 5 2)
    (qEval_qExpOddPoly_nonneg 1 4 5 2)
    mom4_slepian_r8_k4
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r8_k5 :
    ((3011188201 / 10000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (18057 / 25000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 3011188201 10000000000000 18057 25000 3 5

private theorem edge_slepian_r8_k5 :
    HyperEdgeBound 8 5
      (((666667 / 4000000 : ℚ) : ℝ) * (5 : ℕ) + ((0 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (565685424949 / 100000000000)) (θ := (15260733 / 12500000))
    (γ_lo := (18057 / 25000)) (B := (3 / 5))
    (I4_lo := (3011188201 / 10000000000000)) (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 15260733 12500000 565685424949 1650000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 326055249 1250000000 3 5)
    (qEval_qExpOddPoly_nonneg 1 2 3 5)
    mom4_slepian_r8_k5
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r8_k6 :
    ((2239046637 / 10000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (13359 / 20000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 2239046637 10000000000000 13359 20000 3 5

private theorem mom6_slepian_r8_k6 :
    ((50687217 / 10000000000000) : ℚ) ≤
      qMomentLower 6 1 1 1 (13359 / 20000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 50687217 10000000000000 13359 20000 3 5

private theorem edge_slepian_r8_k6 :
    HyperEdgeBound 8 6
      (((666667 / 4000000 : ℚ) : ℝ) * (6 : ℕ) + ((0 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (632455532033 / 100000000000)) (θ := (15714567 / 12500000))
    (γ_lo := (13359 / 20000)) (B := (3 / 5))
    (I4_lo := (2239046637 / 10000000000000)) (I6_lo := (50687217 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 15714567 12500000 632455532033 2050000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 178462881 800000000 3 5)
    (qEval_qExpOddPoly_nonneg 1 2 3 5)
    mom4_slepian_r8_k6
    (fun _ => mom6_slepian_r8_k6)
    (by norm_num [Nat.choose, piLo])

/-- Verified dual-LP certificate at `r = 8` (`K₀ = 6`). -/
theorem cert_r8_slepian :
    HyperDualCert 8 6 (666667 / 4000000 : ℚ) (0 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := hedge_six edge_slepian_r8_k2 edge_slepian_r8_k3 edge_slepian_r8_k4
    edge_slepian_r8_k5 edge_slepian_r8_k6

private theorem edge_slepian_r16_k2 :
    HyperEdgeBound 16 2
      (((4588373 / 50000000 : ℚ) : ℝ) * (2 : ℕ) + ((18096309 / 50000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_of_rat (by decide) (by decide)
    (s_lo := 4) (θ := (108083941 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 108083941 100000000 8 17)
    (by norm_num [piLo])

private theorem edge_slepian_r16_k3 :
    HyperEdgeBound 16 3
      (((4588373 / 50000000 : ℚ) : ℝ) * (3 : ℕ) + ((18096309 / 50000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := (565685424949 / 100000000000)) (s_hi := (11313708499 / 2000000000))
    (θ := (12002041 / 10000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 12002041 10000000 615685424949 1700000000000)
    (by norm_num [piLo])

private theorem mom4_slepian_r16_k4 :
    ((22793381879 / 5000000000000) : ℚ) ≤
      qMomentLower 4 4 3 5 (1480 / 2357) (39 / 10) sqrtTwoPiHi :=
  le_qMomentLower_of_check 22793381879 5000000000000 1480 2357 39 10

private theorem edge_slepian_r16_k4 :
    HyperEdgeBound 16 4
      (((4588373 / 50000000 : ℚ) : ℝ) * (4 : ℕ) + ((18096309 / 50000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 4) (m_out := 3) (S_out := 5)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (692820323027 / 100000000000)) (θ := (128410129 / 100000000))
    (γ_lo := (1480 / 2357)) (B := (39 / 10))
    (I4_lo := (22793381879 / 5000000000000)) (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 128410129 100000000 98974331861 350000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 1095200 5555449 39 10)
    (qEval_qExpOddPoly_nonneg 1 10 39 10)
    mom4_slepian_r16_k4
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r16_k5 :
    ((35556367833 / 10000000000000) : ℚ) ≤
      qMomentLower 4 4 3 6 (4 / 7) (21 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 35556367833 10000000000000 4 7 21 5

private theorem edge_slepian_r16_k5 :
    HyperEdgeBound 16 5
      (((4588373 / 50000000 : ℚ) : ℝ) * (5 : ℕ) + ((18096309 / 50000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 4) (m_out := 3) (S_out := 6)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := 8) (θ := (33052161 / 25000000))
    (γ_lo := (4 / 7)) (B := (21 / 5))
    (I4_lo := (35556367833 / 10000000000000)) (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 33052161 25000000 16 65)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 8 49 21 5)
    (qEval_qExpOddPoly_nonneg 1 12 21 5)
    mom4_slepian_r16_k5
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r16_k6 :
    ((468300427 / 5000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (53239 / 100000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 468300427 5000000000000 53239 100000 3 5

private theorem mom6_slepian_r16_k6 :
    ((6867393 / 5000000000000) : ℚ) ≤
      qMomentLower 6 1 1 1 (53239 / 100000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 6867393 5000000000000 53239 100000 3 5

private theorem edge_slepian_r16_k6 :
    HyperEdgeBound 16 6
      (((4588373 / 50000000 : ℚ) : ℝ) * (6 : ℕ) + ((18096309 / 50000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (894427190999 / 100000000000)) (θ := (13481147 / 10000000))
    (γ_lo := (53239 / 100000)) (B := (3 / 5))
    (I4_lo := (468300427 / 5000000000000)) (I6_lo := (6867393 / 5000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 13481147 10000000 894427190999 4050000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 2834391121 20000000000 3 5)
    (qEval_qExpOddPoly_nonneg 1 2 3 5)
    mom4_slepian_r16_k6
    (fun _ => mom6_slepian_r16_k6)
    (by norm_num [Nat.choose, piLo])

/-- Verified dual-LP certificate at `r = 16` (`K₀ = 6`). -/
theorem cert_r16_slepian :
    HyperDualCert 16 6 (4588373 / 50000000 : ℚ) (18096309 / 50000000 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := hedge_six edge_slepian_r16_k2 edge_slepian_r16_k3 edge_slepian_r16_k4
    edge_slepian_r16_k5 edge_slepian_r16_k6

private theorem edge_slepian_r64_k2 :
    HyperEdgeBound 64 2
      (((2318347 / 50000000 : ℚ) : ℝ) * (2 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_of_rat (by decide) (by decide)
    (s_lo := 8) (θ := (66104337 / 50000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 66104337 50000000 16 65)
    (by norm_num [piLo])

private theorem edge_slepian_r64_k3 :
    HyperEdgeBound 64 3
      (((2318347 / 50000000 : ℚ) : ℝ) * (3 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_three_of_rat (by decide)
    (s_lo := (565685424949 / 50000000000)) (θ := (5577913 / 4000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 5577913 4000000 565685424949 3225000000000)
    (by norm_num [piLo])

private theorem mom4_slepian_r64_k4 :
    ((67244281 / 2000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (20473 / 50000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 67244281 2000000000000 20473 50000 3 5

private theorem edge_slepian_r64_k4 :
    HyperEdgeBound 64 4
      (((2318347 / 50000000 : ℚ) : ℝ) * (4 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (277128129211 / 20000000000)) (θ := (142670897 / 100000000))
    (γ_lo := (20473 / 50000)) (B := (3 / 5))
    (I4_lo := (67244281 / 2000000000000)) (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 142670897 100000000 277128129211 1930000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 419143729 5000000000 3 5)
    (qEval_qExpOddPoly_nonneg 1 2 3 5)
    mom4_slepian_r64_k4
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r64_k5 :
    ((2035466543 / 2000000000000) : ℚ) ≤
      qMomentLower 4 2 3 7 (333 / 883) (47 / 10) sqrtTwoPiHi :=
  le_qMomentLower_of_check 2035466543 2000000000000 333 883 47 10

private theorem edge_slepian_r64_k5 :
    HyperEdgeBound 64 5
      (((2318347 / 50000000 : ℚ) : ℝ) * (5 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 2) (m_out := 3) (S_out := 7)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := 16) (θ := (144595881 / 100000000))
    (γ_lo := (333 / 883)) (B := (47 / 10))
    (I4_lo := (2035466543 / 2000000000000)) (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 144595881 100000000 32 257)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 110889 1559378 47 10)
    (qEval_qExpOddPoly_nonneg 1 14 47 10)
    mom4_slepian_r64_k5
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r64_k6 :
    ((4133382621 / 5000000000000) : ℚ) ≤
      qMomentLower 4 2 3 7 (17 / 48) (23 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 4133382621 5000000000000 17 48 23 5

private theorem mom6_slepian_r64_k6 :
    ((56834371 / 1000000000000) : ℚ) ≤
      qMomentLower 6 2 3 7 (17 / 48) (23 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 56834371 1000000000000 17 48 23 5

private theorem edge_slepian_r64_k6 :
    HyperEdgeBound 64 6
      (((2318347 / 50000000 : ℚ) : ℝ) * (6 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 2) (m_out := 3) (S_out := 7)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (1788854381999 / 100000000000)) (θ := (9119433 / 6250000))
    (γ_lo := (17 / 48)) (B := (23 / 5))
    (I4_lo := (4133382621 / 5000000000000)) (I6_lo := (56834371 / 1000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 9119433 6250000 1788854381999 16050000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 289 4608 23 5)
    (qEval_qExpOddPoly_nonneg 1 14 23 5)
    mom4_slepian_r64_k6
    (fun _ => mom6_slepian_r64_k6)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r64_k7 :
    ((155505707 / 10000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (6733 / 20000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 155505707 10000000000000 6733 20000 3 5

private theorem mom6_slepian_r64_k7 :
    ((930741 / 10000000000000) : ℚ) ≤
      qMomentLower 6 1 1 1 (6733 / 20000) (3 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_check 930741 10000000000000 6733 20000 3 5

private theorem edge_slepian_r64_k7 :
    HyperEdgeBound 64 7
      (((2318347 / 50000000 : ℚ) : ℝ) * (7 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (979795897113 / 50000000000)) (θ := (18360289 / 12500000))
    (γ_lo := (6733 / 20000)) (B := (3 / 5))
    (I4_lo := (155505707 / 10000000000000)) (I6_lo := (930741 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cosBounds_of_check_le 18360289 12500000 89072354283 875000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (qEval_qExpOddPoly_nonneg 45333289 800000000 3 5)
    (qEval_qExpOddPoly_nonneg 1 2 3 5)
    mom4_slepian_r64_k7
    (fun _ => mom6_slepian_r64_k7)
    (by norm_num [Nat.choose, piLo])

/-- Verified dual-LP certificate at `r = 64` (`K₀ = 7`). -/
theorem cert_r64_slepian :
    HyperDualCert 64 7 (2318347 / 50000000 : ℚ) (16272637 / 25000000 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk2, hkK⟩
    interval_cases k
    · exact edge_slepian_r64_k2
    · exact edge_slepian_r64_k3
    · exact edge_slepian_r64_k4
    · exact edge_slepian_r64_k5
    · exact edge_slepian_r64_k6
    · exact edge_slepian_r64_k7

end Cslib.Circuits.Frontier.Hypergraph
