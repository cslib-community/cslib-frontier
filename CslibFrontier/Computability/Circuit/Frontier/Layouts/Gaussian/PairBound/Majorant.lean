/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.Analytic
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertTop
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Soundness of the fixed-point certificate checker and `pairCost_zero_le`

This module proves that every interval combinator, domain-tightening step (`clampBox`), leaf
verifier (`chkSchur`, `chkGram`, `chkShep`, `chkPlanar`), and balanced-tree program step (`stepOne`,
`runProg`, `checkBox`) in `CertChecker.lean` is sound with respect to real arithmetic and Gaussian
measure on `E`. Combining soundness with `Cert.rootBoxI_certified` from `CertTop.lean` and the
dihedral `D_4` reduction `exists_admissiblePair_wlog` yields the unconditional matched-pair bound

`pairCost_zero_le : IsAdmissiblePair u → pairCost u 0 ≤ 27735 / 100000`.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.PairBound.pairCost_zero_le`:
  `IsAdmissiblePair u → pairCost u 0 ≤ 27735 / 100000`.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.pairCost_le`:
  `IsAdmissiblePair u → ∀ t, pairCost u t ≤ 27735 / 100000`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.Gaussian.PairBound

/-! ### Part 1: Fixed-point `10 ^ 8` interval semantics and combinator soundness -/

private noncomputable def valI (n : Int) : ℝ := (n : ℝ) / 100000000

private def MemI (x : ℝ) (v : Cert.Ival) : Prop :=
  valI v.lo ≤ x ∧ x ≤ valI v.hi

private theorem forceNat_eq {α : Type} (n : Nat) (k : Nat → α) :
    Cert.forceNat n k = k n := by
  cases n <;> rfl

private theorem bindInt_eq {α : Type} (x : Int) (k : Int → α) :
    Cert.bindInt x k = k x := by
  cases x with
  | ofNat n => cases n <;> rfl
  | negSucc n => cases n <;> rfl

private theorem bindIval_eq {α : Type} (v : Cert.Ival) (k : Cert.Ival → α) :
    Cert.bindIval v k = k v := by
  cases v
  simp only [Cert.bindIval, bindInt_eq]

private theorem bindBox_eq {α : Type} (b : Cert.BoxI) (k : Cert.BoxI → α) :
    Cert.bindBox b k = k b := by
  cases b
  simp only [Cert.bindBox, bindInt_eq]

private theorem evalBox_eq (b : Cert.BoxI) : Cert.evalBox b = some b := by
  simp only [Cert.evalBox, bindBox_eq]

private theorem if_true_eq {α : Type*} {c : Bool} (hc : c = true) (x y : α) :
    (if c = true then x else y) = x := by rw [hc]; rfl

private theorem if_false_eq {α : Type*} {c : Bool} (hc : c = false) (x y : α) :
    (if c = true then x else y) = y := by rw [hc]; rfl

private theorem ible_iff (a b : Int) : Cert.ible a b = true ↔ a ≤ b := by
  unfold Cert.ible
  change (Int.casesOn (b - a) (fun _ => true) (fun _ => false) = true) ↔ a ≤ b
  cases h : b - a with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast] at h
    simp only [true_iff]
    omega
  | negSucc n =>
    simp only [Bool.false_eq_true, false_iff]
    omega

private theorem ible_false_iff (a b : Int) : Cert.ible a b = false ↔ b < a := by
  rw [Bool.eq_false_iff, ne_eq, ible_iff]; omega

private theorem iblt_iff (a b : Int) : Cert.iblt a b = true ↔ a < b := by
  unfold Cert.iblt
  change (Int.casesOn (b - a) (fun n => Nat.casesOn n false (fun _ => true))
    (fun _ => false) = true) ↔ a < b
  cases h : b - a with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast] at h
    cases n with
    | zero =>
      dsimp only
      simp only [Nat.cast_zero] at h
      exact ⟨Bool.noConfusion, fun hab => by omega⟩
    | succ m =>
      dsimp only
      simp only [Nat.cast_add, Nat.cast_one, true_iff] at h ⊢
      omega
  | negSucc n =>
    simp only [Bool.false_eq_true, false_iff]
    omega

private theorem iblt_false_iff (a b : Int) : Cert.iblt a b = false ↔ b ≤ a := by
  rw [Bool.eq_false_iff, ne_eq, iblt_iff]; omega

private theorem imax_eq (a b : Int) : Cert.imax a b = max a b := by
  unfold Cert.imax
  by_cases h : a ≤ b
  · rw [if_true_eq ((ible_iff a b).mpr h), max_eq_right h]
  · rw [if_false_eq ((ible_false_iff a b).mpr (by omega)), max_eq_left (by omega)]

private theorem imin_eq (a b : Int) : Cert.imin a b = min a b := by
  unfold Cert.imin
  by_cases h : a ≤ b
  · rw [if_true_eq ((ible_iff a b).mpr h), min_eq_left h]
  · rw [if_false_eq ((ible_false_iff a b).mpr (by omega)), min_eq_right (by omega)]

private theorem valI_mono {a b : Int} (h : a ≤ b) : valI a ≤ valI b := by
  unfold valI
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num)

private theorem valI_lt {a b : Int} (h : a < b) : valI a < valI b := by
  unfold valI
  exact div_lt_div_of_pos_right (by exact_mod_cast h) (by norm_num)

private theorem valI_pos {b : Int} (h : 0 < b) : 0 < valI b := by
  unfold valI
  exact div_pos (by exact_mod_cast h) (by norm_num)

private theorem valI_nonneg {b : Int} (h : 0 ≤ b) : 0 ≤ valI b := by
  unfold valI
  exact div_nonneg (by exact_mod_cast h) (by norm_num)

private theorem valI_neg {a : Int} (h : a < 0) : valI a < 0 := by
  unfold valI
  exact div_neg_of_neg_of_pos (by exact_mod_cast h) (by norm_num)

private theorem ediv_real_le (a b : Int) (hb : 0 < b) :
    (Int.ediv a b : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hb_r : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hb_r]
  have hle : Int.ediv a b * b ≤ a := by
    have h1 := Int.mul_ediv_add_emod a b
    have h2 := Int.emod_nonneg a (by omega : b ≠ 0)
    change b * Int.ediv a b + a % b = a at h1
    linarith [mul_comm b (Int.ediv a b)]
  exact_mod_cast hle

private theorem le_cdiv_real (a b : Int) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (Cert.cdiv a b : ℝ) := by
  unfold Cert.cdiv
  simp only [bindInt_eq]
  change (a : ℝ) / (b : ℝ) ≤ (Int.ediv (a + b - 1) b : ℝ)
  have hb_r : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_le_iff₀ hb_r]
  have hge : a ≤ Int.ediv (a + b - 1) b * b := by
    have h1 := Int.mul_ediv_add_emod (a + b - 1) b
    have h2 := Int.emod_lt_of_pos (a + b - 1) hb
    change b * Int.ediv (a + b - 1) b + (a + b - 1) % b = a + b - 1 at h1
    linarith [mul_comm b (Int.ediv (a + b - 1) b)]
  exact_mod_cast hge

private theorem memI_const (n : Int) : MemI (valI n) (Cert.ivConst n) :=
  ⟨le_rfl, le_rfl⟩

private theorem memI_pi : MemI π Cert.ivPi := by
  refine ⟨?_, ?_⟩
  · unfold valI Cert.ivPi Cert.piLoI; linarith [pi_gt_d20]
  · unfold valI Cert.ivPi Cert.piHiI; linarith [pi_lt_d20]

private theorem memI_add {x y : ℝ} {a b : Cert.Ival} (ha : MemI x a) (hb : MemI y b) :
    MemI (x + y) (Cert.ivAdd a b) := by
  cases a; cases b
  rcases ha with ⟨ha0, ha1⟩; rcases hb with ⟨hb0, hb1⟩
  simp only [Cert.ivAdd, MemI, valI] at ha0 ha1 hb0 hb1 ⊢
  change ((_ + _ : Int) : ℝ) / _ ≤ _ ∧ _ ≤ ((_ + _ : Int) : ℝ) / _
  push_cast; constructor <;> linarith

private theorem memI_sub {x y : ℝ} {a b : Cert.Ival} (ha : MemI x a) (hb : MemI y b) :
    MemI (x - y) (Cert.ivSub a b) := by
  cases a; cases b
  rcases ha with ⟨ha0, ha1⟩; rcases hb with ⟨hb0, hb1⟩
  simp only [Cert.ivSub, MemI, valI] at ha0 ha1 hb0 hb1 ⊢
  change ((_ - _ : Int) : ℝ) / _ ≤ _ ∧ _ ≤ ((_ - _ : Int) : ℝ) / _
  push_cast; constructor <;> linarith

private theorem memI_neg {x : ℝ} {a : Cert.Ival} (ha : MemI x a) :
    MemI (-x) (Cert.ivNeg a) := by
  cases a
  rcases ha with ⟨ha0, ha1⟩
  simp only [Cert.ivNeg, MemI, valI] at ha0 ha1 ⊢
  change ((-_ : Int) : ℝ) / _ ≤ _ ∧ _ ≤ ((-_ : Int) : ℝ) / _
  push_cast; constructor <;> linarith

private theorem memI_max {x y : ℝ} {a b : Cert.Ival} (ha : MemI x a) (hb : MemI y b) :
    MemI (max x y) (Cert.ivMax a b) := by
  cases a with | mk alo ahi =>
  cases b with | mk blo bhi =>
  rcases ha with ⟨ha0, ha1⟩; rcases hb with ⟨hb0, hb1⟩
  simp only [Cert.ivMax, imax_eq, MemI]
  constructor
  · rcases le_total alo blo with h | h
    · rw [max_eq_right h]; exact hb0.trans (le_max_right x y)
    · rw [max_eq_left h]; exact ha0.trans (le_max_left x y)
  · rcases le_total ahi bhi with h | h
    · rw [max_eq_right h]; exact max_le (ha1.trans (valI_mono h)) hb1
    · rw [max_eq_left h]; exact max_le ha1 (hb1.trans (valI_mono h))

private theorem memI_abs {x : ℝ} {a : Cert.Ival} (ha : MemI x a) :
    MemI |x| (Cert.ivAbs a) := by
  cases a with | mk alo ahi =>
  rcases ha with ⟨ha0, ha1⟩
  unfold Cert.ivAbs
  dsimp only
  by_cases h0 : 0 ≤ alo
  · rw [if_true_eq ((ible_iff 0 alo).mpr h0)]
    have hx0 : 0 ≤ x := (valI_nonneg h0).trans ha0
    rw [abs_of_nonneg hx0]; exact ⟨ha0, ha1⟩
  · rw [if_false_eq ((ible_false_iff 0 alo).mpr (by omega))]
    by_cases h1 : ahi ≤ 0
    · rw [if_true_eq ((ible_iff ahi 0).mpr h1)]
      have hx1 : x ≤ 0 := ha1.trans <| by
        unfold valI
        exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h1) (by norm_num)
      rw [abs_of_nonpos hx1]
      simp only [MemI, valI] at ha0 ha1 ⊢
      change ((-ahi : Int) : ℝ) / _ ≤ -x ∧ -x ≤ ((-alo : Int) : ℝ) / _
      push_cast; constructor <;> linarith
    · rw [if_false_eq ((ible_false_iff ahi 0).mpr (by omega))]
      simp only [imax_eq, MemI]
      refine ⟨by unfold valI; simp only [Int.cast_zero, zero_div]; exact abs_nonneg x, ?_⟩
      rw [abs_le]
      have hmx1 : valI (-alo) ≤ valI (max (Int.neg alo) ahi) :=
        valI_mono (le_max_left (-alo) ahi)
      have hmx2 : valI ahi ≤ valI (max (Int.neg alo) ahi) :=
        valI_mono (le_max_right (-alo) ahi)
      have hneg : -valI (-alo) = valI alo := by unfold valI; push_cast; ring
      constructor <;> linarith

private theorem memI_scaleInt (k : Int) {x : ℝ} {a : Cert.Ival} (ha : MemI x a) :
    MemI ((k : ℝ) * x) (Cert.ivScaleInt k a) := by
  cases a with | mk alo ahi =>
  rcases ha with ⟨ha0, ha1⟩
  unfold Cert.ivScaleInt
  dsimp only
  by_cases hk : 0 ≤ k
  · rw [if_true_eq ((ible_iff 0 k).mpr hk)]
    have hkr : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    simp only [MemI, valI] at ha0 ha1 ⊢
    change ((k * alo : Int) : ℝ) / _ ≤ _ ∧ _ ≤ ((k * ahi : Int) : ℝ) / _
    push_cast
    exact ⟨by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left ha0 hkr,
      by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left ha1 hkr⟩
  · rw [if_false_eq ((ible_false_iff 0 k).mpr (by omega))]
    have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hk))
    simp only [MemI, valI] at ha0 ha1 ⊢
    change ((k * ahi : Int) : ℝ) / _ ≤ _ ∧ _ ≤ ((k * alo : Int) : ℝ) / _
    push_cast
    exact ⟨by rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left ha1 hkr,
      by rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left ha0 hkr⟩

private theorem memI_divInt {k : Int} (hk : 0 < k) {x : ℝ} {a : Cert.Ival} (ha : MemI x a) :
    MemI (x / (k : ℝ)) (Cert.ivDivInt a k) := by
  cases a with | mk alo ahi =>
  rcases ha with ⟨ha0, ha1⟩
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  simp only [Cert.ivDivInt, MemI, valI] at ha0 ha1 ⊢
  constructor
  · calc (Int.ediv alo k : ℝ) / 100000000
        ≤ ((alo : ℝ) / (k : ℝ)) / 100000000 :=
          div_le_div_of_nonneg_right (ediv_real_le alo k hk) (by norm_num)
      _ = ((alo : ℝ) / 100000000) / (k : ℝ) := by ring
      _ ≤ x / (k : ℝ) := div_le_div_of_nonneg_right ha0 hkr.le
  · calc x / (k : ℝ)
        ≤ ((ahi : ℝ) / 100000000) / (k : ℝ) := div_le_div_of_nonneg_right ha1 hkr.le
      _ = ((ahi : ℝ) / (k : ℝ)) / 100000000 := by ring
      _ ≤ (Cert.cdiv ahi k : ℝ) / 100000000 :=
          div_le_div_of_nonneg_right (le_cdiv_real ahi k hk) (by norm_num)

private theorem memI_scaleNat (n : ℕ) {x : ℝ} {a : Cert.Ival} (ha : MemI x a) :
    MemI ((n : ℝ) * x) (Cert.ivScaleInt (n : Int) a) := by
  simpa only [Int.cast_natCast] using memI_scaleInt (n : Int) ha

private theorem memI_divNat {n : ℕ} (hn : 0 < (n : Int)) {x : ℝ} {a : Cert.Ival}
    (ha : MemI x a) : MemI (x / (n : ℝ)) (Cert.ivDivInt a (n : Int)) := by
  simpa only [Int.cast_natCast] using memI_divInt hn ha

private theorem memI_divTwo {x : ℝ} {a : Cert.Ival} (ha : MemI x a) :
    MemI (x / 2) (Cert.ivDivInt a 2) :=
  memI_divNat (n := 2) (by norm_num) ha

private theorem mul_mem_corners {x0 x1 y0 y1 x y : ℝ}
    (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hy0 : y0 ≤ y) (hy1 : y ≤ y1) :
    min (min (x0 * y0) (x0 * y1)) (min (x1 * y0) (x1 * y1)) ≤ x * y ∧
    x * y ≤ max (max (x0 * y0) (x0 * y1)) (max (x1 * y0) (x1 * y1)) := by
  have step1 : min (x0 * y) (x1 * y) ≤ x * y ∧ x * y ≤ max (x0 * y) (x1 * y) := by
    rcases le_or_gt 0 y with hy | hy
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx0 hy),
        (mul_le_mul_of_nonneg_right hx1 hy).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx1 hy.le),
        (mul_le_mul_of_nonpos_right hx0 hy.le).trans (le_max_left _ _)⟩
  have step_y (c : ℝ) : min (c * y0) (c * y1) ≤ c * y ∧ c * y ≤ max (c * y0) (c * y1) := by
    rcases le_or_gt 0 c with hc | hc
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy0 hc),
        (mul_le_mul_of_nonneg_left hy1 hc).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy1 hc.le),
        (mul_le_mul_of_nonpos_left hy0 hc.le).trans (le_max_left _ _)⟩
  exact ⟨(min_le_min (step_y x0).1 (step_y x1).1).trans step1.1,
    step1.2.trans (max_le_max (step_y x0).2 (step_y x1).2)⟩

private theorem memI_mul {x y : ℝ} {a b : Cert.Ival} (ha : MemI x a) (hb : MemI y b) :
    MemI (x * y) (Cert.ivMul a b) := by
  cases a with | mk alo ahi =>
  cases b with | mk blo bhi =>
  rcases ha with ⟨ha0, ha1⟩; rcases hb with ⟨hb0, hb1⟩
  unfold Cert.ivMul
  simp only [bindIval_eq, bindInt_eq, imin_eq, imax_eq, Cert.certScale]
  by_cases hnn : (Cert.ible 0 alo && Cert.ible 0 blo) = true
  · rw [if_true_eq hnn]
    rw [Bool.and_eq_true, ible_iff, ible_iff] at hnn
    have ha_nn : (0 : ℝ) ≤ valI alo := valI_nonneg hnn.1
    have hb_nn : (0 : ℝ) ≤ valI blo := valI_nonneg hnn.2
    have hx_nn : 0 ≤ x := ha_nn.trans ha0
    simp only [MemI, valI] at ha0 ha1 hb0 hb1 ⊢
    constructor
    · calc (Int.ediv (Int.mul alo blo) 100000000 : ℝ) / 100000000
          ≤ ((alo * blo : Int) : ℝ) / 100000000 / 100000000 :=
            div_le_div_of_nonneg_right (ediv_real_le (alo * blo) 100000000 (by norm_num))
              (by norm_num)
        _ = ((alo : ℝ) / 100000000) * ((blo : ℝ) / 100000000) := by push_cast; ring
        _ ≤ x * y := mul_le_mul ha0 hb0 hb_nn hx_nn
    · calc x * y
          ≤ ((ahi : ℝ) / 100000000) * ((bhi : ℝ) / 100000000) :=
            mul_le_mul ha1 hb1 (hb_nn.trans hb0) (hx_nn.trans ha1)
        _ = ((ahi * bhi : Int) : ℝ) / 100000000 / 100000000 := by push_cast; ring
        _ ≤ (Cert.cdiv (Int.mul ahi bhi) 100000000 : ℝ) / 100000000 :=
            div_le_div_of_nonneg_right (le_cdiv_real (ahi * bhi) 100000000 (by norm_num))
              (by norm_num)
  · rw [if_false_eq (Bool.eq_false_iff.mpr hnn)]
    obtain ⟨hlo_c, hhi_c⟩ := mul_mem_corners ha0 ha1 hb0 hb1
    set mnI : Int := min (min (alo * blo) (alo * bhi)) (min (ahi * blo) (ahi * bhi))
    set mxI : Int := max (max (alo * blo) (alo * bhi)) (max (ahi * blo) (ahi * bhi))
    simp only [MemI]
    change valI (Int.ediv mnI 100000000) ≤ x * y ∧ x * y ≤ valI (Cert.cdiv mxI 100000000)
    have hmn_eq : (mnI : ℝ) / 100000000 / 100000000 =
        min (min (valI alo * valI blo) (valI alo * valI bhi))
          (min (valI ahi * valI blo) (valI ahi * valI bhi)) := by
      unfold valI; dsimp only [mnI]
      push_cast
      have d1 (p q : ℝ) : min p q / (100000000 : ℝ) = min (p / 100000000) (q / 100000000) := by
        rcases le_total p q with h | h
        · rw [min_eq_left h, min_eq_left (div_le_div_of_nonneg_right h (by norm_num))]
        · rw [min_eq_right h, min_eq_right (div_le_div_of_nonneg_right h (by norm_num))]
      rw [d1, d1, d1, d1, d1, d1]
      congr 2 <;> ring
    have hmx_eq : (mxI : ℝ) / 100000000 / 100000000 =
        max (max (valI alo * valI blo) (valI alo * valI bhi))
          (max (valI ahi * valI blo) (valI ahi * valI bhi)) := by
      unfold valI; dsimp only [mxI]
      push_cast
      have d1 (p q : ℝ) : max p q / (100000000 : ℝ) = max (p / 100000000) (q / 100000000) := by
        rcases le_total p q with h | h
        · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h (by norm_num))]
        · rw [max_eq_left h, max_eq_left (div_le_div_of_nonneg_right h (by norm_num))]
      rw [d1, d1, d1, d1, d1, d1]
      congr 2 <;> ring
    constructor
    · unfold valI at hmn_eq ⊢
      exact (div_le_div_of_nonneg_right (ediv_real_le mnI 100000000 (by norm_num))
        (by norm_num)).trans (hmn_eq.trans_le hlo_c)
    · unfold valI at hmx_eq ⊢
      exact hhi_c.trans (hmx_eq.symm.trans_le
        (div_le_div_of_nonneg_right (le_cdiv_real mxI 100000000 (by norm_num)) (by norm_num)))

private theorem memI_sq {x : ℝ} {a : Cert.Ival} (ha : MemI x a) :
    MemI (x ^ 2) (Cert.ivSq a) := by
  cases a with | mk alo ahi =>
  rcases ha with ⟨ha0, ha1⟩
  unfold Cert.ivSq
  simp only [bindIval_eq, bindInt_eq, imax_eq, Cert.certScale]
  by_cases h0 : 0 ≤ alo
  · rw [if_true_eq ((ible_iff 0 alo).mpr h0)]
    have ha_nn : 0 ≤ valI alo := valI_nonneg h0
    simp only [MemI, valI] at ha0 ha1 ⊢
    constructor
    · calc (Int.ediv (Int.mul alo alo) 100000000 : ℝ) / 100000000
          ≤ ((alo * alo : Int) : ℝ) / 100000000 / 100000000 :=
            div_le_div_of_nonneg_right (ediv_real_le (alo * alo) 100000000 (by norm_num))
              (by norm_num)
        _ = ((alo : ℝ) / 100000000) ^ 2 := by push_cast; ring
        _ ≤ x ^ 2 := pow_le_pow_left₀ ha_nn ha0 2
    · calc x ^ 2
          ≤ ((ahi : ℝ) / 100000000) ^ 2 := pow_le_pow_left₀ (ha_nn.trans ha0) ha1 2
        _ = ((ahi * ahi : Int) : ℝ) / 100000000 / 100000000 := by push_cast; ring
        _ ≤ (Cert.cdiv (Int.mul ahi ahi) 100000000 : ℝ) / 100000000 :=
            div_le_div_of_nonneg_right (le_cdiv_real (ahi * ahi) 100000000 (by norm_num))
              (by norm_num)
  · rw [if_false_eq ((ible_false_iff 0 alo).mpr (by omega))]
    by_cases h1 : ahi ≤ 0
    · rw [if_true_eq ((ible_iff ahi 0).mpr h1)]
      have ha_np : valI ahi ≤ 0 := by
        unfold valI
        exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h1) (by norm_num)
      simp only [MemI, valI] at ha0 ha1 ha_np ⊢
      constructor
      · calc (Int.ediv (Int.mul ahi ahi) 100000000 : ℝ) / 100000000
            ≤ ((ahi * ahi : Int) : ℝ) / 100000000 / 100000000 :=
              div_le_div_of_nonneg_right (ediv_real_le (ahi * ahi) 100000000 (by norm_num))
                (by norm_num)
          _ = (-(ahi : ℝ) / 100000000) ^ 2 := by push_cast; ring
          _ ≤ (-x) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
          _ = x ^ 2 := neg_sq x
      · calc x ^ 2 = (-x) ^ 2 := (neg_sq x).symm
          _ ≤ (-(alo : ℝ) / 100000000) ^ 2 :=
              pow_le_pow_left₀ (by linarith) (by linarith) 2
          _ = ((alo * alo : Int) : ℝ) / 100000000 / 100000000 := by push_cast; ring
          _ ≤ (Cert.cdiv (Int.mul alo alo) 100000000 : ℝ) / 100000000 :=
              div_le_div_of_nonneg_right (le_cdiv_real (alo * alo) 100000000 (by norm_num))
                (by norm_num)
    · rw [if_false_eq ((ible_false_iff ahi 0).mpr (by omega))]
      set mx := max (-alo) ahi
      have hmx_pos : 0 ≤ mx := le_trans (by omega : 0 ≤ ahi) (le_max_right _ _)
      have habs : |x| ≤ valI mx := by
        rw [abs_le]
        have hmx1 : valI (-alo) ≤ valI mx := valI_mono (le_max_left (-alo) ahi)
        have hmx2 : valI ahi ≤ valI mx := valI_mono (le_max_right (-alo) ahi)
        have hneg : -valI (-alo) = valI alo := by unfold valI; push_cast; ring
        constructor <;> linarith
      refine ⟨by unfold valI; simp only [Int.cast_zero, zero_div]; exact sq_nonneg x, ?_⟩
      change x ^ 2 ≤ valI (Cert.cdiv (Int.mul mx mx) 100000000)
      calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        _ ≤ (valI mx) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) habs 2
        _ = ((mx * mx : Int) : ℝ) / 100000000 / 100000000 := by unfold valI; push_cast; ring
        _ ≤ (Cert.cdiv (Int.mul mx mx) 100000000 : ℝ) / 100000000 :=
            div_le_div_of_nonneg_right (le_cdiv_real (mx * mx) 100000000 (by norm_num))
              (by norm_num)

private theorem memI_divPos {x y : ℝ} {a b : Cert.Ival} (ha : MemI x a) (hb : MemI y b)
    (hblo : 0 < b.lo) :
    MemI (x / y) (Cert.ivDivPos a b) := by
  cases a with | mk alo ahi =>
  cases b with | mk blo bhi =>
  dsimp only at hblo
  rcases ha with ⟨ha0, ha1⟩; rcases hb with ⟨hb0, hb1⟩
  have hblo_pos : 0 < valI blo := valI_pos hblo
  have hy_pos : 0 < y := lt_of_lt_of_le hblo_pos hb0
  have hbhi_pos_i : 0 < bhi := by
    have : valI blo ≤ valI bhi := hb0.trans hb1
    unfold valI at this
    have : (blo : ℝ) ≤ (bhi : ℝ) := by linarith
    have hle : blo ≤ bhi := by exact_mod_cast this
    omega
  have hbhi_pos : 0 < valI bhi := lt_of_lt_of_le hy_pos hb1
  unfold Cert.ivDivPos
  simp only [bindIval_eq, Cert.certScale, MemI]
  constructor
  · by_cases h0 : 0 ≤ alo
    · rw [if_true_eq ((ible_iff 0 alo).mpr h0)]
      have halo_nn : 0 ≤ valI alo := valI_nonneg h0
      calc valI (Int.ediv (Int.mul alo 100000000) bhi)
          ≤ ((alo * 100000000 : Int) : ℝ) / (bhi : ℝ) / 100000000 :=
            div_le_div_of_nonneg_right (ediv_real_le _ bhi hbhi_pos_i) (by norm_num)
        _ = valI alo / valI bhi := by
            unfold valI; push_cast; field_simp [(by exact_mod_cast hbhi_pos_i.ne' : (bhi : ℝ) ≠ 0)]
        _ ≤ valI alo / y := div_le_div_of_nonneg_left halo_nn hy_pos hb1
        _ ≤ x / y := div_le_div_of_nonneg_right ha0 hy_pos.le
    · rw [if_false_eq ((ible_false_iff 0 alo).mpr (by omega))]
      have halo_neg : valI alo ≤ 0 := by
        unfold valI
        exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (le_of_lt (not_le.mp h0)))
          (by norm_num)
      calc valI (Int.ediv (Int.mul alo 100000000) blo)
          ≤ ((alo * 100000000 : Int) : ℝ) / (blo : ℝ) / 100000000 :=
            div_le_div_of_nonneg_right (ediv_real_le _ blo hblo) (by norm_num)
        _ = valI alo / valI blo := by
            unfold valI; push_cast; field_simp [(by exact_mod_cast hblo.ne' : (blo : ℝ) ≠ 0)]
        _ ≤ valI alo / y := by
            have := div_le_div_of_nonneg_left (neg_nonneg.mpr halo_neg) hblo_pos hb0
            linarith [neg_div y (valI alo), neg_div (valI blo) (valI alo)]
        _ ≤ x / y := div_le_div_of_nonneg_right ha0 hy_pos.le
  · by_cases h1 : 0 ≤ ahi
    · rw [if_true_eq ((ible_iff 0 ahi).mpr h1)]
      have hahi_nn : 0 ≤ valI ahi := valI_nonneg h1
      calc x / y ≤ valI ahi / y := div_le_div_of_nonneg_right ha1 hy_pos.le
        _ ≤ valI ahi / valI blo := div_le_div_of_nonneg_left hahi_nn hblo_pos hb0
        _ = ((ahi * 100000000 : Int) : ℝ) / (blo : ℝ) / 100000000 := by
            unfold valI; push_cast; field_simp [(by exact_mod_cast hblo.ne' : (blo : ℝ) ≠ 0)]
        _ ≤ valI (Cert.cdiv (Int.mul ahi 100000000) blo) :=
            div_le_div_of_nonneg_right (le_cdiv_real _ blo hblo) (by norm_num)
    · rw [if_false_eq ((ible_false_iff 0 ahi).mpr (by omega))]
      have hahi_neg : valI ahi ≤ 0 := by
        unfold valI
        exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (le_of_lt (not_le.mp h1)))
          (by norm_num)
      calc x / y ≤ valI ahi / y := div_le_div_of_nonneg_right ha1 hy_pos.le
        _ ≤ valI ahi / valI bhi := by
            have := div_le_div_of_nonneg_left (neg_nonneg.mpr hahi_neg) hy_pos hb1
            linarith [neg_div y (valI ahi), neg_div (valI bhi) (valI ahi)]
        _ = ((ahi * 100000000 : Int) : ℝ) / (bhi : ℝ) / 100000000 := by
            unfold valI; push_cast; field_simp [(by exact_mod_cast hbhi_pos_i.ne' : (bhi : ℝ) ≠ 0)]
        _ ≤ valI (Cert.cdiv (Int.mul ahi 100000000) bhi) :=
            div_le_div_of_nonneg_right (le_cdiv_real _ bhi hbhi_pos_i) (by norm_num)

private theorem memI_qeval (q : Cert.QuadI) {r : ℝ} {rv : Cert.Ival} (hr : MemI r rv) :
    MemI (quadEval q r) (Cert.ivQeval q rv) := by
  unfold quadEval Cert.ivQeval
  rw [bindIval_eq]
  change MemI (valI q.c0 - valI q.c1 * (r - valI q.r0) - valI q.c2 * (r - valI q.r0) ^ 2) _
  have hd := memI_sub hr (memI_const q.r0)
  exact memI_sub (memI_sub (memI_const q.c0) (memI_mul (memI_const q.c1) hd))
    (memI_mul (memI_const q.c2) (memI_sq hd))

private theorem memI_qslope (q : Cert.QuadI) {r : ℝ} {rv : Cert.Ival} (hr : MemI r rv) :
    MemI (quadSlope q r) (Cert.ivQslope q rv) := by
  unfold quadSlope Cert.ivQslope
  rw [bindIval_eq]
  change MemI (valI q.c1 + (2 : Int) * (valI q.c2 * (r - valI q.r0))) _
  have hd := memI_sub hr (memI_const q.r0)
  exact memI_add (memI_const q.c1) (memI_scaleInt 2 (memI_mul (memI_const q.c2) hd))

private theorem bound1dPt_sound {sl curvLo dmaxHi : Int} {δ A : ℝ}
    (hδ : |δ| ≤ valI dmaxHi) (_hdmax : 0 ≤ dmaxHi) (hA : valI curvLo ≤ A) :
    valI sl * δ - A * δ ^ 2 ≤ valI (Cert.bound1dPt sl curvLo dmaxHi) := by
  unfold Cert.bound1dPt
  simp only [bindInt_eq, imin_eq]
  set absSl : Int := (Int.natAbs sl : Int)
  have habs_sl : |valI sl| = valI absSl := by
    unfold valI; rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 100000000)]
    congr 1; dsimp only [absSl]
    rcases le_or_gt 0 sl with h | h
    · have hnn : (Int.natAbs sl : Int) = sl := by omega
      rw [hnn, abs_of_nonneg (by exact_mod_cast h)]
    · have hneg : (Int.natAbs sl : Int) = -sl := by omega
      rw [hneg, Int.cast_neg, abs_of_neg (by exact_mod_cast h)]
  have hsl_nn : 0 ≤ valI absSl := habs_sl ▸ abs_nonneg _
  have hlin_real : valI sl * δ ≤ valI absSl * |δ| := by
    calc valI sl * δ ≤ |valI sl * δ| := le_abs_self _
      _ = valI absSl * |δ| := by rw [abs_mul, habs_sl]
  have hlin_hi : valI absSl * |δ| ≤
      valI (Cert.ivMul (Cert.ivConst absSl) (Cert.ivConst dmaxHi)).hi := by
    calc valI absSl * |δ| ≤ valI absSl * valI dmaxHi := mul_le_mul_of_nonneg_left hδ hsl_nn
      _ ≤ valI (Cert.ivMul (Cert.ivConst absSl) (Cert.ivConst dmaxHi)).hi :=
          (memI_mul (memI_const absSl) (memI_const dmaxHi)).2
  by_cases hc : curvLo ≤ 0
  · rw [if_true_eq ((ible_iff curvLo 0).mpr hc)]
    have hnegA : -A ≤ valI (-curvLo) := by unfold valI at hA ⊢; push_cast; linarith
    have hnn_neg : 0 ≤ valI (-curvLo) := valI_nonneg (by omega)
    have hsq_le : δ ^ 2 ≤ (valI dmaxHi) ^ 2 := by
      rw [← sq_abs δ]
      exact pow_le_pow_left₀ (abs_nonneg δ) hδ 2
    have hq_hi : -A * δ ^ 2 ≤
        valI (Cert.ivMul (Cert.ivConst (-curvLo)) (Cert.ivSq (Cert.ivConst dmaxHi))).hi := by
      calc -A * δ ^ 2 ≤ valI (-curvLo) * (valI dmaxHi) ^ 2 :=
            mul_le_mul hnegA hsq_le (sq_nonneg δ) hnn_neg
        _ ≤ _ := (memI_mul (memI_const (-curvLo)) (memI_sq (memI_const dmaxHi))).2
    have hv_add : valI ((Cert.ivMul (Cert.ivConst absSl) (Cert.ivConst dmaxHi)).hi +
        (Cert.ivMul (Cert.ivConst (-curvLo)) (Cert.ivSq (Cert.ivConst dmaxHi))).hi) =
        valI (Cert.ivMul (Cert.ivConst absSl) (Cert.ivConst dmaxHi)).hi +
        valI (Cert.ivMul (Cert.ivConst (-curvLo)) (Cert.ivSq (Cert.ivConst dmaxHi))).hi := by
      unfold valI; push_cast; ring
    rw [hv_add]; linarith
  · rw [if_false_eq ((ible_false_iff curvLo 0).mpr (by omega))]
    have hc_pos : 0 < curvLo := not_le.mp hc
    have hcurv_pos : 0 < valI curvLo := valI_pos hc_pos
    have hA_pos : 0 < A := lt_of_lt_of_le hcurv_pos hA
    have h1 : valI sl * δ - A * δ ^ 2 ≤
        valI (Cert.ivMul (Cert.ivConst absSl) (Cert.ivConst dmaxHi)).hi := by
      have : 0 ≤ A * δ ^ 2 := mul_nonneg hA_pos.le (sq_nonneg δ)
      linarith
    have h2 : valI sl * δ - A * δ ^ 2 ≤
        valI (Cert.ivDivPos (Cert.ivSq (Cert.ivConst absSl))
          (Cert.ivScaleInt 4 (Cert.ivConst curvLo))).hi := by
      have hvert : valI absSl * |δ| - A * δ ^ 2 ≤ (valI absSl) ^ 2 / (4 * A) := by
        rw [le_div_iff₀ (by positivity)]
        have hid : (valI absSl) ^ 2 - (valI absSl * |δ| - A * δ ^ 2) * (4 * A) =
            (2 * A * |δ| - valI absSl) ^ 2 := by
          rw [← sq_abs δ]; ring
        nlinarith [sq_nonneg (2 * A * |δ| - valI absSl)]
      have hden_pos : 0 < (Cert.ivScaleInt 4 (Cert.ivConst curvLo)).lo := by
        simp only [Cert.ivScaleInt, Cert.ivConst, show Cert.ible 0 4 = true by decide, ↓reduceIte]
        change 0 < 4 * curvLo; omega
      have hdiv_le : (valI absSl) ^ 2 / (4 * A) ≤ (valI absSl) ^ 2 / ((4 : Int) * valI curvLo) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by push_cast; positivity)
          (by push_cast; linarith)
      have hmem_div := memI_divPos (memI_sq (memI_const absSl))
        (memI_scaleInt 4 (memI_const curvLo)) hden_pos
      linarith [hmem_div.2]
    unfold valI at h1 h2 ⊢
    rcases le_total
      (Cert.ivMul (Cert.ivConst absSl) (Cert.ivConst dmaxHi)).hi
      (Cert.ivDivPos (Cert.ivSq (Cert.ivConst absSl))
        (Cert.ivScaleInt 4 (Cert.ivConst curvLo))).hi with hle | hle
    · rw [min_eq_left hle]; exact h1
    · rw [min_eq_right hle]; exact h2

private theorem bound1dIv_sound {sl curv : Cert.Ival} {dmaxHi : Int} {s A δ : ℝ}
    (hs : MemI s sl) (hA : MemI A curv) (hδ : |δ| ≤ valI dmaxHi) (hdmax : 0 ≤ dmaxHi) :
    s * δ - A * δ ^ 2 ≤ valI (Cert.bound1dIv sl curv dmaxHi) := by
  unfold Cert.bound1dIv
  rw [imax_eq]
  rcases le_or_gt 0 δ with h0 | h0
  · have hle : s * δ ≤ valI sl.hi * δ := mul_le_mul_of_nonneg_right hs.2 h0
    have hb := bound1dPt_sound hδ hdmax hA.1 (sl := sl.hi)
    have hmx : valI (Cert.bound1dPt sl.hi curv.lo dmaxHi) ≤
        valI (max (Cert.bound1dPt sl.lo curv.lo dmaxHi)
          (Cert.bound1dPt sl.hi curv.lo dmaxHi)) := valI_mono (le_max_right _ _)
    linarith
  · have hle : s * δ ≤ valI sl.lo * δ := mul_le_mul_of_nonpos_right hs.1 h0.le
    have hb := bound1dPt_sound hδ hdmax hA.1 (sl := sl.lo)
    have hmx : valI (Cert.bound1dPt sl.lo curv.lo dmaxHi) ≤
        valI (max (Cert.bound1dPt sl.lo curv.lo dmaxHi)
          (Cert.bound1dPt sl.hi curv.lo dmaxHi)) := valI_mono (le_max_left _ _)
    linarith

/-! ### Part 2: Box semantics, `clampBox` soundness, and leaf checkers -/

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private def MemBox (u : Fin 4 → E) (b : Cert.BoxI) : Prop :=
  MemI (pairSab u) ⟨b.a0, b.a1⟩ ∧
  MemI (pairScd u) ⟨b.b0, b.b1⟩ ∧
  MemI (pairRb u) ⟨b.r0, b.r1⟩ ∧
  MemI (pairO1 u) ⟨b.o10, b.o11⟩ ∧
  MemI (pairO2 u) ⟨b.o20, b.o21⟩ ∧
  MemI (pairTau u) ⟨b.t0, b.t1⟩

private def BoxValid (b : Cert.BoxI) : Prop :=
  ∀ u : Fin 4 → E, IsAdmissiblePair u → 0 ≤ pairO1 u → pairO1 u ≤ pairO2 u →
    MemBox u b → pairCost u 0 ≤ 27735 / 100000

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem not_memBox_of_isEmptyBox {b : Cert.BoxI} (hemp : Cert.isEmptyBox b = true)
    (u : Fin 4 → E) : ¬MemBox u b := by
  intro ⟨ha, hb, hr, ho1, ho2, ht⟩
  unfold Cert.isEmptyBox at hemp
  simp only [Bool.or_eq_true, iblt_iff] at hemp
  rcases hemp with ((((h | h) | h) | h) | h) | h
  · linarith [ha.1, ha.2, valI_lt h]
  · linarith [hb.1, hb.2, valI_lt h]
  · linarith [hr.1, hr.2, valI_lt h]
  · linarith [ho1.1, ho1.2, valI_lt h]
  · linarith [ho2.1, ho2.2, valI_lt h]
  · linarith [ht.1, ht.2, valI_lt h]

omit [BorelSpace E] in
private theorem boxValid_of_isEmptyBox {b : Cert.BoxI} (hemp : Cert.isEmptyBox b = true) :
    BoxValid (E := E) b :=
  fun u _ _ _ hm => (not_memBox_of_isEmptyBox hemp u hm).elim

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem box_nonempty_coords {u : Fin 4 → E} {b : Cert.BoxI} (hm : MemBox u b) :
    b.a0 ≤ b.a1 ∧ b.b0 ≤ b.b1 ∧ b.r0 ≤ b.r1 ∧
    b.o10 ≤ b.o11 ∧ b.o20 ≤ b.o21 ∧ b.t0 ≤ b.t1 := by
  have hle {x : ℝ} {lo hi : Int} (h : MemI x ⟨lo, hi⟩) : lo ≤ hi := by
    have : valI lo ≤ valI hi := h.1.trans h.2
    unfold valI at this
    have hr : (lo : ℝ) ≤ (hi : ℝ) := by linarith
    exact_mod_cast hr
  exact ⟨hle hm.1, hle hm.2.1, hle hm.2.2.1, hle hm.2.2.2.1, hle hm.2.2.2.2.1, hle hm.2.2.2.2.2⟩

private theorem intEq_iff (a b : Int) : Cert.intEq a b = true ↔ a = b := by
  unfold Cert.intEq
  rw [Bool.and_eq_true, ible_iff, ible_iff]
  omega

private theorem natLt_iff (a b : Nat) : Cert.natLt a b = true ↔ a < b := by
  unfold Cert.natLt
  rw [iblt_iff]
  simp only [Int.ofNat_eq_natCast, Nat.cast_lt]

private theorem natEq_iff (a b : Nat) : Cert.natEq a b = true ↔ a = b := by
  unfold Cert.natEq
  rw [intEq_iff]
  simp only [Int.ofNat_eq_natCast, Nat.cast_inj]

private theorem boxEq_iff (a b : Cert.BoxI) : Cert.boxEq a b = true ↔ a = b := by
  cases a; cases b
  simp only [Cert.boxEq, Bool.and_eq_true, intEq_iff, Cert.BoxI.mk.injEq]
  tauto

private theorem lookupSub_sound {P : Cert.BoxI → Prop} {t : Cert.SubTree}
    (ht : Cert.SubTreeAll P t) {idx : Nat} {b : Cert.BoxI}
    (hl : Cert.lookupSub t idx = some b) : P b := by
  induction t with
  | empty => cases hl
  | leaf k c =>
    simp only [Cert.lookupSub] at hl
    split_ifs at hl with heq
    injection hl with hb; exact hb ▸ ht
  | node mid l r ihl ihr =>
    simp only [Cert.lookupSub] at hl
    split_ifs at hl with hlt
    · exact ihl ht.1 hl
    · exact ihr ht.2 hl

private theorem divPos_one_lo_le {y : ℝ} {b : Cert.Ival} (hy : 0 < y) (hb : MemI y b) :
    valI (Cert.ivDivPos (Cert.ivConst Cert.certScale) b).lo ≤ 1 / y := by
  cases b with | mk blo bhi =>
  rcases hb with ⟨_, hb1⟩
  have hbhi_pos_r : 0 < valI bhi := lt_of_lt_of_le hy hb1
  have hbhi_pos : 0 < bhi := by
    unfold valI at hbhi_pos_r
    have : (0 : ℝ) < (bhi : ℝ) := by linarith
    exact_mod_cast this
  unfold Cert.ivDivPos
  simp only [bindIval_eq, Cert.ivConst, Cert.certScale,
    show Cert.ible 0 100000000 = true by decide, ↓reduceIte]
  calc valI (Int.ediv (Int.mul 100000000 100000000) bhi)
      ≤ ((100000000 * 100000000 : Int) : ℝ) / (bhi : ℝ) / 100000000 :=
        div_le_div_of_nonneg_right (ediv_real_le _ bhi hbhi_pos) (by norm_num)
    _ = 1 / valI bhi := by
        unfold valI; push_cast
        field_simp [(by exact_mod_cast hbhi_pos.ne' : (bhi : ℝ) ≠ 0)]; ring
    _ ≤ 1 / y := one_div_le_one_div_of_le hy hb1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem calcSchurRhsHi_sound {u : Fin 4 → E} {b : Cert.BoxI} {sig : Int}
    (hadm : IsAdmissiblePair u) (hm : MemBox u b)
    (hsig : sig = 1 ∨ sig = -1) (hok : 0 ≤ Cert.calcSchurRhsHi b sig) :
    0 ≤ (pairSab u + pairScd u) / 2 + 3 / 7 * pairRb u +
      (sig : ℝ) * (16 / 35) * pairTau u - 1322905 / 1000000 +
      valI (Cert.calcSchurRhsHi b sig) := by
  unfold Cert.calcSchurRhsHi at hok ⊢
  cases hpre : Cert.schurPre b sig with
  | none => rw [hpre] at hok; dsimp only at hok; omega
  | some sp =>
    rw [hpre] at hok
    dsimp only at hok ⊢
    unfold Cert.schurPre at hpre
    simp only [bindIval_eq] at hpre hok ⊢
    split_ifs at hpre with hc1 hc2
    injection hpre with hsp; subst hsp
    split_ifs at hok ⊢ with hc3 hc4
    · omega
    · omega
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, ible_false_iff] at hc1 hc4
      rw [Bool.not_eq_true, ible_false_iff] at hc2 hc3
      rcases hm with ⟨ha, hcd, hr, ho1, ho2, ht⟩
      have hc2_eq : valI Cert.c2I = 1322905 / 1000000 := by unfold valI Cert.c2I; norm_num
      have ha1_m : MemI (1322905 / 1000000 - pairSab u) ⟨Cert.c2I - b.a1, Cert.c2I - b.a0⟩ := by
        rw [← hc2_eq]; exact memI_sub (memI_const Cert.c2I) ha
      have ha2_m : MemI (1322905 / 1000000 + pairSab u) ⟨Cert.c2I + b.a0, Cert.c2I + b.a1⟩ := by
        rw [← hc2_eq]; exact memI_add (memI_const Cert.c2I) ha
      have hd2_m : MemI (1322905 / 1000000 + pairScd u) ⟨Cert.c2I + b.b0, Cert.c2I + b.b1⟩ := by
        rw [← hc2_eq]; exact memI_add (memI_const Cert.c2I) hcd
      have hm11_35 : MemI (15 * pairRb u + (sig * 16 : Int) * pairTau u)
          (Cert.ivAdd (Cert.ivScaleInt 15 ⟨b.r0, b.r1⟩)
            (Cert.ivScaleInt (sig * 16) ⟨b.t0, b.t1⟩)) :=
        memI_add (memI_scaleInt 15 hr) (memI_scaleInt (sig * 16) ht)
      have hm22_35 : MemI (15 * pairTau u + (sig * 16 : Int) * pairRb u)
          (Cert.ivAdd (Cert.ivScaleInt 15 ⟨b.t0, b.t1⟩)
            (Cert.ivScaleInt (sig * 16) ⟨b.r0, b.r1⟩)) :=
        memI_add (memI_scaleInt 15 ht) (memI_scaleInt (sig * 16) hr)
      have hm12_35 : MemI (15 * pairO2 u + (sig * 16 : Int) * pairO1 u)
          (Cert.ivAdd (Cert.ivScaleInt 15 ⟨b.o20, b.o21⟩)
            (Cert.ivScaleInt (sig * 16) ⟨b.o10, b.o11⟩)) :=
        memI_add (memI_scaleInt 15 ho2) (memI_scaleInt (sig * 16) ho1)
      have hm21_35 : MemI (15 * pairO1 u + (sig * 16 : Int) * pairO2 u)
          (Cert.ivAdd (Cert.ivScaleInt 15 ⟨b.o10, b.o11⟩)
            (Cert.ivScaleInt (sig * 16) ⟨b.o20, b.o21⟩)) :=
        memI_add (memI_scaleInt 15 ho1) (memI_scaleInt (sig * 16) ho2)
      set sac := ⟪u 0, u 2⟫; set sbd := ⟪u 1, u 3⟫
      set sad := ⟪u 0, u 3⟫; set sbc := ⟪u 1, u 2⟫
      have hsch : schurPairIneq (pairSab u) (pairScd u) sac sbd sad sbc (sig : ℝ) := by
        rcases hadm with ⟨_, _, _, _, _, _, _, hs1, hs2, _, _⟩
        rcases hsig with rfl | rfl
        · simpa only [Int.cast_one, pairSab, pairScd] using hs1
        · simpa only [Int.cast_neg, Int.cast_one, pairSab, pairScd] using hs2
      have eq11 : 2 * (3 / 14 * pairRb u + (sig : ℝ) * (8 / 35) * pairTau u) =
          (15 * pairRb u + (sig * 16 : Int) * pairTau u) / (35 : Int) := by push_cast; ring
      have eq22 : 2 * (3 / 14 * pairTau u + (sig : ℝ) * (8 / 35) * pairRb u) =
          (15 * pairTau u + (sig * 16 : Int) * pairRb u) / (35 : Int) := by push_cast; ring
      have eq12 : 2 * (3 / 14 * pairO2 u + (sig : ℝ) * (8 / 35) * pairO1 u) =
          (15 * pairO2 u + (sig * 16 : Int) * pairO1 u) / (35 : Int) := by push_cast; ring
      have eq21 : 2 * (3 / 14 * pairO1 u + (sig : ℝ) * (8 / 35) * pairO2 u) =
          (15 * pairO1 u + (sig * 16 : Int) * pairO2 u) / (35 : Int) := by push_cast; ring
      have sq12 : (2 * (3 / 14 * pairO2 u + (sig : ℝ) * (8 / 35) * pairO1 u)) ^ 2 =
          (15 * pairO2 u + (sig * 16 : Int) * pairO1 u) ^ 2 / (1225 : Int) := by
        rw [eq12]; push_cast; ring
      have sq22 : (2 * (3 / 14 * pairTau u + (sig : ℝ) * (8 / 35) * pairRb u)) ^ 2 =
          (15 * pairTau u + (sig * 16 : Int) * pairRb u) ^ 2 / (1225 : Int) := by
        rw [eq22]; push_cast; ring
      have sq21 : (2 * (3 / 14 * pairO1 u + (sig : ℝ) * (8 / 35) * pairO2 u)) ^ 2 =
          (15 * pairO1 u + (sig * 16 : Int) * pairO2 u) ^ 2 / (1225 : Int) := by
        rw [eq21]; push_cast; ring
      have hx2_m := memI_sub
        (memI_mul ha2_m (memI_sub (memI_mul ha1_m hd2_m)
          (memI_divInt (k := 1225) (by norm_num) (memI_sq hm12_35))))
        (memI_mul ha1_m (memI_divInt (k := 1225) (by norm_num) (memI_sq hm22_35)))
      rw [← sq12, ← sq22] at hx2_m
      have hy_eq : ((1322905 / 1000000 + pairSab u) *
            (|15 * pairRb u + (sig * 16 : Int) * pairTau u| *
              |15 * pairO2 u + (sig * 16 : Int) * pairO1 u|) +
          (1322905 / 1000000 - pairSab u) *
            (|15 * pairO1 u + (sig * 16 : Int) * pairO2 u| *
              |15 * pairTau u + (sig * 16 : Int) * pairRb u|)) / (1225 : Int) =
          (1322905 / 1000000 + pairSab u) *
            |2 * (3 / 14 * pairRb u + (sig : ℝ) * (8 / 35) * pairTau u)| *
            |2 * (3 / 14 * pairO2 u + (sig : ℝ) * (8 / 35) * pairO1 u)| +
          (1322905 / 1000000 - pairSab u) *
            |2 * (3 / 14 * pairO1 u + (sig : ℝ) * (8 / 35) * pairO2 u)| *
            |2 * (3 / 14 * pairTau u + (sig : ℝ) * (8 / 35) * pairRb u)| := by
        rw [eq11, eq12, eq21, eq22, abs_div, abs_div, abs_div, abs_div]
        push_cast; rw [abs_of_pos (by norm_num : (0 : ℝ) < 35)]; ring
      have hy_sum_m := memI_add
        (memI_mul ha2_m (memI_mul (memI_abs hm11_35) (memI_abs hm12_35)))
        (memI_mul ha1_m (memI_mul (memI_abs hm21_35) (memI_abs hm22_35)))
      have hy_m := memI_divInt (k := 1225) (by norm_num) hy_sum_m
      rw [hy_eq] at hy_m
      have hsm_m : MemI ((pairSab u - pairScd u) / 2)
          (Cert.ivDivInt (Cert.ivSub ⟨b.a0, b.a1⟩ ⟨b.b0, b.b1⟩) 2) :=
        memI_divTwo (memI_sub ha hcd)
      have hsp_m : MemI ((pairSab u + pairScd u) / 2)
          (Cert.ivDivInt (Cert.ivAdd ⟨b.a0, b.a1⟩ ⟨b.b0, b.b1⟩) 2) :=
        memI_divTwo (memI_add ha hcd)
      have hden_m := memI_add (memI_sub (memI_const Cert.c2I) hsp_m)
        (memI_divInt (k := 35) (by norm_num) hm11_35)
      rw [hc2_eq, ← eq11] at hden_m
      have hsq21_m := memI_divInt (k := 1225) (by norm_num) (memI_sq hm21_35)
      rw [← sq21] at hsq21_m
      have hterm1_m := memI_divPos (memI_mul ha1_m hsq21_m) ha2_m hc1.1.2
      have hterm2_m := memI_divPos (memI_sq hy_m) (memI_mul ha2_m hx2_m) hc4.2
      have hnum_m := memI_add (memI_sq hsm_m) (memI_add hterm1_m hterm2_m)
      have hrhs_m := memI_divPos hnum_m hden_m hc4.1
      have ha1_nn : 0 ≤ 1322905 / 1000000 - pairSab u :=
        (valI_pos hc1.1.1).le.trans ha1_m.1
      have ha2_pos : 0 < 1322905 / 1000000 + pairSab u :=
        lt_of_lt_of_le (valI_pos hc1.1.2) ha2_m.1
      have hm11_pos : 0 < 2 * (3 / 14 * pairRb u + (sig : ℝ) * (8 / 35) * pairTau u) := by
        rw [eq11]
        exact div_pos (lt_of_lt_of_le (valI_pos hc2) hm11_35.1) (by norm_num)
      have hx2_pos := lt_of_lt_of_le (valI_pos hc3) hx2_m.1
      have hden_pos := lt_of_lt_of_le (valI_pos hc4.1) hden_m.1
      have hrhs_le := hrhs_m.2
      rw [← add_assoc (((pairSab u - pairScd u) / 2) ^ 2)] at hrhs_le
      dsimp only [pairRb, pairO1, pairO2, pairTau] at hm11_pos hx2_pos hden_pos hrhs_le
      exact schurPairIneq_linear_rhs hsch ha1_nn ha2_pos hm11_pos hx2_pos hden_pos hrhs_le

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem clampStep1_sound {b0 b1 : Cert.BoxI} (h1 : Cert.clampStep1 b0 = some b1)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u)
    (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u) (hm : MemBox u b0) :
    MemBox u b1 := by
  unfold Cert.clampStep1 at h1
  simp only [bindInt_eq, imax_eq, imin_eq, Option.some.injEq] at h1
  subst h1
  rcases hm with ⟨ha, hb, hr, h_o1, h_o2, ht⟩
  have hrb := admissiblePair_root_bounds hadm ho1 ho12
  have hcmin : valI Cert.cminI = 79998000 / 100000000 := by unfold valI Cert.cminI; norm_num
  have hscale : valI Cert.certScale = 1 := by unfold valI Cert.certScale; norm_num
  set o20 := max b0.o20 b0.o10
  set o11 := min b0.o11 b0.o21
  set dlo := max 0 (o20 - o11)
  have ho20_le : valI o20 ≤ pairO2 u := by
    rcases le_total b0.o20 b0.o10 with h | h
    · dsimp only [o20]; rw [max_eq_right h]; exact h_o1.1.trans ho12
    · dsimp only [o20]; rw [max_eq_left h]; exact h_o2.1
  have ho11_ge : pairO1 u ≤ valI o11 := by
    rcases le_total b0.o11 b0.o21 with h | h
    · dsimp only [o11]; rw [min_eq_left h]; exact h_o1.2
    · dsimp only [o11]; rw [min_eq_right h]; exact ho12.trans h_o2.2
  have hdlo_le : valI dlo ≤ pairO2 u - pairO1 u := by
    rcases le_total 0 (o20 - o11) with h | h
    · dsimp only [dlo]; rw [max_eq_right h]
      unfold valI at ho20_le ho11_ge ⊢; push_cast; linarith
    · dsimp only [dlo]; rw [max_eq_left h]
      unfold valI; simp only [Int.cast_zero, zero_div]; linarith
  refine ⟨ha, hb, hr, ⟨h_o1.1, ho11_ge⟩, ⟨ho20_le, h_o2.2⟩, ?_, ?_⟩
  · have ht0_1 : valI (Cert.cminI - b0.r1 + b0.o10 + o20) ≤ pairTau u := by
      have : valI (Cert.cminI - b0.r1 + b0.o10 + o20) =
          valI Cert.cminI - valI b0.r1 + valI b0.o10 + valI o20 := by
        unfold valI; push_cast; ring
      linarith [hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hr.2, h_o1.1]
    have ht0_2 : valI (b0.r0 - Cert.certScale + dlo) ≤ pairTau u := by
      have : valI (b0.r0 - Cert.certScale + dlo) =
          valI b0.r0 - valI Cert.certScale + valI dlo := by unfold valI; push_cast; ring
      linarith [hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
        hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.1]
    have hmx : valI (max b0.t0 (max (Cert.cminI - b0.r1 + b0.o10 + o20)
        (b0.r0 - Cert.certScale + dlo))) =
        max (valI b0.t0) (max (valI (Cert.cminI - b0.r1 + b0.o10 + o20))
          (valI (b0.r0 - Cert.certScale + dlo))) := by
      have m (x y : Int) : valI (max x y) = max (valI x) (valI y) := by
        rcases le_total x y with h | h
        · rw [max_eq_right h, max_eq_right (valI_mono h)]
        · rw [max_eq_left h, max_eq_left (valI_mono h)]
      rw [m, m]
    rw [hmx]; exact max_le ht.1 (max_le ht0_1 ht0_2)
  · have ht1_1 : pairTau u ≤ valI (Cert.certScale - b0.r0 - b0.o10 - o20) := by
      have : valI (Cert.certScale - b0.r0 - b0.o10 - o20) =
          valI Cert.certScale - valI b0.r0 - valI b0.o10 - valI o20 := by
        unfold valI; push_cast; ring
      linarith [hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hrb.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hr.1, h_o1.1]
    have ht1_2 : pairTau u ≤ valI (b0.r1 - Cert.cminI - dlo) := by
      have : valI (b0.r1 - Cert.cminI - dlo) =
          valI b0.r1 - valI Cert.cminI - valI dlo := by unfold valI; push_cast; ring
      linarith [hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2]
    have hmn : valI (min b0.t1 (min (Cert.certScale - b0.r0 - b0.o10 - o20)
        (b0.r1 - Cert.cminI - dlo))) =
        min (valI b0.t1) (min (valI (Cert.certScale - b0.r0 - b0.o10 - o20))
          (valI (b0.r1 - Cert.cminI - dlo))) := by
      have m (x y : Int) : valI (min x y) = min (valI x) (valI y) := by
        rcases le_total x y with h | h
        · rw [min_eq_left h, min_eq_left (valI_mono h)]
        · rw [min_eq_right h, min_eq_right (valI_mono h)]
      rw [m, m]
    rw [hmn]; exact le_min ht.2 (le_min ht1_1 ht1_2)

private theorem valI_cdiv_ge (a b : Int) (hb : 0 < b) :
    valI a / (b : ℝ) ≤ valI (Cert.cdiv a b) := by
  unfold valI
  calc ((a : ℝ) / 100000000) / (b : ℝ)
      = ((a : ℝ) / (b : ℝ)) / 100000000 := by ring
    _ ≤ (Cert.cdiv a b : ℝ) / 100000000 :=
        div_le_div_of_nonneg_right (le_cdiv_real a b hb) (by norm_num)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem clampStep2_sound {b1 : Cert.BoxI} {cs2 : Cert.ClampS2}
    (h2 : Cert.clampStep2 b1 = some cs2)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u) (hm1 : MemBox u b1) :
    MemBox u cs2.b ∧ cs2.srM = Cert.calcSchurRhsHi b1 (-1) ∧
    cs2.srP = Cert.calcSchurRhsHi b1 1 ∧
    cs2.b.a0 = b1.a0 ∧ cs2.b.a1 = b1.a1 ∧ cs2.b.b0 = b1.b0 ∧ cs2.b.b1 = b1.b1 ∧
    cs2.b.r0 = b1.r0 ∧ cs2.b.r1 = b1.r1 ∧ cs2.b.o10 = b1.o10 ∧ cs2.b.o11 = b1.o11 ∧
    cs2.b.o20 = b1.o20 ∧ cs2.b.o21 = b1.o21 := by
  unfold Cert.clampStep2 at h2
  simp only [bindInt_eq, imin_eq, imax_eq, Option.some.injEq] at h2
  subst h2
  rcases hm1 with ⟨ha, hb, hr, ho1, ho2, ht⟩
  have hsp_le : (pairSab u + pairScd u) / 2 ≤ valI (Cert.cdiv (b1.a1 + b1.b1) 2) := by
    calc (pairSab u + pairScd u) / 2
        ≤ valI (b1.a1 + b1.b1) / (2 : Int) := by
          unfold MemI valI at ha hb; unfold valI; push_cast; linarith [ha.2, hb.2]
      _ ≤ valI (Cert.cdiv (b1.a1 + b1.b1) 2) := valI_cdiv_ge _ 2 (by norm_num)
  have hr_le : 3 / 7 * pairRb u ≤ valI (Cert.cdiv (3 * b1.r1) 7) := by
    calc 3 / 7 * pairRb u
        ≤ valI (3 * b1.r1) / (7 : Int) := by
          unfold MemI valI at hr; unfold valI; push_cast; linarith [hr.2]
      _ ≤ valI (Cert.cdiv (3 * b1.r1) 7) := valI_cdiv_ge _ 7 (by norm_num)
  have hc2_eq : valI Cert.c2I = 1322905 / 1000000 := by unfold valI Cert.c2I; norm_num
  refine ⟨⟨ha, hb, hr, ho1, ho2, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩
  dsimp only [MemI]
  constructor
  · split_ifs with hp
    · rw [ible_iff] at hp
      have hsch := calcSchurRhsHi_sound hadm ⟨ha, hb, hr, ho1, ho2, ht⟩ (Or.inl rfl) hp
      have hlin : -pairTau u ≤ valI (35 * (Cert.cdiv (b1.a1 + b1.b1) 2 +
          Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + Cert.calcSchurRhsHi b1 1)) / (16 : Int) := by
        have hval : valI (35 * (Cert.cdiv (b1.a1 + b1.b1) 2 +
            Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + Cert.calcSchurRhsHi b1 1)) =
            35 * (valI (Cert.cdiv (b1.a1 + b1.b1) 2) + valI (Cert.cdiv (3 * b1.r1) 7) -
              valI Cert.c2I + valI (Cert.calcSchurRhsHi b1 1)) := by
          unfold valI; push_cast; ring
        rw [hval, hc2_eq]; push_cast at hsch ⊢; linarith
      have hcdiv := hlin.trans (valI_cdiv_ge _ 16 (by norm_num))
      have hneg : valI (-Cert.cdiv (35 * (Cert.cdiv (b1.a1 + b1.b1) 2 +
          Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + Cert.calcSchurRhsHi b1 1)) 16) ≤ pairTau u := by
        unfold valI at hcdiv ⊢; push_cast; linarith
      rcases le_total b1.t0 (-Cert.cdiv (35 * (Cert.cdiv (b1.a1 + b1.b1) 2 +
          Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + Cert.calcSchurRhsHi b1 1)) 16) with h | h
      · rw [max_eq_right h]; exact hneg
      · rw [max_eq_left h]; exact ht.1
    · exact ht.1
  · split_ifs with hm
    · rw [ible_iff] at hm
      have hsch := calcSchurRhsHi_sound hadm ⟨ha, hb, hr, ho1, ho2, ht⟩ (Or.inr rfl) hm
      have hlin : pairTau u ≤ valI (35 * (Cert.cdiv (b1.a1 + b1.b1) 2 +
          Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + Cert.calcSchurRhsHi b1 (-1))) / (16 : Int) := by
        have hval : valI (35 * (Cert.cdiv (b1.a1 + b1.b1) 2 +
            Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + Cert.calcSchurRhsHi b1 (-1))) =
            35 * (valI (Cert.cdiv (b1.a1 + b1.b1) 2) + valI (Cert.cdiv (3 * b1.r1) 7) -
              valI Cert.c2I + valI (Cert.calcSchurRhsHi b1 (-1))) := by
          unfold valI; push_cast; ring
        rw [hval, hc2_eq]; push_cast at hsch ⊢; linarith
      have hcdiv := hlin.trans (valI_cdiv_ge _ 16 (by norm_num))
      rcases le_total b1.t1 (Cert.cdiv (35 * (Cert.cdiv (b1.a1 + b1.b1) 2 +
          Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + Cert.calcSchurRhsHi b1 (-1))) 16) with h | h
      · rw [min_eq_left h]; exact ht.2
      · rw [min_eq_right h]; exact hcdiv
    · exact ht.2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem clampStep34_sound {b1 : Cert.BoxI} {cs2 : Cert.ClampS2} {cs3 : Cert.ClampS3}
    {b4 : Cert.BoxI}
    (hcs2 : cs2.srM = Cert.calcSchurRhsHi b1 (-1) ∧ cs2.srP = Cert.calcSchurRhsHi b1 1 ∧
      cs2.b.r1 = b1.r1)
    (h3 : Cert.clampStep3 cs2.b = some cs3) (h4 : Cert.clampStep4 b1 cs2 cs3 = some b4)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u) (hm1 : MemBox u b1) (hm2 : MemBox u cs2.b) :
    MemBox u b4 := by
  unfold Cert.clampStep3 at h3
  simp only [bindIval_eq] at h3
  split_ifs at h3 with hd_le
  injection h3 with hcs3
  rw [Bool.not_eq_true, ible_false_iff] at hd_le
  rcases hm2 with ⟨ha, hb, hr, ho1, ho2, ht⟩
  have h1_m : MemI 1 (Cert.ivConst Cert.certScale) := by
    have h1 : valI Cert.certScale = 1 := by unfold valI Cert.certScale; norm_num
    exact h1 ▸ memI_const Cert.certScale
  have hvx_eq : cs3.vx =
      Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨cs2.b.a0, cs2.b.a1⟩) 2 := by
    rw [← hcs3]
  have hvy_eq : cs3.vy =
      Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨cs2.b.b0, cs2.b.b1⟩) 2 := by
    rw [← hcs3]
  have hd_eq : cs3.dIv =
      Cert.ivSub (Cert.ivMul cs3.vx cs3.vy) (Cert.ivSq ⟨cs2.b.r0, cs2.b.r1⟩) := by
    rw [hvx_eq, hvy_eq, ← hcs3]
  have hvx_m : MemI ((1 + pairSab u) / 2) cs3.vx :=
    hvx_eq ▸ memI_divTwo (memI_add h1_m ha)
  have hvy_m : MemI ((1 + pairScd u) / 2) cs3.vy :=
    hvy_eq ▸ memI_divTwo (memI_add h1_m hb)
  have hd_m : MemI ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) cs3.dIv :=
    hd_eq ▸ memI_sub (memI_mul hvx_m hvy_m) (memI_sq hr)
  have hdl_pos : 0 < cs3.dIv.lo := by rwa [hd_eq, hvx_eq, hvy_eq]
  have hD_pos : 0 < (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2 :=
    lt_of_lt_of_le (valI_pos hdl_pos) hd_m.1
  have hh1a_m : MemI ((1 - pairSab u) / 2)
      (Cert.ivDivInt (Cert.ivSub (Cert.ivConst Cert.certScale) ⟨cs2.b.a0, cs2.b.a1⟩) 2) :=
    memI_divTwo (memI_sub h1_m ha)
  have hh1b_m : MemI ((1 - pairScd u) / 2)
      (Cert.ivDivInt (Cert.ivSub (Cert.ivConst Cert.certScale) ⟨cs2.b.b0, cs2.b.b1⟩) 2) :=
    memI_divTwo (memI_sub h1_m hb)
  have hq1_m := memI_divPos (memI_mul (memI_sq ho1) hvx_m) hd_m hdl_pos
  have hq2_m := memI_divPos (memI_mul (memI_sq ho2) hvy_m) hd_m hdl_pos
  have hk00_eq : cs3.k00 =
      Cert.ivSub (Cert.ivDivInt (Cert.ivSub (Cert.ivConst Cert.certScale) ⟨cs2.b.a0, cs2.b.a1⟩) 2)
        (Cert.ivDivPos (Cert.ivMul (Cert.ivSq ⟨cs2.b.o10, cs2.b.o11⟩) cs3.vx) cs3.dIv) := by
    rw [hd_eq, hvx_eq, hvy_eq, ← hcs3]
  have hk11_eq : cs3.k11 =
      Cert.ivSub (Cert.ivDivInt (Cert.ivSub (Cert.ivConst Cert.certScale) ⟨cs2.b.b0, cs2.b.b1⟩) 2)
        (Cert.ivDivPos (Cert.ivMul (Cert.ivSq ⟨cs2.b.o20, cs2.b.o21⟩) cs3.vy) cs3.dIv) := by
    rw [hd_eq, hvx_eq, hvy_eq, ← hcs3]
  obtain ⟨_, _, _, _, _, _, _, hwu_sq, hwv_sq, hwuv, _⟩ := pair_orth_residuals hadm.1 hD_pos
  set vx := (1 + pairSab u) / 2
  set vy := (1 + pairScd u) / 2
  set rb := pairRb u
  set D := vx * vy - rb ^ 2
  set K00 := (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D
  set K11 := (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D
  set K01 := pairTau u + pairO1 u * pairO2 u * rb / D
  have hk00_m : MemI K00 cs3.k00 := hk00_eq ▸ memI_sub hh1a_m hq1_m
  have hk11_m : MemI K11 cs3.k11 := hk11_eq ▸ memI_sub hh1b_m hq2_m
  have hK00_nn : 0 ≤ K00 := by rw [← hwu_sq]; exact sq_nonneg _
  have hK11_nn : 0 ≤ K11 := by rw [← hwv_sq]; exact sq_nonneg _
  have hK01_abs : |K01| ≤ (K00 + K11) / 2 := by
    rw [← hwuv, ← hwu_sq, ← hwv_sq]
    have hcs := abs_real_inner_le_norm ((1 / 2 : ℝ) • (u 0 - u 1) +
        (pairO1 u / D * rb) • ((1 / 2 : ℝ) • (u 0 + u 1)) -
        (pairO1 u / D * vx) • ((1 / 2 : ℝ) • (u 2 + u 3)))
      ((1 / 2 : ℝ) • (u 2 - u 3) -
        (pairO2 u / D * vy) • ((1 / 2 : ℝ) • (u 0 + u 1)) +
        (pairO2 u / D * rb) • ((1 / 2 : ℝ) • (u 2 + u 3)))
    have hsq := sq_nonneg (‖(1 / 2 : ℝ) • (u 0 - u 1) +
        (pairO1 u / D * rb) • ((1 / 2 : ℝ) • (u 0 + u 1)) -
        (pairO1 u / D * vx) • ((1 / 2 : ℝ) • (u 2 + u 3))‖ -
      ‖(1 / 2 : ℝ) • (u 2 - u 3) -
        (pairO2 u / D * vy) • ((1 / 2 : ℝ) • (u 0 + u 1)) +
        (pairO2 u / D * rb) • ((1 / 2 : ℝ) • (u 2 + u 3))‖)
    nlinarith only [hcs, hsq]
  unfold Cert.clampStep4 at h4
  dsimp only at h4
  by_cases hneg_k : (Cert.iblt cs3.k00.hi 0 || Cert.iblt cs3.k11.hi 0) = true
  · rw [Bool.or_eq_true, iblt_iff, iblt_iff] at hneg_k
    rcases hneg_k with hk0 | hk1
    · exfalso; linarith only [hK00_nn, hk00_m.2, valI_neg hk0]
    · exfalso; linarith only [hK11_nn, hk11_m.2, valI_neg hk1]
  · rw [if_false_eq (Bool.eq_false_iff.mpr hneg_k)] at h4
    simp only [bindIval_eq, bindInt_eq, imin_eq, imax_eq] at h4
    injection h4 with hb4; subst hb4
    set sKK := Cert.cdiv (cs3.k00.hi + cs3.k11.hi) 2
    set prod := Cert.ivDivPos (Cert.ivMul
      (Cert.ivMul ⟨cs2.b.o10, cs2.b.o11⟩ ⟨cs2.b.o20, cs2.b.o21⟩)
      ⟨cs2.b.r0, cs2.b.r1⟩) cs3.dIv
    set uqIv := Cert.ivDivInt (Cert.ivAdd
      (Cert.ivDivPos (Cert.ivMul (Cert.ivSq ⟨cs2.b.o10, cs2.b.o11⟩) cs3.vx) cs3.dIv)
      (Cert.ivDivPos (Cert.ivMul (Cert.ivSq ⟨cs2.b.o20, cs2.b.o21⟩) cs3.vy) cs3.dIv)) 2
    set gramC := Cert.certScale / 2 - uqIv.lo
    have hprod_m : MemI (pairO1 u * pairO2 u * rb / D) prod :=
      memI_divPos (memI_mul (memI_mul ho1 ho2) hr) hd_m hdl_pos
    have hsKK_le : (K00 + K11) / 2 ≤ valI sKK := by
      have hk0_hi := hk00_m.2; have hk1_hi := hk11_m.2
      refine (show (K00 + K11) / 2 ≤ valI (cs3.k00.hi + cs3.k11.hi) / (2 : Int) by
        unfold valI at hk0_hi hk1_hi ⊢; push_cast; linarith).trans
        (valI_cdiv_ge _ 2 (by norm_num))
    have ht1c_ge : pairTau u ≤ valI (sKK - prod.lo) := by
      have habs := (abs_le.mp hK01_abs).2
      have hv : valI (sKK - prod.lo) = valI sKK - valI prod.lo := by
        unfold valI; push_cast; ring
      rw [hv]; dsimp only [K01] at habs; linarith [hprod_m.1]
    have ht0c_le : valI (-sKK - prod.hi) ≤ pairTau u := by
      have habs := (abs_le.mp hK01_abs).1
      have hv : valI (-sKK - prod.hi) = -valI sKK - valI prod.hi := by
        unfold valI; push_cast; ring
      rw [hv]; dsimp only [K01] at habs; linarith [hprod_m.2]
    have huq_m : MemI ((pairO1 u ^ 2 * vx / D + pairO2 u ^ 2 * vy / D) / 2) uqIv :=
      memI_divTwo (memI_add hq1_m hq2_m)
    have hgram_id : (K00 + K11) / 2 =
        1 / 2 - (pairSab u + pairScd u) / 4 -
          (pairO1 u ^ 2 * vx / D + pairO2 u ^ 2 * vy / D) / 2 := by
      dsimp only [K00, K11]; ring
    have hgramc_eq : valI gramC = 1 / 2 - valI uqIv.lo := by
      dsimp only [gramC]; unfold valI Cert.certScale; push_cast; ring
    have hr1_le : 3 / 7 * pairRb u ≤ valI (Cert.cdiv (3 * b1.r1) 7) := by
      have hmr := hm1.2.2.1.2
      calc 3 / 7 * pairRb u
          ≤ valI (3 * b1.r1) / (7 : Int) := by
            unfold valI at hmr ⊢; push_cast; linarith
        _ ≤ valI (Cert.cdiv (3 * b1.r1) 7) := valI_cdiv_ge _ 7 (by norm_num)
    have hc2_eq : valI Cert.c2I = 1322905 / 1000000 := by unfold valI Cert.c2I; norm_num
    refine ⟨ha, hb, hr, ho1, ho2, ?_⟩
    dsimp only [MemI]
    constructor
    · have ht0c_ok : valI (max cs2.b.t0 (-sKK - prod.hi)) ≤ pairTau u := by
        rcases le_total cs2.b.t0 (-sKK - prod.hi) with h | h
        · rw [max_eq_right h]; exact ht0c_le
        · rw [max_eq_left h]; exact ht.1
      split_ifs with hp
      · rw [ible_iff, hcs2.2.1] at hp
        have hsch := calcSchurRhsHi_sound hadm hm1 (Or.inl rfl) hp
        have habs := (abs_le.mp hK01_abs).1
        dsimp only [K01] at habs
        have hcomb : -pairTau u ≤
            valI (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srP)) / (86 : Int) +
            valI (35 * (gramC + prod.hi)) / (43 : Int) := by
          have v1 : valI (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srP)) =
              35 * (valI (Cert.cdiv (3 * b1.r1) 7) - valI Cert.c2I + valI cs2.srP) := by
            unfold valI; push_cast; ring
          have v2 : valI (35 * (gramC + prod.hi)) = 35 * (valI gramC + valI prod.hi) := by
            unfold valI; push_cast; ring
          rw [v1, v2, hgramc_eq, hc2_eq, hcs2.2.1]
          push_cast at hsch ⊢
          linarith [huq_m.1, hprod_m.2]
        have hcdiv1 := valI_cdiv_ge
          (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srP)) 86 (by norm_num)
        have hcdiv2 := valI_cdiv_ge (35 * (gramC + prod.hi)) 43 (by norm_num)
        have hlo_comb : valI (-Cert.cdiv (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srP)) 86 -
            Cert.cdiv (35 * (gramC + prod.hi)) 43) ≤ pairTau u := by
          have hv : valI (-Cert.cdiv (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srP)) 86 -
              Cert.cdiv (35 * (gramC + prod.hi)) 43) =
              -valI (Cert.cdiv (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srP)) 86) -
              valI (Cert.cdiv (35 * (gramC + prod.hi)) 43) := by
            unfold valI; push_cast; ring
          rw [hv]; linarith
        rcases le_total (max cs2.b.t0 (-sKK - prod.hi))
            (-Cert.cdiv (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srP)) 86 -
              Cert.cdiv (35 * (gramC + prod.hi)) 43) with h | h
        · rw [max_eq_right h]; exact hlo_comb
        · rw [max_eq_left h]; exact ht0c_ok
      · exact ht0c_ok
    · have ht1c_ok : pairTau u ≤ valI (min cs2.b.t1 (sKK - prod.lo)) := by
        rcases le_total cs2.b.t1 (sKK - prod.lo) with h | h
        · rw [min_eq_left h]; exact ht.2
        · rw [min_eq_right h]; exact ht1c_ge
      split_ifs with hm
      · rw [ible_iff, hcs2.1] at hm
        have hsch := calcSchurRhsHi_sound hadm hm1 (Or.inr rfl) hm
        have habs := (abs_le.mp hK01_abs).2
        dsimp only [K01] at habs
        have hcomb : pairTau u ≤
            valI (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srM)) / (86 : Int) +
            valI (35 * (gramC - prod.lo)) / (43 : Int) := by
          have v1 : valI (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srM)) =
              35 * (valI (Cert.cdiv (3 * b1.r1) 7) - valI Cert.c2I + valI cs2.srM) := by
            unfold valI; push_cast; ring
          have v2 : valI (35 * (gramC - prod.lo)) = 35 * (valI gramC - valI prod.lo) := by
            unfold valI; push_cast; ring
          rw [v1, v2, hgramc_eq, hc2_eq, hcs2.1]
          push_cast at hsch ⊢
          linarith [huq_m.1, hprod_m.1]
        have hcdiv1 := valI_cdiv_ge
          (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srM)) 86 (by norm_num)
        have hcdiv2 := valI_cdiv_ge (35 * (gramC - prod.lo)) 43 (by norm_num)
        have hhi_comb : pairTau u ≤
            valI (Cert.cdiv (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srM)) 86 +
              Cert.cdiv (35 * (gramC - prod.lo)) 43) := by
          have hv : valI (Cert.cdiv (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srM)) 86 +
              Cert.cdiv (35 * (gramC - prod.lo)) 43) =
              valI (Cert.cdiv (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srM)) 86) +
              valI (Cert.cdiv (35 * (gramC - prod.lo)) 43) := by
            unfold valI; push_cast; ring
          rw [hv]; linarith
        rcases le_total (min cs2.b.t1 (sKK - prod.lo))
            (Cert.cdiv (35 * (Cert.cdiv (3 * b1.r1) 7 - Cert.c2I + cs2.srM)) 86 +
              Cert.cdiv (35 * (gramC - prod.lo)) 43) with h | h
        · rw [min_eq_left h]; exact ht1c_ok
        · rw [min_eq_right h]; exact hhi_comb
      · exact ht1c_ok

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem clampBox_sound {b0 b : Cert.BoxI} (hcl : Cert.clampBox b0 = some b)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u)
    (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u) (hm : MemBox u b0) :
    MemBox u b := by
  unfold Cert.clampBox at hcl
  rw [evalBox_eq] at hcl
  dsimp only at hcl
  cases h1 : Cert.clampStep1 b0 with
  | none => rw [h1] at hcl; cases hcl
  | some b1 =>
    rw [h1] at hcl; dsimp only at hcl
    have hm1 := clampStep1_sound h1 hadm ho1 ho12 hm
    split_ifs at hcl with hemp
    · injection hcl with hb; exact hb ▸ hm1
    · cases h2 : Cert.clampStep2 b1 with
      | none => rw [h2] at hcl; cases hcl
      | some cs2 =>
        rw [h2] at hcl; dsimp only at hcl
        obtain ⟨hm2, hsrM, hsrP, _, _, _, _, _, hr1_eq, _, _, _, _⟩ :=
          clampStep2_sound h2 hadm hm1
        split_ifs at hcl with htem
        · injection hcl with hb; exact hb ▸ hm2
        · cases h3 : Cert.clampStep3 cs2.b with
          | none => rw [h3] at hcl; injection hcl with hb; exact hb ▸ hm2
          | some cs3 =>
            rw [h3] at hcl
            exact clampStep34_sound ⟨hsrM, hsrP, hr1_eq⟩ h3 hcl hadm hm1 hm2

omit [BorelSpace E] in
private theorem chkSchur_sound {b : Cert.BoxI} {sigPos : Bool}
    (hok : Cert.chkSchur b sigPos = true) : BoxValid (E := E) b := by
  intro u hadm ho1 ho12 hm
  exfalso
  unfold Cert.chkSchur at hok
  simp only [bindIval_eq, Bool.and_eq_true, iblt_iff] at hok
  rcases hok with ⟨⟨hx1_pos, hx2_pos⟩, hlt⟩
  rcases hm with ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
  set sig : Int := if sigPos then 1 else -1
  have hsig : sig = 1 ∨ sig = -1 := by dsimp only [sig]; split_ifs <;> simp
  have hrb := admissiblePair_root_bounds hadm ho1 ho12
  have ha1_nn : 0 ≤ 1322905 / 1000000 - pairSab u := by linarith only [hrb.2.1]
  have ha2_pos : 0 < 1322905 / 1000000 + pairSab u := by linarith only [hrb.1]
  have hc2_eq : valI Cert.c2I = 1322905 / 1000000 := by unfold valI Cert.c2I; norm_num
  have ha1_m : MemI (1322905 / 1000000 - pairSab u) ⟨Cert.c2I - b.a1, Cert.c2I - b.a0⟩ := by
    rw [← hc2_eq]; exact memI_sub (memI_const Cert.c2I) ha
  have hd1_m : MemI (1322905 / 1000000 - pairScd u) ⟨Cert.c2I - b.b1, Cert.c2I - b.b0⟩ := by
    rw [← hc2_eq]; exact memI_sub (memI_const Cert.c2I) hcd
  have ha2_m : MemI (1322905 / 1000000 + pairSab u) ⟨Cert.c2I + b.a0, Cert.c2I + b.a1⟩ := by
    rw [← hc2_eq]; exact memI_add (memI_const Cert.c2I) ha
  have hd2_m : MemI (1322905 / 1000000 + pairScd u) ⟨Cert.c2I + b.b0, Cert.c2I + b.b1⟩ := by
    rw [← hc2_eq]; exact memI_add (memI_const Cert.c2I) hcd
  have hm11_35 := memI_add (memI_scaleInt 15 hr) (memI_scaleInt (sig * 16) ht)
  have hm22_35 := memI_add (memI_scaleInt 15 ht) (memI_scaleInt (sig * 16) hr)
  have hm12_35 := memI_add (memI_scaleInt 15 h_o2) (memI_scaleInt (sig * 16) h_o1)
  have hm21_35 := memI_add (memI_scaleInt 15 h_o1) (memI_scaleInt (sig * 16) h_o2)
  have eq11 : 2 * (3 / 14 * pairRb u + (sig : ℝ) * (8 / 35) * pairTau u) =
      (15 * pairRb u + (sig * 16 : Int) * pairTau u) / (35 : Int) := by push_cast; ring
  have eq22 : 2 * (3 / 14 * pairTau u + (sig : ℝ) * (8 / 35) * pairRb u) =
      (15 * pairTau u + (sig * 16 : Int) * pairRb u) / (35 : Int) := by push_cast; ring
  have eq12 : 2 * (3 / 14 * pairO2 u + (sig : ℝ) * (8 / 35) * pairO1 u) =
      (15 * pairO2 u + (sig * 16 : Int) * pairO1 u) / (35 : Int) := by push_cast; ring
  have eq21 : 2 * (3 / 14 * pairO1 u + (sig : ℝ) * (8 / 35) * pairO2 u) =
      (15 * pairO1 u + (sig * 16 : Int) * pairO2 u) / (35 : Int) := by push_cast; ring
  have sq11 : (2 * (3 / 14 * pairRb u + (sig : ℝ) * (8 / 35) * pairTau u)) ^ 2 =
      ((15 : Int) * pairRb u + (sig * 16 : Int) * pairTau u) ^ 2 / (1225 : Int) := by
    rw [eq11]; push_cast; ring
  have sq22 : (2 * (3 / 14 * pairTau u + (sig : ℝ) * (8 / 35) * pairRb u)) ^ 2 =
      ((15 : Int) * pairTau u + (sig * 16 : Int) * pairRb u) ^ 2 / (1225 : Int) := by
    rw [eq22]; push_cast; ring
  have sq12 : (2 * (3 / 14 * pairO2 u + (sig : ℝ) * (8 / 35) * pairO1 u)) ^ 2 =
      ((15 : Int) * pairO2 u + (sig * 16 : Int) * pairO1 u) ^ 2 / (1225 : Int) := by
    rw [eq12]; push_cast; ring
  have sq21 : (2 * (3 / 14 * pairO1 u + (sig : ℝ) * (8 / 35) * pairO2 u)) ^ 2 =
      ((15 : Int) * pairO1 u + (sig * 16 : Int) * pairO2 u) ^ 2 / (1225 : Int) := by
    rw [eq21]; push_cast; ring
  have hx1_m := memI_sub
    (memI_mul ha2_m (memI_sub (memI_mul ha1_m hd1_m)
      (memI_divInt (k := 1225) (by norm_num) (memI_sq hm11_35))))
    (memI_mul ha1_m (memI_divInt (k := 1225) (by norm_num) (memI_sq hm21_35)))
  rw [← sq11, ← sq21] at hx1_m
  have hx2_m := memI_sub
    (memI_mul ha2_m (memI_sub (memI_mul ha1_m hd2_m)
      (memI_divInt (k := 1225) (by norm_num) (memI_sq hm12_35))))
    (memI_mul ha1_m (memI_divInt (k := 1225) (by norm_num) (memI_sq hm22_35)))
  rw [← sq12, ← sq22] at hx2_m
  have hy_eq : ((1322905 / 1000000 + pairSab u) *
        (|(15 : Int) * pairRb u + (sig * 16 : Int) * pairTau u| *
          |(15 : Int) * pairO2 u + (sig * 16 : Int) * pairO1 u|) +
      (1322905 / 1000000 - pairSab u) *
        (|(15 : Int) * pairO1 u + (sig * 16 : Int) * pairO2 u| *
          |(15 : Int) * pairTau u + (sig * 16 : Int) * pairRb u|)) / (1225 : Int) =
      (1322905 / 1000000 + pairSab u) *
        |2 * (3 / 14 * pairRb u + (sig : ℝ) * (8 / 35) * pairTau u)| *
        |2 * (3 / 14 * pairO2 u + (sig : ℝ) * (8 / 35) * pairO1 u)| +
      (1322905 / 1000000 - pairSab u) *
        |2 * (3 / 14 * pairO1 u + (sig : ℝ) * (8 / 35) * pairO2 u)| *
        |2 * (3 / 14 * pairTau u + (sig : ℝ) * (8 / 35) * pairRb u)| := by
    rw [eq11, eq12, eq21, eq22, abs_div, abs_div, abs_div, abs_div]
    push_cast; rw [abs_of_pos (by norm_num : (0 : ℝ) < 35)]; ring
  have hy_sum_m := memI_add
    (memI_mul ha2_m (memI_mul (memI_abs hm11_35) (memI_abs hm12_35)))
    (memI_mul ha1_m (memI_mul (memI_abs hm21_35) (memI_abs hm22_35)))
  have hy_m := memI_divInt (k := 1225) (by norm_num) hy_sum_m
  rw [hy_eq] at hy_m
  have hprod_lo := (memI_mul hx1_m hx2_m).1
  have hsq_y_hi := (memI_sq hy_m).2
  have hstrict := valI_lt hlt
  have hsch : schurPairIneq (pairSab u) (pairScd u) ⟪u 0, u 2⟫ ⟪u 1, u 3⟫
      ⟪u 0, u 3⟫ ⟪u 1, u 2⟫ (sig : ℝ) := by
    rcases hadm with ⟨_, _, _, _, _, _, _, hs1, hs2, _, _⟩
    rcases hsig with h1 | h1 <;> rw [h1]
    · simpa only [Int.cast_one, pairSab, pairScd] using hs1
    · simpa only [Int.cast_neg, Int.cast_one, pairSab, pairScd] using hs2
  set M11 := 2 * (3 / 14 * pairRb u + (sig : ℝ) * (8 / 35) * pairTau u)
  set M12 := 2 * (3 / 14 * pairO2 u + (sig : ℝ) * (8 / 35) * pairO1 u)
  set M21 := 2 * (3 / 14 * pairO1 u + (sig : ℝ) * (8 / 35) * pairO2 u)
  set M22 := 2 * (3 / 14 * pairTau u + (sig : ℝ) * (8 / 35) * pairRb u)
  set A1 := 1322905 / 1000000 - pairSab u
  set A2 := 1322905 / 1000000 + pairSab u
  have hsch' : (A2 * (A1 * (1322905 / 1000000 - pairScd u) - M11 ^ 2) - A1 * M21 ^ 2) *
      (A2 * (A1 * (1322905 / 1000000 + pairScd u) - M12 ^ 2) - A1 * M22 ^ 2) ≤
      (A2 * M11 * M12 + A1 * M21 * M22) ^ 2 := hsch
  have hy_le : (A2 * M11 * M12 + A1 * M21 * M22) ^ 2 ≤
      (A2 * |M11| * |M12| + A1 * |M21| * |M22|) ^ 2 := by
    rw [← sq_abs (A2 * M11 * M12 + A1 * M21 * M22)]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    calc |A2 * M11 * M12 + A1 * M21 * M22|
        ≤ |A2 * M11 * M12| + |A1 * M21 * M22| := abs_add_le _ _
      _ = A2 * |M11| * |M12| + A1 * |M21| * |M22| := by
          have h1 : |A2 * M11 * M12| = A2 * |M11| * |M12| := by
            rw [abs_mul, abs_mul, abs_of_pos ha2_pos]
          have h2 : |A1 * M21 * M22| = A1 * |M21| * |M22| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha1_nn]
          rw [h1, h2]
  exact not_lt_of_ge ((hprod_lo.trans hsch').trans (hy_le.trans hsq_y_hi)) hstrict

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem pair_gram_psd_bounds {u : Fin 4 → E} (hadm : IsAdmissiblePair u) :
    let vx := (1 + pairSab u) / 2
    let vy := (1 + pairScd u) / 2
    let rb := pairRb u
    let D := vx * vy - rb ^ 2
    0 ≤ D ∧
    pairO1 u ^ 2 * vx ≤ (1 - pairSab u) / 2 * D ∧
    pairO2 u ^ 2 * vy ≤ (1 - pairScd u) / 2 * D := by
  intro vx vy rb D
  rcases hadm with ⟨hu, hab, hcd, _⟩
  let p_x := (1 / 2 : ℝ) • (u 0 + u 1)
  let p_y := (1 / 2 : ℝ) • (u 2 + u 3)
  let d_x := (1 / 2 : ℝ) • (u 0 - u 1)
  let d_y := (1 / 2 : ℝ) • (u 2 - u 3)
  have hpx : ‖p_x‖ ^ 2 = vx := by
    dsimp only [p_x, vx, pairSab]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_add_sq_real, hu 0, hu 1]; ring
  have hpy : ‖p_y‖ ^ 2 = vy := by
    dsimp only [p_y, vy, pairScd]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_add_sq_real, hu 2, hu 3]; ring
  have hdx : ‖d_x‖ ^ 2 = (1 - pairSab u) / 2 := by
    dsimp only [d_x, pairSab]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_sq_real, hu 0, hu 1]; ring
  have hdy : ‖d_y‖ ^ 2 = (1 - pairScd u) / 2 := by
    dsimp only [d_y, pairScd]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_sq_real, hu 2, hu 3]; ring
  have hpxy : ⟪p_x, p_y⟫ = rb := by
    dsimp only [p_x, p_y, rb, pairRb]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right]; ring
  have hpd_xx : ⟪p_x, d_x⟫ = 0 := by
    dsimp only [p_x, d_x]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right,
      real_inner_self_eq_norm_sq, hu 0, hu 1, real_inner_comm (u 1) (u 0)]; ring
  have hpd_yy : ⟪p_y, d_y⟫ = 0 := by
    dsimp only [p_y, d_y]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right,
      real_inner_self_eq_norm_sq, hu 2, hu 3, real_inner_comm (u 3) (u 2)]; ring
  have hpd_yx : ⟪p_y, d_x⟫ = pairO1 u := by
    dsimp only [p_y, d_x, pairO1]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right,
      real_inner_comm (u 2), real_inner_comm (u 3)]; ring
  have hpd_xy : ⟪p_x, d_y⟫ = pairO2 u := by
    dsimp only [p_x, d_y, pairO2]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right]; ring
  have hD_nn : 0 ≤ D := by
    have hcs := abs_real_inner_le_norm p_x p_y
    have hsq : ⟪p_x, p_y⟫ ^ 2 ≤ ‖p_x‖ ^ 2 * ‖p_y‖ ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hcs 2
      rwa [sq_abs, mul_pow] at this
    rw [hpx, hpy, hpxy] at hsq
    dsimp only [D]; linarith
  have hvx_pos : 0 < vx := by dsimp only [vx, pairSab]; linarith
  have hvy_pos : 0 < vy := by dsimp only [vy, pairScd]; linarith
  let q₁ := vx • p_y - rb • p_x
  have hq1_sq : ‖q₁‖ ^ 2 = vx * D := by
    change ‖vx • p_y - rb • p_x‖ ^ 2 = vx * (vx * vy - rb ^ 2)
    rw [norm_sub_sq_real, norm_smul vx p_y, norm_smul rb p_x, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left p_y (rb • p_x) vx,
      real_inner_smul_right p_y p_x rb, hpx, hpy, real_inner_comm p_x p_y, hpxy]; ring
  have hq1_in : ⟪q₁, d_x⟫ = vx * pairO1 u := by
    change ⟪vx • p_y - rb • p_x, d_x⟫ = vx * pairO1 u
    rw [inner_sub_left, real_inner_smul_left p_y d_x vx, real_inner_smul_left p_x d_x rb,
      hpd_yx, hpd_xx]; ring
  have ho1_le : pairO1 u ^ 2 * vx ≤ (1 - pairSab u) / 2 * D := by
    have hcs := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm q₁ d_x) 2
    rw [sq_abs, mul_pow, hq1_in, hq1_sq, hdx] at hcs
    exact le_of_mul_le_mul_left (by linarith) hvx_pos
  let q₂ := vy • p_x - rb • p_y
  have hq2_sq : ‖q₂‖ ^ 2 = vy * D := by
    change ‖vy • p_x - rb • p_y‖ ^ 2 = vy * (vx * vy - rb ^ 2)
    rw [norm_sub_sq_real, norm_smul vy p_x, norm_smul rb p_y, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left p_x (rb • p_y) vy,
      real_inner_smul_right p_x p_y rb, hpx, hpy, hpxy]; ring
  have hq2_in : ⟪q₂, d_y⟫ = vy * pairO2 u := by
    change ⟪vy • p_x - rb • p_y, d_y⟫ = vy * pairO2 u
    rw [inner_sub_left, real_inner_smul_left p_x d_y vy, real_inner_smul_left p_y d_y rb,
      hpd_xy, hpd_yy]; ring
  have ho2_le : pairO2 u ^ 2 * vy ≤ (1 - pairScd u) / 2 * D := by
    have hcs := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm q₂ d_y) 2
    rw [sq_abs, mul_pow, hq2_in, hq2_sq, hdy] at hcs
    exact le_of_mul_le_mul_left (by linarith) hvy_pos
  exact ⟨hD_nn, ho1_le, ho2_le⟩

omit [BorelSpace E] in
private theorem chkGram_sound {b : Cert.BoxI} (hok : Cert.chkGram b = true) :
    BoxValid (E := E) b := by
  intro u hadm _ _ hm
  exfalso
  rcases hm with ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
  obtain ⟨hD_nn, ho1_le, ho2_le⟩ := pair_gram_psd_bounds hadm
  have h1_m : MemI 1 (Cert.ivConst Cert.certScale) := by
    have h1 : valI Cert.certScale = 1 := by unfold valI Cert.certScale; norm_num
    exact h1 ▸ memI_const Cert.certScale
  have hvx_m : MemI ((1 + pairSab u) / 2)
      (Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨b.a0, b.a1⟩) 2) :=
    memI_divTwo (memI_add h1_m ha)
  have hvy_m : MemI ((1 + pairScd u) / 2)
      (Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨b.b0, b.b1⟩) 2) :=
    memI_divTwo (memI_add h1_m hcd)
  have hd_m := memI_sub (memI_mul hvx_m hvy_m) (memI_sq hr)
  have hh1a_m : MemI ((1 - pairSab u) / 2)
      (Cert.ivDivInt (Cert.ivSub (Cert.ivConst Cert.certScale) ⟨b.a0, b.a1⟩) 2) :=
    memI_divTwo (memI_sub h1_m ha)
  have hh1b_m : MemI ((1 - pairScd u) / 2)
      (Cert.ivDivInt (Cert.ivSub (Cert.ivConst Cert.certScale) ⟨b.b0, b.b1⟩) 2) :=
    memI_divTwo (memI_sub h1_m hcd)
  unfold Cert.chkGram at hok
  simp only [bindIval_eq] at hok
  split_ifs at hok with c1 c2 c3 c4 c5
  · rw [iblt_iff] at c1
    linarith [hD_nn, hd_m.2, valI_neg c1]
  · rw [iblt_iff] at c2
    have hm_l := memI_mul hh1a_m hd_m
    have hm_r := memI_mul (memI_sq h_o1) hvx_m
    linarith [ho1_le, hm_l.2, hm_r.1, valI_lt c2]
  · rw [iblt_iff] at c3
    have hm_l := memI_mul hh1b_m hd_m
    have hm_r := memI_mul (memI_sq h_o2) hvy_m
    linarith [ho2_le, hm_l.2, hm_r.1, valI_lt c3]
  · rw [iblt_iff] at c4
    have hD_pos := lt_of_lt_of_le (valI_pos c4) hd_m.1
    obtain ⟨_, _, _, _, _, _, _, hwu_sq, hwv_sq, _, _⟩ := pair_orth_residuals hadm.1 hD_pos
    have hk00_m := memI_sub hh1a_m (memI_divPos (memI_mul (memI_sq h_o1) hvx_m) hd_m c4)
    have hk11_m := memI_sub hh1b_m (memI_divPos (memI_mul (memI_sq h_o2) hvy_m) hd_m c4)
    rw [Bool.or_eq_true, iblt_iff, iblt_iff] at c5
    rcases c5 with c5 | c5
    · linarith [hwu_sq ▸ sq_nonneg _, hk00_m.2, valI_neg c5]
    · linarith [hwv_sq ▸ sq_nonneg _, hk11_m.2, valI_neg c5]
  · rw [iblt_iff] at c4 hok
    have hD_pos := lt_of_lt_of_le (valI_pos c4) hd_m.1
    obtain ⟨_, _, _, _, _, _, _, hwu_sq, hwv_sq, hwuv, _⟩ := pair_orth_residuals hadm.1 hD_pos
    have hk00_m := memI_sub hh1a_m (memI_divPos (memI_mul (memI_sq h_o1) hvx_m) hd_m c4)
    have hk11_m := memI_sub hh1b_m (memI_divPos (memI_mul (memI_sq h_o2) hvy_m) hd_m c4)
    have hk01_m := memI_add ht (memI_divPos (memI_mul (memI_mul h_o1 h_o2) hr) hd_m c4)
    have hK00_nn : 0 ≤ (1 - pairSab u) / 2 -
        pairO1 u ^ 2 * ((1 + pairSab u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) :=
      hwu_sq ▸ sq_nonneg _
    have hK11_nn : 0 ≤ (1 - pairScd u) / 2 -
        pairO2 u ^ 2 * ((1 + pairScd u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) :=
      hwv_sq ▸ sq_nonneg _
    set k00_iv := Cert.ivSub
      (Cert.ivDivInt (Cert.ivSub (Cert.ivConst Cert.certScale) ⟨b.a0, b.a1⟩) 2)
      (Cert.ivDivPos (Cert.ivMul (Cert.ivSq ⟨b.o10, b.o11⟩)
        (Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨b.a0, b.a1⟩) 2))
        (Cert.ivSub (Cert.ivMul
          (Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨b.a0, b.a1⟩) 2)
          (Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨b.b0, b.b1⟩) 2))
          (Cert.ivSq ⟨b.r0, b.r1⟩)))
    set k11_iv := Cert.ivSub
      (Cert.ivDivInt (Cert.ivSub (Cert.ivConst Cert.certScale) ⟨b.b0, b.b1⟩) 2)
      (Cert.ivDivPos (Cert.ivMul (Cert.ivSq ⟨b.o20, b.o21⟩)
        (Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨b.b0, b.b1⟩) 2))
        (Cert.ivSub (Cert.ivMul
          (Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨b.a0, b.a1⟩) 2)
          (Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨b.b0, b.b1⟩) 2))
          (Cert.ivSq ⟨b.r0, b.r1⟩)))
    have hk00_pos : MemI ((1 - pairSab u) / 2 -
        pairO1 u ^ 2 * ((1 + pairSab u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2))
        ⟨Cert.imax 0 k00_iv.lo, k00_iv.hi⟩ := by
      rw [imax_eq]
      refine ⟨?_, hk00_m.2⟩
      rcases le_total 0 k00_iv.lo with h | h
      · rw [max_eq_right h]; exact hk00_m.1
      · rw [max_eq_left h]; unfold valI; simp only [Int.cast_zero, zero_div]; exact hK00_nn
    have hk11_pos : MemI ((1 - pairScd u) / 2 -
        pairO2 u ^ 2 * ((1 + pairScd u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2))
        ⟨Cert.imax 0 k11_iv.lo, k11_iv.hi⟩ := by
      rw [imax_eq]
      refine ⟨?_, hk11_m.2⟩
      rcases le_total 0 k11_iv.lo with h | h
      · rw [max_eq_right h]; exact hk11_m.1
      · rw [max_eq_left h]; unfold valI; simp only [Int.cast_zero, zero_div]; exact hK11_nn
    have hprod_m := memI_mul hk00_pos hk11_pos
    have hsq_m := memI_sq hk01_m
    have hcs := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm
      ((1 / 2 : ℝ) • (u 0 - u 1) +
        (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) •
          ((1 / 2 : ℝ) • (u 0 + u 1)) -
        (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
          ((1 + pairSab u) / 2)) • ((1 / 2 : ℝ) • (u 2 + u 3)))
      ((1 / 2 : ℝ) • (u 2 - u 3) -
        (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
          ((1 + pairScd u) / 2)) • ((1 / 2 : ℝ) • (u 0 + u 1)) +
        (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) •
          ((1 / 2 : ℝ) • (u 2 + u 3)))) 2
    rw [sq_abs, mul_pow, hwuv, hwu_sq, hwv_sq] at hcs
    exact not_lt_of_ge ((hsq_m.1.trans hcs).trans hprod_m.2) (valI_lt hok)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem cross_slos_le {u : Fin 4 → E} {b : Cert.BoxI}
    (hadm : IsAdmissiblePair u) (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u)
    (hm : MemBox u b) :
    let dlo := Cert.imax 0 (b.o20 - b.o11)
    let s0 := Cert.imin Cert.certScale (Cert.imax Cert.cminI (b.r0 + b.o10 + b.o20 + b.t0))
    let s1 := Cert.imin Cert.certScale (Cert.imax Cert.cminI (b.r0 - b.o11 - b.o21 + b.t0))
    let s2 := Cert.imin Cert.certScale (Cert.imax Cert.cminI (b.r0 - (b.o21 - b.o10) - b.t1))
    let s3 := Cert.imin Cert.certScale (Cert.imax Cert.cminI (b.r0 + dlo - b.t1))
    valI s0 ≤ ⟪u 0, u 2⟫ ∧ ⟪u 0, u 2⟫ ≤ 1 ∧ s0 ≤ Cert.certScale ∧
    valI s1 ≤ ⟪u 1, u 3⟫ ∧ ⟪u 1, u 3⟫ ≤ 1 ∧ s1 ≤ Cert.certScale ∧
    valI s2 ≤ ⟪u 0, u 3⟫ ∧ ⟪u 0, u 3⟫ ≤ 1 ∧ s2 ≤ Cert.certScale ∧
    valI s3 ≤ ⟪u 1, u 2⟫ ∧ ⟪u 1, u 2⟫ ≤ 1 ∧ s3 ≤ Cert.certScale := by
  intro dlo s0 s1 s2 s3
  rcases hm with ⟨_, _, hr, h_o1, h_o2, ht⟩
  unfold MemI valI at hr h_o1 h_o2 ht
  dsimp only at hr h_o1 h_o2 ht
  have hrb := admissiblePair_root_bounds hadm ho1 ho12
  have hcmin : valI Cert.cminI = 79998000 / 100000000 := by unfold valI Cert.cminI; norm_num
  have hscale : valI Cert.certScale = 1 := by unfold valI Cert.certScale; norm_num
  have hdlo_le : valI dlo ≤ pairO2 u - pairO1 u := by
    dsimp only [dlo]; rw [imax_eq]
    rcases le_total 0 (b.o20 - b.o11) with h | h
    · rw [max_eq_right h]; unfold valI; push_cast; linarith [h_o1.2, h_o2.1]
    · rw [max_eq_left h]; unfold valI; simp only [Int.cast_zero, zero_div]; linarith
  have clamp_le (x : ℝ) (raw : Int) (hlo1 : 79998000 / 100000000 ≤ x) (hhi : x ≤ 1)
      (hlo2 : valI raw ≤ x) :
      valI (Cert.imin Cert.certScale (Cert.imax Cert.cminI raw)) ≤ x ∧
      x ≤ 1 ∧ Cert.imin Cert.certScale (Cert.imax Cert.cminI raw) ≤ Cert.certScale := by
    rw [imin_eq, imax_eq]
    refine ⟨?_, hhi, min_le_left _ _⟩
    have hm_le : valI (max Cert.cminI raw) ≤ x := by
      rcases le_total Cert.cminI raw with h | h
      · rw [max_eq_right h]; exact hlo2
      · rw [max_eq_left h]; rwa [hcmin]
    exact (valI_mono (min_le_right _ _)).trans hm_le
  have c0 := clamp_le ⟪u 0, u 2⟫ (b.r0 + b.o10 + b.o20 + b.t0)
    hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by unfold valI; push_cast; linarith [hrb.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.1, h_o1.1, h_o2.1,
      ht.1])
  have c1 := clamp_le ⟪u 1, u 3⟫ (b.r0 - b.o11 - b.o21 + b.t0)
    hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by unfold valI; push_cast; linarith [hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.1, h_o1.2, h_o2.2,
      ht.1])
  have c2 := clamp_le ⟪u 0, u 3⟫ (b.r0 - (b.o21 - b.o10) - b.t1)
    hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by unfold valI; push_cast; linarith [hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.1, h_o1.1, h_o2.2,
      ht.2])
  have c3 := clamp_le ⟪u 1, u 2⟫ (b.r0 + dlo - b.t1)
    hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    (by
      have hv : valI (b.r0 + dlo - b.t1) = valI b.r0 + valI dlo - valI b.t1 := by
        unfold valI; push_cast; ring
      rw [hv]
      have hr0_le : valI b.r0 ≤ pairRb u := by unfold valI; exact hr.1
      have ht1_ge : pairTau u ≤ valI b.t1 := by unfold valI; exact ht.2
      linarith [hrb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])
  exact ⟨c0.1, c0.2.1, c0.2.2, c1.1, c1.2.1, c1.2.2, c2.1, c2.2.1, c2.2.2,
    c3.1, c3.2.1, c3.2.2⟩

private theorem chkShep_sound {b : Cert.BoxI} {mode ia ib ic0 ic1 ic2 ic3 : Nat}
    (hok : Cert.chkShep b mode ia ib ic0 ic1 ic2 ic3 = true) :
    BoxValid (E := E) b := by
  intro u hadm ho1 ho12 hm
  unfold Cert.chkShep at hok
  cases hqa : Cert.starQI ia with
  | none => rw [hqa] at hok; cases hok
  | some qa =>
  cases hqb : Cert.starQI ib with
  | none => rw [hqa, hqb] at hok; cases hok
  | some qb =>
  cases hqc0 : Cert.crossQI ic0 with
  | none => rw [hqa, hqb, hqc0] at hok; cases hok
  | some qc0 =>
  cases hqc1 : Cert.crossQI ic1 with
  | none => rw [hqa, hqb, hqc0, hqc1] at hok; cases hok
  | some qc1 =>
  cases hqc2 : Cert.crossQI ic2 with
  | none => rw [hqa, hqb, hqc0, hqc1, hqc2] at hok; cases hok
  | some qc2 =>
  cases hqc3 : Cert.crossQI ic3 with
  | none => rw [hqa, hqb, hqc0, hqc1, hqc2, hqc3] at hok; cases hok
  | some qc3 =>
    rw [hqa, hqb, hqc0, hqc1, hqc2, hqc3] at hok
    dsimp only at hok
    cases hsp : Cert.shepPre b qa qb qc0 qc1 qc2 qc3 with
    | none => rw [hsp] at hok; cases hok
    | some sp =>
      rw [hsp] at hok
      dsimp only at hok
      simp only [bindInt_eq] at hok
      unfold Cert.shepPre at hsp
      simp only [bindIval_eq, bindInt_eq] at hsp
      split_ifs at hsp with g1 g2 g3
      injection hsp with hsp_eq; subst hsp_eq
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, iblt_false_iff] at g1 g2 g3
      rcases hm with ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
      have hrb := admissiblePair_root_bounds hadm ho1 ho12
      have hcs := cross_slos_le hadm ho1 ho12 ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
      have star_bound (ix : Nat) (q : Cert.QuadI) (hq : Cert.starQI ix = some q)
          (s_lo : Int) (r : ℝ) (hr_min : q.rmin ≤ s_lo)
          (hsl : 0 ≤ (Cert.ivQslope q (Cert.ivConst s_lo)).lo)
          (hlo : valI s_lo ≤ r) (hhi : r ≤ 1) :
          arccos r ≤ valI (Cert.ivQeval q (Cert.ivConst s_lo)).hi := by
        obtain ⟨hc2, harc⟩ := arccos_le_starQI hq ((valI_mono hr_min).trans hlo) hhi
        have hsl_r : 0 ≤ quadSlope q (valI s_lo) :=
          (valI_nonneg hsl).trans (memI_qslope q (memI_const s_lo)).1
        exact (harc.trans (quadEval_anti_on hc2 hsl_r hlo)).trans
          (memI_qeval q (memI_const s_lo)).2
      have cross_bound (ix : Nat) (q : Cert.QuadI) (hq : Cert.crossQI ix = some q)
          (s_lo : Int) (r : ℝ) (hr_min : q.rmin ≤ s_lo)
          (hsl : 0 ≤ (Cert.ivQslope q (Cert.ivConst s_lo)).lo)
          (hlo : valI s_lo ≤ r) (hhi : r ≤ 1) :
          arccos r ≤ valI (Cert.ivQeval q (Cert.ivConst s_lo)).hi := by
        obtain ⟨hc2, harc⟩ := arccos_le_crossQI hq ((valI_mono hr_min).trans hlo) hhi
        have hsl_r : 0 ≤ quadSlope q (valI s_lo) :=
          (valI_nonneg hsl).trans (memI_qslope q (memI_const s_lo)).1
        exact (harc.trans (quadEval_anti_on hc2 hsl_r hlo)).trans
          (memI_qeval q (memI_const s_lo)).2
      have hva := star_bound ia qa hqa b.a0 ⟪u 0, u 1⟫ g1.1 g2.1 ha.1 hrb.2.1
      have hvb := star_bound ib qb hqb b.b0 ⟪u 2, u 3⟫ g1.2 g2.2 hcd.1 hrb.2.2.2.1
      have hvc0 := cross_bound ic0 qc0 hqc0 _ ⟪u 0, u 2⟫ g3.1.1.1.1.1.1.1 g3.1.1.1.1.1.1.2
        hcs.1 hcs.2.1
      have hvc1 := cross_bound ic1 qc1 hqc1 _ ⟪u 1, u 3⟫ g3.1.1.1.1.1.2 g3.1.1.1.1.2
        hcs.2.2.2.1 hcs.2.2.2.2.1
      have hvc2 := cross_bound ic2 qc2 hqc2 _ ⟪u 0, u 3⟫ g3.1.1.1.2 g3.1.1.2
        hcs.2.2.2.2.2.2.1 hcs.2.2.2.2.2.2.2.1
      have hvc3 := cross_bound ic3 qc3 hqc3 _ ⟪u 1, u 2⟫ g3.1.2 g3.2
        hcs.2.2.2.2.2.2.2.2.2.1 hcs.2.2.2.2.2.2.2.2.2.2.1
      have hmodes := pairCost_zero_le_shep_mode hadm.1 hva hvb hvc0 hvc1 hvc2 hvc3
      have finish_lhs (lhs : Int) (hpc : pairCost u 0 ≤ valI lhs / (4 * π))
          (htgt : Cert.ible (Cert.ivDivPos (Cert.ivConst lhs)
            (Cert.ivScaleInt 4 Cert.ivPi)).hi Cert.targetI = true) :
          pairCost u 0 ≤ 27735 / 100000 := by
        rw [ible_iff] at htgt
        have h4pi_pos : 0 < (Cert.ivScaleInt 4 Cert.ivPi).lo := by decide
        have hdiv := memI_divPos (memI_const lhs) (memI_scaleNat 4 memI_pi) h4pi_pos
        have htgt_eq : valI Cert.targetI = 27735 / 100000 := by
          unfold valI Cert.targetI; norm_num
        exact (hpc.trans hdiv.2).trans ((valI_mono htgt).trans_eq htgt_eq)
      match mode with
      | 0 =>
        dsimp only at hok
        split_ifs at hok with hm0
        simp only [bindIval_eq] at hok
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, iblt_false_iff] at hm0
        set s0 := Cert.imin Cert.certScale (Cert.imax Cert.cminI (b.r0 + b.o10 + b.o20 + b.t0))
        set s1 := Cert.imin Cert.certScale (Cert.imax Cert.cminI (b.r0 - b.o11 - b.o21 + b.t0))
        set s2 := Cert.imin Cert.certScale (Cert.imax Cert.cminI (b.r0 - (b.o21 - b.o10) - b.t1))
        set s3 := Cert.imin Cert.certScale
          (Cert.imax Cert.cminI (b.r0 + Cert.imax 0 (b.o20 - b.o11) - b.t1))
        have hmin4 : qc0.rmin ≤ min (min s0 s1) (min s2 s3) := by
          simpa only [imin_eq s0 s1, imin_eq s2 s3, imin_eq (min s0 s1) (min s2 s3)] using hm0.1.1
        have hm0_0 : qc0.rmin ≤ s0 := hmin4.trans ((min_le_left _ _).trans (min_le_left _ _))
        have hm0_1 : qc0.rmin ≤ s1 := hmin4.trans ((min_le_left _ _).trans (min_le_right _ _))
        have hm0_2 : qc0.rmin ≤ s2 := hmin4.trans ((min_le_right _ _).trans (min_le_left _ _))
        have hm0_3 : qc0.rmin ≤ s3 := hmin4.trans ((min_le_right _ _).trans (min_le_right _ _))
        have aq0 := (arccos_le_crossQI hqc0 ((valI_mono hm0_0).trans hcs.1) hcs.2.1).2
        have aq1 := (arccos_le_crossQI hqc0 ((valI_mono hm0_1).trans hcs.2.2.2.1)
          hcs.2.2.2.2.1).2
        have aq2 := (arccos_le_crossQI hqc0 ((valI_mono hm0_2).trans hcs.2.2.2.2.2.2.1)
          hcs.2.2.2.2.2.2.2.1).2
        have aq3 := (arccos_le_crossQI hqc0 ((valI_mono hm0_3).trans hcs.2.2.2.2.2.2.2.2.2.1)
          hcs.2.2.2.2.2.2.2.2.2.2.1).2
        have hc2_nn := (arccos_le_crossQI hqc0 ((valI_mono hm0_0).trans hcs.1) hcs.2.1).1
        have hhad := pairCost_zero_le_hadamard hadm.1 hva hvb qc0 aq0 aq1 aq2 aq3
        have hsl_r0 : 0 ≤ quadSlope qc0 (valI b.r0) :=
          (valI_nonneg hm0.2).trans (memI_qslope qc0 (memI_const b.r0)).1
        have hqe_le := quadEval_anti_on hc2_nn hsl_r0 hr.1
        have hvar_m := memI_add (memI_add (memI_sq h_o1) (memI_sq h_o2)) (memI_sq ht)
        have hhad_m := memI_scaleNat 4 (memI_sub (memI_qeval qc0 (memI_const b.r0))
          (memI_mul (memI_const qc0.c2) hvar_m))
        refine finish_lhs _ (hhad.trans (div_le_div_of_nonneg_right ?_
          (by have := pi_pos; positivity))) hok
        have hv_lin (x y z : Int) : valI (3 * (x + y) + z) = 3 * (valI x + valI y) + valI z := by
          unfold valI; push_cast; ring
        rw [hv_lin]
        have hqc2_eq : (qc0.c2 : ℝ) / 100000000 = valI qc0.c2 := rfl
        have h4_le : 4 * (quadEval qc0 (pairRb u) -
            (qc0.c2 : ℝ) / 100000000 * (pairO1 u ^ 2 + pairO2 u ^ 2 + pairTau u ^ 2)) ≤
            4 * (quadEval qc0 (valI b.r0) -
              valI qc0.c2 * (pairO1 u ^ 2 + pairO2 u ^ 2 + pairTau u ^ 2)) := by
          rw [hqc2_eq]; exact mul_le_mul_of_nonneg_left (sub_le_sub_right hqe_le _) (by norm_num)
        exact add_le_add le_rfl (h4_le.trans hhad_m.2)
      | 1 =>
        exact finish_lhs _ (hmodes.1.trans_eq (by unfold valI; push_cast; ring)) hok
      | 2 =>
        exact finish_lhs _ (hmodes.2.1.trans_eq (by unfold valI; push_cast; ring)) hok
      | 3 =>
        exact finish_lhs _ (hmodes.2.2.1.trans_eq (by unfold valI; push_cast; ring)) hok
      | 4 =>
        exact finish_lhs _ (hmodes.2.2.2.1.trans_eq (by unfold valI; push_cast; ring)) hok
      | 5 =>
        exact finish_lhs _ (hmodes.2.2.2.2.1.trans_eq (by unfold valI; push_cast; ring)) hok
      | 6 =>
        exact finish_lhs _ (hmodes.2.2.2.2.2.1.trans_eq (by unfold valI; push_cast; ring)) hok
      | 7 =>
        exact finish_lhs _ (hmodes.2.2.2.2.2.2.1.trans_eq (by unfold valI; push_cast; ring)) hok
      | 8 =>
        exact finish_lhs _ (hmodes.2.2.2.2.2.2.2.1.trans_eq (by unfold valI; push_cast; ring)) hok
      | 9 =>
        exact finish_lhs _ (hmodes.2.2.2.2.2.2.2.2.1.trans_eq
          (by unfold valI; push_cast; ring)) hok
      | 10 =>
        exact finish_lhs _ (hmodes.2.2.2.2.2.2.2.2.2.1.trans_eq
          (by unfold valI; push_cast; ring)) hok
      | 11 =>
        exact finish_lhs _ (hmodes.2.2.2.2.2.2.2.2.2.2.trans_eq
          (by unfold valI; push_cast; ring)) hok
      | n + 12 => cases hok

/-! ### Part 3: Soundness of `chkPlanar` stages -/

private theorem checkCexOk_sound {st : Cert.PlanarStep} {absK01 kk : Cert.Ival}
    {K00 K11 K01 : ℝ}
    (hcex_nn : 0 ≤ valI st.cex)
    (habs : MemI |K01| absK01) (hkk : MemI (K00 * K11) kk)
    (hok : Cert.checkCexOk st absK01 kk = true) :
    ∀ w_u w_v : E, ‖w_u‖ ^ 2 = K00 → ‖w_v‖ ^ 2 = K11 → ⟪w_u, w_v⟫ = K01 →
      ∫ x, |⟪w_u, x⟫| * |⟪w_v, x⟫| ∂stdGaussian E ≤
        valI st.cex * √(‖w_u‖ ^ 2 * ‖w_v‖ ^ 2) := by
  intro w_u w_v hwu hwv hwuv
  unfold Cert.checkCexOk at hok
  match hc : st.cexMode with
  | 0 =>
    rw [hc] at hok
    change Cert.ible Cert.certScale st.cex = true at hok
    rw [ible_iff] at hok
    have h1 : (1 : ℝ) ≤ valI st.cex := by
      simpa only [valI, Cert.certScale, Int.cast_ofNat,
        div_self (by norm_num : (100000000 : ℝ) ≠ 0)] using valI_mono hok
    exact (integral_abs_mul_abs_le_sqrt_prod w_u w_v).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1 (sqrt_nonneg _))
  | 1 =>
    rw [hc] at hok; dsimp only at hok
    simp only [bindIval_eq] at hok
    split_ifs at hok with hdet_le
    rw [Bool.not_eq_true, ible_false_iff] at hdet_le
    rw [ible_iff] at hok
    have hsq_k01 : K01 ^ 2 ≤ valI (Cert.ivSq absK01).hi := by
      rw [← sq_abs K01]; exact (memI_sq habs).2
    have hB_nn : 0 ≤ valI (Cert.ivSq absK01).hi := (sq_nonneg K01).trans hsq_k01
    set A := valI kk.lo
    set B := valI (Cert.ivSq absK01).hi
    have hdet_m := memI_sub (memI_const kk.lo) (memI_const (Cert.ivSq absK01).hi)
    have hAB_pos : 0 < A - B := lt_of_lt_of_le (valI_pos hdet_le) hdet_m.1
    have hdet_K : 0 < K00 * K11 - K01 ^ 2 := by linarith [hkk.1]
    have hdet_real : 0 < ‖w_u‖ ^ 2 * ‖w_v‖ ^ 2 - ⟪w_u, w_v⟫ ^ 2 := by
      rwa [hwu, hwv, hwuv]
    have hA_pos : 0 < A := by linarith
    have hKK_pos : 0 < K00 * K11 := lt_of_lt_of_le hA_pos hkk.1
    have h2pi_m : MemI (2 / π) (Cert.ivDivPos (Cert.ivConst (2 * Cert.certScale)) Cert.ivPi) := by
      have h2_eq : valI (2 * Cert.certScale) = 2 := by unfold valI Cert.certScale; norm_num
      rw [← h2_eq]
      exact memI_divPos (memI_const _) memI_pi (by decide)
    have hlhs_m := memI_mul (memI_sq h2pi_m) (memI_const kk.lo)
    have hrhs_m := memI_mul (memI_sq (memI_const st.cex)) hdet_m
    have hineq_A : (2 / π) ^ 2 * A ≤ (valI st.cex) ^ 2 * (A - B) :=
      hlhs_m.2.trans ((valI_mono hok).trans hrhs_m.1)
    have hc_ge : (2 / π) ^ 2 ≤ (valI st.cex) ^ 2 := by
      have : (2 / π) ^ 2 * A ≤ (valI st.cex) ^ 2 * A :=
        hineq_A.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _))
      exact le_of_mul_le_mul_right this hA_pos
    have hineq_KK : (2 / π) ^ 2 * (K00 * K11) ≤ (valI st.cex) ^ 2 * (K00 * K11 - K01 ^ 2) := by
      have hdiff : (2 / π) ^ 2 * (K00 * K11 - A) ≤ (valI st.cex) ^ 2 * (K00 * K11 - A) :=
        mul_le_mul_of_nonneg_right hc_ge (by linarith [hkk.1])
      have hsub_le : (valI st.cex) ^ 2 * (K00 * K11 - B) ≤
          (valI st.cex) ^ 2 * (K00 * K11 - K01 ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      linarith
    refine (integral_abs_mul_abs_le_div_sqrt hdet_real).trans ?_
    rw [hwu, hwv, hwuv, div_le_iff₀ (sqrt_pos.mpr hdet_K)]
    have hsq_le : (2 / π * (K00 * K11)) ^ 2 ≤
        (valI st.cex * √(K00 * K11) * √(K00 * K11 - K01 ^ 2)) ^ 2 := by
      calc (2 / π * (K00 * K11)) ^ 2
          = (2 / π) ^ 2 * (K00 * K11) * (K00 * K11) := by ring
        _ ≤ (valI st.cex) ^ 2 * (K00 * K11 - K01 ^ 2) * (K00 * K11) :=
            mul_le_mul_of_nonneg_right hineq_KK hKK_pos.le
        _ = (valI st.cex) ^ 2 * √(K00 * K11) ^ 2 * √(K00 * K11 - K01 ^ 2) ^ 2 := by
            rw [sq_sqrt hKK_pos.le, sq_sqrt hdet_K.le]; ring
        _ = (valI st.cex * √(K00 * K11) * √(K00 * K11 - K01 ^ 2)) ^ 2 := by ring
    nlinarith [sqrt_nonneg (K00 * K11), sqrt_nonneg (K00 * K11 - K01 ^ 2),
      mul_nonneg (mul_nonneg hcex_nn (sqrt_nonneg (K00 * K11)))
        (sqrt_nonneg (K00 * K11 - K01 ^ 2))]
  | 2 =>
    rw [hc] at hok; dsimp only at hok
    split_ifs at hok with g1 g2
    simp only [bindIval_eq, Bool.and_eq_true, ible_iff] at hok
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, iblt_false_iff, ible_false_iff] at g1 g2
    have hr0_nn : 0 ≤ valI st.rhoLo := by
      simpa only [valI, Int.cast_zero, zero_div] using valI_mono g1.1.1.1
    have hr01 : valI st.rhoLo ≤ valI st.rhoHi := valI_mono g1.1.1.2
    have hr1_le : valI st.rhoHi ≤ 1 := by
      simpa only [valI, Cert.certScale, Int.cast_ofNat,
        div_self (by norm_num : (100000000 : ℝ) ≠ 0)] using valI_mono g1.1.2
    have hKK_pos : 0 < ‖w_u‖ ^ 2 * ‖w_v‖ ^ 2 := by
      rw [hwu, hwv]; exact lt_of_lt_of_le (valI_pos g1.2) hkk.1
    have hlo_r : (valI st.rhoLo) ^ 2 * (‖w_u‖ ^ 2 * ‖w_v‖ ^ 2) ≤ ⟪w_u, w_v⟫ ^ 2 := by
      rw [hwu, hwv, hwuv, ← sq_abs K01]
      exact (memI_mul (memI_sq (memI_const st.rhoLo)) hkk).2.trans
        ((valI_mono g2.1).trans (memI_sq habs).1)
    have hhi_r : ⟪w_u, w_v⟫ ^ 2 ≤ (valI st.rhoHi) ^ 2 * (‖w_u‖ ^ 2 * ‖w_v‖ ^ 2) := by
      rw [hwu, hwv, hwuv, ← sq_abs K01]
      exact (memI_sq habs).2.trans
        ((valI_mono g2.2).trans (memI_mul (memI_sq (memI_const st.rhoHi)) hkk).1)
    have h83pi_m : MemI (8 / (3 * π))
        (Cert.ivDivPos (Cert.ivConst (8 * Cert.certScale)) (Cert.ivScaleInt 3 Cert.ivPi)) := by
      have h8_eq : valI (8 * Cert.certScale) = 8 := by unfold valI Cert.certScale; norm_num
      rw [← h8_eq]
      simpa only [Int.cast_ofNat] using
        memI_divPos (memI_const _) (memI_scaleInt 3 memI_pi) (by decide)
    have h1_m : MemI 1 (Cert.ivConst Cert.certScale) := by
      simpa only [valI, Cert.certScale, Int.cast_ofNat,
        div_self (by norm_num : (100000000 : ℝ) ≠ 0)] using memI_const Cert.certScale
    have hcub_le (ri : Int)
        (hri : (Cert.ivAdd (Cert.ivConst ri)
          (Cert.ivMul
            (Cert.ivDivPos (Cert.ivConst (8 * Cert.certScale)) (Cert.ivScaleInt 3 Cert.ivPi))
            (Cert.ivMul (Cert.ivSub (Cert.ivConst Cert.certScale) (Cert.ivConst ri))
              (Cert.ivAdd (Cert.ivSub (Cert.ivConst Cert.certScale) (Cert.ivConst ri))
                (Cert.ivDivInt (Cert.ivSq (Cert.ivConst ri)) 2))))).hi ≤ st.cex) :
        hCub (valI ri) ≤ valI st.cex := by
      have hm := memI_add (memI_const ri) (memI_mul h83pi_m
        (memI_mul (memI_sub h1_m (memI_const ri))
          (memI_add (memI_sub h1_m (memI_const ri)) (memI_divTwo (memI_sq (memI_const ri))))))
      have heq : hCub (valI ri) = valI ri + 8 / (3 * π) * ((1 - valI ri) *
          (1 - valI ri + (valI ri) ^ 2 / 2)) := by unfold hCub; ring
      rw [heq]; exact hm.2.trans (valI_mono hri)
    have hmax_le : max (hCub (valI st.rhoLo)) (hCub (valI st.rhoHi)) ≤ valI st.cex :=
      max_le (hcub_le st.rhoLo hok.1) (hcub_le st.rhoHi hok.2)
    refine (integral_abs_mul_abs_le_cubic_corr hr0_nn hr01 hr1_le hKK_pos hlo_r hhi_r).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hmax_le (sqrt_nonneg _)
  | n + 3 => rw [hc] at hok; cases hok

private theorem starQI_rmin_nonneg {ia : Nat} {q : Cert.QuadI} (hq : Cert.starQI ia = some q) :
    0 ≤ q.rmin := by
  match ia with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => injection hq with hq'; subst hq'; decide
  | n + 7 => cases hq

private structure PlanarS1Valid (u : Fin 4 → E) (b : Cert.BoxI) (st : Cert.PlanarStep)
    (s1 : Cert.PlanarS1) : Prop where
  ho10 : 0 ≤ b.o10
  ho20 : 0 ≤ b.o20
  ha0 : 0 ≤ b.a0
  hb0 : 0 ≤ b.b0
  hlam : 0 ≤ valI st.lam
  hlamM : 0 ≤ valI st.lamM
  hrxy : 0 < valI st.rxy
  hrxy_i : 0 < st.rxy
  hslo : 0 < valI st.slo
  hslo_i : 0 < st.slo
  hshi : 0 < valI st.shi
  hsm : 0 < valI st.sm
  hcex : 0 ≤ valI st.cex
  hrb_pos : 0 < pairRb u
  hvxy : (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) ≤ 2 * pairRb u ^ 2
  hdIv_pos : 0 < s1.dIv.lo
  hD_pos : 0 < (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2
  hvx_m : MemI ((1 + pairSab u) / 2) s1.vx
  hvy_m : MemI ((1 + pairScd u) / 2) s1.vy
  hd_m : MemI ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) s1.dIv
  hslo_sq : (valI st.slo) ^ 2 ≤ valI s1.dIv.lo
  hslo_sD : valI st.slo ≤ √((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)
  hshi_sD : √((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) ≤ valI st.shi
  h35 : 3 * ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) ≤ 5 * (valI st.sm) ^ 2
  hqa : 0 ≤ (s1.qa.c2 : ℝ) ∧ arccos ⟪u 0, u 1⟫ ≤ quadEval s1.qa (pairSab u)
  hqb : 0 ≤ (s1.qb.c2 : ℝ) ∧ arccos ⟪u 2, u 3⟫ ≤ quadEval s1.qb (pairScd u)
  hqc0 : 0 ≤ (s1.qc0.c2 : ℝ) ∧ arccos ⟪u 0, u 2⟫ ≤ quadEval s1.qc0 ⟪u 0, u 2⟫
  hqc1 : 0 ≤ (s1.qc1.c2 : ℝ) ∧ arccos ⟪u 1, u 3⟫ ≤ quadEval s1.qc1 ⟪u 1, u 3⟫
  hqc2 : 0 ≤ (s1.qc2.c2 : ℝ) ∧ arccos ⟪u 0, u 3⟫ ≤ quadEval s1.qc2 ⟪u 0, u 3⟫
  hqc3 : 0 ≤ (s1.qc3.c2 : ℝ) ∧ arccos ⟪u 1, u 2⟫ ≤ quadEval s1.qc3 ⟪u 1, u 2⟫
  hk00_m : MemI ((1 - pairSab u) / 2 -
    pairO1 u ^ 2 * ((1 + pairSab u) / 2) /
      ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) s1.k00
  hk11_m : MemI ((1 - pairScd u) / 2 -
    pairO2 u ^ 2 * ((1 + pairScd u) / 2) /
      ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) s1.k11
  hk01_m : MemI |pairTau u + pairO1 u * pairO2 u * pairRb u /
      ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)| s1.absK01
  hkk_m : MemI (((1 - pairSab u) / 2 -
      pairO1 u ^ 2 * ((1 + pairSab u) / 2) /
        ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
    ((1 - pairScd u) / 2 -
      pairO2 u ^ 2 * ((1 + pairScd u) / 2) /
        ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2))) s1.kk
  hcorr : ∀ w_u w_v : E,
    ‖w_u‖ ^ 2 = (1 - pairSab u) / 2 -
        pairO1 u ^ 2 * ((1 + pairSab u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) →
    ‖w_v‖ ^ 2 = (1 - pairScd u) / 2 -
        pairO2 u ^ 2 * ((1 + pairScd u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) →
    ⟪w_u, w_v⟫ = pairTau u + pairO1 u * pairO2 u * pairRb u /
        ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) →
    ∫ x, |⟪w_u, x⟫| * |⟪w_v, x⟫| ∂stdGaussian E ≤
      valI st.cex * √(‖w_u‖ ^ 2 * ‖w_v‖ ^ 2)

private theorem planarStage1_sound {b : Cert.BoxI} {st : Cert.PlanarStep} {s1 : Cert.PlanarS1}
    (hs1 : Cert.planarStage1 b st = some s1)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u)
    (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u) (hm : MemBox u b) :
    PlanarS1Valid u b st s1 := by
  unfold Cert.planarStage1 at hs1
  cases hs1a : Cert.planarStage1a b st with
  | none => rw [hs1a] at hs1; cases hs1
  | some s1a =>
    rw [hs1a] at hs1
    simp only [bindIval_eq] at hs1
    split_ifs at hs1 with hcex_ok
    injection hs1 with hs1_eq; subst hs1_eq
    unfold Cert.planarStage1a at hs1a
    split_ifs at hs1a with g1 g2
    cases hqa : Cert.starQI st.ia with
    | none => rw [hqa] at hs1a; cases hs1a
    | some qa =>
    cases hqb : Cert.starQI st.ib with
    | none => rw [hqa, hqb] at hs1a; cases hs1a
    | some qb =>
    cases hqc0 : Cert.crossQI st.ic0 with
    | none => rw [hqa, hqb, hqc0] at hs1a; cases hs1a
    | some qc0 =>
    cases hqc1 : Cert.crossQI st.ic1 with
    | none => rw [hqa, hqb, hqc0, hqc1] at hs1a; cases hs1a
    | some qc1 =>
    cases hqc2 : Cert.crossQI st.ic2 with
    | none => rw [hqa, hqb, hqc0, hqc1, hqc2] at hs1a; cases hs1a
    | some qc2 =>
    cases hqc3 : Cert.crossQI st.ic3 with
    | none => rw [hqa, hqb, hqc0, hqc1, hqc2, hqc3] at hs1a; cases hs1a
    | some qc3 =>
      rw [hqa, hqb, hqc0, hqc1, hqc2, hqc3] at hs1a
      simp only [bindInt_eq, bindIval_eq] at hs1a
      split_ifs at hs1a with g3 g4 g5
      injection hs1a with hs1a_eq; subst hs1a_eq
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, iblt_false_iff,
        ible_false_iff] at g1 g2 g3 g4 g5
      rcases hm with ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
      have hrb := admissiblePair_root_bounds hadm ho1 ho12
      have hcs := cross_slos_le hadm ho1 ho12 ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
      have h1_m : MemI 1 (Cert.ivConst Cert.certScale) := by
        simpa only [valI, Cert.certScale, Int.cast_ofNat,
          div_self (by norm_num : (100000000 : ℝ) ≠ 0)] using memI_const Cert.certScale
      have hvx_m : MemI ((1 + pairSab u) / 2)
          (Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨b.a0, b.a1⟩) 2) := by
        simpa only [Int.cast_ofNat] using memI_divInt (k := 2) (by norm_num) (memI_add h1_m ha)
      have hvy_m : MemI ((1 + pairScd u) / 2)
          (Cert.ivDivInt (Cert.ivAdd (Cert.ivConst Cert.certScale) ⟨b.b0, b.b1⟩) 2) := by
        simpa only [Int.cast_ofNat] using memI_divInt (k := 2) (by norm_num) (memI_add h1_m hcd)
      have hd_m := memI_sub (memI_mul hvx_m hvy_m) (memI_sq hr)
      have hD_pos := lt_of_lt_of_le (valI_pos g5.1.1.1) hd_m.1
      have hvxy : (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) ≤ 2 * pairRb u ^ 2 := by
        have h2r := memI_scaleInt 2 (memI_sq hr)
        simp only [Int.cast_ofNat] at h2r
        exact (memI_mul hvx_m hvy_m).2.trans ((valI_mono g4).trans h2r.1)
      have hslo_pos := valI_pos g2.1.1.1.2
      have hshi_pos := valI_pos g2.1.1.2
      have hslo_sq : (valI st.slo) ^ 2 ≤ valI _ :=
        (memI_sq (memI_const st.slo)).2.trans (valI_mono g5.1.1.2)
      have hslo_sD : valI st.slo ≤ √((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) -
          pairRb u ^ 2) := by
        have := sqrt_le_sqrt (hslo_sq.trans hd_m.1)
        rwa [sqrt_sq hslo_pos.le] at this
      have hshi_sD : √((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) ≤
          valI st.shi := by
        have hD_hi : (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2 ≤
            (valI st.shi) ^ 2 :=
          hd_m.2.trans ((valI_mono g5.1.2).trans (memI_sq (memI_const st.shi)).1)
        exact sqrt_le_iff.mpr ⟨hshi_pos.le, hD_hi⟩
      have h35 : 3 * ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) ≤
          5 * (valI st.sm) ^ 2 := by
        have h3d := memI_scaleInt 3 hd_m
        have h5s := memI_scaleInt 5 (memI_sq (memI_const st.sm))
        simp only [Int.cast_ofNat] at h3d h5s
        exact h3d.2.trans ((valI_mono g5.2).trans h5s.1)
      obtain ⟨_, _, _, _, _, _, _, hwu_sq, hwv_sq, _, _⟩ := pair_orth_residuals hadm.1 hD_pos
      have hK00_nn : 0 ≤ (1 - pairSab u) / 2 -
          pairO1 u ^ 2 * ((1 + pairSab u) / 2) /
            ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) :=
        hwu_sq ▸ sq_nonneg _
      have hK11_nn : 0 ≤ (1 - pairScd u) / 2 -
          pairO2 u ^ 2 * ((1 + pairScd u) / 2) /
            ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) :=
        hwv_sq ▸ sq_nonneg _
      have hh1a_m : MemI ((1 - pairSab u) / 2)
          (Cert.ivDivInt (Cert.ivSub (Cert.ivConst Cert.certScale) ⟨b.a0, b.a1⟩) 2) :=
        memI_divTwo (memI_sub h1_m ha)
      have hh1b_m : MemI ((1 - pairScd u) / 2)
          (Cert.ivDivInt (Cert.ivSub (Cert.ivConst Cert.certScale) ⟨b.b0, b.b1⟩) 2) :=
        memI_divTwo (memI_sub h1_m hcd)
      have h0_m : MemI 0 (Cert.ivConst 0) := by
        simpa only [valI, Int.cast_zero, zero_div] using memI_const 0
      have hk00_m := memI_max h0_m (memI_sub hh1a_m
        (memI_divPos (memI_mul (memI_sq h_o1) hvx_m) hd_m g5.1.1.1))
      rw [max_eq_right hK00_nn] at hk00_m
      have hk11_m := memI_max h0_m (memI_sub hh1b_m
        (memI_divPos (memI_mul (memI_sq h_o2) hvy_m) hd_m g5.1.1.1))
      rw [max_eq_right hK11_nn] at hk11_m
      have hk01_m := memI_abs (memI_add ht
        (memI_divPos (memI_mul (memI_mul h_o1 h_o2) hr) hd_m g5.1.1.1))
      have hkk_m := memI_mul hk00_m hk11_m
      have hcex_nn : 0 ≤ valI st.cex := valI_nonneg g2.2
      refine ⟨g1.1.1.1.1.1, g1.1.1.1.1.2, (starQI_rmin_nonneg hqa).trans g3.1.1.1.1.1,
        (starQI_rmin_nonneg hqb).trans g3.1.1.1.1.2,
        valI_nonneg g2.1.1.1.1.1.1, valI_nonneg g2.1.1.1.1.1.2,
        valI_pos g2.1.1.1.1.2, g2.1.1.1.1.2, hslo_pos, g2.1.1.1.2, hshi_pos, valI_pos g2.1.2,
        hcex_nn, by linarith [hrb.2.2.2.2.1], hvxy, g5.1.1.1, hD_pos, hvx_m, hvy_m, hd_m,
        hslo_sq, hslo_sD, hshi_sD, h35,
        arccos_le_starQI hqa ((valI_mono g3.1.1.1.1.1).trans ha.1) hrb.2.1,
        arccos_le_starQI hqb ((valI_mono g3.1.1.1.1.2).trans hcd.1) hrb.2.2.2.1,
        arccos_le_crossQI hqc0 ((valI_mono g3.1.1.1.2).trans hcs.1) hcs.2.1,
        arccos_le_crossQI hqc1 ((valI_mono g3.1.1.2).trans hcs.2.2.2.1) hcs.2.2.2.2.1,
        arccos_le_crossQI hqc2 ((valI_mono g3.1.2).trans hcs.2.2.2.2.2.2.1)
          hcs.2.2.2.2.2.2.2.1,
        arccos_le_crossQI hqc3 ((valI_mono g3.2).trans hcs.2.2.2.2.2.2.2.2.2.1)
          hcs.2.2.2.2.2.2.2.2.2.2.1,
        hk00_m, hk11_m, hk01_m, hkk_m,
        checkCexOk_sound hcex_nn hk01_m hkk_m hcex_ok⟩

private noncomputable def cuReal (v D detM omxa omxb opxa opxb : ℝ) : ℝ :=
  v / 2 * max
    (1 / (opxb * omxa ^ 2) + 1 / (omxb * opxa ^ 2) + omxb / detM ^ 2 + 1 / opxa)
    (1 / (omxb * opxa ^ 2) + 1 / (opxb * omxa ^ 2) + 1 / opxb + 1 / (omxa * detM)) / D

private theorem cuReal_mul_eq_pairCxMax {oVal v D xa xb detM : ℝ}
    (ho : 0 ≤ oVal) (hv : 0 ≤ v) (hD : 0 < D) :
    pairCxMax (oVal / D) v xa xb detM =
      cuReal v D detM (1 - xa) (1 - xb) (1 + xa) (1 + xb) * oVal := by
  unfold pairCxMax pairCxp pairCxm cuReal
  have h1 : (1 + xa) ^ 2 * (1 - xb) = (1 - xb) * (1 + xa) ^ 2 := mul_comm _ _
  have h2 : (1 - xa) ^ 2 * (1 + xb) = (1 + xb) * (1 - xa) ^ 2 := mul_comm _ _
  rw [h1, h2]
  set wp := 1 / ((1 + xb) * (1 - xa) ^ 2) + 1 / ((1 - xb) * (1 + xa) ^ 2) +
    (1 - xb) / detM ^ 2 + 1 / (1 + xa)
  set wm := 1 / ((1 - xb) * (1 + xa) ^ 2) + 1 / ((1 + xb) * (1 - xa) ^ 2) +
    1 / (1 + xb) + 1 / ((1 - xa) * detM)
  have hfac_l : oVal / D * v / 2 * wp = oVal * v / (2 * D) * wp := by ring
  have hfac_r : oVal / D * v / 2 * wm = oVal * v / (2 * D) * wm := by ring
  rw [hfac_l, hfac_r, ← mul_max_of_nonneg wp wm (by positivity)]
  ring

private theorem calcCuOpt_sound {v D detM omxa omxb opxa opxb : ℝ}
    {vIv dIv detMIv omxaIv omxbIv opxaIv opxbIv cuIv : Cert.Ival}
    (hv : MemI v vIv) (hd : MemI D dIv) (hd_pos : 0 < dIv.lo)
    (hdet : MemI detM detMIv)
    (homxa : MemI omxa omxaIv) (homxb : MemI omxb omxbIv)
    (hopxa : MemI opxa opxaIv) (hopxb : MemI opxb opxbIv)
    (hopt : Cert.calcCuOpt vIv dIv detMIv omxaIv omxbIv opxaIv opxbIv = some cuIv) :
    MemI (cuReal v D detM omxa omxb opxa opxb) cuIv := by
  unfold Cert.calcCuOpt at hopt
  cases hcd : Cert.calcCuDenoms detMIv omxaIv omxbIv opxaIv opxbIv with
  | none => rw [hcd] at hopt; cases hopt
  | some cd =>
    rw [hcd] at hopt
    simp only [bindIval_eq, Option.some.injEq] at hopt
    subst hopt
    unfold Cert.calcCuDenoms at hcd
    split_ifs at hcd with g1
    simp only [bindIval_eq] at hcd
    split_ifs at hcd with g2
    injection hcd with hcd_eq; subst hcd_eq
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, ible_false_iff] at g1 g2
    have h1_m : MemI 1 (Cert.ivConst Cert.certScale) := by
      simpa only [valI, Cert.certScale, Int.cast_ofNat,
        div_self (by norm_num : (100000000 : ℝ) ≠ 0)] using memI_const Cert.certScale
    have hd1 := memI_mul hopxb (memI_sq homxa)
    have hd2 := memI_mul homxb (memI_sq hopxa)
    have hd3 := memI_sq hdet
    have hd4 := memI_mul homxa hdet
    have hwp := memI_add
      (memI_add (memI_divPos h1_m hd1 g2.1.1.1) (memI_divPos h1_m hd2 g2.1.1.2))
      (memI_add (memI_divPos homxb hd3 g2.1.2) (memI_divPos h1_m hopxa g1.1))
    have hwm := memI_add
      (memI_add (memI_divPos h1_m hd2 g2.1.1.2) (memI_divPos h1_m hd1 g2.1.1.1))
      (memI_add (memI_divPos h1_m hopxb g1.2) (memI_divPos h1_m hd4 g2.2))
    have hv2 : MemI (v / 2) (Cert.ivDivInt vIv 2) := by
      simpa only [Int.cast_ofNat] using memI_divInt (k := 2) (by norm_num) hv
    have hres := memI_divPos (memI_mul hv2 (memI_max hwp hwm)) hd hd_pos
    simpa only [cuReal, ← add_assoc] using hres

private structure PlanarS2Valid (u : Fin 4 → E) (s2 : Cert.PlanarS2) : Prop where
  hx1_lt : pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
    pairRb u < 1
  hx2_lt : pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
    pairRb u < 1
  hdetM_pos : 0 <
    (1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) *
    (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) -
    pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
      ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2)
  hcxU_hi_nn : 0 ≤ valI s2.cxU.hi
  hceU_hi_nn : 0 ≤ valI s2.ceU.hi
  hcx_le : pairCxMax (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2))
    ((1 + pairScd u) / 2)
    (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    ((1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) *
      (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) -
      pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
        (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
        ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2)) ≤ valI s2.cxU.hi * pairO2 u
  hce_le : pairCxMax (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2))
    ((1 + pairSab u) / 2)
    (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    ((1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) *
      (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) -
      pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
        (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
        ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2)) ≤ valI s2.ceU.hi * pairO1 u
  hcxU_m : MemI (cuReal ((1 + pairScd u) / 2)
    ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)
    ((1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) *
      (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) -
      pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
        (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
        ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2))
    (1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    (1 + pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    (1 + pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u))
    s2.cxU
  hceU_m : MemI (cuReal ((1 + pairSab u) / 2)
    ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)
    ((1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) *
      (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) -
      pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
        (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
        ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2))
    (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    (1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    (1 + pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    (1 + pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u))
    s2.ceU
  hu1_m : MemI (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) s2.u1
  hu2_m : MemI (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) s2.u2
  hx1_m : MemI (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
    pairRb u) s2.x1
  hx2_m : MemI (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
    pairRb u) s2.x2
  hp_m : MemI (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
    (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
    ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2)) s2.pIv
  homx1_m : MemI (1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
    pairRb u) s2.omx1
  homx2_m : MemI (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
    pairRb u) s2.omx2
  hdetM_m : MemI ((1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      pairRb u) *
    (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) -
    pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
      ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2)) s2.detM
  homx1sq_m : MemI (1 - (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
    pairRb u) ^ 2) s2.omx1sq
  hdenX12_m : MemI ((1 - (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      pairRb u) ^ 2) *
    (1 - (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      pairRb u) ^ 2)) s2.denX12
  hdenX12_pos : 0 < s2.denX12.lo
  hdenO12_m : MemI (((1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      pairRb u) *
    (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)) *
    ((1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) *
      (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) -
      pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
        (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
        ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2))) s2.denO12
  hdenO12_pos : 0 < s2.denO12.lo
  hcAB_m : MemI (pairCAB
    (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u)
    (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
      ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2))
    ((1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) *
      (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) -
      pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
        (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
        ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2))) s2.cAB

omit [BorelSpace E] in
private theorem planarStage2_sound {b : Cert.BoxI} {st : Cert.PlanarStep} {s1 : Cert.PlanarS1}
    {s2 : Cert.PlanarS2} (hs2 : Cert.planarStage2 b s1 = some s2)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u)
    (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u) (hm : MemBox u b)
    (hv1 : PlanarS1Valid u b st s1) :
    PlanarS2Valid u s2 := by
  unfold Cert.planarStage2 at hs2
  cases hs2a : Cert.planarStage2a b s1 with
  | none => rw [hs2a] at hs2; cases hs2
  | some s2a =>
    rw [hs2a] at hs2; dsimp only at hs2
    cases hcx : Cert.calcCuOpt s1.vy s1.dIv s2a.detM s2a.omx1 s2a.omx2 s2a.opx1 s2a.opx2 with
    | none => rw [hcx] at hs2; cases hs2
    | some cxU =>
    cases hce : Cert.calcCuOpt s1.vx s1.dIv s2a.detM s2a.omx2 s2a.omx1 s2a.opx2 s2a.opx1 with
    | none => rw [hcx, hce] at hs2; cases hs2
    | some ceU =>
      rw [hcx, hce] at hs2; dsimp only at hs2
      simp only [bindIval_eq] at hs2
      split_ifs at hs2 with g_den
      injection hs2 with hs2_eq; subst hs2_eq
      unfold Cert.planarStage2a at hs2a
      simp only [bindIval_eq] at hs2a
      split_ifs at hs2a with gx hdet_le
      injection hs2a with hs2a_eq; subst hs2a_eq
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, ible_false_iff] at gx g_den
      rw [Bool.not_eq_true, ible_false_iff] at hdet_le
      rcases hm with ⟨_, _, hr, h_o1, h_o2, _⟩
      have hrb := admissiblePair_root_bounds hadm ho1 ho12
      have h1_m : MemI 1 (Cert.ivConst Cert.certScale) := by
        simpa only [valI, Cert.certScale, Int.cast_ofNat,
          div_self (by norm_num : (100000000 : ℝ) ≠ 0)] using memI_const Cert.certScale
      have hu1_m := memI_divPos h_o1 hv1.hd_m hv1.hdIv_pos
      have hu2_m := memI_divPos h_o2 hv1.hd_m hv1.hdIv_pos
      have hx1_m := memI_mul hu1_m hr
      have hx2_m := memI_mul hu2_m hr
      have hx1_lt : pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
          pairRb u < 1 :=
        lt_of_le_of_lt hx1_m.2 ((valI_lt gx.1).trans_eq
          (by unfold valI Cert.certScale; norm_num))
      have hx2_lt : pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
          pairRb u < 1 :=
        lt_of_le_of_lt hx2_m.2 ((valI_lt gx.2).trans_eq
          (by unfold valI Cert.certScale; norm_num))
      have hp_m := memI_mul (memI_mul hu1_m hu2_m) (memI_mul hv1.hvx_m hv1.hvy_m)
      simp only [← mul_assoc] at hp_m
      have homx1_m := memI_sub h1_m hx1_m
      have homx2_m := memI_sub h1_m hx2_m
      have hopx1_m := memI_add h1_m hx1_m
      have hopx2_m := memI_add h1_m hx2_m
      have hdetM_m := memI_sub (memI_mul homx1_m homx2_m) hp_m
      have hdetM_pos := lt_of_lt_of_le (valI_pos hdet_le) hdetM_m.1
      have hcxU_m := calcCuOpt_sound hv1.hvy_m hv1.hd_m hv1.hdIv_pos hdetM_m
        homx1_m homx2_m hopx1_m hopx2_m hcx
      have hceU_m := calcCuOpt_sound hv1.hvx_m hv1.hd_m hv1.hdIv_pos hdetM_m
        homx2_m homx1_m hopx2_m hopx1_m hce
      have ho2_nn : 0 ≤ pairO2 u := ho1.trans ho12
      have hvx_nn : 0 ≤ (1 + pairSab u) / 2 := by linarith [hrb.1]
      have hvy_nn : 0 ≤ (1 + pairScd u) / 2 := by linarith [hrb.2.2.1]
      have hx1_nn : 0 ≤ pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) -
          pairRb u ^ 2) * pairRb u :=
        mul_nonneg (div_nonneg ho1 hv1.hD_pos.le) hv1.hrb_pos.le
      have hx2_nn : 0 ≤ pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) -
          pairRb u ^ 2) * pairRb u :=
        mul_nonneg (div_nonneg ho2_nn hv1.hD_pos.le) hv1.hrb_pos.le
      have hcu_nn {v D detM xa xb : ℝ} (hv_n : 0 ≤ v) (hD_p : 0 < D) (hdM : 0 < detM)
          (ha0 : 0 ≤ xa) (ha1 : xa < 1) (hb0 : 0 ≤ xb) (hb1 : xb < 1) :
          0 ≤ cuReal v D detM (1 - xa) (1 - xb) (1 + xa) (1 + xb) := by
        unfold cuReal
        have hpos1 : 0 < 1 - xa := by linarith
        have hpos2 : 0 < 1 - xb := by linarith
        have hpos3 : 0 < 1 + xa := by linarith
        have hpos4 : 0 < 1 + xb := by linarith
        exact div_nonneg (mul_nonneg (by positivity)
          (le_trans (by positivity) (le_max_left _ _))) hD_p.le
      have hcx_nn := hcu_nn hvy_nn hv1.hD_pos hdetM_pos hx1_nn hx1_lt hx2_nn hx2_lt
      have hce_nn := hcu_nn hvx_nn hv1.hD_pos hdetM_pos hx2_nn hx2_lt hx1_nn hx1_lt
      have homx1sq_m := memI_sub h1_m (memI_sq hx1_m)
      have homx2sq_m := memI_sub h1_m (memI_sq hx2_m)
      have hdenX12_m := memI_mul homx1sq_m homx2sq_m
      have hdenO12_m := memI_mul (memI_mul homx1_m homx2_m) hdetM_m
      have h4_m : MemI 4 (Cert.ivConst (4 * Cert.certScale)) := by
        simpa only [valI, Cert.certScale, Int.cast_mul, Int.cast_ofNat,
          mul_div_cancel_right₀ _ (by norm_num : (100000000 : ℝ) ≠ 0)] using
          memI_const (4 * Cert.certScale)
      have hcAB_m := memI_add (memI_divPos h4_m hdenX12_m g_den.1)
        (memI_divPos hp_m hdenO12_m g_den.2)
      refine ⟨hx1_lt, hx2_lt, hdetM_pos, hcx_nn.trans hcxU_m.2, hce_nn.trans hceU_m.2, ?_, ?_,
        hcxU_m, hceU_m, hu1_m, hu2_m, hx1_m, hx2_m, hp_m, homx1_m, homx2_m, hdetM_m,
        homx1sq_m, hdenX12_m, g_den.1, hdenO12_m, g_den.2, hcAB_m⟩
      · rw [cuReal_mul_eq_pairCxMax ho2_nn hvy_nn hv1.hD_pos]
        exact mul_le_mul_of_nonneg_right hcxU_m.2 ho2_nn
      · rw [cuReal_mul_eq_pairCxMax ho1 hvx_nn hv1.hD_pos]
        exact mul_le_mul_of_nonneg_right hceU_m.2 ho1

private theorem ivSq_lo_nonneg (a : Cert.Ival) : 0 ≤ (Cert.ivSq a).lo := by
  cases a with | mk alo ahi =>
  unfold Cert.ivSq
  simp only [bindIval_eq, bindInt_eq, Cert.certScale]
  split_ifs with h1 h2
  · rw [ible_iff] at h1
    exact Int.ediv_nonneg (mul_nonneg h1 h1) (by norm_num)
  · rw [ible_iff] at h2
    exact Int.ediv_nonneg (mul_nonneg_of_nonpos_of_nonpos h2 h2) (by norm_num)
  · exact le_rfl

private noncomputable def boxMid (lo hi : Int) : ℝ := valI (lo + hi) / 2

private theorem boxMid_mem_and_rad {lo hi : Int} {x : ℝ} (h : MemI x ⟨lo, hi⟩) :
    MemI (boxMid lo hi) (Cert.ivDivInt (Cert.ivConst (lo + hi)) 2) ∧
    |x - boxMid lo hi| ≤ valI (Cert.cdiv (hi - lo) 2) ∧
    0 ≤ Cert.cdiv (hi - lo) 2 := by
  have hm : MemI (boxMid lo hi) (Cert.ivDivInt (Cert.ivConst (lo + hi)) 2) := by
    unfold boxMid
    simpa only [Int.cast_ofNat] using
      memI_divInt (k := 2) (by norm_num) (memI_const (lo + hi))
  have hle_i : lo ≤ hi := by
    have hr : valI lo ≤ valI hi := h.1.trans h.2
    unfold valI at hr
    have : (lo : ℝ) ≤ (hi : ℝ) := by linarith
    exact_mod_cast this
  have habs : |x - boxMid lo hi| ≤ valI (hi - lo) / (2 : Int) := by
    rw [abs_le]
    unfold MemI valI at h
    unfold boxMid valI
    push_cast; constructor <;> linarith [h.1, h.2]
  have hcdiv_nn : 0 ≤ Cert.cdiv (hi - lo) 2 := by
    unfold Cert.cdiv; simp only [bindInt_eq]
    change 0 ≤ Int.ediv (hi - lo + 2 - 1) 2
    exact Int.ediv_nonneg (by omega) (by norm_num)
  exact ⟨hm, habs.trans (valI_cdiv_ge (hi - lo) 2 (by norm_num)), hcdiv_nn⟩

private structure PlanarS3Valid (u : Fin 4 → E) (b : Cert.BoxI) (s3 : Cert.PlanarS3) : Prop where
  haM : MemI (boxMid b.a0 b.a1) s3.aM
  hbM : MemI (boxMid b.b0 b.b1) s3.bM
  hrM : MemI (boxMid b.r0 b.r1) s3.rM
  ho1M : MemI (boxMid b.o10 b.o11) s3.o1M
  ho2M : MemI (boxMid b.o20 b.o21) s3.o2M
  htM : MemI (boxMid b.t0 b.t1) s3.tM
  hda : |pairSab u - boxMid b.a0 b.a1| ≤ valI s3.daHi ∧ 0 ≤ s3.daHi
  hdb : |pairScd u - boxMid b.b0 b.b1| ≤ valI s3.dbHi ∧ 0 ≤ s3.dbHi
  hdr : |pairRb u - boxMid b.r0 b.r1| ≤ valI s3.drHi ∧ 0 ≤ s3.drHi
  hdo1 : |pairO1 u - boxMid b.o10 b.o11| ≤ valI s3.do1Hi ∧ 0 ≤ s3.do1Hi
  hdo2 : |pairO2 u - boxMid b.o20 b.o21| ≤ valI s3.do2Hi ∧ 0 ≤ s3.do2Hi
  hdt : |pairTau u - boxMid b.t0 b.t1| ≤ valI s3.dtHi ∧ 0 ≤ s3.dtHi
  hvxM : MemI ((1 + boxMid b.a0 b.a1) / 2) s3.vxM
  hvyM : MemI ((1 + boxMid b.b0 b.b1) / 2) s3.vyM
  hdM : MemI ((1 + boxMid b.a0 b.a1) / 2 * ((1 + boxMid b.b0 b.b1) / 2) -
    (boxMid b.r0 b.r1) ^ 2) s3.dM
  hsec : ∃ cInv_r invM_r gM_r gSl_r : ℝ,
    0 ≤ cInv_r ∧ MemI cInv_r s3.cInv ∧ MemI invM_r s3.invM ∧
    0 ≤ gM_r ∧ MemI gM_r s3.gM ∧ MemI gSl_r s3.gSl ∧
    1 / √((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) ≤
      invM_r - cInv_r *
        (((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) -
          ((1 + boxMid b.a0 b.a1) / 2 * ((1 + boxMid b.b0 b.b1) / 2) -
            (boxMid b.r0 b.r1) ^ 2)) ∧
    |cInv_r * (((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) -
        ((1 + boxMid b.a0 b.a1) / 2 * ((1 + boxMid b.b0 b.b1) / 2) -
          (boxMid b.r0 b.r1) ^ 2))| ≤ valI s3.dLMax ∧
    gM_r - gSl_r *
        (((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) -
          ((1 + boxMid b.a0 b.a1) / 2 * ((1 + boxMid b.b0 b.b1) / 2) -
            (boxMid b.r0 b.r1) ^ 2)) ≤
      1 / (((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
        √((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) ∧
    |1 / (((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
        √((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) - gM_r| ≤
      valI s3.gVarMax

omit [BorelSpace E] in
private theorem planarStage3_sound {b : Cert.BoxI} {st : Cert.PlanarStep} {s1 : Cert.PlanarS1}
    {s3 : Cert.PlanarS3} (hs3 : Cert.planarStage3 b st s1 = some s3)
    {u : Fin 4 → E} (hm : MemBox u b) (hv1 : PlanarS1Valid u b st s1) :
    PlanarS3Valid u b s3 := by
  unfold Cert.planarStage3 at hs3
  cases hpm : Cert.planarMid b with
  | none => rw [hpm] at hs3; cases hs3
  | some pm =>
    rw [hpm] at hs3; dsimp only at hs3
    cases hsb : Cert.planarStage3b st s1 pm with
    | none => rw [hsb] at hs3; cases hs3
    | some sb =>
      rw [hsb] at hs3; dsimp only at hs3
      simp only [bindIval_eq, bindInt_eq] at hs3
      split_ifs at hs3 with gsm5 hgM_neg hsR3
      injection hs3 with hs3_eq; subst hs3_eq
      unfold Cert.planarMid Cert.planarMidCoords at hpm
      simp only [bindIval_eq, bindInt_eq, Option.some.injEq] at hpm
      subst hpm
      unfold Cert.planarStage3b at hsb
      simp only [bindIval_eq, bindInt_eq, Option.some.injEq] at hsb
      subst hsb
      rw [Bool.not_eq_true, ible_false_iff] at gsm5 hsR3
      rw [Bool.not_eq_true, iblt_false_iff] at hgM_neg
      rcases hm with ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
      obtain ⟨haM, hda, hda_nn⟩ := boxMid_mem_and_rad ha
      obtain ⟨hbM, hdb, hdb_nn⟩ := boxMid_mem_and_rad hcd
      obtain ⟨hrM, hdr, hdr_nn⟩ := boxMid_mem_and_rad hr
      obtain ⟨ho1M, hdo1, hdo1_nn⟩ := boxMid_mem_and_rad h_o1
      obtain ⟨ho2M, hdo2, hdo2_nn⟩ := boxMid_mem_and_rad h_o2
      obtain ⟨htM, hdt, hdt_nn⟩ := boxMid_mem_and_rad ht
      have h1_m : MemI 1 (Cert.ivConst Cert.certScale) := by
        simpa only [valI, Cert.certScale, Int.cast_ofNat,
          div_self (by norm_num : (100000000 : ℝ) ≠ 0)] using memI_const Cert.certScale
      have hvxM : MemI ((1 + boxMid b.a0 b.a1) / 2) _ := memI_divTwo (memI_add h1_m haM)
      have hvyM : MemI ((1 + boxMid b.b0 b.b1) / 2) _ := memI_divTwo (memI_add h1_m hbM)
      have hdM := memI_sub (memI_mul hvxM hvyM) (memI_sq hrM)
      set D := (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2
      set D_m := (1 + boxMid b.a0 b.a1) / 2 * ((1 + boxMid b.b0 b.b1) / 2) -
        (boxMid b.r0 b.r1) ^ 2
      have hden_sec_pos : 0 < valI st.slo * valI st.shi * (valI st.slo + valI st.shi) := by
        have := hv1.hslo; have := hv1.hshi; positivity
      have hden_sec_m := memI_mul (memI_mul (memI_const st.slo) (memI_const st.shi))
        (memI_add (memI_const st.slo) (memI_const st.shi))
      set cInvRaw := (Cert.ivDivPos (Cert.ivConst Cert.certScale)
        (Cert.ivMul (Cert.ivMul (Cert.ivConst st.slo) (Cert.ivConst st.shi))
          (Cert.ivAdd (Cert.ivConst st.slo) (Cert.ivConst st.shi)))).lo
      set cInvI := Cert.imax 0 cInvRaw
      have hcInv_nn : 0 ≤ valI cInvI := by
        dsimp only [cInvI]; rw [imax_eq]
        exact valI_nonneg (le_max_left 0 cInvRaw)
      have hcInv_le : valI cInvI ≤
          1 / (valI st.slo * valI st.shi * (valI st.slo + valI st.shi)) := by
        dsimp only [cInvI]; rw [imax_eq]
        rcases le_total 0 cInvRaw with h | h
        · rw [max_eq_right h]; exact divPos_one_lo_le hden_sec_pos hden_sec_m
        · rw [max_eq_left h]; unfold valI; simp only [Int.cast_zero, zero_div]
          exact div_nonneg zero_le_one hden_sec_pos.le
      set invM_r := 1 / valI st.slo - valI cInvI * (D_m - valI s1.dIv.lo)
      have hinvM_m := memI_sub
        (memI_divPos h1_m (memI_const st.slo) hv1.hslo_i)
        (memI_mul (memI_const cInvI) (memI_sub hdM (memI_const s1.dIv.lo)))
      have hsec_ineq : 1 / √D ≤ invM_r - valI cInvI * (D - D_m) := by
        refine (inv_sqrt_le_secant hv1.hslo hv1.hslo_sq hv1.hd_m.1 hv1.hshi_sD
          hcInv_nn hcInv_le).trans_eq ?_
        dsimp only [invM_r]; ring
      have hdLMax_m := memI_mul (memI_const cInvI) (memI_abs (memI_sub hv1.hd_m hdM))
      have hdLMax_le := (by rw [abs_mul, abs_of_nonneg hcInv_nn] :
        |valI cInvI * (D - D_m)| = valI cInvI * |D - D_m|).trans_le hdLMax_m.2
      -- Tangent `1 / (D * √D)`:
      have hsm2_m := memI_sq (memI_const st.sm)
      have hsm5_eq : ((valI st.sm) ^ 2 * (valI st.sm) ^ 2) * valI st.sm = (valI st.sm) ^ 5 := by
        ring
      set sm5Iv := Cert.ivMul (Cert.ivMul (Cert.ivSq (Cert.ivConst st.sm))
        (Cert.ivSq (Cert.ivConst st.sm))) (Cert.ivConst st.sm)
      have hsm5_m : MemI ((valI st.sm) ^ 5) sm5Iv :=
        hsm5_eq ▸ memI_mul (memI_mul hsm2_m hsm2_m) (memI_const st.sm)
      have h2sm5_m := memI_scaleNat 2 hsm5_m
      have h2sm5_pos : 0 < 2 * (valI st.sm) ^ 5 := by have := hv1.hsm; positivity
      set inv2sm5Raw := (Cert.ivDivPos (Cert.ivConst Cert.certScale)
        (Cert.ivScaleInt 2 sm5Iv)).lo
      set inv2sm5I := Cert.imax 0 inv2sm5Raw
      have hinv2_nn : 0 ≤ valI inv2sm5I := by
        dsimp only [inv2sm5I]; rw [imax_eq]
        exact valI_nonneg (le_max_left 0 inv2sm5Raw)
      have hinv2_le : valI inv2sm5I ≤ 1 / (2 * (valI st.sm) ^ 5) := by
        dsimp only [inv2sm5I]; rw [imax_eq]
        rcases le_total 0 inv2sm5Raw with h | h
        · rw [max_eq_right h]; exact divPos_one_lo_le h2sm5_pos h2sm5_m
        · rw [max_eq_left h]; unfold valI; simp only [Int.cast_zero, zero_div]
          exact div_nonneg zero_le_one h2sm5_pos.le
      set gM_r := valI inv2sm5I * (5 * (valI st.sm) ^ 2 - 3 * D_m)
      set gSl_r := 3 * valI inv2sm5I
      have hgM_m :=
        memI_mul (memI_const inv2sm5I) (memI_sub (memI_scaleNat 5 hsm2_m) (memI_scaleNat 3 hdM))
      have hgM_nn : 0 ≤ gM_r := (valI_nonneg hgM_neg).trans hgM_m.1
      have hgSl_m := memI_scaleNat 3 (memI_const inv2sm5I)
      have htan_ineq : gM_r - gSl_r * (D - D_m) ≤ 1 / (D * √D) := by
        have h := inv_D_sqrt_ge_tangent hv1.hD_pos hv1.hsm hv1.h35 hinv2_nn hinv2_le
        refine le_trans (le_of_eq ?_) h
        dsimp only [gM_r, gSl_r]; ring
      have hsRange_m : MemI √D ⟨st.slo, st.shi⟩ := ⟨hv1.hslo_sD, hv1.hshi_sD⟩
      have hsRange3_eq : √D ^ 2 * √D = D * √D := by rw [sq_sqrt hv1.hD_pos.le]
      have hsRange3_m := memI_mul (memI_sq hsRange_m) hsRange_m
      rw [hsRange3_eq] at hsRange3_m
      have hgRange_m := memI_divPos h1_m hsRange3_m hsR3
      have hgVar_le := (memI_abs (memI_sub hgRange_m hgM_m)).2
      exact ⟨haM, hbM, hrM, ho1M, ho2M, htM, ⟨hda, hda_nn⟩, ⟨hdb, hdb_nn⟩, ⟨hdr, hdr_nn⟩,
        ⟨hdo1, hdo1_nn⟩, ⟨hdo2, hdo2_nn⟩, ⟨hdt, hdt_nn⟩, hvxM, hvyM, hdM,
        ⟨valI cInvI, invM_r, gM_r, gSl_r, hcInv_nn, memI_const cInvI, hinvM_m,
          hgM_nn, hgM_m, hgSl_m, hsec_ineq, hdLMax_le, htan_ineq, hgVar_le⟩⟩

private theorem ival_mid_rad {x : ℝ} {v : Cert.Ival} (h : MemI x v) :
    |x - valI ((v.lo + v.hi) / 2)| ≤ valI (Cert.cdiv (v.hi - v.lo) 2) ∧
    0 ≤ Cert.cdiv (v.hi - v.lo) 2 := by
  have hle_i : v.lo ≤ v.hi := by
    have hr : valI v.lo ≤ valI v.hi := h.1.trans h.2
    unfold valI at hr
    have : (v.lo : ℝ) ≤ (v.hi : ℝ) := by linarith
    exact_mod_cast this
  unfold Cert.cdiv
  simp only [bindInt_eq]
  change |x - valI ((v.lo + v.hi) / 2)| ≤ valI ((v.hi - v.lo + 2 - 1) / 2) ∧
    0 ≤ (v.hi - v.lo + 2 - 1) / 2
  have h1 : (v.lo + v.hi) / 2 - (v.hi - v.lo + 2 - 1) / 2 ≤ v.lo := by omega
  have h2 : v.hi ≤ (v.lo + v.hi) / 2 + (v.hi - v.lo + 2 - 1) / 2 := by omega
  have h1r := valI_mono h1
  have h2r := valI_mono h2
  refine ⟨abs_le.mpr ?_, Int.ediv_nonneg (by omega) (by norm_num)⟩
  unfold MemI valI at h
  unfold valI at h1r h2r ⊢
  push_cast at h1r h2r ⊢
  constructor <;> linarith [h.1, h.2]

private structure PlanarModelValid (u : Fin 4 → E) (b : Cert.BoxI) (st : Cert.PlanarStep)
    (md : Cert.PlanarModel) : Prop where
  hm : ∃ bK0_m bK1_m bK0_sl bK1_sl cEx_sl1 cEx_sl2 cEx_curv : ℝ,
    0 ≤ bK0_m ∧ MemI bK0_m md.bK0M ∧
    0 ≤ bK1_m ∧ MemI bK1_m md.bK1M ∧
    0 ≤ valI md.cExM.hi ∧
    MemI bK0_sl md.bK0Sl ∧ MemI bK1_sl md.bK1Sl ∧
    MemI cEx_sl1 md.cExSl1 ∧ MemI cEx_sl2 md.cExSl2 ∧
    0 ≤ cEx_curv ∧ MemI cEx_curv md.cExCurv ∧
    (let vx := (1 + pairSab u) / 2
     let vy := (1 + pairScd u) / 2
     let rb := pairRb u
     let D := vx * vy - rb ^ 2
     let K00 := (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D
     let K11 := (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D
     let W := valI st.cex * √(K00 * K11) / (4 * π * √D)
     pairCost u 0 ≤
       (arccos ⟪u 0, u 1⟫ + arccos ⟪u 2, u 3⟫) / (2 * π) +
       (arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 3⟫ + arccos ⟪u 0, u 3⟫ + arccos ⟪u 1, u 2⟫) /
         (4 * π) +
       (bK0_m * K00 + bK1_m * K11 + valI md.cExM.hi * (valI st.cex * √(K00 * K11))) /
         (4 * π * √D) +
       (bK0_sl + cEx_sl2 * W) * (pairO2 u - boxMid b.o20 b.o21) +
       (bK1_sl + cEx_sl1 * W) * (pairO1 u - boxMid b.o10 b.o11) +
       cEx_curv * W * ((pairO1 u - boxMid b.o10 b.o11) ^ 2 +
         (pairO2 u - boxMid b.o20 b.o21) ^ 2) +
       valI md.bK0Rem + valI md.bK1Rem)

private theorem hide_valI {a : ℝ} {k : Int} (h : a ≤ valI k) :
    ∃ v : ℝ, v = valI k ∧ a ≤ v := ⟨valI k, rfl, h⟩

private theorem hide_nonneg_add {a b : ℝ} (h : 0 ≤ a + b) :
    ∃ v : ℝ, v = a ∧ 0 ≤ v + b := ⟨a, rfl, h⟩

private theorem planarModelOut_sound {b : Cert.BoxI} {st : Cert.PlanarStep}
    {s1 : Cert.PlanarS1} {s2 : Cert.PlanarS2} {s3 : Cert.PlanarS3} {md : Cert.PlanarModel}
    (hmd : Cert.planarModelOut b st s1 s2 s3 = some md)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u)
    (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u) (hm : MemBox u b)
    (hv1 : PlanarS1Valid u b st s1) (hv2 : PlanarS2Valid u s2) (hv3 : PlanarS3Valid u b s3) :
    PlanarModelValid u b st md := by
  unfold Cert.planarModelOut at hmd
  cases hm1 : Cert.planarModelOut1 st s1 s2 s3 with
  | none => rw [hm1] at hmd; cases hmd
  | some m1 =>
    rw [hm1] at hmd; dsimp only at hmd
    cases hm2 : Cert.planarModelOut2 b s1 s2 s3 m1 with
    | none => rw [hm2] at hmd; cases hmd
    | some m2 =>
      rw [hm2] at hmd; dsimp only at hmd
      simp only [bindIval_eq, Option.some.injEq] at hmd
      subst hmd
      unfold Cert.planarModelOut1 at hm1
      simp only [bindIval_eq, bindInt_eq, Option.some.injEq] at hm1
      subst hm1
      unfold Cert.planarModelOut2 at hm2
      simp only [bindIval_eq, bindInt_eq] at hm2
      split_ifs at hm2 with gdSq
      injection hm2 with hm2_eq; subst hm2_eq
      rw [Bool.not_eq_true, ible_false_iff] at gdSq
      have hcoords := box_nonempty_coords hm
      have mid_nonneg {lo hi : ℤ} (hlo : 0 ≤ lo) (h : lo ≤ hi) : 0 ≤ boxMid lo hi :=
        div_nonneg (valI_nonneg (add_nonneg hlo (hlo.trans h))) zero_le_two
      have ho1M_nn := mid_nonneg hv1.ho10 hcoords.2.2.2.1
      have ho2M_nn := mid_nonneg hv1.ho20 hcoords.2.2.2.2.1
      set vx := (1 + pairSab u) / 2
      set vy := (1 + pairScd u) / 2
      set rb := pairRb u
      set D := vx * vy - rb ^ 2
      set u1 := pairO1 u / D
      set u2 := pairO2 u / D
      set x1 := u1 * rb
      set x2 := u2 * rb
      set P := u1 * u2 * vx * vy
      set detM := (1 - x1) * (1 - x2) - P
      set K00 := (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D
      set K11 := (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D
      set W := valI st.cex * √(K00 * K11) / (4 * π * √D)
      obtain ⟨_, _, _, _, _, _, _, hwu_sq, hwv_sq, _, _⟩ := pair_orth_residuals hadm.1 hv1.hD_pos
      have hK00_nn : 0 ≤ K00 := by
        dsimp only [K00, vx, vy, rb, D]; rw [← hwu_sq]; exact sq_nonneg _
      have hK11_nn : 0 ≤ K11 := by
        dsimp only [K11, vx, vy, rb, D]; rw [← hwv_sq]; exact sq_nonneg _
      have hpi : 0 < π := pi_pos
      have hsD : 0 < √D := sqrt_pos.mpr hv1.hD_pos
      have hW_nn : 0 ≤ W := by dsimp only [W]; have := hv1.hcex; positivity
      have h4pi_m : MemI (4 * π) (Cert.ivScaleInt 4 Cert.ivPi) := by
        simpa only [Int.cast_ofNat] using memI_scaleInt 4 memI_pi
      have h4pi_pos : 0 < (Cert.ivScaleInt 4 Cert.ivPi).lo := by decide
      -- `bK0`, `bK1` linear + remainder bounds:
      set bK0_m := valI s2.cxU.hi * boxMid b.o20 b.o21
      set bK1_m := valI s2.ceU.hi * boxMid b.o10 b.o11
      have hbK0_m_iv := memI_mul (memI_const s2.cxU.hi) hv3.ho2M
      have hbK1_m_iv := memI_mul (memI_const s2.ceU.hi) hv3.ho1M
      have hsRange_m : MemI √D ⟨st.slo, st.shi⟩ := ⟨hv1.hslo_sD, hv1.hshi_sD⟩
      have hk0S_m := memI_divPos hv1.hk00_m hsRange_m hv1.hslo_i
      have hk1S_m := memI_divPos hv1.hk11_m hsRange_m hv1.hslo_i
      obtain ⟨hk0_rad, hvK0_nn⟩ := ival_mid_rad hk0S_m
      obtain ⟨hk1_rad, hvK1_nn⟩ := ival_mid_rad hk1S_m
      set mK0_i := ((Cert.ivDivPos s1.k00 ⟨st.slo, st.shi⟩).lo +
        (Cert.ivDivPos s1.k00 ⟨st.slo, st.shi⟩).hi) / 2
      set vK0_i := Cert.cdiv ((Cert.ivDivPos s1.k00 ⟨st.slo, st.shi⟩).hi -
        (Cert.ivDivPos s1.k00 ⟨st.slo, st.shi⟩).lo) 2
      set mK1_i := ((Cert.ivDivPos s1.k11 ⟨st.slo, st.shi⟩).lo +
        (Cert.ivDivPos s1.k11 ⟨st.slo, st.shi⟩).hi) / 2
      set vK1_i := Cert.cdiv ((Cert.ivDivPos s1.k11 ⟨st.slo, st.shi⟩).hi -
        (Cert.ivDivPos s1.k11 ⟨st.slo, st.shi⟩).lo) 2
      set bK0_sl := (valI s2.cxU.hi * valI mK0_i) / (4 * π)
      set bK1_sl := (valI s2.ceU.hi * valI mK1_i) / (4 * π)
      have hbK0_sl_m := memI_divPos (memI_mul (memI_const s2.cxU.hi) (memI_const mK0_i))
        h4pi_m h4pi_pos
      have hbK1_sl_m := memI_divPos (memI_mul (memI_const s2.ceU.hi) (memI_const mK1_i))
        h4pi_m h4pi_pos
      have hbK0_rem : valI s2.cxU.hi * (pairO2 u - boxMid b.o20 b.o21) *
            (K00 / √D - valI mK0_i) / (4 * π) ≤
          valI (Cert.ivDivPos (Cert.ivMul (Cert.ivMul (Cert.ivConst s2.cxU.hi)
            (Cert.ivConst vK0_i)) (Cert.ivConst s3.do2Hi)) (Cert.ivScaleInt 4 Cert.ivPi)).hi := by
        have hnum : valI s2.cxU.hi * (pairO2 u - boxMid b.o20 b.o21) *
            (K00 / √D - valI mK0_i) ≤ (valI s2.cxU.hi * valI vK0_i) * valI s3.do2Hi := by
          calc valI s2.cxU.hi * (pairO2 u - boxMid b.o20 b.o21) * (K00 / √D - valI mK0_i)
              ≤ |valI s2.cxU.hi * (pairO2 u - boxMid b.o20 b.o21) * (K00 / √D - valI mK0_i)| :=
                le_abs_self _
            _ = valI s2.cxU.hi * |pairO2 u - boxMid b.o20 b.o21| * |K00 / √D - valI mK0_i| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hv2.hcxU_hi_nn]
            _ ≤ valI s2.cxU.hi * valI s3.do2Hi * valI vK0_i := by
                have hv0_nn : 0 ≤ valI vK0_i := by
                  unfold valI; exact div_nonneg (by exact_mod_cast hvK0_nn) (by norm_num)
                have hdo_nn : 0 ≤ valI s3.do2Hi := by
                  unfold valI; exact div_nonneg (by exact_mod_cast hv3.hdo2.2) (by norm_num)
                exact mul_le_mul (mul_le_mul_of_nonneg_left hv3.hdo2.1 hv2.hcxU_hi_nn) hk0_rad
                  (abs_nonneg _) (mul_nonneg hv2.hcxU_hi_nn hdo_nn)
            _ = (valI s2.cxU.hi * valI vK0_i) * valI s3.do2Hi := by ring
        exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
          (memI_divPos (memI_mul (memI_mul (memI_const s2.cxU.hi) (memI_const vK0_i))
            (memI_const s3.do2Hi)) h4pi_m h4pi_pos).2
      have hbK1_rem : valI s2.ceU.hi * (pairO1 u - boxMid b.o10 b.o11) *
            (K11 / √D - valI mK1_i) / (4 * π) ≤
          valI (Cert.ivDivPos (Cert.ivMul (Cert.ivMul (Cert.ivConst s2.ceU.hi)
            (Cert.ivConst vK1_i)) (Cert.ivConst s3.do1Hi)) (Cert.ivScaleInt 4 Cert.ivPi)).hi := by
        have hnum : valI s2.ceU.hi * (pairO1 u - boxMid b.o10 b.o11) *
            (K11 / √D - valI mK1_i) ≤ (valI s2.ceU.hi * valI vK1_i) * valI s3.do1Hi := by
          calc valI s2.ceU.hi * (pairO1 u - boxMid b.o10 b.o11) * (K11 / √D - valI mK1_i)
              ≤ |valI s2.ceU.hi * (pairO1 u - boxMid b.o10 b.o11) * (K11 / √D - valI mK1_i)| :=
                le_abs_self _
            _ = valI s2.ceU.hi * |pairO1 u - boxMid b.o10 b.o11| * |K11 / √D - valI mK1_i| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hv2.hceU_hi_nn]
            _ ≤ valI s2.ceU.hi * valI s3.do1Hi * valI vK1_i := by
                have hv1_nn : 0 ≤ valI vK1_i := by
                  unfold valI; exact div_nonneg (by exact_mod_cast hvK1_nn) (by norm_num)
                have hdo_nn : 0 ≤ valI s3.do1Hi := by
                  unfold valI; exact div_nonneg (by exact_mod_cast hv3.hdo1.2) (by norm_num)
                exact mul_le_mul (mul_le_mul_of_nonneg_left hv3.hdo1.1 hv2.hceU_hi_nn) hk1_rad
                  (abs_nonneg _) (mul_nonneg hv2.hceU_hi_nn hdo_nn)
            _ = (valI s2.ceU.hi * valI vK1_i) * valI s3.do1Hi := by ring
        exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
          (memI_divPos (memI_mul (memI_mul (memI_const s2.ceU.hi) (memI_const vK1_i))
            (memI_const s3.do1Hi)) h4pi_m h4pi_pos).2
      -- Quadratic bound on `pairCAB`:
      have hdSq_m := memI_sq hv1.hd_m
      have h4_m : MemI 4 (Cert.ivConst (4 * Cert.certScale)) := by
        simpa only [valI, Cert.certScale, Int.cast_mul, Int.cast_ofNat,
          mul_div_cancel_right₀ _ (by norm_num : (100000000 : ℝ) ≠ 0)] using
          memI_const (4 * Cert.certScale)
      have hcXsq_m := memI_divPos
        (memI_mul (memI_divPos h4_m hv2.hdenX12_m hv2.hdenX12_pos) (memI_sq hm.2.2.1))
        hdSq_m gdSq
      have hcO12_m := memI_divPos
        (memI_divPos (memI_mul hv1.hvx_m hv1.hvy_m) hdSq_m gdSq)
        hv2.hdenO12_m hv2.hdenO12_pos
      set cXsq_i := (Cert.ivDivPos
        (Cert.ivMul (Cert.ivDivPos (Cert.ivConst (4 * Cert.certScale)) s2.denX12)
          (Cert.ivSq ⟨b.r0, b.r1⟩)) (Cert.ivSq s1.dIv)).hi
      set cO12_i := (Cert.ivDivPos
        (Cert.ivDivPos (Cert.ivMul s1.vx s1.vy) (Cert.ivSq s1.dIv)) s2.denO12).hi
      set cXsq_r := valI cXsq_i
      set cO12_r := valI cO12_i
      have hdenX12_pos_r := lt_of_lt_of_le (valI_pos hv2.hdenX12_pos) hv2.hdenX12_m.1
      have hdenO12_pos_r := lt_of_lt_of_le (valI_pos hv2.hdenO12_pos) hv2.hdenO12_m.1
      have hcXsq_nn : 0 ≤ cXsq_r :=
        (div_nonneg (mul_nonneg (div_nonneg (by norm_num) hdenX12_pos_r.le) (sq_nonneg _))
          (sq_nonneg _)).trans hcXsq_m.2
      have hrb_bo := admissiblePair_root_bounds hadm ho1 ho12
      have hvx_nn : 0 ≤ vx := by dsimp only [vx]; linarith only [hrb_bo.1]
      have hvy_nn : 0 ≤ vy := by dsimp only [vy]; linarith only [hrb_bo.2.2.1]
      have hcO12_nn : 0 ≤ cO12_r :=
        (div_nonneg (div_nonneg (mul_nonneg hvx_nn hvy_nn) (sq_nonneg _))
          hdenO12_pos_r.le).trans hcO12_m.2
      have hcAB_quad : pairCAB x1 x2 P detM ≤
          4 + cXsq_r * (pairO1 u ^ 2 + pairO2 u ^ 2) + cO12_r * (pairO1 u * pairO2 u) := by
        unfold pairCAB
        have ho2_nn : 0 ≤ pairO2 u := ho1.trans ho12
        have hx1_nn : 0 ≤ x1 :=
          mul_nonneg (div_nonneg ho1 hv1.hD_pos.le) hv1.hrb_pos.le
        have hx2_nn : 0 ≤ x2 :=
          mul_nonneg (div_nonneg ho2_nn hv1.hD_pos.le) hv1.hrb_pos.le
        have hd1 : 1 - x1 ^ 2 ≠ 0 := by
          have hlt : x1 ^ 2 < 1 := by
            simpa only [one_pow] using pow_lt_pow_left₀ hv2.hx1_lt hx1_nn two_ne_zero
          linarith only [hlt]
        have hd2 : 1 - x2 ^ 2 ≠ 0 := by
          have hlt : x2 ^ 2 < 1 := by
            simpa only [one_pow] using pow_lt_pow_left₀ hv2.hx2_lt hx2_nn two_ne_zero
          linarith only [hlt]
        have ht1 : 4 / ((1 - x1 ^ 2) * (1 - x2 ^ 2)) ≤
            4 + 4 / ((1 - x1 ^ 2) * (1 - x2 ^ 2)) * rb ^ 2 / D ^ 2 *
              (pairO1 u ^ 2 + pairO2 u ^ 2) := by
          have hid : 4 + 4 * (x1 ^ 2 + x2 ^ 2) / ((1 - x1 ^ 2) * (1 - x2 ^ 2)) -
              4 / ((1 - x1 ^ 2) * (1 - x2 ^ 2)) =
              4 * (x1 ^ 2 * x2 ^ 2) / ((1 - x1 ^ 2) * (1 - x2 ^ 2)) := by
            field_simp [hd1, hd2]; ring
          have hx_sq : x1 ^ 2 + x2 ^ 2 = rb ^ 2 / D ^ 2 * (pairO1 u ^ 2 + pairO2 u ^ 2) := by
            dsimp only [x1, x2, u1, u2]; field_simp [hv1.hD_pos.ne']
          have hnn : 0 ≤ 4 * (x1 ^ 2 * x2 ^ 2) / ((1 - x1 ^ 2) * (1 - x2 ^ 2)) :=
            div_nonneg (by positivity) hdenX12_pos_r.le
          have hrew : 4 * (x1 ^ 2 + x2 ^ 2) / ((1 - x1 ^ 2) * (1 - x2 ^ 2)) =
              4 / ((1 - x1 ^ 2) * (1 - x2 ^ 2)) * rb ^ 2 / D ^ 2 *
                (pairO1 u ^ 2 + pairO2 u ^ 2) := by
            rw [hx_sq]; ring
          linarith only [hid, hnn, hrew]
        have ht2 : P / ((1 - x1) * (1 - x2) * detM) =
            (vx * vy / D ^ 2 / (((1 - x1) * (1 - x2)) * detM)) * (pairO1 u * pairO2 u) := by
          dsimp only [P, u1, u2]; field_simp [hv1.hD_pos.ne']
        have hm1 : 4 / ((1 - x1 ^ 2) * (1 - x2 ^ 2)) * rb ^ 2 / D ^ 2 *
            (pairO1 u ^ 2 + pairO2 u ^ 2) ≤ cXsq_r * (pairO1 u ^ 2 + pairO2 u ^ 2) :=
          mul_le_mul_of_nonneg_right hcXsq_m.2 (add_nonneg (sq_nonneg _) (sq_nonneg _))
        have hm2 : vx * vy / D ^ 2 / (((1 - x1) * (1 - x2)) * detM) *
            (pairO1 u * pairO2 u) ≤ cO12_r * (pairO1 u * pairO2 u) :=
          mul_le_mul_of_nonneg_right hcO12_m.2 (mul_nonneg ho1 ho2_nn)
        linarith only [ht1, ht2, hm1, hm2]
      set o1_m := boxMid b.o10 b.o11
      set o2_m := boxMid b.o20 b.o21
      set cExM_r := 4 + (cXsq_r * (o1_m ^ 2 + o2_m ^ 2) + cO12_r * (o1_m * o2_m))
      set cExSl1_r := 2 * (cXsq_r * o1_m) + cO12_r * o2_m
      set cExSl2_r := 2 * (cXsq_r * o2_m) + cO12_r * o1_m
      set cExCurv_r := cXsq_r + cO12_r / 2
      have hcExM_iv := memI_add h4_m
        (memI_add (memI_mul (memI_const cXsq_i) (memI_add (memI_sq hv3.ho1M) (memI_sq hv3.ho2M)))
          (memI_mul (memI_const cO12_i) (memI_mul hv3.ho1M hv3.ho2M)))
      have hcExSl1_iv := memI_add
        (memI_scaleNat 2 (memI_mul (memI_const cXsq_i) hv3.ho1M))
        (memI_mul (memI_const cO12_i) hv3.ho2M)
      have hcExSl2_iv := memI_add
        (memI_scaleNat 2 (memI_mul (memI_const cXsq_i) hv3.ho2M))
        (memI_mul (memI_const cO12_i) hv3.ho1M)
      have hcExCurv_iv := memI_add (memI_const cXsq_i) (memI_divTwo (memI_const cO12_i))
      have hcAB_exp : 4 + cXsq_r * (pairO1 u ^ 2 + pairO2 u ^ 2) +
            cO12_r * (pairO1 u * pairO2 u) ≤
          cExM_r + cExSl1_r * (pairO1 u - o1_m) + cExSl2_r * (pairO2 u - o2_m) +
            cExCurv_r * ((pairO1 u - o1_m) ^ 2 + (pairO2 u - o2_m) ^ 2) := by
        have hid : cExM_r + cExSl1_r * (pairO1 u - o1_m) + cExSl2_r * (pairO2 u - o2_m) +
            cExCurv_r * ((pairO1 u - o1_m) ^ 2 + (pairO2 u - o2_m) ^ 2) -
            (4 + cXsq_r * (pairO1 u ^ 2 + pairO2 u ^ 2) + cO12_r * (pairO1 u * pairO2 u)) =
            cO12_r / 2 * ((pairO1 u - o1_m) - (pairO2 u - o2_m)) ^ 2 := by
          dsimp only [cExM_r, cExSl1_r, cExSl2_r, cExCurv_r]; ring
        have hnn : 0 ≤ cO12_r / 2 * ((pairO1 u - o1_m) - (pairO2 u - o2_m)) ^ 2 :=
          mul_nonneg (by positivity) (sq_nonneg _)
        linarith only [hid, hnn]
      have hout := pairCost_zero_le_planar_out hadm.1 ho1 (ho1.trans ho12) hv1.hrb_pos hv1.hcex
        hv1.hD_pos hv2.hx1_lt hv2.hx2_lt hv1.hvxy hv2.hdetM_pos hv1.hcorr
      dsimp only at hout
      refine ⟨⟨bK0_m, bK1_m, bK0_sl, bK1_sl, cExSl1_r, cExSl2_r, cExCurv_r,
        mul_nonneg hv2.hcxU_hi_nn ho2M_nn, hbK0_m_iv,
        mul_nonneg hv2.hceU_hi_nn ho1M_nn, hbK1_m_iv,
        (by dsimp only [cExM_r]; positivity : 0 ≤ cExM_r).trans hcExM_iv.2,
        hbK0_sl_m, hbK1_sl_m, hcExSl1_iv, hcExSl2_iv,
        by dsimp only [cExCurv_r]; positivity, hcExCurv_iv, ?_⟩⟩
      dsimp only
      obtain ⟨vExM, hvExM, hcExM_hi_ge⟩ := hide_valI hcExM_iv.2
      obtain ⟨vRem0, hvRem0, hbK0_rem'⟩ := hide_valI hbK0_rem
      obtain ⟨vRem1, hvRem1, hbK1_rem'⟩ := hide_valI hbK1_rem
      rw [← hvExM, ← hvRem0, ← hvRem1]
      have h1_cx := mul_le_mul_of_nonneg_right hv2.hcx_le hK00_nn
      have h1_ce := mul_le_mul_of_nonneg_right hv2.hce_le hK11_nn
      have hcAB_vExM : pairCAB x1 x2 P detM ≤
          vExM + cExSl1_r * (pairO1 u - o1_m) + cExSl2_r * (pairO2 u - o2_m) +
            cExCurv_r * ((pairO1 u - o1_m) ^ 2 + (pairO2 u - o2_m) ^ 2) := by
        linarith only [hcAB_quad, hcAB_exp, hcExM_hi_ge]
      have h1_cab := mul_le_mul_of_nonneg_right hcAB_vExM
        (mul_nonneg hv1.hcex (sqrt_nonneg (K00 * K11)))
      have h4piD_pos : 0 < 4 * π * √D := by positivity
      have hstep := hout.trans (add_le_add le_rfl
        (div_le_div_of_nonneg_right (add_le_add (add_le_add h1_cx h1_ce) h1_cab) h4piD_pos.le))
      have hsplit : (valI s2.cxU.hi * pairO2 u * K00 + valI s2.ceU.hi * pairO1 u * K11 +
            (vExM + cExSl1_r * (pairO1 u - o1_m) + cExSl2_r * (pairO2 u - o2_m) +
              cExCurv_r * ((pairO1 u - o1_m) ^ 2 + (pairO2 u - o2_m) ^ 2)) *
              (valI st.cex * √(K00 * K11))) / (4 * π * √D) =
          (bK0_m * K00 + bK1_m * K11 +
              vExM * (valI st.cex * √(K00 * K11))) / (4 * π * √D) +
            (bK0_sl + cExSl2_r * W) * (pairO2 u - o2_m) +
            (bK1_sl + cExSl1_r * W) * (pairO1 u - o1_m) +
            cExCurv_r * W * ((pairO1 u - o1_m) ^ 2 + (pairO2 u - o2_m) ^ 2) +
            valI s2.cxU.hi * (pairO2 u - o2_m) * (K00 / √D - valI mK0_i) / (4 * π) +
            valI s2.ceU.hi * (pairO1 u - o1_m) * (K11 / √D - valI mK1_i) / (4 * π) := by
        dsimp only [bK0_m, bK1_m, bK0_sl, bK1_sl, W, o1_m, o2_m]
        rw [div_eq_iff h4piD_pos.ne']
        have h4pi_ne : (4 * π : ℝ) ≠ 0 := by positivity
        calc valI s2.cxU.hi * pairO2 u * K00 + valI s2.ceU.hi * pairO1 u * K11 +
              (vExM + cExSl1_r * (pairO1 u - boxMid b.o10 b.o11) +
                cExSl2_r * (pairO2 u - boxMid b.o20 b.o21) +
                cExCurv_r * ((pairO1 u - boxMid b.o10 b.o11) ^ 2 +
                  (pairO2 u - boxMid b.o20 b.o21) ^ 2)) *
                (valI st.cex * √(K00 * K11))
            = (bK0_m * K00 + bK1_m * K11 + vExM * (valI st.cex * √(K00 * K11))) +
              ((valI s2.cxU.hi * valI mK0_i * √D + cExSl2_r * (valI st.cex * √(K00 * K11))) *
                  (pairO2 u - boxMid b.o20 b.o21) +
                (valI s2.ceU.hi * valI mK1_i * √D + cExSl1_r * (valI st.cex * √(K00 * K11))) *
                  (pairO1 u - boxMid b.o10 b.o11) +
                cExCurv_r * (valI st.cex * √(K00 * K11)) *
                  ((pairO1 u - boxMid b.o10 b.o11) ^ 2 +
                    (pairO2 u - boxMid b.o20 b.o21) ^ 2) +
                valI s2.cxU.hi * (pairO2 u - boxMid b.o20 b.o21) *
                  (K00 / √D * √D - valI mK0_i * √D) +
                valI s2.ceU.hi * (pairO1 u - boxMid b.o10 b.o11) *
                  (K11 / √D * √D - valI mK1_i * √D)) := by
              rw [div_mul_cancel₀ _ hsD.ne', div_mul_cancel₀ _ hsD.ne']
              dsimp only [bK0_m, bK1_m]; ring
          _ = _ := by
              field_simp [hpi.ne', hsD.ne']; ring
      dsimp only [W, K00, K11, D, vx, vy, rb, o1_m, o2_m] at hstep hsplit hbK0_rem' hbK1_rem'
      linarith only [hstep, hsplit, hbK0_rem', hbK1_rem']

private structure ModelIn1Valid (u : Fin 4 → E) (st : Cert.PlanarStep)
    (mi1 : Cert.ModelIn1) : Prop where
  hm :
    let vx := (1 + pairSab u) / 2
    let vy := (1 + pairScd u) / 2
    let rb := pairRb u
    let D := vx * vy - rb ^ 2
    let u1 := pairO1 u / D
    let u2 := pairO2 u / D
    let x1 := u1 * rb
    let x2 := u2 * rb
    let P := u1 * u2 * vx * vy
    let detM2 := (1 - x1) * (1 - x2) - 2 * P
    let K00 := (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D
    let K11 := (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D
    let K01 := pairTau u + pairO1 u * pairO2 u * rb / D
    let detK := K00 * K11 - K01 ^ 2
    0 < mi1.detM2.lo ∧ 0 < detM2 ∧ MemI detM2 mi1.detM2 ∧
    0 < detK ∧ 1 / √detK ≤ valI st.invSdetK ∧
    0 < mi1.qpQm.lo ∧ 4 ≤ pairCxe u1 u2 rb D ∧ pairCxe u1 u2 rb D ≤ valI mi1.cExMHi ∧
    ∃ qpQm_lb : ℝ, 0 < qpQm_lb ∧ MemI qpQm_lb mi1.qpQm ∧
      qpQm_lb ≤ pairQp u1 u2 rb D * pairQm u1 u2 rb D

omit [BorelSpace E] in
private theorem planarModelIn1_sound {b : Cert.BoxI} {st : Cert.PlanarStep}
    {s1 : Cert.PlanarS1} {s2 : Cert.PlanarS2} {mi1 : Cert.ModelIn1}
    (hmi1 : Cert.planarModelIn1 b st s1 s2 = some mi1)
    {u : Fin 4 → E} (ho1 : 0 ≤ pairO1 u) (hm : MemBox u b)
    (hv1 : PlanarS1Valid u b st s1) (hv2 : PlanarS2Valid u s2) :
    ModelIn1Valid u st mi1 := by
  unfold Cert.planarModelIn1 at hmi1
  simp only [bindIval_eq, bindInt_eq] at hmi1
  split_ifs at hmi1 with g1 g2 g3
  injection hmi1 with hmi1_eq; subst hmi1_eq
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, ible_false_iff,
    iblt_false_iff] at g1 g2 g3
  rcases hm with ⟨_, _, hr, h_o1, _, _⟩
  set vx := (1 + pairSab u) / 2
  set vy := (1 + pairScd u) / 2
  set rb := pairRb u
  set D := vx * vy - rb ^ 2
  set u1 := pairO1 u / D
  set u2 := pairO2 u / D
  set x1 := u1 * rb
  set x2 := u2 * rb
  set P := u1 * u2 * vx * vy
  set detM := (1 - x1) * (1 - x2) - P
  set detM2 := (1 - x1) * (1 - x2) - 2 * P
  set K00 := (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D
  set K11 := (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D
  set K01 := pairTau u + pairO1 u * pairO2 u * rb / D
  set detK := K00 * K11 - K01 ^ 2
  have hu1_nn : 0 ≤ u1 := div_nonneg ho1 hv1.hD_pos.le
  have hx1_nn : 0 ≤ x1 := mul_nonneg hu1_nn hv1.hrb_pos.le
  have h1mx1 : 0 < 1 - x1 := by linarith only [hv2.hx1_lt]
  have h1px1 : 0 < 1 + x1 := by linarith only [hx1_nn]
  have hdetM2_eq : detM - P = detM2 := by dsimp only [detM, detM2]; ring
  have hdetM2_m := memI_sub hv2.hdetM_m hv2.hp_m
  rw [hdetM2_eq] at hdetM2_m
  have hdetM2_pos := lt_of_lt_of_le (valI_pos g1.1.1) hdetM2_m.1
  have hdetK_m := memI_sub hv1.hkk_m (memI_sq hv1.hk01_m)
  rw [sq_abs] at hdetK_m
  have hdetK_pos := lt_of_lt_of_le (valI_pos g1.1.2) hdetK_m.1
  have hinvS_pos := valI_pos g1.2
  have hinvS_ge : 1 / √detK ≤ valI st.invSdetK := by
    have h1_le : (1 : ℝ) ≤ (valI st.invSdetK) ^ 2 * detK := by
      have hm_inv := memI_mul (memI_sq (memI_const st.invSdetK)) hdetK_m
      have hone : (1 : ℝ) = valI (Cert.ivConst Cert.certScale).lo := by
        unfold valI Cert.ivConst Cert.certScale; norm_num
      rw [hone]; exact (valI_mono g2).trans hm_inv.1
    rw [div_le_iff₀ (sqrt_pos.mpr hdetK_pos)]
    have hnn : 0 ≤ valI st.invSdetK * √detK := mul_nonneg hinvS_pos.le (sqrt_nonneg detK)
    have hsq : (valI st.invSdetK * √detK) ^ 2 = (valI st.invSdetK) ^ 2 * detK := by
      rw [mul_pow, sq_sqrt hdetK_pos.le]
    nlinarith only [h1_le, hsq, hnn]
  have hu1D : u1 * D = pairO1 u := div_mul_cancel₀ _ hv1.hD_pos.ne'
  set s_plus := u2 ^ 2 * (rb + pairO1 u) ^ 2
  set s_minus := u2 ^ 2 * (rb - pairO1 u) ^ 2
  have hs_le : s_minus ≤ s_plus := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg u2)
    have hrb_nn : 0 ≤ rb := hv1.hrb_pos.le
    nlinarith only [hrb_nn, ho1]
  have hs2Iv_m := memI_mul (memI_sq hv2.hu2_m) (memI_sq (memI_add hr h_o1))
  have hqp_m := memI_sub (memI_sq hv2.homx1_m) hs2Iv_m
  have hQm_pos : 0 < pairQm u1 u2 rb D := by
    unfold pairQm
    rw [hu1D]; exact lt_of_lt_of_le (valI_pos g3.1) hqp_m.1
  have hQp_pos : 0 < pairQp u1 u2 rb D := by
    refine lt_of_lt_of_le hQm_pos ?_
    unfold pairQp pairQm
    rw [hu1D]
    have hux : 0 ≤ u1 * rb := hx1_nn
    nlinarith only [hs_le, hux]
  have h1_m : MemI 1 (Cert.ivConst Cert.certScale) := by
    simpa only [valI, Cert.certScale, Int.cast_ofNat,
      div_self (by norm_num : (100000000 : ℝ) ≠ 0)] using memI_const Cert.certScale
  set qpQm_lb := (1 - x1 ^ 2) ^ 2 - 2 * ((1 + x1 ^ 2) * s_plus)
  have hqpQm_m := memI_sub (memI_sq hv2.homx1sq_m)
    (memI_scaleNat 2 (memI_mul (memI_add h1_m (memI_sq hv2.hx1_m)) hs2Iv_m))
  have hqpQm_lb_pos := lt_of_lt_of_le (valI_pos g3.2) hqpQm_m.1
  have hqpQm_le : qpQm_lb ≤ pairQp u1 u2 rb D * pairQm u1 u2 rb D := by
    unfold pairQp pairQm
    rw [hu1D]
    have hid : ((1 + u1 * rb) ^ 2 - s_minus) * ((1 - u1 * rb) ^ 2 - s_plus) - qpQm_lb =
        (1 - u1 * rb) ^ 2 * (s_plus - s_minus) + s_minus * s_plus := by
      dsimp only [qpQm_lb, x1]; ring
    have hnn : 0 ≤ (1 - u1 * rb) ^ 2 * (s_plus - s_minus) + s_minus * s_plus :=
      add_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hs_le))
        (mul_nonneg (by dsimp only [s_minus]; positivity)
          (by dsimp only [s_plus]; positivity))
    linarith only [hid, hnn]
  have hcxe_ge4 : 4 ≤ pairCxe u1 u2 rb D := by
    unfold pairCxe
    have hs_min_nn : 0 ≤ s_minus := by dsimp only [s_minus]; positivity
    have hs_pl_nn : 0 ≤ s_plus := by dsimp only [s_plus]; positivity
    have hqp_ub : pairQp u1 u2 rb D ≤ (1 + x1) ^ 2 := by
      unfold pairQp; rw [hu1D]; dsimp only [x1]; linarith only [hs_min_nn]
    have hqm_ub : pairQm u1 u2 rb D ≤ (1 - x1) ^ 2 := by
      unfold pairQm; rw [hu1D]; dsimp only [x1]; linarith only [hs_pl_nn]
    have h1 : 2 * (1 + x1) / (1 + x1) ^ 2 ≤ 2 * (1 + u1 * rb) / pairQp u1 u2 rb D :=
      div_le_div_of_nonneg_left (by positivity) hQp_pos hqp_ub
    have h2 : 2 * (1 - x1) / (1 - x1) ^ 2 ≤ 2 * (1 - u1 * rb) / pairQm u1 u2 rb D :=
      div_le_div_of_nonneg_left (by positivity) hQm_pos hqm_ub
    have h1mx1sq : 0 < 1 - x1 ^ 2 := by
      have hp := mul_pos h1px1 h1mx1
      have hid : (1 + x1) * (1 - x1) = 1 - x1 ^ 2 := by ring
      linarith only [hp, hid]
    have hsum : 2 * (1 + x1) / (1 + x1) ^ 2 + 2 * (1 - x1) / (1 - x1) ^ 2 =
        4 / (1 - x1 ^ 2) := by
      rw [div_add_div _ _ (pow_ne_zero 2 h1px1.ne') (pow_ne_zero 2 h1mx1.ne'),
        div_eq_div_iff
          (mul_ne_zero (pow_ne_zero 2 h1px1.ne') (pow_ne_zero 2 h1mx1.ne')) h1mx1sq.ne']
      ring
    have h4 : 4 ≤ 4 / (1 - x1 ^ 2) := by
      rw [le_div_iff₀ h1mx1sq]; nlinarith only [sq_nonneg x1]
    have hux : u1 * rb = x1 := rfl
    rw [hux] at h1 h2
    linarith only [h1, h2, hsum, h4]
  have h0_m : MemI 0 (Cert.ivConst 0) := by
    simpa only [valI, Int.cast_zero, zero_div] using memI_const 0
  set rbo1_iv := Cert.ivMax (Cert.ivConst 0) (Cert.ivSub ⟨b.r0, b.r1⟩ (Cert.ivConst b.o11))
  have hrbo1_m : MemI (max 0 (rb - valI b.o11)) rbo1_iv :=
    memI_max h0_m (memI_sub hr (memI_const b.o11))
  have hs_minus_ge : valI (Cert.ivSq s2.u2).lo * valI (Cert.ivSq rbo1_iv).lo ≤ s_minus := by
    have h1 : valI (Cert.ivSq s2.u2).lo ≤ u2 ^ 2 := (memI_sq hv2.hu2_m).1
    have hmax_le : max 0 (rb - valI b.o11) ≤ |rb - pairO1 u| :=
      max_le (abs_nonneg _)
        ((by linarith only [h_o1.2] : rb - valI b.o11 ≤ rb - pairO1 u).trans (le_abs_self _))
    have h2 : valI (Cert.ivSq rbo1_iv).lo ≤ (rb - pairO1 u) ^ 2 :=
      (memI_sq hrbo1_m).1.trans ((pow_le_pow_left₀ (le_max_left _ _) hmax_le 2).trans_eq
        (sq_abs _))
    have hnn1 : 0 ≤ valI (Cert.ivSq s2.u2).lo := by
      unfold valI; exact div_nonneg (by exact_mod_cast ivSq_lo_nonneg s2.u2) (by norm_num)
    have hnn2 : 0 ≤ valI (Cert.ivSq rbo1_iv).lo := by
      unfold valI; exact div_nonneg (by exact_mod_cast ivSq_lo_nonneg rbo1_iv) (by norm_num)
    exact mul_le_mul h1 h2 hnn2 (sq_nonneg u2)
  have hnumCxe_m := memI_sub (memI_scaleNat 4 hv2.homx1sq_m)
    (memI_scaleNat 4 (memI_mul (memI_const (Cert.ivSq s2.u2).lo)
      (memI_const (Cert.ivSq rbo1_iv).lo)))
  have hcxe_div_m := memI_divPos hnumCxe_m hqpQm_m g3.2
  have hcxe_real_le : pairCxe u1 u2 rb D ≤
      (4 * (1 - x1 ^ 2) - 4 * (valI (Cert.ivSq s2.u2).lo * valI (Cert.ivSq rbo1_iv).lo)) /
        qpQm_lb := by
    have hnum_eq : pairCxe u1 u2 rb D =
        (2 * (1 + x1) * pairQm u1 u2 rb D + 2 * (1 - x1) * pairQp u1 u2 rb D) /
          (pairQp u1 u2 rb D * pairQm u1 u2 rb D) := by
      unfold pairCxe; dsimp only [x1]
      rw [div_add_div _ _ hQp_pos.ne' hQm_pos.ne']; ring
    have hnum_le : 2 * (1 + x1) * pairQm u1 u2 rb D + 2 * (1 - x1) * pairQp u1 u2 rb D ≤
        4 * (1 - x1 ^ 2) - 4 * (valI (Cert.ivSq s2.u2).lo * valI (Cert.ivSq rbo1_iv).lo) := by
      have hid : 2 * (1 + x1) * pairQm u1 u2 rb D + 2 * (1 - x1) * pairQp u1 u2 rb D =
          4 * (1 - x1 ^ 2) - 2 * (1 + x1) * s_plus - 2 * (1 - x1) * s_minus := by
        unfold pairQp pairQm; rw [hu1D]; dsimp only [x1]; ring
      have hm1 : 4 * (valI (Cert.ivSq s2.u2).lo * valI (Cert.ivSq rbo1_iv).lo) ≤
          4 * s_minus := mul_le_mul_of_nonneg_left hs_minus_ge (by norm_num)
      have hm2 : 0 ≤ 2 * (1 + x1) * (s_plus - s_minus) :=
        mul_nonneg (by linarith only [h1px1]) (sub_nonneg.mpr hs_le)
      have hid2 : (4 * (1 - x1 ^ 2) - 4 * s_minus) -
          (4 * (1 - x1 ^ 2) - 2 * (1 + x1) * s_plus - 2 * (1 - x1) * s_minus) =
          2 * (1 + x1) * (s_plus - s_minus) := by ring
      linarith only [hid, hm1, hm2, hid2]
    rw [hnum_eq]
    exact (div_le_div_of_nonneg_left (by positivity) hqpQm_lb_pos hqpQm_le).trans
      (div_le_div_of_nonneg_right hnum_le hqpQm_lb_pos.le)
  have hcxe_le := hcxe_real_le.trans hcxe_div_m.2
  simp only [Nat.cast_ofNat] at hqpQm_m hcxe_le
  exact ⟨⟨g1.1.1, hdetM2_pos, hdetM2_m, hdetK_pos, hinvS_ge,
    g3.2, hcxe_ge4, hcxe_le, qpQm_lb, hqpQm_lb_pos, hqpQm_m, hqpQm_le⟩⟩

private theorem planarModelIn_sound {b : Cert.BoxI} {st : Cert.PlanarStep}
    {s1 : Cert.PlanarS1} {s2 : Cert.PlanarS2} {md : Cert.PlanarModel}
    (hmd : Cert.planarModelIn b st s1 s2 = some md)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u)
    (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u) (hm : MemBox u b)
    (hv1 : PlanarS1Valid u b st s1) (hv2 : PlanarS2Valid u s2) :
    PlanarModelValid u b st md := by
  unfold Cert.planarModelIn at hmd
  cases hmi1 : Cert.planarModelIn1 b st s1 s2 with
  | none => rw [hmi1] at hmd; cases hmd
  | some mi1 =>
    rw [hmi1] at hmd; dsimp only at hmd
    cases hmi2 : Cert.planarModelIn2 b s1 s2 mi1 with
    | none => rw [hmi2] at hmd; cases hmd
    | some mi2 =>
      rw [hmi2] at hmd; dsimp only at hmd
      have hv_mi1 := planarModelIn1_sound hmi1 ho1 hm hv1 hv2
      simp only [bindIval_eq, bindInt_eq, Option.some.injEq] at hmd
      subst hmd
      unfold Cert.planarModelIn2 at hmi2
      simp only [bindIval_eq, Option.some.injEq] at hmi2
      subst hmi2
      dsimp only
      rcases hm with ⟨_, _, hr, h_o1, h_o2, _⟩
      have hrb_bo := admissiblePair_root_bounds hadm ho1 ho12
      set vx := (1 + pairSab u) / 2
      set vy := (1 + pairScd u) / 2
      set rb := pairRb u
      set D := vx * vy - rb ^ 2
      set u1 := pairO1 u / D
      set u2 := pairO2 u / D
      set x1 := u1 * rb
      set x2 := u2 * rb
      set P := u1 * u2 * vx * vy
      set detM := (1 - x1) * (1 - x2) - P
      set detM2 := (1 - x1) * (1 - x2) - 2 * P
      set K00 := (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D
      set K11 := (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D
      set K01 := pairTau u + pairO1 u * pairO2 u * rb / D
      set detK := K00 * K11 - K01 ^ 2
      obtain ⟨hdetM2_i, hdetM2_pos, hdetM2_m, hdetK_pos, hinvS_ge,
        hqpQm_i, hcxe_ge4, hcxe_le, qpQm_lb, hqpQm_lb_pos, hqpQm_m, hqpQm_le⟩ := hv_mi1.hm
      obtain ⟨_, _, _, _, _, _, _, hwu_sq, hwv_sq, _, _⟩ := pair_orth_residuals hadm.1 hv1.hD_pos
      have hK00_nn : 0 ≤ K00 := by
        dsimp only [K00, vx, vy, rb, D]; rw [← hwu_sq]; exact sq_nonneg _
      have hK11_nn : 0 ≤ K11 := by
        dsimp only [K11, vx, vy, rb, D]; rw [← hwv_sq]; exact sq_nonneg _
      have ho2_nn : 0 ≤ pairO2 u := ho1.trans ho12
      have hvx_nn : 0 ≤ vx := by dsimp only [vx]; linarith only [hrb_bo.1]
      have hvy_nn : 0 ≤ vy := by dsimp only [vy]; linarith only [hrb_bo.2.2.1]
      have hu1_nn : 0 ≤ u1 := div_nonneg ho1 hv1.hD_pos.le
      have hu2_nn : 0 ≤ u2 := div_nonneg ho2_nn hv1.hD_pos.le
      have h1mx1 : 0 < 1 - x1 := by linarith only [hv2.hx1_lt]
      have h1mx2 : 0 < 1 - x2 := by linarith only [hv2.hx2_lt]
      have hrb_p := hv1.hrb_pos
      have hD_p := hv1.hD_pos
      have hpi : 0 < π := pi_pos
      have h1_m : MemI 1 (Cert.ivConst Cert.certScale) := by
        simpa only [valI, Cert.certScale, Int.cast_ofNat,
          div_self (by norm_num : (100000000 : ℝ) ≠ 0)] using memI_const Cert.certScale
      have h0_m : MemI 0 (Cert.ivConst 0) := by
        simpa only [valI, Int.cast_zero, zero_div] using memI_const 0
      set k2 := u2 * vy * (1 - x2) / detM2
      set k1 := u1 * vx * (1 - x1) / detM2
      have hk2_nn : 0 ≤ k2 := div_nonneg (mul_nonneg (mul_nonneg hu2_nn hvy_nn) h1mx2.le)
        hdetM2_pos.le
      have hk1_nn : 0 ≤ k1 := div_nonneg (mul_nonneg (mul_nonneg hu1_nn hvx_nn) h1mx1.le)
        hdetM2_pos.le
      have hcxm_nn : 0 ≤ pairCxMax u2 vy x1 x2 detM := by
        unfold pairCxMax pairCxp; exact le_trans (by positivity) (le_max_left _ _)
      have hcem_nn : 0 ≤ pairCxMax u1 vx x2 x1 detM := by
        unfold pairCxMax pairCxp; exact le_trans (by positivity) (le_max_left _ _)
      have hqpQm_prod_pos : 0 < pairQp u1 u2 rb D * pairQm u1 u2 rb D :=
        hqpQm_lb_pos.trans_le hqpQm_le
      have hacx_nn : 0 ≤ pairAbsCx2 u1 u2 rb vy D := by
        unfold pairAbsCx2; exact div_nonneg (by positivity) hqpQm_prod_pos.le
      have hace_nn : 0 ≤ pairAbsCe2 u1 u2 rb vx D := by
        unfold pairAbsCe2; exact div_nonneg (by positivity) hqpQm_prod_pos.le
      have hlhs0_nn : 0 ≤ pairAbsCx2 u1 u2 rb vy D +
          (pairCxMax u2 vy x1 x2 detM +
            max 0 (pairCAB x1 x2 P detM - pairCxe u1 u2 rb D) * k2 +
            pairCxMax u1 vx x2 x1 detM * k2 ^ 2) * (4 * k2 * K00 / (π * √detK)) :=
        add_nonneg hacx_nn (mul_nonneg
          (add_nonneg (add_nonneg hcxm_nn (mul_nonneg (le_max_left 0 _) hk2_nn))
            (mul_nonneg hcem_nn (sq_nonneg k2)))
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk2_nn) hK00_nn)
            (mul_nonneg hpi.le (sqrt_nonneg detK))))
      have hlhs1_nn : 0 ≤ pairAbsCe2 u1 u2 rb vx D +
          (pairCxMax u1 vx x2 x1 detM +
            max 0 (pairCAB x1 x2 P detM - pairCxe u1 u2 rb D) * k1 +
            pairCxMax u2 vy x1 x2 detM * k1 ^ 2) * (4 * k1 * K11 / (π * √detK)) :=
        add_nonneg hace_nn (mul_nonneg
          (add_nonneg (add_nonneg hcem_nn (mul_nonneg (le_max_left 0 _) hk1_nn))
            (mul_nonneg hcxm_nn (sq_nonneg k1)))
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk1_nn) hK11_nn)
            (mul_nonneg hpi.le (sqrt_nonneg detK))))
      have hacx_le : pairAbsCx2 u1 u2 rb vy D ≤
          (4 * ((u1 * u2) * (rb * vy) * (1 + u2 ^ 2 * D))) / qpQm_lb := by
        unfold pairAbsCx2
        rw [abs_of_nonneg hu1_nn, abs_of_nonneg hu2_nn]
        have heq : 4 * u1 * u2 * rb * vy * (1 + u2 ^ 2 * D) =
            4 * ((u1 * u2) * (rb * vy) * (1 + u2 ^ 2 * D)) := by ring
        rw [heq]
        exact div_le_div_of_nonneg_left (by positivity) hqpQm_lb_pos hqpQm_le
      have hace_le : pairAbsCe2 u1 u2 rb vx D ≤
          (4 * ((u1 * u2) * (rb * vx) * (1 + u1 ^ 2 * D))) / qpQm_lb := by
        unfold pairAbsCe2
        rw [abs_of_nonneg hu1_nn, abs_of_nonneg hu2_nn]
        have heq : 4 * u1 * u2 * rb * vx * (1 + u1 ^ 2 * D) =
            4 * ((u1 * u2) * (rb * vx) * (1 + u1 ^ 2 * D)) := by ring
        rw [heq]
        exact div_le_div_of_nonneg_left (by positivity) hqpQm_lb_pos hqpQm_le
      have hcab_sub_le : max 0 (pairCAB x1 x2 P detM - pairCxe u1 u2 rb D) ≤
          max 0 (pairCAB x1 x2 P detM - 4) :=
        max_le_max le_rfl (by linarith only [hcxe_ge4])
      have htcx_le : pairCxMax u2 vy x1 x2 detM +
            max 0 (pairCAB x1 x2 P detM - pairCxe u1 u2 rb D) * k2 +
            pairCxMax u1 vx x2 x1 detM * k2 ^ 2 ≤
          pairCxMax u2 vy x1 x2 detM +
            (max 0 (pairCAB x1 x2 P detM - 4) * k2 + pairCxMax u1 vx x2 x1 detM * k2 ^ 2) := by
        have hm0 := mul_le_mul_of_nonneg_right hcab_sub_le hk2_nn
        linarith only [hm0]
      have htce_le : pairCxMax u1 vx x2 x1 detM +
            max 0 (pairCAB x1 x2 P detM - pairCxe u1 u2 rb D) * k1 +
            pairCxMax u2 vy x1 x2 detM * k1 ^ 2 ≤
          pairCxMax u1 vx x2 x1 detM +
            (max 0 (pairCAB x1 x2 P detM - 4) * k1 + pairCxMax u2 vy x1 x2 detM * k1 ^ 2) := by
        have hm0 := mul_le_mul_of_nonneg_right hcab_sub_le hk1_nn
        linarith only [hm0]
      have hfacX_le : 4 * k2 * K00 / (π * √detK) ≤
          4 * (k2 * K00) / π * valI st.invSdetK := by
        have hrew : 4 * k2 * K00 / (π * √detK) = 4 * (k2 * K00) / π * (1 / √detK) := by ring
        rw [hrew]
        exact mul_le_mul_of_nonneg_left hinvS_ge
          (div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hk2_nn hK00_nn)) hpi.le)
      have hfacE_le : 4 * k1 * K11 / (π * √detK) ≤
          4 * (k1 * K11) / π * valI st.invSdetK := by
        have hrew : 4 * k1 * K11 / (π * √detK) = 4 * (k1 * K11) / π * (1 / √detK) := by ring
        rw [hrew]
        exact mul_le_mul_of_nonneg_left hinvS_ge
          (div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hk1_nn hK11_nn)) hpi.le)
      -- Interval enclosures:
      have hu1u2_m := memI_mul hv2.hu1_m hv2.hu2_m
      have hacx_num_m := memI_scaleNat 4
        (memI_mul (memI_mul hu1u2_m (memI_mul hr hv1.hvy_m))
          (memI_add h1_m (memI_mul (memI_sq hv2.hu2_m) hv1.hd_m)))
      have hace_num_m := memI_scaleNat 4
        (memI_mul (memI_mul hu1u2_m (memI_mul hr hv1.hvx_m))
          (memI_add h1_m (memI_mul (memI_sq hv2.hu1_m) hv1.hd_m)))
      have hacx_m := memI_divPos hacx_num_m hqpQm_m hqpQm_i
      have hace_m := memI_divPos hace_num_m hqpQm_m hqpQm_i
      have hk2_m :=
        memI_divPos (memI_mul (memI_mul hv2.hu2_m hv1.hvy_m) hv2.homx2_m) hdetM2_m hdetM2_i
      have hk1_m :=
        memI_divPos (memI_mul (memI_mul hv2.hu1_m hv1.hvx_m) hv2.homx1_m) hdetM2_m hdetM2_i
      have hcxm_m : MemI (pairCxMax u2 vy x1 x2 detM) (Cert.ivMul s2.cxU ⟨b.o20, b.o21⟩) :=
        (cuReal_mul_eq_pairCxMax ho2_nn hvy_nn hv1.hD_pos).symm ▸ memI_mul hv2.hcxU_m h_o2
      have hcem_m : MemI (pairCxMax u1 vx x2 x1 detM) (Cert.ivMul s2.ceU ⟨b.o10, b.o11⟩) :=
        (cuReal_mul_eq_pairCxMax ho1 hvx_nn hv1.hD_pos).symm ▸ memI_mul hv2.hceU_m h_o1
      have h4_m : MemI 4 (Cert.ivConst (4 * Cert.certScale)) := by
        simpa only [valI, Cert.certScale, Int.cast_mul, Int.cast_ofNat,
          mul_div_cancel_right₀ _ (by norm_num : (100000000 : ℝ) ≠ 0)] using
          memI_const (4 * Cert.certScale)
      have hcabM4_m := memI_max h0_m (memI_sub hv2.hcAB_m h4_m)
      have htcx_m := memI_add hcxm_m
        (memI_add (memI_mul hcabM4_m hk2_m) (memI_mul hcem_m (memI_sq hk2_m)))
      have htce_m := memI_add hcem_m
        (memI_add (memI_mul hcabM4_m hk1_m) (memI_mul hcxm_m (memI_sq hk1_m)))
      have hfacX_m := memI_mul
        (memI_divPos (memI_scaleNat 4 (memI_mul hk2_m hv1.hk00_m)) memI_pi (by decide))
        (memI_const st.invSdetK)
      have hfacE_m := memI_mul
        (memI_divPos (memI_scaleNat 4 (memI_mul hk1_m hv1.hk11_m)) memI_pi (by decide))
        (memI_const st.invSdetK)
      have hbK0_iv := memI_add hacx_m (memI_mul htcx_m hfacX_m)
      have hbK1_iv := memI_add hace_m (memI_mul htce_m hfacE_m)
      obtain ⟨vBK0, hvBK0, hbK0_hi⟩ := hide_valI hbK0_iv.2
      obtain ⟨vBK1, hvBK1, hbK1_hi⟩ := hide_valI hbK1_iv.2
      simp only [Nat.cast_ofNat] at hvBK0 hvBK1
      push_cast at hbK0_hi hbK1_hi
      have hbK0_bound := (add_le_add hacx_le (mul_le_mul htcx_le hfacX_le
        (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk2_nn) hK00_nn)
          (mul_nonneg hpi.le (sqrt_nonneg detK)))
        (add_nonneg hcxm_nn (add_nonneg (mul_nonneg (le_max_left 0 _) hk2_nn)
          (mul_nonneg hcem_nn (sq_nonneg k2)))))).trans hbK0_hi
      have hbK1_bound := (add_le_add hace_le (mul_le_mul htce_le hfacE_le
        (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk1_nn) hK11_nn)
          (mul_nonneg hpi.le (sqrt_nonneg detK)))
        (add_nonneg hcem_nn (add_nonneg (mul_nonneg (le_max_left 0 _) hk1_nn)
          (mul_nonneg hcxm_nn (sq_nonneg k1)))))).trans hbK1_hi
      have hbK0_nn := hlhs0_nn.trans hbK0_bound
      have hbK1_nn := hlhs1_nn.trans hbK1_bound
      have hin := pairCost_zero_le_planar_in hadm.1 ho1 ho2_nn hv1.hrb_pos hv1.hcex
        hv1.hD_pos hv2.hx1_lt hv2.hx2_lt hv1.hvxy hdetM2_pos hdetK_pos hv1.hcorr
      dsimp only at hin
      refine ⟨⟨vBK0, vBK1, 0, 0, 0, 0, 0,
        hbK0_nn, by rw [hvBK0]; exact memI_const _,
        hbK1_nn, by rw [hvBK1]; exact memI_const _,
        (by linarith only [hcxe_ge4] : (0 : ℝ) ≤ pairCxe u1 u2 rb D).trans hcxe_le,
        h0_m, h0_m, h0_m, h0_m, le_rfl, h0_m, ?_⟩⟩
      dsimp only
      have hsD : 0 < √D := sqrt_pos.mpr hv1.hD_pos
      have h4piD_pos : 0 < 4 * π * √D := mul_pos (mul_pos (by norm_num) hpi) hsD
      have hm_k0 := mul_le_mul_of_nonneg_right hbK0_bound hK00_nn
      have hm_k1 := mul_le_mul_of_nonneg_right hbK1_bound hK11_nn
      have hm_cxe := mul_le_mul_of_nonneg_right hcxe_le
        (mul_nonneg hv1.hcex (sqrt_nonneg (K00 * K11)))
      have hstep := hin.trans (add_le_add le_rfl
        (div_le_div_of_nonneg_right (add_le_add (add_le_add hm_k0 hm_k1) hm_cxe)
          h4piD_pos.le))
      have hz0 : valI 0 = 0 := by unfold valI; simp
      simp only [Cert.ivConst, hz0, zero_mul, add_zero] at hstep ⊢
      exact hstep

private theorem planarStageModel_sound {b : Cert.BoxI} {st : Cert.PlanarStep}
    {s1 : Cert.PlanarS1} {s2 : Cert.PlanarS2} {s3 : Cert.PlanarS3} {md : Cert.PlanarModel}
    (hmd : Cert.planarStageModel b st s1 s2 s3 = some md)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u)
    (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u) (hm : MemBox u b)
    (hv1 : PlanarS1Valid u b st s1) (hv2 : PlanarS2Valid u s2) (hv3 : PlanarS3Valid u b s3) :
    PlanarModelValid u b st md := by
  unfold Cert.planarStageModel at hmd
  split_ifs at hmd with h_out
  · exact planarModelOut_sound hmd hadm ho1 ho12 hm hv1 hv2 hv3
  · exact planarModelIn_sound hmd hadm ho1 ho12 hm hv1 hv2

private structure PlanarS4Valid (u : Fin 4 → E) (b : Cert.BoxI)
    (s3 : Cert.PlanarS3) (md : Cert.PlanarModel) (s4 : Cert.PlanarS4) : Prop where
  hm : ∃ ck0 ck1 rectM_r cD_r cSKK_r invM_r gM_r cEx_sl1 cEx_sl2 cEx_curv bK0_sl bK1_sl W : ℝ,
    MemI ck0 s4.ck0 ∧ MemI ck1 s4.ck1 ∧
    MemI rectM_r s4.rectM ∧ MemI cD_r s4.cD ∧
    MemI invM_r s3.invM ∧ MemI gM_r s3.gM ∧
    MemI bK0_sl md.bK0Sl ∧ MemI bK1_sl md.bK1Sl ∧
    MemI cEx_sl1 md.cExSl1 ∧ MemI cEx_sl2 md.cExSl2 ∧
    MemI cEx_curv md.cExCurv ∧
    MemI cSKK_r s4.cSKKHi ∧ MemI W s4.cSKKIv ∧
    pairCost u 0 ≤
      (arccos ⟪u 0, u 1⟫ + arccos ⟪u 2, u 3⟫) / (2 * π) +
      (arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 3⟫ + arccos ⟪u 0, u 3⟫ + arccos ⟪u 1, u 2⟫) /
        (4 * π) +
      rectM_r + valI s4.remBilin +
      (-((ck0 * invM_r + (ck0 * (boxMid b.o10 b.o11) ^ 2) * gM_r) / 2) / (4 * π) +
          cD_r * (((1 + boxMid b.b0 b.b1) / 2) / 2)) * (pairSab u - boxMid b.a0 b.a1) +
      (-((ck1 * invM_r + (ck1 * (boxMid b.o20 b.o21) ^ 2) * gM_r) / 2) / (4 * π) +
          cD_r * (((1 + boxMid b.a0 b.a1) / 2) / 2)) * (pairScd u - boxMid b.b0 b.b1) +
      (-(2 * (cD_r * boxMid b.r0 b.r1))) * (pairRb u - boxMid b.r0 b.r1) -
      cD_r * (pairRb u - boxMid b.r0 b.r1) ^ 2 +
      (-(2 * (ck0 * (boxMid b.o10 b.o11 * (((1 + boxMid b.a0 b.a1) / 2) * gM_r)))) /
          (4 * π) + (bK1_sl + cEx_sl1 * W)) * (pairO1 u - boxMid b.o10 b.o11) +
      (-(2 * (ck1 * (boxMid b.o20 b.o21 * (((1 + boxMid b.b0 b.b1) / 2) * gM_r)))) /
          (4 * π) + (bK0_sl + cEx_sl2 * W)) * (pairO2 u - boxMid b.o20 b.o21) +
      cEx_curv * cSKK_r *
        ((pairO1 u - boxMid b.o10 b.o11) ^ 2 + (pairO2 u - boxMid b.o20 b.o21) ^ 2)

/-- One endpoint's second-order remainder in `planarStage4_sound`, bounded term by term. -/
private theorem remainder_le {δ c e P f g gM Q q dHi dL fVar gVar qVar : ℝ}
    (hδ : |δ| ≤ dHi) (he : |c * e| ≤ dL) (hP : |P - f| ≤ fVar) (hg : |g - gM| ≤ gVar)
    (hQ : |Q - q| ≤ qVar) (hgM : 0 ≤ gM) :
    (-δ / 2) * (-c * e) + -(P - f) * (g - gM) + -(Q - q) * (δ / 2) * gM ≤
      dHi / 2 * dL + (fVar * gVar + (dHi / 2 * qVar) * gM) := by
  have hδ2 : |δ| / 2 ≤ dHi / 2 := div_le_div_of_nonneg_right hδ zero_le_two
  have hd2 : 0 ≤ dHi / 2 := (div_nonneg (abs_nonneg δ) zero_le_two).trans hδ2
  have t1 : (-δ / 2) * (-c * e) ≤ dHi / 2 * dL := by
    calc (-δ / 2) * (-c * e) ≤ |δ / 2 * (c * e)| := by
          rw [show (-δ / 2) * (-c * e) = δ / 2 * (c * e) by ring]; exact le_abs_self _
      _ = |δ| / 2 * |c * e| := by rw [abs_mul, abs_div, abs_two]
      _ ≤ dHi / 2 * dL := mul_le_mul hδ2 he (abs_nonneg _) hd2
  have t2 : -(P - f) * (g - gM) ≤ fVar * gVar := by
    calc -(P - f) * (g - gM) ≤ |-(P - f) * (g - gM)| := le_abs_self _
      _ = |P - f| * |g - gM| := by rw [abs_mul, abs_neg]
      _ ≤ fVar * gVar := mul_le_mul hP hg (abs_nonneg _) ((abs_nonneg _).trans hP)
  have t3 : -(Q - q) * (δ / 2) ≤ dHi / 2 * qVar := by
    calc -(Q - q) * (δ / 2) ≤ |-(Q - q) * (δ / 2)| := le_abs_self _
      _ = |δ| / 2 * |Q - q| := by rw [abs_mul, abs_neg, abs_div, abs_two, mul_comm]
      _ ≤ dHi / 2 * qVar := mul_le_mul hδ2 hQ (abs_nonneg _) hd2
  linarith only [t1, t2, mul_le_mul_of_nonneg_right t3 hgM]

omit [BorelSpace E] in
private theorem planarStage4_sound {b : Cert.BoxI} {st : Cert.PlanarStep}
    {s1 : Cert.PlanarS1} {s3 : Cert.PlanarS3} {md : Cert.PlanarModel} {s4 : Cert.PlanarS4}
    (hs4 : Cert.planarStage4 b st s1 s3 md = some s4)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u)
    (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u) (hm : MemBox u b)
    (hv1 : PlanarS1Valid u b st s1) (hv3 : PlanarS3Valid u b s3)
    (hvmd : PlanarModelValid u b st md) :
    PlanarS4Valid u b s3 md s4 := by
  unfold Cert.planarStage4 at hs4
  cases hs4a : Cert.planarStage4a st s3 md with
  | none => rw [hs4a] at hs4; cases hs4
  | some s4a =>
    rw [hs4a] at hs4; dsimp only at hs4
    simp only [bindIval_eq, bindInt_eq, Option.some.injEq] at hs4
    subst hs4
    unfold Cert.planarStage4a at hs4a
    simp only [bindIval_eq, bindInt_eq, Option.some.injEq] at hs4a
    subst hs4a
    obtain ⟨cInv_r, invM_r, gM_r, gSl_r, hcInv_nn, hcInv_m, hinvM_m, hgM_nn, hgM_m, hgSl_m,
      hsec_ineq, hdLMax_le, htan_ineq, hgVar_le⟩ := hv3.hsec
    obtain ⟨bK0_m, bK1_m, bK0_sl, bK1_sl, cEx_sl1, cEx_sl2, cEx_curv,
      hbK0_nn, hbK0_m, hbK1_nn, hbK1_m, hcExM_nn,
      hbK0_sl_m, hbK1_sl_m, hcEx_sl1_m, hcEx_sl2_m, hcEx_curv_nn, hcEx_curv_m, hpc_md⟩ :=
      hvmd.hm
    dsimp only at hpc_md
    rcases hm with ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
    have hrb_bo := admissiblePair_root_bounds hadm ho1 ho12
    set a_m := boxMid b.a0 b.a1
    set b_m := boxMid b.b0 b.b1
    set r_m := boxMid b.r0 b.r1
    set o1_m := boxMid b.o10 b.o11
    set o2_m := boxMid b.o20 b.o21
    set δ_a := pairSab u - a_m
    set δ_b := pairScd u - b_m
    set δ_r := pairRb u - r_m
    set δ_1 := pairO1 u - o1_m
    set δ_2 := pairO2 u - o2_m
    set vx := (1 + pairSab u) / 2
    set vy := (1 + pairScd u) / 2
    set rb := pairRb u
    set D := vx * vy - rb ^ 2
    set vx_m := (1 + a_m) / 2
    set vy_m := (1 + b_m) / 2
    set D_m := vx_m * vy_m - r_m ^ 2
    set K00 := (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D
    set K11 := (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D
    set W := valI st.cex * √(K00 * K11) / (4 * π * √D)
    obtain ⟨_, _, _, _, _, _, _, hwu_sq, hwv_sq, _, _⟩ := pair_orth_residuals hadm.1 hv1.hD_pos
    have hK00_nn : 0 ≤ K00 := by
      dsimp only [K00, vx, vy, rb, D]; rw [← hwu_sq]; exact sq_nonneg _
    have hK11_nn : 0 ≤ K11 := by
      dsimp only [K11, vx, vy, rb, D]; rw [← hwv_sq]; exact sq_nonneg _
    have hpi : 0 < π := pi_pos
    have hsD : 0 < √D := sqrt_pos.mpr hv1.hD_pos
    have h1_m : MemI 1 (Cert.ivConst Cert.certScale) := by
      simpa only [valI, Cert.certScale, Int.cast_ofNat,
        div_self (by norm_num : (100000000 : ℝ) ≠ 0)] using memI_const Cert.certScale
    have h4pi_m : MemI (4 * π) (Cert.ivScaleInt 4 Cert.ivPi) := memI_scaleNat 4 memI_pi
    have h4pi_pos : 0 < (Cert.ivScaleInt 4 Cert.ivPi).lo := by decide
    -- Step A: `invRxy`, AM-GM on `√(K00 * K11)`, `ck0`, `ck1`, and `cSKK`!
    set invRxy_i := (Cert.ivDivPos (Cert.ivConst Cert.certScale) (Cert.ivConst st.rxy)).hi
    have hinvRxy_ge : 1 / valI st.rxy ≤ valI invRxy_i :=
      (memI_divPos h1_m (memI_const st.rxy) hv1.hrxy_i).2
    have hinvRxy_nn : 0 ≤ valI invRxy_i :=
      (show (0 : ℝ) ≤ 1 / valI st.rxy by have := hv1.hrxy; positivity).trans hinvRxy_ge
    have hamgm_KK : √(K00 * K11) ≤ (valI st.rxy * K00 + valI invRxy_i * K11) / 2 := by
      have h1 : √(K00 * K11) ≤ (valI st.rxy * K00 + 1 / valI st.rxy * K11) / 2 := by
        rw [sqrt_mul hK00_nn]
        have hsq : 0 ≤ (valI st.rxy * √K00 - √K11) ^ 2 := sq_nonneg _
        have hexp : (valI st.rxy * √K00 - √K11) ^ 2 =
            (valI st.rxy) ^ 2 * K00 - 2 * valI st.rxy * (√K00 * √K11) + K11 := by
          calc (valI st.rxy * √K00 - √K11) ^ 2
              = (valI st.rxy) ^ 2 * √K00 ^ 2 - 2 * valI st.rxy * (√K00 * √K11) + √K11 ^ 2 := by
                ring
            _ = (valI st.rxy) ^ 2 * K00 - 2 * valI st.rxy * (√K00 * √K11) + K11 := by
                rw [sq_sqrt hK00_nn, sq_sqrt hK11_nn]
        have hmul_pos : 0 < valI st.rxy := hv1.hrxy
        have hdiv := div_nonneg hsq hmul_pos.le
        have hdiv_eq : (valI st.rxy * √K00 - √K11) ^ 2 / valI st.rxy =
            valI st.rxy * K00 + 1 / valI st.rxy * K11 - 2 * (√K00 * √K11) := by
          rw [hexp, div_eq_iff hmul_pos.ne']
          calc (valI st.rxy) ^ 2 * K00 - 2 * valI st.rxy * (√K00 * √K11) + K11
              = (valI st.rxy) ^ 2 * K00 - 2 * valI st.rxy * (√K00 * √K11) +
                  valI st.rxy * (1 / valI st.rxy) * K11 := by
                rw [mul_one_div_cancel hmul_pos.ne', one_mul]
            _ = (valI st.rxy * K00 + 1 / valI st.rxy * K11 - 2 * (√K00 * √K11)) *
                  valI st.rxy := by ring
        linarith only [hdiv, hdiv_eq]
      have hm_inv := mul_le_mul_of_nonneg_right hinvRxy_ge hK11_nn
      linarith only [h1, hm_inv]
    set cExP_i := (Cert.ivMul (Cert.ivConst md.cExM.hi) (Cert.ivConst st.cex)).hi
    have hcExP_ge : valI md.cExM.hi * valI st.cex ≤ valI cExP_i :=
      (memI_mul (memI_const md.cExM.hi) (memI_const st.cex)).2
    have hcExP_nn : 0 ≤ valI cExP_i := (mul_nonneg hcExM_nn hv1.hcex).trans hcExP_ge
    set ck0_i := (Cert.ivAdd md.bK0M
      (Cert.ivDivInt (Cert.ivMul (Cert.ivConst cExP_i) (Cert.ivConst st.rxy)) 2)).hi
    set ck1_i := (Cert.ivAdd md.bK1M
      (Cert.ivDivInt (Cert.ivMul (Cert.ivConst cExP_i) (Cert.ivConst invRxy_i)) 2)).hi
    have hck0_ge : bK0_m + valI cExP_i * valI st.rxy / 2 ≤ valI ck0_i :=
      (memI_add hbK0_m
        (memI_divTwo (memI_mul (memI_const cExP_i) (memI_const st.rxy)))).2
    have hck1_ge : bK1_m + valI cExP_i * valI invRxy_i / 2 ≤ valI ck1_i :=
      (memI_add hbK1_m
        (memI_divTwo (memI_mul (memI_const cExP_i) (memI_const invRxy_i)))).2
    have hck0_nn : 0 ≤ valI ck0_i :=
      (add_nonneg hbK0_nn (div_nonneg (mul_nonneg hcExP_nn hv1.hrxy.le) zero_le_two)).trans
        hck0_ge
    have hck1_nn : 0 ≤ valI ck1_i :=
      (add_nonneg hbK1_nn (div_nonneg (mul_nonneg hcExP_nn hinvRxy_nn) zero_le_two)).trans
        hck1_ge
    have hck_comb : bK0_m * K00 + bK1_m * K11 +
        valI md.cExM.hi * (valI st.cex * √(K00 * K11)) ≤
        valI ck0_i * K00 + valI ck1_i * K11 := by
      have h1 : valI md.cExM.hi * (valI st.cex * √(K00 * K11)) ≤
          valI cExP_i * ((valI st.rxy * K00 + valI invRxy_i * K11) / 2) := by
        calc valI md.cExM.hi * (valI st.cex * √(K00 * K11))
            = (valI md.cExM.hi * valI st.cex) * √(K00 * K11) := by ring
          _ ≤ valI cExP_i * √(K00 * K11) :=
              mul_le_mul_of_nonneg_right hcExP_ge (sqrt_nonneg _)
          _ ≤ valI cExP_i * ((valI st.rxy * K00 + valI invRxy_i * K11) / 2) :=
              mul_le_mul_of_nonneg_left hamgm_KK hcExP_nn
      have hm0 := mul_le_mul_of_nonneg_right hck0_ge hK00_nn
      have hm1 := mul_le_mul_of_nonneg_right hck1_ge hK11_nn
      linarith only [h1, hm0, hm1]
    -- Enclosure of `W` in `⟨0, cSKK⟩`:
    have hk00_hi : K00 ≤ valI s1.k00.hi := hv1.hk00_m.2
    have hk11_hi : K11 ≤ valI s1.k11.hi := hv1.hk11_m.2
    have hsKK_iv := memI_divTwo (memI_add
      (memI_mul (memI_const st.rxy) (memI_const s1.k00.hi))
      (memI_mul (memI_const invRxy_i) (memI_const s1.k11.hi)))
    set sKKHi_i := (Cert.ivDivInt (Cert.ivAdd
      (Cert.ivMul (Cert.ivConst st.rxy) (Cert.ivConst s1.k00.hi))
      (Cert.ivMul (Cert.ivConst invRxy_i) (Cert.ivConst s1.k11.hi))) 2).hi
    have hsKK_iv_hi : (valI st.rxy * valI s1.k00.hi + valI invRxy_i * valI s1.k11.hi) / 2 ≤
        valI sKKHi_i := hsKK_iv.2
    have hsKK_ge : √(K00 * K11) ≤ valI sKKHi_i :=
      hamgm_KK.trans ((div_le_div_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_left hk00_hi hv1.hrxy.le)
          (mul_le_mul_of_nonneg_left hk11_hi hinvRxy_nn)) zero_le_two).trans hsKK_iv_hi)
    set cSKK_i := (Cert.ivDivPos (Cert.ivMul (Cert.ivConst st.cex) (Cert.ivConst sKKHi_i))
      (Cert.ivMul (Cert.ivScaleInt 4 Cert.ivPi) (Cert.ivConst st.slo))).hi
    have h4pislo_pos : 0 < (Cert.ivMul (Cert.ivScaleInt 4 Cert.ivPi)
        (Cert.ivConst st.slo)).lo := by
      unfold Cert.ivMul Cert.ivScaleInt Cert.ivPi Cert.piLoI Cert.ivConst Cert.certScale
      simp only [bindIval_eq, Int.mul_def, show Cert.ible 0 4 = true by decide, ↓reduceIte]
      have hslo_pos := hv1.hslo_i
      have hcond : (Cert.ible 0 (4 * 314159200) && Cert.ible 0 st.slo) = true := by
        simp only [Bool.and_eq_true, ible_iff]; exact ⟨by decide, hslo_pos.le⟩
      rw [if_true_eq hcond]
      dsimp only
      change 0 < (4 * 314159200 * st.slo) / 100000000
      omega
    have hW_mem : MemI W ⟨0, cSKK_i⟩ := by
      have hW_nn : valI 0 ≤ W := by
        unfold valI; simp only [Int.cast_zero, zero_div]
        exact div_nonneg (mul_nonneg hv1.hcex (sqrt_nonneg _)) (by positivity)
      refine ⟨hW_nn, ?_⟩
      calc W = valI st.cex * √(K00 * K11) / (4 * π * √D) := rfl
        _ ≤ valI st.cex * valI sKKHi_i / (4 * π * valI st.slo) := by
            refine div_le_div₀ (mul_nonneg hv1.hcex ((sqrt_nonneg _).trans hsKK_ge))
              (mul_le_mul_of_nonneg_left hsKK_ge hv1.hcex)
              (by have := hv1.hslo; positivity)
              (mul_le_mul_of_nonneg_left hv1.hslo_sD (by positivity))
        _ ≤ valI cSKK_i :=
            (memI_divPos (memI_mul (memI_const st.cex) (memI_const sKKHi_i))
              (memI_mul h4pi_m (memI_const st.slo)) h4pislo_pos).2
    -- Step B: Bilinear expansion of `(ck0 * K00 + ck1 * K11) / (4 * π * √D)`!
    set ck0 := valI ck0_i
    set ck1 := valI ck1_i
    set N_m := ck0 * ((1 - a_m) / 2) + ck1 * ((1 - b_m) / 2)
    set f1_m := o1_m ^ 2 * vx_m
    set f2_m := o2_m ^ 2 * vy_m
    set F_m := ck0 * f1_m + ck1 * f2_m
    have hnM_m := memI_add
      (memI_mul (memI_const ck0_i) (memI_divTwo (memI_sub h1_m hv3.haM)))
      (memI_mul (memI_const ck1_i) (memI_divTwo (memI_sub h1_m hv3.hbM)))
    have hf1M_m := memI_mul (memI_sq hv3.ho1M) hv3.hvxM
    have hf2M_m := memI_mul (memI_sq hv3.ho2M) hv3.hvyM
    have hfM_m := memI_add (memI_mul (memI_const ck0_i) hf1M_m)
      (memI_mul (memI_const ck1_i) hf2M_m)
    set rectM_r := (N_m * invM_r - F_m * gM_r) / (4 * π)
    set cD_r := (F_m * gSl_r - N_m * cInv_r) / (4 * π)
    have hrectM_m := memI_divPos
      (memI_sub (memI_mul hnM_m hinvM_m) (memI_mul hfM_m hgM_m)) h4pi_m h4pi_pos
    have hcD_m := memI_divPos
      (memI_sub (memI_mul hfM_m hgSl_m) (memI_mul hnM_m hcInv_m)) h4pi_m h4pi_pos
    have hvxM_nn : 0 ≤ vx_m := by
      have ha0_nn := hv1.ha0
      have hcoords := box_nonempty_coords ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
      dsimp only [vx_m, a_m]; unfold boxMid valI; push_cast
      have hsum : (0 : ℝ) ≤ (b.a0 : ℝ) + b.a1 := by exact_mod_cast (by omega : 0 ≤ b.a0 + b.a1)
      linarith only [hsum]
    have hvyM_nn : 0 ≤ vy_m := by
      have hb0_nn := hv1.hb0
      have hcoords := box_nonempty_coords ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
      dsimp only [vy_m, b_m]; unfold boxMid valI; push_cast
      have hsum : (0 : ℝ) ≤ (b.b0 : ℝ) + b.b1 := by exact_mod_cast (by omega : 0 ≤ b.b0 + b.b1)
      linarith only [hsum]
    have hFm_nn : 0 ≤ F_m := by dsimp only [F_m, f1_m, f2_m]; positivity
    set N := ck0 * ((1 - pairSab u) / 2) + ck1 * ((1 - pairScd u) / 2)
    set F := ck0 * (pairO1 u ^ 2 * vx) + ck1 * (pairO2 u ^ 2 * vy)
    have hN_nn : 0 ≤ N := by
      dsimp only [N]
      have h1 : 0 ≤ (1 - pairSab u) / 2 := by linarith only [hrb_bo.2.1]
      have h2 : 0 ≤ (1 - pairScd u) / 2 := by linarith only [hrb_bo.2.2.2.1]
      positivity
    have hKK_eq : (ck0 * K00 + ck1 * K11) / (4 * π * √D) =
        (N * (1 / √D) - F * (1 / (D * √D))) / (4 * π) := by
      dsimp only [K00, K11, N, F]
      field_simp [hpi.ne', hsD.ne', hv1.hD_pos.ne']
      ring
    -- Remainder bounds `rem0`, `rem1`, `remBilin`:
    have hf1Var_le : |pairO1 u ^ 2 * vx - f1_m| ≤
        valI (Cert.ivAbs (Cert.ivSub (Cert.ivMul (Cert.ivSq ⟨b.o10, b.o11⟩) s1.vx)
          (Cert.ivMul (Cert.ivSq s3.o1M) s3.vxM))).hi :=
      (memI_abs (memI_sub (memI_mul (memI_sq h_o1) hv1.hvx_m) hf1M_m)).2
    have hf2Var_le : |pairO2 u ^ 2 * vy - f2_m| ≤
        valI (Cert.ivAbs (Cert.ivSub (Cert.ivMul (Cert.ivSq ⟨b.o20, b.o21⟩) s1.vy)
          (Cert.ivMul (Cert.ivSq s3.o2M) s3.vyM))).hi :=
      (memI_abs (memI_sub (memI_mul (memI_sq h_o2) hv1.hvy_m) hf2M_m)).2
    have ho1SqVar_le : |pairO1 u ^ 2 - o1_m ^ 2| ≤
        valI (Cert.ivAbs (Cert.ivSub (Cert.ivSq ⟨b.o10, b.o11⟩) (Cert.ivSq s3.o1M))).hi :=
      (memI_abs (memI_sub (memI_sq h_o1) (memI_sq hv3.ho1M))).2
    have ho2SqVar_le : |pairO2 u ^ 2 - o2_m ^ 2| ≤
        valI (Cert.ivAbs (Cert.ivSub (Cert.ivSq ⟨b.o20, b.o21⟩) (Cert.ivSq s3.o2M))).hi :=
      (memI_abs (memI_sub (memI_sq h_o2) (memI_sq hv3.ho2M))).2
    set f1Var_i := (Cert.ivAbs (Cert.ivSub (Cert.ivMul (Cert.ivSq ⟨b.o10, b.o11⟩) s1.vx)
      (Cert.ivMul (Cert.ivSq s3.o1M) s3.vxM))).hi
    set f2Var_i := (Cert.ivAbs (Cert.ivSub (Cert.ivMul (Cert.ivSq ⟨b.o20, b.o21⟩) s1.vy)
      (Cert.ivMul (Cert.ivSq s3.o2M) s3.vyM))).hi
    set o1SqVar_i := (Cert.ivAbs (Cert.ivSub (Cert.ivSq ⟨b.o10, b.o11⟩)
      (Cert.ivSq s3.o1M))).hi
    set o2SqVar_i := (Cert.ivAbs (Cert.ivSub (Cert.ivSq ⟨b.o20, b.o21⟩)
      (Cert.ivSq s3.o2M))).hi
    have hrem0_m := memI_add
      (memI_mul (memI_divTwo (memI_const s3.daHi)) (memI_const s3.dLMax))
      (memI_add (memI_mul (memI_const f1Var_i) (memI_const s3.gVarMax))
        (memI_mul (memI_mul (memI_divTwo (memI_const s3.daHi)) (memI_const o1SqVar_i))
          hgM_m))
    have hrem1_m := memI_add
      (memI_mul (memI_divTwo (memI_const s3.dbHi)) (memI_const s3.dLMax))
      (memI_add (memI_mul (memI_const f2Var_i) (memI_const s3.gVarMax))
        (memI_mul (memI_mul (memI_divTwo (memI_const s3.dbHi)) (memI_const o2SqVar_i))
          hgM_m))
    have hrem0_real := remainder_le (δ := δ_a) hv3.hda.1 hdLMax_le hf1Var_le hgVar_le
      ho1SqVar_le hgM_nn
    have hrem1_real := remainder_le (δ := δ_b) hv3.hdb.1 hdLMax_le hf2Var_le hgVar_le
      ho2SqVar_le hgM_nn
    have hbilin_m := memI_mul (memI_abs hcD_m)
      (memI_divNat (n := 4) (by norm_num)
        (memI_mul (memI_const s3.daHi) (memI_const s3.dbHi)))
    have hremDiv_m := memI_divPos
      (memI_add (memI_mul (memI_const ck0_i) hrem0_m)
        (memI_mul (memI_const ck1_i) hrem1_m)) h4pi_m h4pi_pos
    obtain ⟨vRemB, hvRemB, hbilin_hi⟩ := hide_valI hbilin_m.2
    obtain ⟨vRemD, hvRemD, hremDiv_hi⟩ := hide_valI hremDiv_m.2
    have hcD_bilin : cD_r * (δ_a * δ_b / 4) ≤ vRemB := by
      have habs : cD_r * (δ_a * δ_b / 4) ≤ |cD_r| * ((valI s3.daHi * valI s3.dbHi) / 4) := by
        calc cD_r * (δ_a * δ_b / 4)
            ≤ |cD_r * (δ_a * δ_b / 4)| := le_abs_self _
          _ = |cD_r| * (|δ_a| * |δ_b| / 4) := by
              rw [abs_mul cD_r, abs_div (δ_a * δ_b), abs_mul δ_a,
                abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          _ ≤ |cD_r| * ((valI s3.daHi * valI s3.dbHi) / 4) :=
              mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right
                  (mul_le_mul hv3.hda.1 hv3.hdb.1 (abs_nonneg _)
                    ((abs_nonneg _).trans hv3.hda.1)) (by norm_num))
                (abs_nonneg _)
      exact habs.trans hbilin_hi
    have hD_diff : D - D_m = vy_m / 2 * δ_a + vx_m / 2 * δ_b - 2 * (r_m * δ_r) - δ_r ^ 2 +
        δ_a * δ_b / 4 := by
      dsimp only [D, D_m, vx, vy, vx_m, vy_m, rb, δ_a, δ_b, δ_r]; ring
    have hrect_expand : (N * (1 / √D) - F * (1 / (D * √D))) / (4 * π) ≤
        rectM_r +
        (-((ck0 * invM_r + (ck0 * o1_m ^ 2) * gM_r) / 2) / (4 * π) + cD_r * (vy_m / 2)) *
          δ_a +
        (-((ck1 * invM_r + (ck1 * o2_m ^ 2) * gM_r) / 2) / (4 * π) + cD_r * (vx_m / 2)) *
          δ_b +
        (-(2 * (cD_r * r_m))) * δ_r - cD_r * δ_r ^ 2 +
        (-(2 * (ck0 * (o1_m * (vx_m * gM_r)))) / (4 * π)) * δ_1 +
        (-(2 * (ck1 * (o2_m * (vy_m * gM_r)))) / (4 * π)) * δ_2 +
        vRemD + vRemB := by
      have hN_le : N * (1 / √D) ≤ N * (invM_r - cInv_r * (D - D_m)) :=
        mul_le_mul_of_nonneg_left hsec_ineq hN_nn
      have hFm_le : -F_m * (1 / (D * √D)) ≤ -F_m * (gM_r - gSl_r * (D - D_m)) := by
        have h := mul_le_mul_of_nonneg_left htan_ineq hFm_nn
        linarith only [h]
      have hdrop1 : 0 ≤ ck0 * vx_m * gM_r * δ_1 ^ 2 := by positivity
      have hdrop2 : 0 ≤ ck1 * vy_m * gM_r * δ_2 ^ 2 := by positivity
      have hid : N * (invM_r - cInv_r * (D - D_m)) +
          (-F_m * (gM_r - gSl_r * (D - D_m)) - (F - F_m) * gM_r -
            (F - F_m) * (1 / (D * √D) - gM_r)) =
          (N_m * invM_r - F_m * gM_r) +
          (F_m * gSl_r - N_m * cInv_r) * (D - D_m) -
          ((ck0 * invM_r + (ck0 * o1_m ^ 2) * gM_r) / 2) * δ_a -
          ((ck1 * invM_r + (ck1 * o2_m ^ 2) * gM_r) / 2) * δ_b -
          (2 * (ck0 * (o1_m * (vx_m * gM_r)))) * δ_1 -
          (2 * (ck1 * (o2_m * (vy_m * gM_r)))) * δ_2 -
          ck0 * vx_m * gM_r * δ_1 ^ 2 - ck1 * vy_m * gM_r * δ_2 ^ 2 +
          ck0 * ((-δ_a / 2) * (-cInv_r * (D - D_m)) +
            -(pairO1 u ^ 2 * vx - f1_m) * (1 / (D * √D) - gM_r) +
            -(pairO1 u ^ 2 - o1_m ^ 2) * (δ_a / 2) * gM_r) +
          ck1 * ((-δ_b / 2) * (-cInv_r * (D - D_m)) +
            -(pairO2 u ^ 2 * vy - f2_m) * (1 / (D * √D) - gM_r) +
            -(pairO2 u ^ 2 - o2_m ^ 2) * (δ_b / 2) * gM_r) := by
        dsimp only [N, N_m, F, F_m, f1_m, f2_m, vx, vy, vx_m, vy_m, δ_a, δ_b, δ_1, δ_2]
        ring
      have hrem_div : (ck0 * ((-δ_a / 2) * (-cInv_r * (D - D_m)) +
            -(pairO1 u ^ 2 * vx - f1_m) * (1 / (D * √D) - gM_r) +
            -(pairO1 u ^ 2 - o1_m ^ 2) * (δ_a / 2) * gM_r) +
          ck1 * ((-δ_b / 2) * (-cInv_r * (D - D_m)) +
            -(pairO2 u ^ 2 * vy - f2_m) * (1 / (D * √D) - gM_r) +
            -(pairO2 u ^ 2 - o2_m ^ 2) * (δ_b / 2) * gM_r)) / (4 * π) ≤ vRemD := by
        have hm0 := mul_le_mul_of_nonneg_left hrem0_real hck0_nn
        have hm1 := mul_le_mul_of_nonneg_left hrem1_real hck1_nn
        exact (div_le_div_of_nonneg_right (add_le_add hm0 hm1) (by positivity)).trans
          hremDiv_hi
      have hF_split : -F * (1 / (D * √D)) =
          -F_m * (1 / (D * √D)) - (F - F_m) * gM_r - (F - F_m) * (1 / (D * √D) - gM_r) := by
        ring
      have hnum_le : N * (1 / √D) - F * (1 / (D * √D)) ≤
          (N_m * invM_r - F_m * gM_r) +
          (F_m * gSl_r - N_m * cInv_r) * (D - D_m) -
          ((ck0 * invM_r + (ck0 * o1_m ^ 2) * gM_r) / 2) * δ_a -
          ((ck1 * invM_r + (ck1 * o2_m ^ 2) * gM_r) / 2) * δ_b -
          (2 * (ck0 * (o1_m * (vx_m * gM_r)))) * δ_1 -
          (2 * (ck1 * (o2_m * (vy_m * gM_r)))) * δ_2 +
          (ck0 * ((-δ_a / 2) * (-cInv_r * (D - D_m)) +
            -(pairO1 u ^ 2 * vx - f1_m) * (1 / (D * √D) - gM_r) +
            -(pairO1 u ^ 2 - o1_m ^ 2) * (δ_a / 2) * gM_r) +
          ck1 * ((-δ_b / 2) * (-cInv_r * (D - D_m)) +
            -(pairO2 u ^ 2 * vy - f2_m) * (1 / (D * √D) - gM_r) +
            -(pairO2 u ^ 2 - o2_m ^ 2) * (δ_b / 2) * gM_r)) := by
        linarith only [hN_le, hFm_le, hF_split, hid, hdrop1, hdrop2]
      have hdiv_step := div_le_div_of_nonneg_right hnum_le (by positivity : 0 ≤ 4 * π)
      have hrew_div : ((N_m * invM_r - F_m * gM_r) +
          (F_m * gSl_r - N_m * cInv_r) * (D - D_m) -
          ((ck0 * invM_r + (ck0 * o1_m ^ 2) * gM_r) / 2) * δ_a -
          ((ck1 * invM_r + (ck1 * o2_m ^ 2) * gM_r) / 2) * δ_b -
          (2 * (ck0 * (o1_m * (vx_m * gM_r)))) * δ_1 -
          (2 * (ck1 * (o2_m * (vy_m * gM_r)))) * δ_2 +
          (ck0 * ((-δ_a / 2) * (-cInv_r * (D - D_m)) +
            -(pairO1 u ^ 2 * vx - f1_m) * (1 / (D * √D) - gM_r) +
            -(pairO1 u ^ 2 - o1_m ^ 2) * (δ_a / 2) * gM_r) +
          ck1 * ((-δ_b / 2) * (-cInv_r * (D - D_m)) +
            -(pairO2 u ^ 2 * vy - f2_m) * (1 / (D * √D) - gM_r) +
            -(pairO2 u ^ 2 - o2_m ^ 2) * (δ_b / 2) * gM_r))) / (4 * π) =
          rectM_r +
          (-((ck0 * invM_r + (ck0 * o1_m ^ 2) * gM_r) / 2) / (4 * π) + cD_r * (vy_m / 2)) *
            δ_a +
          (-((ck1 * invM_r + (ck1 * o2_m ^ 2) * gM_r) / 2) / (4 * π) + cD_r * (vx_m / 2)) *
            δ_b +
          (-(2 * (cD_r * r_m))) * δ_r - cD_r * δ_r ^ 2 +
          (-(2 * (ck0 * (o1_m * (vx_m * gM_r)))) / (4 * π)) * δ_1 +
          (-(2 * (ck1 * (o2_m * (vy_m * gM_r)))) / (4 * π)) * δ_2 +
          cD_r * (δ_a * δ_b / 4) +
          (ck0 * ((-δ_a / 2) * (-cInv_r * (D - D_m)) +
            -(pairO1 u ^ 2 * vx - f1_m) * (1 / (D * √D) - gM_r) +
            -(pairO1 u ^ 2 - o1_m ^ 2) * (δ_a / 2) * gM_r) +
          ck1 * ((-δ_b / 2) * (-cInv_r * (D - D_m)) +
            -(pairO2 u ^ 2 * vy - f2_m) * (1 / (D * √D) - gM_r) +
            -(pairO2 u ^ 2 - o2_m ^ 2) * (δ_b / 2) * gM_r)) / (4 * π) := by
        rw [hD_diff]; dsimp only [rectM_r, cD_r]
        field_simp [hpi.ne']; ring
      linarith only [hdiv_step, hrew_div, hrem_div, hcD_bilin]
    obtain ⟨vCSKK, hvCSKK, hW_hi⟩ := hide_valI hW_mem.2
    have hcurv_W : cEx_curv * W * (δ_1 ^ 2 + δ_2 ^ 2) ≤
        cEx_curv * vCSKK * (δ_1 ^ 2 + δ_2 ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW_hi hcEx_curv_nn)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hlin12 : (-(2 * (ck0 * (o1_m * (vx_m * gM_r)))) / (4 * π)) * δ_1 +
          (bK1_sl + cEx_sl1 * W) * δ_1 +
          (-(2 * (ck1 * (o2_m * (vy_m * gM_r)))) / (4 * π)) * δ_2 +
          (bK0_sl + cEx_sl2 * W) * δ_2 =
        (-(2 * (ck0 * (o1_m * (vx_m * gM_r)))) / (4 * π) + (bK1_sl + cEx_sl1 * W)) * δ_1 +
          (-(2 * (ck1 * (o2_m * (vy_m * gM_r)))) / (4 * π) + (bK0_sl + cEx_sl2 * W)) * δ_2 := by
      ring
    have h4piD_pos : 0 < 4 * π * √D := by positivity
    have hrect_le := (div_le_div_of_nonneg_right hck_comb h4piD_pos.le).trans
      (hKK_eq.trans_le hrect_expand)
    refine ⟨⟨ck0, ck1, rectM_r, cD_r, vCSKK, invM_r, gM_r, cEx_sl1, cEx_sl2, cEx_curv,
      bK0_sl, bK1_sl, W,
      memI_const ck0_i, memI_const ck1_i, hrectM_m, hcD_m, hinvM_m, hgM_m,
      hbK0_sl_m, hbK1_sl_m, hcEx_sl1_m, hcEx_sl2_m, hcEx_curv_m,
      by rw [hvCSKK]; exact memI_const cSKK_i, hW_mem, ?_⟩⟩
    dsimp only
    have hv_add4 (w x y z : Int) : valI (w + x + y + z) = valI w + valI x + valI y + valI z := by
      unfold valI; push_cast; ring
    simp only [Nat.cast_ofNat] at hvRemB
    rw [hv_add4, ← hvRemD, ← hvRemB]
    dsimp only [vx_m, vy_m, δ_a, δ_b, δ_r, δ_1, δ_2, a_m, b_m, r_m, o1_m, o2_m]
      at hpc_md hrect_le hcurv_W hlin12
    linarith only [hpc_md, hrect_le, hcurv_W, hlin12]

omit [BorelSpace E] in
private theorem planarStage5_sound {b : Cert.BoxI} {st : Cert.PlanarStep}
    {s1 : Cert.PlanarS1} {s3 : Cert.PlanarS3} {md : Cert.PlanarModel} {s4 : Cert.PlanarS4}
    (hs5 : Cert.planarStage5 b st s1 s3 md s4 = true)
    {u : Fin 4 → E} (hadm : IsAdmissiblePair u)
    (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u) (hm : MemBox u b)
    (hv1 : PlanarS1Valid u b st s1) (hv3 : PlanarS3Valid u b s3)
    (hv4 : PlanarS4Valid u b s3 md s4) :
    pairCost u 0 ≤ 27735 / 100000 := by
  unfold Cert.planarStage5 at hs5
  cases hs5a : Cert.planarStage5a b st s1 s3 with
  | none => rw [hs5a] at hs5; cases hs5
  | some s5a =>
  rw [hs5a] at hs5; dsimp only at hs5
  cases hs5b : Cert.planarStage5b s1 s3 with
  | none => rw [hs5b] at hs5; cases hs5
  | some s5b =>
  rw [hs5b] at hs5; dsimp only at hs5
  cases hs5c : Cert.planarStage5c st s3 md s4 s5a s5b with
  | none => rw [hs5c] at hs5; cases hs5
  | some s5c =>
    rw [hs5c] at hs5; dsimp only at hs5
    simp only [bindIval_eq, bindInt_eq, ible_iff] at hs5
    unfold Cert.planarStage5a at hs5a
    simp only [bindIval_eq, bindInt_eq] at hs5a
    have g_sch : ((Cert.iblt 0 st.lam &&
        Cert.iblt (if Cert.iblt 0 st.lam then Cert.calcSchurRhsHi b 1 else 0) 0) ||
      (Cert.iblt 0 st.lamM &&
        Cert.iblt (if Cert.iblt 0 st.lamM then Cert.calcSchurRhsHi b (-1) else 0) 0)) =
        false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      rw [if_true_eq h] at hs5a
      cases hs5a
    rw [if_false_eq g_sch] at hs5a
    injection hs5a with hs5a_eq; subst hs5a_eq
    unfold Cert.planarStage5b at hs5b
    cases hsb1 : Cert.planarStage5b1 s1 s3 with
    | none => rw [hsb1] at hs5b; cases hs5b
    | some sb1 =>
      rw [hsb1] at hs5b; dsimp only at hs5b
      simp only [bindIval_eq, bindInt_eq, Option.some.injEq] at hs5b
      subst hs5b
      unfold Cert.planarStage5b1 at hsb1
      simp only [bindIval_eq, bindInt_eq, Option.some.injEq] at hsb1
      subst hsb1
      unfold Cert.planarStage5c at hs5c
      simp only [bindIval_eq, Option.some.injEq] at hs5c
      subst hs5c
      obtain ⟨ck0, ck1, rectM_r, cD_r, cSKK_r, invM_r, gM_r, cEx_sl1, cEx_sl2, cEx_curv,
        bK0_sl, bK1_sl, W, hck0_m, hck1_m, hrectM_m, hcD_m, hinvM_m, hgM_m,
        hbK0_sl_m, hbK1_sl_m, hcEx_sl1_m, hcEx_sl2_m, hcEx_curv_m,
        hcSKKHi_m, hW_mem, hpc_s4⟩ := hv4.hm
      rcases hm with ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
      have hrb_bo := admissiblePair_root_bounds hadm ho1 ho12
      set a_m := boxMid b.a0 b.a1
      set b_m := boxMid b.b0 b.b1
      set r_m := boxMid b.r0 b.r1
      set o1_m := boxMid b.o10 b.o11
      set o2_m := boxMid b.o20 b.o21
      set t_m := boxMid b.t0 b.t1
      set δ_a := pairSab u - a_m
      set δ_b := pairScd u - b_m
      set δ_r := pairRb u - r_m
      set δ_1 := pairO1 u - o1_m
      set δ_2 := pairO2 u - o2_m
      set δ_t := pairTau u - t_m
      set vx_m := (1 + a_m) / 2
      set vy_m := (1 + b_m) / 2
      have hpi : 0 < π := pi_pos
      have h2pi_m : MemI (2 * π) (Cert.ivScaleInt 2 Cert.ivPi) := memI_scaleNat 2 memI_pi
      have h4pi_m : MemI (4 * π) (Cert.ivScaleInt 4 Cert.ivPi) := memI_scaleNat 4 memI_pi
      have h2pi_pos : 0 < (Cert.ivScaleInt 2 Cert.ivPi).lo := by decide
      have h4pi_pos : 0 < (Cert.ivScaleInt 4 Cert.ivPi).lo := by decide
      -- Step C: Schur Lagrange penalties `schP` and `schM` (`planarStage5a`)!
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_imp, iblt_iff,
        iblt_false_iff] at g_sch
      have hc2_eq : valI Cert.c2I = 1322905 / 1000000 := by unfold valI Cert.c2I; norm_num
      have hschP : 0 ≤ (if Cert.iblt 0 st.lam then
          valI (Cert.ivMul (Cert.ivConst st.lam)
            (Cert.ivAdd (Cert.ivSub (Cert.ivAdd (Cert.ivDivInt (Cert.ivAdd s3.aM s3.bM) 2)
              (Cert.ivAdd (Cert.ivDivInt (Cert.ivScaleInt 3 s3.rM) 7)
                (Cert.ivDivInt (Cert.ivScaleInt 16 s3.tM) 35))) (Cert.ivConst Cert.c2I))
              (Cert.ivConst (if Cert.iblt 0 st.lam then Cert.calcSchurRhsHi b 1 else 0)))).hi
          else 0) +
          valI st.lam * (δ_a / 2 + δ_b / 2 + 3 / 7 * δ_r + 16 / 35 * δ_t) := by
        by_cases hlp : Cert.iblt 0 st.lam = true
        · rw [if_true_eq hlp, if_true_eq hlp]
          have hlp_lt : 0 < st.lam := (iblt_iff 0 st.lam).mp hlp
          have hsr : 0 ≤ Cert.calcSchurRhsHi b 1 := by
            have := g_sch.1 hlp_lt; simp only [hlp_lt, ↓reduceIte] at this; exact this
          have hs_ineq := calcSchurRhsHi_sound hadm ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
            (Or.inl rfl) hsr
          push_cast at hs_ineq
          have hmul := mul_nonneg hv1.hlam hs_ineq
          have hlin_m := memI_mul (memI_const st.lam) (memI_add
            (memI_sub (memI_add (memI_divTwo (memI_add hv3.haM hv3.hbM))
              (memI_add
                (memI_divNat (n := 7) (by norm_num) (memI_scaleNat 3 hv3.hrM))
                (memI_divNat (n := 35) (by norm_num) (memI_scaleNat 16 hv3.htM))))
              (memI_const Cert.c2I))
            (memI_const (Cert.calcSchurRhsHi b 1)))
          rw [hc2_eq] at hlin_m
          obtain ⟨vLin, hvLin, hlin_hi⟩ := hide_valI hlin_m.2
          simp only [Nat.cast_ofNat] at hvLin
          push_cast at hlin_hi
          rw [← hvLin]
          have hsplit : valI st.lam * ((pairSab u + pairScd u) / 2 + 3 / 7 * pairRb u +
              1 * (16 / 35) * pairTau u - 1322905 / 1000000 +
              valI (Cert.calcSchurRhsHi b 1)) =
              valI st.lam * (((a_m + b_m) / 2 + (3 * r_m / 7 + 16 * t_m / 35) -
                1322905 / 1000000) + valI (Cert.calcSchurRhsHi b 1)) +
              valI st.lam * (δ_a / 2 + δ_b / 2 + 3 / 7 * δ_r + 16 / 35 * δ_t) := by
            dsimp only [δ_a, δ_b, δ_r, δ_t]; ring
          linarith only [hmul, hsplit, hlin_hi]
        · rw [if_false_eq (Bool.eq_false_iff.mpr hlp)]
          rw [Bool.not_eq_true, iblt_false_iff] at hlp
          have hlam0 : valI st.lam = 0 :=
            le_antisymm ((valI_mono hlp).trans_eq (by unfold valI; simp)) hv1.hlam
          rw [hlam0]; ring_nf; exact le_rfl
      have hschM : 0 ≤ (if Cert.iblt 0 st.lamM then
          valI (Cert.ivMul (Cert.ivConst st.lamM)
            (Cert.ivAdd (Cert.ivSub (Cert.ivAdd (Cert.ivDivInt (Cert.ivAdd s3.aM s3.bM) 2)
              (Cert.ivAdd (Cert.ivDivInt (Cert.ivScaleInt 3 s3.rM) 7)
                (Cert.ivDivInt (Cert.ivScaleInt (-16) s3.tM) 35))) (Cert.ivConst Cert.c2I))
              (Cert.ivConst
                (if Cert.iblt 0 st.lamM then Cert.calcSchurRhsHi b (-1) else 0)))).hi
          else 0) +
          valI st.lamM * (δ_a / 2 + δ_b / 2 + 3 / 7 * δ_r - 16 / 35 * δ_t) := by
        by_cases hlm : Cert.iblt 0 st.lamM = true
        · rw [if_true_eq hlm, if_true_eq hlm]
          have hlm_lt : 0 < st.lamM := (iblt_iff 0 st.lamM).mp hlm
          have hsr : 0 ≤ Cert.calcSchurRhsHi b (-1) := by
            have := g_sch.2 hlm_lt; simp only [hlm_lt, ↓reduceIte] at this; exact this
          have hs_ineq := calcSchurRhsHi_sound hadm ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
            (Or.inr rfl) hsr
          push_cast at hs_ineq
          have hmul := mul_nonneg hv1.hlamM hs_ineq
          have hm16t : MemI (-16 * t_m / 35)
              (Cert.ivDivInt (Cert.ivScaleInt (-16) s3.tM) 35) := by
            simpa only [Int.cast_neg, Int.cast_ofNat] using
              memI_divInt (k := 35) (by norm_num) (memI_scaleInt (-16) hv3.htM)
          have hlin_m := memI_mul (memI_const st.lamM) (memI_add
            (memI_sub (memI_add (memI_divTwo (memI_add hv3.haM hv3.hbM))
              (memI_add
                (memI_divNat (n := 7) (by norm_num) (memI_scaleNat 3 hv3.hrM)) hm16t))
              (memI_const Cert.c2I))
            (memI_const (Cert.calcSchurRhsHi b (-1))))
          rw [hc2_eq] at hlin_m
          obtain ⟨vLin, hvLin, hlin_hi⟩ := hide_valI hlin_m.2
          simp only [Nat.cast_ofNat] at hvLin
          push_cast at hlin_hi
          rw [← hvLin]
          have hsplit : valI st.lamM * ((pairSab u + pairScd u) / 2 + 3 / 7 * pairRb u +
              (-1) * (16 / 35) * pairTau u - 1322905 / 1000000 +
              valI (Cert.calcSchurRhsHi b (-1))) =
              valI st.lamM * (((a_m + b_m) / 2 + (3 * r_m / 7 + -16 * t_m / 35) -
                1322905 / 1000000) + valI (Cert.calcSchurRhsHi b (-1))) +
              valI st.lamM * (δ_a / 2 + δ_b / 2 + 3 / 7 * δ_r - 16 / 35 * δ_t) := by
            dsimp only [δ_a, δ_b, δ_r, δ_t]; ring
          linarith only [hmul, hsplit, hlin_hi]
        · rw [if_false_eq (Bool.eq_false_iff.mpr hlm)]
          rw [Bool.not_eq_true, iblt_false_iff] at hlm
          have hlam0 : valI st.lamM = 0 :=
            le_antisymm ((valI_mono hlm).trans_eq (by unfold valI; simp)) hv1.hlamM
          rw [hlam0]; ring_nf; exact le_rfl
      -- Step D: Star and cross Taylor expansions (`planarStage5a`, `planarStage5b`)!
      have hstar_m := memI_divPos
        (memI_add (memI_qeval s1.qa hv3.haM) (memI_qeval s1.qb hv3.hbM)) h2pi_m h2pi_pos
      obtain ⟨vStar, hvStar, hstar_hi⟩ := hide_valI hstar_m.2
      have hstar_exp : (arccos ⟪u 0, u 1⟫ + arccos ⟪u 2, u 3⟫) / (2 * π) ≤
          vStar +
          (-quadSlope s1.qa a_m / (2 * π)) * δ_a - (valI s1.qa.c2 / (2 * π)) * δ_a ^ 2 +
          (-quadSlope s1.qb b_m / (2 * π)) * δ_b - (valI s1.qb.c2 / (2 * π)) * δ_b ^ 2 := by
        have h1 := hv1.hqa.2.trans_eq (quadEval_taylor s1.qa (pairSab u) a_m)
        have h2 := hv1.hqb.2.trans_eq (quadEval_taylor s1.qb (pairScd u) b_m)
        have hdiv := div_le_div_of_nonneg_right (add_le_add h1 h2)
          (by positivity : 0 ≤ 2 * π)
        have hrew : (quadEval s1.qa a_m - quadSlope s1.qa a_m * δ_a -
              (s1.qa.c2 : ℝ) / 100000000 * δ_a ^ 2 +
            (quadEval s1.qb b_m - quadSlope s1.qb b_m * δ_b -
              (s1.qb.c2 : ℝ) / 100000000 * δ_b ^ 2)) / (2 * π) =
            (quadEval s1.qa a_m + quadEval s1.qb b_m) / (2 * π) +
            (-quadSlope s1.qa a_m / (2 * π)) * δ_a - (valI s1.qa.c2 / (2 * π)) * δ_a ^ 2 +
            (-quadSlope s1.qb b_m / (2 * π)) * δ_b - (valI s1.qb.c2 / (2 * π)) * δ_b ^ 2 := by
          unfold valI; field_simp [hpi.ne']; ring
        change (arccos ⟪u 0, u 1⟫ + arccos ⟪u 2, u 3⟫) / (2 * π) ≤ _
        linarith only [hdiv, hrew, hstar_hi]
      set sac_m := (r_m + o1_m) + (o2_m + t_m)
      set sbd_m := (r_m - o1_m) + (t_m - o2_m)
      set sad_m := (r_m + o1_m) - (o2_m + t_m)
      set sbc_m := (r_m - o1_m) - (t_m - o2_m)
      have hsacM_m := memI_add (memI_add hv3.hrM hv3.ho1M) (memI_add hv3.ho2M hv3.htM)
      have hsbdM_m := memI_add (memI_sub hv3.hrM hv3.ho1M) (memI_sub hv3.htM hv3.ho2M)
      have hsadM_m := memI_sub (memI_add hv3.hrM hv3.ho1M) (memI_add hv3.ho2M hv3.htM)
      have hsbcM_m := memI_sub (memI_sub hv3.hrM hv3.ho1M) (memI_sub hv3.htM hv3.ho2M)
      have hcross_m := memI_divPos
        (memI_add (memI_add (memI_qeval s1.qc0 hsacM_m) (memI_qeval s1.qc1 hsbdM_m))
          (memI_add (memI_qeval s1.qc2 hsadM_m) (memI_qeval s1.qc3 hsbcM_m)))
        h4pi_m h4pi_pos
      set c2Min_i := Cert.imin (Cert.imin s1.qc0.c2 s1.qc1.c2)
        (Cert.imin s1.qc2.c2 s1.qc3.c2)
      have hc2m_0 : valI c2Min_i ≤ valI s1.qc0.c2 := by
        dsimp only [c2Min_i]; simp only [imin_eq]
        exact valI_mono ((min_le_left _ _).trans (min_le_left _ _))
      have hc2m_1 : valI c2Min_i ≤ valI s1.qc1.c2 := by
        dsimp only [c2Min_i]; simp only [imin_eq]
        exact valI_mono ((min_le_left _ _).trans (min_le_right _ _))
      have hc2m_2 : valI c2Min_i ≤ valI s1.qc2.c2 := by
        dsimp only [c2Min_i]; simp only [imin_eq]
        exact valI_mono ((min_le_right _ _).trans (min_le_left _ _))
      have hc2m_3 : valI c2Min_i ≤ valI s1.qc3.c2 := by
        dsimp only [c2Min_i]; simp only [imin_eq]
        exact valI_mono ((min_le_right _ _).trans (min_le_right _ _))
      set sl0 := quadSlope s1.qc0 sac_m
      set sl1 := quadSlope s1.qc1 sbd_m
      set sl2 := quadSlope s1.qc2 sad_m
      set sl3 := quadSlope s1.qc3 sbc_m
      have hcross_exp : (arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 3⟫ +
          arccos ⟪u 0, u 3⟫ + arccos ⟪u 1, u 2⟫) / (4 * π) ≤
          ((quadEval s1.qc0 sac_m + quadEval s1.qc1 sbd_m) +
            (quadEval s1.qc2 sad_m + quadEval s1.qc3 sbc_m)) / (4 * π) +
          (-(((sl0 + sl1) + (sl2 + sl3)) / (4 * π))) * δ_r +
          (-(((sl0 - sl1) + (sl2 - sl3)) / (4 * π))) * δ_1 +
          (-(((sl0 - sl1) - (sl2 - sl3)) / (4 * π))) * δ_2 +
          (-(((sl0 + sl1) - (sl2 + sl3)) / (4 * π))) * δ_t -
          (valI c2Min_i / π) * (δ_r ^ 2 + δ_1 ^ 2 + δ_2 ^ 2 + δ_t ^ 2) := by
        have t0 := hv1.hqc0.2.trans_eq (quadEval_taylor s1.qc0 ⟪u 0, u 2⟫ sac_m)
        have t1 := hv1.hqc1.2.trans_eq (quadEval_taylor s1.qc1 ⟪u 1, u 3⟫ sbd_m)
        have t2 := hv1.hqc2.2.trans_eq (quadEval_taylor s1.qc2 ⟪u 0, u 3⟫ sad_m)
        have t3 := hv1.hqc3.2.trans_eq (quadEval_taylor s1.qc3 ⟪u 1, u 2⟫ sbc_m)
        have c0 := mul_le_mul_of_nonneg_right hc2m_0 (sq_nonneg (⟪u 0, u 2⟫ - sac_m))
        have c1 := mul_le_mul_of_nonneg_right hc2m_1 (sq_nonneg (⟪u 1, u 3⟫ - sbd_m))
        have c2 := mul_le_mul_of_nonneg_right hc2m_2 (sq_nonneg (⟪u 0, u 3⟫ - sad_m))
        have c3 := mul_le_mul_of_nonneg_right hc2m_3 (sq_nonneg (⟪u 1, u 2⟫ - sbc_m))
        have d0 : ⟪u 0, u 2⟫ - sac_m = δ_r + δ_1 + δ_2 + δ_t := by
          rw [hrb_bo.2.2.2.2.2.2.2.2.2.2.2.2.1]
          dsimp only [sac_m, δ_r, δ_1, δ_2, δ_t]; ring
        have d1 : ⟪u 1, u 3⟫ - sbd_m = δ_r - δ_1 - δ_2 + δ_t := by
          rw [hrb_bo.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
          dsimp only [sbd_m, δ_r, δ_1, δ_2, δ_t]; ring
        have d2 : ⟪u 0, u 3⟫ - sad_m = δ_r + δ_1 - δ_2 - δ_t := by
          rw [hrb_bo.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
          dsimp only [sad_m, δ_r, δ_1, δ_2, δ_t]; ring
        have d3 : ⟪u 1, u 2⟫ - sbc_m = δ_r - δ_1 + δ_2 - δ_t := by
          rw [hrb_bo.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
          dsimp only [sbc_m, δ_r, δ_1, δ_2, δ_t]; ring
        unfold valI at c0 c1 c2 c3
        have hsum_le : arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 3⟫ +
            arccos ⟪u 0, u 3⟫ + arccos ⟪u 1, u 2⟫ ≤
            ((quadEval s1.qc0 sac_m + quadEval s1.qc1 sbd_m) +
              (quadEval s1.qc2 sad_m + quadEval s1.qc3 sbc_m)) -
            sl0 * (⟪u 0, u 2⟫ - sac_m) - sl1 * (⟪u 1, u 3⟫ - sbd_m) -
            sl2 * (⟪u 0, u 3⟫ - sad_m) - sl3 * (⟪u 1, u 2⟫ - sbc_m) -
            valI c2Min_i * ((⟪u 0, u 2⟫ - sac_m) ^ 2 + (⟪u 1, u 3⟫ - sbd_m) ^ 2 +
              (⟪u 0, u 3⟫ - sad_m) ^ 2 + (⟪u 1, u 2⟫ - sbc_m) ^ 2) := by
          unfold valI; linarith only [t0, t1, t2, t3, c0, c1, c2, c3]
        refine (div_le_div_of_nonneg_right hsum_le (by positivity)).trans_eq ?_
        rw [d0, d1, d2, d3]
        field_simp [hpi.ne']; ring
      -- Step E: 6-coordinate `bound1dIv_sound` applications (`planarStage5c`, `planarStage5`)!
      have hsl0_m := memI_qslope s1.qc0 hsacM_m
      have hsl1_m := memI_qslope s1.qc1 hsbdM_m
      have hsl2_m := memI_qslope s1.qc2 hsadM_m
      have hsl3_m := memI_qslope s1.qc3 hsbcM_m
      have hsaM_m := memI_qslope s1.qa hv3.haM
      have hsbM_m := memI_qslope s1.qb hv3.hbM
      have hlamSum_m : MemI (valI st.lam + valI st.lamM) (Cert.ivConst (st.lam + st.lamM)) := by
        have h : valI (st.lam + st.lamM) = valI st.lam + valI st.lamM := by
          unfold valI; push_cast; ring
        simpa only [h] using memI_const (st.lam + st.lamM)
      have hlamDiff_m : MemI (valI st.lam - valI st.lamM) (Cert.ivConst (st.lam - st.lamM)) := by
        have h : valI (st.lam - st.lamM) = valI st.lam - valI st.lamM := by
          unfold valI; push_cast; ring
        simpa only [h] using memI_const (st.lam - st.lamM)
      have hslA_m := memI_add (memI_neg (memI_divPos hsaM_m h2pi_m h2pi_pos))
        (memI_add (memI_neg (memI_divPos
          (memI_divTwo (memI_add (memI_mul hck0_m hinvM_m)
            (memI_mul (memI_mul hck0_m (memI_sq hv3.ho1M)) hgM_m)))
          h4pi_m h4pi_pos))
          (memI_add (memI_mul hcD_m (memI_divTwo hv3.hvyM)) (memI_divTwo hlamSum_m)))
      have hslB_m := memI_add (memI_neg (memI_divPos hsbM_m h2pi_m h2pi_pos))
        (memI_add (memI_neg (memI_divPos
          (memI_divTwo (memI_add (memI_mul hck1_m hinvM_m)
            (memI_mul (memI_mul hck1_m (memI_sq hv3.ho2M)) hgM_m)))
          h4pi_m h4pi_pos))
          (memI_add (memI_mul hcD_m (memI_divTwo hv3.hvxM)) (memI_divTwo hlamSum_m)))
      have hslR_m := memI_add
        (memI_sub (memI_neg (memI_divPos
          (memI_add (memI_add hsl0_m hsl1_m) (memI_add hsl2_m hsl3_m)) h4pi_m h4pi_pos))
          (memI_scaleNat 2 (memI_mul hcD_m hv3.hrM)))
        (memI_divNat (n := 7) (by norm_num) (memI_scaleNat 3 hlamSum_m))
      have hslO1_m := memI_add
        (memI_sub (memI_neg (memI_divPos
          (memI_add (memI_sub hsl0_m hsl1_m) (memI_sub hsl2_m hsl3_m)) h4pi_m h4pi_pos))
          (memI_divPos (memI_scaleNat 2
            (memI_mul hck0_m (memI_mul hv3.ho1M (memI_mul hv3.hvxM hgM_m))))
            h4pi_m h4pi_pos))
        (memI_add hbK1_sl_m (memI_mul hcEx_sl1_m hW_mem))
      have hslO2_m := memI_add
        (memI_sub (memI_neg (memI_divPos
          (memI_sub (memI_sub hsl0_m hsl1_m) (memI_sub hsl2_m hsl3_m)) h4pi_m h4pi_pos))
          (memI_divPos (memI_scaleNat 2
            (memI_mul hck1_m (memI_mul hv3.ho2M (memI_mul hv3.hvyM hgM_m))))
            h4pi_m h4pi_pos))
        (memI_add hbK0_sl_m (memI_mul hcEx_sl2_m hW_mem))
      have hslT_m := memI_add
        (memI_neg (memI_divPos
          (memI_sub (memI_add hsl0_m hsl1_m) (memI_add hsl2_m hsl3_m)) h4pi_m h4pi_pos))
        (memI_divNat (n := 35) (by norm_num) (memI_scaleNat 16 hlamDiff_m))
      have hc2Pi_m := memI_divPos (memI_const c2Min_i) memI_pi (by decide)
      have haR_m := memI_add hc2Pi_m hcD_m
      have haO_m := memI_sub hc2Pi_m (memI_mul hcEx_curv_m hcSKKHi_m)
      have hmDa := bound1dIv_sound hslA_m (memI_divPos (memI_const s1.qa.c2) h2pi_m h2pi_pos)
        hv3.hda.1 hv3.hda.2
      have hmDb := bound1dIv_sound hslB_m (memI_divPos (memI_const s1.qb.c2) h2pi_m h2pi_pos)
        hv3.hdb.1 hv3.hdb.2
      have hmDr := bound1dIv_sound hslR_m haR_m hv3.hdr.1 hv3.hdr.2
      have hmDo1 := bound1dIv_sound hslO1_m haO_m hv3.hdo1.1 hv3.hdo1.2
      have hmDo2 := bound1dIv_sound hslO2_m haO_m hv3.hdo2.1 hv3.hdo2.2
      have hmDt := bound1dIv_sound hslT_m hc2Pi_m hv3.hdt.1 hv3.hdt.2
      have htot_val : valI Cert.targetI = 27735 / 100000 := by
        unfold valI Cert.targetI; norm_num
      dsimp only at hs5
      have htot_le := (valI_mono hs5).trans_eq htot_val
      have hv_add (x y : Int) : valI (x + y) = valI x + valI y := by
        unfold valI; push_cast; ring
      have hv_zero : valI 0 = 0 := by unfold valI; simp
      have hv_ite (cond : Bool) (x : Int) :
          valI (if cond then x else 0) = if cond then valI x else 0 := by
        cases cond
        · exact hv_zero
        · rfl
      repeat rw [hv_add] at htot_le
      rw [hv_ite, hv_ite] at htot_le
      obtain ⟨vCross, hvCross, hcross_hi⟩ := hide_valI hcross_m.2
      obtain ⟨vRect, hvRect, hrectM_hi⟩ := hide_valI hrectM_m.2
      obtain ⟨vSchP, hvSchP, hschP'⟩ := hide_nonneg_add hschP
      obtain ⟨vSchM, hvSchM, hschM'⟩ := hide_nonneg_add hschM
      obtain ⟨vDa, hvDa, hmDa'⟩ := hide_valI hmDa
      obtain ⟨vDb, hvDb, hmDb'⟩ := hide_valI hmDb
      obtain ⟨vDr, hvDr, hmDr'⟩ := hide_valI hmDr
      obtain ⟨vDo1, hvDo1, hmDo1'⟩ := hide_valI hmDo1
      obtain ⟨vDo2, hvDo2, hmDo2'⟩ := hide_valI hmDo2
      obtain ⟨vDt, hvDt, hmDt'⟩ := hide_valI hmDt
      simp only [Nat.cast_ofNat] at hvDr hvDo1 hvDo2 hvDt
      push_cast at hmDr' hmDo1' hmDo2' hmDt'
      rw [← hvStar, ← hvCross, ← hvRect, ← hvSchP, ← hvSchM,
        ← hvDa, ← hvDb, ← hvDr, ← hvDo1, ← hvDo2, ← hvDt] at htot_le
      have hcomb :
          ((-quadSlope s1.qa a_m / (2 * π) * δ_a - valI s1.qa.c2 / (2 * π) * δ_a ^ 2 +
              -quadSlope s1.qb b_m / (2 * π) * δ_b - valI s1.qb.c2 / (2 * π) * δ_b ^ 2) +
            (-(((sl0 + sl1) + (sl2 + sl3)) / (4 * π)) * δ_r +
              -(((sl0 - sl1) + (sl2 - sl3)) / (4 * π)) * δ_1 +
              -(((sl0 - sl1) - (sl2 - sl3)) / (4 * π)) * δ_2 +
              -(((sl0 + sl1) - (sl2 + sl3)) / (4 * π)) * δ_t -
              (valI c2Min_i / π) * (δ_r ^ 2 + δ_1 ^ 2 + δ_2 ^ 2 + δ_t ^ 2)) +
            ((-((ck0 * invM_r + (ck0 * o1_m ^ 2) * gM_r) / 2) / (4 * π) + cD_r * (vy_m / 2)) *
                δ_a +
              (-((ck1 * invM_r + (ck1 * o2_m ^ 2) * gM_r) / 2) / (4 * π) + cD_r * (vx_m / 2)) *
                δ_b +
              (-(2 * (cD_r * r_m))) * δ_r - cD_r * δ_r ^ 2 +
              (-(2 * (ck0 * (o1_m * (vx_m * gM_r)))) / (4 * π) + (bK1_sl + cEx_sl1 * W)) * δ_1 +
              (-(2 * (ck1 * (o2_m * (vy_m * gM_r)))) / (4 * π) + (bK0_sl + cEx_sl2 * W)) * δ_2 +
              cEx_curv * cSKK_r * (δ_1 ^ 2 + δ_2 ^ 2)) +
            valI st.lam * (δ_a / 2 + δ_b / 2 + 3 / 7 * δ_r + 16 / 35 * δ_t) +
            valI st.lamM * (δ_a / 2 + δ_b / 2 + 3 / 7 * δ_r - 16 / 35 * δ_t)) =
          ((-(quadSlope s1.qa a_m / (2 * π)) +
                (-((ck0 * invM_r + (ck0 * o1_m ^ 2) * gM_r) / 2 / (4 * π)) +
                  (cD_r * (vy_m / 2) + (valI st.lam + valI st.lamM) / 2))) * δ_a -
              (valI s1.qa.c2 / (2 * π)) * δ_a ^ 2) +
          ((-(quadSlope s1.qb b_m / (2 * π)) +
                (-((ck1 * invM_r + (ck1 * o2_m ^ 2) * gM_r) / 2 / (4 * π)) +
                  (cD_r * (vx_m / 2) + (valI st.lam + valI st.lamM) / 2))) * δ_b -
              (valI s1.qb.c2 / (2 * π)) * δ_b ^ 2) +
          ((-(((sl0 + sl1) + (sl2 + sl3)) / (4 * π)) - 2 * (cD_r * r_m) +
                3 * (valI st.lam + valI st.lamM) / 7) * δ_r -
              (valI c2Min_i / π + cD_r) * δ_r ^ 2) +
          ((-(((sl0 - sl1) + (sl2 - sl3)) / (4 * π)) -
                2 * (ck0 * (o1_m * (vx_m * gM_r))) / (4 * π) +
                (bK1_sl + cEx_sl1 * W)) * δ_1 -
              (valI c2Min_i / π - cEx_curv * cSKK_r) * δ_1 ^ 2) +
          ((-(((sl0 - sl1) - (sl2 - sl3)) / (4 * π)) -
                2 * (ck1 * (o2_m * (vy_m * gM_r))) / (4 * π) +
                (bK0_sl + cEx_sl2 * W)) * δ_2 -
              (valI c2Min_i / π - cEx_curv * cSKK_r) * δ_2 ^ 2) +
          ((-(((sl0 + sl1) - (sl2 + sl3)) / (4 * π)) +
                16 * (valI st.lam - valI st.lamM) / 35) * δ_t -
              (valI c2Min_i / π) * δ_t ^ 2) := by
        ring
      dsimp only [sl0, sl1, sl2, sl3, sac_m, sbd_m, sad_m, sbc_m, vx_m, vy_m,
        δ_a, δ_b, δ_r, δ_1, δ_2, δ_t, a_m, b_m, r_m, o1_m, o2_m, t_m]
        at hpc_s4 hstar_exp hcross_exp hschP' hschM' hcomb
      linarith only [hpc_s4, hstar_exp, hcross_exp, hcross_hi, hrectM_hi,
        hschP', hschM', hmDa', hmDb', hmDr', hmDo1', hmDo2', hmDt', htot_le, hcomb]

private theorem chkPlanar_sound {b : Cert.BoxI} {st : Cert.PlanarStep}
    (hok : Cert.chkPlanar b st = true) : BoxValid (E := E) b := by
  intro u hadm ho1 ho12 hm
  unfold Cert.chkPlanar at hok
  cases hs1 : Cert.planarStage1 b st with
  | none => rw [hs1] at hok; cases hok
  | some s1 =>
  rw [hs1] at hok; dsimp only at hok
  cases hs2 : Cert.planarStage2 b s1 with
  | none => rw [hs2] at hok; cases hok
  | some s2 =>
  rw [hs2] at hok; dsimp only at hok
  cases hs3 : Cert.planarStage3 b st s1 with
  | none => rw [hs3] at hok; cases hok
  | some s3 =>
  rw [hs3] at hok; dsimp only at hok
  cases hmd : Cert.planarStageModel b st s1 s2 s3 with
  | none => rw [hmd] at hok; cases hok
  | some md =>
  rw [hmd] at hok; dsimp only at hok
  cases hs4 : Cert.planarStage4 b st s1 s3 md with
  | none => rw [hs4] at hok; cases hok
  | some s4 =>
    rw [hs4] at hok; dsimp only at hok
    have hv1 := planarStage1_sound hs1 hadm ho1 ho12 hm
    have hv2 := planarStage2_sound hs2 hadm ho1 ho12 hm hv1
    have hv3 := planarStage3_sound hs3 hm hv1
    have hvmd := planarStageModel_sound hmd hadm ho1 ho12 hm hv1 hv2 hv3
    have hv4 := planarStage4_sound hs4 hadm ho1 ho12 hm hv1 hv3 hvmd
    exact planarStage5_sound hok hadm ho1 ho12 hm hv1 hv3 hv4

/-! ### Part 4: Stack-machine soundness (`stepOne`, `runProg`, `checkBox`) and `pairCost_le` -/

private def StackValid (stk : List Cert.BoxI) : Prop :=
  ∀ b ∈ stk, BoxValid (E := E) b

omit [BorelSpace E] in
private theorem splitBox_sound {b : Cert.BoxI} (d : Nat) (m : Int)
    (hL : BoxValid (E := E) (Cert.splitBox b d m).1)
    (hR : BoxValid (E := E) (Cert.splitBox b d m).2) :
    BoxValid (E := E) b := by
  intro u hadm ho1 ho12 ⟨ha, hcd, hr, h_o1, h_o2, ht⟩
  unfold Cert.splitBox at hL hR
  match d with
  | 0 =>
    rcases le_total (pairSab u) (valI m) with h | h
    · exact hL u hadm ho1 ho12 ⟨⟨ha.1, h⟩, hcd, hr, h_o1, h_o2, ht⟩
    · exact hR u hadm ho1 ho12 ⟨⟨h, ha.2⟩, hcd, hr, h_o1, h_o2, ht⟩
  | 1 =>
    rcases le_total (pairScd u) (valI m) with h | h
    · exact hL u hadm ho1 ho12 ⟨ha, ⟨hcd.1, h⟩, hr, h_o1, h_o2, ht⟩
    · exact hR u hadm ho1 ho12 ⟨ha, ⟨h, hcd.2⟩, hr, h_o1, h_o2, ht⟩
  | 2 =>
    rcases le_total (pairRb u) (valI m) with h | h
    · exact hL u hadm ho1 ho12 ⟨ha, hcd, ⟨hr.1, h⟩, h_o1, h_o2, ht⟩
    · exact hR u hadm ho1 ho12 ⟨ha, hcd, ⟨h, hr.2⟩, h_o1, h_o2, ht⟩
  | 3 =>
    rcases le_total (pairO1 u) (valI m) with h | h
    · exact hL u hadm ho1 ho12 ⟨ha, hcd, hr, ⟨h_o1.1, h⟩, h_o2, ht⟩
    · exact hR u hadm ho1 ho12 ⟨ha, hcd, hr, ⟨h, h_o1.2⟩, h_o2, ht⟩
  | 4 =>
    rcases le_total (pairO2 u) (valI m) with h | h
    · exact hL u hadm ho1 ho12 ⟨ha, hcd, hr, h_o1, ⟨h_o2.1, h⟩, ht⟩
    · exact hR u hadm ho1 ho12 ⟨ha, hcd, hr, h_o1, ⟨h, h_o2.2⟩, ht⟩
  | n + 5 =>
    rcases le_total (pairTau u) (valI m) with h | h
    · exact hL u hadm ho1 ho12 ⟨ha, hcd, hr, h_o1, h_o2, ⟨ht.1, h⟩⟩
    · exact hR u hadm ho1 ho12 ⟨ha, hcd, hr, h_o1, h_o2, ⟨h, ht.2⟩⟩

private theorem stepOne_sound {subs : Cert.SubTree}
    (hsubs : Cert.SubTreeAll (BoxValid (E := E)) subs)
    {st : Cert.Step} {stk1 stk2 : List Cert.BoxI}
    (hstep : Cert.stepOne subs st stk1 = some stk2)
    (hpost : StackValid (E := E) stk2) :
    StackValid (E := E) stk1 := by
  cases stk1 with
  | nil => cases hstep
  | cons cur stk =>
    unfold Cert.stepOne at hstep
    have tail_ok (hstk : stk = stk2) (hcur : BoxValid (E := E) cur) :
        StackValid (E := E) (cur :: stk) := by
      subst hstk
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hcur
      · exact hpost x hmem
    cases st with
    | subbox idx =>
      dsimp only at hstep
      cases hl : Cert.lookupSub subs idx with
      | none => rw [hl] at hstep; cases hstep
      | some target =>
        rw [hl] at hstep; dsimp only at hstep; split_ifs at hstep with heq
        injection hstep with hstk
        rw [boxEq_iff] at heq; subst heq
        exact tail_ok hstk (lookupSub_sound hsubs hl)
    | clamp =>
      dsimp only at hstep
      cases hcl : Cert.clampBox cur with
      | none => rw [hcl] at hstep; cases hstep
      | some cur' =>
        rw [hcl] at hstep; dsimp only at hstep; injection hstep with hstk; subst hstk
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · intro u hadm ho1 ho12 hm
          exact hpost cur' (List.mem_cons_self ..) u hadm ho1 ho12
            (clampBox_sound hcl hadm ho1 ho12 hm)
        · exact hpost x (List.mem_cons_of_mem _ hmem)
    | empty =>
      dsimp only at hstep; split_ifs at hstep with hemp
      injection hstep with hstk
      exact tail_ok hstk (boxValid_of_isEmptyBox hemp)
    | split d m =>
      dsimp only at hstep; split_ifs at hstep with hemp
      rw [evalBox_eq, evalBox_eq] at hstep
      injection hstep with hstk; subst hstk
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact splitBox_sound d m
          (hpost _ (List.mem_cons_self ..))
          (hpost _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      · exact hpost x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem))
    | schur sigPos =>
      dsimp only at hstep; split_ifs at hstep with hemp hok
      injection hstep with hstk
      exact tail_ok hstk (chkSchur_sound hok)
    | gram =>
      dsimp only at hstep; split_ifs at hstep with hemp hok
      injection hstep with hstk
      exact tail_ok hstk (chkGram_sound hok)
    | shep mode ia ib ic0 ic1 ic2 ic3 =>
      dsimp only at hstep; split_ifs at hstep with hemp hok
      injection hstep with hstk
      exact tail_ok hstk (chkShep_sound hok)
    | planar p =>
      dsimp only at hstep; split_ifs at hstep with hemp hok
      injection hstep with hstk
      exact tail_ok hstk (chkPlanar_sound hok)

private theorem runProg_sound {subs : Cert.SubTree}
    (hsubs : Cert.SubTreeAll (BoxValid (E := E)) subs)
    {p : Cert.Prog} {stk1 stk2 : List Cert.BoxI}
    (hrun : Cert.runProg subs p stk1 = some stk2)
    (hpost : StackValid (E := E) stk2) :
    StackValid (E := E) stk1 := by
  induction p generalizing stk1 stk2 with
  | step s => exact stepOne_sound hsubs hrun hpost
  | seq p1 p2 ih1 ih2 =>
    unfold Cert.runProg at hrun
    cases hm : Cert.runProg subs p1 stk1 with
    | none => rw [hm] at hrun; cases hrun
    | some stkm =>
      rw [hm] at hrun; dsimp only at hrun
      exact ih1 hm (ih2 hrun hpost)

private theorem checkBox_sound {subs : Cert.SubTree}
    (hsubs : Cert.SubTreeAll (BoxValid (E := E)) subs)
    {p : Cert.Prog} {b : Cert.BoxI}
    (hchk : Cert.checkBox subs p b = true) :
    BoxValid (E := E) b := by
  unfold Cert.checkBox at hchk
  rw [evalBox_eq] at hchk
  dsimp only at hchk
  cases hr : Cert.runProg subs p [b] with
  | none => rw [hr] at hchk; cases hchk
  | some rem =>
    rw [hr] at hchk
    cases rem with
    | nil =>
      have hstk := runProg_sound hsubs hr (fun _ h => by cases h)
      exact hstk b (List.mem_singleton.mpr rfl)
    | cons _ _ => cases hchk

private theorem subTreeAll_imp {P Q : Cert.BoxI → Prop} (hPQ : ∀ b, P b → Q b)
    {t : Cert.SubTree} (ht : Cert.SubTreeAll P t) :
    Cert.SubTreeAll Q t := by
  induction t with
  | empty => trivial
  | leaf _ b => exact hPQ b ht
  | node _ _ _ ihl ihr => exact ⟨ihl ht.1, ihr ht.2⟩

private theorem boxValid_of_certified1 {b : Cert.BoxI} (hc : Cert.Certified1 b) :
    BoxValid (E := E) b := by
  rcases hc with ⟨p, hp⟩
  exact checkBox_sound (subs := .empty) trivial hp

private theorem boxValid_of_certified2 {b : Cert.BoxI} (hc : Cert.Certified2 b) :
    BoxValid (E := E) b := by
  rcases hc with ⟨subs, p, hsubs, hp⟩
  exact checkBox_sound (subTreeAll_imp (fun _ => boxValid_of_certified1) hsubs) hp

private theorem rootBoxI_valid : BoxValid (E := E) Cert.rootBoxI := by
  obtain ⟨subs, p, hsubs, hp⟩ := Cert.rootBoxI_certified
  exact checkBox_sound (subTreeAll_imp (fun _ => boxValid_of_certified2) hsubs) hp

/-- **Zero-threshold matched-pair Gaussian majorant.** Any admissible `4`-tuple of unit vectors has
zero-threshold matched-pair cost at most `27735 / 100000`. -/
theorem pairCost_zero_le {u : Fin 4 → E} (h : IsAdmissiblePair u) :
    pairCost u 0 ≤ 27735 / 100000 := by
  obtain ⟨v, hv_adm, hcost_eq, ho1, ho12⟩ := exists_admissiblePair_wlog h
  rw [hcost_eq]
  have hrb := admissiblePair_root_bounds hv_adm ho1 ho12
  refine rootBoxI_valid v hv_adm ho1 ho12 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold MemI valI Cert.rootBoxI Cert.sminI Cert.certScale
    push_cast; exact ⟨by linarith [hrb.1], by linarith [hrb.2.1]⟩
  · unfold MemI valI Cert.rootBoxI Cert.sminI Cert.certScale
    push_cast; exact ⟨by linarith [hrb.2.2.1], by linarith [hrb.2.2.2.1]⟩
  · unfold MemI valI Cert.rootBoxI Cert.cminI Cert.certScale
    push_cast; exact ⟨by linarith [hrb.2.2.2.2.1], by linarith [hrb.2.2.2.2.2.1]⟩
  · unfold MemI valI Cert.rootBoxI Cert.maxoI
    push_cast; exact ⟨by linarith [hrb.2.2.2.2.2.2.1], by linarith [hrb.2.2.2.2.2.2.2.1]⟩
  · unfold MemI valI Cert.rootBoxI Cert.maxoI
    push_cast
    exact ⟨by linarith [hrb.2.2.2.2.2.2.2.2.1], by linarith [hrb.2.2.2.2.2.2.2.2.2.1]⟩
  · unfold MemI valI Cert.rootBoxI Cert.maxoI
    push_cast
    exact ⟨by linarith [hrb.2.2.2.2.2.2.2.2.2.2.1], by linarith [hrb.2.2.2.2.2.2.2.2.2.2.2.1]⟩

/-- **All-threshold matched-pair Gaussian majorant.** Any admissible `4`-tuple of unit vectors has
matched-pair cost at most `27735 / 100000` at every threshold `t : ℝ`. -/
theorem pairCost_le {u : Fin 4 → E} (h : IsAdmissiblePair u) (t : ℝ) :
    pairCost u t ≤ 27735 / 100000 :=
  (pairCost_le_zero h.1 t).trans (pairCost_zero_le h)

end Space

end Cslib.Circuits.Frontier.Gaussian.PairBound
