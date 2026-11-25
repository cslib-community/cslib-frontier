/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Planar `120°` sectors, boundary normals, and oriented ray crossings

Internal `ℝ × ℝ` geometry for `Z₃`-symmetric `120°` open sectors (`inOpenSector`), oriented ray
crossings (`rayCross`), and Cramer's rule for `(0, 0) ∈ conv(z₀, z₁, z₂)`
(`convex_zero_of_pos_det2`).
-/

-- This proof-only companion is intentionally private; sibling ThreeWayCut modules use import all.
set_option linter.privateModule false

open Real Set
open scoped Interval

namespace Cslib.Circuits.Frontier.TensorRank

private def dot2 (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2 * v.2

private def det2 (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.2 - u.2 * v.1

private def neg2 (z : ℝ × ℝ) : ℝ × ℝ :=
  (-z.1, -z.2)

/-- Outward normals of the three `120°` boundary rays (`60°`, `180°`, `300°`). -/
private noncomputable def normVec : Fin 3 → ℝ × ℝ
  | 0 => (-√3 / 2, 1 / 2)
  | 1 => (0, -1)
  | 2 => (√3 / 2, 1 / 2)

/-- Counterclockwise `120°` rotation on `ℝ × ℝ`. -/
private noncomputable def rot120 (z : ℝ × ℝ) : ℝ × ℝ :=
  (-1 / 2 * z.1 - √3 / 2 * z.2, √3 / 2 * z.1 - 1 / 2 * z.2)

private theorem normVec_sq (c : Fin 3) : (normVec c).1 ^ 2 + (normVec c).2 ^ 2 = 1 := by
  fin_cases c
  · dsimp [normVec]; ring_nf; rw [sq_sqrt (by norm_num)]; norm_num
  · dsimp [normVec]; norm_num
  · dsimp [normVec]; ring_nf; rw [sq_sqrt (by norm_num)]; norm_num

private theorem sum_dot2_normVec (z : ℝ × ℝ) :
    dot2 (normVec 0) z + dot2 (normVec 1) z + dot2 (normVec 2) z = 0 := by
  dsimp [normVec, dot2]
  ring

private theorem dot2_normVec_rot120 (c : Fin 3) (z : ℝ × ℝ) :
    dot2 (normVec (c + 1)) (rot120 z) = dot2 (normVec c) z := by
  fin_cases c
  · change dot2 (normVec 1) (rot120 z) = dot2 (normVec 0) z
    dsimp [normVec, rot120, dot2]; ring
  · change dot2 (normVec 2) (rot120 z) = dot2 (normVec 1) z
    dsimp [normVec, rot120, dot2]; ring_nf; rw [sq_sqrt (by norm_num)]; ring
  · change dot2 (normVec 0) (rot120 z) = dot2 (normVec 2) z
    dsimp [normVec, rot120, dot2]; ring_nf; rw [sq_sqrt (by norm_num)]; ring

private theorem det2_rot120 (z₁ z₂ : ℝ × ℝ) :
    det2 (rot120 z₁) (rot120 z₂) = det2 z₁ z₂ := by
  dsimp [rot120, det2]
  ring_nf
  rw [sq_sqrt (by norm_num)]
  ring

private theorem dot2_neg2 (u z : ℝ × ℝ) : dot2 u (neg2 z) = -dot2 u z := by
  dsimp [dot2, neg2]
  ring

private theorem det2_neg2 (z₁ z₂ : ℝ × ℝ) : det2 (neg2 z₁) (neg2 z₂) = det2 z₁ z₂ := by
  dsimp [det2, neg2]
  ring

/-- The `c`-th open `120°` sector: strictly negative on `normVec c` and strictly positive on
`normVec (c + 2)`. -/
private def inOpenSector (c : Fin 3) (z : ℝ × ℝ) : Prop :=
  dot2 (normVec c) z < 0 ∧ 0 < dot2 (normVec (c + 2)) z

private theorem inOpenSector_rot120 (c : Fin 3) (z : ℝ × ℝ) :
    inOpenSector (c + 1) (rot120 z) ↔ inOpenSector c z := by
  have h2 : (c + 1) + 2 = (c + 2) + 1 := by fin_cases c <;> decide
  simp only [inOpenSector, h2, dot2_normVec_rot120]

private theorem inOpenSector_unique {c₁ c₂ : Fin 3} {z : ℝ × ℝ}
    (h₁ : inOpenSector c₁ z) (h₂ : inOpenSector c₂ z) : c₁ = c₂ := by
  by_contra hne
  have h : c₂ + 2 = c₁ ∨ c₁ + 2 = c₂ := by fin_cases c₁ <;> fin_cases c₂ <;> simp_all
  rcases h with rfl | rfl <;> linarith only [h₁.1, h₁.2, h₂.1, h₂.2]

private theorem exists_inOpenSector_of_ne_zero {z : ℝ × ℝ}
    (hz : ∀ c : Fin 3, dot2 (normVec c) z ≠ 0) : ∃ c : Fin 3, inOpenSector c z := by
  have hsum := sum_dot2_normVec z
  rcases lt_or_gt_of_ne (hz 0) with h0 | h0 <;>
    rcases lt_or_gt_of_ne (hz 1) with h1 | h1 <;>
    rcases lt_or_gt_of_ne (hz 2) with h2 | h2
  · exfalso; linarith only [hsum, h0, h1, h2]
  · exact ⟨0, h0, h2⟩
  · exact ⟨2, h2, h1⟩
  · exact ⟨0, h0, h2⟩
  · exact ⟨1, h1, h0⟩
  · exact ⟨1, h1, h0⟩
  · exact ⟨2, h2, h1⟩
  · exfalso; linarith only [hsum, h0, h1, h2]

/-- Oriented crossing of the positive boundary ray `{w | dot2 (normVec c) w = 0}` between `z₁` and
`z₂`: opposite signs on `normVec c` paired with the matching orientation sign on `det2 z₁ z₂`. -/
private def rayCross (c : Fin 3) (z₁ z₂ : ℝ × ℝ) : Prop :=
  (dot2 (normVec c) z₁ < 0 ∧ 0 < dot2 (normVec c) z₂ ∧ 0 < det2 z₁ z₂) ∨
    (dot2 (normVec c) z₂ < 0 ∧ 0 < dot2 (normVec c) z₁ ∧ det2 z₁ z₂ < 0)

private theorem rayCross_rot120 (c : Fin 3) (z₁ z₂ : ℝ × ℝ) :
    rayCross (c + 1) (rot120 z₁) (rot120 z₂) ↔ rayCross c z₁ z₂ := by
  simp only [rayCross, dot2_normVec_rot120, det2_rot120]

private theorem rayCross_comm (c : Fin 3) (z₁ z₂ : ℝ × ℝ) :
    rayCross c z₁ z₂ ↔ rayCross c z₂ z₁ := by
  have hdet : det2 z₂ z₁ = -det2 z₁ z₂ := by dsimp [det2]; ring
  simp only [rayCross, hdet, Left.neg_pos_iff, Left.neg_neg_iff]
  exact or_comm

private theorem rayCross_disjoint_neg2 (c : Fin 3) (z₁ z₂ : ℝ × ℝ) :
    ¬(rayCross c z₁ z₂ ∧ rayCross c (neg2 z₁) (neg2 z₂)) := by
  simp only [rayCross, dot2_neg2, det2_neg2]
  rintro ⟨⟨h1, h2, hd⟩ | ⟨h1, h2, hd⟩, ⟨h3, h4, hd'⟩ | ⟨h3, h4, hd'⟩⟩ <;>
    linarith only [h1, h2, h3, h4, hd, hd']

private theorem rayCross_or_neg2_imp_mem_uIoc (c : Fin 3) (z₁ z₂ : ℝ × ℝ)
    (h : rayCross c z₁ z₂ ∨ rayCross c (neg2 z₁) (neg2 z₂)) :
    (0 : ℝ) ∈ Ι (dot2 (normVec c) z₁) (dot2 (normVec c) z₂) := by
  rw [mem_uIoc]
  simp only [rayCross, dot2_neg2, det2_neg2] at h
  rcases h with (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) | (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩)
  · exact Or.inl ⟨h1, h2.le⟩
  · exact Or.inr ⟨h1, h2.le⟩
  · exact Or.inr ⟨by linarith only [h2], by linarith only [h1]⟩
  · exact Or.inl ⟨by linarith only [h2], by linarith only [h1]⟩

/-- When `z₁ ∈ S_c` and `z₂ ∈ S_{c + 1}`, a positive determinant crosses ray `c`, while a negative
determinant crosses *both* rays `c + 1` and `c + 2`. -/
private theorem rayCross_of_adj_sectors_zero {z₁ z₂ : ℝ × ℝ}
    (h₁ : inOpenSector 0 z₁) (h₂ : inOpenSector 1 z₂) :
    (0 < det2 z₁ z₂ → rayCross 0 z₁ z₂) ∧
      (det2 z₁ z₂ < 0 → rayCross 1 z₁ z₂ ∧ rayCross 2 z₁ z₂) := by
  change dot2 (normVec 0) z₁ < 0 ∧ 0 < dot2 (normVec 2) z₁ at h₁
  change dot2 (normVec 1) z₂ < 0 ∧ 0 < dot2 (normVec 0) z₂ at h₂
  refine ⟨fun hd => Or.inl ⟨h₁.1, h₂.2, hd⟩, fun hd => ?_⟩
  have hid1 : dot2 (normVec 2) z₁ * dot2 (normVec 0) z₂ -
      dot2 (normVec 0) z₁ * dot2 (normVec 2) z₂ = √3 / 2 * det2 z₁ z₂ := by
    dsimp [normVec, dot2, det2]
    ring
  have hid2 : dot2 (normVec 1) z₁ * dot2 (normVec 2) z₂ -
      dot2 (normVec 2) z₁ * dot2 (normVec 1) z₂ = √3 / 2 * det2 z₁ z₂ := by
    dsimp [normVec, dot2, det2]
    ring
  have hsqrt3 : (0 : ℝ) < √3 := sqrt_pos.mpr (by norm_num)
  have hrhs_neg : √3 / 2 * det2 z₁ z₂ < 0 := mul_neg_of_pos_of_neg (by positivity) hd
  have hprod_pos : 0 < dot2 (normVec 2) z₁ * dot2 (normVec 0) z₂ := mul_pos h₁.2 h₂.2
  have hn0z1_neg := h₁.1
  have hn2z2_neg : dot2 (normVec 2) z₂ < 0 := by
    by_contra! hge
    have hle : dot2 (normVec 0) z₁ * dot2 (normVec 2) z₂ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hn0z1_neg.le hge
    linarith only [hid1, hrhs_neg, hprod_pos, hle]
  have hprod2_neg : dot2 (normVec 2) z₁ * dot2 (normVec 1) z₂ < 0 :=
    mul_neg_of_pos_of_neg h₁.2 h₂.1
  have hn1z1_pos : 0 < dot2 (normVec 1) z₁ := by
    by_contra! hle
    have hge : 0 ≤ dot2 (normVec 1) z₁ * dot2 (normVec 2) z₂ :=
      mul_nonneg_of_nonpos_of_nonpos hle hn2z2_neg.le
    linarith only [hid2, hrhs_neg, hprod2_neg, hge]
  exact ⟨Or.inr ⟨h₂.1, hn1z1_pos, hd⟩, Or.inr ⟨hn2z2_neg, h₁.2, hd⟩⟩

private theorem rayCross_of_adj_sectors (c : Fin 3) {z₁ z₂ : ℝ × ℝ}
    (h₁ : inOpenSector c z₁) (h₂ : inOpenSector (c + 1) z₂) :
    (0 < det2 z₁ z₂ → rayCross c z₁ z₂) ∧
      (det2 z₁ z₂ < 0 → rayCross (c + 1) z₁ z₂ ∧ rayCross (c + 2) z₁ z₂) := by
  have step {d : Fin 3} {w₁ w₂ : ℝ × ℝ}
      (h : (0 < det2 (rot120 w₁) (rot120 w₂) → rayCross (d + 1) (rot120 w₁) (rot120 w₂)) ∧
        (det2 (rot120 w₁) (rot120 w₂) < 0 →
          rayCross ((d + 1) + 1) (rot120 w₁) (rot120 w₂) ∧
          rayCross ((d + 1) + 2) (rot120 w₁) (rot120 w₂))) :
      (0 < det2 w₁ w₂ → rayCross d w₁ w₂) ∧
        (det2 w₁ w₂ < 0 → rayCross (d + 1) w₁ w₂ ∧ rayCross (d + 2) w₁ w₂) := by
    have h2 : (d + 1) + 2 = (d + 2) + 1 := by fin_cases d <;> decide
    simpa only [det2_rot120, h2, rayCross_rot120] using h
  fin_cases c
  · exact rayCross_of_adj_sectors_zero h₁ h₂
  · exact step <| step <| rayCross_of_adj_sectors_zero
      ((inOpenSector_rot120 (1 + 1) _).mpr ((inOpenSector_rot120 1 z₁).mpr h₁))
      ((inOpenSector_rot120 ((1 + 1) + 1) _).mpr ((inOpenSector_rot120 (1 + 1) z₂).mpr h₂))
  · exact step <| rayCross_of_adj_sectors_zero
      ((inOpenSector_rot120 2 z₁).mpr h₁) ((inOpenSector_rot120 0 z₂).mpr h₂)

/-- **Cramer's rule for `(0, 0) ∈ conv(z₀, z₁, z₂)`.** When all three cyclic determinants are
strictly positive, `(0, 0)` is a convex combination of `z₀, z₁, z₂`. -/
private theorem convex_zero_of_pos_det2 {z₀ z₁ z₂ : ℝ × ℝ}
    (hd₀ : 0 < det2 z₀ z₁) (hd₁ : 0 < det2 z₁ z₂) (hd₂ : 0 < det2 z₂ z₀) :
    ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
      w₀ * z₀.1 + w₁ * z₁.1 + w₂ * z₂.1 = 0 ∧
      w₀ * z₀.2 + w₁ * z₁.2 + w₂ * z₂.2 = 0 := by
  set S := det2 z₀ z₁ + det2 z₁ z₂ + det2 z₂ z₀
  have hS : 0 < S := by dsimp [S]; linarith only [hd₀, hd₁, hd₂]
  have hS0 : S ≠ 0 := hS.ne'
  refine ⟨det2 z₁ z₂ / S, det2 z₂ z₀ / S, det2 z₀ z₁ / S,
    by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
  · dsimp [S]; field_simp; ring
  · dsimp [det2]; field_simp; ring
  · dsimp [det2]; field_simp; ring

open Classical in
/-- Sum of `rayCross` indicators over `c : Fin 3` for an adjacent-sector pair `(z₁, z₂)` with
nonzero determinant: at least `1` when `0 < det2 z₁ z₂` and at least `2` when `det2 z₁ z₂ < 0`. -/
private theorem one_or_two_le_sum_rayCross (c : Fin 3) {z₁ z₂ : ℝ × ℝ}
    (h₁ : inOpenSector c z₁) (h₂ : inOpenSector (c + 1) z₂) (hd : det2 z₁ z₂ ≠ 0) :
    1 ≤ (∑ k : Fin 3, if rayCross k z₁ z₂ then (1 : ℕ) else 0) ∧
      (det2 z₁ z₂ < 0 → 2 ≤ ∑ k : Fin 3, if rayCross k z₁ z₂ then (1 : ℕ) else 0) := by
  obtain ⟨hpos, hneg⟩ := rayCross_of_adj_sectors c h₁ h₂
  have hsum : ∑ k : Fin 3, (if rayCross k z₁ z₂ then (1 : ℕ) else 0) =
      (if rayCross c z₁ z₂ then 1 else 0) + (if rayCross (c + 1) z₁ z₂ then 1 else 0) +
        (if rayCross (c + 2) z₁ z₂ then 1 else 0) := by
    match c with
    | 0 => exact Fin.sum_univ_three _
    | 1 => rw [Fin.sum_univ_three]; simp only [Fin.reduceAdd]; omega
    | 2 => rw [Fin.sum_univ_three]; simp only [Fin.reduceAdd]; omega
  rw [hsum]
  rcases lt_or_gt_of_ne hd with hlt | hgt
  · obtain ⟨hc1, hc2⟩ := hneg hlt
    simp only [ite_eq_left hc1, ite_eq_left hc2]
    exact ⟨by omega, fun _ => by omega⟩
  · simp only [ite_eq_left (hpos hgt)]
    exact ⟨by omega, fun hlt => absurd hlt (not_lt.mpr hgt.le)⟩


end Cslib.Circuits.Frontier.TensorRank
