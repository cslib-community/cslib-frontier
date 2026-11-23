/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CappedCompression
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Coefficient
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Straddle
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos
import CslibFrontier.Foundations.Geometry.Euclidean.Angle.Cap
import CslibFrontier.Foundations.MeasureTheory.Constructions.BorelSpace.Order
import CslibFrontier.Foundations.Probability.Gaussian.ConvexCap
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.OffMedian
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.UnionBound
import CslibFrontier.Foundations.Probability.WeightedSecondMoment
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `Z₃`-symmetric planar Gaussian `3`-way cuts of subcubic multigraphs

To reduce a fan-in-`2` circuit to a single square matrix multiplication `Tensor.mm D D D`, one needs
a vertex `3`-coloring `V = V₀ ⊔ V₁ ⊔ V₂` of a connected loopless subcubic multigraph `G` that
simultaneously balances a target vertex subset `A ⊆ V` (`|A ∩ V_c| = |A| / 3 ± o(|V|)`) and bounds
all three pairwise edge cuts `E(V₀, V₁)`, `E(V₁, V₂)`, `E(V₂, V₀)`.

1. **Weight-capped compression.** `CappedCompression` with unit vertex weight and cap `M` shrinks
   `G` to a loopless subcubic quotient `Q` with block size `≤ M`, `#(Q₁ ∪ Q₂) = O(|V| / M)`, and
   `#Q₃ ≤ 2 β₁(G) + #Q₁`.
2. **`Z₃`-symmetric `120°` planar Gaussian cut.** Assign each block two independent standard
   Gaussians `(g₁, g₂)` and three independent Gaussian tie-breakers. Each quotient edge `e` gets the
   `2`D vector `z_e = (edgeScore Q q R g₁ e, edgeScore Q q R g₂ e) ∈ ℝ²`, partitioned into three
   `120°` open sectors `S₀, S₁, S₂`. Each block chooses the sector containing the strict majority of
   its incident edge vectors (breaking ties via its independent tie-breakers).
3. **Ray-crossing + spherical-cap triangle bound.** At a degree-`3` block `B`, the number of
   incident edges falling outside `B`'s chosen sector is `0` in `(3, 0, 0)`, `1` in `(2, 1, 0)`, and
   `2` in the rainbow `(1, 1, 1)` case. Counting oriented crossings of the three boundary rays by
   ordered edge pairs (`rayCross`) together with the origin-in-triangle event `(0, 0) ∈ conv(z_i)`
   (`ProbabilityTheory.measureReal_pi_prod_convex_zero_le`) bounds the expected mismatched half-edge
   count at `B` by
   `threeWayCapCoefficient = (3 / 2) p + (1 / 2) (1 - √((1 + 2√2 / 3) / 2)) ≈ 0.217728 ≤ 0.21773`,
   so each pairwise cut has expected size at most `(2 / 3) threeWayCapCoefficient β₁(G) + o(|V|)`.
   Weighted local Chebyshev concentration (`WeightedSecondMoment`) yields a single coloring meeting
   all six balance and cut bounds simultaneously.

## Main definitions

* `Cslib.Circuits.Frontier.TensorRank.threeWayCapCoefficient`: the `3`-way planar Gaussian
  half-edge mismatch coefficient `(3 / 2) p + (1 / 2) (1 - √((1 + 2√2 / 3) / 2))`.

## Main results

* `Cslib.Circuits.Frontier.TensorRank.threeWayCapCoefficient_pos`: `0 < threeWayCapCoefficient`.
* `Cslib.Circuits.Frontier.TensorRank.threeWayCapCoefficient_le_21773`:
  `threeWayCapCoefficient ≤ 21773 / 100000`.
* `Cslib.Circuits.Frontier.TensorRank.circuitThreshold_gt_3041`:
  `3041 / 1000 < 1 + 4 / (9 * threeWayCapCoefficient)`.
* `Cslib.Circuits.Frontier.TensorRank.exists_balanced_threeWayCut`: simultaneous `1 / 3`-balance on
  `A ⊆ V` and `(2 / 3) · threeWayCapCoefficient · β₁(G)` bound on all three pairwise edge cuts.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.TensorRank

open Cslib.Circuits.Frontier.Gaussian Cslib.Circuits.Frontier.Multigraph

/-! ### The `3`-way planar Gaussian coefficient and its rational bounds -/

/-- The `3`-way planar Gaussian half-edge mismatch coefficient on cubic blocks:
`(3 / 2) * gaussianCoefficient + (1 / 2) * (1 - √((1 + 2√2 / 3) / 2)) ≈ 0.217728`. -/
noncomputable def threeWayCapCoefficient : ℝ :=
  3 / 2 * gaussianCoefficient + 1 / 2 * (1 - √((1 + 2 * √2 / 3) / 2))

/-- The parametric `3`-way mismatch bound at adjacent kernel correlation `ρ₀`. -/
private noncomputable def capAt (ρ₀ : ℝ) : ℝ :=
  3 / 2 * straddleBound ρ₀ + 1 / 2 * (1 - √((1 + ρ₀) / 2))

private theorem capAt_limit : capAt (2 * √2 / 3) = threeWayCapCoefficient := by
  rw [capAt, threeWayCapCoefficient, gaussianCoefficient_eq]

private theorem capAt_le_three (ρ₀ : ℝ) : capAt ρ₀ ≤ 3 := by
  have hpi : 0 < π := pi_pos
  have harc : arccos ((1 + 3 * ρ₀) / 4) ≤ π := arccos_le_pi _
  have hstrad : straddleBound ρ₀ ≤ 3 / 2 := by
    rw [straddleBound, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [harc, hpi]
  have hsqrt : 0 ≤ √((1 + ρ₀) / 2) := sqrt_nonneg _
  unfold capAt
  linarith only [hstrad, hsqrt]

/-- `threeWayCapCoefficient` is strictly positive. -/
theorem threeWayCapCoefficient_pos : 0 < threeWayCapCoefficient := by
  have hp : 0 < gaussianCoefficient := gaussianCoefficient_pos
  have hsqrt2 : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hcap : √((1 + 2 * √2 / 3) / 2) ≤ 1 := sqrt_le_one.mpr (by linarith)
  unfold threeWayCapCoefficient
  linarith only [hp, hcap]

/-- Rational upper bound `threeWayCapCoefficient ≤ 21773 / 100000 = 0.21773`. -/
theorem threeWayCapCoefficient_le_21773 :
    threeWayCapCoefficient ≤ 21773 / 100000 := by
  have hp_pos : 0 < gaussianCoefficient := gaussianCoefficient_pos
  have hcc : (456249 / 100000 : ℝ) ≤ 1 + 1 / (2 * gaussianCoefficient) := by
    rw [one_add_inv_two_mul_gaussianCoefficient]
    exact circuitCoefficient_ge_456249
  have hdiv : (356249 / 100000 : ℝ) ≤ 1 / (2 * gaussianCoefficient) := by linarith only [hcc]
  have hp_le : gaussianCoefficient ≤ 100000 / 712498 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 2 * gaussianCoefficient)).mp hdiv
    linarith only [hmul]
  have hsqrt2 : (141421356 / 100000000 : ℝ) < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hκ_ge : (9855985 / 10000000 : ℝ) ≤ √((1 + 2 * √2 / 3) / 2) :=
    (le_sqrt (by norm_num) (by positivity)).mpr (by linarith only [hsqrt2])
  unfold threeWayCapCoefficient
  linarith only [hp_le, hκ_ge]

/-- Combining `threeWayCapCoefficient ≤ 21773 / 100000` with `ω ≤ 9 / 4` exceeds `3.041`:
`3041 / 1000 < 1 + 4 / (9 * threeWayCapCoefficient)`. -/
theorem circuitThreshold_gt_3041 :
    (3041 / 1000 : ℝ) < 1 + 4 / (9 * threeWayCapCoefficient) := by
  have hpos : 0 < threeWayCapCoefficient := threeWayCapCoefficient_pos
  have hle : threeWayCapCoefficient ≤ 21773 / 100000 := threeWayCapCoefficient_le_21773
  have hlt : (2041 / 1000 : ℝ) < 4 / (9 * threeWayCapCoefficient) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith only [hle]
  linarith only [hlt]

/-! ### Planar `120°` sectors, boundary normals, and oriented ray crossings -/

section PlanarGeometry

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
  fin_cases c₁ <;> fin_cases c₂
  · rfl
  · exfalso
    change dot2 (normVec 0) z < 0 ∧ 0 < dot2 (normVec 2) z at h₁
    change dot2 (normVec 1) z < 0 ∧ 0 < dot2 (normVec 0) z at h₂
    linarith only [h₁.1, h₂.2]
  · exfalso
    change dot2 (normVec 0) z < 0 ∧ 0 < dot2 (normVec 2) z at h₁
    change dot2 (normVec 2) z < 0 ∧ 0 < dot2 (normVec 1) z at h₂
    linarith only [h₁.2, h₂.1]
  · exfalso
    change dot2 (normVec 1) z < 0 ∧ 0 < dot2 (normVec 0) z at h₁
    change dot2 (normVec 0) z < 0 ∧ 0 < dot2 (normVec 2) z at h₂
    linarith only [h₁.2, h₂.1]
  · rfl
  · exfalso
    change dot2 (normVec 1) z < 0 ∧ 0 < dot2 (normVec 0) z at h₁
    change dot2 (normVec 2) z < 0 ∧ 0 < dot2 (normVec 1) z at h₂
    linarith only [h₁.1, h₂.2]
  · exfalso
    change dot2 (normVec 2) z < 0 ∧ 0 < dot2 (normVec 1) z at h₁
    change dot2 (normVec 0) z < 0 ∧ 0 < dot2 (normVec 2) z at h₂
    linarith only [h₁.1, h₂.2]
  · exfalso
    change dot2 (normVec 2) z < 0 ∧ 0 < dot2 (normVec 1) z at h₁
    change dot2 (normVec 1) z < 0 ∧ 0 < dot2 (normVec 0) z at h₂
    linarith only [h₁.2, h₂.1]
  · rfl

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
  simp only [rayCross, hdet]
  exact ⟨fun h => h.elim (fun ⟨h1, h2, hd⟩ => Or.inr ⟨h1, h2, by linarith only [hd]⟩)
      (fun ⟨h1, h2, hd⟩ => Or.inl ⟨h1, h2, by linarith only [hd]⟩),
    fun h => h.elim (fun ⟨h1, h2, hd⟩ => Or.inr ⟨h1, h2, by linarith only [hd]⟩)
      (fun ⟨h1, h2, hd⟩ => Or.inl ⟨h1, h2, by linarith only [hd]⟩)⟩

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
  fin_cases c
  · exact rayCross_of_adj_sectors_zero h₁ h₂
  · have h₁' : inOpenSector 0 (rot120 (rot120 z₁)) := by
      have hA : inOpenSector (1 + 1) (rot120 z₁) := (inOpenSector_rot120 1 z₁).mpr h₁
      exact (inOpenSector_rot120 (1 + 1) (rot120 z₁)).mpr hA
    have h₂' : inOpenSector 1 (rot120 (rot120 z₂)) := by
      have hA : inOpenSector ((1 + 1) + 1) (rot120 z₂) := (inOpenSector_rot120 (1 + 1) z₂).mpr h₂
      exact (inOpenSector_rot120 ((1 + 1) + 1) (rot120 z₂)).mpr hA
    obtain ⟨hpos, hneg⟩ := rayCross_of_adj_sectors_zero h₁' h₂'
    rw [det2_rot120, det2_rot120] at hpos hneg
    have hr0 : rayCross 0 (rot120 (rot120 z₁)) (rot120 (rot120 z₂)) ↔ rayCross 1 z₁ z₂ := by
      calc rayCross 0 (rot120 (rot120 z₁)) (rot120 (rot120 z₂))
          ↔ rayCross (2 + 1) (rot120 (rot120 z₁)) (rot120 (rot120 z₂)) := Iff.rfl
        _ ↔ rayCross 2 (rot120 z₁) (rot120 z₂) := rayCross_rot120 2 _ _
        _ ↔ rayCross (1 + 1) (rot120 z₁) (rot120 z₂) := Iff.rfl
        _ ↔ rayCross 1 z₁ z₂ := rayCross_rot120 1 _ _
    have hr1 : rayCross 1 (rot120 (rot120 z₁)) (rot120 (rot120 z₂)) ↔ rayCross (1 + 1) z₁ z₂ := by
      calc rayCross 1 (rot120 (rot120 z₁)) (rot120 (rot120 z₂))
          ↔ rayCross (0 + 1) (rot120 (rot120 z₁)) (rot120 (rot120 z₂)) := Iff.rfl
        _ ↔ rayCross 0 (rot120 z₁) (rot120 z₂) := rayCross_rot120 0 _ _
        _ ↔ rayCross (2 + 1) (rot120 z₁) (rot120 z₂) := Iff.rfl
        _ ↔ rayCross (1 + 1) z₁ z₂ := rayCross_rot120 2 _ _
    have hr2 : rayCross 2 (rot120 (rot120 z₁)) (rot120 (rot120 z₂)) ↔ rayCross (1 + 2) z₁ z₂ := by
      calc rayCross 2 (rot120 (rot120 z₁)) (rot120 (rot120 z₂))
          ↔ rayCross (1 + 1) (rot120 (rot120 z₁)) (rot120 (rot120 z₂)) := Iff.rfl
        _ ↔ rayCross 1 (rot120 z₁) (rot120 z₂) := rayCross_rot120 1 _ _
        _ ↔ rayCross (0 + 1) (rot120 z₁) (rot120 z₂) := Iff.rfl
        _ ↔ rayCross (1 + 2) z₁ z₂ := rayCross_rot120 0 _ _
    exact ⟨fun hd => hr0.mp (hpos hd), fun hd => ⟨hr1.mp (hneg hd).1, hr2.mp (hneg hd).2⟩⟩
  · have h₁' : inOpenSector 0 (rot120 z₁) := (inOpenSector_rot120 2 z₁).mpr h₁
    have h₂' : inOpenSector 1 (rot120 z₂) := (inOpenSector_rot120 0 z₂).mpr h₂
    obtain ⟨hpos, hneg⟩ := rayCross_of_adj_sectors_zero h₁' h₂'
    rw [det2_rot120] at hpos hneg
    have hr0 : rayCross 0 (rot120 z₁) (rot120 z₂) ↔ rayCross 2 z₁ z₂ := rayCross_rot120 2 _ _
    have hr1 : rayCross 1 (rot120 z₁) (rot120 z₂) ↔ rayCross (2 + 1) z₁ z₂ :=
      rayCross_rot120 0 _ _
    have hr2 : rayCross 2 (rot120 z₁) (rot120 z₂) ↔ rayCross (2 + 2) z₁ z₂ :=
      rayCross_rot120 1 _ _
    exact ⟨fun hd => hr0.mp (hpos hd), fun hd => ⟨hr1.mp (hneg hd).1, hr2.mp (hneg hd).2⟩⟩

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
  rcases lt_or_gt_of_ne hd with hlt | hgt
  · obtain ⟨hc1, hc2⟩ := hneg hlt
    have hne : c + 1 ≠ c + 2 := by fin_cases c <;> decide
    have hle : ({c + 1, c + 2} : Finset (Fin 3)).card ≤
        (Finset.univ.filter fun k : Fin 3 => rayCross k z₁ z₂).card := by
      refine Finset.card_le_card fun k hk => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hk with rfl | rfl
      exacts [hc1, hc2]
    rw [Finset.card_pair hne, Finset.card_filter] at hle
    exact ⟨ by omega, fun _ => hle⟩
  · have hc0 := hpos hgt
    have hle : ({c} : Finset (Fin 3)).card ≤
        (Finset.univ.filter fun k : Fin 3 => rayCross k z₁ z₂).card := by
      refine Finset.card_le_card fun k hk => ?_
      simp only [Finset.mem_singleton] at hk
      subst hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0⟩
    rw [Finset.card_singleton, Finset.card_filter] at hle
    exact ⟨hle, fun hlt => absurd hlt (not_lt.mpr hgt.le)⟩

end PlanarGeometry

/-! ### Measure-preserving maps and null sets on the planar Gaussian sample -/

section SampleSpace

/-- Per-block sample: two Gaussian coordinates for `2`D edge scores plus three Gaussian
tie-breakers. -/
private abbrev BlockSample := (ℝ × ℝ) × (Fin 3 → ℝ)

private noncomputable def gauss2 : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

private noncomputable def gaussTie : Measure (Fin 3 → ℝ) :=
  Measure.pi fun _ : Fin 3 => gaussianReal 0 1

private noncomputable def blockMeasure : Measure BlockSample :=
  gauss2.prod gaussTie

private instance : IsProbabilityMeasure gauss2 := by
  unfold gauss2; infer_instance

private instance : IsProbabilityMeasure gaussTie := by
  unfold gaussTie; infer_instance

private instance : IsProbabilityMeasure blockMeasure := by
  unfold blockMeasure; infer_instance

/-- Any unit linear functional `(a, b)` on `gauss2` has law `gaussianReal 0 1`. -/
private theorem measurePreserving_dot2_unit {u : ℝ × ℝ} (hu : u.1 ^ 2 + u.2 ^ 2 = 1) :
    MeasurePreserving (dot2 u) gauss2 (gaussianReal 0 1) := by
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![u.1, u.2]
  have hv_norm : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    dsimp [v]
    rw [sq_abs, sq_abs, hu, sqrt_one]
  have hv_nn : ‖v‖₊ ^ 2 = 1 := by ext; simp [hv_norm]
  have hmp1 := (measurePreserving_finTwoArrow (gaussianReal 0 1)).symm
  have hmp2 := measurePreserving_toLp_pi_gaussianReal (Fin 2)
  have hmp3 : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 2) => ⟪v, x⟫)
      (stdGaussian (EuclideanSpace ℝ (Fin 2))) (gaussianReal 0 1) :=
    ⟨by fun_prop, by rw [stdGaussian_map_inner, hv_nn]⟩
  have hcomp := (hmp3.comp hmp2).comp hmp1
  unfold gauss2
  convert hcomp using 1
  funext p
  simp only [Function.comp_apply, PiLp.inner_apply, Fin.sum_univ_two, v,
    Matrix.cons_val_zero, Matrix.cons_val_one, RCLike.inner_apply, conj_trivial]
  change u.1 * p.1 + u.2 * p.2 = p.1 * u.1 + p.2 * u.2
  ring

/-- Any orthogonal `2 × 2` map given by two orthogonal unit vectors preserves `gauss2`. -/
private theorem measurePreserving_ortho2 {u₀ u₁ : ℝ × ℝ}
    (h₀ : u₀.1 ^ 2 + u₀.2 ^ 2 = 1) (h₁ : u₁.1 ^ 2 + u₁.2 ^ 2 = 1)
    (horth : u₀.1 * u₁.1 + u₀.2 * u₁.2 = 0) :
    MeasurePreserving (fun p : ℝ × ℝ => (dot2 u₀ p, dot2 u₁ p)) gauss2 gauss2 := by
  let v : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
    ![WithLp.toLp 2 ![u₀.1, u₀.2], WithLp.toLp 2 ![u₁.1, u₁.2] ]
  have hv_norm (i : Fin 2) : ‖v i‖ = 1 := by
    fin_cases i
    · rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]; dsimp [v]
      rw [sq_abs, sq_abs, h₀, sqrt_one]
    · rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]; dsimp [v]
      rw [sq_abs, sq_abs, h₁, sqrt_one]
  have hv_orth : Pairwise fun i j : Fin 2 => ⟪v i, v j⟫ = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change ⟪v 0, v 1⟫ = 0
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp only [RCLike.inner_apply, conj_trivial]
      dsimp [v]
      linarith [show u₁.1 * u₀.1 + u₁.2 * u₀.2 = u₀.1 * u₁.1 + u₀.2 * u₁.2 by ring, horth]
    · change ⟪v 1, v 0⟫ = 0
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp only [RCLike.inner_apply, conj_trivial]
      dsimp [v]
      linarith only [horth]
    · exact absurd rfl hij
  have hmp1 := (measurePreserving_finTwoArrow (gaussianReal 0 1)).symm
  have hmp2 := measurePreserving_toLp_pi_gaussianReal (Fin 2)
  have hmp3 : MeasurePreserving (fun x (i : Fin 2) => ⟪v i, x⟫)
      (stdGaussian (EuclideanSpace ℝ (Fin 2))) (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
    ⟨by fun_prop, stdGaussian_map_inner_pi hv_norm hv_orth⟩
  have hmp4 := measurePreserving_finTwoArrow (gaussianReal 0 1)
  have hcomp := hmp4.comp ((hmp3.comp hmp2).comp hmp1)
  unfold gauss2
  convert hcomp using 1
  funext p
  ext
  · simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply, PiLp.inner_apply,
      Fin.sum_univ_two, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      RCLike.inner_apply, conj_trivial]
    change u₀.1 * p.1 + u₀.2 * p.2 = p.1 * u₀.1 + p.2 * u₀.2
    ring
  · simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply, PiLp.inner_apply,
      Fin.sum_univ_two, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      RCLike.inner_apply, conj_trivial]
    change u₁.1 * p.1 + u₁.2 * p.2 = p.1 * u₁.1 + p.2 * u₁.2
    ring

private theorem measurePreserving_rot120 : MeasurePreserving rot120 gauss2 gauss2 := by
  have h := measurePreserving_ortho2 (u₀ := (-1 / 2, -√3 / 2)) (u₁ := (√3 / 2, -1 / 2))
    (by ring_nf; rw [sq_sqrt (by norm_num)]; norm_num)
    (by ring_nf; rw [sq_sqrt (by norm_num)]; norm_num)
    (by ring)
  convert h using 1
  funext p
  ext <;> (dsimp [rot120, dot2]; ring)

private theorem measurePreserving_neg2 : MeasurePreserving neg2 gauss2 gauss2 := by
  have h := measurePreserving_ortho2 (u₀ := (-1, 0)) (u₁ := (0, -1))
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  funext p
  ext <;> (dsimp [neg2, dot2]; ring)

/-- Cyclic shift `τ ↦ (c ↦ τ (c + 2))` on `Fin 3 → ℝ` preserves `gaussTie`. -/
private def shiftTie (τ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun c => τ (c + 2)

private theorem shiftTie_add_one (τ : Fin 3 → ℝ) (c : Fin 3) :
    shiftTie τ (c + 1) = τ c := by
  dsimp [shiftTie]
  congr 1
  fin_cases c <;> decide

private theorem measurePreserving_shiftTie :
    MeasurePreserving shiftTie gaussTie gaussTie := by
  let f : Fin 3 ≃ Fin 3 :=
    { toFun := fun c => c + 2
      invFun := fun c => c + 1
      left_inv := fun c => by fin_cases c <;> decide
      right_inv := fun c => by fin_cases c <;> decide }
  have hmp := (measurePreserving_piCongrLeft (α := fun _ : Fin 3 => ℝ)
    (fun _ : Fin 3 => gaussianReal 0 1) f).symm
  unfold gaussTie shiftTie
  convert hmp using 1
  rfl

private noncomputable def rotSample (s : BlockSample) : BlockSample :=
  (rot120 s.1, shiftTie s.2)

private def negSample (s : BlockSample) : BlockSample :=
  (neg2 s.1, s.2)

private theorem measurePreserving_rotSample :
    MeasurePreserving rotSample blockMeasure blockMeasure :=
  measurePreserving_rot120.prod measurePreserving_shiftTie

private theorem measurePreserving_negSample :
    MeasurePreserving negSample blockMeasure blockMeasure :=
  measurePreserving_neg2.prod (MeasurePreserving.id gaussTie)

/-- Under `gaussTie`, two distinct coordinates agree with probability zero. -/
private theorem gaussTie_not_injective_zero :
    gaussTie.real {τ : Fin 3 → ℝ | ¬Function.Injective τ} = 0 := by
  have hpair (c₁ c₂ : Fin 3) (hne : c₁ ≠ c₂) :
      gaussTie.real {τ : Fin 3 → ℝ | τ c₁ = τ c₂} = 0 := by
    let e₁ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single c₁ 1
    let e₂ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single c₂ 1
    let u : EuclideanSpace ℝ (Fin 3) := (1 / √2 : ℝ) • (e₁ - e₂)
    have hon := EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)
    have hsub_sq : ‖e₁ - e₂‖ ^ 2 = 2 := by
      rw [@norm_sub_sq_real (EuclideanSpace ℝ (Fin 3)) _ _ e₁ e₂, hon.1 c₁, hon.1 c₂, hon.2 hne]
      norm_num
    have hu : ‖u‖ = 1 := by
      have hdiff : ‖e₁ - e₂‖ = √2 := by rw [← sqrt_sq (norm_nonneg _), hsub_sq]
      rw [norm_smul, hdiff, Real.norm_of_nonneg (by positivity)]
      exact one_div_mul_cancel (by positivity)
    have hsub : {τ : Fin 3 → ℝ | τ c₁ = τ c₂} ⊆
        {τ : Fin 3 → ℝ | ⟪u, WithLp.toLp 2 τ⟫ = 0} := by
      intro τ hτ
      change τ c₁ = τ c₂ at hτ
      rw [mem_ofPred_eq]
      dsimp only [u, e₁, e₂]
      rw [real_inner_smul_left, inner_sub_left, EuclideanSpace.inner_single_left,
        EuclideanSpace.inner_single_left]
      simp [hτ]
    exact le_antisymm ((ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans_eq
      (measureReal_pi_gaussianReal_inner_eq_zero hu)) measureReal_nonneg
  have hcov : {τ : Fin 3 → ℝ | ¬Function.Injective τ} ⊆
      {τ | τ 0 = τ 1} ∪ ({τ | τ 1 = τ 2} ∪ {τ | τ 2 = τ 0}) := by
    intro τ hτ
    change ¬(∀ a₁ a₂ : Fin 3, τ a₁ = τ a₂ → a₁ = a₂) at hτ
    push Not at hτ
    obtain ⟨c₁, c₂, heq, hne⟩ := hτ
    fin_cases c₁ <;> fin_cases c₂
    · exact absurd rfl hne
    · exact Or.inl heq
    · exact Or.inr (Or.inr heq.symm)
    · exact Or.inl heq.symm
    · exact absurd rfl hne
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr heq)
    · exact Or.inr (Or.inl heq.symm)
    · exact absurd rfl hne
  have hle : gaussTie.real {τ : Fin 3 → ℝ | ¬Function.Injective τ} ≤
      gaussTie.real {τ | τ 0 = τ 1} +
        (gaussTie.real {τ | τ 1 = τ 2} + gaussTie.real {τ | τ 2 = τ 0}) :=
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcov)).trans
      ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _)))
  rw [hpair 0 1 (by decide), hpair 1 2 (by decide), hpair 2 0 (by decide)] at hle
  exact le_antisymm (by linarith only [hle]) measureReal_nonneg

/-- Under two independent copies of `gauss2`, `{((a₀, a₁), (b₀, b₁)) | a₀ * b₁ = b₀ * a₁}` has
measure zero. -/
private theorem gauss2_prod_det_eq_zero :
    (gauss2.prod gauss2) {p : (ℝ × ℝ) × (ℝ × ℝ) | p.1.1 * p.2.2 - p.1.2 * p.2.1 = 0} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p | p.1.1 * p.2.2 - p.1.2 * p.2.1 = 0}
  have hSm : MeasurableSet S :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [Measure.prod_apply hSm]
  have ha0 : gauss2 {a : ℝ × ℝ | a.1 = 0} = 0 := by
    have hset : {a : ℝ × ℝ | a.1 = 0} = ({0} : Set ℝ) ×ˢ (univ : Set ℝ) := by
      ext ⟨a₀, a₁⟩; simp
    rw [hset, gauss2, Measure.prod_prod, measure_singleton, zero_mul]
  have hslice (a : ℝ × ℝ) (ha : a.1 ≠ 0) : gauss2 (Prod.mk a ⁻¹' S) = 0 := by
    have hpre_m : MeasurableSet (Prod.mk a ⁻¹' S) := hSm.preimage (by fun_prop)
    rw [gauss2, Measure.prod_apply hpre_m]
    refine (lintegral_eq_zero_iff (measurable_measure_prodMk_left hpre_m)).mpr
      (Filter.Eventually.of_forall fun b₀ => ?_)
    have hsub : Prod.mk b₀ ⁻¹' (Prod.mk a ⁻¹' S) ⊆ ({a.2 * b₀ / a.1} : Set ℝ) := by
      intro b₁ hb₁
      simp only [mem_preimage, S, mem_ofPred_eq, mem_singleton_iff] at hb₁ ⊢
      rw [eq_div_iff ha]
      linarith only [hb₁]
    exact measure_mono_null hsub (measure_singleton _)
  refine (lintegral_eq_zero_iff (measurable_measure_prodMk_left hSm)).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr ha0] with a ha
  exact hslice a ha

/-- For distinct unit vectors `y₁ ≠ y₂` with `-1 < ⟪y₁, y₂⟫`, the `2`D Gaussian projections
`(⟪y_i, g₁⟫, ⟪y_i, g₂⟫)` are collinear (`det2 = 0`) with probability zero. -/
private theorem measureReal_pi_prod_det2_eq_zero {ι : Type*} [Fintype ι]
    {y₁ y₂ : EuclideanSpace ℝ ι} (hy₁ : ‖y₁‖ = 1) (hy₂ : ‖y₂‖ = 1)
    (hρ_gt : -1 < ⟪y₁, y₂⟫) (hne : y₁ ≠ y₂) :
    ((Measure.pi fun _ : ι => gaussianReal 0 1).prod
        (Measure.pi fun _ : ι => gaussianReal 0 1)).real
      {g : (ι → ℝ) × (ι → ℝ) |
        det2 (⟪y₁, WithLp.toLp 2 g.1⟫, ⟪y₁, WithLp.toLp 2 g.2⟫)
          (⟪y₂, WithLp.toLp 2 g.1⟫, ⟪y₂, WithLp.toLp 2 g.2⟫) = 0} = 0 := by
  set ρ := ⟪y₁, y₂⟫
  have hdiff_pos : 0 < ‖y₂ - y₁‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))
  have hdiff_eq : ‖y₂ - y₁‖ ^ 2 = 2 - 2 * ρ := by
    rw [norm_sub_sq_real, hy₂, hy₁, real_inner_comm]
    ring
  have hρ_lt : ρ < 1 := by linarith only [hdiff_pos, hdiff_eq]
  set w := y₂ - ρ • y₁
  have hw_sq : ‖w‖ ^ 2 = 1 - ρ ^ 2 := by
    dsimp [w]
    rw [norm_sub_sq_real, hy₂, norm_smul, Real.norm_eq_abs, hy₁, mul_one, sq_abs,
      real_inner_smul_right, real_inner_comm]
    ring
  have hw_pos : 0 < ‖w‖ := by
    have h1 : 0 < 1 - ρ ^ 2 := by nlinarith only [hρ_gt, hρ_lt]
    refine norm_pos_iff.mpr fun h0 => ?_
    rw [h0, norm_zero] at hw_sq
    linarith
  let u₂ : EuclideanSpace ℝ ι := ‖w‖⁻¹ • w
  have hu₂_norm : ‖u₂‖ = 1 := by
    dsimp [u₂]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw_pos.ne']
  have hy₁u₂ : ⟪y₁, u₂⟫ = 0 := by
    dsimp [u₂, w]
    rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hy₁]
    change ‖w‖⁻¹ * (ρ - ρ * 1 ^ 2) = 0
    ring
  have hy₂_decomp (x : EuclideanSpace ℝ ι) :
      ⟪y₂, x⟫ = ρ * ⟪y₁, x⟫ + ‖w‖ * ⟪u₂, x⟫ := by
    have hw_eq : y₂ = ρ • y₁ + ‖w‖ • u₂ := by
      dsimp [u₂, w]
      rw [smul_smul, mul_inv_cancel₀ hw_pos.ne', one_smul, add_sub_cancel]
    conv_lhs => rw [hw_eq]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  let u : Fin 2 → EuclideanSpace ℝ ι := ![y₁, u₂]
  have hu_norm (i : Fin 2) : ‖u i‖ = 1 := by
    fin_cases i <;> simp [u, hy₁, hu₂_norm]
  have hu_orth : Pairwise fun i j : Fin 2 => ⟪u i, u j⟫ = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hy₁u₂
    · rw [real_inner_comm]; exact hy₁u₂
    · exact absurd rfl hij
  let proj (x : EuclideanSpace ℝ ι) : ℝ × ℝ := (⟪y₁, x⟫, ⟪u₂, x⟫)
  have hmp_single : MeasurePreserving proj
      (stdGaussian (EuclideanSpace ℝ ι)) gauss2 := by
    have h1 : MeasurePreserving (fun x (i : Fin 2) => ⟪u i, x⟫)
        (stdGaussian (EuclideanSpace ℝ ι)) (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
      ⟨by fun_prop, stdGaussian_map_inner_pi hu_norm hu_orth⟩
    have h2 := measurePreserving_finTwoArrow (gaussianReal 0 1)
    unfold gauss2
    convert h2.comp h1 using 1
    funext x
    simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply, proj, u,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have hmp_lp := (measurePreserving_toLp_pi_gaussianReal ι).prod
    (measurePreserving_toLp_pi_gaussianReal ι)
  have hmp_all := (hmp_single.prod hmp_single).comp hmp_lp
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p | p.1.1 * p.2.2 - p.1.2 * p.2.1 = 0}
  have hSm : MeasurableSet S :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hsub : {g : (ι → ℝ) × (ι → ℝ) |
      det2 (⟪y₁, WithLp.toLp 2 g.1⟫, ⟪y₁, WithLp.toLp 2 g.2⟫)
        (⟪y₂, WithLp.toLp 2 g.1⟫, ⟪y₂, WithLp.toLp 2 g.2⟫) = 0} ⊆
      (Prod.map proj proj ∘ Prod.map (WithLp.toLp 2) (WithLp.toLp 2)) ⁻¹' S := by
    intro g hg
    simp only [mem_ofPred_eq, mem_preimage, Function.comp_apply, proj, S] at hg ⊢
    rw [hy₂_decomp, hy₂_decomp] at hg
    have hid : det2 (⟪y₁, WithLp.toLp 2 g.1⟫, ⟪y₁, WithLp.toLp 2 g.2⟫)
        (ρ * ⟪y₁, WithLp.toLp 2 g.1⟫ + ‖w‖ * ⟪u₂, WithLp.toLp 2 g.1⟫,
         ρ * ⟪y₁, WithLp.toLp 2 g.2⟫ + ‖w‖ * ⟪u₂, WithLp.toLp 2 g.2⟫) =
        ‖w‖ * (⟪y₁, WithLp.toLp 2 g.1⟫ * ⟪u₂, WithLp.toLp 2 g.2⟫ -
          ⟪u₂, WithLp.toLp 2 g.1⟫ * ⟪y₁, WithLp.toLp 2 g.2⟫) := by
      dsimp [det2]; ring
    rw [hid] at hg
    exact (mul_eq_zero.mp hg).resolve_left hw_pos.ne'
  rw [measureReal_def]
  have h0 : ((Measure.pi fun _ : ι => gaussianReal 0 1).prod
      (Measure.pi fun _ : ι => gaussianReal 0 1))
      ((Prod.map proj proj ∘ Prod.map (WithLp.toLp 2) (WithLp.toLp 2)) ⁻¹' S) = 0 := by
    rw [hmp_all.measure_preimage hSm.nullMeasurableSet]
    exact gauss2_prod_det_eq_zero
  rw [measure_mono_null hsub h0, ENNReal.toReal_zero]

end SampleSpace

/-! ### `Z₃`-equivariant block coloring on a loopless subcubic multigraph -/

section QuotientColoring

variable {W F : Type*} [Fintype W] [Finite F]

/-- The `2`D Gaussian edge vector `(edgeScore Q q R g₁ e, edgeScore Q q R g₂ e)` of an edge `e`. -/
private noncomputable def edgeVec2 (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (e : F) : ℝ × ℝ :=
  (edgeScore Q q R (fun B => (ω B).1.1) e, edgeScore Q q R (fun B => (ω B).1.2) e)

omit [Finite F] in
private theorem measurable_edgeVec2 (Q : Multigraph W F) (q : ℝ) (R : ℕ) (e : F) :
    Measurable fun ω : W → BlockSample => edgeVec2 Q q R ω e := by
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_edgeScore q R e).comp
      (measurable_pi_iff.mpr fun B => (measurable_fst.comp measurable_fst).comp
        (measurable_pi_apply B))
  · exact (measurable_edgeScore q R e).comp
      (measurable_pi_iff.mpr fun B => (measurable_snd.comp measurable_fst).comp
        (measurable_pi_apply B))

omit [Finite F] in
private theorem edgeVec2_congr {Q : Multigraph W F} {q : ℝ} {R : ℕ} {B : W} {e : F}
    (he : e ∈ Q.incidenceSet B) {ω ω' : W → BlockSample}
    (h : ∀ z ∈ closedBall Q.toSimpleGraph B (R + 1), ω z = ω' z) :
    edgeVec2 Q q R ω e = edgeVec2 Q q R ω' e := by
  ext
  · exact edgeScore_congr he fun z hz => congrArg (fun s => s.1.1) (h z hz)
  · exact edgeScore_congr he fun z hz => congrArg (fun s => s.1.2) (h z hz)

omit [Finite F] in
private theorem dot2_edgeVec2 (Q : Multigraph W F) (q : ℝ) (R : ℕ) (u : ℝ × ℝ)
    (ω : W → BlockSample) (e : F) :
    dot2 u (edgeVec2 Q q R ω e) = edgeScore Q q R (fun B => dot2 u (ω B).1) e := by
  dsimp [dot2, edgeVec2, edgeScore]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun B _ => ?_
  ring

omit [Finite F] in
private theorem edgeVec2_rotSample (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (e : F) :
    edgeVec2 Q q R (fun B => rotSample (ω B)) e = rot120 (edgeVec2 Q q R ω e) := by
  have h1 := dot2_edgeVec2 Q q R (-1 / 2, -√3 / 2) ω e
  have h2 := dot2_edgeVec2 Q q R (√3 / 2, -1 / 2) ω e
  ext
  · dsimp [edgeVec2, rotSample, rot120, dot2] at h1 ⊢
    have hfun : (fun B => -1 / 2 * (ω B).1.1 + -√3 / 2 * (ω B).1.2) =
        fun B => -1 / 2 * (ω B).1.1 - √3 / 2 * (ω B).1.2 := by funext B; ring
    rw [hfun] at h1
    linarith only [h1]
  · dsimp [edgeVec2, rotSample, rot120, dot2] at h2 ⊢
    have hfun : (fun B => √3 / 2 * (ω B).1.1 + -1 / 2 * (ω B).1.2) =
        fun B => √3 / 2 * (ω B).1.1 - 1 / 2 * (ω B).1.2 := by funext B; ring
    rw [hfun] at h2
    linarith only [h2]

omit [Finite F] in
private theorem edgeVec2_negSample (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (e : F) :
    edgeVec2 Q q R (fun B => negSample (ω B)) e = neg2 (edgeVec2 Q q R ω e) := by
  have h1 := dot2_edgeVec2 Q q R (-1, 0) ω e
  have h2 := dot2_edgeVec2 Q q R (0, -1) ω e
  ext
  · dsimp [edgeVec2, negSample, neg2, dot2] at h1 ⊢
    have hfun : (fun B => -1 * (ω B).1.1 + 0 * (ω B).1.2) = fun B => -(ω B).1.1 := by
      funext B; ring
    rw [hfun] at h1
    linarith only [h1]
  · dsimp [edgeVec2, negSample, neg2, dot2] at h2 ⊢
    have hfun : (fun B => 0 * (ω B).1.1 + -1 * (ω B).1.2) = fun B => -(ω B).1.2 := by
      funext B; ring
    rw [hfun] at h2
    linarith only [h2]

private theorem toFinset_eq_of_fintype {α : Type*} (S : Set α) (i₁ : Fintype S) [i₂ : Fintype S] :
    @Set.toFinset α S i₁ = @Set.toFinset α S i₂ := by
  ext x
  rw [@Set.mem_toFinset _ _ i₁, @Set.mem_toFinset _ _ i₂]

open Classical in
/-- Number of incident edges at `B` falling into open sector `c`. -/
private noncomputable def secCount (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) (c : Fin 3) : ℕ :=
  ((@Set.toFinset F (Q.incidenceSet B) (Fintype.ofFinite _)).filter fun e =>
    inOpenSector c (edgeVec2 Q q R ω e)).card

private theorem secCount_rotSample (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) (c : Fin 3) :
    secCount Q q R (fun B' => rotSample (ω B')) B (c + 1) = secCount Q q R ω B c := by
  classical
  have := Fintype.ofFinite F
  dsimp [secCount]
  congr 1
  ext e
  simp only [Finset.mem_filter, edgeVec2_rotSample, inOpenSector_rot120]

/-- Lexicographic sector comparison `(secCount, tieBreaker)`. -/
private def beats (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) (c c' : Fin 3) : Prop :=
  secCount Q q R ω B c' < secCount Q q R ω B c ∨
    (secCount Q q R ω B c' = secCount Q q R ω B c ∧ (ω B).2 c' < (ω B).2 c)

private theorem beats_rotSample (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) (c c' : Fin 3) :
    beats Q q R (fun B' => rotSample (ω B')) B (c + 1) (c' + 1) ↔ beats Q q R ω B c c' := by
  unfold beats
  rw [secCount_rotSample, secCount_rotSample]
  dsimp [rotSample]
  rw [shiftTie_add_one, shiftTie_add_one]

private theorem beats_asymm {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} {c c' : Fin 3}
    (h : beats Q q R ω B c c') : ¬beats Q q R ω B c' c := by
  simp only [beats] at h ⊢
  rintro (h' | ⟨heq, hτ'⟩) <;> rcases h with hlt | ⟨heq2, hτ⟩
  · omega
  · omega
  · omega
  · linarith only [hτ, hτ']

private theorem beats_total {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} (hinj : Function.Injective (ω B).2)
    {c c' : Fin 3} (hne : c ≠ c') :
    beats Q q R ω B c c' ∨ beats Q q R ω B c' c := by
  rcases lt_trichotomy (secCount Q q R ω B c') (secCount Q q R ω B c) with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases lt_or_gt_of_ne (fun h => hne (hinj h).symm) with hτ | hτ
    · exact Or.inl (Or.inr ⟨heq, hτ⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hτ⟩)
  · exact Or.inr (Or.inl hgt)

private theorem beats_trans {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} {c₁ c₂ c₃ : Fin 3}
    (h12 : beats Q q R ω B c₁ c₂) (h23 : beats Q q R ω B c₂ c₃) :
    beats Q q R ω B c₁ c₃ := by
  rcases h12 with hlt1 | ⟨heq1, hτ1⟩ <;> rcases h23 with hlt2 | ⟨heq2, hτ2⟩
  · exact Or.inl (hlt2.trans hlt1)
  · exact Or.inl (heq2.trans_lt hlt1)
  · exact Or.inl (hlt2.trans_eq heq1)
  · exact Or.inr ⟨heq2.trans heq1, hτ2.trans hτ1⟩

open Classical in
/-- Block sector color: chooses the unique winner under `beats` (with deterministic fallback on
measure-zero ties). -/
private noncomputable def blockColor (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) : Fin 3 :=
  if beats Q q R ω B 0 1 ∧ beats Q q R ω B 0 2 then 0
  else if beats Q q R ω B 1 2 then 1
  else 2

private theorem blockColor_eq_iff_of_injective {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} (hinj : Function.Injective (ω B).2) (c : Fin 3) :
    blockColor Q q R ω B = c ↔ ∀ c' : Fin 3, c' ≠ c → beats Q q R ω B c c' := by
  have ht01 := beats_total (Q := Q) (q := q) (R := R) hinj (by decide : (0 : Fin 3) ≠ 1)
  have ht12 := beats_total (Q := Q) (q := q) (R := R) hinj (by decide : (1 : Fin 3) ≠ 2)
  have ht02 := beats_total (Q := Q) (q := q) (R := R) hinj (by decide : (0 : Fin 3) ≠ 2)
  constructor
  · intro hc c' hc'
    subst hc
    unfold blockColor at hc' ⊢
    split_ifs at hc' ⊢ with h0 h1
    · fin_cases c'
      · exact absurd rfl hc'
      · exact h0.1
      · exact h0.2
    · fin_cases c'
      · rcases ht01 with hb01 | hb10
        · exact absurd ⟨hb01, beats_trans hb01 h1⟩ h0
        · exact hb10
      · exact absurd rfl hc'
      · exact h1
    · have hb21 : beats Q q R ω B 2 1 := ht12.resolve_left h1
      fin_cases c'
      · rcases ht02 with hb02 | hb20
        · rcases ht01 with hb01 | hb10
          · exact absurd ⟨hb01, hb02⟩ h0
          · exact absurd (beats_trans hb10 hb02) h1
        · exact hb20
      · exact hb21
      · exact absurd rfl hc'
  · intro hall
    unfold blockColor
    fin_cases c
    · have h0 : beats Q q R ω B 0 1 ∧ beats Q q R ω B 0 2 :=
        ⟨hall 1 (by decide), hall 2 (by decide)⟩
      simp only [h0]; rfl
    · have hn0 : ¬(beats Q q R ω B 0 1 ∧ beats Q q R ω B 0 2) := fun h =>
        beats_asymm (hall 0 (by decide)) h.1
      have h1 : beats Q q R ω B 1 2 := hall 2 (by decide)
      simp only [hn0, h1, ↓reduceIte]; rfl
    · have hn0 : ¬(beats Q q R ω B 0 1 ∧ beats Q q R ω B 0 2) := fun h =>
        beats_asymm (hall 0 (by decide)) h.2
      have hn1 : ¬beats Q q R ω B 1 2 := beats_asymm (hall 1 (by decide))
      simp only [hn0, hn1, ↓reduceIte]; rfl

private theorem blockColor_of_strict_majority {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} (hinj : Function.Injective (ω B).2) {c : Fin 3}
    (hmaj : ∀ c' : Fin 3, c' ≠ c → secCount Q q R ω B c' < secCount Q q R ω B c) :
    blockColor Q q R ω B = c :=
  (blockColor_eq_iff_of_injective hinj c).mpr fun c' hc' => Or.inl (hmaj c' hc')

private theorem blockColor_rotSample {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} (hinj : Function.Injective (ω B).2) :
    blockColor Q q R (fun B' => rotSample (ω B')) B = blockColor Q q R ω B + 1 := by
  have hinj' : Function.Injective (((fun B' => rotSample (ω B')) B).2) := by
    intro c₁ c₂ h
    dsimp [rotSample, shiftTie] at h
    exact add_right_cancel (hinj h)
  set c := blockColor Q q R ω B
  have hall := (blockColor_eq_iff_of_injective hinj c).mp rfl
  refine (blockColor_eq_iff_of_injective (Q := Q) (q := q) (R := R)
      (ω := fun B' => rotSample (ω B')) hinj' (c + 1)).mpr fun c' hc' => ?_
  have hc'_eq : c' = (c' + 2) + 1 := by fin_cases c' <;> decide
  rw [hc'_eq, beats_rotSample]
  refine hall (c' + 2) fun h => hc' ?_
  rw [hc'_eq, h]

open Classical in
private theorem measurable_secCount (Q : Multigraph W F) (q : ℝ) (R : ℕ) (B : W) (c : Fin 3) :
    Measurable fun ω : W → BlockSample => secCount Q q R ω B c := by
  have := Fintype.ofFinite F
  have hfn : (fun ω : W → BlockSample => secCount Q q R ω B c) =
      fun ω => ∑ e ∈ (Q.incidenceSet B).toFinset,
        if inOpenSector c (edgeVec2 Q q R ω e) then 1 else 0 := by
    funext ω
    unfold secCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _]
    exact Finset.card_filter (fun e => inOpenSector c (edgeVec2 Q q R ω e))
      (Q.incidenceSet B).toFinset
  rw [hfn]
  refine Finset.measurable_sum _ fun e _ => ?_
  have hm_sec : MeasurableSet {ω : W → BlockSample | inOpenSector c (edgeVec2 Q q R ω e)} := by
    dsimp [inOpenSector]
    exact (measurableSet_lt
        ((by unfold dot2; fun_prop : Measurable (dot2 (normVec c))).comp
          (measurable_edgeVec2 Q q R e)) measurable_const).inter
      (measurableSet_lt measurable_const
        ((by unfold dot2; fun_prop : Measurable (dot2 (normVec (c + 2)))).comp
          (measurable_edgeVec2 Q q R e)))
  exact Measurable.ite hm_sec measurable_const measurable_const

private theorem measurableSet_beats (Q : Multigraph W F) (q : ℝ) (R : ℕ) (B : W)
    (c c' : Fin 3) : MeasurableSet {ω : W → BlockSample | beats Q q R ω B c c'} := by
  dsimp [beats]
  exact (measurableSet_lt (measurable_secCount Q q R B c') (measurable_secCount Q q R B c)).union
    ((measurableSet_eq_fun (measurable_secCount Q q R B c')
      (measurable_secCount Q q R B c)).inter
      (measurableSet_lt
        ((measurable_pi_apply c').comp ((measurable_snd).comp (measurable_pi_apply B)))
        ((measurable_pi_apply c).comp ((measurable_snd).comp (measurable_pi_apply B)))))

private theorem measurableSet_blockColor_eq (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (B : W) (c : Fin 3) :
    MeasurableSet {ω : W → BlockSample | blockColor Q q R ω B = c} := by
  have hm01 := measurableSet_beats Q q R B 0 1
  have hm02 := measurableSet_beats Q q R B 0 2
  have hm12 := measurableSet_beats Q q R B 1 2
  rcases c with ⟨_ | _ | _ | _, hlt⟩
  · have hset : {ω | blockColor Q q R ω B = 0} =
        {ω | beats Q q R ω B 0 1} ∩ {ω | beats Q q R ω B 0 2} := by
      ext ω
      simp only [blockColor, mem_ofPred_eq, mem_inter_iff]
      split_ifs with h0 h1 <;> simp_all
    change MeasurableSet {ω | blockColor Q q R ω B = 0}
    rw [hset]; exact hm01.inter hm02
  · have hset : {ω | blockColor Q q R ω B = 1} =
        ({ω | beats Q q R ω B 0 1} ∩ {ω | beats Q q R ω B 0 2})ᶜ ∩
          {ω | beats Q q R ω B 1 2} := by
      ext ω
      simp only [blockColor, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
      split_ifs with h0 h1 <;> simp_all
    change MeasurableSet {ω | blockColor Q q R ω B = 1}
    rw [hset]; exact (hm01.inter hm02).compl.inter hm12
  · have hset : {ω | blockColor Q q R ω B = 2} =
        ({ω | beats Q q R ω B 0 1} ∩ {ω | beats Q q R ω B 0 2})ᶜ ∩
          ({ω | beats Q q R ω B 1 2})ᶜ := by
      ext ω
      simp only [blockColor, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
      split_ifs with h0 h1 <;> simp_all
    change MeasurableSet {ω | blockColor Q q R ω B = 2}
    rw [hset]; exact (hm01.inter hm02).compl.inter hm12.compl
  · omega

private theorem dependsOn_blockColor (Q : Multigraph W F) (q : ℝ) (R : ℕ) (B : W) :
    DependsOn (fun ω => blockColor Q q R ω B) (closedBall Q.toSimpleGraph B (R + 1)) := by
  intro ω₁ ω₂ h12
  have hB : B ∈ closedBall Q.toSimpleGraph B (R + 1) := by
    simp [closedBall]
  have hsec (c : Fin 3) : secCount Q q R ω₁ B c = secCount Q q R ω₂ B c := by
    classical
    dsimp [secCount]
    congr 1; ext e
    simp only [Finset.mem_filter, @Set.mem_toFinset _ _ (Fintype.ofFinite _)]
    refine and_congr_right fun he => ?_
    rw [edgeVec2_congr he h12]
  have hbeats (c c' : Fin 3) : beats Q q R ω₁ B c c' ↔ beats Q q R ω₂ B c c' := by
    simp only [beats, hsec, h12 B hB]
  dsimp only [blockColor]
  rw [hbeats 0 1, hbeats 0 2, hbeats 1 2]

/-- At any block `B`, the event `{ω | ¬Function.Injective (ω B).2}` has measure zero under
`Measure.pi (fun _ => blockMeasure)`. -/
private theorem measureReal_not_injective_tie_zero (B : W) :
    (Measure.pi fun _ : W => blockMeasure).real
      {ω : W → BlockSample | ¬Function.Injective (ω B).2} = 0 := by
  have hmp_eval : MeasurePreserving (fun ω : W → BlockSample => (ω B).2)
      (Measure.pi fun _ : W => blockMeasure) gaussTie :=
    (MeasureTheory.measurePreserving_snd (μ := gauss2) (ν := gaussTie)).comp
      (MeasureTheory.measurePreserving_eval (fun _ : W => blockMeasure) B)
  have hm : MeasurableSet {τ : Fin 3 → ℝ | ¬Function.Injective τ} := by
    have hset : {τ : Fin 3 → ℝ | ¬Function.Injective τ} =
        ⋃ c₁ : Fin 3, ⋃ c₂ ∈ ({c₁}ᶜ : Set (Fin 3)), {τ | τ c₁ = τ c₂} := by
      ext τ
      simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff, mem_singleton_iff]
      change (¬∀ a₁ a₂ : Fin 3, τ a₁ = τ a₂ → a₁ = a₂) ↔ _
      push Not
      exact ⟨fun ⟨c₁, c₂, heq, hne⟩ => ⟨c₁, c₂, Ne.symm hne, heq⟩,
        fun ⟨c₁, c₂, hne, heq⟩ => ⟨c₁, c₂, heq, Ne.symm hne⟩⟩
    rw [hset]
    exact MeasurableSet.iUnion fun c₁ => (toFinite _).measurableSet_biUnion fun c₂ _ =>
      measurableSet_eq_fun (measurable_pi_apply c₁) (measurable_pi_apply c₂)
  have hpre : {ω : W → BlockSample | ¬Function.Injective (ω B).2} =
      (fun ω : W → BlockSample => (ω B).2) ⁻¹' {τ : Fin 3 → ℝ | ¬Function.Injective τ} := rfl
  rw [hpre, hmp_eval.measureReal_preimage hm.nullMeasurableSet]
  exact gaussTie_not_injective_zero

/-- **Exact `1 / 3` marginal.** By `Z₃`-symmetry (`rotSample`), every block `B` lands in each color
`c : Fin 3` with probability `1 / 3`. -/
private theorem measureReal_blockColor_eq_one_third (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (B : W) (c : Fin 3) :
    (Measure.pi fun _ : W => blockMeasure).real
      {ω | blockColor Q q R ω B = c} = 1 / 3 := by
  set P := Measure.pi fun _ : W => blockMeasure
  set N := {ω : W → BlockSample | ¬Function.Injective (ω B).2}
  have hN0 : P.real N = 0 := measureReal_not_injective_tie_zero B
  have hN_null : P N = 0 := by
    have h := hN0
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at h
    exact h.resolve_right (measure_ne_top _ _)
  have hmp_rot : MeasurePreserving (fun ω B' => rotSample (ω B')) P P :=
    measurePreserving_pi _ _ fun _ => measurePreserving_rotSample
  have hstep (k : Fin 3) :
      P.real {ω | blockColor Q q R ω B = k} = P.real {ω | blockColor Q q R ω B = k + 1} := by
    have hpre_eq : P.real ((fun ω B' => rotSample (ω B')) ⁻¹'
        {ω | blockColor Q q R ω B = k + 1}) =
        P.real {ω | blockColor Q q R ω B = k + 1} :=
      hmp_rot.measureReal_preimage (measurableSet_blockColor_eq Q q R B (k + 1)).nullMeasurableSet
    rw [← hpre_eq]
    refine measureReal_congr ?_
    filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hω
    have hinj : Function.Injective (ω B).2 := by
      dsimp [N] at hω; exact not_not.mp hω
    simp only [mem_preimage, mem_ofPred_eq]
    rw [blockColor_rotSample hinj]
    exact ⟨fun h => by rw [h], fun h => add_right_cancel h⟩
  have h01 : P.real {ω | blockColor Q q R ω B = 0} = P.real {ω | blockColor Q q R ω B = 1} :=
    hstep 0
  have h12 : P.real {ω | blockColor Q q R ω B = 1} = P.real {ω | blockColor Q q R ω B = 2} :=
    hstep 1
  have hpart1 : Disjoint {ω | blockColor Q q R ω B = 0} {ω | blockColor Q q R ω B = 1} :=
    disjoint_left.mpr fun _ h0 h1 => by
      rw [mem_ofPred_eq] at h0 h1; rw [h0] at h1; revert h1; decide
  have hpart2 : Disjoint ({ω | blockColor Q q R ω B = 0} ∪ {ω | blockColor Q q R ω B = 1})
      {ω | blockColor Q q R ω B = 2} :=
    disjoint_left.mpr fun _ h01' h2 => by
      rcases h01' with h0 | h1
      · rw [mem_ofPred_eq] at h0 h2; rw [h0] at h2; revert h2; decide
      · rw [mem_ofPred_eq] at h1 h2; rw [h1] at h2; revert h2; decide
  have huniv : ({ω | blockColor Q q R ω B = 0} ∪ {ω | blockColor Q q R ω B = 1}) ∪
      {ω | blockColor Q q R ω B = 2} = univ := by
    ext ω
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    rcases hc : blockColor Q q R ω B with ⟨val, hlt⟩
    interval_cases val
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl
  have hsum : P.real {ω | blockColor Q q R ω B = 0} + P.real {ω | blockColor Q q R ω B = 1} +
      P.real {ω | blockColor Q q R ω B = 2} = 1 := by
    rw [← measureReal_union hpart1 (measurableSet_blockColor_eq Q q R B 1),
      ← measureReal_union hpart2 (measurableSet_blockColor_eq Q q R B 2),
      huniv, probReal_univ]
  rcases c with ⟨_ | _ | _ | _, hlt⟩
  · change P.real {ω | blockColor Q q R ω B = 0} = 1 / 3; linarith only [h01, h12, hsum]
  · change P.real {ω | blockColor Q q R ω B = 1} = 1 / 3; linarith only [h01, h12, hsum]
  · change P.real {ω | blockColor Q q R ω B = 2} = 1 / 3; linarith only [h01, h12, hsum]
  · omega

/-- Event that quotient edge `e` crosses between color `c` and color `c + 1`. -/
private def cutPairEvent (Q : Multigraph W F) (q : ℝ) (R : ℕ) (c : Fin 3) (e : F) :
    Set (W → BlockSample) :=
  {ω | (blockColor Q q R ω (Q.src e) = c ∧ blockColor Q q R ω (Q.tgt e) = c + 1) ∨
    (blockColor Q q R ω (Q.src e) = c + 1 ∧ blockColor Q q R ω (Q.tgt e) = c)}

/-- Event that quotient edge `e` is bichromatic (`blockColor (src e) ≠ blockColor (tgt e)`). -/
private def cutAnyEvent (Q : Multigraph W F) (q : ℝ) (R : ℕ) (e : F) :
    Set (W → BlockSample) :=
  {ω | blockColor Q q R ω (Q.src e) ≠ blockColor Q q R ω (Q.tgt e)}

private theorem measurableSet_cutPairEvent (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (c : Fin 3) (e : F) : MeasurableSet (cutPairEvent Q q R c e) :=
  ((measurableSet_blockColor_eq Q q R (Q.src e) c).inter
      (measurableSet_blockColor_eq Q q R (Q.tgt e) (c + 1))).union
    ((measurableSet_blockColor_eq Q q R (Q.src e) (c + 1)).inter
      (measurableSet_blockColor_eq Q q R (Q.tgt e) c))

private theorem dependsOn_cutPairEvent (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (c : Fin 3) (e : F) :
    DependsOn (· ∈ cutPairEvent Q q R c e)
      (closedBall Q.toSimpleGraph (Q.src e) (R + 2)) := by
  intro ω₁ ω₂ h12
  have hsrc_sub : closedBall Q.toSimpleGraph (Q.src e) (R + 1) ⊆
      closedBall Q.toSimpleGraph (Q.src e) (R + 2) := by
    intro z hz
    simp only [closedBall, mem_ofPred_eq] at hz ⊢
    exact hz.trans (Nat.cast_le.mpr (by omega))
  have htgt_sub : closedBall Q.toSimpleGraph (Q.tgt e) (R + 1) ⊆
      closedBall Q.toSimpleGraph (Q.src e) (R + 2) :=
    closedBall_tgt_subset e (R + 1)
  have hcs := dependsOn_blockColor Q q R (Q.src e) fun z hz => h12 z (hsrc_sub hz)
  have hct := dependsOn_blockColor Q q R (Q.tgt e) fun z hz => h12 z (htgt_sub hz)
  simp only [cutPairEvent, mem_ofPred_eq, hcs, hct]

/-- **Exact `1 / 3` cut symmetry.** Each unordered color pair `{c, c + 1}` receives `1 / 3` of the
bichromatic probability of every edge `e`. -/
private theorem measureReal_cutPairEvent_eq_third (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (c : Fin 3) (e : F) :
    (Measure.pi fun _ : W => blockMeasure).real (cutPairEvent Q q R c e) =
      1 / 3 * (Measure.pi fun _ : W => blockMeasure).real (cutAnyEvent Q q R e) := by
  set P := Measure.pi fun _ : W => blockMeasure
  set N := {ω : W → BlockSample | ¬Function.Injective (ω (Q.src e)).2} ∪
    {ω : W → BlockSample | ¬Function.Injective (ω (Q.tgt e)).2}
  have hN0 : P.real N = 0 := by
    have hle := (measureReal_union_le
      {ω : W → BlockSample | ¬Function.Injective (ω (Q.src e)).2}
      {ω : W → BlockSample | ¬Function.Injective (ω (Q.tgt e)).2}).trans_eq
      (by rw [measureReal_not_injective_tie_zero, measureReal_not_injective_tie_zero, add_zero])
    exact le_antisymm hle measureReal_nonneg
  have hN_null : P N = 0 := by
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hN0
    exact hN0.resolve_right (measure_ne_top _ _)
  have hmp_rot : MeasurePreserving (fun ω B' => rotSample (ω B')) P P :=
    measurePreserving_pi _ _ fun _ => measurePreserving_rotSample
  have hstep (k : Fin 3) :
      P.real (cutPairEvent Q q R k e) = P.real (cutPairEvent Q q R (k + 1) e) := by
    rw [← hmp_rot.measureReal_preimage
      (measurableSet_cutPairEvent Q q R (k + 1) e).nullMeasurableSet]
    refine measureReal_congr ?_
    filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hω
    simp only [N, mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_not] at hω
    simp only [mem_preimage, cutPairEvent, mem_ofPred_eq]
    rw [blockColor_rotSample hω.1, blockColor_rotSample hω.2]
    exact ⟨fun h => h.imp (fun ⟨h1, h2⟩ => ⟨by rw [h1], by rw [h2]⟩)
        (fun ⟨h1, h2⟩ => ⟨by rw [h1], by rw [h2]⟩),
      fun h => h.imp (fun ⟨h1, h2⟩ => ⟨add_right_cancel h1, add_right_cancel h2⟩)
        (fun ⟨h1, h2⟩ => ⟨add_right_cancel h1, add_right_cancel h2⟩)⟩
  have h01 : P.real (cutPairEvent Q q R 0 e) = P.real (cutPairEvent Q q R 1 e) := hstep 0
  have h12 : P.real (cutPairEvent Q q R 1 e) = P.real (cutPairEvent Q q R 2 e) := hstep 1
  have hd01 : Disjoint (cutPairEvent Q q R 0 e) (cutPairEvent Q q R 1 e) := by
    refine disjoint_left.mpr fun ω h0 h1 => ?_
    rcases h0 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases h1 with ⟨hc1, hd1⟩ | ⟨hc1, hd1⟩ <;>
      (rw [ha] at hc1; rw [hb] at hd1; revert hc1 hd1; decide)
  have hd012 : Disjoint (cutPairEvent Q q R 0 e ∪ cutPairEvent Q q R 1 e)
      (cutPairEvent Q q R 2 e) := by
    refine disjoint_left.mpr fun ω h01' h2 => ?_
    rcases h01' with (⟨ha, hb⟩ | ⟨ha, hb⟩) | (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      rcases h2 with ⟨hc1, hd1⟩ | ⟨hc1, hd1⟩ <;>
      (rw [ha] at hc1; rw [hb] at hd1; revert hc1 hd1; decide)
  have hunion : (cutPairEvent Q q R 0 e ∪ cutPairEvent Q q R 1 e) ∪ cutPairEvent Q q R 2 e =
      cutAnyEvent Q q R e := by
    ext ω
    simp only [mem_union, cutPairEvent, cutAnyEvent, mem_ofPred_eq]
    generalize blockColor Q q R ω (Q.src e) = a
    generalize blockColor Q q R ω (Q.tgt e) = b
    fin_cases a <;> fin_cases b <;> decide
  have hsum : P.real (cutPairEvent Q q R 0 e) + P.real (cutPairEvent Q q R 1 e) +
      P.real (cutPairEvent Q q R 2 e) = P.real (cutAnyEvent Q q R e) := by
    rw [← measureReal_union hd01 (measurableSet_cutPairEvent Q q R 1 e),
      ← measureReal_union hd012 (measurableSet_cutPairEvent Q q R 2 e), hunion]
  rcases c with ⟨_ | _ | _ | _, hlt⟩
  · change P.real (cutPairEvent Q q R 0 e) = _; linarith only [h01, h12, hsum]
  · change P.real (cutPairEvent Q q R 1 e) = _; linarith only [h01, h12, hsum]
  · change P.real (cutPairEvent Q q R 2 e) = _; linarith only [h01, h12, hsum]
  · omega

/-! ### Degree-`3` mismatch expectation via `rayCross` and `ConvexCap` -/

open Classical in
/-- Number of incident edges at `B` whose `2`D vector does *not* lie in `B`'s chosen open sector. -/
private noncomputable def badCount (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) : ℕ :=
  ((@Set.toFinset F (Q.incidenceSet B) (Fintype.ofFinite _)).filter fun e =>
    ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e)).card

open Classical in
private theorem integrable_badCount {Q : Multigraph W F} (hdeg : Q.MaxDegreeLE 3)
    (q : ℝ) (R : ℕ) (B : W) :
    Integrable (fun ω => (badCount Q q R ω B : ℝ))
      (Measure.pi fun _ : W => blockMeasure) := by
  have := Fintype.ofFinite F
  have hfn : (fun ω : W → BlockSample => (badCount Q q R ω B : ℝ)) =
      fun ω => ∑ e ∈ (Q.incidenceSet B).toFinset,
        if ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e) then (1 : ℝ) else 0 := by
    funext ω
    unfold badCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _]
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
  have hm_bad : Measurable (fun ω : W → BlockSample => (badCount Q q R ω B : ℝ)) := by
    rw [hfn]
    refine Finset.measurable_sum _ fun e _ => ?_
    have hm_in : MeasurableSet
        {ω : W → BlockSample | inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e)} := by
      have hsplit : {ω : W → BlockSample |
          inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e)} =
          ⋃ c : Fin 3, {ω | blockColor Q q R ω B = c} ∩
            {ω | inOpenSector c (edgeVec2 Q q R ω e)} := by
        ext ω
        simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
        exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, hc, h⟩ => hc ▸ h⟩
      rw [hsplit]
      refine MeasurableSet.iUnion fun c => (measurableSet_blockColor_eq Q q R B c).inter ?_
      dsimp [inOpenSector]
      exact (measurableSet_lt
          ((by unfold dot2; fun_prop : Measurable (dot2 (normVec c))).comp
            (measurable_edgeVec2 Q q R e)) measurable_const).inter
        (measurableSet_lt measurable_const
          ((by unfold dot2; fun_prop : Measurable (dot2 (normVec (c + 2)))).comp
            (measurable_edgeVec2 Q q R e)))
    exact Measurable.ite hm_in.compl measurable_const measurable_const
  refine Integrable.of_bound hm_bad.aestronglyMeasurable 3
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hle : badCount Q q R ω B ≤ 3 := by
    unfold badCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _]
    exact (Finset.card_filter_le _ _).trans (by rw [← Set.ncard_eq_toFinset_card']; exact hdeg B)
  exact_mod_cast hle

open Classical in
/-- **Pointwise degree-`3` mismatch inequality.** Suppose `s = {e₀, e₁, e₂}` has size `3`, equals
`Q.incidenceSet B`, `(ω B).2` is injective, every `e ∈ s` avoids the three sector boundary lines,
and edges in distinct open sectors are non-collinear (`det2 ≠ 0`). Then `4 * badCount Q q R ω B` is
at most the sum of `rayCross` indicators over `s.offDiag × Fin 3` plus `2` times the
origin-in-triangle indicator `(0, 0) ∈ conv(z_{e₀}, z_{e₁}, z_{e₂})`. -/
private theorem four_mul_badCount_le [Fintype F] {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} {e₀ e₁ e₂ : F}
    (h01 : e₀ ≠ e₁) (h12 : e₁ ≠ e₂) (h02 : e₀ ≠ e₂)
    (hinc : ({e₀, e₁, e₂} : Finset F) = (Q.incidenceSet B).toFinset)
    (hinj : Function.Injective (ω B).2)
    (hray : ∀ e ∈ ({e₀, e₁, e₂} : Finset F), ∀ c : Fin 3,
      dot2 (normVec c) (edgeVec2 Q q R ω e) ≠ 0)
    (hdet : ∀ a ∈ ({e₀, e₁, e₂} : Finset F), ∀ b ∈ ({e₀, e₁, e₂} : Finset F),
      ∀ c₁ c₂ : Fin 3, inOpenSector c₁ (edgeVec2 Q q R ω a) →
        inOpenSector c₂ (edgeVec2 Q q R ω b) → c₁ ≠ c₂ →
        det2 (edgeVec2 Q q R ω a) (edgeVec2 Q q R ω b) ≠ 0) :
    4 * badCount Q q R ω B ≤
      (∑ p ∈ ({e₀, e₁, e₂} : Finset F).offDiag, ∑ c : Fin 3,
        if rayCross c (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) then 1 else 0) +
      2 * (if ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
        w₀ * (edgeVec2 Q q R ω e₀).1 + w₁ * (edgeVec2 Q q R ω e₁).1 +
          w₂ * (edgeVec2 Q q R ω e₂).1 = 0 ∧
        w₀ * (edgeVec2 Q q R ω e₀).2 + w₁ * (edgeVec2 Q q R ω e₁).2 +
          w₂ * (edgeVec2 Q q R ω e₂).2 = 0 then 1 else 0) := by
  set s : Finset F := {e₀, e₁, e₂}
  let fn (p : F × F) : ℕ :=
    ∑ c : Fin 3, if rayCross c (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) then 1 else 0
  have fn_swap (x y : F) : fn (x, y) = fn (y, x) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : rayCross c (edgeVec2 Q q R ω x) (edgeVec2 Q q R ω y)
    · have h' := (rayCross_comm c _ _).mp h; simp only [h, h', ↓reduceIte]
    · have h' := mt (rayCross_comm c _ _).mpr h; simp only [h, h', ↓reduceIte]
  have two_mul_sum_le (U : Finset (F × F)) (hU : U ⊆ s.offDiag)
      (hasym : ∀ p ∈ U, (p.2, p.1) ∉ U) :
      2 * ∑ p ∈ U, fn p ≤ ∑ p ∈ s.offDiag, fn p := by
    let sw : F × F ↪ F × F := ⟨Prod.swap, Prod.swap_injective⟩
    have hmap_sub : U.map sw ⊆ s.offDiag := by
      intro q_p hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
      obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp (hU hp)
      exact Finset.mem_offDiag.mpr ⟨h2, h1, hne.symm⟩
    have hdisj : Disjoint U (U.map sw) := by
      refine Finset.disjoint_right.mpr fun q_p hq hqU => ?_
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
      exact hasym p hp hqU
    have hmap_eq : ∑ p ∈ U.map sw, fn p = ∑ p ∈ U, fn p := by
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun p _ => fn_swap p.2 p.1
    calc 2 * ∑ p ∈ U, fn p = ∑ p ∈ U, fn p + ∑ p ∈ U.map sw, fn p := by rw [hmap_eq]; ring
      _ = ∑ p ∈ U ∪ U.map sw, fn p := (Finset.sum_union hdisj).symm
      _ ≤ ∑ p ∈ s.offDiag, fn p := Finset.sum_le_sum_of_subset (Finset.union_subset hU hmap_sub)
  have hs_card : s.card = 3 := by
    dsimp [s]
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]), Finset.card_pair h12]
  have he₀ : e₀ ∈ s := by simp [s]
  have he₁ : e₁ ∈ s := by simp [s]
  have he₂ : e₂ ∈ s := by simp [s]
  obtain ⟨s₀, hs₀⟩ := exists_inOpenSector_of_ne_zero (hray e₀ he₀)
  obtain ⟨s₁, hs₁⟩ := exists_inOpenSector_of_ne_zero (hray e₁ he₁)
  obtain ⟨s₂, hs₂⟩ := exists_inOpenSector_of_ne_zero (hray e₂ he₂)
  have hsec_eq (c : Fin 3) :
      secCount Q q R ω B c = (s.filter fun e => inOpenSector c (edgeVec2 Q q R ω e)).card := by
    unfold secCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _, ← hinc]
  have hbad_eq : badCount Q q R ω B =
      (s.filter fun e => ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e)).card := by
    unfold badCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _, ← hinc]
  have hbad_compl : badCount Q q R ω B + secCount Q q R ω B (blockColor Q q R ω B) = 3 := by
    rw [hbad_eq, hsec_eq, add_comm, Finset.card_filter_add_card_filter_not, hs_card]
  have case_two_one {a₁ a₂ b : F} (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s) (hb : b ∈ s)
      (ha12 : a₁ ≠ a₂) (ha1b : a₁ ≠ b) (ha2b : a₂ ≠ b)
      {c₀ c₁ : Fin 3} (hc01 : c₀ ≠ c₁)
      (h_a₁ : inOpenSector c₀ (edgeVec2 Q q R ω a₁))
      (h_a₂ : inOpenSector c₀ (edgeVec2 Q q R ω a₂))
      (h_b : inOpenSector c₁ (edgeVec2 Q q R ω b)) :
      4 * badCount Q q R ω B ≤ ∑ p ∈ s.offDiag, fn p := by
    have hs_perm : s = {a₁, a₂, b} := by
      refine (Finset.eq_of_subset_of_card_le (s := {a₁, a₂, b}) (t := s) ?_ ?_).symm
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · rw [hs_card, Finset.card_insert_of_notMem (by simp [ha12, ha1b]),
          Finset.card_pair ha2b]
    have hcnt_c₀ : secCount Q q R ω B c₀ = 2 := by
      rw [hsec_eq, hs_perm]
      have hnb : ¬inOpenSector c₀ (edgeVec2 Q q R ω b) := fun h => hc01 (inOpenSector_unique h h_b)
      simp only [Finset.filter_insert, h_a₁, h_a₂, Finset.filter_singleton, hnb, ↓reduceIte]
      exact Finset.card_pair ha12
    have hcnt_lt : ∀ c' : Fin 3, c' ≠ c₀ → secCount Q q R ω B c' < 2 := fun c' hc' => by
      rw [hsec_eq, hs_perm]
      have hn1 : ¬inOpenSector c' (edgeVec2 Q q R ω a₁) :=
        fun h => hc' (inOpenSector_unique h h_a₁)
      have hn2 : ¬inOpenSector c' (edgeVec2 Q q R ω a₂) :=
        fun h => hc' (inOpenSector_unique h h_a₂)
      simp only [Finset.filter_insert, hn1, hn2, ↓reduceIte]
      exact (Finset.card_filter_le _ _).trans_lt (by simp)
    have hcol : blockColor Q q R ω B = c₀ :=
      blockColor_of_strict_majority hinj fun c' hc' => by rw [hcnt_c₀]; exact hcnt_lt c' hc'
    have hbad1 : badCount Q q R ω B = 1 := by
      rw [hcol, hcnt_c₀] at hbad_compl; omega
    rw [hbad1]
    have hadj : c₁ = c₀ + 1 ∨ c₀ = c₁ + 1 := by
      fin_cases c₀ <;> fin_cases c₁ <;> (try exact absurd rfl hc01) <;> decide
    rcases hadj with rfl | hrev
    · have hp1 : (a₁, b) ∈ s.offDiag := Finset.mem_offDiag.mpr ⟨ha₁, hb, ha1b⟩
      have hp2 : (a₂, b) ∈ s.offDiag := Finset.mem_offDiag.mpr ⟨ha₂, hb, ha2b⟩
      have hp_ne : (a₁, b) ≠ (a₂, b) := fun h => ha12 (Prod.mk.inj h).1
      have hr1 := (one_or_two_le_sum_rayCross c₀ h_a₁ h_b
        (hdet a₁ ha₁ b hb c₀ (c₀ + 1) h_a₁ h_b (by fin_cases c₀ <;> decide))).1
      have hr2 := (one_or_two_le_sum_rayCross c₀ h_a₂ h_b
        (hdet a₂ ha₂ b hb c₀ (c₀ + 1) h_a₂ h_b (by fin_cases c₀ <;> decide))).1
      have hsub : ({(a₁, b), (a₂, b)} : Finset (F × F)) ⊆ s.offDiag := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> assumption
      have hasym : ∀ p ∈ ({(a₁, b), (a₂, b)} : Finset (F × F)),
          (p.2, p.1) ∉ ({(a₁, b), (a₂, b)} : Finset (F × F)) := by
        rintro p hp hsw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hsw
        rcases hp with rfl | rfl <;> rcases hsw with h | h
        · exact ha1b (Prod.mk.inj h).1.symm
        · exact ha2b (Prod.mk.inj h).1.symm
        · exact ha1b (Prod.mk.inj h).1.symm
        · exact ha2b (Prod.mk.inj h).1.symm
      have hU := two_mul_sum_le _ hsub hasym
      rw [Finset.sum_pair hp_ne] at hU
      change 1 ≤ fn (a₁, b) at hr1
      change 1 ≤ fn (a₂, b) at hr2
      omega
    · subst hrev
      have hp1 : (b, a₁) ∈ s.offDiag := Finset.mem_offDiag.mpr ⟨hb, ha₁, ha1b.symm⟩
      have hp2 : (b, a₂) ∈ s.offDiag := Finset.mem_offDiag.mpr ⟨hb, ha₂, ha2b.symm⟩
      have hp_ne : (b, a₁) ≠ (b, a₂) := fun h => ha12 (Prod.mk.inj h).2
      have hr1 := (one_or_two_le_sum_rayCross c₁ h_b h_a₁
        (hdet b hb a₁ ha₁ c₁ (c₁ + 1) h_b h_a₁ (by fin_cases c₁ <;> decide))).1
      have hr2 := (one_or_two_le_sum_rayCross c₁ h_b h_a₂
        (hdet b hb a₂ ha₂ c₁ (c₁ + 1) h_b h_a₂ (by fin_cases c₁ <;> decide))).1
      have hsub : ({(b, a₁), (b, a₂)} : Finset (F × F)) ⊆ s.offDiag := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> assumption
      have hasym : ∀ p ∈ ({(b, a₁), (b, a₂)} : Finset (F × F)),
          (p.2, p.1) ∉ ({(b, a₁), (b, a₂)} : Finset (F × F)) := by
        rintro p hp hsw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hsw
        rcases hp with rfl | rfl <;> rcases hsw with h | h
        · exact ha1b (Prod.mk.inj h).1
        · exact ha1b (Prod.mk.inj h).1
        · exact ha2b (Prod.mk.inj h).1
        · exact ha2b (Prod.mk.inj h).1
      have hU := two_mul_sum_le _ hsub hasym
      rw [Finset.sum_pair hp_ne] at hU
      change 1 ≤ fn (b, a₁) at hr1
      change 1 ≤ fn (b, a₂) at hr2
      omega
  by_cases hs01 : s₀ = s₁
  · subst hs01
    by_cases hs02 : s₀ = s₂
    · subst hs02
      have hcnt3 : secCount Q q R ω B s₀ = 3 := by
        rw [hsec_eq]
        have hall : s.filter (fun e => inOpenSector s₀ (edgeVec2 Q q R ω e)) = s := by
          refine Finset.filter_eq_self.mpr fun e he => ?_
          dsimp [s] at he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl | rfl <;> assumption
        rw [hall, hs_card]
      have hcnt0 : ∀ c' : Fin 3, c' ≠ s₀ → secCount Q q R ω B c' = 0 := fun c' hc' => by
        rw [hsec_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hsec
        dsimp [s] at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hc' (inOpenSector_unique hsec hs₀)
        · exact hc' (inOpenSector_unique hsec hs₁)
        · exact hc' (inOpenSector_unique hsec hs₂)
      have hcol : blockColor Q q R ω B = s₀ :=
        blockColor_of_strict_majority hinj fun c' hc' => by rw [hcnt3, hcnt0 c' hc']; omega
      rw [hcol, hcnt3] at hbad_compl
      have hb0 : badCount Q q R ω B = 0 := by omega
      rw [hb0]; omega
    · exact (case_two_one he₀ he₁ he₂ h01 h02 h12 hs02 hs₀ hs₁ hs₂).trans (Nat.le_add_right _ _)
  · by_cases hs02 : s₀ = s₂
    · subst hs02
      exact (case_two_one he₀ he₂ he₁ h02 h01 h12.symm hs01 hs₀ hs₂ hs₁).trans
        (Nat.le_add_right _ _)
    · by_cases hs12 : s₁ = s₂
      · subst hs12
        exact (case_two_one he₁ he₂ he₀ h12 h01.symm h02.symm (Ne.symm hs01) hs₁ hs₂ hs₀).trans
          (Nat.le_add_right _ _)
      · have hex_sec (c : Fin 3) : ∃ u ∈ s, inOpenSector c (edgeVec2 Q q R ω u) := by
          have himg : ({s₀, s₁, s₂} : Finset (Fin 3)) = Finset.univ := by
            refine Finset.eq_univ_of_card _ ?_
            rw [Finset.card_insert_of_notMem (by simp [hs01, hs02]), Finset.card_pair hs12,
              Fintype.card_fin]
          have hmem : c ∈ ({s₀, s₁, s₂} : Finset (Fin 3)) := by rw [himg]; exact Finset.mem_univ c
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl | rfl
          · exact ⟨e₀, he₀, hs₀⟩
          · exact ⟨e₁, he₁, hs₁⟩
          · exact ⟨e₂, he₂, hs₂⟩
        obtain ⟨u₀, hu₀, hsec_u₀⟩ := hex_sec 0
        obtain ⟨u₁, hu₁, hsec_u₁⟩ := hex_sec 1
        obtain ⟨u₂, hu₂, hsec_u₂⟩ := hex_sec 2
        have hu01 : u₀ ≠ u₁ := fun h => by
          subst h; exact absurd (inOpenSector_unique hsec_u₀ hsec_u₁) (by decide)
        have hu12 : u₁ ≠ u₂ := fun h => by
          subst h; exact absurd (inOpenSector_unique hsec_u₁ hsec_u₂) (by decide)
        have hu20 : u₂ ≠ u₀ := fun h => by
          subst h; exact absurd (inOpenSector_unique hsec_u₂ hsec_u₀) (by decide)
        have hs_u : s = {u₀, u₁, u₂} := by
          refine (Finset.eq_of_subset_of_card_le (s := {u₀, u₁, u₂}) (t := s) ?_ ?_).symm
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> assumption
          · rw [hs_card, Finset.card_insert_of_notMem (by simp [hu01, hu20.symm]),
              Finset.card_pair hu12]
        have hcnt1 (c : Fin 3) : secCount Q q R ω B c = 1 := by
          rw [hsec_eq, hs_u]
          rcases c with ⟨_ | _ | _ | _, hlt⟩
          · change (({u₀, u₁, u₂} : Finset F).filter
              fun e => inOpenSector 0 (edgeVec2 Q q R ω e)).card = 1
            have hn1 : ¬inOpenSector 0 (edgeVec2 Q q R ω u₁) := fun h =>
              absurd (inOpenSector_unique h hsec_u₁) (by decide)
            have hn2 : ¬inOpenSector 0 (edgeVec2 Q q R ω u₂) := fun h =>
              absurd (inOpenSector_unique h hsec_u₂) (by decide)
            simp only [Finset.filter_insert, hsec_u₀, hn1, Finset.filter_singleton, hn2,
              ↓reduceIte]
            exact Finset.card_singleton u₀
          · change (({u₀, u₁, u₂} : Finset F).filter
              fun e => inOpenSector 1 (edgeVec2 Q q R ω e)).card = 1
            have hn0 : ¬inOpenSector 1 (edgeVec2 Q q R ω u₀) := fun h =>
              absurd (inOpenSector_unique h hsec_u₀) (by decide)
            have hn2 : ¬inOpenSector 1 (edgeVec2 Q q R ω u₂) := fun h =>
              absurd (inOpenSector_unique h hsec_u₂) (by decide)
            simp only [Finset.filter_insert, hn0, hsec_u₁, Finset.filter_singleton, hn2,
              ↓reduceIte]
            exact Finset.card_singleton u₁
          · change (({u₀, u₁, u₂} : Finset F).filter
              fun e => inOpenSector 2 (edgeVec2 Q q R ω e)).card = 1
            have hn0 : ¬inOpenSector 2 (edgeVec2 Q q R ω u₀) := fun h =>
              absurd (inOpenSector_unique h hsec_u₀) (by decide)
            have hn1 : ¬inOpenSector 2 (edgeVec2 Q q R ω u₁) := fun h =>
              absurd (inOpenSector_unique h hsec_u₁) (by decide)
            simp only [Finset.filter_insert, hn0, hn1, Finset.filter_singleton, hsec_u₂,
              ↓reduceIte, Finset.card_singleton]
          · omega
        have hbad2 : badCount Q q R ω B = 2 := by
          rw [hcnt1] at hbad_compl; omega
        rw [hbad2]
        have hd01 := hdet u₀ hu₀ u₁ hu₁ 0 1 hsec_u₀ hsec_u₁ (by decide)
        have hd12 := hdet u₁ hu₁ u₂ hu₂ 1 2 hsec_u₁ hsec_u₂ (by decide)
        have hd20 := hdet u₂ hu₂ u₀ hu₀ 2 0 hsec_u₂ hsec_u₀ (by decide)
        obtain ⟨hr0_1, hr0_2⟩ := one_or_two_le_sum_rayCross 0 hsec_u₀ hsec_u₁ hd01
        obtain ⟨hr1_1, hr1_2⟩ := one_or_two_le_sum_rayCross 1 hsec_u₁ hsec_u₂ hd12
        obtain ⟨hr2_1, hr2_2⟩ := one_or_two_le_sum_rayCross 2 hsec_u₂ hsec_u₀ hd20
        let T : Finset (F × F) := {(u₀, u₁), (u₁, u₂), (u₂, u₀)}
        have hT_sub : T ⊆ s.offDiag := by
          intro p hp
          simp only [T, Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl
          · exact Finset.mem_offDiag.mpr ⟨hu₀, hu₁, hu01⟩
          · exact Finset.mem_offDiag.mpr ⟨hu₁, hu₂, hu12⟩
          · exact Finset.mem_offDiag.mpr ⟨hu₂, hu₀, hu20⟩
        have hT_asym : ∀ p ∈ T, (p.2, p.1) ∉ T := by
          rintro p hp hsw
          simp only [T, Finset.mem_insert, Finset.mem_singleton] at hp hsw
          rcases hp with rfl | rfl | rfl
          · rcases hsw with h | h | h
            · exact hu01 (Prod.mk.inj h).2
            · exact hu20 (Prod.mk.inj h).2.symm
            · exact hu12 (Prod.mk.inj h).1
          · rcases hsw with h | h | h
            · exact hu20 (Prod.mk.inj h).1
            · exact hu12 (Prod.mk.inj h).2
            · exact hu01 (Prod.mk.inj h).2.symm
          · rcases hsw with h | h | h
            · exact hu12 (Prod.mk.inj h).2.symm
            · exact hu01 (Prod.mk.inj h).1
            · exact hu20 (Prod.mk.inj h).2
        have hT_sum : (∑ p ∈ T, fn p) = fn (u₀, u₁) + (fn (u₁, u₂) + fn (u₂, u₀)) := by
          dsimp [T]
          have hnot_mem : (u₀, u₁) ∉ ({(u₁, u₂), (u₂, u₀)} : Finset (F × F)) := by
            intro hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with h | h
            · exact hu01 (Prod.mk.inj h).1
            · exact hu20 (Prod.mk.inj h).1.symm
          rw [Finset.sum_insert hnot_mem,
            Finset.sum_pair (by intro h; exact hu12 (Prod.mk.inj h).1)]
        have hT_two_le : 2 * ∑ p ∈ T, fn p ≤ ∑ p ∈ s.offDiag, fn p :=
          two_mul_sum_le T hT_sub hT_asym
        by_cases hall_pos : 0 < det2 (edgeVec2 Q q R ω u₀) (edgeVec2 Q q R ω u₁) ∧
            0 < det2 (edgeVec2 Q q R ω u₁) (edgeVec2 Q q R ω u₂) ∧
            0 < det2 (edgeVec2 Q q R ω u₂) (edgeVec2 Q q R ω u₀)
        · obtain ⟨w₀', w₁', w₂', hw₀', hw₁', hw₂', hsum', hx', hy'⟩ :=
            convex_zero_of_pos_det2 hall_pos.1 hall_pos.2.1 hall_pos.2.2
          have hex_conv : ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
              w₀ * (edgeVec2 Q q R ω e₀).1 + w₁ * (edgeVec2 Q q R ω e₁).1 +
                w₂ * (edgeVec2 Q q R ω e₂).1 = 0 ∧
              w₀ * (edgeVec2 Q q R ω e₀).2 + w₁ * (edgeVec2 Q q R ω e₁).2 +
                w₂ * (edgeVec2 Q q R ω e₂).2 = 0 := by
            let wt (e : F) : ℝ :=
              (if e = u₀ then w₀' else 0) + (if e = u₁ then w₁' else 0) +
                (if e = u₂ then w₂' else 0)
            have hwt_nonneg (e : F) : 0 ≤ wt e := by
              dsimp [wt]
              refine add_nonneg (add_nonneg ?_ ?_) ?_ <;> split_ifs <;> linarith
            have hwt_u0 : wt u₀ = w₀' := by simp [wt, hu01, hu20.symm]
            have hwt_u1 : wt u₁ = w₁' := by simp [wt, hu01.symm, hu12]
            have hwt_u2 : wt u₂ = w₂' := by simp [wt, hu20, hu12.symm]
            have hsum_s : ∀ f : F → ℝ, f e₀ + f e₁ + f e₂ = f u₀ + f u₁ + f u₂ := fun f => by
              have h1 : ∑ x ∈ s, f x = f e₀ + (f e₁ + f e₂) := by
                dsimp [s]
                rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_pair h12]
              have h2 : ∑ x ∈ s, f x = f u₀ + (f u₁ + f u₂) := by
                rw [hs_u, Finset.sum_insert (by simp [hu01, hu20.symm]), Finset.sum_pair hu12]
              linarith only [h1, h2]
            refine ⟨wt e₀, wt e₁, wt e₂, hwt_nonneg e₀, hwt_nonneg e₁, hwt_nonneg e₂, ?_, ?_, ?_⟩
            · rw [hsum_s wt, hwt_u0, hwt_u1, hwt_u2, hsum']
            · rw [hsum_s (fun e => wt e * (edgeVec2 Q q R ω e).1), hwt_u0, hwt_u1, hwt_u2, hx']
            · rw [hsum_s (fun e => wt e * (edgeVec2 Q q R ω e).2), hwt_u0, hwt_u1, hwt_u2, hy']
          simp only [hex_conv, ↓reduceIte]
          change 4 * 2 ≤ (∑ p ∈ s.offDiag, fn p) + 2 * 1
          have h3 : 3 ≤ ∑ p ∈ T, fn p := by
            rw [hT_sum]; dsimp [fn]; omega
          omega
        · have h4 : 4 ≤ ∑ p ∈ T, fn p := by
            rw [hT_sum]
            dsimp [fn]
            rcases lt_or_gt_of_ne hd01 with hn0 | hp0
            · have := hr0_2 hn0; omega
            · rcases lt_or_gt_of_ne hd12 with hn1 | hp1
              · have := hr1_2 hn1; omega
              · rcases lt_or_gt_of_ne hd20 with hn2 | hp2
                · have := hr2_2 hn2; omega
                · exact absurd ⟨hp0, hp1, hp2⟩ hall_pos
          change 4 * 2 ≤ (∑ p ∈ s.offDiag, fn p) + _
          omega

/-- Probability of `rayCross c` on any ordered pair `(e₁, e₂)` is at most
`arccos ⟪edgeVector e₁, edgeVector e₂⟫ / (2π)`. -/
private theorem measureReal_rayCross_le {Q : Multigraph W F} (hloop : Q.Loopless)
    (hdeg : Q.MaxDegreeLE 3) {q : ℝ} (hq : 0 ≤ q) {R : ℕ} {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (c : Fin 3) (e₁ e₂ : F) :
    (Measure.pi fun _ : W => blockMeasure).real
      {ω | rayCross c (edgeVec2 Q q R ω e₁) (edgeVec2 Q q R ω e₂)} ≤
        arccos ⟪edgeVector Q q R e₁, edgeVector Q q R e₂⟫ / (2 * π) := by
  set P := Measure.pi fun _ : W => blockMeasure
  set A : Set (W → BlockSample) :=
    {ω | rayCross c (edgeVec2 Q q R ω e₁) (edgeVec2 Q q R ω e₂)}
  set Aneg : Set (W → BlockSample) := (fun ω : W → BlockSample => fun B => negSample (ω B)) ⁻¹' A
  have hm_dot (e : F) : Measurable fun ω : W → BlockSample =>
      dot2 (normVec c) (edgeVec2 Q q R ω e) :=
    (by unfold dot2; fun_prop : Measurable (dot2 (normVec c))).comp (measurable_edgeVec2 Q q R e)
  have hm_det : Measurable fun ω : W → BlockSample =>
      det2 (edgeVec2 Q q R ω e₁) (edgeVec2 Q q R ω e₂) :=
    (by unfold det2; fun_prop : Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => det2 p.1 p.2).comp
      ((measurable_edgeVec2 Q q R e₁).prodMk (measurable_edgeVec2 Q q R e₂))
  have hAm : MeasurableSet A :=
    ((measurableSet_lt (hm_dot e₁) measurable_const).inter
      ((measurableSet_lt measurable_const (hm_dot e₂)).inter
        (measurableSet_lt measurable_const hm_det))).union
    ((measurableSet_lt (hm_dot e₂) measurable_const).inter
      ((measurableSet_lt measurable_const (hm_dot e₁)).inter
        (measurableSet_lt hm_det measurable_const)))
  have hmp_neg : MeasurePreserving (fun ω : W → BlockSample => fun B => negSample (ω B)) P P :=
    measurePreserving_pi _ _ fun _ => measurePreserving_negSample
  have hAneg_eq : P.real Aneg = P.real A :=
    hmp_neg.measureReal_preimage hAm.nullMeasurableSet
  have hAneg_m : MeasurableSet Aneg := hAm.preimage hmp_neg.measurable
  have hdisj : Disjoint A Aneg := by
    refine disjoint_left.mpr fun ω h1 h2 => ?_
    simp only [A, Aneg, mem_preimage, mem_ofPred_eq, edgeVec2_negSample] at h1 h2
    exact rayCross_disjoint_neg2 c _ _ ⟨h1, h2⟩
  let proj_n (ω : W → BlockSample) : W → ℝ := fun B => dot2 (normVec c) (ω B).1
  have hmp_n : MeasurePreserving proj_n P (Measure.pi fun _ : W => gaussianReal 0 1) :=
    measurePreserving_pi _ _ fun _ =>
      (measurePreserving_dot2_unit (normVec_sq c)).comp
        (MeasureTheory.measurePreserving_fst (μ := gauss2) (ν := gaussTie))
  set U := {g : W → ℝ | (0 : ℝ) ∈ Ι (edgeScore Q q R g e₁) (edgeScore Q q R g e₂)}
  have hUm : MeasurableSet U :=
    measurableSet_setOf_mem_uIoc (measurable_edgeScore q R e₁) (measurable_edgeScore q R e₂) 0
  have hsub : A ∪ Aneg ⊆ proj_n ⁻¹' U := by
    intro ω hω
    simp only [mem_union, A, Aneg, mem_preimage, mem_ofPred_eq, edgeVec2_negSample] at hω
    simp only [mem_preimage, U, mem_ofPred_eq, proj_n, ← dot2_edgeVec2]
    exact rayCross_or_neg2_imp_mem_uIoc c _ _ hω
  have hunit1 : ‖edgeVector Q q R e₁‖ = 1 := norm_edgeVector hloop hdeg hq hρ₀ hρ e₁
  have hunit2 : ‖edgeVector Q q R e₂‖ = 1 := norm_edgeVector hloop hdeg hq hρ₀ hρ e₂
  have h2A : 2 * P.real A ≤ arccos ⟪edgeVector Q q R e₁, edgeVector Q q R e₂⟫ / π := by
    calc 2 * P.real A = P.real A + P.real Aneg := by rw [hAneg_eq]; ring
      _ = P.real (A ∪ Aneg) := (measureReal_union hdisj hAneg_m).symm
      _ ≤ P.real (proj_n ⁻¹' U) :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ = (Measure.pi fun _ : W => gaussianReal 0 1).real U :=
          hmp_n.measureReal_preimage hUm.nullMeasurableSet
      _ ≤ arccos ⟪edgeVector Q q R e₁, edgeVector Q q R e₂⟫ / π := by
          rw [← InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hunit1 hunit2]
          exact measureReal_mem_uIoc_le (hunit1.trans hunit2.symm) 0
  have hpi : 0 < π := pi_pos
  rw [le_div_iff₀ (by positivity)]
  have hmul := (le_div_iff₀ hpi).mp h2A
  linarith only [hmul]

/-- **Expected `badCount` at a degree-`3` block.** At any block `B` with
`(Q.incidenceSet B).ncard = 3`, `E[badCount Q q R · B] ≤ capAt ρ₀`. -/
private theorem integral_badCount_le_capAt {Q : Multigraph W F} (hloop : Q.Loopless)
    (hdeg : Q.MaxDegreeLE 3) {q : ℝ} (hq : 0 ≤ q) {R : ℕ} {ρ₀ : ℝ}
    (hρ₀ : 0 ≤ ρ₀) (hρ_lt : ρ₀ < 1)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {B : W} (h3 : (Q.incidenceSet B).ncard = 3) :
    ∫ ω, (badCount Q q R ω B : ℝ) ∂(Measure.pi fun _ : W => blockMeasure) ≤ capAt ρ₀ := by
  classical
  have := Fintype.ofFinite F
  set P := Measure.pi fun _ : W => blockMeasure
  obtain ⟨e₀, e₁, e₂, h01, h02, h12, hinc_set⟩ := ncard_eq_three.mp h3
  set s : Finset F := {e₀, e₁, e₂}
  have hs_inc : (s : Set F) = Q.incidenceSet B := by simp [s, hinc_set]
  have hs_toFin : s = (Q.incidenceSet B).toFinset := by
    ext e; simp [← hs_inc]
  have hs_card : s.card = 3 := by
    dsimp [s]
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]), Finset.card_pair h12]
  have hoff_card : (s.offDiag.card : ℝ) = 6 := by
    rw [Finset.offDiag_card, hs_card]; norm_num
  have hunit (e : F) : ‖edgeVector Q q R e‖ = 1 :=
    norm_edgeVector hloop hdeg hq (by linarith) hρ e
  have hcap_vec (e : F) (he : e ∈ s) :
      √((1 + ρ₀) / 2) ≤ ⟪edgeVector Q q R e, unitKernelRow Q.toSimpleGraph q R B⟫ :=
    le_inner_edgeVector hloop hdeg hq hρ₀ hρ (by rw [← hs_inc]; exact he)
  have hpair_mem (p : F × F) (hp : p ∈ s.offDiag) :
      ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ ∈ Icc 0 1 := by
    obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hp
    refine ⟨?_, (real_inner_le_norm _ _).trans_eq (by rw [hunit, hunit, one_mul])⟩
    have := InnerProductGeometry.two_mul_sq_sub_one_le_inner (norm_unitKernelRow q R B)
      (hunit p.1) (hunit p.2) (sqrt_nonneg _) (hcap_vec _ h1) (hcap_vec _ h2)
    rw [sq_sqrt (by linarith)] at this
    linarith
  let proj2 (ω : W → BlockSample) : (W → ℝ) × (W → ℝ) :=
    (fun B' => (ω B').1.1, fun B' => (ω B').1.2)
  have hmp_proj2 : MeasurePreserving proj2 P
      ((Measure.pi fun _ : W => gaussianReal 0 1).prod
        (Measure.pi fun _ : W => gaussianReal 0 1)) := by
    have h1 : MeasurePreserving (fun ω B' => (ω B').1) P (Measure.pi fun _ : W => gauss2) :=
      measurePreserving_pi _ _ fun _ =>
        MeasureTheory.measurePreserving_fst (μ := gauss2) (ν := gaussTie)
    have h2 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ W
      (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
    exact h2.comp h1
  set NullTie : Set (W → BlockSample) := {ω | ¬Function.Injective (ω B).2}
  set NullRay : Set (W → BlockSample) :=
    ⋃ e ∈ s, ⋃ c : Fin 3, {ω | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0}
  set NullDet : Set (W → BlockSample) :=
    ⋃ p ∈ s.offDiag.filter (fun p => edgeVector Q q R p.1 ≠ edgeVector Q q R p.2),
      {ω | det2 (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) = 0}
  set NullB := NullTie ∪ (NullRay ∪ NullDet)
  have hNullRay_zero : P.real NullRay = 0 := by
    have hterm (e : F) (c : Fin 3) :
        P.real {ω | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0} = 0 := by
      let proj_n (ω : W → BlockSample) : W → ℝ := fun B' => dot2 (normVec c) (ω B').1
      have hmp_n : MeasurePreserving proj_n P (Measure.pi fun _ : W => gaussianReal 0 1) :=
        measurePreserving_pi _ _ fun _ =>
          (measurePreserving_dot2_unit (normVec_sq c)).comp
            (MeasureTheory.measurePreserving_fst (μ := gauss2) (ν := gaussTie))
      have hpre : {ω | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0} =
          proj_n ⁻¹' {g : W → ℝ | ⟪edgeVector Q q R e, WithLp.toLp 2 g⟫ = 0} := by
        ext ω; simp [proj_n, dot2_edgeVec2, edgeScore]
      have hm : MeasurableSet {g : W → ℝ | ⟪edgeVector Q q R e, WithLp.toLp 2 g⟫ = 0} :=
        (isClosed_eq (by fun_prop) continuous_const).measurableSet
      rw [hpre, hmp_n.measureReal_preimage hm.nullMeasurableSet]
      exact measureReal_pi_gaussianReal_inner_eq_zero (hunit e)
    have h1 : P NullRay = 0 := by
      refine (measure_biUnion_null_iff s.countable_toSet).mpr fun e _ =>
        measure_iUnion_null fun c => ?_
      have hz := hterm e c
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hz
      exact hz.resolve_right (measure_ne_top _ _)
    rw [measureReal_def, h1, ENNReal.toReal_zero]
  have hNullDet_zero : P.real NullDet = 0 := by
    have h1 : P NullDet = 0 := by
      refine (measure_biUnion_null_iff (Finset.countable_toSet _)).mpr fun p hp => ?_
      obtain ⟨hp_off, hne_vec⟩ := Finset.mem_filter.mp hp
      have hρ_pair : -1 < ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ := by
        linarith [(hpair_mem p hp_off).1]
      set Sd : Set ((W → ℝ) × (W → ℝ)) :=
        {g | det2 (⟪edgeVector Q q R p.1, WithLp.toLp 2 g.1⟫,
                    ⟪edgeVector Q q R p.1, WithLp.toLp 2 g.2⟫)
                  (⟪edgeVector Q q R p.2, WithLp.toLp 2 g.1⟫,
                    ⟪edgeVector Q q R p.2, WithLp.toLp 2 g.2⟫) = 0}
      have hSm : MeasurableSet Sd :=
        (isClosed_eq (by unfold det2; fun_prop) continuous_const).measurableSet
      have hpre : {ω | det2 (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) = 0} =
          proj2 ⁻¹' Sd := rfl
      have hz : P.real {ω | det2 (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) = 0} = 0 := by
        rw [hpre, hmp_proj2.measureReal_preimage hSm.nullMeasurableSet]
        exact measureReal_pi_prod_det2_eq_zero (hunit p.1) (hunit p.2) hρ_pair hne_vec
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hz
      exact hz.resolve_right (measure_ne_top _ _)
    rw [measureReal_def, h1, ENNReal.toReal_zero]
  have hNullB_null : P NullB = 0 := by
    have hle : P.real NullB ≤ P.real NullTie + (P.real NullRay + P.real NullDet) :=
      (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
    rw [measureReal_not_injective_tie_zero B, hNullRay_zero, hNullDet_zero] at hle
    have hz : P.real NullB = 0 := le_antisymm (by linarith only [hle]) measureReal_nonneg
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hz
    exact hz.resolve_right (measure_ne_top _ _)
  let RC (p : F × F) (c : Fin 3) : Set (W → BlockSample) :=
    {ω | rayCross c (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2)}
  set Conv : Set (W → BlockSample) :=
    {ω | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
      w₀ * (edgeVec2 Q q R ω e₀).1 + w₁ * (edgeVec2 Q q R ω e₁).1 +
        w₂ * (edgeVec2 Q q R ω e₂).1 = 0 ∧
      w₀ * (edgeVec2 Q q R ω e₀).2 + w₁ * (edgeVec2 Q q R ω e₁).2 +
        w₂ * (edgeVec2 Q q R ω e₂).2 = 0}
  have hRC_m (p : F × F) (c : Fin 3) : MeasurableSet (RC p c) := by
    have hm_dot (e : F) : Measurable fun ω : W → BlockSample =>
        dot2 (normVec c) (edgeVec2 Q q R ω e) :=
      (by unfold dot2; fun_prop : Measurable (dot2 (normVec c))).comp (measurable_edgeVec2 Q q R e)
    have hm_det : Measurable fun ω : W → BlockSample =>
        det2 (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) :=
      (by unfold det2; fun_prop : Measurable fun q2 : (ℝ × ℝ) × (ℝ × ℝ) => det2 q2.1 q2.2).comp
        ((measurable_edgeVec2 Q q R p.1).prodMk (measurable_edgeVec2 Q q R p.2))
    exact ((measurableSet_lt (hm_dot p.1) measurable_const).inter
        ((measurableSet_lt measurable_const (hm_dot p.2)).inter
          (measurableSet_lt measurable_const hm_det))).union
      ((measurableSet_lt (hm_dot p.2) measurable_const).inter
        ((measurableSet_lt measurable_const (hm_dot p.1)).inter
          (measurableSet_lt hm_det measurable_const)))
  have hConv_m : MeasurableSet Conv :=
    measurableSet_convex_zero_three
      (f₀ := fun ω => edgeVec2 Q q R ω e₀)
      (f₁ := fun ω => edgeVec2 Q q R ω e₁)
      (f₂ := fun ω => edgeVec2 Q q R ω e₂)
      (by unfold edgeVec2 edgeScore; fun_prop)
      (by unfold edgeVec2 edgeScore; fun_prop)
      (by unfold edgeVec2 edgeScore; fun_prop)
  have hint_bad : Integrable (fun ω => (badCount Q q R ω B : ℝ)) P :=
    integrable_badCount hdeg q R B
  have hint1 {S : Set (W → BlockSample)} (hSm : MeasurableSet S) :
      Integrable (S.indicator (1 : (W → BlockSample) → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hSm
  let rhsFn (ω : W → BlockSample) : ℝ :=
    (∑ p ∈ s.offDiag, ∑ c : Fin 3, (RC p c).indicator (1 : (W → BlockSample) → ℝ) ω) +
      2 * Conv.indicator (1 : (W → BlockSample) → ℝ) ω
  have hint_rhs : Integrable rhsFn P :=
    (integrable_finsetSum _ fun p _ =>
      integrable_finsetSum _ fun c _ => hint1 (hRC_m p c)).add
      ((hint1 hConv_m).const_mul 2)
  have hae_le : (fun ω => 4 * (badCount Q q R ω B : ℝ)) ≤ᵐ[P] rhsFn := by
    filter_upwards [compl_mem_ae_iff.mpr hNullB_null] with ω hω
    simp only [NullB, NullTie, NullRay, NullDet, mem_compl_iff, mem_union, mem_iUnion,
      mem_ofPred_eq, not_or, not_exists, not_not] at hω
    obtain ⟨hinj, hray_ω, hdet_ω⟩ := hω
    have hdet_sec : ∀ a ∈ s, ∀ b ∈ s, ∀ c₁ c₂ : Fin 3,
        inOpenSector c₁ (edgeVec2 Q q R ω a) → inOpenSector c₂ (edgeVec2 Q q R ω b) →
        c₁ ≠ c₂ → det2 (edgeVec2 Q q R ω a) (edgeVec2 Q q R ω b) ≠ 0 := by
      intro a ha b hb c₁ c₂ hc₁ hc₂ hne_c
      have hab : a ≠ b := fun h => by
        subst h; exact hne_c (inOpenSector_unique hc₁ hc₂)
      have hvec_ne : edgeVector Q q R a ≠ edgeVector Q q R b := fun heq => by
        have hz_eq : edgeVec2 Q q R ω a = edgeVec2 Q q R ω b := by
          dsimp [edgeVec2, edgeScore]; rw [heq]
        rw [hz_eq] at hc₁
        exact hne_c (inOpenSector_unique hc₁ hc₂)
      exact hdet_ω (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, hvec_ne⟩)
    have hnat := four_mul_badCount_le h01 h12 h02 hs_toFin hinj hray_ω hdet_sec
    have hreal : (4 : ℝ) * (badCount Q q R ω B : ℝ) ≤
        ((∑ p ∈ s.offDiag, ∑ c : Fin 3,
          if rayCross c (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) then 1 else 0) +
        2 * (if ω ∈ Conv then 1 else 0) : ℕ) := by
      exact_mod_cast hnat
    refine hreal.trans_eq ?_
    dsimp only [rhsFn]
    rw [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun p _ => ?_) (congrArg (2 * ·) ?_)
    · rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases h : ω ∈ RC p c
      · have hr : rayCross c (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) := h
        simp [h, hr]
      · have hr : ¬rayCross c (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) := h
        simp [h, hr]
    · by_cases h : ω ∈ Conv <;> simp [h]
  have hint_ineq : 4 * ∫ ω, (badCount Q q R ω B : ℝ) ∂P ≤ ∫ ω, rhsFn ω ∂P := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hint_bad.const_mul 4) hint_rhs hae_le
  have hint_rhs_eq : ∫ ω, rhsFn ω ∂P =
      (∑ p ∈ s.offDiag, ∑ c : Fin 3, P.real (RC p c)) + 2 * P.real Conv := by
    dsimp [rhsFn]
    rw [integral_add
      (integrable_finsetSum _ fun p _ =>
        integrable_finsetSum _ fun c _ => hint1 (hRC_m p c))
      ((hint1 hConv_m).const_mul 2),
      integral_const_mul, integral_indicator_one hConv_m,
      integral_finsetSum _ fun p _ =>
        integrable_finsetSum _ fun c _ => hint1 (hRC_m p c)]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum _ fun c _ => hint1 (hRC_m p c)]
    exact Finset.sum_congr rfl fun c _ => integral_indicator_one (hRC_m p c)
  have hpart1 : (∑ p ∈ s.offDiag, ∑ c : Fin 3, P.real (RC p c)) ≤ 6 * straddleBound ρ₀ := by
    have hinner_sum : 6 * ((1 + 3 * ρ₀) / 4) ≤
        ∑ p ∈ s.offDiag, ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ := by
      have h := InnerProductGeometry.le_sum_offDiag_inner (norm_unitKernelRow q R B)
        (s := s) (y := edgeVector Q q R) (fun e _ => hunit e) (sqrt_nonneg _) hcap_vec
      rw [hs_card, sq_sqrt (by linarith)] at h
      linarith
    have hjensen := Real.sum_arccos_le_card_mul_arccos s.offDiag hpair_mem
      (by rw [hoff_card]; exact hinner_sum)
    rw [hoff_card] at hjensen
    have hp_bound (p : F × F) :
        (∑ c : Fin 3, P.real (RC p c)) ≤
          3 / (2 * π) * arccos ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ := by
      calc (∑ c : Fin 3, P.real (RC p c))
          ≤ ∑ _c : Fin 3, arccos ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ / (2 * π) :=
            Finset.sum_le_sum fun c _ =>
              measureReal_rayCross_le hloop hdeg hq (by linarith) hρ c p.1 p.2
        _ = 3 / (2 * π) * arccos ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc (∑ p ∈ s.offDiag, ∑ c : Fin 3, P.real (RC p c))
        ≤ ∑ p ∈ s.offDiag, 3 / (2 * π) * arccos ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ :=
          Finset.sum_le_sum fun p _ => hp_bound p
      _ = 3 / (2 * π) * ∑ p ∈ s.offDiag, arccos ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ 3 / (2 * π) * (6 * arccos ((1 + 3 * ρ₀) / 4)) := by gcongr
      _ = 6 * straddleBound ρ₀ := by unfold straddleBound; ring
  have hpart2 : P.real Conv ≤ 1 - √((1 + ρ₀) / 2) := by
    set Sconv : Set ((W → ℝ) × (W → ℝ)) :=
      {g | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
        w₀ * ⟪edgeVector Q q R e₀, WithLp.toLp 2 g.1⟫ +
          w₁ * ⟪edgeVector Q q R e₁, WithLp.toLp 2 g.1⟫ +
          w₂ * ⟪edgeVector Q q R e₂, WithLp.toLp 2 g.1⟫ = 0 ∧
        w₀ * ⟪edgeVector Q q R e₀, WithLp.toLp 2 g.2⟫ +
          w₁ * ⟪edgeVector Q q R e₁, WithLp.toLp 2 g.2⟫ +
          w₂ * ⟪edgeVector Q q R e₂, WithLp.toLp 2 g.2⟫ = 0}
    have hSconv_m : MeasurableSet Sconv :=
      measurableSet_convex_zero_three
        (f₀ := fun g : (W → ℝ) × (W → ℝ) =>
          (⟪edgeVector Q q R e₀, WithLp.toLp 2 g.1⟫, ⟪edgeVector Q q R e₀, WithLp.toLp 2 g.2⟫))
        (f₁ := fun g : (W → ℝ) × (W → ℝ) =>
          (⟪edgeVector Q q R e₁, WithLp.toLp 2 g.1⟫, ⟪edgeVector Q q R e₁, WithLp.toLp 2 g.2⟫))
        (f₂ := fun g : (W → ℝ) × (W → ℝ) =>
          (⟪edgeVector Q q R e₂, WithLp.toLp 2 g.1⟫, ⟪edgeVector Q q R e₂, WithLp.toLp 2 g.2⟫))
        (by fun_prop) (by fun_prop) (by fun_prop)
    have hpre : Conv = proj2 ⁻¹' Sconv := rfl
    rw [hpre, hmp_proj2.measureReal_preimage hSconv_m.nullMeasurableSet]
    exact measureReal_pi_prod_convex_zero_le (norm_unitKernelRow q R B)
      (sqrt_pos.mpr (by linarith)) (sqrt_le_one.mpr (by linarith))
      (hcap_vec e₀ (by simp [s])) (hcap_vec e₁ (by simp [s])) (hcap_vec e₂ (by simp [s]))
      (hunit e₀).le (hunit e₁).le (hunit e₂).le
  rw [hint_rhs_eq] at hint_ineq
  unfold capAt
  linarith only [hint_ineq, hpart1, hpart2]

open Classical in
/-- Every bichromatic edge contributes at least `1` mismatched endpoint half-edge (`badCount`). -/
private theorem sum_cutAny_le_sum_badCount [Fintype F] {Q : Multigraph W F}
    (hloop : Q.Loopless) (q : ℝ) (R : ℕ) {ω : W → BlockSample}
    (_hray : ∀ e : F, ∀ c : Fin 3, dot2 (normVec c) (edgeVec2 Q q R ω e) ≠ 0) :
    (Finset.univ.filter fun e : F => ω ∈ cutAnyEvent Q q R e).card ≤
      ∑ B : W, badCount Q q R ω B := by
  have h1 : (Finset.univ.filter fun e : F => ω ∈ cutAnyEvent Q q R e).card ≤
      ∑ e : F, ((if ¬inOpenSector (blockColor Q q R ω (Q.src e)) (edgeVec2 Q q R ω e)
          then 1 else 0) +
        (if ¬inOpenSector (blockColor Q q R ω (Q.tgt e)) (edgeVec2 Q q R ω e)
          then 1 else 0)) := by
    rw [Finset.card_filter]
    refine Finset.sum_le_sum fun e _ => ?_
    by_cases hcut : ω ∈ cutAnyEvent Q q R e
    · simp only [hcut, ↓reduceIte]
      by_contra! h0
      have hs : inOpenSector (blockColor Q q R ω (Q.src e)) (edgeVec2 Q q R ω e) := by
        by_contra h; simp only [h, not_false_eq_true, ↓reduceIte] at h0; omega
      have ht : inOpenSector (blockColor Q q R ω (Q.tgt e)) (edgeVec2 Q q R ω e) := by
        by_contra h; simp only [h, not_false_eq_true, ↓reduceIte] at h0; omega
      exact hcut (inOpenSector_unique hs ht)
    · simp only [hcut, ↓reduceIte]; omega
  refine h1.trans ?_
  have hbad_sum : (∑ B : W, badCount Q q R ω B) =
      ∑ B : W, ∑ e : F,
        if (Q.src e = B ∨ Q.tgt e = B) ∧
            ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e) then 1 else 0 := by
    refine Finset.sum_congr rfl fun B _ => ?_
    unfold badCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _, ← Finset.card_filter]
    congr 1; ext e; simp [Multigraph.mem_incidenceSet]
  rw [hbad_sum, Finset.sum_comm]
  refine Finset.sum_le_sum fun e _ => ?_
  have hsub : ({Q.src e, Q.tgt e} : Finset W) ⊆ Finset.univ := Finset.subset_univ _
  calc ((if ¬inOpenSector (blockColor Q q R ω (Q.src e)) (edgeVec2 Q q R ω e) then 1 else 0) +
        (if ¬inOpenSector (blockColor Q q R ω (Q.tgt e)) (edgeVec2 Q q R ω e) then 1 else 0))
      = ∑ B ∈ ({Q.src e, Q.tgt e} : Finset W),
          if (Q.src e = B ∨ Q.tgt e = B) ∧
            ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e) then 1 else 0 := by
        rw [Finset.sum_pair (hloop e)]
        simp
    _ ≤ ∑ B : W,
          if (Q.src e = B ∨ Q.tgt e = B) ∧
            ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e) then 1 else 0 :=
        Finset.sum_le_sum_of_subset hsub

end QuotientColoring

/-! ### Parameter selection and the global balanced `3`-way cut theorem -/

private theorem exists_threeWay_params {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ₀ η : ℝ) (M : ℕ),
      0 ≤ q ∧ 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧
      ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧
      0 < η ∧ 2 ≤ M ∧
      capAt ρ₀ ≤ threeWayCapCoefficient + ξ / 4 ∧
      16 / (M : ℝ) + η ≤ ξ / 4 := by
  set g : ℝ := 2 * √2 / 3 with hg
  have hsqrt_lo : (7 : ℝ) / 5 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hsqrt_hi : √2 < (3 : ℝ) / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hcont_cap : Continuous fun ρ : ℝ => capAt ρ := by
    unfold capAt straddleBound
    fun_prop
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hcont_cap.continuousAt (x := g))
    (ξ / 4) (by positivity)
  set ρ₀ := g - min δ (1 / 4) / 2
  have hmin : 0 < min δ (1 / 4) := lt_min hδ (by norm_num)
  have hρ₀_lt_g : ρ₀ < g := by dsimp [ρ₀]; linarith
  have hρ₀_nonneg : 0 ≤ ρ₀ := by
    dsimp [ρ₀, g]; linarith [min_le_right δ (1 / 4)]
  have hρ₀_lt_one : ρ₀ < 1 := by
    dsimp [ρ₀, g]; linarith
  have hcap_le : capAt ρ₀ ≤ threeWayCapCoefficient + ξ / 4 := by
    have hdist : dist ρ₀ g < δ := by
      rw [Real.dist_eq, show ρ₀ - g = -(min δ (1 / 4) / 2) by dsimp [ρ₀]; ring, abs_neg,
        abs_of_pos (by positivity)]
      linarith [min_le_left δ (1 / 4)]
    have hd := hclose hdist
    rw [Real.dist_eq, capAt_limit] at hd
    linarith [le_abs_self (capAt ρ₀ - threeWayCapCoefficient), hd]
  have hv3 : vertexCorrelation 3 = g := by norm_num [vertexCorrelation, g]
  obtain ⟨q, R, hq, hρ_raw⟩ := exists_decay_radius_degree (by norm_num : 2 ≤ 3)
    (ρ := ρ₀) (by rw [hv3]; exact hρ₀_lt_g)
  have hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R := by
    norm_num at hρ_raw; exact hρ_raw
  set η := ξ / 8
  have hη : 0 < η := by positivity
  set M : ℕ := ⌈128 / ξ⌉₊ + 2
  have hM2 : 2 ≤ M := by dsimp [M]; omega
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM_ge : 128 / ξ ≤ (M : ℝ) := by
    dsimp [M]; push_cast; linarith [Nat.le_ceil (128 / ξ)]
  have h16M : 16 / (M : ℝ) ≤ ξ / 8 := by
    rw [div_le_iff₀ hM_pos]
    have hmul := mul_le_mul_of_nonneg_left hM_ge hξ.le
    rw [mul_div_cancel₀ _ hξ.ne'] at hmul
    linarith only [hmul]
  exact ⟨q, R, ρ₀, η, M, hq, hρ₀_nonneg, hρ₀_lt_one, hρ, hη, hM2, hcap_le,
    by dsimp [η]; linarith only [h16M]⟩

/-- **Balanced `3`-way cut of a connected loopless subcubic multigraph.** For every `ξ > 0` there is
a constant `C₀ : ℕ` such that every finite connected loopless multigraph `G` of maximum degree at
most `3` and every subset `A ⊆ V` admit a vertex `3`-coloring `col : V → Fin 3` balancing `A` up to
`ξ |V| + C₀` on all three parts while keeping all three pairwise edge cuts at most
`(2 / 3) · threeWayCapCoefficient · β₁(G) + ξ |V| + C₀`. -/
theorem exists_balanced_threeWayCut {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ C₀ : ℕ, ∀ {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E),
      G.Loopless → G.toSimpleGraph.Connected → G.MaxDegreeLE 3 →
      ∀ A : Set V, ∃ col : V → Fin 3,
        (∀ c : Fin 3,
          |((A ∩ {v | col v = c}).ncard : ℝ) - 1 / 3 * (A.ncard : ℝ)| ≤
            ξ * Nat.card V + C₀) ∧
        (∀ c : Fin 3,
          ((G.edgeCut {v | col v = c} ∩ G.edgeCut {v | col v = c + 1}).ncard : ℝ) ≤
            2 / 3 * threeWayCapCoefficient * (G.cycleRank : ℝ) + ξ * Nat.card V + C₀) := by
  obtain ⟨q, R, ρ₀, η, M, hq, hρ₀, hρ_lt, hρ, hη, hM2, hcap_le, hslack⟩ :=
    exists_threeWay_params hξ
  set D_blk := vertexOverlap 3 R
  set D_edg := vertexOverlap 3 (R + 1)
  set C₀ : ℕ := max M (⌈12 * ((M : ℝ) ^ 2 * ((D_blk : ℝ) + D_edg)) / η ^ 2⌉₊ + 1)
  refine ⟨C₀, fun {V E} _ _ G hloop hconn hdeg A => ?_⟩
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  by_cases hsmall : Nat.card V ≤ C₀
  · -- Small-graph regime `|V| ≤ C₀`: the constant coloring `fun _ => 0` has `0` cut edges!
    refine ⟨fun _ => 0, fun c => ?_, fun c => ?_⟩
    · have hA_le : (A.ncard : ℝ) ≤ (C₀ : ℝ) :=
        Nat.cast_le.mpr ((ncard_le_card A).trans hsmall)
      have hA_nonneg : (0 : ℝ) ≤ A.ncard := Nat.cast_nonneg _
      have hv_nonneg : (0 : ℝ) ≤ ξ * Nat.card V := by positivity
      rcases c with ⟨_ | _ | _ | _, hlt⟩
      · change |((A ∩ {v : V | (0 : Fin 3) = 0}).ncard : ℝ) - 1 / 3 * (A.ncard : ℝ)| ≤ _
        have heq : A ∩ {v : V | (0 : Fin 3) = 0} = A := by simp
        rw [heq]
        have habs : |(A.ncard : ℝ) - 1 / 3 * (A.ncard : ℝ)| = 2 / 3 * (A.ncard : ℝ) := by
          rw [show (A.ncard : ℝ) - 1 / 3 * (A.ncard : ℝ) = 2 / 3 * (A.ncard : ℝ) by ring,
            abs_of_nonneg (by positivity)]
        rw [habs]
        linarith only [hA_le, hA_nonneg, hv_nonneg]
      · change |((A ∩ {v : V | (0 : Fin 3) = 1}).ncard : ℝ) - 1 / 3 * (A.ncard : ℝ)| ≤ _
        have heq : A ∩ {v : V | (0 : Fin 3) = 1} = ∅ := by ext; simp
        rw [heq, ncard_empty, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
        linarith only [hA_le, hA_nonneg, hv_nonneg]
      · change |((A ∩ {v : V | (0 : Fin 3) = 2}).ncard : ℝ) - 1 / 3 * (A.ncard : ℝ)| ≤ _
        have heq : A ∩ {v : V | (0 : Fin 3) = 2} = ∅ := by ext; simp
        rw [heq, ncard_empty, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
        linarith only [hA_le, hA_nonneg, hv_nonneg]
      · omega
    · have hempty : G.edgeCut {v : V | (0 : Fin 3) = c} ∩
          G.edgeCut {v : V | (0 : Fin 3) = c + 1} = ∅ := by
        rcases c with ⟨_ | _ | _ | _, hlt⟩
        · ext e
          change e ∈ G.edgeCut {v | (0 : Fin 3) = 0} ∩ G.edgeCut {v | (0 : Fin 3) = 1} ↔ _
          simp
        · ext e
          change e ∈ G.edgeCut {v | (0 : Fin 3) = 1} ∩ G.edgeCut {v | (0 : Fin 3) = 2} ↔ _
          simp
        · ext e
          change e ∈ G.edgeCut {v | (0 : Fin 3) = 2} ∩ G.edgeCut {v | (0 : Fin 3) = 0} ↔ _
          simp
        · omega
      rw [hempty, ncard_empty, Nat.cast_zero]
      have hpos_cap := threeWayCapCoefficient_pos
      positivity
  · -- Large-graph regime `C₀ < |V|`: compress with unit vertex weight and run `Z₃` Gaussian cut.
    push Not at hsmall
    have hM_lt_V : M < Nat.card V := (le_max_left _ _).trans_lt hsmall
    obtain ⟨cmp, hsat⟩ := CappedCompression.exists_saturated (G := G) (w := fun _ => 1)
      (d := 3) (M := M) hdeg fun _ => by omega
    set Q := cmp.quotient
    have hQ_loop : Q.Loopless := cmp.quotient_loopless
    have hQ_deg : Q.MaxDegreeLE 3 := cmp.quotient_maxDegreeLE
    -- Since every block has size `≤ M < |V|`, there are at least two blocks.
    have htwo : 1 < Nat.card cmp.blocks := by
      by_contra! hle1
      have hsum := cmp.sum_blockWeight_univ
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
        ← Nat.card_eq_fintype_card] at hsum
      have hleM : ∑ B : cmp.blocks, cmp.blockWeight B ≤ Nat.card cmp.blocks * M := by
        calc ∑ B : cmp.blocks, cmp.blockWeight B ≤ ∑ _B : cmp.blocks, M :=
              Finset.sum_le_sum fun B _ => cmp.blockWeight_le B
          _ = Nat.card cmp.blocks * M := by
              simp [Nat.card_eq_fintype_card]
      have hV_le : Nat.card V ≤ M := by
        rw [← hsum]
        exact hleM.trans (by nlinarith only [hle1])
      omega
    -- Block counts: `#cmp.blocks ≤ |V|`, `#cmp.external ≤ 2 |V|`, `#Q_{1,2} ≤ 8 |V| / M`,
    -- `#Q₃ ≤ 2 β₁ + #Q₁`.
    have hblocks_le_V : cmp.blocks.card ≤ Nat.card V := cmp.card_blocks_le
    have hext_le : 2 * Nat.card cmp.external ≤ 3 * Nat.card V := by
      have hhand := Q.sum_ncard_incidenceSet hQ_loop
      have hdeg_sum : ∑ B : cmp.blocks, (Q.incidenceSet B).ncard ≤ 3 * cmp.blocks.card := by
        calc ∑ B : cmp.blocks, (Q.incidenceSet B).ncard ≤ ∑ _B : cmp.blocks, 3 :=
              Finset.sum_le_sum fun B _ => hQ_deg B
          _ = 3 * cmp.blocks.card := by simp [Nat.mul_comm]
      omega
    have hG_edges_le : 2 * Nat.card E ≤ 3 * Nat.card V := by
      have hhand := G.sum_ncard_incidenceSet hloop
      have hdeg_sum : ∑ v : V, (G.incidenceSet v).ncard ≤ 3 * Nat.card V := by
        calc ∑ v : V, (G.incidenceSet v).ncard ≤ ∑ _v : V, 3 :=
              Finset.sum_le_sum fun v _ => hdeg v
          _ = 3 * Nat.card V := by simp [Nat.mul_comm, Nat.card_eq_fintype_card]
      omega
    have hbeta_le_V : G.cycleRank ≤ Nat.card V := by
      have hconnE := G.card_le_card_add_one_of_connected hconn
      unfold Multigraph.cycleRank
      omega
    set Q12 := Finset.univ.filter fun B : cmp.blocks =>
      1 ≤ (Q.incidenceSet B).ncard ∧ (Q.incidenceSet B).ncard ≤ 2
    set Q1 := Finset.univ.filter fun B : cmp.blocks => (Q.incidenceSet B).ncard = 1
    set Q3 := Finset.univ.filter fun B : cmp.blocks => (Q.incidenceSet B).ncard = 3
    have hQ12_real : (Q12.card : ℝ) ≤ 8 * (Nat.card V : ℝ) / (M : ℝ) := by
      have : M * Q12.card ≤ 8 * Nat.card V := by
        simpa [Q12, Nat.card_eq_fintype_card] using hsat.mul_card_deg_one_two_le
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast (by linarith : Q12.card * M ≤ 8 * Nat.card V)
    have hQ1_sub : Q1 ⊆ Q12 := fun B hB => by
      have h1 := (Finset.mem_filter.mp hB).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ B, by omega, by omega⟩
    have hQ1_le_Q12 : Q1.card ≤ Q12.card := Finset.card_le_card hQ1_sub
    have hQ3_le : Q3.card ≤ 2 * G.cycleRank + Q1.card :=
      cmp.card_deg_three_le_of_connected hloop hconn htwo
    -- Expected pairwise cut bound on `Q`:
    set P := Measure.pi fun _ : cmp.blocks => blockMeasure
    have hexp_cutAny :
        (∑ e : cmp.external, P.real (cutAnyEvent Q q R e)) ≤
          capAt ρ₀ * (Q3.card : ℝ) + 2 * (Q12.card : ℝ) := by
      -- Outside `NullAllRay`, `#{e | cutAnyEvent} ≤ ∑ B, badCount B`.
      set NullAllRay : Set (cmp.blocks → BlockSample) :=
        ⋃ e : cmp.external, ⋃ c : Fin 3, {ω | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0}
      have hNullAllRay_null : P NullAllRay = 0 := by
        refine measure_iUnion_null fun e => measure_iUnion_null fun c => ?_
        let proj_n (ω : cmp.blocks → BlockSample) : cmp.blocks → ℝ :=
          fun B' => dot2 (normVec c) (ω B').1
        have hmp_n : MeasurePreserving proj_n P
            (Measure.pi fun _ : cmp.blocks => gaussianReal 0 1) :=
          measurePreserving_pi _ _ fun _ =>
            (measurePreserving_dot2_unit (normVec_sq c)).comp
              (MeasureTheory.measurePreserving_fst (μ := gauss2) (ν := gaussTie))
        have hpre : {ω | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0} =
            proj_n ⁻¹' {g : cmp.blocks → ℝ | ⟪edgeVector Q q R e, WithLp.toLp 2 g⟫ = 0} := by
          ext ω; simp [proj_n, dot2_edgeVec2, edgeScore]
        have hm : MeasurableSet {g : cmp.blocks → ℝ |
            ⟪edgeVector Q q R e, WithLp.toLp 2 g⟫ = 0} :=
          (isClosed_eq (by fun_prop) continuous_const).measurableSet
        have hz : P.real {ω | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0} = 0 := by
          rw [hpre, hmp_n.measureReal_preimage hm.nullMeasurableSet]
          exact measureReal_pi_gaussianReal_inner_eq_zero
            (norm_edgeVector hQ_loop hQ_deg hq (by linarith) hρ e)
        rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hz
        exact hz.resolve_right (measure_ne_top _ _)
      have hcutAny_m (e : cmp.external) : MeasurableSet (cutAnyEvent Q q R e) := by
        have hunion : cutAnyEvent Q q R e =
            (cutPairEvent Q q R 0 e ∪ cutPairEvent Q q R 1 e) ∪ cutPairEvent Q q R 2 e := by
          ext ω
          simp only [mem_union, cutPairEvent, cutAnyEvent, mem_ofPred_eq]
          generalize blockColor Q q R ω (Q.src e) = a
          generalize blockColor Q q R ω (Q.tgt e) = b
          fin_cases a <;> fin_cases b <;> decide
        rw [hunion]
        exact ((measurableSet_cutPairEvent Q q R 0 e).union
          (measurableSet_cutPairEvent Q q R 1 e)).union
          (measurableSet_cutPairEvent Q q R 2 e)
      have hbad_int (B : cmp.blocks) :
          Integrable (fun ω => (badCount Q q R ω B : ℝ)) P :=
        integrable_badCount hQ_deg q R B
      let indCut (e : cmp.external) (ω : cmp.blocks → BlockSample) : ℝ :=
        (cutAnyEvent Q q R e).indicator (1 : (cmp.blocks → BlockSample) → ℝ) ω
      have hint_cut (e : cmp.external) : Integrable (indCut e) P :=
        (integrable_const (1 : ℝ)).indicator (hcutAny_m e)
      have hlhs_eq : (∑ e : cmp.external, P.real (cutAnyEvent Q q R e)) =
          ∫ ω, (∑ e : cmp.external, indCut e ω) ∂P := by
        rw [integral_finsetSum Finset.univ fun e _ => hint_cut e]
        exact (Finset.sum_congr rfl fun e _ => integral_indicator_one (hcutAny_m e)).symm
      have hae_cut_bad :
          (fun ω => ∑ e : cmp.external, indCut e ω) ≤ᵐ[P]
          (fun ω => ∑ B : cmp.blocks, (badCount Q q R ω B : ℝ)) := by
        filter_upwards [compl_mem_ae_iff.mpr hNullAllRay_null] with ω hω
        simp only [NullAllRay, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists] at hω
        have hnat := sum_cutAny_le_sum_badCount hQ_loop q R hω
        have hlhs_nat : (∑ e : cmp.external, indCut e ω) =
            ((Finset.univ.filter fun e : cmp.external => ω ∈ cutAnyEvent Q q R e).card : ℝ) := by
          rw [Finset.card_filter, Nat.cast_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          dsimp [indCut]
          by_cases h : ω ∈ cutAnyEvent Q q R e <;> simp [h]
        rw [hlhs_nat, ← Nat.cast_sum]
        exact_mod_cast hnat
      have hsum_bad : (∑ e : cmp.external, P.real (cutAnyEvent Q q R e)) ≤
          ∑ B : cmp.blocks, ∫ ω, (badCount Q q R ω B : ℝ) ∂P := by
        rw [hlhs_eq, ← integral_finsetSum _ fun B _ => hbad_int B]
        exact integral_mono_ae
          (integrable_finsetSum _ fun e _ => hint_cut e)
          (integrable_finsetSum _ fun B _ => hbad_int B) hae_cut_bad
      -- Bound `∫ badCount B` by `0` on deg `0`, `2` on `Q12`, and `capAt ρ₀` on `Q3`.
      have hB_bound (B : cmp.blocks) :
          ∫ ω, (badCount Q q R ω B : ℝ) ∂P ≤
            (if B ∈ Q3 then capAt ρ₀ else 0) + (if B ∈ Q12 then 2 else 0) := by
        have hd_le := hQ_deg B
        have hbad_le_deg (ω) : badCount Q q R ω B ≤ (Q.incidenceSet B).ncard := by
          unfold badCount
          rw [toFinset_eq_of_fintype (Q.incidenceSet B) _]
          exact (Finset.card_filter_le _ _).trans_eq (Set.ncard_eq_toFinset_card' _).symm
        interval_cases hdegB : (Q.incidenceSet B).ncard
        · have h0 (ω) : badCount Q q R ω B = 0 := Nat.eq_zero_of_le_zero (hbad_le_deg ω)
          have hn3 : B ∉ Q3 := by simp [Q3, hdegB]
          have hn12 : B ∉ Q12 := by simp [Q12, hdegB]
          simp [h0, hn3, hn12]
        · have hn3 : B ∉ Q3 := by simp [Q3, hdegB]
          have hm12 : B ∈ Q12 := by simp [Q12, hdegB]
          simp only [hn3, hm12, ↓reduceIte, zero_add]
          calc ∫ ω, (badCount Q q R ω B : ℝ) ∂P ≤ ∫ _, (2 : ℝ) ∂P :=
                integral_mono (hbad_int B) (integrable_const 2) fun ω => by
                  have h1 := hbad_le_deg ω
                  exact_mod_cast (by omega : badCount Q q R ω B ≤ 2)
            _ = 2 := by simp
        · have hn3 : B ∉ Q3 := by simp [Q3, hdegB]
          have hm12 : B ∈ Q12 := by simp [Q12, hdegB]
          simp only [hn3, hm12, ↓reduceIte, zero_add]
          calc ∫ ω, (badCount Q q R ω B : ℝ) ∂P ≤ ∫ _, (2 : ℝ) ∂P :=
                integral_mono (hbad_int B) (integrable_const 2) fun ω => by
                  exact_mod_cast hbad_le_deg ω
            _ = 2 := by simp
        · have hm3 : B ∈ Q3 := by simp [Q3, hdegB]
          have hn12 : B ∉ Q12 := by simp [Q12, hdegB]
          simp only [hm3, hn12, ↓reduceIte, add_zero]
          exact integral_badCount_le_capAt hQ_loop hQ_deg hq hρ₀ hρ_lt hρ hdegB
      calc (∑ e : cmp.external, P.real (cutAnyEvent Q q R e))
          ≤ ∑ B : cmp.blocks, ∫ ω, (badCount Q q R ω B : ℝ) ∂P := hsum_bad
        _ ≤ ∑ B : cmp.blocks, ((if B ∈ Q3 then capAt ρ₀ else 0) + (if B ∈ Q12 then 2 else 0)) :=
            Finset.sum_le_sum fun B _ => hB_bound B
        _ = capAt ρ₀ * (Q3.card : ℝ) + 2 * (Q12.card : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
              Finset.sum_const, nsmul_eq_mul, mul_comm (Q3.card : ℝ),
              Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
              mul_comm (Q12.card : ℝ)]
    -- Deduce the expected pairwise cut bound for each `c : Fin 3`.
    have hexp_cutPair (c : Fin 3) :
        (∑ e : cmp.external, (1 : ℝ) * P.real (cutPairEvent Q q R c e)) ≤
          2 / 3 * threeWayCapCoefficient * (G.cycleRank : ℝ) +
            (ξ / 2 + 16 / (M : ℝ)) * (Nat.card V : ℝ) := by
      have hthird : (∑ e : cmp.external, (1 : ℝ) * P.real (cutPairEvent Q q R c e)) =
          1 / 3 * ∑ e : cmp.external, P.real (cutAnyEvent Q q R e) := by
        have h3e (e : cmp.external) : P.real (cutPairEvent Q q R c e) =
            1 / 3 * P.real (cutAnyEvent Q q R e) :=
          measureReal_cutPairEvent_eq_third Q q R c e
        simp_rw [one_mul, h3e]
        rw [← Finset.mul_sum]
      have hcap3 : capAt ρ₀ ≤ 3 := capAt_le_three ρ₀
      have hcap_nonneg : 0 ≤ capAt ρ₀ := by
        have hstrad_pos : 0 ≤ straddleBound ρ₀ := by
          unfold straddleBound
          have ha : 0 ≤ arccos ((1 + 3 * ρ₀) / 4) := arccos_nonneg _
          positivity
        have hsqrt_le1 : √((1 + ρ₀) / 2) ≤ 1 := sqrt_le_one.mpr (by linarith)
        unfold capAt
        linarith only [hstrad_pos, hsqrt_le1]
      have hQ3_real : (Q3.card : ℝ) ≤ 2 * (G.cycleRank : ℝ) + (Q12.card : ℝ) := by
        exact_mod_cast hQ3_le.trans (Nat.add_le_add_left hQ1_le_Q12 _)
      have h1 : capAt ρ₀ * (Q3.card : ℝ) + 2 * (Q12.card : ℝ) ≤
          2 * capAt ρ₀ * (G.cycleRank : ℝ) + 5 * (Q12.card : ℝ) := by
        have hm1 := mul_le_mul_of_nonneg_left hQ3_real hcap_nonneg
        have hm2 : capAt ρ₀ * (Q12.card : ℝ) ≤ 3 * (Q12.card : ℝ) := by gcongr
        linarith only [hm1, hm2]
      have h2 : 2 * capAt ρ₀ * (G.cycleRank : ℝ) ≤
          2 * threeWayCapCoefficient * (G.cycleRank : ℝ) +
            ξ / 2 * (Nat.card V : ℝ) := by
        have hβ_real : (G.cycleRank : ℝ) ≤ (Nat.card V : ℝ) := Nat.cast_le.mpr hbeta_le_V
        have hm1 : 2 * capAt ρ₀ * (G.cycleRank : ℝ) ≤
            2 * (threeWayCapCoefficient + ξ / 4) * (G.cycleRank : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hcap_le]) (Nat.cast_nonneg _)
        have hm2 : ξ / 2 * (G.cycleRank : ℝ) ≤ ξ / 2 * (Nat.card V : ℝ) := by gcongr
        linarith only [hm1, hm2]
      have h3 : 5 / 3 * (Q12.card : ℝ) ≤ 16 / (M : ℝ) * (Nat.card V : ℝ) := by
        calc 5 / 3 * (Q12.card : ℝ) ≤ 2 * (Q12.card : ℝ) := by
              have : (0 : ℝ) ≤ Q12.card := Nat.cast_nonneg _
              linarith only [this]
          _ ≤ 2 * (8 * (Nat.card V : ℝ) / (M : ℝ)) := by gcongr
          _ = 16 / (M : ℝ) * (Nat.card V : ℝ) := by ring
      have hξV : 0 ≤ ξ * (Nat.card V : ℝ) := by positivity
      rw [hthird, add_mul]
      linarith only [hexp_cutAny, h1, h2, h3, hξV]
    -- Apply `WeightedSecondMoment` to the `6` local block/edge sums!
    set h : ℝ := (Nat.card V : ℝ)
    have hh_pos : 0 < h := by
      dsimp [h]; exact_mod_cast (Nat.zero_lt_of_lt hM_lt_V)
    set thr : ℝ := η * h
    have hthr_pos : 0 < thr := by positivity
    let aWt (B : cmp.blocks) : ℝ := ((A ∩ {v : V | v ∈ B.1}).ncard : ℝ)
    have haWt_bounds (B : cmp.blocks) : 0 ≤ aWt B ∧ aWt B ≤ M := by
      refine ⟨Nat.cast_nonneg _, ?_⟩
      have hsub : A ∩ {v : V | v ∈ B.1} ⊆ {v : V | v ∈ B.1} := inter_subset_right
      have hle_len : (A ∩ {v : V | v ∈ B.1}).ncard ≤ cmp.blockWeight B := by
        refine (ncard_le_ncard hsub (toFinite _)).trans ?_
        rw [cmp.ncard_block_eq_length B, CappedCompression.blockWeight]
        simp
      exact Nat.cast_le.mpr (hle_len.trans (cmp.blockWeight_le B))
    have haWt_eq (B : cmp.blocks) :
        aWt B = (((Finset.univ.filter (· ∈ A)).filter fun v => cmp.blockOf v = B).card : ℝ) := by
      dsimp only [aWt]
      congr 1; rw [← ncard_coe_finset]; congr 1; ext v; simp [cmp.mem_iff_blockOf_eq]
    have haWt_sum_univ : ∑ B : cmp.blocks, aWt B = (A.ncard : ℝ) := by
      simp_rw [haWt_eq]
      rw [← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter, ← ncard_coe_finset]
      congr 2; ext v; simp
    let colEvent (c : Fin 3) (B : cmp.blocks) : Set (cmp.blocks → BlockSample) :=
      {ω | blockColor Q q R ω B = c}
    let devA (c : Fin 3) := weightedDeviation P Finset.univ aWt (colEvent c) thr
    let devCut (c : Fin 3) :=
      weightedDeviation P Finset.univ (fun _ => 1) (cutPairEvent Q q R c) thr
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have hdevA_le (c : Fin 3) : P.real (devA c) ≤ h * (M : ℝ) ^ 2 * D_blk / thr ^ 2 :=
      (measureReal_weightedDeviation_le _ (fun B _ => measurableSet_blockColor_eq Q q R B c)
        (fun B _ => (haWt_bounds B).1) (fun B _ => (haWt_bounds B).2) _
        (fun B _ ω₁ ω₂ h12 => by simp only [mem_ofPred_eq, dependsOn_blockColor Q q R B h12])
        (fun B _ => card_not_disjoint_closedBall_le hQ_deg (by norm_num) R B) hthr_pos).trans (by
          gcongr
          rw [Finset.card_univ, Fintype.card_coe, show h = Nat.card V from rfl]
          exact_mod_cast hblocks_le_V)
    have hdevCut_le (c : Fin 3) : P.real (devCut c) ≤ 2 * h * (M : ℝ) ^ 2 * D_edg / thr ^ 2 :=
      (measureReal_weightedDeviation_le _ (fun e _ => measurableSet_cutPairEvent Q q R c e)
        (fun _ _ => zero_le_one) (fun _ _ => hM1) _ (fun e _ => dependsOn_cutPairEvent Q q R c e)
        (fun e _ => card_not_disjoint_closedBall_src_le hQ_deg (R + 1) e) hthr_pos).trans (by
          gcongr
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, show h = Nat.card V from rfl]
          exact_mod_cast (by omega : Nat.card cmp.external ≤ 2 * Nat.card V))
    -- The `6` deviation events together have probability strictly below `1`.
    have ha : 6 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2 < h := by
      have hlt : ((⌈12 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2⌉₊ + 1 : ℕ) : ℝ) < h :=
        Nat.cast_lt.mpr ((le_max_right _ _).trans_lt hsmall)
      have := Nat.le_ceil (12 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2)
      have : 0 ≤ 6 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2 := by positivity
      push_cast at hlt
      linarith [show 12 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2 =
        2 * (6 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2) by ring]
    obtain ⟨ω, hω⟩ := exists_forall_notMem_of_sum_le (s := Finset.univ) (A := Sum.elim devA devCut)
      (b := Sum.elim (fun _ => h * (M : ℝ) ^ 2 * D_blk / thr ^ 2)
        (fun _ => 2 * h * (M : ℝ) ^ 2 * D_edg / thr ^ 2))
      (by rintro (c | c) -; exacts [hdevA_le c, hdevCut_le c]) (by
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : 0 ≤ h * (M : ℝ) ^ 2 * D_blk / thr ^ 2 := by positivity
        calc _ ≤ 6 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) * h / thr ^ 2 := by
              linarith [show 6 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) * h / thr ^ 2 =
                6 * (h * M ^ 2 * D_blk / thr ^ 2) + 3 * (2 * h * M ^ 2 * D_edg / thr ^ 2) by ring]
          _ < 1 := mul_div_mul_sq_lt_one hη.ne' hh_pos ha)
    have hgoodA (c : Fin 3) : ω ∉ devA c := hω (.inl c) (Finset.mem_univ _)
    have hgoodC (c : Fin 3) : ω ∉ devCut c := hω (.inr c) (Finset.mem_univ _)
    -- Lift `blockColor Q q R ω` to `col : V → Fin 3` along `cmp.blockOf`.
    refine ⟨fun v => blockColor Q q R ω (cmp.blockOf v), fun c => ?_, fun c => ?_⟩
    · -- Balance of `A ∩ {v | col v = c}`:
      have hgood :=
        not_le.mp (by simpa only [devA, weightedDeviation, mem_ofPred_eq] using hgoodA c)
      have hval : ((A ∩ {v : V | blockColor Q q R ω (cmp.blockOf v) = c}).ncard : ℝ) =
          ∑ B : cmp.blocks, aWt B * (colEvent c B).indicator 1 ω := by
        have htot_card : (A ∩ {v : V | blockColor Q q R ω (cmp.blockOf v) = c}).ncard =
            ∑ B ∈ Finset.univ.filter (fun B => blockColor Q q R ω B = c),
              ((Finset.univ.filter (· ∈ A)).filter fun v => cmp.blockOf v = B).card := by
          rw [Finset.sum_card_fiberwise_eq_card_filter, ← ncard_coe_finset]
          congr 1; ext v; simp
        rw [htot_card, Nat.cast_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [haWt_eq]
        by_cases hB : blockColor Q q R ω B = c <;> simp [colEvent, hB]
      have hmean : (∑ B : cmp.blocks, aWt B * P.real (colEvent c B)) =
          1 / 3 * (A.ncard : ℝ) := by
        have h3b (B : cmp.blocks) : P.real (colEvent c B) = 1 / 3 :=
          measureReal_blockColor_eq_one_third Q q R B c
        simp_rw [h3b]
        rw [← Finset.sum_mul, haWt_sum_univ]
        ring
      rw [hval, ← hmean]
      have hη_le : η * h ≤ ξ * h + (C₀ : ℝ) := by
        have hη_lt_ξ : η ≤ ξ := by
          linarith only [hξ, hη, hslack, show 0 ≤ 16 / (M : ℝ) by positivity]
        have hm := mul_le_mul_of_nonneg_right hη_lt_ξ hh_pos.le
        have hc0 : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
        linarith only [hm, hc0]
      exact hgood.le.trans hη_le
    · -- Pairwise edge-cut bound `E(V_c, V_{c + 1})`:
      have hgood :=
        not_le.mp (by simpa only [devCut, weightedDeviation, mem_ofPred_eq] using hgoodC c)
      set Sc : Set cmp.blocks := {B | blockColor Q q R ω B = c}
      set Sc1 : Set cmp.blocks := {B | blockColor Q q R ω B = c + 1}
      have hdisj_c : Disjoint Sc Sc1 :=
        disjoint_left.mpr fun B h1 h2 => by
          rw [mem_ofPred_eq] at h1 h2; rw [h1] at h2; fin_cases c <;> revert h2 <;> decide
      have hpre_eq : (G.edgeCut {v | blockColor Q q R ω (cmp.blockOf v) = c} ∩
          G.edgeCut {v | blockColor Q q R ω (cmp.blockOf v) = c + 1}).ncard =
          (Q.edgeCut Sc ∩ Q.edgeCut Sc1).ncard :=
        cmp.ncard_crossEdges_preimage hdisj_c
      have hQ_cut_sum : ((Q.edgeCut Sc ∩ Q.edgeCut Sc1).ncard : ℝ) =
          ∑ e : cmp.external, (1 : ℝ) * (cutPairEvent Q q R c e).indicator 1 ω := by
        have hset_eq : Q.edgeCut Sc ∩ Q.edgeCut Sc1 =
            {e : cmp.external | ω ∈ cutPairEvent Q q R c e} := by
          ext e
          simp only [mem_inter_iff, Multigraph.mem_edgeCut, Sc, Sc1, cutPairEvent, mem_ofPred_eq]
          generalize blockColor Q q R ω (Q.src e) = a
          generalize blockColor Q q R ω (Q.tgt e) = b
          fin_cases c <;> fin_cases a <;> fin_cases b <;> decide
        rw [hset_eq, show {e : cmp.external | ω ∈ cutPairEvent Q q R c e}.ncard =
            (Finset.univ.filter fun e : cmp.external => ω ∈ cutPairEvent Q q R c e).card by
          rw [← ncard_coe_finset]; congr 1; ext e; simp]
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        by_cases he : ω ∈ cutPairEvent Q q R c e <;> simp [he]
      rw [hpre_eq, hQ_cut_sum]
      have habs := le_of_abs_le hgood.le
      have hexp := hexp_cutPair c
      have hslack_h : (ξ / 2 + 16 / (M : ℝ)) * h + η * h ≤ ξ * h + (C₀ : ℝ) := by
        have hsum_coef : (ξ / 2 + 16 / (M : ℝ)) + η ≤ ξ := by linarith only [hslack, hξ]
        have hm := mul_le_mul_of_nonneg_right hsum_coef hh_pos.le
        have hc0 : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
        linarith only [hm, hc0]
      dsimp [thr] at habs
      dsimp [h] at hslack_h ⊢
      linarith only [habs, hexp, hslack_h]

end Cslib.Circuits.Frontier.TensorRank
