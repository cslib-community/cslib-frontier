/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.BoundedDegree
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Core
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Coefficient
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.MultiGaussian
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Degree-weighted max-product walk kernels for bounded-degree layouts

In a saturated compression of a multigraph of maximum degree `d ≥ 3`, the quotient core `H` is not
necessarily `d`-regular: vertex degrees `D_u = |incidenceSet u|` (counted with multiplicity) range
over `3 ≤ D_u ≤ d`, subject to the saturation condition `D_u + D_v ≥ d + 3` across every edge
`e = (u, v)`. Using a uniform decay ratio `q = 1 / √(d - 1)` penalises degree-three endpoints as
if they had degree `d`, losing both on the core-size bound `3 d / (2 d - 3)` and on mixed-degree
edges.

Give each edge `(u, v)` of `H.toSimpleGraph` the degree-weighted step factor

`q_{uv} = θ / (√(√(D_u - 1)) · √(√(D_v - 1))) = θ · ((D_u - 1)(D_v - 1)) ^ (-1/4)`

for `θ ∈ [0, 1)`, and define the *truncated max-product walk kernel* `weightedKernelRow` at radius
`R` by Bellman–Ford iteration up to `R` steps. Because `q_{uv} < 1` when `D_u, D_v ≥ 3`, strictly
improving walks never backtrack, and backward induction bounds the truncation-boundary square sum
at `u` by `(D_u / 2) θ ^ (2 R) ≤ (d / 2) θ ^ (2 R)`, even in the presence of parallel edges
(`(H.toSimpleGraph.neighborSet w).ncard ≤ D_w`). Consequently, adjacent unit rows satisfy

`2 q_{uv} / (1 + q_{uv} ^ 2) - (d / 2) θ ^ (2 R) ≤
  ⟪unitWeightedKernelRow u, unitWeightedKernelRow v⟫`

(`le_inner_unitWeightedKernelRow`). Summing Sheppard's crossing bound [Sheppard1899] over all
edges of `H` with multiplicity and comparing edge-by-edge against `1 - 1 / D_u - 1 / D_v` via the
multigraph handshake identity `∑_e (1 - 1 / D_u - 1 / D_v) = |E(H)| - |V(H)| ≤ β₁(G) - 1` yields
`LayoutBound d A` whenever `arccos(ρ_{d₁, d₂}) / π ≤ A (1 - 1 / d₁ - 1 / d₂)` holds on all valid
endpoint degree pairs `3 ≤ d₁ ≤ d₂ ≤ d` with `d₁ + d₂ ≥ d + 3` (`layoutBound_of_weightedKernel`).

## Closed-form layout bounds

* **`d = 4` (`r = 3`)**: `LayoutBound 4 (1 / 3)` (`layoutBound_four_one_third`), improving `A_4`
  from `2 / 5` to `1 / 3` (`(4, 4)` is tight at `arccos(√3 / 2) / π = 1 / 6`; `(3, 4)` has slack).
* **`d = 5` (`r = 4`)**: `LayoutBound 5 (5 / 3 * arccos (4 / 5) / π)` (`layoutBound_five_weighted`,
  `≈ 0.341388`, down from `≈ 0.43893`).
* **`d = 6` (`r = 5`)**: `LayoutBound 6 (3 / 2 * arccos (√5 / 3) / π)` (`layoutBound_six_weighted`,
  `≈ 0.348419`, down from `≈ 0.46456`).

## Main definitions

* `Cslib.Circuits.Frontier.WeightedKernel.edgeWeight`: degree-weighted step factor `q_{uv}`.
* `Cslib.Circuits.Frontier.WeightedKernel.weightedKernelRow`,
  `Cslib.Circuits.Frontier.WeightedKernel.unitWeightedKernelRow`: truncated max-product walk kernel
  row and its unit normalization.
* `Cslib.Circuits.Frontier.WeightedKernel.pairWeight`,
  `Cslib.Circuits.Frontier.WeightedKernel.pairCorrelation`: limiting `θ = 1` weight and adjacent
  correlation for endpoint degrees `(d₁, d₂)`.
* `Cslib.Circuits.Frontier.WeightedKernel.fiveCoefficient`,
  `Cslib.Circuits.Frontier.WeightedKernel.sixCoefficient`: exact layout coefficients for `d = 5, 6`.

## Main results

* `Cslib.Circuits.Frontier.WeightedKernel.le_inner_weightedKernelRow`,
  `Cslib.Circuits.Frontier.WeightedKernel.le_inner_unitWeightedKernelRow`: adjacent inner-product
  lower bounds.
* `Cslib.Circuits.Frontier.WeightedKernel.sum_one_sub_inv_deg_eq`: multigraph cycle-excess
  handshake.
* `Cslib.Circuits.Frontier.WeightedKernel.pairCorrelation_self`: diagonal specialization to
  `Cslib.Circuits.Frontier.Gaussian.vertexCorrelation`.
* `Cslib.Circuits.Frontier.layoutBound_of_weightedKernel`: general degree-pair criterion for
  `LayoutBound d A`.
* `Cslib.Circuits.Frontier.layoutBound_four_one_third`: `LayoutBound 4 (1 / 3)`.
* `Cslib.Circuits.Frontier.layoutBound_five_weighted`: `LayoutBound 5 fiveCoefficient`.
* `Cslib.Circuits.Frontier.layoutBound_six_weighted`: `LayoutBound 6 sixCoefficient`.

## References

* [W. F. Sheppard, *On the application of the theory of error to cases of normal distribution
  and normal correlation*][Sheppard1899]
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier

namespace WeightedKernel

open Cslib.Circuits.Frontier.Gaussian

/-! ### Finite maximum with zero floor -/

/-- Maximum of `f` over a finite set `s`, floored at `0`. -/
private noncomputable def finsetMaxZero {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  open Classical in
  (insert (0 : ℝ) (s.image f)).max' (Finset.insert_nonempty _ _)

private theorem finsetMaxZero_nonneg {α : Type*} (s : Finset α) (f : α → ℝ) :
    0 ≤ finsetMaxZero s f :=
  open Classical in Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

private theorem le_finsetMaxZero {α : Type*} {s : Finset α} {f : α → ℝ} {w : α} (hw : w ∈ s) :
    f w ≤ finsetMaxZero s f :=
  open Classical in Finset.le_max' _ (f w) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hw))

private theorem finsetMaxZero_le {α : Type*} {s : Finset α} {f : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ w ∈ s, f w ≤ c) : finsetMaxZero s f ≤ c := by
  classical
  refine Finset.max'_le _ _ _ fun y hy => (Finset.mem_insert.mp hy).elim (· ▸ hc) fun hy => ?_
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  exact h w hw

private theorem exists_mem_of_finsetMaxZero_pos {α : Type*} {s : Finset α} {f : α → ℝ}
    (hpos : 0 < finsetMaxZero s f) : ∃ w ∈ s, f w = finsetMaxZero s f := by
  classical
  exact Finset.mem_image.mp <|
    (Finset.mem_insert.mp (Finset.max'_mem _ _)).resolve_left hpos.ne'

private theorem sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] (B : Finset β)
    (g : β → Finset α) {f : α → ℝ} (hf : ∀ z, 0 ≤ f z) :
    ∑ z ∈ B.biUnion g, f z ≤ ∑ c ∈ B, ∑ z ∈ g c, f z := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert b B hb ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hb, ← Finset.union_sdiff_self_eq_union,
      Finset.sum_union disjoint_sdiff_self_right]
    exact add_le_add le_rfl
      ((Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun z _ _ => hf z).trans ih)

/-! ### Degree-weighted max-product walk kernel -/

section Kernel

variable {V : Type*}

/-- Symmetric degree-weighted step factor `θ / (√(√(deg u - 1)) * √(√(deg v - 1)))`. -/
noncomputable def edgeWeight (deg : V → ℕ) (θ : ℝ) (u v : V) : ℝ :=
  θ / (√(√((deg u : ℝ) - 1)) * √(√((deg v : ℝ) - 1)))

/-- The edge weight is symmetric in its endpoints. -/
theorem edgeWeight_comm (deg : V → ℕ) (θ : ℝ) (u v : V) :
    edgeWeight deg θ u v = edgeWeight deg θ v u := by
  simp only [edgeWeight, mul_comm]

/-- The edge weight is nonnegative when `θ ≥ 0`. -/
theorem edgeWeight_nonneg (deg : V → ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (u v : V) :
    0 ≤ edgeWeight deg θ u v :=
  div_nonneg hθ (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))

/-- Squaring `edgeWeight` removes the outer square roots. -/
theorem edgeWeight_sq (deg : V → ℕ) (θ : ℝ) (u v : V) :
    edgeWeight deg θ u v ^ 2 = θ ^ 2 / (√((deg u : ℝ) - 1) * √((deg v : ℝ) - 1)) := by
  rw [edgeWeight, div_pow, mul_pow, sq_sqrt (sqrt_nonneg _), sq_sqrt (sqrt_nonneg _)]

private theorem sqrt_two_le_sqrt_deg_sub_one {d : ℕ} (hd : 3 ≤ d) :
    √2 ≤ √((d : ℝ) - 1) :=
  sqrt_le_sqrt (by linarith [Nat.ofNat_le_cast (α := ℝ).mpr hd])

private theorem edgeWeight_sq_le_half {deg : V → ℕ} {θ : ℝ} {u v : V} (hu : 3 ≤ deg u)
    (hv : 3 ≤ deg v) : edgeWeight deg θ u v ^ 2 ≤ θ ^ 2 / 2 := by
  rw [edgeWeight_sq]
  have hprod : (2 : ℝ) ≤ √((deg u : ℝ) - 1) * √((deg v : ℝ) - 1) :=
    calc (2 : ℝ) = √2 * √2 := (mul_self_sqrt (by norm_num)).symm
      _ ≤ √((deg u : ℝ) - 1) * √((deg v : ℝ) - 1) :=
          mul_le_mul (sqrt_two_le_sqrt_deg_sub_one hu) (sqrt_two_le_sqrt_deg_sub_one hv)
            (sqrt_nonneg _) (sqrt_nonneg _)
  exact div_le_div_of_nonneg_left (sq_nonneg θ) (by norm_num) hprod

private theorem edgeWeight_lt_one {deg : V → ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {u v : V}
    (hu : 3 ≤ deg u) (hv : 3 ≤ deg v) : edgeWeight deg θ u v < 1 := by
  apply (pow_lt_pow_iff_left₀ (edgeWeight_nonneg deg hθ0 u v) zero_le_one two_ne_zero).mp
  rw [one_pow]
  have hθsq := (pow_le_pow_left₀ hθ0 hθ1 2).trans_eq (one_pow _)
  exact (edgeWeight_sq_le_half (θ := θ) hu hv).trans_lt (by linarith only [hθsq])

/-- Maximum walk weight of length at most `r` from `u` to `z` in `H`, computed recursively by
Bellman–Ford updates from the source vertex. -/
private noncomputable def bestWalkWeight [Finite V] (H : SimpleGraph V) (deg : V → ℕ) (θ : ℝ) :
    ℕ → V → V → ℝ
  | 0, u, z => open Classical in if u = z then 1 else 0
  | r + 1, u, z =>
      open Classical in
      letI : Fintype V := Fintype.ofFinite V
      max (bestWalkWeight H deg θ r u z)
        (finsetMaxZero (H.neighborFinset u) fun w =>
          edgeWeight deg θ u w * bestWalkWeight H deg θ r w z)

/-- The truncated degree-weighted max-product walk kernel row of `v` at radius `R`. -/
noncomputable def weightedKernelRow [Finite V] (H : SimpleGraph V) (deg : V → ℕ) (θ : ℝ) (R : ℕ)
    (v : V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 fun z => bestWalkWeight H deg θ R v z

/-- The unit degree-weighted kernel row of `v`: `weightedKernelRow` divided by its norm. -/
noncomputable def unitWeightedKernelRow [Fintype V] (H : SimpleGraph V) (deg : V → ℕ) (θ : ℝ)
    (R : ℕ) (v : V) : EuclideanSpace ℝ V :=
  ‖weightedKernelRow H deg θ R v‖⁻¹ • weightedKernelRow H deg θ R v

section FiniteProps

variable [Finite V] {H : SimpleGraph V} {deg : V → ℕ} {θ : ℝ}

private theorem weightedKernelRow_apply (R : ℕ) (v z : V) :
    weightedKernelRow H deg θ R v z = bestWalkWeight H deg θ R v z :=
  rfl

private theorem bestWalkWeight_succ (r : ℕ) (u z : V) :
    bestWalkWeight H deg θ (r + 1) u z =
      open Classical in
      letI : Fintype V := Fintype.ofFinite V
      max (bestWalkWeight H deg θ r u z)
        (finsetMaxZero (H.neighborFinset u) fun w =>
          edgeWeight deg θ u w * bestWalkWeight H deg θ r w z) := by
  rw [bestWalkWeight]

private theorem bestWalkWeight_nonneg (R : ℕ) (u z : V) : 0 ≤ bestWalkWeight H deg θ R u z := by
  cases R with
  | zero =>
    rw [bestWalkWeight]
    split_ifs <;> norm_num
  | succ r =>
    rw [bestWalkWeight_succ]
    exact le_trans (finsetMaxZero_nonneg _ _) (le_max_right _ _)

/-- Every entry of `weightedKernelRow` is nonnegative. -/
theorem weightedKernelRow_nonneg (R : ℕ) (v z : V) : 0 ≤ weightedKernelRow H deg θ R v z :=
  bestWalkWeight_nonneg R v z

private theorem bestWalkWeight_le_succ (r : ℕ) (u z : V) :
    bestWalkWeight H deg θ r u z ≤ bestWalkWeight H deg θ (r + 1) u z :=
  bestWalkWeight_succ r u z ▸ le_max_left _ _

private theorem step_le_bestWalkWeight_succ (r : ℕ) {u w : V} (huw : H.Adj u w) (z : V) :
    edgeWeight deg θ u w * bestWalkWeight H deg θ r w z ≤
      bestWalkWeight H deg θ (r + 1) u z := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  rw [bestWalkWeight_succ]
  exact (le_finsetMaxZero (f := fun w' => edgeWeight deg θ u w' * bestWalkWeight H deg θ r w' z)
    ((SimpleGraph.mem_neighborFinset H u w).mpr huw)).trans (le_max_right _ _)

private theorem one_le_bestWalkWeight_self (R : ℕ) (v : V) :
    1 ≤ bestWalkWeight H deg θ R v v := by
  induction R with
  | zero => simp [bestWalkWeight]
  | succ r ih => exact ih.trans (bestWalkWeight_le_succ r v v)

private theorem bestWalkWeight_le_one (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hlo : ∀ v, 3 ≤ deg v)
    (R : ℕ) (u z : V) : bestWalkWeight H deg θ R u z ≤ 1 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  induction R generalizing u with
  | zero =>
    rw [bestWalkWeight]
    split_ifs <;> norm_num
  | succ r ih =>
    rw [bestWalkWeight_succ]
    exact max_le (ih u) (finsetMaxZero_le zero_le_one fun w _ =>
      (mul_le_of_le_one_left (bestWalkWeight_nonneg r w z)
        (edgeWeight_lt_one hθ0 hθ1 (hlo u) (hlo w)).le).trans (ih w))

/-- At `v` itself, `weightedKernelRow` equals `1` whenever `0 ≤ θ ≤ 1` and degrees are at least
three. -/
theorem weightedKernelRow_self (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hlo : ∀ v, 3 ≤ deg v) (R : ℕ)
    (v : V) : weightedKernelRow H deg θ R v v = 1 :=
  le_antisymm (bestWalkWeight_le_one hθ0 hθ1 hlo R v v) (one_le_bestWalkWeight_self R v)

/-- Outside the closed ball of radius `R` around `v`, `weightedKernelRow` vanishes. -/
theorem weightedKernelRow_eq_zero_of_lt {R : ℕ} {v z : V} (h : R < H.edist v z) :
    weightedKernelRow H deg θ R v z = 0 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  rw [weightedKernelRow_apply]
  induction R generalizing v with
  | zero =>
    rw [bestWalkWeight, ite_eq_right fun hvz => by simp [hvz] at h]
  | succ r ih =>
    rw [bestWalkWeight_succ, ih (lt_of_le_of_lt (by exact_mod_cast Nat.le_succ r) h),
      max_eq_right (finsetMaxZero_nonneg _ _)]
    refine le_antisymm (finsetMaxZero_le le_rfl fun w hw => ?_) (finsetMaxZero_nonneg _ _)
    have hvw : H.Adj v w := (SimpleGraph.mem_neighborFinset H v w).mp hw
    have hwz : (r : ℕ∞) < H.edist w z := lt_of_not_ge fun hle => by
      push_cast at h
      exact h.not_ge ((hvw.edist_le_edist_add_one z).trans (add_le_add_left hle 1))
    rw [ih hwz, mul_zero]

/-! ### Pointwise adjacent defect -/

/-- **Pointwise adjacent defect.** At radius `r + 1`, the entries at `z` of adjacent vertices
`u ~ v` satisfy `κ (a ^ 2 + b ^ 2) / 2 - a b ≤ 0` unless the larger entry strictly improved at step
`r + 1`, in which case the defect is at most half its square. -/
private theorem weightedKernelRow_defect_le (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hlo : ∀ v, 3 ≤ deg v)
    (r : ℕ) {u v : V} (huv : H.Adj u v) (z : V) :
    let q := edgeWeight deg θ u v
    2 * q / (1 + q ^ 2) *
        (bestWalkWeight H deg θ (r + 1) u z ^ 2 + bestWalkWeight H deg θ (r + 1) v z ^ 2) / 2 -
        bestWalkWeight H deg θ (r + 1) u z * bestWalkWeight H deg θ (r + 1) v z ≤
      ((if bestWalkWeight H deg θ r u z < bestWalkWeight H deg θ (r + 1) u z
          then bestWalkWeight H deg θ (r + 1) u z ^ 2 else 0) +
        (if bestWalkWeight H deg θ r v z < bestWalkWeight H deg θ (r + 1) v z
          then bestWalkWeight H deg θ (r + 1) v z ^ 2 else 0)) / 2 := by
  classical
  dsimp only
  wlog hba : bestWalkWeight H deg θ (r + 1) v z ≤ bestWalkWeight H deg θ (r + 1) u z
    generalizing u v
  · simpa only [edgeWeight_comm deg θ v u, add_comm, mul_comm] using
      this huv.symm (le_of_not_ge hba)
  set q := edgeWeight deg θ u v
  set a := bestWalkWeight H deg θ (r + 1) u z
  set b := bestWalkWeight H deg θ (r + 1) v z
  have hb0 : 0 ≤ b := bestWalkWeight_nonneg (r + 1) v z
  have hIv : 0 ≤ if bestWalkWeight H deg θ r v z < b then b ^ 2 else 0 := by
    split_ifs <;> positivity
  by_cases hu : bestWalkWeight H deg θ r u z < a
  · rw [ite_eq_left hu]
    have hκ_ab := mul_le_of_le_one_left (by positivity : 0 ≤ a ^ 2 + b ^ 2)
      (two_mul_div_one_add_sq_le_one q)
    linarith only [(pow_two b).trans_le (mul_le_mul_of_nonneg_right hba hb0), hκ_ab, hIv,
      mul_nonneg (hb0.trans hba) hb0]
  · rw [ite_eq_right hu, zero_add]
    have hru : bestWalkWeight H deg θ r u z = a :=
      le_antisymm (bestWalkWeight_le_succ r u z) (le_of_not_gt hu)
    have hqa : q * a ≤ b := by
      simpa only [edgeWeight_comm deg θ v u, hru] using
        step_le_bestWalkWeight_succ (deg := deg) (θ := θ) r huv.symm z
    have hqb : q * b ≤ a :=
      (mul_le_of_le_one_left hb0 (edgeWeight_lt_one hθ0 hθ1 (hlo u) (hlo v)).le).trans hba
    have hneg : 2 * q / (1 + q ^ 2) * (a ^ 2 + b ^ 2) / 2 ≤ a * b := by
      rw [div_le_iff₀ two_pos, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hqa) (sub_nonpos.mpr hqb)]
    linarith only [hneg, hIv]

end FiniteProps

/-! ### Norms and backward-induction sum bounds -/

section FintypeProps

variable [Fintype V] {H : SimpleGraph V} {deg : V → ℕ} {θ : ℝ}

/-- Every `weightedKernelRow` has Euclidean norm at least `1`. -/
theorem one_le_norm_weightedKernelRow (R : ℕ) (v : V) :
    1 ≤ ‖weightedKernelRow H deg θ R v‖ := by
  apply (one_le_pow_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  exact (one_le_pow₀ (one_le_bestWalkWeight_self R v)).trans <|
    Finset.single_le_sum (f := fun z => weightedKernelRow H deg θ R v z ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ v)

/-- Coordinate `z` of `unitWeightedKernelRow` is `weightedKernelRow` divided by its norm. -/
theorem unitWeightedKernelRow_apply (R : ℕ) (v z : V) :
    unitWeightedKernelRow H deg θ R v z =
      ‖weightedKernelRow H deg θ R v‖⁻¹ * weightedKernelRow H deg θ R v z := by
  simp [unitWeightedKernelRow]

/-- Unit weighted kernel rows have norm `1`. -/
@[simp]
theorem norm_unitWeightedKernelRow (R : ℕ) (v : V) :
    ‖unitWeightedKernelRow H deg θ R v‖ = 1 := by
  have h := one_le_norm_weightedKernelRow (H := H) (deg := deg) (θ := θ) R v
  rw [unitWeightedKernelRow, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (by linarith)]

/-- Outside the closed ball of radius `R` around `v`, `unitWeightedKernelRow` vanishes. -/
theorem unitWeightedKernelRow_eq_zero_of_lt {R : ℕ} {v z : V} (h : R < H.edist v z) :
    unitWeightedKernelRow H deg θ R v z = 0 := by
  rw [unitWeightedKernelRow_apply, weightedKernelRow_eq_zero_of_lt h, mul_zero]

open Classical in
/-- Vertices `z` where stepping `a → b` strictly beats `bestWalkWeight` of radius `r` at `a`. -/
private noncomputable def strictStepSet (H : SimpleGraph V) (deg : V → ℕ) (θ : ℝ) (r : ℕ)
    (a b : V) : Finset V :=
  Finset.univ.filter fun z => bestWalkWeight H deg θ r a z <
    edgeWeight deg θ a b * bestWalkWeight H deg θ r b z

open Classical in
/-- Subset of `strictStepSet H deg θ r u b` where `b` achieves `bestWalkWeight` of radius `r + 1`
at `u`. -/
private noncomputable def strictPiece (H : SimpleGraph V) (deg : V → ℕ) (θ : ℝ) (r : ℕ)
    (u b : V) : Finset V :=
  (strictStepSet H deg θ r u b).filter fun z =>
    bestWalkWeight H deg θ (r + 1) u z = edgeWeight deg θ u b * bestWalkWeight H deg θ r b z

/-- Any target `z` whose `bestWalkWeight` strictly improves from radius `r` to `r + 1` at `u`
belongs to `strictPiece H deg θ r u b` for some neighbor `b` of `u`. -/
private theorem exists_mem_strictPiece_of_lt {r : ℕ} {u z : V} [Fintype (H.neighborSet u)]
    (hlt : bestWalkWeight H deg θ r u z < bestWalkWeight H deg θ (r + 1) u z) :
    ∃ b ∈ H.neighborFinset u, z ∈ strictPiece H deg θ r u b ∧
      bestWalkWeight H deg θ (r + 1) u z = edgeWeight deg θ u b * bestWalkWeight H deg θ r b z := by
  classical
  have hdef : bestWalkWeight H deg θ (r + 1) u z =
      max (bestWalkWeight H deg θ r u z)
        (finsetMaxZero (H.neighborFinset u)
          fun b => edgeWeight deg θ u b * bestWalkWeight H deg θ r b z) := by
    rw [bestWalkWeight_succ]
    congr!
  have hmax_eq := hdef.trans ((max_choice _ _).resolve_left fun h => hlt.ne' (hdef.trans h))
  obtain ⟨b, hb_mem, hb_eq⟩ := exists_mem_of_finsetMaxZero_pos
    (hmax_eq ▸ (bestWalkWeight_nonneg r u z).trans_lt hlt)
  have hval := hmax_eq.trans hb_eq.symm
  exact ⟨b, hb_mem, Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ z, hval ▸ hlt⟩, hval⟩, hval⟩

/-- Squared `bestWalkWeight` sum on `strictPiece H deg θ r u b` reduces to `strictStepSet` at
`b`. -/
private theorem sum_sq_strictPiece_le (r : ℕ) (u b : V) :
    ∑ z ∈ strictPiece H deg θ r u b, bestWalkWeight H deg θ (r + 1) u z ^ 2 ≤
      edgeWeight deg θ u b ^ 2 *
        ∑ z ∈ strictStepSet H deg θ r u b, bestWalkWeight H deg θ r b z ^ 2 := by
  classical
  calc ∑ z ∈ strictPiece H deg θ r u b, bestWalkWeight H deg θ (r + 1) u z ^ 2
      = edgeWeight deg θ u b ^ 2 *
          ∑ z ∈ strictPiece H deg θ r u b, bestWalkWeight H deg θ r b z ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z hz => by rw [(Finset.mem_filter.mp hz).2, mul_pow]
    _ ≤ edgeWeight deg θ u b ^ 2 *
          ∑ z ∈ strictStepSet H deg θ r u b, bestWalkWeight H deg θ r b z ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => sq_nonneg _) (sq_nonneg _)

/-- **Non-backtracking tail bound.** Along any oriented edge `a ~ b`, the weighted square sum of
`bestWalkWeight` over `strictStepSet` is at most `(θ ^ 2) ^ (r + 1) / (√(deg a - 1) * √2)`. -/
private theorem edgeWeight_sq_mul_sum_strictStepSet_le (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hlo : ∀ v, 3 ≤ deg v) (hsimple : ∀ v, (H.neighborSet v).ncard ≤ deg v) :
    ∀ (r : ℕ) {a b : V}, H.Adj a b →
      edgeWeight deg θ a b ^ 2 *
          (∑ z ∈ strictStepSet H deg θ r a b, bestWalkWeight H deg θ r b z ^ 2) ≤
        (θ ^ 2) ^ (r + 1) / (√((deg a : ℝ) - 1) * √2)
  | 0, a, b, _ => by
    classical
    have hsub : strictStepSet H deg θ 0 a b ⊆ {b} := fun z hz => by
      have hz' := (Finset.mem_filter.mp hz).2
      rw [bestWalkWeight, bestWalkWeight] at hz'
      refine Finset.mem_singleton.mpr (by_contra fun hzb => ?_)
      rw [ite_eq_right (Ne.symm hzb), mul_zero] at hz'
      split_ifs at hz' <;> linarith
    have hsum : ∑ z ∈ strictStepSet H deg θ 0 a b, bestWalkWeight H deg θ 0 b z ^ 2 ≤ 1 :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _).trans
        (by simp [bestWalkWeight])
    refine (mul_le_of_le_one_right (sq_nonneg _) hsum).trans ?_
    rw [edgeWeight_sq, pow_one]
    have hsa : 0 < √((deg a : ℝ) - 1) :=
      lt_of_lt_of_le (by positivity) (sqrt_two_le_sqrt_deg_sub_one (hlo a))
    exact div_le_div_of_nonneg_left (sq_nonneg θ) (by positivity)
      (mul_le_mul_of_nonneg_left (sqrt_two_le_sqrt_deg_sub_one (hlo b)) hsa.le)
  | r + 1, a, b, hab => by
    classical
    let nb : Finset V := (H.neighborFinset b).erase a
    have hcov : strictStepSet H deg θ (r + 1) a b ⊆ nb.biUnion (strictPiece H deg θ r b) := by
      intro z hz
      have hz' : bestWalkWeight H deg θ (r + 1) a z <
          edgeWeight deg θ a b * bestWalkWeight H deg θ (r + 1) b z :=
        (Finset.mem_filter.mp hz).2
      have hq0 := edgeWeight_nonneg deg hθ0 a b
      have hlt_b : bestWalkWeight H deg θ r b z < bestWalkWeight H deg θ (r + 1) b z :=
        lt_of_not_ge fun hle => hz'.not_ge
          ((mul_le_mul_of_nonneg_left hle hq0).trans (step_le_bestWalkWeight_succ r hab z))
      obtain ⟨c, hc_mem, hc_piece, hc_eq⟩ := exists_mem_strictPiece_of_lt hlt_b
      have hca : c ≠ a := by
        rintro rfl
        rw [hc_eq, edgeWeight_comm deg θ b c, ← mul_assoc, ← sq] at hz'
        have hsq1 := (pow_le_pow_left₀ hq0 (edgeWeight_lt_one hθ0 hθ1.le (hlo c) (hlo b)).le
          2).trans_eq (one_pow _)
        exact hz'.not_ge ((mul_le_of_le_one_left (bestWalkWeight_nonneg r c z) hsq1).trans
          (bestWalkWeight_le_succ r c z))
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_erase.mpr ⟨hca, hc_mem⟩, hc_piece⟩
    have hsum_cov : ∑ z ∈ strictStepSet H deg θ (r + 1) a b,
          bestWalkWeight H deg θ (r + 1) b z ^ 2 ≤
        ∑ c ∈ nb, ∑ z ∈ strictPiece H deg θ r b c, bestWalkWeight H deg θ (r + 1) b z ^ 2 :=
      (Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => sq_nonneg _).trans
        (sum_biUnion_le_of_nonneg nb (strictPiece H deg θ r b) fun _ => sq_nonneg _)
    have hpiece_le : ∀ c ∈ nb,
        ∑ z ∈ strictPiece H deg θ r b c, bestWalkWeight H deg θ (r + 1) b z ^ 2 ≤
          (θ ^ 2) ^ (r + 1) / (√((deg b : ℝ) - 1) * √2) := fun c hc =>
      (sum_sq_strictPiece_le r b c).trans
        (edgeWeight_sq_mul_sum_strictStepSet_le hθ0 hθ1 hlo hsimple r
          ((SimpleGraph.mem_neighborFinset H b c).mp (Finset.mem_of_mem_erase hc)))
    have hcard_nb : (nb.card : ℝ) ≤ (deg b : ℝ) - 1 := by
      have h1 := Finset.card_erase_add_one ((SimpleGraph.mem_neighborFinset H b a).mpr hab.symm)
      rw [SimpleGraph.neighborFinset, ← ncard_eq_toFinset_card'] at h1
      rw [le_sub_iff_add_le]
      exact_mod_cast h1.trans_le (hsimple b)
    have hdb : (3 : ℝ) ≤ deg b := Nat.ofNat_le_cast.mpr (hlo b)
    have hda : (3 : ℝ) ≤ deg a := Nat.ofNat_le_cast.mpr (hlo a)
    have hsb_pos : 0 < √((deg b : ℝ) - 1) := sqrt_pos.mpr (by linarith)
    have hsa_pos : 0 < √((deg a : ℝ) - 1) := sqrt_pos.mpr (by linarith)
    calc edgeWeight deg θ a b ^ 2 *
          ∑ z ∈ strictStepSet H deg θ (r + 1) a b, bestWalkWeight H deg θ (r + 1) b z ^ 2
        ≤ edgeWeight deg θ a b ^ 2 *
            (((deg b : ℝ) - 1) * ((θ ^ 2) ^ (r + 1) / (√((deg b : ℝ) - 1) * √2))) := by
          gcongr
          refine hsum_cov.trans ((Finset.sum_le_sum hpiece_le).trans ?_)
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
      _ = (θ ^ 2) ^ (r + 1 + 1) / (√((deg a : ℝ) - 1) * √2) := by
          rw [edgeWeight_sq, pow_succ' (θ ^ 2) (r + 1)]
          field_simp
          rw [sq_sqrt (by linarith)]

/-- **Root truncation square sum.** At any vertex `u` with `3 ≤ deg u ≤ d` and radius `r + 1 ≥ 1`,
the squared entries of `bestWalkWeight` that strictly improve from radius `r` to `r + 1` sum to at
most `(d / 2) (θ ^ 2) ^ (r + 1)`. -/
private theorem sum_sq_strict_root_le {d : ℕ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hlo : ∀ v, 3 ≤ deg v)
    (hhi : ∀ v, deg v ≤ d) (hsimple : ∀ v, (H.neighborSet v).ncard ≤ deg v) (r : ℕ) (u : V) :
    (∑ z, if bestWalkWeight H deg θ r u z < bestWalkWeight H deg θ (r + 1) u z
        then bestWalkWeight H deg θ (r + 1) u z ^ 2 else 0) ≤
      (d : ℝ) / 2 * (θ ^ 2) ^ (r + 1) := by
  classical
  let rootSet : Finset V :=
    Finset.univ.filter fun z => bestWalkWeight H deg θ r u z < bestWalkWeight H deg θ (r + 1) u z
  have hcov : rootSet ⊆ (H.neighborFinset u).biUnion (strictPiece H deg θ r u) := by
    intro z hz
    obtain ⟨b, hb_mem, hb_piece, _⟩ := exists_mem_strictPiece_of_lt (Finset.mem_filter.mp hz).2
    exact Finset.mem_biUnion.mpr ⟨b, hb_mem, hb_piece⟩
  have hpiece_le : ∀ b ∈ H.neighborFinset u,
      ∑ z ∈ strictPiece H deg θ r u b, bestWalkWeight H deg θ (r + 1) u z ^ 2 ≤
        (θ ^ 2) ^ (r + 1) / (√((deg u : ℝ) - 1) * √2) := fun b hb =>
    (sum_sq_strictPiece_le r u b).trans
      (edgeWeight_sq_mul_sum_strictStepSet_le hθ0 hθ1 hlo hsimple r
        ((SimpleGraph.mem_neighborFinset H u b).mp hb))
  have hprod : (2 : ℝ) ≤ √((deg u : ℝ) - 1) * √2 :=
    calc (2 : ℝ) = √2 * √2 := (mul_self_sqrt (by norm_num)).symm
      _ ≤ √((deg u : ℝ) - 1) * √2 :=
          mul_le_mul_of_nonneg_right (sqrt_two_le_sqrt_deg_sub_one (hlo u)) (sqrt_nonneg _)
  have hcard_u : ((H.neighborFinset u).card : ℝ) ≤ d := by
    rw [SimpleGraph.neighborFinset, ← ncard_eq_toFinset_card']
    exact_mod_cast (hsimple u).trans (hhi u)
  calc (∑ z, if bestWalkWeight H deg θ r u z < bestWalkWeight H deg θ (r + 1) u z
          then bestWalkWeight H deg θ (r + 1) u z ^ 2 else 0)
      = ∑ z ∈ rootSet, bestWalkWeight H deg θ (r + 1) u z ^ 2 :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ b ∈ H.neighborFinset u,
          ∑ z ∈ strictPiece H deg θ r u b, bestWalkWeight H deg θ (r + 1) u z ^ 2 :=
        (Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => sq_nonneg _).trans
          (sum_biUnion_le_of_nonneg _ _ fun _ => sq_nonneg _)
    _ ≤ ∑ _b ∈ H.neighborFinset u, (θ ^ 2) ^ (r + 1) / (√((deg u : ℝ) - 1) * √2) :=
        Finset.sum_le_sum hpiece_le
    _ = ((H.neighborFinset u).card : ℝ) * ((θ ^ 2) ^ (r + 1) / (√((deg u : ℝ) - 1) * √2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ) * ((θ ^ 2) ^ (r + 1) / 2) :=
        by gcongr
    _ = (d : ℝ) / 2 * (θ ^ 2) ^ (r + 1) := by ring

/-- **Correlation of adjacent degree-weighted kernel rows.** For `R ≥ 1` and `θ ∈ [0, 1)`, if
every vertex has degree `3 ≤ deg w ≤ d` bounding its simple neighbor count, adjacent kernel rows
satisfy `κ (‖k_u‖ ^ 2 + ‖k_v‖ ^ 2) / 2 - (d / 2) (θ ^ 2) ^ R ≤ ⟪k_u, k_v⟫` with
`κ = 2 q_{uv} / (1 + q_{uv} ^ 2)`. -/
theorem le_inner_weightedKernelRow {d : ℕ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hlo : ∀ v, 3 ≤ deg v)
    (hhi : ∀ v, deg v ≤ d) (hsimple : ∀ v, (H.neighborSet v).ncard ≤ deg v)
    {R : ℕ} (hR : 1 ≤ R) {u v : V} (huv : H.Adj u v) :
    let q := edgeWeight deg θ u v
    2 * q / (1 + q ^ 2) *
        (‖weightedKernelRow H deg θ R u‖ ^ 2 + ‖weightedKernelRow H deg θ R v‖ ^ 2) / 2 -
        (d : ℝ) / 2 * (θ ^ 2) ^ R ≤
      ⟪weightedKernelRow H deg θ R u, weightedKernelRow H deg θ R v⟫ := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, (Nat.sub_add_cancel hR).symm⟩
  dsimp only
  set q := edgeWeight deg θ u v
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, weightedKernelRow_apply]
  have hpt := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) =>
    weightedKernelRow_defect_le hθ0 hθ1.le hlo r huv z
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib,
    mul_comm (bestWalkWeight H deg θ (r + 1) u _)] at hpt
  linarith [sum_sq_strict_root_le hθ0 hθ1 hlo hhi hsimple r u,
    sum_sq_strict_root_le hθ0 hθ1 hlo hhi hsimple r v]

/-- **Correlation of adjacent unit degree-weighted kernel rows.** Under the hypotheses of
`le_inner_weightedKernelRow`, the normalized unit rows of adjacent vertices `u ~ v` satisfy
`2 q_{uv} / (1 + q_{uv} ^ 2) - (d / 2) (θ ^ 2) ^ R ≤
  ⟪unitWeightedKernelRow u, unitWeightedKernelRow v⟫`. -/
theorem le_inner_unitWeightedKernelRow {d : ℕ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hlo : ∀ v, 3 ≤ deg v) (hhi : ∀ v, deg v ≤ d)
    (hsimple : ∀ v, (H.neighborSet v).ncard ≤ deg v)
    {R : ℕ} (hR : 1 ≤ R) {u v : V} (huv : H.Adj u v) :
    let q := edgeWeight deg θ u v
    2 * q / (1 + q ^ 2) - (d : ℝ) / 2 * (θ ^ 2) ^ R ≤
      ⟪unitWeightedKernelRow H deg θ R u, unitWeightedKernelRow H deg θ R v⟫ := by
  dsimp only
  have hC := le_inner_weightedKernelRow hθ0 hθ1 hlo hhi hsimple hR huv
  dsimp only at hC
  have hs := one_le_norm_weightedKernelRow (H := H) (deg := deg) (θ := θ) R u
  have ht := one_le_norm_weightedKernelRow (H := H) (deg := deg) (θ := θ) R v
  rw [unitWeightedKernelRow, unitWeightedKernelRow, real_inner_smul_left, real_inner_smul_right,
    ← mul_assoc, ← mul_inv, inv_mul_eq_div]
  set q := edgeWeight deg θ u v
  generalize ⟪weightedKernelRow H deg θ R u, weightedKernelRow H deg θ R v⟫ = C at hC ⊢
  generalize ‖weightedKernelRow H deg θ R u‖ = s at hs hC ⊢
  generalize ‖weightedKernelRow H deg θ R v‖ = t at ht hC ⊢
  have hκ : 0 ≤ 2 * q / (1 + q ^ 2) :=
    div_nonneg (mul_nonneg two_pos.le (edgeWeight_nonneg deg hθ0 u v)) (by positivity)
  have he : 0 ≤ (d : ℝ) / 2 * (θ ^ 2) ^ R := by positivity
  have hamgm : 2 * (s * t) ≤ s ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (s - t)]
  rw [le_div_iff₀ (mul_pos (zero_lt_one.trans_le hs) (zero_lt_one.trans_le ht))]
  linarith only [hC, mul_le_mul_of_nonneg_left hamgm hκ,
    mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hs ht) he]

end FintypeProps

end Kernel

/-! ### Multigraph handshake and limiting degree-pair correlations -/

/-- **Multigraph cycle-excess handshake.** In a finite loopless multigraph where every vertex has
at least one incident edge, `∑_e (1 - 1 / D_{src e} - 1 / D_{tgt e}) = |E| - |V|`. -/
theorem sum_one_sub_inv_deg_eq {V E : Type*} [Fintype V] [Fintype E] {G : Multigraph V E}
    (hl : G.Loopless) (hpos : ∀ v : V, 0 < (G.incidenceSet v).ncard) :
    (∑ e : E, (1 - 1 / ((G.incidenceSet (G.src e)).ncard : ℝ) -
        1 / ((G.incidenceSet (G.tgt e)).ncard : ℝ))) =
      (Fintype.card E : ℝ) - Fintype.card V := by
  have hhand := G.sum_ncard_incidenceSet_mul hl
    fun v => 1 / ((G.incidenceSet v).ncard : ℝ)
  have hV : (∑ v : V, ((G.incidenceSet v).ncard : ℝ) *
        (1 / ((G.incidenceSet v).ncard : ℝ))) = Fintype.card V :=
    calc _ = ∑ _v : V, (1 : ℝ) :=
          Finset.sum_congr rfl fun v _ => mul_one_div_cancel (Nat.cast_ne_zero.mpr (hpos v).ne')
      _ = Fintype.card V := by simp
  rw [Finset.sum_congr rfl fun _ _ => sub_sub _ _ _, Finset.sum_sub_distrib, ← hhand, hV]
  simp

/-- Limiting step factor `1 / (√(√(d₁ - 1)) * √(√(d₂ - 1)))` at `θ = 1` for endpoint degrees
`(d₁, d₂)`. -/
@[expose] noncomputable def pairWeight (d₁ d₂ : ℕ) : ℝ :=
  1 / (√(√((d₁ : ℝ) - 1)) * √(√((d₂ : ℝ) - 1)))

/-- Limiting adjacent unit-row correlation `2 q / (1 + q ^ 2)` at `θ = 1` for endpoint degrees
`(d₁, d₂)`. -/
@[expose] noncomputable def pairCorrelation (d₁ d₂ : ℕ) : ℝ :=
  2 * pairWeight d₁ d₂ / (1 + pairWeight d₁ d₂ ^ 2)

/-- `pairCorrelation` is symmetric in `(d₁, d₂)`. -/
theorem pairCorrelation_comm (d₁ d₂ : ℕ) : pairCorrelation d₁ d₂ = pairCorrelation d₂ d₁ := by
  simp only [pairCorrelation, pairWeight, mul_comm (√(√((d₁ : ℝ) - 1)))]

private theorem pairWeight_le_one {d₁ d₂ : ℕ} (h₁ : 3 ≤ d₁) (h₂ : 3 ≤ d₂) :
    pairWeight d₁ d₂ ≤ 1 := by
  have hs {d : ℕ} (hd : 3 ≤ d) : 1 ≤ √(√((d : ℝ) - 1)) :=
    Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (by linarith [Nat.ofNat_le_cast (α := ℝ).mpr hd]))
  have hprod := one_le_mul_of_one_le_of_one_le (hs h₁) (hs h₂)
  exact (div_le_one (by linarith)).mpr hprod

private theorem pairWeight_nonneg (d₁ d₂ : ℕ) : 0 ≤ pairWeight d₁ d₂ :=
  div_nonneg zero_le_one (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))

private theorem sub_two_mul_div_bounds {q₀ θ : ℝ} (hq0 : 0 ≤ q₀) (hq1 : q₀ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    0 ≤ 2 * q₀ / (1 + q₀ ^ 2) - 2 * (θ * q₀) / (1 + (θ * q₀) ^ 2) ∧
      2 * q₀ / (1 + q₀ ^ 2) - 2 * (θ * q₀) / (1 + (θ * q₀) ^ 2) ≤ 2 * (1 - θ) := by
  set q := θ * q₀
  have hqq₀ : q ≤ q₀ := mul_le_of_le_one_left hq0 hθ1
  have hq_nonneg : 0 ≤ q := mul_nonneg hθ0 hq0
  have hden : (0 : ℝ) < (1 + q₀ ^ 2) * (1 + q ^ 2) := by positivity
  have hnum : 2 * q₀ * (1 + q ^ 2) - (1 + q₀ ^ 2) * (2 * q) =
      2 * (q₀ - q) * (1 - q₀ * q) := by ring
  rw [div_sub_div _ _ (by positivity) (by positivity), hnum]
  refine ⟨div_nonneg (mul_nonneg (by linarith) (by nlinarith)) hden.le, (div_le_iff₀ hden).mpr ?_⟩
  have ha : 2 * (q₀ - q) * (1 - q₀ * q) ≤ 2 * (1 - θ) :=
    (mul_le_of_le_one_right (by linarith) (by nlinarith)).trans (by nlinarith)
  nlinarith [sq_nonneg q₀, sq_nonneg q, mul_nonneg (sq_nonneg q₀) (sq_nonneg q)]

private theorem exists_delta_arccos {α : Type*} (s : Finset α) (g : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ s, ∀ x, dist x (g p) < δ → dist (arccos x) (arccos (g p)) < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun _ hp => absurd hp (Finset.notMem_empty _)⟩
  | @insert a s _ ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.mp
      (continuous_arccos.continuousAt (x := g a)) ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := ih
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun p hp x hx => ?_⟩
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact h₁ (hx.trans_le (min_le_left _ _))
    · exact h₂ p hp x (hx.trans_le (min_le_right _ _))

end WeightedKernel

/-! ### General degree-pair layout theorem -/

open WeightedKernel Cslib.Circuits.Frontier.Gaussian

/-- **Degree-weighted max-product walk kernel layout bound.** For `d ≥ 3` and `A ≥ 0`, if every
degree pair `(d₁, d₂)` with `3 ≤ d₁ ≤ d₂ ≤ d` and `d + 3 ≤ d₁ + d₂` satisfies
`arccos (pairCorrelation d₁ d₂) / π ≤ A (1 - 1 / d₁ - 1 / d₂)`, then `LayoutBound d A` holds. -/
theorem layoutBound_of_weightedKernel {d : ℕ} (hd : 3 ≤ d) {A : ℝ} (hA : 0 ≤ A)
    (hpairs : ∀ d₁ d₂ : ℕ, 3 ≤ d₁ → d₁ ≤ d₂ → d₂ ≤ d → d + 3 ≤ d₁ + d₂ →
      arccos (pairCorrelation d₁ d₂) / π ≤ A * (1 - 1 / (d₁ : ℝ) - 1 / (d₂ : ℝ))) :
    LayoutBound d A := by
  classical
  have hd2 : 2 ≤ d := by omega
  set D : ℝ := (d : ℝ)
  have hD : 3 ≤ D := Nat.ofNat_le_cast.mpr hd
  have hpairs_symm : ∀ d₁ d₂ : ℕ, 3 ≤ d₁ → d₁ ≤ d → 3 ≤ d₂ → d₂ ≤ d → d + 3 ≤ d₁ + d₂ →
      arccos (pairCorrelation d₁ d₂) / π ≤ A * (1 - 1 / (d₁ : ℝ) - 1 / (d₂ : ℝ)) := by
    intro d₁ d₂ h1lo h1hi h2lo h2hi hsum
    rcases le_total d₁ d₂ with hle | hge
    · exact hpairs d₁ d₂ h1lo hle h2hi hsum
    · rw [pairCorrelation_comm]
      exact (hpairs d₂ d₁ h2lo hge h1hi (by omega)).trans_eq (by ring)
  refine LayoutBound.of_saturated hA fun η hη => ?_
  set ξ : ℝ := η / 6
  have hξ : 0 < ξ := by positivity
  let pairSet : Finset (ℕ × ℕ) := Finset.Icc 3 d ×ˢ Finset.Icc 3 d
  obtain ⟨δ, hδ, hcont⟩ := exists_delta_arccos pairSet
    (fun p => pairCorrelation p.1 p.2) (ε := π * ξ) (by positivity)
  set μ : ℝ := min δ 1
  have hμ : 0 < μ := lt_min hδ one_pos
  set θ : ℝ := 1 - μ / 4 with hθ
  have hθ0 : 0 ≤ θ := by linarith [min_le_right δ 1]
  have hθ1 : θ < 1 := by linarith
  have hθsq1 : θ ^ 2 < 1 := by nlinarith
  obtain ⟨R₀, hR₀⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < μ / (2 * D)) hθsq1
  set R : ℕ := R₀ + 1
  have hR1 : 1 ≤ R := Nat.le_add_left 1 R₀
  have hRerr : D / 2 * (θ ^ 2) ^ R < μ / 4 := by
    have : D ≠ 0 := by linarith
    calc D / 2 * (θ ^ 2) ^ R < D / 2 * (μ / (2 * D)) := by
          gcongr
          exact (pow_le_pow_of_le_one (sq_nonneg θ) hθsq1.le (Nat.le_succ R₀)).trans_lt hR₀
      _ = μ / 4 := by field_simp; ring
  obtain ⟨N₀, hN₀⟩ := exists_width_le_of_unitRows_add_mul hd2 R hξ
  refine ⟨N₀, fun V E _ _ G Q hG hQ two big => ?_⟩
  let _ : Fintype Q.blocks := Fintype.ofFinite Q.blocks
  let _ : Fintype Q.external := Fintype.ofFinite Q.external
  set H := Q.quotient
  let degH (u : Q.blocks) : ℕ := (H.incidenceSet u).ncard
  have hlo : ∀ u, 3 ≤ degH u := hQ.three_le_ncard_incidenceSet_quotient hG two
  have hhi : ∀ u, degH u ≤ d := Q.quotient_maxDegreeLE
  let row (u : Q.blocks) : EuclideanSpace ℝ Q.blocks :=
    unitWeightedKernelRow H.toSimpleGraph degH θ R u
  let ρ (e : Q.external) : ℝ :=
    let q := edgeWeight degH θ (H.src e) (H.tgt e)
    2 * q / (1 + q ^ 2) - D / 2 * (θ ^ 2) ^ R
  have hcorr : ∀ e : Q.external, ρ e ≤ ⟪row (H.src e), row (H.tgt e)⟫ := fun e =>
    le_inner_unitWeightedKernelRow hθ0 hθ1 hlo hhi H.ncard_neighborSet_toSimpleGraph_le hR1
      (Multigraph.toSimpleGraph_adj.mpr ⟨Q.quotient_loopless e, e, rfl⟩)
  obtain ⟨σ, hσ⟩ := hN₀ Q.blocks Q.external H hhi big row
    (fun v => norm_unitWeightedKernelRow R v)
    (fun _ _ hz => unitWeightedKernelRow_eq_zero_of_lt hz)
    ρ hcorr
  refine ⟨σ, hσ.trans ?_⟩
  have hedge_le : ∀ e : Q.external,
      arccos (ρ e) / π ≤
        A * (1 - 1 / (degH (H.src e) : ℝ) - 1 / (degH (H.tgt e) : ℝ)) + ξ := by
    intro e
    set d₁ := degH (H.src e)
    set d₂ := degH (H.tgt e)
    have hmem : (d₁, d₂) ∈ pairSet :=
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hlo (H.src e), hhi (H.src e)⟩,
        Finset.mem_Icc.mpr ⟨hlo (H.tgt e), hhi (H.tgt e)⟩⟩
    set q₀ := pairWeight d₁ d₂
    have hq_eq : edgeWeight degH θ (H.src e) (H.tgt e) = θ * q₀ := by
      simp only [edgeWeight, q₀, pairWeight, d₁, d₂]; ring
    obtain ⟨hsub1_nonneg, hsub1⟩ :
        0 ≤ pairCorrelation d₁ d₂ - 2 * (θ * q₀) / (1 + (θ * q₀) ^ 2) ∧
          pairCorrelation d₁ d₂ - 2 * (θ * q₀) / (1 + (θ * q₀) ^ 2) ≤ 2 * (1 - θ) :=
      sub_two_mul_div_bounds (pairWeight_nonneg d₁ d₂)
        (pairWeight_le_one (hlo (H.src e)) (hlo (H.tgt e))) hθ0 hθ1.le
    have hρ_le : ρ e ≤ pairCorrelation d₁ d₂ := by
      have hpos : 0 ≤ D / 2 * (θ ^ 2) ^ R := by positivity
      dsimp only [ρ]
      rw [hq_eq]
      linarith
    have hρ_diff : pairCorrelation d₁ d₂ - ρ e < δ := by
      dsimp only [ρ]
      rw [hq_eq]
      linarith [min_le_left δ 1]
    have harc := hcont (d₁, d₂) hmem (ρ e)
      (by rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]; exact hρ_diff)
    rw [Real.dist_eq] at harc
    have hdiv : arccos (ρ e) / π ≤ arccos (pairCorrelation d₁ d₂) / π + ξ := by
      rw [div_add' _ _ _ pi_pos.ne', div_le_div_iff_of_pos_right pi_pos]
      linarith [(abs_lt.mp harc).2]
    linarith [hpairs_symm d₁ d₂ (hlo (H.src e)) (hhi (H.src e)) (hlo (H.tgt e)) (hhi (H.tgt e))
      (hQ.add_three_le_ncard_incidenceSet_quotient e)]
  have hsum_cross : (∑ e : Q.external, arccos (ρ e) / π) ≤
      A * ((Fintype.card Q.external : ℝ) - Fintype.card Q.blocks) +
        ξ * Fintype.card Q.external := by
    calc (∑ e : Q.external, arccos (ρ e) / π)
        ≤ ∑ e : Q.external,
            (A * (1 - 1 / (degH (H.src e) : ℝ) - 1 / (degH (H.tgt e) : ℝ)) + ξ) :=
          Finset.sum_le_sum fun e _ => hedge_le e
      _ = A * (∑ e : Q.external,
            (1 - 1 / (degH (H.src e) : ℝ) - 1 / (degH (H.tgt e) : ℝ))) +
            ξ * Fintype.card Q.external := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          ring
      _ = A * ((Fintype.card Q.external : ℝ) - Fintype.card Q.blocks) +
            ξ * Fintype.card Q.external := by
          rw [sum_one_sub_inv_deg_eq Q.quotient_loopless fun u => lt_of_lt_of_le (by norm_num)
            (hlo u)]
  have hdiff_le : (Fintype.card Q.external : ℝ) - Fintype.card Q.blocks ≤ G.cycleRank := by
    have hcard := Q.card_add_card_external_le
    have hconn := G.card_le_card_add_one_of_connected hG
    have hβ : Nat.card E + 1 ≤ G.cycleRank + Nat.card V := by grind [Multigraph.cycleRank]
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, sub_le_iff_le_add']
    exact_mod_cast (by omega : Nat.card Q.external ≤ Nat.card Q.blocks + G.cycleRank)
  have ⟨hE3, hV3⟩ := hQ.card_external_and_blocks_le_three_mul_cycleRank hd hG two
  rw [Nat.card_eq_fintype_card] at hE3
  have hξ6 : 6 * ξ = η := by simp only [ξ]; ring
  nlinarith [mul_le_mul_of_nonneg_left hdiff_le hA, mul_le_mul_of_nonneg_left hE3 hξ.le,
    mul_le_mul_of_nonneg_right hV3 hξ.le]

/-! ### Closed-form rational and trigonometric helpers for `d = 4, 5, 6` -/

namespace WeightedKernel

private noncomputable def cosOctUpper (x : ℝ) : ℝ :=
  let t := x / 8
  let c := 1 - 2 * (t - t ^ 3 / 6) ^ 2
  2 * (2 * c ^ 2 - 1) ^ 2 - 1

private theorem arccos_le_of_cosOctUpper {r x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2)
    (hr : cosOctUpper x ≤ r) : arccos r ≤ x := by
  have ht : 0 ≤ x / 8 := by linarith
  have ht0 : 0 ≤ x / 8 - (x / 8) ^ 3 / 6 := by nlinarith [sq_nonneg (x / 8)]
  have hc0 : cos (2 * (x / 8)) ≤ 1 - 2 * (x / 8 - (x / 8) ^ 3 / 6) ^ 2 := by
    rw [cos_two_mul']
    linarith [pow_le_pow_left₀ ht0 (sin_ge_sub_cube ht) 2, sin_sq_add_cos_sq (x / 8)]
  have hc1 := cos_two_mul_le (by nlinarith) hc0 le_rfl
  have hx8 : x = 2 * (2 * (2 * (x / 8))) := by ring
  have hc2 : cos x ≤ cosOctUpper x := by
    conv_lhs => rw [hx8]
    exact cos_two_mul_le (by nlinarith) hc1 le_rfl
  exact (arccos_le_arccos (hc2.trans hr)).trans_eq (arccos_cos hx0 (by linarith [pi_gt_three]))

private noncomputable def cosQuarLower (x : ℝ) : ℝ :=
  let t := x / 4
  let c := 1 - 2 * (t - t ^ 3 / 6 + t ^ 5 / 100) ^ 2
  2 * c ^ 2 - 1

private theorem le_arccos_of_cosQuarLower {r x : ℝ} (hx0 : 0 ≤ x) (hx3 : x ≤ 3)
    (hc0 : 0 ≤ 1 - 2 * ((x / 4) - (x / 4) ^ 3 / 6 + (x / 4) ^ 5 / 100) ^ 2)
    (hr : r ≤ cosQuarLower x) : x ≤ arccos r := by
  have ht0 : 0 ≤ x / 4 := by linarith
  have hb := sin_bound (x := x / 4) (by rw [abs_of_nonneg ht0]; linarith)
  rw [abs_of_nonneg ht0] at hb
  have hsin : sin (x / 4) ≤ x / 4 - (x / 4) ^ 3 / 6 + (x / 4) ^ 5 / 100 := by
    linarith [(abs_le.mp hb).2]
  have hsin0 : 0 ≤ sin (x / 4) := sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [pi_gt_three])
  have hc1 : 1 - 2 * (x / 4 - (x / 4) ^ 3 / 6 + (x / 4) ^ 5 / 100) ^ 2 ≤ cos (2 * (x / 4)) := by
    rw [cos_two_mul']
    linarith [pow_le_pow_left₀ hsin0 hsin 2, sin_sq_add_cos_sq (x / 4)]
  have hx4 : x = 2 * (2 * (x / 4)) := by ring
  have hc2 : cosQuarLower x ≤ cos x := by
    rw [cosQuarLower, hx4, cos_two_mul]
    linarith [pow_le_pow_left₀ hc0 hc1 2]
  exact (arccos_cos hx0 (by linarith [pi_gt_three])).symm.trans_le (arccos_le_arccos (hr.trans hc2))

/-- Rational lower-bound certificate for `pairCorrelation d₁ d₂ = 2 √(√p) / (√p + 1)` where
`p = (d₁ - 1)(d₂ - 1)`. -/
private theorem lt_pairCorrelation_of_bounds {d₁ d₂ : ℕ} (hd₁ : 3 ≤ d₁) (hd₂ : 3 ≤ d₂)
    {u r_hi s_lo : ℝ} (hs : 0 < s_lo) (hr : 0 < r_hi)
    (h1 : ((d₁ : ℝ) - 1) * ((d₂ : ℝ) - 1) < r_hi ^ 2)
    (h2 : s_lo ^ 4 < ((d₁ : ℝ) - 1) * ((d₂ : ℝ) - 1))
    (h3 : u * (r_hi + 1) < 2 * s_lo) : u < pairCorrelation d₁ d₂ := by
  set a : ℝ := (d₁ : ℝ) - 1
  set b : ℝ := (d₂ : ℝ) - 1
  have ha : 0 < a := by linarith [Nat.ofNat_le_cast (α := ℝ).mpr hd₁]
  have hb : 0 < b := by linarith [Nat.ofNat_le_cast (α := ℝ).mpr hd₂]
  set p : ℝ := a * b
  have hp : 0 < p := mul_pos ha hb
  have hs_eq : √(√a) * √(√b) = √(√p) := by
    rw [← sqrt_mul (sqrt_nonneg a), ← sqrt_mul ha.le]
  have hs_pos : 0 < √(√p) := by positivity
  have hcorr_eq : pairCorrelation d₁ d₂ = 2 * √(√p) / (√p + 1) := by
    rw [pairCorrelation, pairWeight, hs_eq, div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    nlinarith [sq_sqrt (sqrt_nonneg p)]
  rw [hcorr_eq, lt_div_iff₀ (by positivity)]
  have hr_lt : √p < r_hi := (sqrt_lt' hr).mpr h1
  have hs_lt : s_lo < √(√p) :=
    (lt_sqrt hs.le).mpr ((lt_sqrt (sq_nonneg s_lo)).mpr (pow_mul s_lo 2 2 ▸ h2))
  by_cases hu0 : 0 ≤ u
  · linarith [mul_le_mul_of_nonneg_left hr_lt.le hu0]
  · linarith [mul_neg_of_neg_of_pos (not_le.mp hu0) (by positivity : 0 < √p + 1)]

private theorem arccos_pairCorrelation_le {d₁ d₂ : ℕ} (hd₁ : 3 ≤ d₁) (hd₂ : 3 ≤ d₂)
    {x r_hi s_lo : ℝ}
    (hcert : 0 ≤ x ∧ x ≤ 2 ∧ 0 < s_lo ∧ 0 < r_hi ∧
      ((d₁ : ℝ) - 1) * ((d₂ : ℝ) - 1) < r_hi ^ 2 ∧
      s_lo ^ 4 < ((d₁ : ℝ) - 1) * ((d₂ : ℝ) - 1) ∧
      cosOctUpper x * (r_hi + 1) < 2 * s_lo) :
    arccos (pairCorrelation d₁ d₂) ≤ x :=
  let ⟨hx0, hx2, hs, hr, h1, h2, h3⟩ := hcert
  arccos_le_of_cosOctUpper hx0 hx2 (lt_pairCorrelation_of_bounds hd₁ hd₂ hs hr h1 h2 h3).le

/-- Diagonal evaluation: `pairCorrelation d d = Gaussian.vertexCorrelation d` for `d ≥ 1`. -/
theorem pairCorrelation_self {d : ℕ} (hd : 1 ≤ d) :
    pairCorrelation d d = Gaussian.vertexCorrelation d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : √((d : ℝ) - 1) ^ 2 = (d : ℝ) - 1 := sq_sqrt (by linarith)
  rw [pairCorrelation, pairWeight, Gaussian.vertexCorrelation, mul_self_sqrt (sqrt_nonneg _)]
  rcases eq_or_lt_of_le hd with rfl | h1
  · norm_num
  · have hne : √((d : ℝ) - 1) ≠ 0 :=
      (sqrt_pos.mpr (by linarith [Nat.ofNat_le_cast (α := ℝ).mpr h1])).ne'
    field_simp
    nlinarith [hs]

/-- At `(4, 4)`, `pairCorrelation 4 4 = √3 / 2 = cos (π / 6)`. -/
theorem pairCorrelation_four_four : pairCorrelation 4 4 = cos (π / 6) := by
  rw [pairCorrelation_self (by norm_num), Gaussian.vertexCorrelation, cos_pi_div_six]
  norm_num
  ring

/-- At `(5, 5)`, `pairCorrelation 5 5 = 4 / 5`. -/
theorem pairCorrelation_five_five : pairCorrelation 5 5 = 4 / 5 := by
  have h4 : ((5 : ℕ) : ℝ) - 1 = 2 ^ 2 := by norm_num
  rw [pairCorrelation_self (by norm_num), Gaussian.vertexCorrelation, h4, sqrt_sq zero_le_two]
  norm_num

/-- At `(6, 6)`, `pairCorrelation 6 6 = √5 / 3`. -/
theorem pairCorrelation_six_six : pairCorrelation 6 6 = √5 / 3 := by
  rw [pairCorrelation_self (by norm_num), Gaussian.vertexCorrelation]
  norm_num
  ring

private theorem arccos_pairCorrelation_three_four_le :
    arccos (pairCorrelation 3 4) / π ≤ 5 / 36 := by
  have harc : arccos (pairCorrelation 3 4) ≤ 157075 / 360000 :=
    arccos_pairCorrelation_le (by norm_num) (by norm_num)
      (s_lo := 39127 / 25000) (r_hi := 244949 / 100000) (by dsimp only [cosOctUpper]; norm_num)
  rw [div_le_iff₀ pi_pos]
  linarith [pi_gt_d4]

private theorem le_arccos_four_fifths : (3217 / 5000 : ℝ) ≤ arccos (4 / 5) :=
  le_arccos_of_cosQuarLower (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [cosQuarLower]; norm_num)

private theorem arccos_four_fifths_le : arccos (4 / 5) ≤ 64351 / 100000 :=
  arccos_le_of_cosOctUpper (by norm_num) (by norm_num) (by dsimp only [cosOctUpper]; norm_num)

private theorem arccos_pairCorrelation_four_five_le :
    arccos (pairCorrelation 4 5) ≤ 35387 / 60000 :=
  arccos_pairCorrelation_le (by norm_num) (by norm_num)
    (s_lo := 4653 / 2500) (r_hi := 346411 / 100000) (by dsimp only [cosOctUpper]; norm_num)

private theorem arccos_pairCorrelation_three_five_le :
    arccos (pairCorrelation 3 5) ≤ 22519 / 45000 :=
  arccos_pairCorrelation_le (by norm_num) (by norm_num)
    (s_lo := 168179 / 100000) (r_hi := 282843 / 100000) (by dsimp only [cosOctUpper]; norm_num)

/-- The exact degree-five layout coefficient `(5 / 3) arccos (4 / 5) / π ≈ 0.341388`. -/
@[expose] noncomputable def fiveCoefficient : ℝ :=
  5 / 3 * arccos (4 / 5) / π

/-- `fiveCoefficient` is strictly positive. -/
theorem fiveCoefficient_pos : 0 < fiveCoefficient :=
  div_pos (mul_pos (by norm_num) (arccos_pos.mpr (by norm_num))) pi_pos

/-- Closed-form circuit lower-bound coefficient `1 + 1 / fiveCoefficient`. -/
theorem one_add_inv_fiveCoefficient :
    1 + 1 / fiveCoefficient = 1 + 3 * π / (5 * arccos (4 / 5)) := by
  have ha : 0 < arccos (4 / 5) := arccos_pos.mpr (by norm_num)
  unfold fiveCoefficient
  field_simp

/-- Rational lower bound `3929 / 1000 ≤ 1 + 3 π / (5 arccos (4 / 5)) ≈ 3.929219`. -/
theorem fiveCircuitCoefficient_ge_3929 :
    (3929 / 1000 : ℝ) ≤ 1 + 3 * π / (5 * arccos (4 / 5)) := by
  have ha : 0 < arccos (4 / 5) := arccos_pos.mpr (by norm_num)
  rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
  linarith [pi_gt_d6, arccos_four_fifths_le]

private theorem le_arccos_sqrt_five_div_three : (7297 / 10000 : ℝ) ≤ arccos (√5 / 3) := by
  have hs5 : √5 < 3 * (931710513 / 1250000000 : ℝ) :=
    (sqrt_lt' (by norm_num)).mpr (by norm_num)
  refine le_arccos_of_cosQuarLower (by norm_num) (by norm_num) (by norm_num) ?_
  dsimp only [cosQuarLower]; linarith

private theorem arccos_sqrt_five_div_three_le : arccos (√5 / 3) ≤ 72973 / 100000 := by
  have hs5 : 3 * (3726777277 / 5000000000 : ℝ) < √5 :=
    (lt_sqrt (by norm_num)).mpr (by norm_num)
  refine arccos_le_of_cosOctUpper (by norm_num) (by norm_num) ?_
  dsimp only [cosOctUpper]; linarith

private theorem arccos_pairCorrelation_five_six_le :
    arccos (pairCorrelation 5 6) ≤ 138643 / 200000 :=
  arccos_pairCorrelation_le (by norm_num) (by norm_num)
    (s_lo := 105737 / 50000) (r_hi := 223607 / 50000) (by dsimp only [cosOctUpper]; norm_num)

private theorem arccos_pairCorrelation_four_six_le :
    arccos (pairCorrelation 4 6) ≤ 51079 / 80000 :=
  arccos_pairCorrelation_le (by norm_num) (by norm_num)
    (s_lo := 98399 / 50000) (r_hi := 387299 / 100000) (by dsimp only [cosOctUpper]; norm_num)

private theorem arccos_pairCorrelation_three_six_le :
    arccos (pairCorrelation 3 6) ≤ 21891 / 40000 :=
  arccos_pairCorrelation_le (by norm_num) (by norm_num)
    (s_lo := 177827 / 100000) (r_hi := 79057 / 25000) (by dsimp only [cosOctUpper]; norm_num)

/-- The exact degree-six layout coefficient `(3 / 2) arccos (√5 / 3) / π ≈ 0.348419`. -/
@[expose] noncomputable def sixCoefficient : ℝ :=
  3 / 2 * arccos (√5 / 3) / π

/-- `sixCoefficient` is strictly positive. -/
theorem sixCoefficient_pos : 0 < sixCoefficient := by
  have ha : 0 < arccos (√5 / 3) := by linarith [le_arccos_sqrt_five_div_three]
  exact div_pos (mul_pos (by norm_num) ha) pi_pos

/-- Closed-form circuit lower-bound coefficient `1 + 1 / sixCoefficient`. -/
theorem one_add_inv_sixCoefficient :
    1 + 1 / sixCoefficient = 1 + 2 * π / (3 * arccos (√5 / 3)) := by
  have ha : 0 < arccos (√5 / 3) := by linarith [le_arccos_sqrt_five_div_three]
  unfold sixCoefficient
  field_simp

/-- Rational lower bound `387 / 100 ≤ 1 + 2 π / (3 arccos (√5 / 3)) ≈ 3.870105`. -/
theorem sixCircuitCoefficient_ge_387 :
    (387 / 100 : ℝ) ≤ 1 + 2 * π / (3 * arccos (√5 / 3)) := by
  have ha : 0 < arccos (√5 / 3) := by linarith [le_arccos_sqrt_five_div_three]
  rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
  linarith [pi_gt_d6, arccos_sqrt_five_div_three_le]

end WeightedKernel

/-! ### Closed-form `LayoutBound` instances for maximum degrees `4`, `5`, and `6` -/

/-- **Degree-four layout bound `1 / 3`.** Connected loopless multigraphs of maximum degree four
have layouts of width `(1 / 3 + o(1)) β₁ + o(|V|)`: `(4, 4)` edges meet `1 / 3` with equality and
`(3, 4)` edges have strictly smaller normalized crossing probability. -/
theorem layoutBound_four_one_third : LayoutBound 4 (1 / 3) := by
  refine layoutBound_of_weightedKernel (by norm_num) (by norm_num) fun d₁ d₂ h1 h12 h2 hsum => ?_
  rcases (by omega : (d₁ = 3 ∧ d₂ = 4) ∨ (d₁ = 4 ∧ d₂ = 4)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact arccos_pairCorrelation_three_four_le.trans_eq (by push_cast; norm_num)
  · rw [pairCorrelation_four_four, arccos_cos (by positivity) (by linarith [pi_pos])]
    push_cast; field_simp; norm_num

/-- **Degree-five weighted layout bound.** Connected loopless multigraphs of maximum degree five
have layouts of width `(fiveCoefficient + o(1)) β₁ + o(|V|)`, where
`fiveCoefficient = (5 / 3) arccos (4 / 5) / π ≈ 0.341388`. -/
theorem layoutBound_five_weighted : LayoutBound 5 WeightedKernel.fiveCoefficient := by
  refine layoutBound_of_weightedKernel (by norm_num) WeightedKernel.fiveCoefficient_pos.le
    fun d₁ d₂ h1 h12 h2 hsum => ?_
  unfold WeightedKernel.fiveCoefficient
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ pi_pos.le
  have ha5 := WeightedKernel.le_arccos_four_fifths
  rcases (by omega : (d₁ = 4 ∧ d₂ = 4) ∨ (d₁ = 3 ∧ d₂ = 5) ∨ (d₁ = 4 ∧ d₂ = 5) ∨
      (d₁ = 5 ∧ d₂ = 5)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [pairCorrelation_four_four, arccos_cos (by positivity) (by linarith [pi_pos])]
    push_cast; linarith [pi_lt_d4]
  · push_cast; linarith [WeightedKernel.arccos_pairCorrelation_three_five_le]
  · push_cast; linarith [WeightedKernel.arccos_pairCorrelation_four_five_le]
  · rw [pairCorrelation_five_five]; push_cast; linarith

/-- **Degree-six weighted layout bound.** Connected loopless multigraphs of maximum degree six
have layouts of width `(sixCoefficient + o(1)) β₁ + o(|V|)`, where
`sixCoefficient = (3 / 2) arccos (√5 / 3) / π ≈ 0.348419`. -/
theorem layoutBound_six_weighted : LayoutBound 6 WeightedKernel.sixCoefficient := by
  refine layoutBound_of_weightedKernel (by norm_num) WeightedKernel.sixCoefficient_pos.le
    fun d₁ d₂ h1 h12 h2 hsum => ?_
  unfold WeightedKernel.sixCoefficient
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ pi_pos.le
  have ha6 := WeightedKernel.le_arccos_sqrt_five_div_three
  rcases (by omega : (d₁ = 4 ∧ d₂ = 5) ∨ (d₁ = 3 ∧ d₂ = 6) ∨ (d₁ = 4 ∧ d₂ = 6) ∨
      (d₁ = 5 ∧ d₂ = 5) ∨ (d₁ = 5 ∧ d₂ = 6) ∨ (d₁ = 6 ∧ d₂ = 6)) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · push_cast; linarith [WeightedKernel.arccos_pairCorrelation_four_five_le]
  · push_cast; linarith [WeightedKernel.arccos_pairCorrelation_three_six_le]
  · push_cast; linarith [WeightedKernel.arccos_pairCorrelation_four_six_le]
  · rw [pairCorrelation_five_five]; push_cast; linarith [WeightedKernel.arccos_four_fifths_le]
  · push_cast; linarith [WeightedKernel.arccos_pairCorrelation_five_six_le]
  · rw [pairCorrelation_six_six]; push_cast; linarith

end Cslib.Circuits.Frontier
