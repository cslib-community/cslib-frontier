/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/Deriv.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.NormNum

/-!
# First-order conditions for convex functions on normed spaces

A convex function lies above its tangent hyperplanes: if `f` is convex on `K` and differentiable
within `K` at `x ∈ K` with derivative `f'`, then `f x + f' (y - x) ≤ f y` for `y ∈ K` (strictly
when `f` is strictly convex and `y ≠ x`). In a
Hilbert space with gradient `g` this reads `f x + ⟪g, y - x⟫ ≤ f y`, so the gradient is a
subgradient relative to `K`. For `m`-strongly convex functions the bound improves by
`m / 2 * ‖y - x‖ ^ 2`. Mathlib proves
the one-dimensional statements (`ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` and its relatives);
here they are lifted along the segment `s ↦ x + s • (y - x)`.

These are the forms of convexity and strong convexity assumed by online convex optimization
([Hazan2022] §2.1).

## Main results

* `ConvexOn.add_le_of_hasFDerivWithinAt`: the tangent-hyperplane inequality on a real normed
  space, for a derivative within `K` (so boundary points of `K` are allowed);
  `ConvexOn.add_le_of_hasFDerivAt` is the special case of a full derivative, and
  `StrictConvexOn.add_lt_of_hasFDerivWithinAt` / `StrictConvexOn.add_lt_of_hasFDerivAt` are the
  strict inequalities for strictly convex functions.
  `ConcaveOn.le_add_mul_of_hasDerivWithinAt` gives the one-dimensional concave form
  `f y ≤ f x + d * (y - x)`.
* `ConvexOn.add_inner_le_of_hasGradientWithinAt`, `ConvexOn.add_inner_le_of_hasGradientAt`: the
  gradient form in a Hilbert space.
* `StrongConvexOn.add_inner_add_le_of_hasGradientWithinAt`,
  `StrongConvexOn.add_inner_add_le_of_hasGradientAt`: the strongly convex gradient form
  `f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y`.
* `convexOn_of_forall_add_le`, `strictConvexOn_of_forall_add_lt`,
  `convexOn_of_forall_add_inner_le`: conversely, a function with a (strict) subgradient relative
  to `K` at every point of `K` is (strictly) convex on `K`.
* `abs_sub_le_of_forall_add_inner_le`: subgradients of norm at most `ρ` make the function
  `ρ`-Lipschitz on `K`.
* `hasDerivWithinAt_nonpos_of_eventually_le`, `eventually_add_mul_nonneg_nhdsGE`,
  `eventually_add_mul_le_nhdsGE`: first-order right-derivative optimality and feasible boundary-ray
  helpers on `[0, ∞)` (used for KKT multiplier extraction on polyhedral domains).

## References

* [Hazan2022]
-/

public section

open Filter Set
open scoped RealInnerProductSpace Topology

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set F} {f : F → ℝ}

/-- A convex function lies above its tangent hyperplane at any point where it is differentiable
within its domain: `f x + f' (y - x) ≤ f y` for `x y ∈ K`. -/
theorem ConvexOn.add_le_of_hasFDerivWithinAt (hf : ConvexOn ℝ K f) {x y : F} {f' : F →L[ℝ] ℝ}
    (hx : x ∈ K) (hy : y ∈ K) (hd : HasFDerivWithinAt f f' K x) :
    f x + f' (y - x) ≤ f y := by
  set φ : ℝ → F := fun s => x + s • (y - x) with hφ
  have hφK : MapsTo φ (Icc 0 1) K := fun s hs => by
    convert hf.1 hx hy (sub_nonneg.mpr hs.2) hs.1 (by ring) using 1
    simp only [hφ]
    module
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) (f ∘ φ) := ⟨convex_Icc 0 1,
    fun a ha b hb p q hp hq hpq => by
      have hφab : φ (p • a + q • b) = p • φ a + q • φ b := by
        simp only [hφ, show q = 1 - p by linarith]
        module
      simpa only [Function.comp_apply, hφab] using hf.2 (hφK ha) (hφK hb) hp hq hpq⟩
  have hder : HasDerivWithinAt (f ∘ φ) (f' (y - x)) (Icc 0 1) 0 :=
    (by simpa only [hφ, zero_smul, add_zero] using hd : HasFDerivWithinAt f f' K (φ 0))
      |>.comp_hasDerivWithinAt 0
      (by simpa only [one_smul, hφ, id] using
        (((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x).hasDerivWithinAt) hφK
  have h := hconv.le_slope_of_hasDerivWithinAt_Ioi (by simp) (by simp) zero_lt_one
    (hder.mono_of_mem_nhdsWithin (Icc_mem_nhdsGT zero_lt_one))
  simp only [slope_def_field, Function.comp_apply, hφ, zero_smul, add_zero, one_smul,
    add_sub_cancel, sub_zero, div_one] at h
  linarith

/-- A convex function lies above its tangent hyperplane at any point of differentiability:
`f x + f' (y - x) ≤ f y` for `x y ∈ K`. -/
theorem ConvexOn.add_le_of_hasFDerivAt (hf : ConvexOn ℝ K f) {x y : F} {f' : F →L[ℝ] ℝ}
    (hx : x ∈ K) (hy : y ∈ K) (hd : HasFDerivAt f f' x) :
    f x + f' (y - x) ≤ f y :=
  hf.add_le_of_hasFDerivWithinAt hx hy hd.hasFDerivWithinAt

/-- A concave function on `ℝ` lies below its tangent line at any point where it is differentiable
within its domain: `f y ≤ f x + d * (y - x)` for `x y ∈ K`. -/
theorem ConcaveOn.le_add_mul_of_hasDerivWithinAt {K : Set ℝ} {f : ℝ → ℝ} {x y d : ℝ}
    (hf : ConcaveOn ℝ K f) (hx : x ∈ K) (hy : y ∈ K) (hd : HasDerivWithinAt f d K x) :
    f y ≤ f x + d * (y - x) := by
  have h := hf.neg.add_le_of_hasFDerivWithinAt hx hy hd.neg.hasFDerivWithinAt
  simp only [Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
  linarith

/-- Conversely, a function with a subgradient relative to `K` at every point of a convex set `K`
is convex on `K`: if `f x + g x (y - x) ≤ f y` for all `x y ∈ K`, then `f` is convex on `K`. -/
theorem convexOn_of_forall_add_le (hK : Convex ℝ K) {g : F → F →L[ℝ] ℝ}
    (hsub : ∀ x ∈ K, ∀ y ∈ K, f x + g x (y - x) ≤ f y) : ConvexOn ℝ K f := by
  refine ⟨hK, fun x hx y hy a b ha hb hab => ?_⟩
  set p := a • x + b • y
  have hp : p ∈ K := hK hx hy ha hb hab
  have h0 : a • (x - p) + b • (y - p) = 0 := by
    simp only [smul_sub, p, show b = 1 - a by linarith]
    module
  have hlin : a * g p (x - p) + b * g p (y - p) = 0 := by
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add, h0, map_zero]
  have e1 := mul_le_mul_of_nonneg_left (hsub p hp x hx) ha
  have e2 := mul_le_mul_of_nonneg_left (hsub p hp y hy) hb
  simp only [smul_eq_mul]
  linarith [show f p = a * f p + b * f p by rw [← add_mul, hab, one_mul]]

/-- A strictly convex function lies strictly above its tangent hyperplane at any point where it is
differentiable within its domain: `f x + f' (y - x) < f y` for `x y ∈ K` with `y ≠ x`. -/
theorem StrictConvexOn.add_lt_of_hasFDerivWithinAt (hf : StrictConvexOn ℝ K f) {x y : F}
    {f' : F →L[ℝ] ℝ} (hx : x ∈ K) (hy : y ∈ K) (hxy : y ≠ x)
    (hd : HasFDerivWithinAt f f' K x) :
    f x + f' (y - x) < f y := by
  set m : F := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hm : m ∈ K := hf.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have hmid : f m < (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f y := by
    simpa only [smul_eq_mul] using
      hf.2 hx hy hxy.symm (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num)
  have hsub := hf.convexOn.add_le_of_hasFDerivWithinAt hx hm hd
  have hdiff : m - x = (1 / 2 : ℝ) • (y - x) := by
    simp only [m]
    module
  rw [hdiff, map_smul, smul_eq_mul] at hsub
  linarith

/-- A strictly convex function lies strictly above its tangent hyperplane at any point of
differentiability: `f x + f' (y - x) < f y` for `x y ∈ K` with `y ≠ x`. -/
theorem StrictConvexOn.add_lt_of_hasFDerivAt (hf : StrictConvexOn ℝ K f) {x y : F}
    {f' : F →L[ℝ] ℝ} (hx : x ∈ K) (hy : y ∈ K) (hxy : y ≠ x) (hd : HasFDerivAt f f' x) :
    f x + f' (y - x) < f y :=
  hf.add_lt_of_hasFDerivWithinAt hx hy hxy hd.hasFDerivWithinAt

/-- Conversely, a function with a strict subgradient relative to `K` at every point of a convex set
`K` is strictly convex on `K`: if `f x + g x (y - x) < f y` for all `x y ∈ K` with `y ≠ x`, then
`f` is strictly convex on `K`. -/
theorem strictConvexOn_of_forall_add_lt (hK : Convex ℝ K) {g : F → F →L[ℝ] ℝ}
    (hsub : ∀ x ∈ K, ∀ y ∈ K, y ≠ x → f x + g x (y - x) < f y) : StrictConvexOn ℝ K f := by
  refine ⟨hK, fun x hx y hy hxy a b ha hb hab => ?_⟩
  set p := a • x + b • y
  have hp : p ∈ K := hK hx hy ha.le hb.le hab
  have hxp : x ≠ p := fun h => by
    have hp' : p - x = b • (y - x) := by
      simp only [p, show a = 1 - b by linarith]
      module
    have h0 : b • (y - x) = 0 := by rw [← hp', h, sub_self]
    exact hxy (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_left hb.ne')).symm
  have hyp : y ≠ p := fun h => by
    have hp' : p - y = a • (x - y) := by
      simp only [p, show b = 1 - a by linarith]
      module
    have h0 : a • (x - y) = 0 := by rw [← hp', h, sub_self]
    exact hxy (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_left ha.ne'))
  have h0 : a • (x - p) + b • (y - p) = 0 := by
    simp only [smul_sub, p, show b = 1 - a by linarith]
    module
  have hlin : a * g p (x - p) + b * g p (y - p) = 0 := by
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add, h0, map_zero]
  have e1 := mul_lt_mul_of_pos_left (hsub p hp x hx hxp) ha
  have e2 := mul_lt_mul_of_pos_left (hsub p hp y hy hyp) hb
  simp only [smul_eq_mul]
  linarith [show f p = a * f p + b * f p by rw [← add_mul, hab, one_mul]]

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {K : Set E} {f : E → ℝ}

/-- The gradient of a convex function within its domain is a subgradient relative to the domain:
`f x + ⟪g, y - x⟫ ≤ f y` for `x y ∈ K`. -/
theorem ConvexOn.add_inner_le_of_hasGradientWithinAt (hf : ConvexOn ℝ K f) {x y g : E}
    (hx : x ∈ K) (hy : y ∈ K) (hg : HasGradientWithinAt f g K x) :
    f x + ⟪g, y - x⟫ ≤ f y := by
  simpa only [InnerProductSpace.toDual_apply_apply] using
    hf.add_le_of_hasFDerivWithinAt hx hy hg.hasFDerivWithinAt

/-- The gradient of a convex function is a subgradient relative to its domain:
`f x + ⟪g, y - x⟫ ≤ f y` for `x y ∈ K`. -/
theorem ConvexOn.add_inner_le_of_hasGradientAt (hf : ConvexOn ℝ K f) {x y g : E} (hx : x ∈ K)
    (hy : y ∈ K) (hg : HasGradientAt f g x) :
    f x + ⟪g, y - x⟫ ≤ f y :=
  hf.add_inner_le_of_hasGradientWithinAt hx hy
    (hasGradientWithinAt_iff_hasFDerivWithinAt.mpr hg.hasFDerivAt.hasFDerivWithinAt)

omit [CompleteSpace E] in
/-- Conversely, a function with a subgradient relative to `K` at every point of a convex set `K`
is convex on `K`: if `f x + ⟪g x, y - x⟫ ≤ f y` for all `x y ∈ K`, then `f` is convex on `K`. -/
theorem convexOn_of_forall_add_inner_le (hK : Convex ℝ K) {g : E → E}
    (hsub : ∀ x ∈ K, ∀ y ∈ K, f x + ⟪g x, y - x⟫ ≤ f y) : ConvexOn ℝ K f :=
  convexOn_of_forall_add_le (g := fun x => innerSL ℝ (g x)) hK fun x hx y hy => by
    simpa only [innerSL_apply_apply] using hsub x hx y hy

omit [CompleteSpace E] in
/-- Bounded subgradients make a function Lipschitz: if `f x + ⟪g x, y - x⟫ ≤ f y` for `x y ∈ K`
and `‖g x‖ ≤ ρ` on `K`, then `|f x - f y| ≤ ρ * ‖x - y‖` for `x y ∈ K`. -/
theorem abs_sub_le_of_forall_add_inner_le {g : E → E} {ρ : ℝ}
    (hsub : ∀ x ∈ K, ∀ y ∈ K, f x + ⟪g x, y - x⟫ ≤ f y) (hg : ∀ x ∈ K, ‖g x‖ ≤ ρ) {x y : E}
    (hx : x ∈ K) (hy : y ∈ K) : |f x - f y| ≤ ρ * ‖x - y‖ := by
  have b1 : |⟪g x, y - x⟫| ≤ ρ * ‖x - y‖ := norm_sub_rev x y ▸
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hg x hx) (norm_nonneg _))
  have b2 : |⟪g y, x - y⟫| ≤ ρ * ‖x - y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hg y hy) (norm_nonneg _))
  rw [abs_le] at b1 b2 ⊢
  refine ⟨?_, ?_⟩
  · linarith [hsub y hy x hx]
  · linarith [hsub x hx y hy]

/-- The first-order bound for an `m`-strongly convex function with a gradient within its domain:
`f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for `x y ∈ K`. -/
theorem StrongConvexOn.add_inner_add_le_of_hasGradientWithinAt {m : ℝ}
    (hf : StrongConvexOn K m f) {x y g : E} (hx : x ∈ K) (hy : y ∈ K)
    (hg : HasGradientWithinAt f g K x) :
    f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hd := hg.hasFDerivWithinAt.sub
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.hasFDerivWithinAt.const_mul (m / 2))
  have h := (strongConvexOn_iff_convex.mp hf).add_le_of_hasFDerivWithinAt hx hy hd
  simp only [sub_apply, smul_apply, InnerProductSpace.toDual_apply_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at h
  rw [norm_sub_sq_real]
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at h ⊢
  rw [real_inner_comm x y]
  linarith

/-- The first-order bound for an `m`-strongly convex function:
`f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for `x y ∈ K`. -/
theorem StrongConvexOn.add_inner_add_le_of_hasGradientAt {m : ℝ} (hf : StrongConvexOn K m f)
    {x y g : E} (hx : x ∈ K) (hy : y ∈ K) (hg : HasGradientAt f g x) :
    f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y :=
  hf.add_inner_add_le_of_hasGradientWithinAt hx hy
    (hasGradientWithinAt_iff_hasFDerivWithinAt.mpr hg.hasFDerivAt.hasFDerivWithinAt)

end InnerProduct

section RightBoundary

/-- First-order directional derivative nonpositivity for a right-differentiable function at a local
maximum on `[0, ∞)`: if `φ` has right derivative `d` at `0` within `[0, ∞)` and `φ t ≤ φ 0`
eventually as `t → 0⁺`, then `d ≤ 0`. -/
theorem hasDerivWithinAt_nonpos_of_eventually_le {φ : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivWithinAt φ d (Ici 0) 0) (hmax : ∀ᶠ t in 𝓝[≥] (0 : ℝ), φ t ≤ φ 0) :
    d ≤ 0 := by
  have hlim : Tendsto (slope φ 0) (𝓝[>] 0) (𝓝 d) := by
    have h1 := hasDerivWithinAt_iff_tendsto_slope.1 (hd.mono Ioi_subset_Ici_self)
    simpa only [Set.sdiff_singleton_eq_self (notMem_Ioi.2 le_rfl)] using h1
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope φ 0 t ≤ 0 := by
    filter_upwards [hmax.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self),
      self_mem_nhdsWithin] with t ht hpos
    rw [slope_def_field, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ht) (mem_Ioi.1 hpos).le
  exact le_of_tendsto hlim hle

/-- If `a ≥ 0` and any boundary point `a = 0` moves inward (`b ≥ 0`), then `0 ≤ a + t * b` holds
eventually as `t → 0⁺`. -/
theorem eventually_add_mul_nonneg_nhdsGE {a b : ℝ} (ha : 0 ≤ a) (hb : a = 0 → 0 ≤ b) :
    ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ a + t * b := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← ha0, zero_add]
    exact mul_nonneg (mem_Ici.1 ht) (hb ha0.symm)
  · have hcont : ContinuousAt (fun t : ℝ => a + t * b) 0 :=
      continuousAt_const.add (continuousAt_id.mul continuousAt_const)
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < a + t * b :=
      hcont.eventually (show Ioi (0 : ℝ) ∈ 𝓝 (a + 0 * b) by
        simpa only [zero_mul, add_zero] using Ioi_mem_nhds hapos)
    exact (hmem.filter_mono nhdsWithin_le_nhds).mono fun _ ht => ht.le

/-- If `a ≤ c` and any tight point `a = c` moves weakly downward (`b ≤ 0`), then `a + t * b ≤ c`
holds eventually as `t → 0⁺`. -/
theorem eventually_add_mul_le_nhdsGE {a b c : ℝ} (hac : a ≤ c) (hb : a = c → b ≤ 0) :
    ∀ᶠ t in 𝓝[≥] (0 : ℝ), a + t * b ≤ c := by
  have h := eventually_add_mul_nonneg_nhdsGE (a := c - a) (b := -b) (sub_nonneg.2 hac)
    fun h0 => neg_nonneg.2 (hb (by linarith))
  exact h.mono fun t ht => by linarith

end RightBoundary
