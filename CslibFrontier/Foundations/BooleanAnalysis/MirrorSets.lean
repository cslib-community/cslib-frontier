/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.BooleanAnalysis.Fibers
public import CslibFrontier.Foundations.BooleanAnalysis.CoordinateSampling
public import CslibFrontier.Foundations.BooleanAnalysis.LightPatterns
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Korten's strong mirror-set lemma

A point `x` is a `(p, k)`-limit of a set `Y` of points of the cube (`IsDensityLimit`,
[Korten, Definition 2][Korten2026]) when, with probability at least `3 / 4` over a random mask `P`
of rate `p`, the fiber of `Y` over the coordinates of `x` outside `P` has density at least
`2 ^ (-k)`. If every point of a nonempty set `X` of deficit at most `k ≥ 1` is a `(p, k)`-limit of
`Y`, then `Y` has a nonempty subset of deficit at most `2 k + 2` all of whose points are
`(32768 k p, 194 k)`-limits of `X` (`exists_mirror_set`). This is the analogue, in the setting of
Section 4 of [Korten2026], of Korten's strong mirror-set lemma [Korten, Lemma 5][Korten2026]; the
constants `32768` and `194` are the ones of this proof.

The proof follows Korten's. By the entropy lemma for fibers, the light-patterns lemma and the
conditional sampling law, modifying a uniform point of `X` first on a random mask of rate `p` and
then on a random mask of rate `q = 32768 k p` rarely leaves a point whose fiber in `X` has density
below `2 ^ (-194 k)`. For the first modification, a guiding distribution, which on dense fibers
samples uniformly from their intersection with `Y`, replaces Korten's fixed-size guiding sets. It
has density at most `2 ^ k` and lands in `Y` with probability at least `3 / 4`, so it gives mass at
least `1 / 4` to the points of `Y` that are `(q, 194 k)`-limits of `X`, and these points are many.

## Main definitions

* `Cslib.BitString.IsDensityLimit`: density limits [Korten, Definition 2][Korten2026].

## Main results

* `Cslib.BitString.IsDensityLimit.exists_mem_apply_eq`: at each coordinate, a density limit of `Y`
  at a nonnegative rate below `3 / 4` agrees with some point of `Y`, which may depend on the
  coordinate.
* `Cslib.BitString.exists_mirror_set`: the strong mirror-set lemma, with the constants
  `32768` and `194`.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A `(p,k)`-limit point of `Y` [Korten, Definition 2][Korten2026]: with probability at least
`3/4`, the rate-`p` coordinate fiber over `x` has density at least `2^(-k)` in `Y`. -/
def IsDensityLimit (Y : Finset (ι → Bool)) (p k : ℝ) (x : ι → Bool) : Prop :=
  3 / 4 ≤ bernoulliAverage p
    (fun P => if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then (1 : ℝ) else 0)

/-- Being a density limit of `Y` is decidable, classically, as a real inequality. -/
noncomputable instance (Y : Finset (ι → Bool)) (p k : ℝ) :
    DecidablePred (IsDensityLimit Y p k) :=
  fun _ => Real.decidableLE _ _

/-- At each coordinate `i`, a density limit of `Y` at a nonnegative rate below `3 / 4` agrees with
some point of `Y`, which may depend on `i`. -/
theorem IsDensityLimit.exists_mem_apply_eq {Y : Finset (ι → Bool)} {p k : ℝ} {x : ι → Bool}
    (hlim : IsDensityLimit Y p k x) (hp : 0 ≤ p) (hp' : p < 3 / 4) (i : ι) :
    ∃ y ∈ Y, y i = x i := by
  by_contra hn
  have hd (P : ι → Bool) (hi : P i ≠ true) : coordinateDensity Y P x = 0 := by
    rw [coordinateDensity_eq_expect]
    exact expect_eq_zero fun y _ => ite_eq_right fun hy =>
      hn ⟨resample P x y, hy, by simp [resample, hi]⟩
  have hpoint (P : ι → Bool) :
      (if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then (1 : ℝ) else 0) ≤
        if P i then 1 else 0 := by
    by_cases hi : P i = true
    · rw [ite_eq_left hi]
      split_ifs <;> norm_num
    · rw [ite_eq_right hi, hd P hi, ite_eq_right (not_le.mpr (by positivity))]
  have h := hlim.trans (bernoulliAverage_mono hp (by linarith) hpoint)
  rw [bernoulliAverage_coordinate] at h
  linarith

/-- A density limit with deficit `k` is one with every larger deficit. -/
theorem IsDensityLimit.mono_right {Y : Finset (ι → Bool)} {p k k' : ℝ} {x : ι → Bool}
    (hlim : IsDensityLimit Y p k x) (hp : 0 ≤ p) (hp' : p ≤ 1) (hkk' : k ≤ k') :
    IsDensityLimit Y p k' x := by
  refine hlim.trans (bernoulliAverage_mono hp hp' fun P => ?_)
  by_cases h : (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x
  · have h' : (2 : ℝ) ^ (-k') ≤ coordinateDensity Y P x :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hkk')).trans h
    simp only [ite_eq_left h, ite_eq_left h', le_refl]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

/-! ### Completion densities after two modifications

Apply the entropy lemma and the light-patterns lemma inside the fiber over the union of the two
masks. The conditional sampling law then yields the `31 / 32` estimate for the fraction of first
modifications with low completion density. The explicit constants are `q = 32768 k p` and the
completion deficit `194 k`. -/

private theorem projectionAverage_uniformDensity_fiber (X : Finset (ι → Bool)) (s x : ι → Bool)
    (hX : (coordinateFiber X s x).Nonempty) (R u : {i // s i = true} → Bool) :
    projectionAverage (uniformDensity (coordinateFiber X s x)) R u =
      (2 : ℝ) ^ uniformDeficit (coordinateFiber X s x) *
        coordinateDensity X (fun i => if h : s i = true then !R ⟨i, h⟩ else false)
          (completePattern s x u) := by
  have he : uniformDensity (coordinateFiber X s x) = fun z =>
      (2 : ℝ) ^ uniformDeficit (coordinateFiber X s x) *
        (if completePattern s x z ∈ X then 1 else 0) := by
    funext z
    rw [uniformDensity_eq_deficit hX]
    simp only [coordinateFiber, mem_filter, mem_univ, true_and]
  rw [he, projectionAverage_const_mul,
    projectionAverage_comp_completePattern (fun y => if y ∈ X then 1 else 0),
    coordinateDensity_eq_projectionAverage]
  congr 2 with i : 1
  by_cases hs : s i = true <;> simp [hs]

private theorem coordinateFiber_light_patterns (X : Finset (ι → Bool)) (hX : X.Nonempty)
    (s : ι → Bool) {k r : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (32768 * k)) :
    31 / 32 ≤ 𝔼 x ∈ X, bernoulliAverage r (fun R =>
      if uniformDeficit (coordinateFiber X s x) ≤ 64 * k ∧
        (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X s x)) R z ≤
          (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)
        then 1 else 0) := by
  have hpoint (x : ι → Bool) (hx : x ∈ X) :
      63 / 64 * (if uniformDeficit (coordinateFiber X s x) ≤ 64 * k then (1 : ℝ) else 0) ≤
        bernoulliAverage r (fun R =>
          if uniformDeficit (coordinateFiber X s x) ≤ 64 * k ∧
            (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X s x)) R z ≤
              (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)
            then 1 else 0) := by
    by_cases hd : uniformDeficit (coordinateFiber X s x) ≤ 64 * k
    · simp only [hd, true_and, ite_true, mul_one]
      have hne := coordinateFiber_nonempty s hx
      have ht := le_bernoulliAverage_expect_coordinateMarginal_le
        (fun z => mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ Fintype.card {i // s i = true})
          (uniformMass_nonneg (coordinateFiber X s x) z))
        (expect_uniformDensity hne) (show (1 : ℝ) ≤ 64 * k by linarith)
        (uniformDensity_le_rpow hne hd) hr (hr'.trans_eq (by ring))
      rwa [show (-2 : ℝ) * (64 * k) - 2 = -128 * k - 2 by ring,
        show -(64 * k) = -64 * k by ring] at ht
    · simp [hd, bernoulliAverage_const]
  have hl := expect_le_expect (s := X) hpoint
  rw [← mul_expect] at hl
  linarith [le_expect_uniformDeficit_coordinateFiber_le X hX s (by linarith) hdef]

private theorem fiber_completion_density (X : Finset (ι → Bool)) (s x : ι → Bool)
    (hX : (coordinateFiber X s x).Nonempty) (R : {i // s i = true} → Bool)
    {k : ℝ} (hk : 1 ≤ k) (hd : uniformDeficit (coordinateFiber X s x) ≤ 64 * k)
    (hl : (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X s x)) R z ≤
      (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)) :
    (𝔼 u, if coordinateDensity X (fun i => if h : s i = true then !R ⟨i, h⟩ else false)
      (completePattern s x u) < (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-k - 6) := by
  have hpoint (u : {i // s i = true} → Bool) :
      (if coordinateDensity X (fun i => if h : s i = true then !R ⟨i, h⟩ else false)
        (completePattern s x u) < (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤
        if projectionAverage (uniformDensity (coordinateFiber X s x)) R u ≤
          (2 : ℝ) ^ (-128 * k - 2) then 1 else 0 := by
    split_ifs with hb hl
    · exact le_rfl
    · refine (hl ?_).elim
      rw [projectionAverage_uniformDensity_fiber X s x hX R u]
      calc
        _ ≤ (2 : ℝ) ^ uniformDeficit (coordinateFiber X s x) * (2 : ℝ) ^ (-194 * k) := by gcongr
        _ = (2 : ℝ) ^ (uniformDeficit (coordinateFiber X s x) - 194 * k) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    · positivity
    · exact le_rfl
  have he := expect_le_expect (s := univ) (fun u _ => hpoint u)
  rw [expect_comp_projectionAverage (uniformDensity (coordinateFiber X s x)) R
    (fun v => if v ≤ (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0)] at he
  exact (he.trans hl).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

private theorem fiber_completion_density_union (X : Finset (ι → Bool)) (P Q x : ι → Bool)
    (hx : x ∈ X) {k : ℝ} (hk : 1 ≤ k)
    (hd : uniformDeficit (coordinateFiber X (fun i => P i || Q i) x) ≤ 64 * k)
    (hl : (𝔼 z, if coordinateMarginal
      (uniformDensity (coordinateFiber X (fun i => P i || Q i) x))
      (fun i => P i && !Q i) z ≤ (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-64 * k)) :
    (𝔼 y, if coordinateDensity X Q (resample P x y) < (2 : ℝ) ^ (-194 * k) then
      (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-k - 6) := by
  let S := fun i => P i || Q i
  let R : {i // S i = true} → Bool := fun i => P i && !Q i
  have hq : (fun i => if h : S i = true then !R ⟨i, h⟩ else false) = Q := by
    funext i
    cases hp : P i <;> cases hq : Q i <;> simp [S, R, hp, hq]
  simp_rw [coordinateDensity_resample_union X P Q x, resample_eq_completePattern]
  rw [Fintype.expect_restrict_coordinates
    (fun u => if coordinateDensity X Q (completePattern S x u) <
      (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0), ← hq]
  exact fiber_completion_density X S x (coordinateFiber_nonempty S hx) R hk hd hl

private theorem bad_modifications_probability_of_rate (X : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q r : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (32768 * k))
    (hjoint : (p + q - p * q) * r = p * (1 - q)) :
    31 / 32 ≤ bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      𝔼 x ∈ X, if (𝔼 y, if coordinateDensity X Q (resample P x y) <
        (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-k - 6) then 1 else 0)) := by
  let good (S : ι → Bool) (R : {i // S i = true} → Bool) (x : ι → Bool) : Prop :=
    uniformDeficit (coordinateFiber X S x) ≤ 64 * k ∧
      (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X S x)) R z ≤
        (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)
  have htheta : 0 ≤ p + q - p * q ∧ p + q - p * q ≤ 1 := by
    constructor <;> nlinarith only [hp, hp', hq, hq']
  have hg : 31 / 32 ≤ bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      𝔼 x ∈ X, if good (fun i => P i || Q i) (fun i => P i && !Q i) x then
        (1 : ℝ) else 0)) := by
    rw [bernoulliAverage_union_difference_subtype p q r hjoint
      (fun S R => 𝔼 x ∈ X, if good S R x then (1 : ℝ) else 0)]
    have hs (S : ι → Bool) : 31 / 32 ≤ bernoulliAverage r (fun R =>
        𝔼 x ∈ X, if good S R x then (1 : ℝ) else 0) := by
      rw [bernoulliAverage_expect_comm]
      exact coordinateFiber_light_patterns X hX S hk hdef hr hr'
    simpa only [bernoulliAverage_const] using
      bernoulliAverage_mono htheta.1 htheta.2 hs
  refine hg.trans (bernoulliAverage_mono hp hp' fun P =>
    bernoulliAverage_mono hq hq' fun Q => expect_le_expect (s := X) fun x hx => ?_)
  by_cases hg : good (fun i => P i || Q i) (fun i => P i && !Q i) x
  · have hb := fiber_completion_density_union X P Q x hx hk hg.1 hg.2
    simp only [ite_eq_left hg, ite_eq_left hb, le_refl]
  · simp only [ite_eq_right hg]
    split_ifs <;> norm_num

private theorem mirror_rate_bounds {k p q : ℝ} (hk : 1 ≤ k) (hp : 0 < p) (hq : q = 32768 * k * p)
    (hq' : q ≤ 1 / 2) : 0 < q ∧ q ≤ 1 ∧ p ≤ q := by
  refine ⟨by rw [hq]; positivity, by linarith, ?_⟩
  calc p = 1 * p := (one_mul p).symm
    _ ≤ 32768 * k * p := by gcongr; linarith
    _ = q := hq.symm

/-- With probability at least `31/32` over `P`, `Q`, and a uniform `x ∈ X`,
at most a `2^(-k-6)` fraction of modifications to `x` on `P` have completion
density below `2^(-194*k)` when the coordinates in `Q` are subsequently modified. -/
private theorem mirror_bad_modifications_probability (X : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2) :
    31 / 32 ≤ bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      𝔼 x ∈ X, if (𝔼 y, if coordinateDensity X Q (resample P x y) <
        (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-k - 6) then 1 else 0)) := by
  obtain ⟨hqp, hq1, hpq⟩ := mirror_rate_bounds hk hp hq hq'
  have htheta : 0 < p + q - p * q := by nlinarith only [hp, hqp, hq1]
  have hr : conditionalSamplingRate p q ≤ 1 / (32768 * k) := by
    refine (conditionalSamplingRate_le_div hp.le hqp hq1).trans_eq ?_
    rw [hq]
    field_simp
  exact bad_modifications_probability_of_rate X hX hk hdef hp.le (hpq.trans hq1) hqp.le hq1
    (conditionalSamplingRate_nonneg hp.le hqp.le hq1) hr (mul_conditionalSamplingRate htheta.ne')

/-! ### The guiding distribution

On a sufficiently dense fiber, sample uniformly from its intersection with `Y`; on the remaining
fibers, sample uniformly from the whole fiber. The density of this sampling rule is at most `2^k`.
This is a distributional variant of the fixed-size guiding sets in Korten's proof, avoiding a
rounding operation. The completion estimate bounds the guided failure probability by `1/16`, and
intersecting `Y` with the `(q, 194 k)`-limits of `X` gives a nonempty mirror set of deficit at most
`2 k + 2`, with `q = 32768 k p`. -/

/-- Density of the guiding rule relative to uniform coordinate modifications.
Dense fibers are restricted to `Y`; the other fibers are left uniform. -/
private noncomputable def guidingDensity (Y : Finset (ι → Bool)) (k : ℝ) (P x y : ι → Bool) :
    ℝ :=
  if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then
    (if resample P x y ∈ Y then 1 else 0) / coordinateDensity Y P x else 1

/-- Expectation of a test function after a guided modification of a uniform
point of `X`, using a rate-`p` coordinate mask and deficit parameter `k`. -/
private noncomputable def guidedAverage (X Y : Finset (ι → Bool)) (p k : ℝ)
    (f : (ι → Bool) → ℝ) : ℝ :=
  𝔼 x ∈ X, bernoulliAverage p (fun P =>
    𝔼 y, guidingDensity Y k P x y * f (resample P x y))

private theorem guidingDensity_nonneg (Y : Finset (ι → Bool)) (k : ℝ) (P x y : ι → Bool) :
    0 ≤ guidingDensity Y k P x y := by
  have hd := coordinateDensity_nonneg Y P x
  unfold guidingDensity
  split_ifs <;> positivity

private theorem expect_guidingDensity (Y : Finset (ι → Bool)) (k : ℝ) (P x : ι → Bool) :
    (𝔼 y, guidingDensity Y k P x y) = 1 := by
  unfold guidingDensity
  split_ifs with h
  · rw [← expect_div, ← coordinateDensity_eq_expect]
    exact div_self (ne_of_gt (lt_of_lt_of_le (by positivity) h))
  · exact Fintype.expect_const _

private theorem guidingDensity_le (Y : Finset (ι → Bool)) {k : ℝ} (hk : 0 ≤ k)
    (P x y : ι → Bool) : guidingDensity Y k P x y ≤ (2 : ℝ) ^ k := by
  unfold guidingDensity
  split_ifs with h hy
  · rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) h)]
    calc (1 : ℝ) = (2 : ℝ) ^ k * (2 : ℝ) ^ (-k) := by
          rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
      _ ≤ (2 : ℝ) ^ k * coordinateDensity Y P x := by gcongr
  · simp only [zero_div]; positivity
  · exact Real.one_le_rpow (by norm_num) hk

private theorem guidedAverage_mono (X Y : Finset (ι → Bool)) {p k : ℝ} (hp : 0 ≤ p)
    (hp' : p ≤ 1) {f g : (ι → Bool) → ℝ} (hfg : ∀ z, f z ≤ g z) :
    guidedAverage X Y p k f ≤ guidedAverage X Y p k g :=
  expect_le_expect fun x _ => bernoulliAverage_mono hp hp' fun P =>
    expect_le_expect fun y _ =>
      mul_le_mul_of_nonneg_left (hfg _) (guidingDensity_nonneg Y k P x y)

private theorem guidedAverage_bound (X Y : Finset (ι → Bool)) {p k : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hk : 0 ≤ k) (f : (ι → Bool) → ℝ)
    (hf : ∀ z, 0 ≤ f z) :
    guidedAverage X Y p k f ≤ (2 : ℝ) ^ k * (∑ z, f z) / X.card := by
  have hm : guidedAverage X Y p k f ≤
      (2 : ℝ) ^ k * bernoulliAverage p (fun P => 𝔼 x ∈ X, 𝔼 y, f (resample P x y)) := by
    unfold guidedAverage
    rw [bernoulliAverage_expect_comm, mul_expect]
    refine expect_le_expect fun x _ => ?_
    rw [← bernoulliAverage_const_mul]
    refine bernoulliAverage_mono hp hp' fun P => ?_
    rw [mul_expect]
    exact expect_le_expect fun y _ =>
      mul_le_mul_of_nonneg_right (guidingDensity_le Y hk P x y) (hf _)
  have hb := bernoulliAverage_mono hp hp' (expect_resample_subset_le X hf)
  rw [bernoulliAverage_const] at hb
  exact hm.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq
    (mul_div_assoc _ _ _).symm)

private theorem guidingDensity_hits (Y : Finset (ι → Bool)) (k : ℝ) (P x : ι → Bool) :
    (if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then (1 : ℝ) else 0) ≤
      𝔼 y, guidingDensity Y k P x y * (if resample P x y ∈ Y then 1 else 0) := by
  by_cases h : (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x
  · have he (y : ι → Bool) : guidingDensity Y k P x y *
        (if resample P x y ∈ Y then 1 else 0) = guidingDensity Y k P x y := by
      simp only [guidingDensity, ite_eq_left h]
      split_ifs <;> ring
    simp_rw [he, expect_guidingDensity, ite_eq_left h]
    exact le_rfl
  · rw [ite_eq_right h]
    exact expect_nonneg fun y _ => mul_nonneg (guidingDensity_nonneg Y k P x y)
      (by split_ifs <;> norm_num)

private theorem guidedAverage_hits (X Y : Finset (ι → Bool)) (hX : X.Nonempty) {p k : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hlim : ∀ x ∈ X, IsDensityLimit Y p k x) :
    3 / 4 ≤ guidedAverage X Y p k (fun z => if z ∈ Y then 1 else 0) := by
  have hpoint (x : ι → Bool) (hx : x ∈ X) : 3 / 4 ≤ bernoulliAverage p (fun P =>
      𝔼 y, guidingDensity Y k P x y * (if resample P x y ∈ Y then 1 else 0)) :=
    (hlim x hx).trans (bernoulliAverage_mono hp hp' (fun P => guidingDensity_hits Y k P x))
  simpa only [guidedAverage, expect_const hX] using expect_le_expect (s := X) hpoint

private theorem guidedAverage_add_const_mul (X Y : Finset (ι → Bool)) (p k a : ℝ)
    (f g : (ι → Bool) → ℝ) :
    guidedAverage X Y p k (fun z => f z + a * g z) =
      guidedAverage X Y p k f + a * guidedAverage X Y p k g := by
  unfold guidedAverage
  have he (x P y : ι → Bool) : guidingDensity Y k P x y *
      (f (resample P x y) + a * g (resample P x y)) =
        guidingDensity Y k P x y * f (resample P x y) +
        a * (guidingDensity Y k P x y * g (resample P x y)) := by ring
  simp_rw [he, expect_add_distrib, ← mul_expect, bernoulliAverage_add,
    bernoulliAverage_const_mul]
  rw [expect_add_distrib, ← mul_expect]

private theorem guidedAverage_bernoulli (X Y : Finset (ι → Bool)) (p q k : ℝ)
    (f : (ι → Bool) → (ι → Bool) → ℝ) :
    guidedAverage X Y p k (fun z => bernoulliAverage q (fun Q => f Q z)) =
      bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
        𝔼 x ∈ X, 𝔼 y, guidingDensity Y k P x y * f Q (resample P x y))) := by
  unfold guidedAverage
  simp_rw [← bernoulliAverage_const_mul, ← bernoulliAverage_expect_comm]

private theorem guidingDensity_small_event (Y : Finset (ι → Bool)) {k : ℝ} (hk : 0 ≤ k)
    (P x : ι → Bool) (f : (ι → Bool) → ℝ) (hf : ∀ y, 0 ≤ f y) (hf' : ∀ y, f y ≤ 1) :
    (𝔼 y, guidingDensity Y k P x y * f y) ≤
      65 / 64 - (if (𝔼 y, f y) ≤ (2 : ℝ) ^ (-k - 6) then (1 : ℝ) else 0) := by
  have hone : (𝔼 y, guidingDensity Y k P x y * f y) ≤ 1 := by
    rw [← expect_guidingDensity Y k P x]
    exact expect_le_expect fun y _ => mul_le_of_le_one_right
      (guidingDensity_nonneg Y k P x y) (hf' y)
  by_cases hsmall : (𝔼 y, f y) ≤ (2 : ℝ) ^ (-k - 6)
  · have hcap : (𝔼 y, guidingDensity Y k P x y * f y) ≤
        (2 : ℝ) ^ k * (𝔼 y, f y) := by
      rw [mul_expect]
      exact expect_le_expect fun y _ =>
        mul_le_mul_of_nonneg_right (guidingDensity_le Y hk P x y) (hf y)
    have he : (2 : ℝ) ^ k * (2 : ℝ) ^ (-k - 6) = 1 / 64 := by
      rw [← Real.rpow_add (by norm_num), show k + (-k - 6) = (-6 : ℝ) by ring]; norm_num
    rw [ite_eq_left hsmall]
    linarith [hcap.trans ((mul_le_mul_of_nonneg_left hsmall (by positivity)).trans_eq he)]
  · rw [ite_eq_right hsmall]; linarith

private theorem guidedAverage_bad_completion (X Y : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2) :
    guidedAverage X Y p k (fun z => bernoulliAverage q (fun Q =>
      if coordinateDensity X Q z < (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0)) ≤ 1 / 16 := by
  obtain ⟨hqp, hq1, hpq⟩ := mirror_rate_bounds hk hp hq hq'
  let f (Q z : ι → Bool) : ℝ :=
    if coordinateDensity X Q z < (2 : ℝ) ^ (-194 * k) then 1 else 0
  have hm : guidedAverage X Y p k (fun z => bernoulliAverage q (fun Q => f Q z)) ≤
      bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
        𝔼 x ∈ X, (65 / 64 - (if (𝔼 y, f Q (resample P x y)) ≤ (2 : ℝ) ^ (-k - 6)
          then (1 : ℝ) else 0)))) := by
    rw [guidedAverage_bernoulli]
    exact bernoulliAverage_mono hp.le (hpq.trans hq1) fun P =>
      bernoulliAverage_mono hqp.le hq1 fun Q => expect_le_expect fun x _ =>
        guidingDensity_small_event Y (by linarith) P x (fun y => f Q (resample P x y))
          (fun y => by dsimp [f]; split_ifs <;> norm_num)
          (fun y => by dsimp [f]; split_ifs <;> norm_num)
  simp_rw [expect_sub_distrib, expect_const hX, bernoulliAverage_sub,
    bernoulliAverage_const] at hm
  have hg := mirror_bad_modifications_probability X hX hk hdef hp hq hq'
  dsimp only [f] at hm
  linarith

private theorem one_sub_bernoulliAverage_density_lt (X : Finset (ι → Bool)) (q t : ℝ)
    (z : ι → Bool) :
    bernoulliAverage q (fun Q => if coordinateDensity X Q z < (2 : ℝ) ^ (-t) then
      (1 : ℝ) else 0) = 1 - bernoulliAverage q
        (fun Q => if (2 : ℝ) ^ (-t) ≤ coordinateDensity X Q z then (1 : ℝ) else 0) := by
  have he (Q : ι → Bool) : (if coordinateDensity X Q z < (2 : ℝ) ^ (-t) then
      (1 : ℝ) else 0) = 1 - (if (2 : ℝ) ^ (-t) ≤ coordinateDensity X Q z then 1 else 0) := by
    split_ifs <;> linarith
  simp_rw [he, bernoulliAverage_sub, bernoulliAverage_const]

private theorem guidedAverage_mirror_mass (X Y : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2)
    (hlim : ∀ x ∈ X, IsDensityLimit Y p k x) :
    1 / 4 ≤ guidedAverage X Y p k
      (fun z => if z ∈ Y ∧ IsDensityLimit X q (194 * k) z then (1 : ℝ) else 0) := by
  obtain ⟨hqp, hq1, hpq⟩ := mirror_rate_bounds hk hp hq hq'
  let bad (z : ι → Bool) : ℝ := bernoulliAverage q (fun Q =>
    if coordinateDensity X Q z < (2 : ℝ) ^ (-(194 * k)) then (1 : ℝ) else 0)
  have hbad (z : ι → Bool) : 0 ≤ bad z := by
    simpa only [bernoulliAverage_const] using
      bernoulliAverage_mono hqp.le hq1 (f := fun _ => 0) fun _ => by split_ifs <;> norm_num
  have hpoint (z : ι → Bool) : (if z ∈ Y then (1 : ℝ) else 0) ≤
      (if z ∈ Y ∧ IsDensityLimit X q (194 * k) z then 1 else 0) + 4 * bad z := by
    by_cases hy : z ∈ Y
    · by_cases hl : IsDensityLimit X q (194 * k) z
      · simp only [hy, hl, and_self, ↓reduceIte]; linarith [hbad z]
      · simp only [hy, hl, and_false, ↓reduceIte, zero_add, bad,
          one_sub_bernoulliAverage_density_lt]
        unfold IsDensityLimit at hl
        linarith
    · simp only [hy, false_and, ↓reduceIte, zero_add]; linarith [hbad z]
  have hm := guidedAverage_mono X Y (k := k) hp.le (hpq.trans hq1) hpoint
  rw [guidedAverage_add_const_mul] at hm
  have hhit := guidedAverage_hits X Y hX hp.le (hpq.trans hq1) hlim
  have hloss : guidedAverage X Y p k bad ≤ 1 / 16 := by
    simpa only [bad, neg_mul] using guidedAverage_bad_completion X Y hX hk hdef hp hq hq'
  linarith

/-- **The strong mirror-set lemma** [Korten, Lemma 5 and Section 4][Korten2026], with the constants
of this proof: if every point of a nonempty set `X` of deficit at most `k ≥ 1` is a
`(p, k)`-limit of `Y`, for a rate `p > 0` with `q = 32768 k p ≤ 1 / 2`, then `Y` has a nonempty
subset of deficit at most `2 k + 2` all of whose points are `(q, 194 k)`-limits of `X`. -/
theorem exists_mirror_set (X Y : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2)
    (hlim : ∀ x ∈ X, IsDensityLimit Y p k x) :
    ∃ Y' : Finset (ι → Bool), Y' ⊆ Y ∧ Y'.Nonempty ∧ uniformDeficit Y' ≤ 2 * k + 2 ∧
      ∀ y ∈ Y', IsDensityLimit X q (194 * k) y := by
  let A := Y.filter (IsDensityLimit X q (194 * k))
  obtain ⟨_, hq1, hpq⟩ := mirror_rate_bounds hk hp hq hq'
  have hm : 1 / 4 ≤ guidedAverage X Y p k (fun z => if z ∈ A then (1 : ℝ) else 0) := by
    simpa only [A, mem_filter] using
      guidedAverage_mirror_mass X Y hX hk hdef hp hq hq' hlim
  have hb : guidedAverage X Y p k (fun z => if z ∈ A then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ k * A.card / X.card := by
    simpa using guidedAverage_bound X Y hp.le (hpq.trans hq1) (show 0 ≤ k by linarith)
      (fun z => if z ∈ A then (1 : ℝ) else 0) (fun z => by split_ifs <;> norm_num)
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hxcount := (uniformDeficit_le_iff hX).mp hdef
  have hprod : (4 * (2 : ℝ) ^ k) * (2 : ℝ) ^ ((Fintype.card ι : ℝ) - (2 * k + 2)) =
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) - k) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    congr 1
    ring
  have hcard : (2 : ℝ) ^ ((Fintype.card ι : ℝ) - (2 * k + 2)) ≤ A.card := by
    have hh := (le_div_iff₀ hxpos).mp (hm.trans hb)
    rw [← mul_le_mul_iff_right₀ (show 0 < 4 * (2 : ℝ) ^ k by positivity), hprod]
    calc (2 : ℝ) ^ ((Fintype.card ι : ℝ) - k) ≤ X.card := hxcount
      _ = 4 * (1 / 4 * X.card) := by ring
      _ ≤ 4 * ((2 : ℝ) ^ k * A.card) := by gcongr
      _ = 4 * (2 : ℝ) ^ k * A.card := by ring
  have hA : A.Nonempty := card_pos.mp <| Nat.cast_pos.mp <|
    (Real.rpow_pos_of_pos two_pos _).trans_le hcard
  exact ⟨A, filter_subset _ _, hA, (uniformDeficit_le_iff hA).mpr hcard,
    fun y hy => (mem_filter.mp hy).2⟩

end

end Cslib.BitString
