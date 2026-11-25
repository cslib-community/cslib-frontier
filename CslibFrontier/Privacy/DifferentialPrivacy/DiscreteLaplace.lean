/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Privacy.DifferentialPrivacy.Basic
public import CslibFrontier.Privacy.DifferentialPrivacy.Sensitivity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The geometric mechanism and the discrete Laplace distribution

The two-sided geometric distribution with ratio `α ∈ [0, 1)` gives each integer `z` the mass
`(1 - α) / (1 + α) · α ^ |z|` (`twoSidedGeometric`). Adding it to the value of a count query is
the `α`-geometric mechanism [GhoshRoughgardenSundararajan2012, Example 2.1]. The masses of
neighboring integers differ by a factor of at most `α⁻¹`, so adding this noise to an
integer-valued query `q` of sensitivity `Δ` (`Sensitivity Adj (fun x => (q x : ℝ)) Δ`) is
`(Δ · ln α⁻¹, 0)`-differentially private (`differentiallyPrivate_addNoise_twoSidedGeometric`).

With `α = exp (-1 / t)` it is the discrete Laplace distribution with scale `t`
(`discreteLaplace`, `discreteLaplace_apply`) [CanonneKamathSteinke2020, Definition 28]. Adding
discrete Laplace noise of scale `Δ / ε` to an integer-valued query of sensitivity `Δ` is
`(ε, 0)`-private (`differentiallyPrivate_addNoise_discreteLaplace`)
[CanonneKamathSteinke2020, Lemma 29], and for `Y` with scale `1 / ε` the tails are
`Pr[Y ≥ m] = Pr[Y ≤ -m] = exp (-ε (m - 1)) / (exp ε + 1)` for every natural `m`
(`discreteLaplace_toOuterMeasure_Ici`, `discreteLaplace_toOuterMeasure_Iic`)
[CanonneKamathSteinke2020, Lemma 30]. For the ratio form, `twoSidedGeometric_toOuterMeasure_Ici`
and `twoSidedGeometric_toOuterMeasure_Iic` give `α ^ m / (1 + α)`, and for `m ≠ 0`,
`twoSidedGeometric_toOuterMeasure_le_natAbs` gives the two-sided accuracy bound
`Pr[|Y| ≥ m] = 2 α ^ m / (1 + α)`.

These distributions have infinite support, so they are ideal laws (`PMF ℤ`), not programs over
finitely many fair coins; the mechanisms are stated at the level of their output distributions.
The cost of sampling them exactly is not modelled here.

## Main definitions

* `Cslib.Privacy.twoSidedGeometric`: the two-sided geometric distribution on `ℤ`.
* `Cslib.Privacy.discreteLaplace`: the discrete Laplace distribution with scale `t`.
* `Cslib.Privacy.addNoise`: an integer-valued query plus independent integer noise.

## Main results

* `Cslib.Privacy.DifferentiallyPrivate.addNoise`: noise whose masses change by a factor of at most
  `exp ε` under shifts of size at most `Δ` makes a query of sensitivity `Δ` `(ε, 0)`-private.
* `Cslib.Privacy.differentiallyPrivate_addNoise_twoSidedGeometric`: the geometric mechanism.
* `Cslib.Privacy.differentiallyPrivate_addNoise_discreteLaplace`: the discrete Laplace mechanism.
* `Cslib.Privacy.twoSidedGeometric_toOuterMeasure_le_natAbs`,
  `Cslib.Privacy.discreteLaplace_toOuterMeasure_Ici`: exact tails.

## References

* [CanonneKamathSteinke2020]
* [GhoshRoughgardenSundararajan2012]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

private theorem hasSum_ofReal_of_hasSum_one {β : Type*} {f : β → ℝ} (h0 : ∀ b, 0 ≤ f b)
    (h : HasSum f 1) : HasSum (fun b => ENNReal.ofReal (f b)) 1 := by
  rw [CompleteLattice.summable.hasSum_iff, ← ENNReal.ofReal_tsum_of_nonneg h0 h.summable,
    h.tsum_eq, ENNReal.ofReal_one]

private theorem toOuterMeasure_eq_ofReal_tsum {β : Type*} {f : β → ℝ} (h0 : ∀ b, 0 ≤ f b)
    (hf : Summable f) (p : PMF β) (hp : ∀ b, p b = ENNReal.ofReal (f b)) (S : Set β) :
    p.toOuterMeasure S = ENNReal.ofReal (∑' b, S.indicator f b) := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.ofReal_tsum_of_nonneg
    (fun b => Set.indicator_nonneg (fun b _ => h0 b) b) (hf.indicator S)]
  refine tsum_congr fun b => ?_
  by_cases hb : b ∈ S <;> simp [hb, hp]

section Geometric

variable {α : ℝ}

/-- `∑ z : ℤ, α ^ |z| = (1 + α) / (1 - α)` for `α ∈ [0, 1)`. -/
theorem hasSum_pow_natAbs (h0 : 0 ≤ α) (h1 : α < 1) :
    HasSum (fun z : ℤ => α ^ z.natAbs) ((1 + α) / (1 - α)) := by
  have hpos := hasSum_geometric_of_lt_one h0 h1
  convert HasSum.of_nat_of_neg_add_one (f := fun z : ℤ => α ^ z.natAbs) (by simpa using hpos)
    (by simpa only [show ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 by omega, pow_succ'] using
      hpos.mul_left α) using 1
  have : (1 - α) ≠ 0 := by linarith
  field_simp

/-- The masses of the two-sided geometric distribution sum to one. -/
theorem hasSum_mul_pow_natAbs (h0 : 0 ≤ α) (h1 : α < 1) :
    HasSum (fun z : ℤ => (1 - α) / (1 + α) * α ^ z.natAbs) 1 := by
  convert (hasSum_pow_natAbs h0 h1).mul_left ((1 - α) / (1 + α)) using 1
  have : (1 - α) ≠ 0 := by linarith
  have : (1 + α) ≠ 0 := by linarith
  field_simp

/-- The two-sided geometric distribution on `ℤ` with ratio `α ∈ [0, 1)`: the integer `z` has mass
`(1 - α) / (1 + α) · α ^ |z|` [GhoshRoughgardenSundararajan2012, Example 2.1]. -/
noncomputable def twoSidedGeometric (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) : PMF ℤ :=
  ⟨fun z => ENNReal.ofReal ((1 - α) / (1 + α) * α ^ z.natAbs),
    hasSum_ofReal_of_hasSum_one
      (fun z => mul_nonneg (div_nonneg (by linarith) (by linarith)) (pow_nonneg h0 _))
      (hasSum_mul_pow_natAbs h0 h1)⟩

/-- The mass of `z` under the two-sided geometric distribution. -/
theorem twoSidedGeometric_apply (h0 : 0 ≤ α) (h1 : α < 1) (z : ℤ) :
    twoSidedGeometric α h0 h1 z = ENNReal.ofReal ((1 - α) / (1 + α) * α ^ z.natAbs) := by
  rfl

/-- The two-sided geometric distribution is symmetric. -/
theorem twoSidedGeometric_map_neg (h0 : 0 ≤ α) (h1 : α < 1) :
    (twoSidedGeometric α h0 h1).map Neg.neg = twoSidedGeometric α h0 h1 := by
  ext z
  rw [PMF.map_apply, tsum_eq_single (-z)]
  · simp [twoSidedGeometric_apply]
  · intro w hw
    exact ite_eq_right (by omega)

private theorem hasSum_ite_le_mul_pow (h0 : 0 ≤ α) (h1 : α < 1) (C : ℝ) (m : ℕ) :
    HasSum (fun n : ℕ => if m ≤ n then C * α ^ n else 0) (C * α ^ m * (1 - α)⁻¹) := by
  rw [← hasSum_nat_add_iff' m,
    Finset.sum_eq_zero fun i hi => ite_eq_right (by simpa using hi), sub_zero]
  convert (hasSum_geometric_of_lt_one h0 h1).mul_left (C * α ^ m) using 1
  funext n
  simp only [ite_eq_left (Nat.le_add_left m n), pow_add]
  ring

/-- Upper tail of the two-sided geometric distribution: `Pr[Y ≥ m] = α ^ m / (1 + α)` for every
natural `m`. -/
theorem twoSidedGeometric_toOuterMeasure_Ici (h0 : 0 ≤ α) (h1 : α < 1) (m : ℕ) :
    (twoSidedGeometric α h0 h1).toOuterMeasure (Set.Ici (m : ℤ)) =
      ENNReal.ofReal (α ^ m / (1 + α)) := by
  have : 0 ≤ 1 - α := by linarith
  set C := (1 - α) / (1 + α) with hC
  rw [toOuterMeasure_eq_ofReal_tsum (f := fun z : ℤ => C * α ^ z.natAbs) (fun z => by positivity)
    (hasSum_mul_pow_natAbs h0 h1).summable _ (twoSidedGeometric_apply h0 h1)]
  congr 1
  have h := HasSum.of_nat_of_neg_add_one
    (f := (Set.Ici (m : ℤ)).indicator (fun z => C * α ^ z.natAbs))
    (by simpa [Set.indicator_apply] using hasSum_ite_le_mul_pow h0 h1 C m)
    (by
      have hneg (n : ℕ) :
          (Set.Ici (m : ℤ)).indicator (fun z => C * α ^ z.natAbs) (-((n : ℤ) + 1)) = 0 :=
        Set.indicator_of_notMem (by simp only [Set.mem_Ici]; omega) _
      simpa only [hneg] using (hasSum_zero : HasSum _ (0 : ℝ)))
  rw [h.tsum_eq, add_zero, hC]
  have : (1 - α) ≠ 0 := by linarith
  have : (1 + α) ≠ 0 := by linarith
  field_simp

/-- Lower tail of the two-sided geometric distribution: `Pr[Y ≤ -m] = α ^ m / (1 + α)` for every
natural `m`. -/
theorem twoSidedGeometric_toOuterMeasure_Iic (h0 : 0 ≤ α) (h1 : α < 1) (m : ℕ) :
    (twoSidedGeometric α h0 h1).toOuterMeasure (Set.Iic (-(m : ℤ))) =
      ENNReal.ofReal (α ^ m / (1 + α)) := by
  rw [← twoSidedGeometric_toOuterMeasure_Ici h0 h1 m, ← twoSidedGeometric_map_neg h0 h1,
    PMF.toOuterMeasure_map_apply, twoSidedGeometric_map_neg h0 h1]
  exact congrArg _
    (Set.ext fun _ => by simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]; omega)

/-- Two-sided tail of the two-sided geometric distribution: `Pr[|Y| ≥ m] = 2 α ^ m / (1 + α)`
for every positive natural `m`. -/
theorem twoSidedGeometric_toOuterMeasure_le_natAbs (h0 : 0 ≤ α) (h1 : α < 1) {m : ℕ}
    (hm : m ≠ 0) :
    (twoSidedGeometric α h0 h1).toOuterMeasure {z | m ≤ z.natAbs} =
      ENNReal.ofReal (2 * α ^ m / (1 + α)) := by
  have : 0 ≤ 1 - α := by linarith
  set C := (1 - α) / (1 + α) with hC
  rw [toOuterMeasure_eq_ofReal_tsum (f := fun z : ℤ => C * α ^ z.natAbs) (fun z => by positivity)
    (hasSum_mul_pow_natAbs h0 h1).summable _ (twoSidedGeometric_apply h0 h1)]
  congr 1
  set F : ℕ → ℝ := fun n => if m ≤ n then C * α ^ n else 0
  have hA : HasSum F (C * α ^ m * (1 - α)⁻¹) := hasSum_ite_le_mul_pow h0 h1 C m
  have hB : HasSum (fun n => F (n + 1)) (C * α ^ m * (1 - α)⁻¹) := by
    simpa [F, Nat.pos_of_ne_zero hm, Nat.not_succ_le_zero, hm] using (hasSum_nat_add_iff' 1).mpr hA
  have h := HasSum.of_nat_of_neg_add_one
    (f := {z : ℤ | m ≤ z.natAbs}.indicator (fun z => C * α ^ z.natAbs))
    (by simpa [Set.indicator_apply, F] using hA)
    (by simpa only [Set.indicator_apply, Set.mem_ofPred_eq,
      show ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 by omega, F] using hB)
  rw [h.tsum_eq, hC]
  have : (1 - α) ≠ 0 := by linarith
  have : (1 + α) ≠ 0 := by linarith
  field_simp
  ring

end Geometric

section Mechanism

variable {D : Type*}

/-- The mechanism releasing the integer-valued query `q` plus independent noise drawn from
`noise`. -/
noncomputable def addNoise (q : D → ℤ) (noise : PMF ℤ) (x : D) : PMF ℤ :=
  noise.map (q x + ·)

/-- The noisy answer is `r` exactly when the noise is `r - q x`. -/
theorem addNoise_apply (q : D → ℤ) (noise : PMF ℤ) (x : D) (r : ℤ) :
    addNoise q noise x r = noise (r - q x) := by
  rw [addNoise, PMF.map_apply, tsum_eq_single (r - q x)]
  · simp
  · intro w hw
    exact ite_eq_right (by omega)

/-- The error of the noisy answer has the law of the noise. -/
theorem addNoise_toOuterMeasure_le_natAbs_sub (q : D → ℤ) (noise : PMF ℤ) (x : D) (m : ℕ) :
    (addNoise q noise x).toOuterMeasure {r | m ≤ (r - q x).natAbs} =
      noise.toOuterMeasure {z | m ≤ z.natAbs} := by
  rw [addNoise, PMF.toOuterMeasure_map_apply]
  exact congrArg _ (Set.ext fun _ => by simp)

/-- If shifting the noise by at most `Δ` changes each mass by a factor of at most `exp ε`, then
adding it to a query of sensitivity `Δ` is `(ε, 0)`-differentially private. -/
theorem DifferentiallyPrivate.addNoise {Adj : D → D → Prop} {q : D → ℤ} {noise : PMF ℤ} {Δ ε : ℝ}
    (hq : Sensitivity Adj (fun x => (q x : ℝ)) Δ)
    (hnoise : ∀ z d : ℤ, |(d : ℝ)| ≤ Δ → noise z ≤ ENNReal.ofReal (Real.exp ε) * noise (z + d)) :
    DifferentiallyPrivate Adj (Privacy.addNoise q noise) ε 0 :=
  of_apply_le fun x y hxy r => by
    rw [addNoise_apply, addNoise_apply]
    have := hnoise (r - q x) (q x - q y) (by push_cast; exact hq hxy)
    rwa [show r - q x + (q x - q y) = r - q y by ring] at this

variable {α : ℝ}

/-- Shifting the two-sided geometric distribution by at most `Δ` changes each mass by a factor of
at most `α⁻¹ ^ Δ`. -/
theorem twoSidedGeometric_apply_le (h0 : 0 < α) (h1 : α < 1) {Δ : ℝ} (z d : ℤ)
    (hd : |(d : ℝ)| ≤ Δ) :
    twoSidedGeometric α h0.le h1 z ≤
      ENNReal.ofReal (Real.exp (Δ * Real.log α⁻¹)) * twoSidedGeometric α h0.le h1 (z + d) := by
  rw [twoSidedGeometric_apply, twoSidedGeometric_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hC : 0 ≤ (1 - α) / (1 + α) := div_nonneg (by linarith) (by linarith)
  simp only [show ∀ n : ℕ, α ^ n = Real.exp (n * Real.log α) from fun n => by
    rw [Real.exp_nat_mul, Real.exp_log h0], mul_left_comm, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  rw [Real.log_inv]
  have hlog : Real.log α < 0 := Real.log_neg h0 h1
  have hdR : (d.natAbs : ℝ) ≤ Δ := by rwa [Nat.cast_natAbs, Int.cast_abs]
  have htri : ((z + d).natAbs : ℝ) ≤ z.natAbs + d.natAbs := by exact_mod_cast Int.natAbs_add_le z d
  nlinarith

/-- The `α`-geometric mechanism [GhoshRoughgardenSundararajan2012, Example 2.1]: adding
two-sided geometric noise with ratio `α ∈ (0, 1)` to an integer-valued query of sensitivity `Δ`
is `(Δ · ln α⁻¹, 0)`-differentially private. For a count query (`Δ = 1`) this is the source's
`α`-differential privacy. -/
theorem differentiallyPrivate_addNoise_twoSidedGeometric {Adj : D → D → Prop} {q : D → ℤ}
    {Δ : ℝ} (hq : Sensitivity Adj (fun x => (q x : ℝ)) Δ) (h0 : 0 < α) (h1 : α < 1) :
    DifferentiallyPrivate Adj (addNoise q (twoSidedGeometric α h0.le h1))
      (Δ * Real.log α⁻¹) 0 :=
  DifferentiallyPrivate.addNoise hq fun z d hd => twoSidedGeometric_apply_le h0 h1 z d hd

end Mechanism

section DiscreteLaplace

/-- The discrete Laplace distribution with scale `t > 0` [CanonneKamathSteinke2020,
Definition 28]: the two-sided geometric distribution with ratio `exp (-1 / t)`. -/
noncomputable def discreteLaplace (t : ℝ) (ht : 0 < t) : PMF ℤ :=
  twoSidedGeometric (Real.exp (-1 / t)) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) ht))

/-- The discrete Laplace distribution gives `z` the mass
`(exp (1 / t) - 1) / (exp (1 / t) + 1) · exp (-|z| / t)` [CanonneKamathSteinke2020,
Definition 28]. -/
theorem discreteLaplace_apply (t : ℝ) (ht : 0 < t) (z : ℤ) :
    discreteLaplace t ht z =
      ENNReal.ofReal ((Real.exp (1 / t) - 1) / (Real.exp (1 / t) + 1) *
        Real.exp (-|(z : ℝ)| / t)) := by
  rw [discreteLaplace, twoSidedGeometric_apply]
  congr 1
  rw [← Real.exp_nat_mul, Nat.cast_natAbs, Int.cast_abs,
    show Real.exp (-1 / t) = (Real.exp (1 / t))⁻¹ by rw [← Real.exp_neg, neg_div]]
  have := Real.exp_pos (1 / t)
  congr 1 <;> [field_simp; ring_nf]

/-- Adding discrete Laplace noise of scale `Δ / ε` to an integer-valued query of sensitivity
`Δ > 0` is `(ε, 0)`-differentially private [CanonneKamathSteinke2020, Lemma 29]. -/
theorem differentiallyPrivate_addNoise_discreteLaplace {D : Type*} {Adj : D → D → Prop}
    {q : D → ℤ} {Δ : ℝ} (hΔ : 0 < Δ) (hq : Sensitivity Adj (fun x => (q x : ℝ)) Δ)
    {ε : ℝ} (hε : 0 < ε) :
    DifferentiallyPrivate Adj (addNoise q (discreteLaplace (Δ / ε) (by positivity))) ε 0 := by
  rw [discreteLaplace]
  simpa only [Real.log_inv, Real.log_exp, show Δ * -(-1 / (Δ / ε)) = ε by field_simp] using
    differentiallyPrivate_addNoise_twoSidedGeometric hq (Real.exp_pos (-1 / (Δ / ε)))
      (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) (by positivity)))

/-- Upper tail of the discrete Laplace distribution with scale `1 / ε`:
`Pr[Y ≥ m] = exp (-ε (m - 1)) / (exp ε + 1)` for every natural `m`
[CanonneKamathSteinke2020, Lemma 30]. -/
theorem discreteLaplace_toOuterMeasure_Ici {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    (discreteLaplace (1 / ε) (by positivity)).toOuterMeasure (Set.Ici (m : ℤ)) =
      ENNReal.ofReal (Real.exp (-ε * (m - 1)) / (Real.exp ε + 1)) := by
  rw [discreteLaplace, twoSidedGeometric_toOuterMeasure_Ici,
    show -1 / (1 / ε) = -ε by field_simp]
  congr 1
  rw [div_eq_div_iff (by positivity) (by positivity), ← Real.exp_nat_mul, mul_add, mul_add,
    ← Real.exp_add, ← Real.exp_add, mul_one, mul_one]
  ring_nf

/-- Lower tail of the discrete Laplace distribution with scale `1 / ε`:
`Pr[Y ≤ -m] = exp (-ε (m - 1)) / (exp ε + 1)` for every natural `m`
[CanonneKamathSteinke2020, Lemma 30]. -/
theorem discreteLaplace_toOuterMeasure_Iic {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    (discreteLaplace (1 / ε) (by positivity)).toOuterMeasure (Set.Iic (-(m : ℤ))) =
      ENNReal.ofReal (Real.exp (-ε * (m - 1)) / (Real.exp ε + 1)) := by
  rw [← discreteLaplace_toOuterMeasure_Ici hε m, discreteLaplace,
    twoSidedGeometric_toOuterMeasure_Iic, twoSidedGeometric_toOuterMeasure_Ici]

/-- Two-sided tail of the discrete Laplace distribution with scale `t`:
`Pr[|Y| ≥ m] = 2 exp (-m / t) / (1 + exp (-1 / t))` for every positive natural `m`. -/
theorem discreteLaplace_toOuterMeasure_le_natAbs (t : ℝ) (ht : 0 < t) {m : ℕ} (hm : m ≠ 0) :
    (discreteLaplace t ht).toOuterMeasure {z | m ≤ z.natAbs} =
      ENNReal.ofReal (2 * Real.exp (-m / t) / (1 + Real.exp (-1 / t))) := by
  rw [show -(m : ℝ) / t = m * (-1 / t) by ring, Real.exp_nat_mul]
  exact twoSidedGeometric_toOuterMeasure_le_natAbs _ _ hm

/-- The discrete Laplace distribution with scale `t` exceeds `a ≥ 0` in absolute value with
probability at most `2 exp (-a / t)`. -/
theorem discreteLaplace_toOuterMeasure_lt_abs_le (t : ℝ) (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a) :
    (discreteLaplace t ht).toOuterMeasure {z | a < |(z : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-a / t)) := by
  rw [show {z : ℤ | a < |(z : ℝ)|} = {z | ⌊a⌋₊ + 1 ≤ z.natAbs} from Set.ext fun z => by
      simp only [Set.mem_ofPred_eq, ← Int.cast_abs, ← Nat.cast_natAbs, ← Nat.floor_lt ha,
        Nat.lt_iff_add_one_le],
    discreteLaplace_toOuterMeasure_le_natAbs t ht (Nat.succ_ne_zero _)]
  refine ENNReal.ofReal_le_ofReal <| (div_le_self (by positivity)
    (by linarith [Real.exp_pos (-1 / t)])).trans ?_
  have : a ≤ ((⌊a⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_floor_add_one a).le
  gcongr

/-- Shifting the discrete Laplace distribution with scale `t` by at most `Δ` changes each mass by
a factor of at most `exp (Δ / t)`. -/
theorem discreteLaplace_apply_le (t : ℝ) (ht : 0 < t) {Δ : ℝ} (z d : ℤ) (hd : |(d : ℝ)| ≤ Δ) :
    discreteLaplace t ht z ≤ ENNReal.ofReal (Real.exp (Δ / t)) * discreteLaplace t ht (z + d) := by
  rw [discreteLaplace]
  simpa only [Real.log_inv, Real.log_exp, show Δ * -(-1 / t) = Δ / t by ring] using
    twoSidedGeometric_apply_le (Real.exp_pos (-1 / t))
      (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) ht)) z d hd

end DiscreteLaplace

end Cslib.Privacy
