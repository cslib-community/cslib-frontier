/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Flip
public import CslibFrontier.Probability.Minimax.LeCam
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Assouad's hypercube minimax lower-bound lemma

**Assouad's lemma** lower-bounds minimax estimation risk over a hypercube-indexed family
`{P_v : v ∈ (ι → Bool)}` when the loss decomposes coordinatewise (`∑ i, coordLoss i t v ≤ loss t v`)
and flipping coordinate `i` (`Function.update v i (!v i)`) separates the `i`-th coordinate loss by
`sep ≤ coordLoss i t v + coordLoss i t (Function.update v i (!v i))` ([Tsybakov2009], Section 2.7.2,
Theorem 2.12).

Pairing hypercube vertices along each coordinate involution
(`Cslib.BitString.sum_update_not`) and applying our exact two-point Le Cam sum inequality
(`Cslib.Probability.leCam_measure_add_ge`, `Cslib.Probability.PMF.leCam_add_ge`) yields the sharp
constant `sep / 2` per coordinate both for arbitrary probability measures (`Measure α`) and for
finite distributions (`PMF X`), including randomized estimators and `n`-sample i.i.d. observations.

As a concrete high-dimensional application, this file proves the minimax estimation lower bounds for
`d`-dimensional product-Bernoulli mean vectors `p : ι → I` from `n ≥ 1` i.i.d. observations:
* **`Ω(|ι| / n)` under squared `ℓ₂` loss**
  (`Cslib.Probability.PMF.product_bernoulli_minimax_sq_l2_lower_bound`): worst-case risk at least
  `|ι| / (72 n)`.
* **`Ω(|ι| / √n)` under `ℓ₁` loss**
  (`Cslib.Probability.PMF.product_bernoulli_minimax_l1_lower_bound`): worst-case risk at least
  `|ι| / (12 √n)`.

## Main results

* `Cslib.Probability.assouad_measure_avg_ge`, `Cslib.Probability.assouad_measure_exists_ge`,
  `Cslib.Probability.assouad_measure_exists_ge_of_klDiv_le`: measure-theoretic Assouad's lemma.
* `Cslib.Probability.PMF.assouad_avg_ge`, `Cslib.Probability.PMF.assouad_exists_ge`,
  `Cslib.Probability.PMF.assouad_randomized_exists_ge`: finite-`PMF` Assouad's lemma for
  deterministic and randomized estimators.
* `Cslib.Probability.PMF.assouad_exists_ge_of_dist_le`,
  `Cslib.Probability.PMF.assouad_exists_ge_of_klDiv_le`,
  `Cslib.Probability.PMF.assouad_iid_exists_ge_of_klDiv_le`: edge-TV, edge-KL, and `n`-sample i.i.d.
  forms.
* `Cslib.Probability.PMF.product_bernoulli_minimax_sq_l2_lower_bound`,
  `Cslib.Probability.PMF.product_bernoulli_minimax_l1_lower_bound`: `Ω(|ι| / n)` and `Ω(|ι| / √n)`
  minimax lower bounds for product-Bernoulli mean estimation.

## References

* [A. B. Tsybakov, *Introduction to Nonparametric Estimation*][Tsybakov2009], Section 2.7.2,
  Theorem 2.12.
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory InformationTheory Finset Cslib.BitString
open scoped BigOperators ENNReal unitInterval

private theorem exists_cube_ge_of_avg_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} {c : ℝ}
    (h : c ≤ (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ v : ι → Bool, f v) :
    ∃ v : ι → Bool, c ≤ f v := by
  have hsum : ∑ _ : ι → Bool, c ≤ ∑ v : ι → Bool, f v := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (le_inv_mul_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)).mp h
  exact Exists.imp (fun _ => And.right) (Finset.exists_le_of_sum_le Finset.univ_nonempty hsum)

private theorem hypercube_sum_coord_avg_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {sep : ℝ} {d F : ι → (ι → Bool) → ℝ}
    (hpair : ∀ i v, sep * (1 - d i v) ≤ F i v + F i (Function.update v i (!v i))) :
    (sep / 2) * ∑ i : ι, (1 - (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ v : ι → Bool, d i v) ≤
      (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ v : ι → Bool, ∑ i : ι, F i v := by
  have hcard_pos : (0 : ℝ) < Fintype.card (ι → Bool) := Nat.cast_pos.mpr Fintype.card_pos
  have hcoord (i : ι) :
      (sep / 2) * (1 - (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ v : ι → Bool, d i v) ≤
        (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ v : ι → Bool, F i v := by
    have hsum_pair := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hpair i v
    rw [Finset.sum_add_distrib, sum_update_not i (F i)] at hsum_pair
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum] at hsum_pair
    have hdiv := mul_le_mul_of_nonneg_left hsum_pair (inv_nonneg.mpr hcard_pos.le)
    have hsimp : (Fintype.card (ι → Bool) : ℝ)⁻¹ *
        ((Fintype.card (ι → Bool) : ℝ) * sep - sep * ∑ v : ι → Bool, d i v) =
        2 * ((sep / 2) * (1 - (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ v : ι → Bool, d i v)) := by
      field_simp
    rw [hsimp] at hdiv
    linarith
  have hsum_i := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcoord i
  rwa [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm] at hsum_i

private theorem card_mul_le_sum_one_sub_avg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → (ι → Bool) → ℝ} {sep τ : ℝ} (hsep0 : 0 ≤ sep) (hd : ∀ i w, d i w ≤ τ) :
    (Fintype.card ι : ℝ) * (sep / 2) * (1 - τ) ≤
      (sep / 2) * ∑ i : ι, (1 - (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ w : ι → Bool, d i w) := by
  have hpos : (0 : ℝ) < Fintype.card (ι → Bool) := Nat.cast_pos.mpr Fintype.card_pos
  have havg (i : ι) : (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ w : ι → Bool, d i w ≤ τ := by
    calc (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ w : ι → Bool, d i w
        ≤ (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ _ : ι → Bool, τ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => hd i w)
            (inv_nonneg.mpr hpos.le)
      _ = τ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hpos.ne']
  calc (Fintype.card ι : ℝ) * (sep / 2) * (1 - τ)
      = (sep / 2) * ∑ _ : ι, (1 - τ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ (sep / 2) * ∑ i : ι, (1 - (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ w : ι → Bool, d i w) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => sub_le_sub_left (havg i) 1)
          (by positivity)

/-! ### Measure-theoretic Assouad's hypercube lemma -/

section Measure

variable {ι α T : Type*} [Fintype ι] [DecidableEq ι] {mα : MeasurableSpace α}

/-- **Measure-theoretic Assouad's lemma (hypercube average form)**: if
`∑ i, coordLoss i t v ≤ loss t v` and flipping coordinate `i` gives
`sep ≤ coordLoss i t v + coordLoss i t (update v i (!v i))`, then the hypercube-average risk is at
least `(sep / 2) · ∑ i, (1 - |{0,1}^ι|⁻¹ · ∑ v, tvDist (μ v) (μ (update v i (!v i))) / 2)`. -/
theorem assouad_measure_avg_ge (μ : (ι → Bool) → Measure α) [∀ v, IsProbabilityMeasure (μ v)]
    {coordLoss : ι → T → (ι → Bool) → ℝ} {loss : T → (ι → Bool) → ℝ} {sep : ℝ}
    (hcoord_nn : ∀ i t v, 0 ≤ coordLoss i t v)
    (hsum_le : ∀ t v, ∑ i : ι, coordLoss i t v ≤ loss t v)
    (hsep : ∀ i t v, sep ≤ coordLoss i t v + coordLoss i t (Function.update v i (!v i)))
    (est : α → T)
    (hint_coord : ∀ i v, Integrable (fun x => coordLoss i (est x) v) (μ v))
    (hint_loss : ∀ v, Integrable (fun x => loss (est x) v) (μ v)) :
    (sep / 2) * ∑ i : ι, (1 - (Fintype.card (ι → Bool) : ℝ)⁻¹ *
        ∑ v : ι → Bool, tvDist (μ v) (μ (Function.update v i (!v i))) / 2) ≤
      (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ v : ι → Bool, ∫ x, loss (est x) v ∂(μ v) := by
  refine (hypercube_sum_coord_avg_ge
    (d := fun i v => tvDist (μ v) (μ (Function.update v i (!v i))) / 2)
    (F := fun i v => ∫ x, coordLoss i (est x) v ∂(μ v)) fun i v =>
      leCam_measure_add_ge (μ v) (μ (Function.update v i (!v i)))
        (fun x => hcoord_nn i (est x) v)
        (fun x => hcoord_nn i (est x) (Function.update v i (!v i)))
        (hint_coord i v) (hint_coord i (Function.update v i (!v i)))
        (fun x => hsep i (est x) v)).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => ?_)
      (inv_nonneg.mpr (Nat.cast_nonneg _)))
  rw [← integral_finsetSum Finset.univ fun i _ => hint_coord i v]
  exact integral_mono (integrable_finsetSum Finset.univ fun i _ => hint_coord i v)
    (hint_loss v) fun x => hsum_le (est x) v

/-- **Measure-theoretic Assouad's lemma (worst-case vertex form)**. -/
theorem assouad_measure_exists_ge (μ : (ι → Bool) → Measure α) [∀ v, IsProbabilityMeasure (μ v)]
    {coordLoss : ι → T → (ι → Bool) → ℝ} {loss : T → (ι → Bool) → ℝ} {sep : ℝ}
    (hcoord_nn : ∀ i t v, 0 ≤ coordLoss i t v)
    (hsum_le : ∀ t v, ∑ i : ι, coordLoss i t v ≤ loss t v)
    (hsep : ∀ i t v, sep ≤ coordLoss i t v + coordLoss i t (Function.update v i (!v i)))
    (est : α → T)
    (hint_coord : ∀ i v, Integrable (fun x => coordLoss i (est x) v) (μ v))
    (hint_loss : ∀ v, Integrable (fun x => loss (est x) v) (μ v)) :
    ∃ v : ι → Bool,
      (sep / 2) * ∑ i : ι, (1 - (Fintype.card (ι → Bool) : ℝ)⁻¹ *
          ∑ w : ι → Bool, tvDist (μ w) (μ (Function.update w i (!w i))) / 2) ≤
        ∫ x, loss (est x) v ∂(μ v) :=
  exists_cube_ge_of_avg_ge
    (assouad_measure_avg_ge μ hcoord_nn hsum_le hsep est hint_coord hint_loss)

/-- **Measure-theoretic Assouad–Pinsker bound**: if `klDiv (μ v) (μ (update v i (!v i))) ≤ ofReal β`
along every hypercube edge (`0 ≤ sep`, `0 ≤ β`), then some vertex `v` incurs expected loss at least
`|ι| · (sep / 2) · (1 - √(β / 2))`. -/
theorem assouad_measure_exists_ge_of_klDiv_le (μ : (ι → Bool) → Measure α)
    [∀ v, IsProbabilityMeasure (μ v)]
    {coordLoss : ι → T → (ι → Bool) → ℝ} {loss : T → (ι → Bool) → ℝ} {sep β : ℝ}
    (hsep0 : 0 ≤ sep) (hβ0 : 0 ≤ β)
    (hkl : ∀ i v, klDiv (μ v) (μ (Function.update v i (!v i))) ≤ ENNReal.ofReal β)
    (hcoord_nn : ∀ i t v, 0 ≤ coordLoss i t v)
    (hsum_le : ∀ t v, ∑ i : ι, coordLoss i t v ≤ loss t v)
    (hsep : ∀ i t v, sep ≤ coordLoss i t v + coordLoss i t (Function.update v i (!v i)))
    (est : α → T)
    (hint_coord : ∀ i v, Integrable (fun x => coordLoss i (est x) v) (μ v))
    (hint_loss : ∀ v, Integrable (fun x => loss (est x) v) (μ v)) :
    ∃ v : ι → Bool,
      (Fintype.card ι : ℝ) * (sep / 2) * (1 - Real.sqrt (β / 2)) ≤
        ∫ x, loss (est x) v ∂(μ v) := by
  obtain ⟨v, hv⟩ := assouad_measure_exists_ge μ hcoord_nn hsum_le hsep est hint_coord hint_loss
  refine ⟨v, (card_mul_le_sum_one_sub_avg hsep0 fun i w => ?_).trans hv⟩
  have hsq : tvDist (μ w) (μ (Function.update w i (!w i))) ^ 2 / 2 ≤ β :=
    (ENNReal.ofReal_le_ofReal_iff hβ0).mp
      ((ofReal_tvDist_sq_div_two_le_klDiv _ _).trans (hkl i w))
  exact Real.le_sqrt_of_sq_le (by linarith)

end Measure

/-! ### Finite-distribution (`PMF`) Assouad's lemma and `d`-dimensional Bernoulli minimax rates -/

namespace PMF

section Finite

variable {ι X T : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]

/-- **Assouad's lemma on `PMF` (hypercube average form)**: the hypercube-average expected risk is at
least `(sep / 2) · ∑ i, (1 - |{0,1}^ι|⁻¹ · ∑ v, dist (P v) (P (update v i (!v i))))`. -/
theorem assouad_avg_ge (P : (ι → Bool) → PMF X)
    {coordLoss : ι → T → (ι → Bool) → ℝ} {loss : T → (ι → Bool) → ℝ} {sep : ℝ}
    (hcoord_nn : ∀ i t v, 0 ≤ coordLoss i t v)
    (hsum_le : ∀ t v, ∑ i : ι, coordLoss i t v ≤ loss t v)
    (hsep : ∀ i t v, sep ≤ coordLoss i t v + coordLoss i t (Function.update v i (!v i)))
    (est : X → T) :
    (sep / 2) * ∑ i : ι, (1 - (Fintype.card (ι → Bool) : ℝ)⁻¹ *
        ∑ v : ι → Bool, dist (P v) (P (Function.update v i (!v i)))) ≤
      (Fintype.card (ι → Bool) : ℝ)⁻¹ *
        ∑ v : ι → Bool, ∑ x : X, (P v x).toReal * loss (est x) v := by
  let _ : MeasurableSpace X := ⊤
  simpa only [PMF.integral_eq_sum, smul_eq_mul, dist_eq_tvDist_toMeasure_div_two] using
    assouad_measure_avg_ge (fun v => (P v).toMeasure) hcoord_nn hsum_le hsep est
      (fun _ _ => Integrable.of_finite) (fun _ => Integrable.of_finite)

/-- **Assouad's lemma on `PMF` (worst-case vertex form)**. -/
theorem assouad_exists_ge (P : (ι → Bool) → PMF X)
    {coordLoss : ι → T → (ι → Bool) → ℝ} {loss : T → (ι → Bool) → ℝ} {sep : ℝ}
    (hcoord_nn : ∀ i t v, 0 ≤ coordLoss i t v)
    (hsum_le : ∀ t v, ∑ i : ι, coordLoss i t v ≤ loss t v)
    (hsep : ∀ i t v, sep ≤ coordLoss i t v + coordLoss i t (Function.update v i (!v i)))
    (est : X → T) :
    ∃ v : ι → Bool,
      (sep / 2) * ∑ i : ι, (1 - (Fintype.card (ι → Bool) : ℝ)⁻¹ *
          ∑ w : ι → Bool, dist (P w) (P (Function.update w i (!w i)))) ≤
        ∑ x : X, (P v x).toReal * loss (est x) v :=
  exists_cube_ge_of_avg_ge (assouad_avg_ge P hcoord_nn hsum_le hsep est)

/-- **Assouad's lemma for randomized estimators** `est : X → PMF T`. -/
theorem assouad_randomized_exists_ge [Fintype T] (P : (ι → Bool) → PMF X)
    {coordLoss : ι → T → (ι → Bool) → ℝ} {loss : T → (ι → Bool) → ℝ} {sep : ℝ}
    (hcoord_nn : ∀ i t v, 0 ≤ coordLoss i t v)
    (hsum_le : ∀ t v, ∑ i : ι, coordLoss i t v ≤ loss t v)
    (hsep : ∀ i t v, sep ≤ coordLoss i t v + coordLoss i t (Function.update v i (!v i)))
    (est : X → PMF T) :
    ∃ v : ι → Bool,
      (sep / 2) * ∑ i : ι, (1 - (Fintype.card (ι → Bool) : ℝ)⁻¹ *
          ∑ w : ι → Bool, dist (P w) (P (Function.update w i (!w i)))) ≤
        ∑ x : X, (P v x).toReal * ∑ t : T, (est x t).toReal * loss t v := by
  refine assouad_exists_ge P
    (coordLoss := fun i (q : PMF T) v => ∑ t : T, (q t).toReal * coordLoss i t v)
    (loss := fun (q : PMF T) v => ∑ t : T, (q t).toReal * loss t v)
    (fun i q v => Finset.sum_nonneg fun t _ => mul_nonneg ENNReal.toReal_nonneg (hcoord_nn i t v))
    (fun q v => ?_) (fun i q v => ?_) est
  · rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hsum_le t v) ENNReal.toReal_nonneg
  · rw [← Finset.sum_add_distrib]
    calc sep = ∑ t : T, (q t).toReal * sep := by
          rw [← Finset.sum_mul, sum_toReal, one_mul]
      _ ≤ ∑ t : T, ((q t).toReal * coordLoss i t v +
            (q t).toReal * coordLoss i t (Function.update v i (!v i))) := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (hsep i t v) ENNReal.toReal_nonneg

/-- **Uniform edge-distance Assouad bound**: if `dist (P v) (P (update v i (!v i))) ≤ τ` along every
hypercube edge (`0 ≤ sep`), then some `v` incurs expected loss `≥ |ι| · (sep / 2) · (1 - τ)`. -/
theorem assouad_exists_ge_of_dist_le (P : (ι → Bool) → PMF X)
    {coordLoss : ι → T → (ι → Bool) → ℝ} {loss : T → (ι → Bool) → ℝ} {sep τ : ℝ}
    (hsep0 : 0 ≤ sep)
    (hdist : ∀ i v, dist (P v) (P (Function.update v i (!v i))) ≤ τ)
    (hcoord_nn : ∀ i t v, 0 ≤ coordLoss i t v)
    (hsum_le : ∀ t v, ∑ i : ι, coordLoss i t v ≤ loss t v)
    (hsep : ∀ i t v, sep ≤ coordLoss i t v + coordLoss i t (Function.update v i (!v i)))
    (est : X → T) :
    ∃ v : ι → Bool,
      (Fintype.card ι : ℝ) * (sep / 2) * (1 - τ) ≤ ∑ x : X, (P v x).toReal * loss (est x) v := by
  obtain ⟨v, hv⟩ := assouad_exists_ge P hcoord_nn hsum_le hsep est
  exact ⟨v, (card_mul_le_sum_one_sub_avg hsep0 hdist).trans hv⟩

/-- **Assouad–Pinsker bound on `PMF`**: if `D(P v ‖ P (update v i (!v i))) ≤ β` along every
hypercube edge (`0 ≤ sep`), then some `v` incurs expected loss at least
`|ι| · (sep / 2) · (1 - √(β / 2))`. -/
theorem assouad_exists_ge_of_klDiv_le [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : (ι → Bool) → PMF X)
    {coordLoss : ι → T → (ι → Bool) → ℝ} {loss : T → (ι → Bool) → ℝ} {sep β : ℝ}
    (hsep0 : 0 ≤ sep)
    (hsupp : ∀ i v, (P v).support ⊆ (P (Function.update v i (!v i))).support)
    (hkl : ∀ i v, (klDiv (P v).toMeasure (P (Function.update v i (!v i))).toMeasure).toReal ≤ β)
    (hcoord_nn : ∀ i t v, 0 ≤ coordLoss i t v)
    (hsum_le : ∀ t v, ∑ i : ι, coordLoss i t v ≤ loss t v)
    (hsep : ∀ i t v, sep ≤ coordLoss i t v + coordLoss i t (Function.update v i (!v i)))
    (est : X → T) :
    ∃ v : ι → Bool,
      (Fintype.card ι : ℝ) * (sep / 2) * (1 - Real.sqrt (β / 2)) ≤
        ∑ x : X, (P v x).toReal * loss (est x) v := by
  refine assouad_exists_ge_of_dist_le P hsep0 (fun i v => ?_) hcoord_nn hsum_le hsep est
  exact (dist_le_sqrt_toReal_klDiv_div_two (hsupp i v)).trans
    (Real.sqrt_le_sqrt (by linarith [hkl i v]))

/-- **I.i.d. `n`-sample Assouad–Pinsker bound**: if single-sample edge divergences satisfy
`D(P v ‖ P (update v i (!v i))) ≤ β`, then from `n` i.i.d. observations some `v : ι → Bool` incurs
expected loss at least `|ι| · (sep / 2) · (1 - √(n · β / 2))`. -/
theorem assouad_iid_exists_ge_of_klDiv_le [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : (ι → Bool) → PMF X) (n : ℕ)
    {coordLoss : ι → T → (ι → Bool) → ℝ} {loss : T → (ι → Bool) → ℝ} {sep β : ℝ}
    (hsep0 : 0 ≤ sep)
    (hsupp : ∀ i v, (P v).support ⊆ (P (Function.update v i (!v i))).support)
    (hkl : ∀ i v, (klDiv (P v).toMeasure (P (Function.update v i (!v i))).toMeasure).toReal ≤ β)
    (hcoord_nn : ∀ i t v, 0 ≤ coordLoss i t v)
    (hsum_le : ∀ t v, ∑ i : ι, coordLoss i t v ≤ loss t v)
    (hsep : ∀ i t v, sep ≤ coordLoss i t v + coordLoss i t (Function.update v i (!v i)))
    (est : (Fin n → X) → T) :
    ∃ v : ι → Bool,
      (Fintype.card ι : ℝ) * (sep / 2) * (1 - Real.sqrt (n * β / 2)) ≤
        ∑ x : Fin n → X, (iid (P v) n x).toReal * loss (est x) v := by
  refine assouad_exists_ge_of_klDiv_le (fun v => iid (P v) n) hsep0
    (fun i v => support_iid_subset (hsupp i v) n) (fun i v => ?_) hcoord_nn hsum_le hsep est
  rw [toReal_klDiv_iid (hsupp i v) n]
  exact mul_le_mul_of_nonneg_left (hkl i v) (Nat.cast_nonneg n)

end Finite

/-! ### High-dimensional product-Bernoulli mean estimation minimax lower bounds -/

section ProductBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_product_bernoulli_edge_klDiv_le {n : ℕ} (hn : 0 < n) :
    let δ : ℝ := 1 / (6 * Real.sqrt n)
    ∃ pBit : Bool → I,
      (pBit false : ℝ) = 1 / 2 - δ ∧
      (pBit true : ℝ) = 1 / 2 + δ ∧
      (∀ (i : ι) (v : ι → Bool),
        (pi fun j => coin (pBit (v j))).support ⊆
          (pi fun j => coin (pBit (Function.update v i (!v i) j))).support) ∧
      ∀ (i : ι) (v : ι → Bool),
        (klDiv (pi fun j => coin (pBit (v j))).toMeasure
            (pi fun j => coin (pBit (Function.update v i (!v i) j))).toMeasure).toReal ≤
          1 / (2 * (n : ℝ)) := by
  obtain ⟨pBit, hpF, hpT, hsupp, hkl⟩ := exists_coin_perturbed_klDiv_le hn
  refine ⟨pBit, hpF, hpT,
    fun i v => support_pi_subset_iff.mpr fun j => hsupp (v j) (Function.update v i (!v i) j),
    fun i v => ?_⟩
  rw [toReal_klDiv_pi fun j => hsupp (v j) (Function.update v i (!v i) j)]
  have hterm (j : ι) :
      (klDiv (coin (pBit (v j))).toMeasure
          (coin (pBit (Function.update v i (!v i) j))).toMeasure).toReal =
        if j = i then
          (klDiv (coin (pBit (v i))).toMeasure (coin (pBit (!v i))).toMeasure).toReal
        else 0 := by
    by_cases hji : j = i <;> simp [hji]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact hkl (v i)

private theorem sqrt_mul_one_div_two_mul_div_two {n : ℕ} (hn : 0 < n) :
    Real.sqrt ((n : ℝ) * (1 / (2 * (n : ℝ))) / 2) = 1 / 2 := by
  have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq : (n : ℝ) * (1 / (2 * (n : ℝ))) / 2 = (1 / 2) ^ 2 := by field_simp
  rw [hq, Real.sqrt_sq (by norm_num)]

/-- **`Ω(|ι| / n)` minimax lower bound for `d`-dimensional product-Bernoulli mean estimation under
squared `ℓ₂` loss**: for every `n ≥ 1` and every estimator `est : (Fin n → ι → Bool) → (ι → ℝ)`,
some mean vector `p : ι → I` incurs expected squared `ℓ₂` error at least `|ι| / (72 n)`. -/
theorem product_bernoulli_minimax_sq_l2_lower_bound {n : ℕ} (hn : 0 < n)
    (est : (Fin n → ι → Bool) → (ι → ℝ)) :
    ∃ p : ι → I, (Fintype.card ι : ℝ) / (72 * (n : ℝ)) ≤
      ∑ x : Fin n → ι → Bool,
        (iid (pi fun i => coin (p i)) n x).toReal * ∑ i : ι, (est x i - (p i : ℝ)) ^ 2 := by
  obtain ⟨pBit, hpF, hpT, hsupp, hkl⟩ := exists_product_bernoulli_edge_klDiv_le (ι := ι) hn
  set δ : ℝ := 1 / (6 * Real.sqrt n)
  have hδ_sq : δ ^ 2 = 1 / (36 * (n : ℝ)) := by
    simp only [δ, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; ring
  obtain ⟨v, hv⟩ := assouad_iid_exists_ge_of_klDiv_le
    (P := fun v : ι → Bool => pi fun j => coin (pBit (v j))) n
    (coordLoss := fun i (t : ι → ℝ) v => (t i - (pBit (v i) : ℝ)) ^ 2)
    (loss := fun (t : ι → ℝ) v => ∑ i : ι, (t i - (pBit (v i) : ℝ)) ^ 2)
    (sep := 2 * δ ^ 2) (β := 1 / (2 * (n : ℝ))) (by positivity) hsupp hkl
    (fun _ _ _ => sq_nonneg _) (fun _ _ => le_rfl)
    (fun i t v => by
      cases v i <;> simp only [Function.update_self, Bool.not_false, Bool.not_true, hpF, hpT] <;>
        nlinarith [sq_nonneg (t i - 1 / 2)])
    est
  refine ⟨fun i => pBit (v i), le_trans ?_ hv⟩
  rw [sqrt_mul_one_div_two_mul_div_two hn, hδ_sq]
  exact le_of_eq (by ring)

/-- **`Ω(|ι| / √n)` minimax lower bound for `d`-dimensional product-Bernoulli mean estimation under
`ℓ₁` loss**: for every `n ≥ 1` and every estimator `est : (Fin n → ι → Bool) → (ι → ℝ)`,
some mean vector `p : ι → I` incurs expected `ℓ₁` error at least `|ι| / (12 √n)`. -/
theorem product_bernoulli_minimax_l1_lower_bound {n : ℕ} (hn : 0 < n)
    (est : (Fin n → ι → Bool) → (ι → ℝ)) :
    ∃ p : ι → I, (Fintype.card ι : ℝ) / (12 * Real.sqrt n) ≤
      ∑ x : Fin n → ι → Bool,
        (iid (pi fun i => coin (p i)) n x).toReal * ∑ i : ι, |est x i - (p i : ℝ)| := by
  obtain ⟨pBit, hpF, hpT, hsupp, hkl⟩ := exists_product_bernoulli_edge_klDiv_le (ι := ι) hn
  set δ : ℝ := 1 / (6 * Real.sqrt n)
  obtain ⟨v, hv⟩ := assouad_iid_exists_ge_of_klDiv_le
    (P := fun v : ι → Bool => pi fun j => coin (pBit (v j))) n
    (coordLoss := fun i (t : ι → ℝ) v => |t i - (pBit (v i) : ℝ)|)
    (loss := fun (t : ι → ℝ) v => ∑ i : ι, |t i - (pBit (v i) : ℝ)|)
    (sep := 2 * δ) (β := 1 / (2 * (n : ℝ))) (by positivity) hsupp hkl
    (fun _ _ _ => abs_nonneg _) (fun _ _ => le_rfl)
    (fun i t v => by
      cases v i <;> simp only [Function.update_self, Bool.not_false, Bool.not_true, hpF, hpT] <;>
        linarith [le_abs_self (t i - (1 / 2 - δ)), neg_le_abs (t i - (1 / 2 + δ))])
    est
  refine ⟨fun i => pBit (v i), le_trans ?_ hv⟩
  rw [sqrt_mul_one_div_two_mul_div_two hn]
  exact le_of_eq (by simp only [δ]; ring)

end ProductBernoulli

end PMF

end Cslib.Probability
