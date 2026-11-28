/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Frontier.Linear.DirectedShift
public import CslibFrontier.Computability.Circuit.Frontier.Linear.Unconditional
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Coefficient
import CslibFrontier.Foundations.Probability.Gaussian.QuadrantDeriv
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Checked clients and non-vacuity witnesses for unbalanced linear-map cut demands and directed
Gaussian divergence shifts (`4.2170 N`). -/

public section

open Cslib.Circuits Cslib.Circuits.Frontier Matrix MeasureTheory ProbabilityTheory Real Set Filter

namespace CslibFrontierTests.FrontierDirectedLinear

/-! ### 1. Exact numerical comparisons (`4.0815 N < 4.2170 N`) -/

/-- Shifted `VertexGaussian` (`> 4.2170 N`) strictly beats unshifted `VertexGaussian`
(`1 + 1 / degreeCoefficient 3 ≈ 4.0815 N`). -/
theorem unshifted_lt_shifted_coeff : 1 + 1 / Gaussian.degreeCoefficient 3 < 4217 / 1000 := by
  have hcos : 2 * √2 / 3 ≤ cos (338 / 1000) := by
    have hs2_hi : √2 < 1414214 / 1000000 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
    have hlo := one_sub_sq_div_two_le_cos (x := 338 / 1000)
    linarith
  have harc : (338 / 1000 : ℝ) ≤ arccos (2 * √2 / 3) := by
    calc (338 / 1000 : ℝ) = arccos (cos (338 / 1000)) :=
          (arccos_cos (by norm_num) (by linarith [pi_gt_d20])).symm
      _ ≤ arccos (2 * √2 / 3) := arccos_le_arccos hcos
  have hpi_hi : π < 31416 / 10000 := by linarith [pi_lt_d20]
  have hdeg_eq : Gaussian.degreeCoefficient 3 = 3 * arccos (2 * √2 / 3) / π := by
    unfold Gaussian.degreeCoefficient Gaussian.vertexCoefficient Gaussian.vertexCorrelation
    norm_num
    ring
  have hdeg_pos : 0 < Gaussian.degreeCoefficient 3 := Gaussian.degreeCoefficient_pos (by norm_num)
  have hdeg_lo : (1000 / 3217 : ℝ) < Gaussian.degreeCoefficient 3 := by
    rw [hdeg_eq, lt_div_iff₀ pi_pos]
    linarith [harc, hpi_hi]
  have hinv : 1 / Gaussian.degreeCoefficient 3 < 3217 / 1000 := by
    have h1 := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1000 / 3217) hdeg_lo
    norm_num at h1
    rwa [one_div]
  linarith

example :
    (4217 / 1000 : ℝ) <
      1 + cdf (gaussianReal 0 1) (-1 / 20) /
        (2 * DirectedShift.shiftedSupply (2 * √2 / 3) (1 / 20)) :=
  DirectedShift.four_two_one_seven_lt_shifted_coeff

example (a b : ℝ) :
    (correlatedGaussian (1 / 2)).real {p | p.1 ≤ a ∧ p.2 ≤ b} ≤
      (correlatedGaussian (2 * √2 / 3)).real {p | p.1 ≤ a ∧ p.2 ≤ b} := by
  have hs2_lo : (7 / 5 : ℝ) < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs2_hi : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  exact measureReal_correlatedGaussian_le_and_le_mono (by norm_num) (by linarith) (by linarith) a b

example (a b : ℝ) :
    (correlatedGaussian (-4 / 5)).real {p | p.1 ≤ a ∧ p.2 ≤ b} ≤
      (correlatedGaussian (1 / 2)).real {p | p.1 ≤ a ∧ p.2 ≤ b} :=
  measureReal_correlatedGaussian_le_and_le_mono (by norm_num) (by norm_num) (by norm_num) a b

example (a b : ℝ) :
    (correlatedGaussian (1 / 2)).real {p | a < p.1 ∧ p.2 ≤ b} ≤
      (correlatedGaussian (-4 / 5)).real {p | a < p.1 ∧ p.2 ≤ b} :=
  measureReal_correlatedGaussian_gt_and_le_anti (by norm_num) (by norm_num) (by norm_num) a b

example (α β : ℝ) :
    gaussianQuadrant (-4 / 5) α β ≤ gaussianQuadrant (1 / 2) α β :=
  monotoneOn_gaussianQuadrant α β (by norm_num) (by norm_num) (by norm_num)

example :
    gaussianQuadrant (-1 / 2) (2 / 3) (3 / 4) =
      1 - 1 / 3 - 1 / 4 + gaussianQuadrant (-1 / 2) (1 / 3) (1 / 4) := by
  have h := gaussianQuadrant_one_sub_one_sub (ρ := -1 / 2) (α := 1 / 3) (β := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-! ### 2. Concrete directed cubic theta multigraph (with antiparallel 2-cycles) -/

/-- Oriented cubic theta multigraph: edges `0, 1` run `false → true` (`σ(false) = +1`), edge `2`
runs `true → false` (`σ(true) = -1`), forming two directed 2-cycles. -/
private def dirTheta : Multigraph Bool (Fin 3) where
  src e := if e.val < 2 then false else true
  tgt e := if e.val < 2 then true else false

private theorem dirTheta_loopless : dirTheta.Loopless := by
  intro e
  fin_cases e <;> decide

private theorem dirTheta_cubic (v : Bool) : (dirTheta.incidenceSet v).ncard = 3 := by
  have heq : dirTheta.incidenceSet v = univ := by
    ext e
    cases v <;> fin_cases e <;> simp [Multigraph.incidenceSet, dirTheta]
  rw [heq, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

example (v : Bool) : (1 : ℤ) ≤ |dirTheta.divergence v| :=
  dirTheta.one_le_abs_divergence_of_cubic dirTheta_loopless dirTheta_cubic v

example (P : Set Bool) [DecidablePred (· ∈ P)] :
    (2 * (dirTheta.inCut P).ncard : ℤ) + ∑ v : Bool, (if v ∈ P then dirTheta.divergence v else 0) =
      ((dirTheta.edgeCut P).ncard : ℤ) :=
  dirTheta.two_mul_ncard_inCut_add_sum_divergence dirTheta_loopless P

/-! ### 3. Non-vacuity witness for `exists_pos_shifted_inCut_ratio_lt` -/

/-- Concrete `(4 / 5)`-correlated Gaussian scores on `dirTheta` satisfying every hypothesis of
`DirectedShift.exists_pos_shifted_inCut_ratio_lt` (including `c 0 < 1 / 2` and `HasDerivAt c 0 0`),
plus the tie-cusp witness `DirectedShift.tie_mem_edgeCut_shiftedCut`. -/
example {M : Bool → ℝ} {d : ℝ} (hsrc : 0 < dirTheta.divergence false)
    (htgt : ¬ 0 < dirTheta.divergence true) (htie : M false = M true)
    (hlo : -d < M false) (hhi : M false ≤ d) :
    (0 : Fin 3) ∈ dirTheta.edgeCut (DirectedShift.shiftedCut dirTheta M d) :=
  DirectedShift.tie_mem_edgeCut_shiftedCut dirTheta M hsrc htgt htie hlo hhi

example :
    let P := correlatedGaussian (4 / 5)
    let M : ℝ × ℝ → Bool → ℝ := fun p v => if v then p.2 else p.1
    ∃ d > 0, 0 < cdf (gaussianReal 0 1) (-d) ∧
      ((∑ e : Fin 3, P.real {ω | e ∈ dirTheta.inCut (DirectedShift.shiftedCut dirTheta (M ω) d)}) /
          Fintype.card Bool) / cdf (gaussianReal 0 1) (-d) <
        (∑ e : Fin 3,
          P.real {ω | e ∈ dirTheta.edgeCut (DirectedShift.shiftedCut dirTheta (M ω) 0)}) /
          Fintype.card Bool := by
  set P := correlatedGaussian (4 / 5)
  let M : ℝ × ℝ → Bool → ℝ := fun p v => if v then p.2 else p.1
  have hρ_lt : |(4 / 5 : ℝ)| < 1 := by norm_num
  -- Divergences of `false` (`+1 > 0`) and `true` (`-1 < 0`):
  have hdiv_f : 0 < dirTheta.divergence false := by
    have hout : dirTheta.outDeg false = 2 := by
      have : dirTheta.outCut {false} = ({0, 1} : Finset (Fin 3)) := by
        ext e; fin_cases e <;> simp [dirTheta, Multigraph.outCut]
      rw [Multigraph.outDeg, this, ncard_coe_finset]; decide
    have hin : dirTheta.inDeg false = 1 := by
      have : dirTheta.inCut {false} = ({2} : Finset (Fin 3)) := by
        ext e; fin_cases e <;> simp [dirTheta, Multigraph.inCut]
      rw [Multigraph.inDeg, this, ncard_coe_finset]; decide
    unfold Multigraph.divergence
    omega
  have hdiv_t : ¬ 0 < dirTheta.divergence true := by
    have htot := dirTheta.sum_divergence dirTheta_loopless
    rw [Fintype.sum_bool] at htot
    omega
  -- Marginal cdf `Φ`:
  have hFm (v : Bool) (t : ℝ) : P.real {ω | M ω v ≤ t} = cdf (gaussianReal 0 1) t := by
    cases v
    · have h := map_measureReal_apply (μ := P) measurable_fst (measurableSet_Iic (a := t))
      rw [correlatedGaussian_map_fst, ← cdf_eq_real] at h
      exact h.symm
    · have h := map_measureReal_apply (μ := P) measurable_snd (measurableSet_Iic (a := t))
      rw [correlatedGaussian_map_snd hρ_lt.le, ← cdf_eq_real] at h
      exact h.symm
  -- Crossing probability of every edge `e` at shift `d` is `1 - 2 * P(p.1 ≤ d ∧ p.2 ≤ -d)`:
  have hedge_prob (e : Fin 3) (d : ℝ) :
      P.real {ω | e ∈ dirTheta.edgeCut (DirectedShift.shiftedCut dirTheta (M ω) d)} =
        1 - 2 * P.real {p | p.1 ≤ d ∧ p.2 ≤ -d} := by
    have hset : {ω : ℝ × ℝ | e ∈ dirTheta.edgeCut (DirectedShift.shiftedCut dirTheta (M ω) d)} =
        {p | d < p.1 ∧ p.2 ≤ -d} ∪ {p | p.1 ≤ d ∧ -d < p.2} := by
      have hiff_cut (a b : ℝ) :
          ¬((a ≤ d) ↔ (b ≤ -d)) ↔ (d < a ∧ b ≤ -d) ∨ (a ≤ d ∧ -d < b) :=
        ⟨fun h => (le_or_gt a d).elim
            (fun h1 => Or.inr ⟨h1, lt_of_not_ge fun h2 => h ⟨fun _ => h2, fun _ => h1⟩⟩)
            (fun h1 => Or.inl ⟨h1, le_of_not_gt fun h2 =>
              h ⟨fun ha => absurd ha (not_le.mpr h1), fun hb => absurd hb (not_le.mpr h2)⟩⟩),
          fun h hiff => h.elim (fun ⟨h1, h2⟩ => not_le.mpr h1 (hiff.mpr h2))
            (fun ⟨h1, h2⟩ => not_le.mpr h2 (hiff.mp h1))⟩
      ext p
      fin_cases e
      · change ¬((p.1 ≤ if 0 < dirTheta.divergence false then d else -d) ↔
            (p.2 ≤ if 0 < dirTheta.divergence true then d else -d)) ↔ _
        simp only [hdiv_f, hdiv_t, ↓reduceIte]
        exact hiff_cut p.1 p.2
      · change ¬((p.1 ≤ if 0 < dirTheta.divergence false then d else -d) ↔
            (p.2 ≤ if 0 < dirTheta.divergence true then d else -d)) ↔ _
        simp only [hdiv_f, hdiv_t, ↓reduceIte]
        exact hiff_cut p.1 p.2
      · change ¬((p.2 ≤ if 0 < dirTheta.divergence true then d else -d) ↔
            (p.1 ≤ if 0 < dirTheta.divergence false then d else -d)) ↔ _
        simp only [hdiv_f, hdiv_t, ↓reduceIte, Iff.comm]
        exact hiff_cut p.1 p.2
    have hdisj : Disjoint {p : ℝ × ℝ | d < p.1 ∧ p.2 ≤ -d} {p | p.1 ≤ d ∧ -d < p.2} :=
      disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h2.1 h1.1
    have hm2 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ d ∧ -d < p.2} :=
      (measurableSet_Iic.preimage measurable_fst).inter (measurableSet_Ioi.preimage measurable_snd)
    have hp2 : P.real {p | p.1 ≤ d ∧ -d < p.2} = P.real {p | -d < p.1 ∧ p.2 ≤ d} := by
      conv_lhs => rw [show P = correlatedGaussian (4 / 5) from rfl,
        ← correlatedGaussian_map_swap hρ_lt.le, map_measureReal_apply measurable_swap hm2]
      congr 1
      ext p
      exact and_comm
    have hsym : P.real {p | p.1 ≤ -d ∧ p.2 ≤ d} = P.real {p | p.1 ≤ d ∧ p.2 ≤ -d} := by
      dsimp [P]
      rw [← gaussianQuadrant_cdf_cdf, ← gaussianQuadrant_cdf_cdf, gaussianQuadrant_comm hρ_lt.le]
    rw [hset, measureReal_union hdisj hm2, hp2,
      measureReal_correlatedGaussian_gt_and_le hρ_lt.le d (-d),
      measureReal_correlatedGaussian_gt_and_le hρ_lt.le (-d) d, hsym,
      cdf_gaussianReal_neg one_ne_zero]
    ring
  have hc_eq (d : ℝ) :
      (∑ e : Fin 3, P.real {ω | e ∈ dirTheta.edgeCut (DirectedShift.shiftedCut dirTheta (M ω) d)}) /
        Fintype.card Bool = 3 / 2 * (1 - 2 * P.real {p | p.1 ≤ d ∧ p.2 ≤ -d}) := by
    simp only [hedge_prob, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul]
    ring
  -- Check `c 0 < 1 / 2` via `cos (π / 3) = 1 / 2 < 4 / 5`.
  have hc0 : (∑ e : Fin 3,
      P.real {ω | e ∈ dirTheta.edgeCut (DirectedShift.shiftedCut dirTheta (M ω) 0)}) /
        Fintype.card Bool < 1 / 2 := by
    rw [hc_eq 0]
    have hp00 : P.real {p | p.1 ≤ 0 ∧ p.2 ≤ -0} = 1 / 2 - arccos (4 / 5) / (2 * π) := by
      dsimp [P]
      rw [neg_zero, ← gaussianQuadrant_cdf_cdf, cdf_gaussianReal_zero_zero one_ne_zero, one_div,
        ← one_div, gaussianQuadrant_half_half hρ_lt.le]
    rw [hp00]
    have harc_lt : arccos (4 / 5) < π / 3 := by
      have hlt : cos (π / 3) < 4 / 5 := by rw [cos_pi_div_three]; norm_num
      have ha := arccos_lt_arccos (by norm_num) hlt (by norm_num)
      rwa [arccos_cos (by positivity) (by linarith [pi_pos])] at ha
    have hdiv_lt : arccos (4 / 5) / π < 1 / 3 := by
      rw [div_lt_iff₀ pi_pos]
      linarith
    have hrew : 3 / 2 * (1 - 2 * (1 / 2 - arccos (4 / 5) / (2 * π))) =
        3 / 2 * (arccos (4 / 5) / π) := by ring
    linarith [hdiv_lt, hrew]
  -- Check `HasDerivAt c 0 0` via `hasFDerivAt_gaussianQuadrant`!
  have hcderiv : HasDerivAt
      (fun d => (∑ e : Fin 3,
        P.real {ω | e ∈ dirTheta.edgeCut (DirectedShift.shiftedCut dirTheta (M ω) d)}) /
          Fintype.card Bool) 0 0 := by
    simp_rw [hc_eq]
    have hquad_eq (d : ℝ) : P.real {p | p.1 ≤ d ∧ p.2 ≤ -d} =
        Function.uncurry (gaussianQuadrant (4 / 5))
          (cdf (gaussianReal 0 1) d, cdf (gaussianReal 0 1) (-d)) :=
      (gaussianQuadrant_cdf_cdf (4 / 5) d (-d)).symm
    simp_rw [hquad_eq]
    have hd_cdf : HasDerivAt (cdf (gaussianReal 0 1)) (gaussianPDFReal 0 1 0) 0 :=
      hasDerivAt_cdf_gaussianReal 0 one_ne_zero 0
    have hd_cdf_neg : HasDerivAt (fun d => cdf (gaussianReal 0 1) (-d))
        (-gaussianPDFReal 0 1 0) 0 := by
      have hd0' : HasDerivAt (cdf (gaussianReal 0 1)) (gaussianPDFReal 0 1 0) (-(0 : ℝ)) := by
        rwa [neg_zero]
      have hc := hd0'.comp (0 : ℝ) (hasDerivAt_neg 0)
      rwa [mul_neg_one] at hc
    have hhalf_mem : cdf (gaussianReal 0 1) 0 ∈ Ioo (0 : ℝ) 1 := by
      rw [cdf_gaussianReal_zero_zero one_ne_zero]
      constructor <;> norm_num
    have hpt0 : (cdf (gaussianReal 0 1) 0, cdf (gaussianReal 0 1) 0) =
        (cdf (gaussianReal 0 1) 0, cdf (gaussianReal 0 1) (-0)) := by rw [neg_zero]
    have hfderiv := hpt0 ▸ hasFDerivAt_gaussianQuadrant hρ_lt hhalf_mem hhalf_mem
    have hcomp := hfderiv.comp_hasDerivAt (0 : ℝ) (HasDerivAt.prodMk hd_cdf hd_cdf_neg)
    have h32 := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hcomp.const_mul 2)).const_mul (3 / 2)
    refine h32.congr_deriv ?_
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  have hFderiv : HasDerivAt (cdf (gaussianReal 0 1)) (gaussianPDFReal 0 1 0) 0 :=
    hasDerivAt_cdf_gaussianReal 0 one_ne_zero 0
  exact DirectedShift.exists_pos_shifted_inCut_ratio_lt dirTheta dirTheta_loopless dirTheta_cubic
    M (fun v => by cases v <;> (dsimp [M]; fun_prop))
    (by rw [cdf_gaussianReal_zero_zero one_ne_zero]; norm_num)
    (fun t => by rw [cdf_gaussianReal_neg one_ne_zero]; ring)
    hFm hFderiv (gaussianPDFReal_pos 0 1 0 one_ne_zero) hc0 hcderiv

/-! ### 4. Unbalanced cut demand and Cauchy circuit lower bounds (`4.2170 N`) -/

example {N : ℕ} {F : Type} [Field F] {σ : Signature.{0}} {I : Interpretation σ F}
    {M : Matrix (Fin N) (Fin N) F} {c : Circuit σ N N} (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (hcap : c.LinearCapacity I)
    (P : Set (Compiler.Vertex c)) :
    min (((Compiler.network c I fun _ => univ).readIn P).ncard +
        {o : Fin N | Compiler.Vertex.output o ∈ P}.ncard)
      (2 * N - (((Compiler.network c I fun _ => univ).readIn P).ncard +
        {o : Fin N | Compiler.Vertex.output o ∈ P}.ncard)) ≤
      ((Compiler.graph c).edgeCut P).ncard :=
  Compiler.min_le_ncard_edgeCut hM hc hcap P

example : ∀ᶠ N in atTop,
    ∀ (c : Circuit (arithSignature ℚ) N N),
      c.Computes (arithInterpretation ℚ) (fun x => Matrix.cauchyNat ℚ N *ᵥ x) →
        (4217 / 1000 - 1 / 1000 : ℝ) * N < c.innerSize := by
  filter_upwards
    [eventually_4217_div_1000_sub_mul_lt_innerSize_arith_cauchyNat.{0} (ε := 1 / 1000)
      (by norm_num)] with N hN c hc
  exact hN ℚ c hc

example : ∀ᶠ N in atTop, ∀ (q : ℕ) [Fact q.Prime], 2 * N ≤ q →
    ∀ (σ : Signature.{0}) (I : Interpretation σ (ZMod q)) (c : Circuit σ N N),
      c.FanInAtMost 2 → c.Computes I (fun x => Matrix.cauchyNat (ZMod q) N *ᵥ x) →
        (4217 / 1000 - 1 / 1000 : ℝ) * N < c.innerSize :=
  eventually_4217_div_1000_sub_mul_lt_innerSize_cauchyNat_zmod.{0} (ε := 1 / 1000) (by norm_num)

end CslibFrontierTests.FrontierDirectedLinear
