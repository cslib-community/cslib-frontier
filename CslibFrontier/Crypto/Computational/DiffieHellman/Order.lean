/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PPT

/-!
# The expected inverse group order is negligible under CDH and DDH

If a prime-order group family satisfies `CDH` or `DDH` for a setup distribution, then the expected
inverse group order `n ↦ ∑' d, setup n d * (F.order d)⁻¹` is negligible, with no separate
lower-bound hypothesis on the group orders. Under `CDH`, the adversary always outputs the identity
element `0` and succeeds whenever `a = 0` or `b = 0` (so at least when `a = 0`, which occurs with
probability `1 / q`). Under `DDH`, the distinguisher tests whether the candidate shared element is
the identity: it succeeds with probability `1 / q + (q - 1) / q²` on real triples and `1 / q` on
random ones, so the expected inverse order is at most twice its advantage. The DDH bound is not
derived from the CDH bound, because `DDH.cdh`, which turns DDH into CDH, itself needs a negligible
inverse-order bound as a hypothesis.

Clients can use these bounds without importing Naor–Reingold or ElGamal.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_expected_inv_order`: `F.DDH setup` implies
  that the expected inverse group order is negligible.
* `Cslib.Crypto.PrimeOrderGroupFamily.CDH.negligible_expected_inv_order`: `F.CDH setup` implies
  that the expected inverse group order is negligible.
* `Cslib.Crypto.PrimeOrderGroupFamily.CDH.negligible_inv_order`: deterministic-schedule corollary
  in the `(F.order (d n) : ℝ≥0)⁻¹` form.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_le_expected_inv_order`: averaging a pointwise
  `(F.order d)⁻¹` advantage bound over `setup` yields advantage at most the expected inverse group
  order.

## References

* [BonehShoup2023], Attack Game 10.5 (`CDH`), Attack Game 10.6 (`DDH`), and Section 12.6.2,
  p. 500 (`1 / q` negligible under `CDH`). The expected-order bounds over arbitrary setup laws are
  original.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Probability.PMF Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

/-- Test whether the candidate shared element is the identity (original). -/
private def ddhZeroDistinguisher (F : PrimeOrderGroupFamily) : F.DDHDistinguisher :=
  fun _ _ _ _ w => pure (decide (w = 0))

private theorem isPPT_ddhZeroDistinguisher (F : PrimeOrderGroupFamily) :
    (ddhZeroDistinguisher F).IsPPT := by
  refine (ComputableInPolyTime.isPPTOn (f := fun x : F.DDHInput =>
    decide (F.encode x.groupParameters x.candidateShared = F.encode x.groupParameters 0))
    (by fun_prop)).congr fun x => ?_
  simp [ddhZeroDistinguisher, (F.encode_injective _).eq_iff]

private theorem uniform_mul_decide_eq_zero_apply (F : PrimeOrderGroupFamily) (d : F.Desc) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
        PMF.pure (decide (α * β = 0))) true =
      (F.order d : ℝ≥0∞)⁻¹ +
        ((F.order d - 1 : ℕ) : ℝ≥0∞) * ((F.order d : ℝ≥0∞)⁻¹ * (F.order d : ℝ≥0∞)⁻¹) := by
  let _ : Fact (Nat.Prime (F.order d)) := ⟨F.prime_order d⟩
  have hinner (α : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
        PMF.pure (decide (α * β = 0))) true =
        if α = 0 then 1 else (F.order d : ℝ≥0∞)⁻¹ := by
    by_cases hα : α = 0
    · subst hα
      simp [PMF.bind_const]
    · simp only [hα, ↓reduceIte, mul_eq_zero, false_or]
      simpa only [eq_comm, ZMod.card] using uniformOfFintype_bind_decide_eq_apply_true
        (0 : ZMod (F.order d))
  rw [PMF.bind_apply, tsum_fintype]
  simp only [hinner, PMF.uniformOfFintype_apply, ZMod.card]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod (F.order d)))]
  have herase :
      ∑ x ∈ Finset.univ.erase (0 : ZMod (F.order d)),
        (F.order d : ℝ≥0∞)⁻¹ * (if x = 0 then 1 else (F.order d : ℝ≥0∞)⁻¹) =
      ((F.order d - 1 : ℕ) : ℝ≥0∞) * ((F.order d : ℝ≥0∞)⁻¹ * (F.order d : ℝ≥0∞)⁻¹) := by
    have hcongr :
        ∑ x ∈ Finset.univ.erase (0 : ZMod (F.order d)),
          (F.order d : ℝ≥0∞)⁻¹ * (if x = 0 then 1 else (F.order d : ℝ≥0∞)⁻¹) =
        ∑ _x ∈ Finset.univ.erase (0 : ZMod (F.order d)),
          (F.order d : ℝ≥0∞)⁻¹ * (F.order d : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp [Finset.ne_of_mem_erase hx]
    rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card, nsmul_eq_mul]
  rw [herase]
  simp [add_comm]

/-- For any setup distribution `setup`, the expected inverse group order
`∑' d, setup n d * (F.order d)⁻¹` is at most twice the DDH advantage of testing whether the
candidate shared element is the identity (original). -/
private theorem expected_inv_order_le_two_mul_advantage_ddh (F : PrimeOrderGroupFamily)
    (setup : ℕ → PMF F.Desc) (n : ℕ) :
    (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal ≤
      2 * Game.advantage (F.ddhRealGame setup (ddhZeroDistinguisher F) n)
        (F.ddhRandomGame setup (ddhZeroDistinguisher F) n) := by
  set E := ∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹ with hE
  set R := ∑' d, setup n d *
    (((F.order d - 1 : ℕ) : ℝ≥0∞) * ((F.order d : ℝ≥0∞)⁻¹ * (F.order d : ℝ≥0∞)⁻¹)) with hR
  have hreal : (F.ddhRealGame setup (ddhZeroDistinguisher F) n) true = E + R := by
    simp only [ddhRealGame, Game.withSetup, ddhRealExperiment, ddhZeroDistinguisher,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, smul_eq_zero,
      F.generator_ne_zero, or_false]
    rw [PMF.bind_apply, hE, hR, ← tsum_add]
    refine tsum_congr fun d => ?_
    rw [uniform_mul_decide_eq_zero_apply F d, mul_add]
  have hideal : (F.ddhRandomGame setup (ddhZeroDistinguisher F) n) true = E := by
    simp only [ddhRandomGame, Game.withSetup, ddhRandomExperiment, ddhZeroDistinguisher,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, smul_eq_zero,
      F.generator_ne_zero, or_false, PMF.bind_const]
    rw [PMF.bind_apply, hE]
    refine tsum_congr fun d => congrArg (setup n d * ·) ?_
    simpa only [eq_comm, ZMod.card] using uniformOfFintype_bind_decide_eq_apply_true
      (0 : ZMod (F.order d))
  have hle_sum : E ≤ 2 * R := by
    rw [hE, hR, ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun d => ?_
    rw [← mul_assoc, mul_comm (2 : ℝ≥0∞) (setup n d), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    have hq2 : 2 ≤ F.order d := (F.prime_order d).two_le
    have hq0 : (F.order d : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqtop : (F.order d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hnat : (F.order d : ℝ≥0∞) ≤ 2 * ((F.order d - 1 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (show F.order d ≤ 2 * (F.order d - 1) by omega)
    calc (F.order d : ℝ≥0∞)⁻¹
        = ((F.order d : ℝ≥0∞) * (F.order d : ℝ≥0∞)⁻¹) * (F.order d : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.mul_inv_cancel hq0 hqtop, one_mul]
      _ ≤ (2 * ((F.order d - 1 : ℕ) : ℝ≥0∞) * (F.order d : ℝ≥0∞)⁻¹) * (F.order d : ℝ≥0∞)⁻¹ := by
          gcongr
      _ = 2 * (((F.order d - 1 : ℕ) : ℝ≥0∞) * ((F.order d : ℝ≥0∞)⁻¹ * (F.order d : ℝ≥0∞)⁻¹)) := by
          ring
  have hrem_top : R ≠ ⊤ := fun htop =>
    PMF.apply_ne_top (F.ddhRealGame setup (ddhZeroDistinguisher F) n) true (by
      rw [hreal, htop, add_top])
  have hadv : R.toNNReal = Game.advantage (F.ddhRealGame setup (ddhZeroDistinguisher F) n)
      (F.ddhRandomGame setup (ddhZeroDistinguisher F) n) := by
    apply NNReal.eq
    rw [Game.coe_advantage]
    unfold Game.succProbability
    rw [hreal, hideal, ENNReal.toNNReal_add (hideal ▸ PMF.apply_ne_top _ _) hrem_top,
      NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg (NNReal.coe_nonneg _)]
  rw [← hadv, ← ENNReal.toNNReal_ofNat, ← ENNReal.toNNReal_mul]
  exact ENNReal.toNNReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hrem_top) hle_sum

/-- **Expected inverse group order is negligible under `DDH`** (original): if `F.DDH setup` holds,
then `n ↦ (∑' d, setup n d * (F.order d)⁻¹).toNNReal` is negligible. -/
theorem DDH.negligible_expected_inv_order {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) :
    Negligible fun n => (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal :=
  negligible_of_le
    ((hDDH (ddhZeroDistinguisher F) (isPPT_ddhZeroDistinguisher F)).const_mul 2)
    (expected_inv_order_le_two_mul_advantage_ddh F setup)

/-- Constant-identity CDH adversary that always outputs `0 : F.Carrier d` (original). -/
private def cdhZeroAdversary (F : PrimeOrderGroupFamily) : F.CDHAdversary :=
  fun _ _ _ _ => pure 0

private theorem isPPT_cdhZeroAdversary (F : PrimeOrderGroupFamily) :
    (cdhZeroAdversary F).IsPPT := by
  refine (ComputableInPolyTime.isPPTOn (f := fun x : F.CDHInput =>
    F.encode x.groupParameters 0) (by fun_prop)).congr fun x => ?_
  simp [cdhZeroAdversary]

/-- For any setup distribution `setup`, the expected inverse group order
`∑' d, setup n d * (F.order d)⁻¹` is at most the CDH success probability of `cdhZeroAdversary`
(original). -/
private theorem expected_inv_order_le_succProbability_cdhZeroAdversary
    (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (n : ℕ) :
    (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal ≤
      Game.succProbability (F.cdhGame setup (cdhZeroAdversary F) n) := by
  have hcdh (d : F.Desc) :
      (F.order d : ℝ≥0∞)⁻¹ ≤
        (ProbComp.eval (cdhExperiment (F.order d) (F.generator d)
          (cdhZeroAdversary F n d))) true := by
    simp only [cdhExperiment, cdhZeroAdversary, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure]
    rw [PMF.bind_apply]
    refine le_trans ?_ (le_tsum _ (0 : ZMod (F.order d)))
    simp [PMF.bind_const, PMF.uniformOfFintype_apply, PMF.pure_apply, ZMod.card]
  have hsum :
      ∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹ ≤
        (F.cdhGame setup (cdhZeroAdversary F) n) true := by
    simp only [cdhGame, Game.withSetup, PMF.bind_apply]
    exact tsum_le_tsum fun d => mul_le_mul_of_nonneg_left (hcdh d) zero_le
  exact ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) hsum

/-- **Expected inverse group order is negligible under `CDH`** (original): if `F.CDH setup` holds,
then `n ↦ (∑' d, setup n d * (F.order d)⁻¹).toNNReal` is negligible. -/
theorem CDH.negligible_expected_inv_order {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hCDH : F.CDH setup) :
    Negligible fun n => (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal :=
  negligible_of_le (hCDH (cdhZeroAdversary F) (isPPT_cdhZeroAdversary F))
    (expected_inv_order_le_succProbability_cdhZeroAdversary F setup)

/-- Along a deterministic group-parameter schedule `d : ℕ → F.Desc`, `F.CDH` at
`fun n => PMF.pure (d n)` implies that `(F.order (d n) : ℝ≥0)⁻¹` is negligible
([BonehShoup2023], §12.6.2, p. 500). -/
theorem CDH.negligible_inv_order {F : PrimeOrderGroupFamily} {d : ℕ → F.Desc}
    (hCDH : F.CDH (fun n => PMF.pure (d n))) :
    Negligible fun n => (F.order (d n) : ℝ≥0)⁻¹ := by
  refine hCDH.negligible_expected_inv_order.congr' (Filter.Eventually.of_forall fun n => ?_)
  dsimp only
  have h : (∑' d', PMF.pure (d n) d' * (F.order d' : ℝ≥0∞)⁻¹) = (F.order (d n) : ℝ≥0∞)⁻¹ := by
    simp [PMF.pure_apply]
  rw [h, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-- If `Game.advantage (f d) (g d) ≤ (F.order d)⁻¹` for every group description `d`, then
averaging over `setup` yields advantage at most `(∑' d, setup d * (F.order d)⁻¹).toNNReal`. -/
theorem advantage_bind_le_expected_inv_order (F : PrimeOrderGroupFamily)
    (setup : PMF F.Desc) (f g : F.Desc → Game)
    (h : ∀ d, Game.advantage (f d) (g d) ≤ (F.order d : ℝ≥0)⁻¹) :
    Game.advantage (setup.bind f) (setup.bind g) ≤
      (∑' d, setup d * (F.order d : ℝ≥0∞)⁻¹).toNNReal := by
  let errPMF : F.Desc → Game := fun d =>
    (PMF.uniformOfFintype (ZMod (F.order d))).bind fun x => PMF.pure (decide (x = 0))
  have herr_true (d : F.Desc) : errPMF d true = (F.order d : ℝ≥0∞)⁻¹ := by
    dsimp only [errPMF]
    rw [PMF.bind_apply, tsum_fintype]
    simp [PMF.uniformOfFintype_apply, PMF.pure_apply, ZMod.card, eq_comm (a := true)]
  have herr_succ :
      Game.succProbability (setup.bind errPMF) =
        (∑' d, setup d * (F.order d : ℝ≥0∞)⁻¹).toNNReal := by
    unfold Game.succProbability
    rw [PMF.bind_apply]
    simp_rw [herr_true]
  rw [← herr_succ]
  refine Game.advantage_bind_le_succProbability_bind setup f g errPMF fun d => ?_
  rw [herr_true, ← ENNReal.coe_natCast,
    ← ENNReal.coe_inv (by exact_mod_cast (F.prime_order d).ne_zero)]
  exact Game.apply_true_le_of_advantage_le (h d)

end Cslib.Crypto.PrimeOrderGroupFamily
