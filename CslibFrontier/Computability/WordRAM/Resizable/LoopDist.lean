/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Resizable.Clocked
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Probability.PMF.SupportTsum

/-!
# Geometric `while`-loop exit distributions on the Resizable Word RAM

Iteration and limiting exit distributions (`loopStepRPMF`, `loopIterRPMF`, `loopExitRPMF`) and
state invariants (`RLoopStateInv`) on `RData r` for randomized Las Vegas `while` loops over the
word-granular **Resizable Word RAM** (`Cslib.WordRAM.Resizable`), mirroring the fixed-memory
absorbing `while`-loop exit calculus in `Cslib.WordRAM.Randomized.Expected` on `RData r` (including
the dynamic word frontier `frontier`).

## Main definitions

* `Cslib.WordRAM.Resizable.loopStepRPMF`, `Cslib.WordRAM.Resizable.loopIterRPMF`: single-step and
  `K`-step `while`-loop distributions on `RData r`.
* `Cslib.WordRAM.Resizable.RLoopStateInv`: combined active/exit loop invariant on `RData r`.
* `Cslib.WordRAM.Resizable.loopExitRPMF`: limiting exit distribution of a geometric `while` loop.

## Main results

* `Cslib.WordRAM.Resizable.hasSum_loopExitRDensity`: total exit probability equals `1` whenever
  each active step exits with probability bounded below by `p_exit > 0`.
* `Cslib.WordRAM.Resizable.loopExitRPMF_of_holds`,
  `Cslib.WordRAM.Resizable.loopExitRPMF_of_not_holds`,
  `Cslib.WordRAM.Resizable.mem_support_loopExitRPMF`: fixed-point unfolding and support invariant
  for `loopExitRPMF`.

## References

* [MitzenmacherUpfal2017] Michael Mitzenmacher and Eli Upfal, *Probability and Computing*, 2nd ed.,
  Cambridge University Press, 2017, Sections 2.1, 2.3, and 2.4.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.WordRAM.Resizable

variable {r : ℕ}

/-- One step of a `while` loop distribution on `RData r`. -/
noncomputable def loopStepRPMF (cond : Cond r) (μ_body : RData r → PMF (RData r)) (x : RData r) :
    PMF (RData r) :=
  open Classical in if cond.Holds x.toData then μ_body x else PMF.pure x

theorem loopStepRPMF_of_holds {cond : Cond r} {μ_body : RData r → PMF (RData r)} {x : RData r}
    (hc : cond.Holds x.toData) : loopStepRPMF cond μ_body x = μ_body x := by
  classical simp [loopStepRPMF, hc]

theorem loopStepRPMF_of_not_holds {cond : Cond r} {μ_body : RData r → PMF (RData r)} {x : RData r}
    (hc : ¬cond.Holds x.toData) : loopStepRPMF cond μ_body x = PMF.pure x := by
  classical simp [loopStepRPMF, hc]

/-- `K`-step iterate of `loopStepRPMF`. -/
noncomputable def loopIterRPMF (cond : Cond r) (μ_body : RData r → PMF (RData r)) :
    ℕ → RData r → PMF (RData r)
  | 0, x => PMF.pure x
  | K + 1, x => (loopStepRPMF cond μ_body x).bind (loopIterRPMF cond μ_body K)

@[simp] theorem loopIterRPMF_zero (cond : Cond r) (μ_body : RData r → PMF (RData r)) (x : RData r) :
    loopIterRPMF cond μ_body 0 x = PMF.pure x := rfl

theorem loopIterRPMF_succ (cond : Cond r) (μ_body : RData r → PMF (RData r)) (K : ℕ)
    (x : RData r) :
    loopIterRPMF cond μ_body (K + 1) x =
      (loopStepRPMF cond μ_body x).bind (loopIterRPMF cond μ_body K) := rfl

theorem loopIterRPMF_of_not_holds {cond : Cond r} {μ_body : RData r → PMF (RData r)} {x : RData r}
    (hc : ¬cond.Holds x.toData) (K : ℕ) :
    loopIterRPMF cond μ_body K x = PMF.pure x := by
  induction K with
  | zero => rfl
  | succ K ih => rw [loopIterRPMF_succ, loopStepRPMF_of_not_holds hc, PMF.pure_bind, ih]

theorem loopIterRPMF_succ_right (cond : Cond r) (μ_body : RData r → PMF (RData r)) (K : ℕ)
    (x : RData r) :
    loopIterRPMF cond μ_body (K + 1) x =
      (loopIterRPMF cond μ_body K x).bind (loopStepRPMF cond μ_body) := by
  induction K generalizing x with
  | zero => simp [loopIterRPMF]
  | succ K ih =>
    rw [loopIterRPMF_succ (K := K), PMF.bind_bind]
    exact congrArg ((loopStepRPMF cond μ_body x).bind ·) (funext ih)

theorem loopIterRPMF_indicator_mono (cond : Cond r) (μ_body : RData r → PMF (RData r))
    (x y : RData r) :
    Monotone fun K => Set.indicator {z : RData r | ¬cond.Holds z.toData}
      (loopIterRPMF cond μ_body K x) y := by
  intro K₁ K₂ hK
  by_cases hy : y ∈ {z : RData r | ¬cond.Holds z.toData}
  · simp only [Set.indicator_of_mem hy]
    refine monotone_nat_of_le_succ (f := fun K => loopIterRPMF cond μ_body K x y) (fun K => ?_) hK
    rw [loopIterRPMF_succ_right, PMF.bind_apply]
    simpa [loopStepRPMF_of_not_holds hy] using
      le_tsum (f := fun z => loopIterRPMF cond μ_body K x z * loopStepRPMF cond μ_body z y) y
  · simp [Set.indicator_of_notMem hy]

/-- Combined active/exit state invariant for `while` loops on `RData r`. -/
def RLoopStateInv (cond : Cond r) (I Q : RData r → Prop) (x : RData r) : Prop :=
  (cond.Holds x.toData ∧ I x) ∨ (¬cond.Holds x.toData ∧ Q x)

theorem loopIterRPMF_support_inv {cond : Cond r} {I Q : RData r → Prop}
    {μ_body : RData r → PMF (RData r)}
    (hinv : ∀ x, I x → cond.Holds x.toData → ∀ y ∈ (μ_body x).support, RLoopStateInv cond I Q y)
    (K : ℕ) {x : RData r} (hx : RLoopStateInv cond I Q x) :
    ∀ y ∈ (loopIterRPMF cond μ_body K x).support, RLoopStateInv cond I Q y := by
  induction K generalizing x with
  | zero => simp [loopIterRPMF_zero, hx]
  | succ K ih =>
    intro y hy
    obtain ⟨z, hz, hyz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
    rcases hx with ⟨hcx, hIx⟩ | ⟨hcx, hQx⟩
    · rw [loopStepRPMF_of_holds hcx] at hz
      exact ih (hinv x hIx hcx z hz) y hyz
    · rw [loopStepRPMF_of_not_holds hcx, PMF.support_pure, Set.mem_singleton_iff] at hz
      exact ih (hz ▸ Or.inr ⟨hcx, hQx⟩) y hyz

theorem pmf_rdata_step_drift_bound (μ : PMF (RData r)) (cond : Cond r)
    {C p_exit : ℝ≥0∞} (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hp_exit : p_exit ≤ μ.toOuterMeasure {y : RData r | ¬cond.Holds y.toData}) :
    C + ∑' y, μ y * (if cond.Holds y.toData then C / p_exit else 0) ≤ C / p_exit := by
  have hact : (∑' y, μ y * (if cond.Holds y.toData then C / p_exit else 0)) =
      μ.toOuterMeasure {y : RData r | cond.Holds y.toData} * (C / p_exit) := by
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun y => by by_cases hc : cond.Holds y.toData <;> simp [hc]
  calc C + ∑' y, μ y * (if cond.Holds y.toData then C / p_exit else 0)
      = (p_exit + μ.toOuterMeasure {y : RData r | cond.Holds y.toData}) * (C / p_exit) := by
        rw [hact, add_mul, mul_comm p_exit, ENNReal.div_mul_cancel hp_pos.ne' hp_top]
    _ ≤ (μ.toOuterMeasure {y : RData r | cond.Holds y.toData}ᶜ +
          μ.toOuterMeasure {y : RData r | cond.Holds y.toData}) * (C / p_exit) :=
        mul_le_mul_left (add_le_add hp_exit le_rfl) _
    _ = C / p_exit := by
        rw [add_comm, Cslib.Probability.PMF.toOuterMeasure_add_compl_ennreal, one_mul]

private noncomputable def loopActiveRSteps (cond : Cond r) (μ_body : RData r → PMF (RData r))
    (N : ℕ) (x : RData r) : ℝ≥0∞ :=
  ∑ K ∈ Finset.range N,
    (loopIterRPMF cond μ_body K x).toOuterMeasure {y : RData r | cond.Holds y.toData}

private theorem loopActiveRSteps_le {cond : Cond r} {I Q : RData r → Prop}
    {μ_body : RData r → PMF (RData r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x.toData → ∀ y ∈ (μ_body x).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x.toData →
      p_exit ≤ (μ_body x).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    (N : ℕ) {x : RData r} (hx : RLoopStateInv cond I Q x) :
    loopActiveRSteps cond μ_body N x ≤ if cond.Holds x.toData then 1 / p_exit else 0 := by
  induction N generalizing x with
  | zero => simp [loopActiveRSteps]
  | succ N ih =>
    rcases hx with ⟨hcx, hIx⟩ | ⟨hcx, _⟩
    · simp only [hcx, ↓reduceIte, loopActiveRSteps, Finset.sum_range_succ', loopIterRPMF_zero,
        PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, add_comm]
      simp_rw [loopIterRPMF_succ, loopStepRPMF_of_holds hcx, PMF.toOuterMeasure_bind_apply]
      rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
      simp_rw [← Finset.mul_sum]
      exact (add_le_add le_rfl (Cslib.Probability.PMF.tsum_mul_mono_support (μ_body x) fun z hz =>
        ih (hinv x hIx hcx z hz))).trans
        (pmf_rdata_step_drift_bound (μ_body x) cond hp_pos hp_top (hp_exit x hIx hcx))
    · simp only [hcx, ↓reduceIte, nonpos_iff_eq_zero, loopActiveRSteps]
      exact Finset.sum_eq_zero fun K _ => by
        simp [loopIterRPMF_of_not_holds hcx, PMF.toOuterMeasure_pure_apply, hcx]

theorem hasSum_loopExitRDensity {cond : Cond r} {I Q : RData r → Prop}
    {μ_body : RData r → PMF (RData r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x.toData → ∀ y ∈ (μ_body x).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x.toData →
      p_exit ≤ (μ_body x).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    {x : RData r} (hx : RLoopStateInv cond I Q x) :
    HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z : RData r | ¬cond.Holds z.toData} (loopIterRPMF cond μ_body K x) y) 1 := by
  rw [CompleteLattice.summable.hasSum_iff,
    ENNReal.tsum_iSup_of_monotone (loopIterRPMF_indicator_mono cond μ_body x)]
  simp_rw [← PMF.toOuterMeasure_apply]
  set b := ⨆ K : ℕ,
    (loopIterRPMF cond μ_body K x).toOuterMeasure {z : RData r | ¬cond.Holds z.toData}
  refine le_antisymm (iSup_le fun _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
    (tsub_eq_zero_iff_le.mp <| by_contra fun hne => ?_)
  have hN : ∀ N : ℕ, (N : ℝ≥0∞) * (1 - b) ≤ 1 / p_exit := fun N => by
    have hsum : (N : ℝ≥0∞) * (1 - b) ≤ loopActiveRSteps cond μ_body N x := by
      rw [loopActiveRSteps]
      conv_lhs => rw [← Finset.card_range N, ← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun K _ => tsub_le_iff_left.mpr ?_
      have hc := Cslib.Probability.PMF.toOuterMeasure_add_compl_ennreal
        (loopIterRPMF cond μ_body K x) {z : RData r | cond.Holds z.toData}
      rw [add_comm]
      exact hc.ge.trans (add_le_add le_rfl (le_iSup (fun J =>
        (loopIterRPMF cond μ_body J x).toOuterMeasure {z : RData r | ¬cond.Holds z.toData}) K))
    exact hsum.trans <| (loopActiveRSteps_le hp_pos hp_top hinv hp_exit N hx).trans
      (by split_ifs <;> simp)
  exact ENNReal.div_ne_top ENNReal.one_ne_top hp_pos.ne' <| top_le_iff.mp <| by
    rw [← ENNReal.top_mul hne, ← ENNReal.iSup_natCast, ENNReal.iSup_mul]
    exact iSup_le hN

/-- Limiting exit distribution of `RCode.loop cond body` from `x` under `μ_body`. -/
noncomputable def loopExitRPMF (cond : Cond r) (μ_body : RData r → PMF (RData r)) (x : RData r) :
    PMF (RData r) :=
  open Classical in
  if h : HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z : RData r | ¬cond.Holds z.toData} (loopIterRPMF cond μ_body K x) y) 1 then
    ⟨_, h⟩
  else PMF.pure x

theorem loopExitRPMF_apply_of_hasSum {cond : Cond r} {μ_body : RData r → PMF (RData r)}
    {x : RData r}
    (h : HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z : RData r | ¬cond.Holds z.toData} (loopIterRPMF cond μ_body K x) y) 1)
    (y : RData r) :
    loopExitRPMF cond μ_body x y =
      ⨆ K : ℕ, Set.indicator {z : RData r | ¬cond.Holds z.toData}
        (loopIterRPMF cond μ_body K x) y := by
  classical simp only [loopExitRPMF, h, ↓reduceDIte]; rfl

theorem loopExitRPMF_of_not_holds {cond : Cond r} {μ_body : RData r → PMF (RData r)} {x : RData r}
    (hc : ¬cond.Holds x.toData) : loopExitRPMF cond μ_body x = PMF.pure x := by
  have hfun : (fun y => ⨆ K : ℕ, Set.indicator {z : RData r | ¬cond.Holds z.toData}
      (loopIterRPMF cond μ_body K x) y) = PMF.pure x := funext fun y => by
    suffices ∀ K, Set.indicator {z : RData r | ¬cond.Holds z.toData}
        (loopIterRPMF cond μ_body K x) y = PMF.pure x y by simp [this]
    intro K; rw [loopIterRPMF_of_not_holds hc]
    by_cases hyx : y = x <;> simp [hyx, hc, PMF.pure_apply]
  ext y; rw [loopExitRPMF_apply_of_hasSum (hfun ▸ (PMF.pure x).2), congrFun hfun y]

theorem loopExitRPMF_of_holds {cond : Cond r} {I Q : RData r → Prop}
    {μ_body : RData r → PMF (RData r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x.toData → ∀ y ∈ (μ_body x).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x.toData →
      p_exit ≤ (μ_body x).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    {x : RData r} (hIx : I x) (hcx : cond.Holds x.toData) :
    loopExitRPMF cond μ_body x = (μ_body x).bind (loopExitRPMF cond μ_body) := by
  ext y
  rw [loopExitRPMF_apply_of_hasSum
    (hasSum_loopExitRDensity hp_pos hp_top hinv hp_exit (Or.inl ⟨hcx, hIx⟩)), PMF.bind_apply]
  rw [← (loopIterRPMF_indicator_mono cond μ_body x y).iSup_nat_add 1]
  have hstep (K : ℕ) : Set.indicator {z : RData r | ¬cond.Holds z.toData}
      (loopIterRPMF cond μ_body (K + 1) x) y = ∑' z, μ_body x z *
      Set.indicator {w' : RData r | ¬cond.Holds w'.toData} (loopIterRPMF cond μ_body K z) y := by
    rw [loopIterRPMF_succ, loopStepRPMF_of_holds hcx]
    by_cases hy : ¬cond.Holds y.toData <;> simp [hy, PMF.bind_apply]
  simp_rw [hstep]
  rw [← ENNReal.tsum_iSup_of_monotone
    (f := fun K z => μ_body x z *
      Set.indicator {w' : RData r | ¬cond.Holds w'.toData} (loopIterRPMF cond μ_body K z) y)
    (fun z _ _ hK => mul_le_mul_right (loopIterRPMF_indicator_mono cond μ_body z y hK) _)]
  simp_rw [← ENNReal.mul_iSup]
  exact Cslib.Probability.PMF.tsum_mul_congr_support (μ_body x) fun z hz =>
    (loopExitRPMF_apply_of_hasSum
      (hasSum_loopExitRDensity hp_pos hp_top hinv hp_exit (hinv x hIx hcx z hz)) y).symm

theorem mem_support_loopExitRPMF {cond : Cond r} {I Q : RData r → Prop}
    {μ_body : RData r → PMF (RData r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x.toData → ∀ y ∈ (μ_body x).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x.toData →
      p_exit ≤ (μ_body x).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    {x : RData r} (hx : RLoopStateInv cond I Q x)
    {y : RData r} (hy : y ∈ (loopExitRPMF cond μ_body x).support) :
    (¬cond.Holds y.toData ∧ Q y) ∧ ∃ K, y ∈ (loopIterRPMF cond μ_body K x).support := by
  rw [PMF.mem_support_iff, loopExitRPMF_apply_of_hasSum
    (hasSum_loopExitRDensity hp_pos hp_top hinv hp_exit hx)] at hy
  have ⟨K, hK⟩ : ∃ K, Set.indicator {z : RData r | ¬cond.Holds z.toData}
      (loopIterRPMF cond μ_body K x) y ≠ 0 := by
    by_contra! hzero
    exact hy (nonpos_iff_eq_zero.mp (iSup_le fun K => (hzero K).le))
  rw [Set.indicator_apply_ne_zero] at hK
  rcases loopIterRPMF_support_inv hinv K hx y hK.2 with ⟨hcy, _⟩ | ⟨_, hQy⟩
  · exact absurd hcy hK.1
  · exact ⟨⟨hK.1, hQy⟩, K, hK.2⟩

end Cslib.WordRAM.Resizable
