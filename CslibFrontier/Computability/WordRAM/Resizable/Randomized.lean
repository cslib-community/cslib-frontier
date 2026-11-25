/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Randomized.Structured
public import CslibFrontier.Computability.WordRAM.Resizable.Clocked
public import CslibFrontier.Computability.WordRAM.Resizable.LoopDist
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.SupportTsum
import CslibFrontier.Tactic.SuppCases

/-!
# Compositional distributional execution (`ExecRCodeDist`) on the Resizable Word RAM

Structured distributional execution (`ExecRCodeDist`) and its compilation (`toExecRProgramDist`) to
flat clocked adaptive-adversary execution (`ExecRProgramDist`) for the word-granular
**Resizable Word RAM** (`Cslib.WordRAM.Resizable`).

`ExecRCodeDist w c x μ T L_peak` couples an adversary-independent fallthrough distribution
`μ : PMF (RData r)` with an expected instruction bound `T : ℝ≥0∞` and an every-step peak hardware
frontier bound `L_peak : ℕ`. Deterministic big-step `RDemonicExec` certificates (including
single-word `.shrink`, the derived `Θ(k + 1)` subroutines `growDirtyCode`, `growZeroCode`, and
`shrinkCode`, and `by realize` segments lifted via `RDemonicExec.of_execBounded`) lift
via `ExecRCodeDist.of_demonicExec`, compose with `.rand`, `.seq`, `.branch`, `.loop_bounded`, and
`.loop_geometric`, transfer along basis simulations (`mapSimulates`), and compile via
`ExecRCodeDist.toExecRProgramDist` to `ExecRProgramDist w (c.program out) out x μ (T + 1) L_peak`.

## Main definitions

* `Cslib.WordRAM.Resizable.ExecRCodeDist`: compositional structured execution certificate on
  `RCode B r` with expected step bound `T : ℝ≥0∞` and peak hardware frontier bound `L_peak : ℕ`
  (publicly re-exporting `Clocked` and `LoopDist`).
* `Cslib.WordRAM.Resizable.ExecRandBounded`: frontier-bounded exact randomized execution of a
  fixed-memory `Code B r` program, recording `Op.BoundedAccess L o x` on every data instruction.

## Main results

* `Cslib.WordRAM.Resizable.ExecRCodeDist.loop_bounded`: ranked `K`-iteration bounded `while` rule.
* `Cslib.WordRAM.Resizable.ExecRCodeDist.mapSimulates`: basis-simulation transport.
* `Cslib.WordRAM.Resizable.ExecRCodeDist.toExecRProgramDist`: compiles `c.program out` to
  `ExecRProgramDist` with fault-freedom, `PeakFrontierLe`, `expectedTimeDemonic ≤ T + 1`, and exact
  halting-state distribution `μ`.
* `Cslib.WordRAM.Resizable.ExecRCodeDist.of_execRandBounded`,
  `Cslib.WordRAM.Resizable.ExecRCodeDist.of_execRandBounded_rename`,
  `Cslib.WordRAM.Resizable.ExecRCodeDist.of_execRandBounded_rename_le`: lift frontier-bounded
  `WordRAM.Code` randomized executions (directly or along an injective register map) into
  `ExecRCodeDist`.

## References

* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF pp. 16–20 / printed pp. 15–19).
* [MitzenmacherUpfal2017] Michael Mitzenmacher and Eli Upfal, *Probability and Computing*, 2nd ed.,
  Cambridge University Press, 2017, Sections 2.1, 2.3, and 2.4.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.WordRAM.Resizable

variable {B B' : Basis} {r : ℕ}

/-! ## Compositional distributional execution (`ExecRCodeDist`) -/

/-- **Compositional Distributional Execution on the Resizable Word RAM (`ExecRCodeDist`).**
`ExecRCodeDist w c x μ T L_peak`: at word width `w` starting from `x : RData r`, running structured
program `c : RCode B r` executes without faulting across all adaptive adversaries `adv : RAdv r`,
keeps the hardware frontier `≤ L_peak` at every intermediate step, realizes adversary-independent
fallthrough distribution `μ : PMF (RData r)` at `pc + c.size`, and uses at most `T : ℝ≥0∞`
expected instructions. -/
inductive ExecRCodeDist {B : Basis} {r : ℕ} (w : ℕ) :
    RCode B r → RData r → PMF (RData r) → ℝ≥0∞ → ℕ → Prop where
  | of_demonicExec {L_peak n : ℕ} {c : RCode B r} {x y : RData r} :
      RDemonicExec w L_peak c x n (· = y) →
      ExecRCodeDist w c x (PMF.pure y) n L_peak
  | rand {L_peak : ℕ} {dst src : Fin r} {x : RData r} :
      x.frontier ≤ L_peak → Fits w (x.regs src) →
      ExecRCodeDist w (.rand dst src) x
        ((ProbComp.unifFin (x.regs src)).eval.map fun k => x.set dst k.val) 1 L_peak
  | mono {L_peak : ℕ} {c : RCode B r} {x : RData r} {μ : PMF (RData r)} {T T' : ℝ≥0∞} :
      ExecRCodeDist w c x μ T L_peak → T ≤ T' → ExecRCodeDist w c x μ T' L_peak
  | mono_peak {L₁ L₂ : ℕ} {c : RCode B r} {x : RData r} {μ : PMF (RData r)} {T : ℝ≥0∞} :
      L₁ ≤ L₂ → ExecRCodeDist w c x μ T L₁ → ExecRCodeDist w c x μ T L₂
  | seq {L_peak : ℕ} {c₁ c₂ : RCode B r} {x : RData r} {μ₁ : PMF (RData r)}
      {μ₂ : RData r → PMF (RData r)} {T₁ : ℝ≥0∞} {T₂ : RData r → ℝ≥0∞} :
      ExecRCodeDist w c₁ x μ₁ T₁ L_peak →
      (∀ y ∈ μ₁.support, ExecRCodeDist w c₂ y (μ₂ y) (T₂ y) L_peak) →
      ExecRCodeDist w (.seq c₁ c₂) x (μ₁.bind μ₂) (T₁ + ∑' y, μ₁ y * T₂ y) L_peak
  | branch_pos {L_peak : ℕ} {cond : Cond r} {pos neg : RCode B r} {x : RData r}
      {μ : PMF (RData r)} {T : ℝ≥0∞} :
      cond.Holds x.toData → ExecRCodeDist w pos x μ T L_peak →
      ExecRCodeDist w (.branch cond pos neg) x μ (T + 1) L_peak
  | branch_neg {L_peak : ℕ} {cond : Cond r} {pos neg : RCode B r} {x : RData r}
      {μ : PMF (RData r)} {T : ℝ≥0∞} :
      ¬cond.Holds x.toData → ExecRCodeDist w neg x μ T L_peak →
      ExecRCodeDist w (.branch cond pos neg) x μ (T + 2) L_peak
  | loop_iter {L_peak : ℕ} {cond : Cond r} {body : RCode B r} {x : RData r}
      {μ₁ : PMF (RData r)} {μ₂ : RData r → PMF (RData r)} {T₁ : ℝ≥0∞} {T₂ : RData r → ℝ≥0∞} :
      cond.Holds x.toData →
      ExecRCodeDist w body x μ₁ T₁ L_peak →
      (∀ y ∈ μ₁.support, ExecRCodeDist w (.loop cond body) y (μ₂ y) (T₂ y) L_peak) →
      ExecRCodeDist w (.loop cond body) x (μ₁.bind μ₂) (T₁ + 2 + ∑' y, μ₁ y * T₂ y) L_peak
  | loop_geometric {L_peak : ℕ} {cond : Cond r} {body : RCode B r}
      (I Q : RData r → Prop) {μ_body : RData r → PMF (RData r)} {T_body : RData r → ℝ≥0∞}
      {B_body p_exit : ℝ≥0∞} {x : RData r} :
      0 < p_exit → p_exit ≠ ⊤ →
      (∀ z, I z → cond.Holds z.toData → ExecRCodeDist w body z (μ_body z) (T_body z) L_peak) →
      (∀ z, I z → cond.Holds z.toData → T_body z ≤ B_body) →
      (∀ z, I z → cond.Holds z.toData →
        ∀ y ∈ (μ_body z).support, RLoopStateInv cond I Q y) →
      (∀ z, I z → cond.Holds z.toData →
        p_exit ≤ (μ_body z).toOuterMeasure {y : RData r | ¬cond.Holds y.toData}) →
      (∀ z, ¬cond.Holds z.toData → Q z → z.frontier ≤ L_peak) →
      RLoopStateInv cond I Q x →
      ExecRCodeDist w (.loop cond body) x (loopExitRPMF cond μ_body x)
        ((B_body + 2) / p_exit + 2) L_peak

namespace ExecRCodeDist

variable {w L_peak : ℕ} {c c₁ c₂ pos neg body : RCode B r} {cond : Cond r} {x y : RData r}
  {μ μ₁ μ' : PMF (RData r)} {T T' T₁ T₂ : ℝ≥0∞}

private theorem tsum_pure_mul (y : RData r) (f : RData r → ℝ≥0∞) :
    (∑' z, PMF.pure y z * f z) = f y := by
  rw [tsum_eq_single y (fun z hz => by simp [PMF.pure_apply, hz]), PMF.pure_apply_self, one_mul]

theorem congr_dist (h : ExecRCodeDist w c x μ T L_peak) (hμ : μ = μ') (hT : T ≤ T') :
    ExecRCodeDist w c x μ' T' L_peak := hμ ▸ h.mono hT

/-- Entry hardware frontier is bounded by `L_peak`. -/
theorem frontier_le (h : ExecRCodeDist w c x μ T L_peak) : x.frontier ≤ L_peak := by
  induction h with
  | of_demonicExec hd => exact hd.frontier_le
  | rand hL _ => exact hL
  | mono _ _ ih | seq _ _ ih _ | branch_pos _ _ ih | branch_neg _ _ ih | loop_iter _ _ _ ih _ =>
    exact ih
  | mono_peak hL _ ih => exact ih.trans hL
  | loop_geometric _ _ _ _ _ _ _ _ hfr hx ih_body =>
    exact hx.elim (fun ⟨hc, hI⟩ => ih_body _ hI hc) (fun ⟨hc, hQ⟩ => hfr _ hc hQ)

/-- Every state in the support of `μ` satisfies `y.frontier ≤ L_peak`. -/
theorem post_frontier_le (h : ExecRCodeDist w c x μ T L_peak) :
    ∀ y ∈ μ.support, y.frontier ≤ L_peak := by
  induction h with
  | of_demonicExec hd =>
    intro z hz; supp_cases hz
    obtain ⟨_, rfl, hfr⟩ := hd.exists_post_frontier_le
    exact hfr
  | rand hL _ =>
    intro z hz; supp_cases hz; exact hL
  | mono _ _ ih | branch_pos _ _ ih | branch_neg _ _ ih => exact ih
  | mono_peak hL _ ih => exact fun z hz => (ih z hz).trans hL
  | seq _ _ _ ih₂ | loop_iter _ _ _ _ ih₂ =>
    intro z hz; supp_cases hz with ⟨u, hu, hzu⟩
    exact ih₂ u hu z hzu
  | loop_geometric _ _ hp_pos hp_top _ _ hinv hp_exit hfr hx _ =>
    intro z hz
    obtain ⟨⟨hcz, hQz⟩, _⟩ := mem_support_loopExitRPMF hp_pos hp_top hinv hp_exit hx hz
    exact hfr z hcz hQz

theorem loop_exit (hL : x.frontier ≤ L_peak) (hc : ¬cond.Holds x.toData) :
    ExecRCodeDist w (.loop cond body) x (PMF.pure x) 2 L_peak :=
  .of_demonicExec (RDemonicExec.loop_exit hL hc rfl)

theorem branch (hpos : cond.Holds x.toData → ExecRCodeDist w pos x μ T L_peak)
    (hneg : ¬cond.Holds x.toData → ExecRCodeDist w neg x μ T L_peak) :
    ExecRCodeDist w (.branch cond pos neg) x μ (T + 2) L_peak := by
  by_cases hc : cond.Holds x.toData
  · exact (branch_pos hc (hpos hc)).mono (add_le_add le_rfl one_le_two)
  · exact branch_neg hc (hneg hc)

theorem seq_const {μ₂ : RData r → PMF (RData r)} {T₂ : RData r → ℝ≥0∞} {B₂ : ℝ≥0∞}
    (h₁ : ExecRCodeDist w c₁ x μ₁ T₁ L_peak)
    (h₂ : ∀ y ∈ μ₁.support, ExecRCodeDist w c₂ y (μ₂ y) (T₂ y) L_peak)
    (hB₂ : ∀ y ∈ μ₁.support, T₂ y ≤ B₂) :
    ExecRCodeDist w (.seq c₁ c₂) x (μ₁.bind μ₂) (T₁ + B₂) L_peak :=
  (h₁.seq h₂).mono (add_le_add le_rfl (Cslib.Probability.PMF.tsum_mul_le_of_support μ₁ hB₂))

theorem seq_pure (h₁ : ExecRCodeDist w c₁ x (PMF.pure y) T₁ L_peak)
    (h₂ : ExecRCodeDist w c₂ y μ T₂ L_peak) :
    ExecRCodeDist w (.seq c₁ c₂) x μ (T₁ + T₂) L_peak := by
  classical
  have h := h₁.seq (c₂ := c₂) (μ₂ := fun z => if z = y then μ else PMF.pure z)
    (T₂ := fun z => if z = y then T₂ else 0) fun z hz => by
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz; simp only [hz, ↓reduceIte]; exact h₂
  exact h.congr_dist (by simp) (by simp only [tsum_pure_mul, ↓reduceIte, le_rfl])

/-- Ranked worst-case `K`-iteration `while` loop rule for `ExecRCodeDist`. -/
theorem loop_bounded (I Q : RData r → Prop) {μ_body : RData r → PMF (RData r)}
    {T_body : RData r → ℝ≥0∞} {B_body : ℝ≥0∞} (rank : RData r → ℕ) (K : ℕ)
    (hbody : ∀ z, I z → cond.Holds z.toData → ExecRCodeDist w body z (μ_body z) (T_body z) L_peak)
    (hB : ∀ z, I z → cond.Holds z.toData → T_body z ≤ B_body)
    (hinv : ∀ z, I z → cond.Holds z.toData → ∀ y ∈ (μ_body z).support,
      RLoopStateInv cond I Q y ∧ (cond.Holds y.toData → rank y < rank z))
    (hfr : ∀ z, ¬cond.Holds z.toData → Q z → z.frontier ≤ L_peak)
    (hx_inv : RLoopStateInv cond I Q x) (hrank : cond.Holds x.toData → rank x < K) :
    ExecRCodeDist w (.loop cond body) x (loopIterRPMF cond μ_body K x)
      ((K : ℝ≥0∞) * (B_body + 2) + 2) L_peak := by
  induction K generalizing x with
  | zero =>
    rcases hx_inv with ⟨hcx, _⟩ | ⟨hcx, hQx⟩
    · exact absurd (hrank hcx) (Nat.not_lt_zero _)
    · simpa [loopIterRPMF] using loop_exit (hfr x hcx hQx) hcx
  | succ K ih =>
    rcases hx_inv with ⟨hcx, hIx⟩ | ⟨hcx, hQx⟩
    · refine (loop_iter hcx (hbody x hIx hcx) fun z hz =>
        ih (hinv x hIx hcx z hz).1 fun hcz =>
          Nat.lt_of_lt_of_le ((hinv x hIx hcx z hz).2 hcz)
            (Nat.lt_succ_iff.mp (hrank hcx))).congr_dist
        (by rw [loopIterRPMF_succ, loopStepRPMF_of_holds hcx]) ?_
      rw [ENNReal.tsum_mul_right, (μ_body x).tsum_coe, one_mul, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul]
      exact (add_le_add (add_le_add (hB x hIx hcx) le_rfl) le_rfl).trans_eq (by ac_rfl)
    · exact (loop_exit (hfr x hcx hQx) hcx).congr_dist
        (loopIterRPMF_of_not_holds hcx (K + 1)).symm le_add_self

/-- Transport `ExecRCodeDist` along any defined-evaluation basis simulation `φ : B.Simulates B'`. -/
theorem mapSimulates (φ : B.Simulates B') (h : ExecRCodeDist w c x μ T L_peak) :
    ExecRCodeDist w (c.mapSimulates φ) x μ T L_peak := by
  induction h with
  | of_demonicExec hd => exact .of_demonicExec (hd.mapSimulates φ)
  | rand hL hfit => exact .rand hL hfit
  | mono _ hT ih => exact ih.mono hT
  | mono_peak hL _ ih => exact ih.mono_peak hL
  | seq _ _ ih₁ ih₂ => exact ih₁.seq ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_iter hc _ _ ihb ihr => exact .loop_iter hc ihb ihr
  | loop_geometric I Q hp_pos hp_top _ hB hinv hp_exit hfr hx ih_body =>
    exact .loop_geometric I Q hp_pos hp_top ih_body hB hinv hp_exit hfr hx

end ExecRCodeDist


section HaltedReachRDemonic
attribute [local irreducible] haltedReach

private theorem haltedReach_jump_le {w pc₁ pc₂ v : ℕ} {p : RProgram B r} {d y : RData r}
    (hj : p[pc₁]? = some (.jump pc₂)) :
    haltedReach w p v d pc₂ y ≤ haltedReach w p v d pc₁ y :=
  haltedReach_le_of_const (s := ⟨pc₁, y⟩) (v := v) (d := d) fun _ =>
    stepRandResizable_jump (s := ⟨pc₁, y⟩) hj

theorem RDemonicExec.le_haltedReach_assemble {w L_peak n pc v : ℕ} {c : RCode B r}
    {x d : RData r} {P : RData r → Prop} (h : RDemonicExec w L_peak c x n P) {p : RProgram B r}
    (hp : p.Contains pc (c.assemble pc)) :
    (⨅ (y : RData r) (_ : P y), haltedReach w p v d (pc + c.size) y) ≤
      haltedReach w p v d pc x := by
  induction h generalizing pc with
  | @op o x y P _ he hp_y =>
    exact (iInf₂_le y hp_y).trans
      (haltedReach_le_of_const fun _ => stepRandResizable_op (s := ⟨pc, x⟩) hp.head he)
  | @grow dst x P _ hfit hp_y =>
    refine LE.le.trans (le_iInf fun (f : RState r → ℕ → ℕ) =>
      iInf₂_le _ (hp_y _ (demonicGrow_advGrowMem w (f ⟨pc, x⟩) _ _ _)))
      (haltedReach_le_of_pure fun f => stepRandResizable_grow_of_fits (s := ⟨pc, x⟩) hp.head hfit)
  | @shrink x P _ hk hp_y =>
    exact (iInf₂_le _ hp_y).trans
      (haltedReach_le_of_const fun _ => stepRandResizable_shrink_of_pos (s := ⟨pc, x⟩) hp.head hk)
  | @rand dst src x P _ hfit hp_y =>
    refine ((ProbComp.expect_const (ProbComp.unifFin (x.regs src)) _).symm.trans_le ?_).trans
      (haltedReach_le_of_rand hp.head hfit)
    exact tsum_le_tsum fun k => mul_le_mul_right (iInf₂_le _ (hp_y k.val k.is_le)) _
  | @seq c₁ c₂ x _ _ Q P _ _ ih₁ ih₂ =>
    refine (le_iInf₂ fun y₁ hy₁ => ?_).trans (ih₁ hp.append_left)
    simpa only [RCode.size, Nat.add_assoc] using ih₂ y₁ hy₁ hp.seq_right
  | @branch_pos c pos neg x _ P hc _ ih =>
    rw [show pc + (RCode.branch c pos neg).size = pc + neg.size + 2 + pos.size by
      simp only [RCode.size]; omega]
    exact (ih hp.branch_pos).trans (haltedReach_le_of_const fun _ =>
      stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.branch_head hc)
  | @branch_neg c pos neg x _ P hc _ ih =>
    refine (le_iInf₂ fun y hy => (iInf₂_le y hy).trans ?_).trans
      ((ih hp.branch_neg).trans (haltedReach_le_of_const fun _ =>
        stepRandResizable_branch_neg (s := ⟨pc, x⟩) hp.branch_head hc))
    simpa only [RCode.size, Nat.add_assoc] using
      haltedReach_jump_le (d := d) (y := y) hp.branch_jump
  | @loop_exit c body x P _ hc hp_y =>
    refine (iInf₂_le x hp_y).trans <| LE.le.trans ?_
      (haltedReach_le_of_const fun _ => stepRandResizable_branch_neg (s := ⟨pc, x⟩) hp.head hc)
    simpa only [RCode.size, Nat.add_assoc] using haltedReach_jump_le (d := d) (y := x) hp.loop_exit
  | @loop_iter c body x _ _ Q P hc _ _ ihb ihl =>
    exact (le_iInf₂ fun y hy => (ihl y hy hp).trans
      (haltedReach_jump_le (d := d) (y := y) hp.loop_back)).trans
      ((ihb hp.loop_body).trans
        (haltedReach_le_of_const fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.head hc))
  | mono _ _ hPQ ih =>
    exact (le_iInf₂ fun y hy => iInf₂_le y (hPQ y hy)).trans (ih hp)

end HaltedReachRDemonic

namespace ExecRCodeDist

variable {w L_peak : ℕ} {c : RCode B r} {x : RData r} {μ : PMF (RData r)} {T : ℝ≥0∞}

private theorem supExpectedStepsWithin_succ_le_of_const {w n : ℕ} {p : RProgram B r}
    {s t : RState r}
    (hstep : ∀ f : RState r → ℕ → ℕ, stepRandResizable w f p (.running s) = pure (.running t)) :
    supExpectedStepsWithin w p (n + 1) (.running s) ≤
      1 + supExpectedStepsWithin w p n (.running t) := by
  refine iSup_le fun adv => ?_
  rw [expectedStepsWithinAdv_running_succ, hstep, ProbComp.expect_pure]
  exact add_le_add le_rfl (le_iSup
    (fun adv' => expectedStepsWithinAdv w adv' p n (.running t)) (adv.shift 1))

private theorem tsum_supExpectedStepsWithin_jump {w N pc₁ pc₂ : ℕ} {p : RProgram B r}
    (hj : p[pc₁]? = some (.jump pc₂)) (μ : PMF (RData r)) :
    (∑' y, μ y * supExpectedStepsWithin w p N (.running ⟨pc₁, y⟩)) ≤
      1 + ∑' y, μ y * supExpectedStepsWithin w p N (.running ⟨pc₂, y⟩) := by
  calc ∑' y, μ y * supExpectedStepsWithin w p N (.running ⟨pc₁, y⟩)
      ≤ ∑' y, μ y * (1 + supExpectedStepsWithin w p N (.running ⟨pc₂, y⟩)) :=
        tsum_le_tsum fun y => mul_le_mul_right (supExpectedStepsWithin_le_of_const fun _ =>
          stepRandResizable_jump (s := ⟨pc₁, y⟩) hj) _
    _ = 1 + ∑' y, μ y * supExpectedStepsWithin w p N (.running ⟨pc₂, y⟩) := by
        simp_rw [mul_add, tsum_add, mul_one, μ.tsum_coe]

private theorem supExpectedStepsWithin_loop_geometric {cond : Cond r} {body : RCode B r}
    {I Q : RData r → Prop} {μ_body : RData r → PMF (RData r)} {T_body : RData r → ℝ≥0∞}
    {B_body p_exit : ℝ≥0∞} {p : RProgram B r} {pc N : ℕ}
    (hp : p.Contains pc ((RCode.loop cond body).assemble pc))
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hB : ∀ z, I z → cond.Holds z.toData → T_body z ≤ B_body)
    (hinv : ∀ z, I z → cond.Holds z.toData → ∀ y ∈ (μ_body z).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ z, I z → cond.Holds z.toData →
      p_exit ≤ (μ_body z).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    (ih_body : ∀ z, I z → cond.Holds z.toData → ∀ n,
      supExpectedStepsWithin w p n (.running ⟨pc + 2, z⟩) ≤ T_body z +
        ∑' u, μ_body z u * supExpectedStepsWithin w p n (.running ⟨pc + 2 + body.size, u⟩))
    (hx_inv : RLoopStateInv cond I Q x) :
    supExpectedStepsWithin w p N (.running ⟨pc, x⟩) ≤
      (B_body + 2) / p_exit + 2 +
        ∑' y, loopExitRPMF cond μ_body x y *
          supExpectedStepsWithin w p N (.running ⟨pc + (RCode.loop cond body).size, y⟩) := by
  set K_cont : RData r → ℝ≥0∞ := fun y =>
    supExpectedStepsWithin w p N (.running ⟨pc + (RCode.loop cond body).size, y⟩)
  set M := (B_body + 2) / p_exit
  have hmain : ∀ n ≤ N, ∀ z, RLoopStateInv cond I Q z →
      supExpectedStepsWithin w p n (.running ⟨pc, z⟩) ≤
        (if cond.Holds z.toData then M else 0) + 2 +
          ∑' y, loopExitRPMF cond μ_body z y * K_cont y := by
    intro n; induction n with
    | zero => simp
    | succ n ihn =>
      intro hn z hz_inv
      rcases hz_inv with ⟨hcz, hIz⟩ | ⟨hcz, _⟩
      · simp only [hcz, ↓reduceIte]
        have h1 := supExpectedStepsWithin_succ_le_of_const (w := w) (n := n) (p := p)
          fun _ => stepRandResizable_branch_pos (s := ⟨pc, z⟩) hp.head hcz
        have hbody := (ih_body z hIz hcz n).trans (add_le_add (hB z hIz hcz) le_rfl)
        have hback := tsum_supExpectedStepsWithin_jump (w := w) (N := n) hp.loop_back (μ_body z)
        have hbind : (∑' u, μ_body z u * ∑' y, loopExitRPMF cond μ_body u y * K_cont y) =
            ∑' y, loopExitRPMF cond μ_body z y * K_cont y := by
          rw [loopExitRPMF_of_holds hp_pos hp_top hinv hp_exit hIz hcz]
          exact (Cslib.Probability.PMF.tsum_bind_mul _ _ _).symm
        have hih : (∑' u, μ_body z u * supExpectedStepsWithin w p n (.running ⟨pc, u⟩)) ≤
            (∑' u, μ_body z u * (if cond.Holds u.toData then M else 0)) + 2 +
              ∑' y, loopExitRPMF cond μ_body z y * K_cont y :=
          (Cslib.Probability.PMF.tsum_mul_mono_support (μ_body z) fun u hu =>
            ihn (Nat.le_of_succ_le hn) u (hinv z hIz hcz u hu)).trans_eq <| by
            simp_rw [mul_add, tsum_add, ENNReal.tsum_mul_right, (μ_body z).tsum_coe,
              one_mul, hbind]
        have hdrift := pmf_rdata_step_drift_bound (μ_body z) cond (C := B_body + 2)
          hp_pos hp_top (hp_exit z hIz hcz)
        calc supExpectedStepsWithin w p (n + 1) (.running ⟨pc, z⟩)
            ≤ 1 + (B_body + (1 + ∑' u, μ_body z u *
                supExpectedStepsWithin w p n (.running ⟨pc, u⟩))) :=
              h1.trans (add_le_add le_rfl (hbody.trans (add_le_add le_rfl hback)))
          _ = B_body + 2 + ∑' u, μ_body z u *
                supExpectedStepsWithin w p n (.running ⟨pc, u⟩) := by
              rw [show (2 : ℝ≥0∞) = 1 + 1 from one_add_one_eq_two.symm]; ac_rfl
          _ ≤ (B_body + 2 + ∑' u, μ_body z u * (if cond.Holds u.toData then M else 0)) + 2 +
                ∑' y, loopExitRPMF cond μ_body z y * K_cont y :=
              (add_le_add le_rfl hih).trans_eq (by ac_rfl)
          _ ≤ M + 2 + ∑' y, loopExitRPMF cond μ_body z y * K_cont y :=
              add_le_add (add_le_add hdrift le_rfl) le_rfl
      · simp only [hcz, ↓reduceIte, zero_add]
        rw [loopExitRPMF_of_not_holds hcz, tsum_pure_mul]
        have h1 := supExpectedStepsWithin_succ_le_of_const (w := w) (n := n) (p := p)
          fun _ => stepRandResizable_branch_neg (s := ⟨pc, z⟩) hp.head hcz
        refine (h1.trans (add_le_add le_rfl (supExpectedStepsWithin_le_of_const fun _ =>
          stepRandResizable_jump (s := ⟨pc + 1, z⟩) hp.loop_exit))).trans ?_
        rw [← add_assoc (1 : ℝ≥0∞), one_add_one_eq_two]
        exact add_le_add le_rfl <| by
          simpa [K_cont, RCode.size, Nat.add_assoc] using supExpectedStepsWithin_mono w p
            (.running ⟨pc + (body.size + 3), z⟩) (Nat.le_of_succ_le hn)
  refine (hmain N le_rfl x hx_inv).trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  split_ifs <;> simp

/-- Finite-horizon Bellman inequality for `ExecRCodeDist` inside any containing
`p : RProgram B r`. -/
theorem supExpectedStepsWithin_assemble (h : ExecRCodeDist w c x μ T L_peak) {p : RProgram B r}
    {pc : ℕ} (hp : p.Contains pc (c.assemble pc)) (N : ℕ) :
    supExpectedStepsWithin w p N (.running ⟨pc, x⟩) ≤
      T + ∑' y, μ y * supExpectedStepsWithin w p N (.running ⟨pc + c.size, y⟩) := by
  induction h generalizing pc N with
  | @of_demonicExec _ n c x y hd =>
    rw [tsum_pure_mul]
    exact (hd.supExpectedStepsWithin_assemble hp).trans
      (add_le_add le_rfl (iSup₂_le fun z hz => hz ▸ le_rfl))
  | @rand _ dst src x _ hfit =>
    have hle : supExpectedStepsWithin w p N (.running ⟨pc, x⟩) ≤
        1 + (ProbComp.unifFin (x.regs src)).expect (fun k : Fin (x.regs src + 1) =>
          supExpectedStepsWithin w p N (.running ⟨pc + 1, x.set dst k.val⟩)) :=
      iSup_le fun adv => (expectedStepsWithinAdv_running_le w adv p N ⟨pc, x⟩).trans_eq <| by
        rw [stepRandResizable_rand_of_fits (s := ⟨pc, x⟩) hp.head hfit, ProbComp.expect_bind]
        simp only [ProbComp.expect_pure]
    refine hle.trans_eq ?_
    simp only [RCode.size]
    exact congrArg (1 + ·) (Cslib.Probability.PMF.tsum_map_mul
      (ProbComp.unifFin (x.regs src)).eval (fun k => x.set dst k.val)
      (fun y => supExpectedStepsWithin w p N (.running ⟨pc + 1, y⟩))).symm
  | mono _ hT ih => exact (ih hp N).trans (add_le_add hT le_rfl)
  | mono_peak _ _ ih => exact ih hp N
  | @seq _ c₁ c₂ x μ₁ μ₂ T₁ T₂ _ _ ih₁ ih₂ =>
    refine (ih₁ hp.append_left N).trans <| (add_le_add le_rfl ?_).trans_eq (add_assoc _ _ _).symm
    refine (Cslib.Probability.PMF.tsum_mul_mono_support μ₁ fun y hy =>
      ih₂ y hy hp.seq_right N).trans_eq ?_
    simp_rw [mul_add, tsum_add]
    congr 1; simp only [RCode.size, Nat.add_assoc]
    exact (Cslib.Probability.PMF.tsum_bind_mul μ₁ μ₂ _).symm
  | @branch_pos _ cond pos neg x μ T hc _ ih =>
    have hpc : pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) := by omega
    refine ((supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.branch_head hc).trans
      (add_le_add le_rfl (ih hp.branch_pos N))).trans_eq ?_
    simp only [RCode.size, hpc]; ac_rfl
  | @branch_neg _ cond pos neg x μ T hc _ ih =>
    refine ((supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_neg (s := ⟨pc, x⟩) hp.branch_head hc).trans
      (add_le_add le_rfl ((ih hp.branch_neg N).trans
        (add_le_add le_rfl (tsum_supExpectedStepsWithin_jump hp.branch_jump μ))))).trans_eq ?_
    simp only [RCode.size, Nat.add_assoc, show (2 : ℝ≥0∞) = 1 + 1 from one_add_one_eq_two.symm]
    ac_rfl
  | @loop_iter _ cond body x μ₁ μ₂ T₁ T₂ hc _ _ ihb ihr =>
    have hback : (∑' y, μ₁ y * supExpectedStepsWithin w p N (.running ⟨pc + 2 + body.size, y⟩)) ≤
        1 + ((∑' y, μ₁ y * T₂ y) + ∑' z, (μ₁.bind μ₂) z *
          supExpectedStepsWithin w p N (.running ⟨pc + (RCode.loop cond body).size, z⟩)) := by
      refine (tsum_supExpectedStepsWithin_jump hp.loop_back μ₁).trans (add_le_add le_rfl ?_)
      refine (Cslib.Probability.PMF.tsum_mul_mono_support μ₁ fun y hy =>
        ihr y hy hp N).trans_eq ?_
      simp_rw [mul_add, tsum_add]
      exact congrArg (_ + ·) (Cslib.Probability.PMF.tsum_bind_mul μ₁ μ₂ _).symm
    exact ((supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.head hc).trans
      (add_le_add le_rfl ((ihb hp.loop_body N).trans (add_le_add le_rfl hback)))).trans_eq <| by
      rw [show (2 : ℝ≥0∞) = 1 + 1 from one_add_one_eq_two.symm]; ac_rfl
  | @loop_geometric _ cond body I Q μ_body T_body B_body p_exit x
      hp_pos hp_top _ hB hinv hp_exit _ hx_inv ih_body =>
    exact supExpectedStepsWithin_loop_geometric hp hp_pos hp_top hB hinv hp_exit
      (fun z hIz hcz n => ih_body z hIz hcz hp.loop_body n) hx_inv

/-- Full-horizon Bellman inequality for `ExecRCodeDist`. -/
theorem expectedStepsFromDemonic_assemble (h : ExecRCodeDist w c x μ T L_peak) {p : RProgram B r}
    {pc : ℕ} (hp : p.Contains pc (c.assemble pc)) :
    expectedStepsFromDemonic w p (.running ⟨pc, x⟩) ≤
      T + ∑' y, μ y * expectedStepsFromDemonic w p (.running ⟨pc + c.size, y⟩) := by
  rw [← iSup_supExpectedStepsWithin w p (.running ⟨pc, x⟩)]
  refine iSup_le fun N => (h.supExpectedStepsWithin_assemble hp N).trans ?_
  exact add_le_add le_rfl (tsum_le_tsum fun y => mul_le_mul_right
    (supExpectedStepsWithin_le_expectedStepsFromDemonic w p N (.running ⟨pc + c.size, y⟩)) _)

private theorem demonicSafeWithin_loop_geometric {cond : Cond r} {body : RCode B r}
    {I Q : RData r → Prop} {μ_body : RData r → PMF (RData r)} {p_exit : ℝ≥0∞}
    {L_bound : ℕ} {p : RProgram B r} {pc T_hor : ℕ}
    (hp : p.Contains pc ((RCode.loop cond body).assemble pc))
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ z, I z → cond.Holds z.toData → ∀ y ∈ (μ_body z).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ z, I z → cond.Holds z.toData →
      p_exit ≤ (μ_body z).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    (hfr_active : ∀ z, I z → cond.Holds z.toData → z.frontier ≤ L_bound)
    (hfr_exit : ∀ z, ¬cond.Holds z.toData → Q z → z.frontier ≤ L_bound)
    (ih_body : ∀ z, I z → cond.Holds z.toData → ∀ k,
      (∀ u ∈ (μ_body z).support, DemonicSafeWithin w L_bound k p ⟨pc + 2 + body.size, u⟩) →
      DemonicSafeWithin w L_bound k p ⟨pc + 2, z⟩)
    {x : RData r} (hx_inv : RLoopStateInv cond I Q x)
    (hcont : ∀ y ∈ (loopExitRPMF cond μ_body x).support,
      DemonicSafeWithin w L_bound T_hor p ⟨pc + (RCode.loop cond body).size, y⟩) :
    DemonicSafeWithin w L_bound T_hor p ⟨pc, x⟩ := by
  have hfr_inv : ∀ u, RLoopStateInv cond I Q u → u.frontier ≤ L_bound :=
    fun u hu => hu.elim (fun ⟨hc, hI⟩ => hfr_active u hI hc) (fun ⟨hc, hQ⟩ => hfr_exit u hc hQ)
  have hmain : ∀ n ≤ T_hor, ∀ z, RLoopStateInv cond I Q z →
      (∀ y ∈ (loopExitRPMF cond μ_body z).support,
        DemonicSafeWithin w L_bound T_hor p ⟨pc + (RCode.loop cond body).size, y⟩) →
      DemonicSafeWithin w L_bound n p ⟨pc, z⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro hn z hz_inv hcont_z
      rcases hz_inv with ⟨hcz, hIz⟩ | ⟨hcz, hQz⟩
      · refine demonicSafeWithin_of_pure (hfr_active z hIz hcz)
          (fun _ => stepRandResizable_branch_pos (s := ⟨pc, z⟩) hp.head hcz)
          fun _ k hk => ih_body z hIz hcz k fun u hu => ?_
        have hu_inv := hinv z hIz hcz u hu
        refine demonicSafeWithin_of_pure (hfr_inv u hu_inv)
          (fun _ => stepRandResizable_jump (s := ⟨pc + 2 + body.size, u⟩) hp.loop_back)
          fun _ k' hk' => ihn k' (by omega) (by omega) u hu_inv fun y hy => hcont_z y ?_
        rw [loopExitRPMF_of_holds hp_pos hp_top hinv hp_exit hIz hcz, PMF.mem_support_bind_iff]
        exact ⟨u, hu, hy⟩
      · refine demonicSafeWithin_of_pure (hfr_exit z hcz hQz)
          (fun _ => stepRandResizable_branch_neg (s := ⟨pc, z⟩) hp.head hcz)
          fun _ k hk => demonicSafeWithin_of_pure (hfr_exit z hcz hQz)
            (fun _ => stepRandResizable_jump (s := ⟨pc + 1, z⟩) hp.loop_exit) fun _ k' hk' => ?_
        simpa [RCode.size, Nat.add_assoc] using
          (hcont_z z (by simp [loopExitRPMF_of_not_holds hcz])).anti (by omega)
  exact hmain T_hor le_rfl x hx_inv hcont

/-- Horizon-bounded safety and peak-frontier propagation for `ExecRCodeDist`. -/
theorem demonicSafeWithin_assemble (h : ExecRCodeDist w c x μ T L_peak) {L_bound : ℕ}
    (hL_bound : L_peak ≤ L_bound) {p : RProgram B r} {pc T_hor : ℕ}
    (hp : p.Contains pc (c.assemble pc))
    (hcont : ∀ y ∈ μ.support, DemonicSafeWithin w L_bound T_hor p ⟨pc + c.size, y⟩) :
    DemonicSafeWithin w L_bound T_hor p ⟨pc, x⟩ := by
  induction h generalizing pc T_hor with
  | of_demonicExec hd =>
    exact (hd.mono_peak hL_bound).demonicSafeWithin_assemble hp fun z hz =>
      hz ▸ hcont z (by simp [hz])
  | @rand _ dst src x hL hfit =>
    refine demonicSafeWithin_of_rand (hL.trans hL_bound) hp.head hfit fun j k hk =>
      (hcont (x.set dst j.val) <| (PMF.mem_support_map_iff _ _ _).mpr
        ⟨j, ProbComp.support_eval _ ▸ ProbComp.mem_support_unifFin _ j, rfl⟩).anti (by omega)
  | mono _ _ ih => exact ih hL_bound hp hcont
  | mono_peak hL _ ih => exact ih (hL.trans hL_bound) hp hcont
  | @seq _ c₁ c₂ x μ₁ μ₂ _ _ _ _ ih₁ ih₂ =>
    refine ih₁ hL_bound hp.append_left fun y₁ hy₁ =>
      ih₂ y₁ hy₁ hL_bound hp.seq_right fun y₂ hy₂ => ?_
    simpa [RCode.size, Nat.add_assoc] using
      hcont y₂ ((PMF.mem_support_bind_iff _ _ _).mpr ⟨y₁, hy₁, hy₂⟩)
  | @branch_pos _ cond pos neg x μ _ hc hpos ih =>
    have hpc : pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) := by omega
    refine demonicSafeWithin_of_pure (hpos.frontier_le.trans hL_bound)
      (fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.branch_head hc)
      fun _ k hk => ih hL_bound hp.branch_pos fun y hy => by
        simpa [RCode.size, hpc] using (hcont y hy).anti (by omega)
  | @branch_neg _ cond pos neg x μ _ hc hneg ih =>
    refine demonicSafeWithin_of_pure (hneg.frontier_le.trans hL_bound)
      (fun _ => stepRandResizable_branch_neg (s := ⟨pc, x⟩) hp.branch_head hc)
      fun _ k hk => ih hL_bound hp.branch_neg fun y hy =>
        demonicSafeWithin_of_pure (hcont y hy).frontier_le
          (fun _ => stepRandResizable_jump (s := ⟨pc + 1 + neg.size, y⟩) hp.branch_jump)
          fun _ k' hk' => by simpa [RCode.size, Nat.add_assoc] using (hcont y hy).anti (by omega)
  | @loop_iter _ cond body x μ₁ μ₂ _ _ hc hbody hrest ihb ihr =>
    refine demonicSafeWithin_of_pure (hbody.frontier_le.trans hL_bound)
      (fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.head hc)
      fun _ k hk => ihb hL_bound hp.loop_body fun y hy =>
        demonicSafeWithin_of_pure ((hrest y hy).frontier_le.trans hL_bound)
          (fun _ => stepRandResizable_jump (s := ⟨pc + 2 + body.size, y⟩) hp.loop_back)
          fun _ k' hk' => ihr y hy hL_bound hp fun z hz =>
            (hcont z ((PMF.mem_support_bind_iff _ _ _).mpr ⟨y, hy, hz⟩)).anti (by omega)
  | @loop_geometric _ cond body I Q μ_body _ _ p_exit x
      hp_pos hp_top hbody _ hinv hp_exit hfr hx_inv ih_body =>
    exact demonicSafeWithin_loop_geometric hp hp_pos hp_top hinv hp_exit
      (fun z hIz hcz => (hbody z hIz hcz).frontier_le.trans hL_bound)
      (fun z hcz hQz => (hfr z hcz hQz).trans hL_bound)
      (fun z hIz hcz _ hcont_b => ih_body z hIz hcz hL_bound hp.loop_body hcont_b)
      hx_inv hcont

section HaltedReachExecRCodeDist
attribute [local irreducible] haltedReach

private theorem le_haltedReach_loop_geometric {cond : Cond r} {body : RCode B r}
    {I Q : RData r → Prop} {μ_body : RData r → PMF (RData r)} {p_exit : ℝ≥0∞}
    {p : RProgram B r} {pc v : ℕ} {d : RData r}
    (hp : p.Contains pc ((RCode.loop cond body).assemble pc))
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ z, I z → cond.Holds z.toData → ∀ y ∈ (μ_body z).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ z, I z → cond.Holds z.toData →
      p_exit ≤ (μ_body z).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    (ih_body : ∀ z, I z → cond.Holds z.toData →
      (∑' u, μ_body z u * haltedReach w p v d (pc + 2 + body.size) u) ≤
        haltedReach w p v d (pc + 2) z)
    (hx_inv : RLoopStateInv cond I Q x) :
    (∑' y, loopExitRPMF cond μ_body x y *
      haltedReach w p v d (pc + (RCode.loop cond body).size) y) ≤
      haltedReach w p v d pc x := by
  set H_loop : RData r → ℝ≥0∞ := haltedReach w p v d pc
  set H_exit : RData r → ℝ≥0∞ := haltedReach w p v d (pc + (RCode.loop cond body).size)
  have hpc : pc + body.size + 3 = pc + (body.size + 3) := by omega
  have hexit_le : ∀ z, ¬cond.Holds z.toData → H_exit z ≤ H_loop z := fun z hcz =>
    ((show H_exit z ≤ haltedReach w p v d (pc + 1) z by
      simpa only [H_exit, RCode.size, hpc] using
        haltedReach_jump_le (d := d) (y := z) hp.loop_exit)).trans
      (haltedReach_le_of_const fun _ => stepRandResizable_branch_neg (s := ⟨pc, z⟩) hp.head hcz)
  have hiter_le : ∀ K z, RLoopStateInv cond I Q z →
      (∑' y, loopIterRPMF cond μ_body K z y * H_loop y) ≤ H_loop z := by
    intro K; induction K with
    | zero => intro z _; rw [show loopIterRPMF cond μ_body 0 z = PMF.pure z from rfl, tsum_pure_mul]
    | succ K ihK =>
      intro z hz_inv
      rcases hz_inv with ⟨hcz, hIz⟩ | ⟨hcz, _⟩
      · rw [loopIterRPMF_succ, loopStepRPMF_of_holds hcz,
          Cslib.Probability.PMF.tsum_bind_mul (μ_body z) (loopIterRPMF cond μ_body K) H_loop]
        refine (Cslib.Probability.PMF.tsum_mul_mono_support (μ_body z) fun u hu =>
          ihK u (hinv z hIz hcz u hu)).trans <|
          (tsum_le_tsum fun u => mul_le_mul_right
            (haltedReach_jump_le (d := d) (y := u) hp.loop_back) _).trans <|
          (ih_body z hIz hcz).trans <|
          haltedReach_le_of_const fun _ => stepRandResizable_branch_pos (s := ⟨pc, z⟩) hp.head hcz
      · rw [loopIterRPMF_of_not_holds hcz, tsum_pure_mul]
  have hrewrite : (∑' y, loopExitRPMF cond μ_body x y * H_exit y) =
      ⨆ K : ℕ, ∑' y, Set.indicator {w' : RData r | ¬cond.Holds w'.toData}
        (loopIterRPMF cond μ_body K x) y * H_exit y := by
    simp_rw [loopExitRPMF_apply_of_hasSum
      (hasSum_loopExitRDensity hp_pos hp_top hinv hp_exit hx_inv), ENNReal.iSup_mul]
    exact ENNReal.tsum_iSup_of_monotone fun y _ _ hK =>
      mul_le_mul_of_nonneg_right (loopIterRPMF_indicator_mono cond μ_body x y hK) zero_le
  rw [hrewrite]
  refine iSup_le fun K => (tsum_le_tsum fun y => ?_).trans (hiter_le K x hx_inv)
  by_cases hcy : ¬cond.Holds y.toData
  · rw [Set.indicator_of_mem hcy]; exact mul_le_mul_right (hexit_le y hcy) _
  · simp [Set.indicator_of_notMem, hcy]

/-- Halting-reachability propagation for `ExecRCodeDist`. -/
theorem le_haltedReach_assemble (h : ExecRCodeDist w c x μ T L_peak) {p : RProgram B r}
    {pc v : ℕ} {d : RData r} (hp : p.Contains pc (c.assemble pc)) :
    (∑' y, μ y * haltedReach w p v d (pc + c.size) y) ≤ haltedReach w p v d pc x := by
  induction h generalizing pc with
  | of_demonicExec hd =>
    rw [tsum_pure_mul]
    exact (le_iInf₂ fun z hz => hz ▸ le_rfl).trans (hd.le_haltedReach_assemble hp)
  | @rand _ dst src x _ hfit =>
    refine (Cslib.Probability.PMF.tsum_map_mul (ProbComp.unifFin (x.regs src)).eval
      (fun k => x.set dst k.val) (haltedReach w p v d (pc + 1))).trans_le ?_
    exact haltedReach_le_of_rand hp.head hfit
  | mono _ _ ih | mono_peak _ _ ih => exact ih hp
  | @seq _ c₁ c₂ x μ₁ μ₂ _ _ _ _ ih₁ ih₂ =>
    simp only [RCode.size, ← Nat.add_assoc]
    rw [Cslib.Probability.PMF.tsum_bind_mul μ₁ μ₂ _]
    exact (Cslib.Probability.PMF.tsum_mul_mono_support μ₁ fun y₁ hy₁ =>
      ih₂ y₁ hy₁ hp.seq_right).trans (ih₁ hp.append_left)
  | @branch_pos _ cond pos neg x μ _ hc _ ih =>
    rw [show pc + (RCode.branch cond pos neg).size = pc + neg.size + 2 + pos.size by
      simp only [RCode.size]; omega]
    exact (ih hp.branch_pos).trans (haltedReach_le_of_const fun _ =>
      stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.branch_head hc)
  | @branch_neg _ cond pos neg x μ _ hc _ ih =>
    refine (tsum_le_tsum fun y => mul_le_mul_right ?_ (μ y)).trans
      ((ih hp.branch_neg).trans (haltedReach_le_of_const fun _ =>
        stepRandResizable_branch_neg (s := ⟨pc, x⟩) hp.branch_head hc))
    simpa only [RCode.size, Nat.add_assoc] using
      haltedReach_jump_le (d := d) (y := y) hp.branch_jump
  | @loop_iter _ cond body x μ₁ μ₂ _ _ hc _ _ ihb ihr =>
    rw [Cslib.Probability.PMF.tsum_bind_mul μ₁ μ₂ _]
    exact (Cslib.Probability.PMF.tsum_mul_mono_support μ₁ fun y₁ hy₁ =>
      (ihr y₁ hy₁ hp).trans (haltedReach_jump_le (d := d) (y := y₁) hp.loop_back)).trans
      ((ihb hp.loop_body).trans (haltedReach_le_of_const fun _ =>
        stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.head hc))
  | @loop_geometric _ cond body I Q μ_body _ _ p_exit x
      hp_pos hp_top _ _ hinv hp_exit _ hx_inv ih_body =>
    exact le_haltedReach_loop_geometric hp hp_pos hp_top hinv hp_exit
      (fun z hIz hcz => ih_body z hIz hcz hp.loop_body) hx_inv

end HaltedReachExecRCodeDist

/-- **Main Structured-to-Flat Resizable Word RAM Compilation (`toExecRProgramDist`).**
Every `ExecRCodeDist w c x μ T L_peak` certificate compiles via `c.program out` to
`ExecRProgramDist w (c.program out) out x μ (T + 1) L_peak`. -/
theorem toExecRProgramDist (h : ExecRCodeDist w c x μ T L_peak) (out : Fin r) :
    ExecRProgramDist w (c.program out) out x μ (T + 1) L_peak := by
  have hp : (c.program out).Contains 0 (c.assemble 0) :=
    (RProgram.Contains.self (c.program out)).append_left
  have hhalt : (c.program out)[0 + c.size]? = some (.halt out) := by simp [RCode.program]
  have hsafe : ∀ T_hor, DemonicSafeWithin w L_peak T_hor (c.program out) ⟨0, x⟩ := fun T_hor =>
    h.demonicSafeWithin_assemble le_rfl hp fun y hy adv t _ cfg hcfg => by
      cases t <;> simp only [evalRandDemonic, runRandResizable_zero, runRandResizable_succ,
          stepRandResizable_halt (s := ⟨0 + c.size, y⟩) hhalt, pure_bind, runRandResizable_halted,
          ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hcfg <;>
        exact hcfg ▸ h.post_frontier_le y hy
  refine ⟨fun adv t => (PMF.apply_eq_zero_iff _ _).mpr fun hmem =>
      (hsafe t adv t le_rfl .faulted hmem).ne_faulted rfl,
    fun adv t cfg hcfg => (hsafe t adv t le_rfl cfg hcfg).frontierLe, ?_, fun adv y => ?_⟩
  · refine (h.expectedStepsFromDemonic_assemble hp).trans <| add_le_add le_rfl <|
      Cslib.Probability.PMF.tsum_mul_le_of_support μ fun y _ => iSup_le fun adv => le_of_eq ?_
    rw [expectedStepsFromAdv_running, stepRandResizable_halt (s := ⟨0 + c.size, y⟩) hhalt,
      ProbComp.expect_pure, expectedStepsFromAdv_halted, add_zero]
  · have h1 : (1 : ℝ≥0∞) ≤ haltedReach w (c.program out) (y.regs out) y (0 + c.size) y :=
      le_iInf fun adv' => le_iSup_of_le 1 <| by
        rw [evalRandDemonic, runRandResizable_succ,
          stepRandResizable_halt (s := ⟨0 + c.size, y⟩) hhalt, pure_bind,
          runRandResizable_zero, ProbComp.eval_pure, PMF.pure_apply_self]
    have hμ : μ y ≤ μ y * haltedReach w (c.program out) (y.regs out) y (0 + c.size) y := by
      simpa using mul_le_mul_right h1 (μ y)
    exact (hμ.trans (le_tsum (f := fun z => μ z *
        haltedReach w (c.program out) (y.regs out) y (0 + c.size) z) y)).trans
      ((h.le_haltedReach_assemble (v := y.regs out) (d := y) hp).trans (iInf_le _ adv))

end ExecRCodeDist

/-! ## Lifting frontier-bounded randomized `WordRAM.Code` executions (`ExecRandBounded`) -/

/-- Frontier-bounded randomized big-step execution of a structured `Code B r`. Mirrors
`Cslib.WordRAM.ExecRand` while recording `Op.BoundedAccess L o x` on every data instruction,
allowing any non-allocating randomized subroutine to lift directly to `ExecRCodeDist` on
`RCode.ofCode c` (and across injective register renamings `c.rename f`). -/
inductive ExecRandBounded {B : Basis} {r : ℕ} (w L : ℕ) :
    Code B r → Data r → ProbComp (Data r × ℕ) → Prop where
  /-- A data instruction whose memory access stays strictly below `L` takes `1` step. -/
  | op {o : Op B r} {x y : Data r} :
      o.BoundedAccess L x → o.eval w x = some y →
      ExecRandBounded w L (.op o) x (pure (y, 1))
  /-- Random uniform draw `rand dst src` takes `1` step with no memory access. -/
  | rand {dst src : Fin r} {x : Data r} :
      Fits w (x.regs src) →
      ExecRandBounded w L (.rand dst src) x (do
        let k ← ProbComp.unifFin (x.regs src)
        pure (x.set dst k.val, 1))
  /-- Sequencing composes bounded-access randomized executions via monadic `bind`. -/
  | seq {c₁ c₂ : Code B r} {x : Data r}
      {m₁ : ProbComp (Data r × ℕ)} {m₂ : Data r → ProbComp (Data r × ℕ)} :
      ExecRandBounded w L c₁ x m₁ →
      (∀ z ∈ m₁.support, ExecRandBounded w L c₂ z.1 (m₂ z.1)) →
      ExecRandBounded w L (.seq c₁ c₂) x (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2))
  /-- Positive branch of a conditional adds `1` step. -/
  | branch_pos {cond : Cond r} {pos neg : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)} :
      cond.Holds x → ExecRandBounded w L pos x m →
      ExecRandBounded w L (.branch cond pos neg) x ((fun z => (z.1, z.2 + 1)) <$> m)
  /-- Negative branch of a conditional adds `2` steps. -/
  | branch_neg {cond : Cond r} {pos neg : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)} :
      ¬cond.Holds x → ExecRandBounded w L neg x m →
      ExecRandBounded w L (.branch cond pos neg) x ((fun z => (z.1, z.2 + 2)) <$> m)
  /-- Exiting a while loop takes `2` steps. -/
  | loop_exit {cond : Cond r} {body : Code B r} {x : Data r} :
      ¬cond.Holds x → ExecRandBounded w L (.loop cond body) x (pure (x, 2))
  /-- One iteration of a while loop followed by the rest adds `z₁.2 + z₂.2 + 2` steps. -/
  | loop_iter {cond : Cond r} {body : Code B r} {x : Data r}
      {m₁ : ProbComp (Data r × ℕ)} {m₂ : Data r → ProbComp (Data r × ℕ)} :
      cond.Holds x → ExecRandBounded w L body x m₁ →
      (∀ z ∈ m₁.support, ExecRandBounded w L (.loop cond body) z.1 (m₂ z.1)) →
      ExecRandBounded w L (.loop cond body) x (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + 2))

namespace ExecRandBounded

/-- Forget the address bound `L` to obtain an `ExecRand` execution. -/
theorem toExecRand {w L : ℕ} {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExecRandBounded w L c x m) : ExecRand w c x m := by
  induction h with
  | op _ he => exact .op he
  | rand hf => exact .rand hf
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl

/-- Embed a deterministic frontier-bounded execution `ExecBoundedExact` as a point-mass
`ExecRandBounded`. -/
theorem of_execBoundedExact {w L n : ℕ} {c : Code B r} {x y : Data r}
    (h : ExecBoundedExact w L c x y n) :
    ExecRandBounded w L c x (pure (y, n)) := by
  induction h with
  | op hb he => exact .op hb he
  | seq _ _ ih₁ ih₂ =>
    simpa only [pure_bind] using ExecRandBounded.seq ih₁ (m₂ := fun _ => pure (_, _)) fun z hz => by
      supp_cases hz; exact ih₂
  | branch_pos hc _ ih =>
    simpa only [map_pure] using ExecRandBounded.branch_pos hc ih
  | branch_neg hc _ ih =>
    simpa only [map_pure] using ExecRandBounded.branch_neg hc ih
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc _ _ ihb ihl =>
    simpa only [pure_bind] using ExecRandBounded.loop_iter hc ihb
      (m₂ := fun _ => pure (_, _)) fun z hz => by supp_cases hz; exact ihl

/-- Prepend a register-only deterministic `Exec` onto an `ExecRandBounded`. -/
theorem seq_of_exec_regOnly {w L n₁ : ℕ} {c₁ c₂ : Code B r} {x y : Data r}
    {m₂ : ProbComp (Data r × ℕ)} (hc₁ : IsRegOnlyCode c₁) (h₁ : Exec w c₁ x y n₁)
    (h₂ : ExecRandBounded w L c₂ y m₂) :
    ExecRandBounded w L (.seq c₁ c₂) x ((fun z => (z.1, n₁ + z.2)) <$> m₂) := by
  have hseq := ExecRandBounded.seq (of_execBoundedExact (.of_exec_regOnly hc₁ h₁))
    (m₂ := fun _ => m₂) fun z hz => by supp_cases hz; exact h₂
  simpa only [pure_bind, ← bind_pure_comp] using hseq

/-- A `rand` instruction followed by a frontier-bounded deterministic `ExecBoundedExact` suffix. -/
theorem rand_seq_det {w L : ℕ} {dst src : Fin r} {a : ℕ} {c₂ : Code B r} {x : Data r}
    {f : Fin (a + 1) → Data r} {n : ℕ}
    (hs : x.regs src = a) (hfit : Fits w a)
    (h₂ : ∀ k : Fin (a + 1), ExecBoundedExact w L c₂ (x.set dst k.val) (f k) n) :
    ExecRandBounded w L (.seq (.rand dst src) c₂) x (do
      let k ← ProbComp.unifFin a
      pure (f k, 1 + n)) := by
  classical
  have hr : ExecRandBounded (B := B) w L (.rand dst src) x (do
      let k ← ProbComp.unifFin a
      pure (x.set dst k.val, 1)) := by
    have h0 := ExecRandBounded.rand (B := B) (L := L) (dst := dst) (src := src) (hs ▸ hfit)
    rwa [hs] at h0
  let m₂ : Data r → ProbComp (Data r × ℕ) := fun d =>
    if h : d.regs dst < a + 1 then pure (f ⟨d.regs dst, h⟩, n) else pure (d, 0)
  have hseq := ExecRandBounded.seq hr (m₂ := m₂) fun z hz => by
    supp_cases hz with ⟨k, rfl⟩
    simp only [m₂, Data.set_regs, Function.update_self, k.isLt, ↓reduceDIte]
    exact of_execBoundedExact (h₂ k)
  have heq : (do let z₁ ← do let k ← ProbComp.unifFin a; pure (x.set dst k.val, 1)
                 let z₂ ← m₂ z₁.1; pure (z₂.1, z₁.2 + z₂.2)) =
      (do let k ← ProbComp.unifFin a; pure (f k, 1 + n)) := by
    simp only [pure_bind]
    refine congrArg (ProbComp.unifFin a >>= ·) (funext fun k => ?_)
    simp only [m₂, Data.set_regs, Function.update_self, k.isLt, ↓reduceDIte, pure_bind]
  exact heq ▸ hseq

private theorem boundedAccess_rename_iff {r' L : ℕ} {f : Fin r → Fin r'} (o : Op B r)
    (x : Data r') : (o.rename f).BoundedAccess L x ↔ o.BoundedAccess L (x.comap f) := by
  cases o <;> rfl

private theorem rename_bind_step {r' w L extra : ℕ} {f : Fin r → Fin r'} (hf : f.Injective)
    {c₂ : Code B r} (x : Data r') {m₁ : ProbComp (Data r × ℕ)}
    {m₂ : Data r → ProbComp (Data r × ℕ)}
    (h₂ : ∀ z ∈ m₁.support, ExecRandBounded w L c₂ z.1 (m₂ z.1))
    (ih₂ : ∀ z₁ ∈ m₁.support, ∀ {x' : Data r'}, x'.comap f = z₁.1 →
      ExecRandBounded w L (c₂.rename f) x' ((fun z => (z.1.extend f x', z.2)) <$> m₂ z₁.1)) :
    ∃ m₂' : Data r' → ProbComp (Data r' × ℕ),
      (∀ z' ∈ ((fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> m₁).support,
        ExecRandBounded w L (c₂.rename f) z'.1 (m₂' z'.1)) ∧
      ((fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + extra))) = (do
        let z₁ ← (fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> m₁
        let z₂ ← m₂' z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + extra)) := by
  refine ⟨fun d => (fun z => (z.1.extend f x, z.2)) <$> codeComp w c₂ (d.comap f),
    fun z' hz' => ?_, ?_⟩
  · supp_cases hz' with ⟨z₁, hz₁, rfl⟩
    dsimp only
    rw [Data.comap_extend hf, (h₂ z₁ hz₁).toExecRand.codeComp_eq]
    simpa only [Data.extend_extend hf] using ih₂ z₁ hz₁ (Data.comap_extend hf z₁.1 x)
  · simp only [← bind_pure_comp, bind_assoc, pure_bind]
    refine OracleComp.bind_congr_on_support fun z₁ hz₁ => ?_
    rw [Data.comap_extend hf, (h₂ z₁ hz₁).toExecRand.codeComp_eq]

/-- Rename registers in an `ExecRandBounded` execution along an injective map `f`. -/
theorem rename {r' w L : ℕ} {f : Fin r → Fin r'} (hf : f.Injective)
    {c : Code B r} {x : Data r'} {m : ProbComp (Data r × ℕ)}
    (h : ExecRandBounded w L c (x.comap f) m) :
    ExecRandBounded w L (c.rename f) x ((fun z => (z.1.extend f x, z.2)) <$> m) := by
  generalize hx : x.comap f = x₀ at h
  induction h generalizing x with
  | @op o _ y hb ho =>
    subst hx
    have ho' : (o.rename f).eval w x = some (y.extend f x) := by rw [Op.eval_rename hf, ho]; rfl
    simpa only [Code.rename, map_pure] using
      ExecRandBounded.op ((boundedAccess_rename_iff o x).mpr hb) ho'
  | @rand dst src _ hfit =>
    subst hx
    have heq : ((fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> (do
        let k ← ProbComp.unifFin (x.regs (f src))
        pure ((x.comap f).set dst k.val, 1))) = (do
        let k ← ProbComp.unifFin (x.regs (f src))
        pure (x.set (f dst) k.val, 1)) := by
      rw [← bind_pure_comp, bind_assoc]
      refine congrArg (ProbComp.unifFin (x.regs (f src)) >>= ·) (funext fun k => ?_)
      simp only [pure_bind, Data.extend_set hf, Data.extend_comap hf]
    simpa only [Code.rename, Data.comap_regs, heq] using ExecRandBounded.rand (x := x) hfit
  | @seq c₁ c₂ _ m₁ m₂ _ h₂ ih₁ ih₂ =>
    subst hx
    obtain ⟨_, hcont, heq⟩ := rename_bind_step (extra := 0) hf x h₂ fun z₁ hz₁ {_} h => ih₂ z₁ hz₁ h
    simp only [Nat.add_zero] at heq
    simpa only [Code.rename, ← heq] using ExecRandBounded.seq (ih₁ rfl) hcont
  | @branch_pos cond pos neg _ m hc _ ih =>
    subst hx
    simpa only [Code.rename, Functor.map_map] using
      ExecRandBounded.branch_pos (neg := neg.rename f) ((Cond.holds_rename _ _).2 hc) (ih rfl)
  | @branch_neg cond pos neg _ m hc _ ih =>
    subst hx
    simpa only [Code.rename, Functor.map_map] using
      ExecRandBounded.branch_neg (pos := pos.rename f)
        (fun h => hc ((Cond.holds_rename _ _).1 h)) (ih rfl)
  | @loop_exit cond body _ hc =>
    subst hx
    simpa only [Code.rename, map_pure, Data.extend_comap hf] using
      ExecRandBounded.loop_exit (body := body.rename f) (fun h => hc ((Cond.holds_rename _ _).1 h))
  | @loop_iter cond body _ mb ml hc _ hl ihb ihl =>
    subst hx
    obtain ⟨_, hcont, heq⟩ :=
      rename_bind_step (extra := 2) hf x hl fun z₁ hz₁ {_} h => ihl z₁ hz₁ h
    simp only [Code.rename] at hcont ⊢
    simpa only [← heq] using
      ExecRandBounded.loop_iter ((Cond.holds_rename _ _).2 hc) (ihb rfl) hcont

end ExecRandBounded

private theorem lift_bind_dist {extra : ℕ} (L_fr : ℕ)
    (m₁ : ProbComp (Data r × ℕ)) (m₂ : Data r → ProbComp (Data r × ℕ))
    {P : RData r → Prop}
    (ih₂ : ∀ z₁ ∈ m₁.support, P ⟨z₁.1.regs, z₁.1.mem, L_fr⟩) :
    let lift (z : Data r × ℕ) : RData r := ⟨z.1.regs, z.1.mem, L_fr⟩
    let μ₂ (u : RData r) : PMF (RData r) := (m₂ u.toData).eval.map lift
    let T₂ (u : RData r) : ℝ≥0∞ := ProbComp.expect (m₂ u.toData) fun z => (z.2 : ℝ≥0∞)
    (∀ u ∈ (m₁.eval.map lift).support, P u) ∧
      (m₁.eval.map lift).bind μ₂ =
        ((do
          let z₁ ← m₁
          let z₂ ← m₂ z₁.1
          pure (z₂.1, z₁.2 + z₂.2 + extra)).eval.map lift) ∧
      (ProbComp.expect m₁ fun z => (z.2 : ℝ≥0∞)) + extra +
          (∑' u, (m₁.eval.map lift) u * T₂ u) =
        ProbComp.expect (do
          let z₁ ← m₁
          let z₂ ← m₂ z₁.1
          pure (z₂.1, z₁.2 + z₂.2 + extra)) fun z => (z.2 : ℝ≥0∞) := by
  refine ⟨fun u hu => ?_, ?_, ?_⟩
  · supp_cases hu with ⟨z₁, hz₁, rfl⟩
    rw [ProbComp.support_eval] at hz₁
    exact ih₂ z₁ hz₁
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.bind_map, PMF.pure_map]
    rfl
  · simp only [ProbComp.expect_bind, ProbComp.expect_pure, Nat.cast_add, ProbComp.expect_add,
      ProbComp.expect_const]
    rw [Cslib.Probability.PMF.tsum_map_mul]
    change (ProbComp.expect m₁ fun z => (z.2 : ℝ≥0∞)) + extra +
        (ProbComp.expect m₁ fun a => ProbComp.expect (m₂ a.1) fun z => (z.2 : ℝ≥0∞)) = _
    ac_rfl

/-- Lift a frontier-bounded randomized execution `ExecRandBounded w L c x.toData m` directly into
`ExecRCodeDist` on `RCode.ofCode c` with unchanged hardware frontier `x.frontier`. -/
theorem ExecRCodeDist.of_execRandBounded {w L_peak L : ℕ} {c : Code B r} {x : RData r}
    {m : ProbComp (Data r × ℕ)}
    (hL_peak : x.frontier ≤ L_peak) (hL : L ≤ x.frontier)
    (h : ExecRandBounded w L c x.toData m) :
    ExecRCodeDist w (RCode.ofCode c) x
      (m.eval.map fun z => ⟨z.1.regs, z.1.mem, x.frontier⟩)
      (ProbComp.expect m fun z => (z.2 : ℝ≥0∞)) L_peak := by
  generalize hx0 : x.toData = x₀ at h
  induction h generalizing x with
  | @op o _ y hb he =>
    subst hx0
    exact (ExecRCodeDist.of_demonicExec
      (.op hL_peak (evalResizable_of_boundedAccess hb hL he) rfl)).congr_dist
      (by simp [ProbComp.eval_pure]) (by simp [ProbComp.expect_pure])
  | @rand dst src _ hfit =>
    subst hx0
    cases x
    refine (ExecRCodeDist.rand (B := B) (dst := dst) (src := src) hL_peak hfit).congr_dist ?_ ?_
    · simp only [ProbComp.eval_bind, PMF.map_bind, ProbComp.eval_pure, PMF.pure_map]
      rfl
    · simp only [ProbComp.expect_bind, ProbComp.expect_pure, Nat.cast_one,
        ProbComp.expect_const, le_rfl]
  | @seq c₁ c₂ _ m₁ m₂ _ _ ih₁ ih₂ =>
    subst hx0
    obtain ⟨hcont, hμ, hT⟩ := lift_bind_dist (extra := 0) x.frontier m₁ m₂
      (P := fun u => ExecRCodeDist w (RCode.ofCode c₂) u
        ((m₂ u.toData).eval.map fun z => ⟨z.1.regs, z.1.mem, x.frontier⟩)
        (ProbComp.expect (m₂ u.toData) fun z => (z.2 : ℝ≥0∞)) L_peak)
      fun z₁ hz₁ => ih₂ z₁ hz₁ (x := ⟨z₁.1.regs, z₁.1.mem, x.frontier⟩) hL_peak hL rfl
    simp only [Nat.add_zero] at hμ hT
    simpa only [RCode.ofCode] using
      (ExecRCodeDist.seq (ih₁ hL_peak hL rfl) hcont).congr_dist hμ
        (le_of_eq (by simpa only [CharP.cast_eq_zero, add_zero] using hT))
  | @branch_pos cond pos neg _ m hc _ ih =>
    subst hx0
    refine (ExecRCodeDist.branch_pos hc (ih hL_peak hL rfl)).congr_dist
      (by simp only [ProbComp.eval_map, PMF.map_comp, Function.comp_def]) (le_of_eq ?_)
    simp only [ProbComp.expect_map, Nat.cast_add, Nat.cast_one, ProbComp.expect_add,
      ProbComp.expect_const]
  | @branch_neg cond pos neg _ m hc _ ih =>
    subst hx0
    refine (ExecRCodeDist.branch_neg hc (ih hL_peak hL rfl)).congr_dist
      (by simp only [ProbComp.eval_map, PMF.map_comp, Function.comp_def]) (le_of_eq ?_)
    simp only [ProbComp.expect_map, Nat.cast_add, Nat.cast_ofNat, ProbComp.expect_add,
      ProbComp.expect_const]
  | @loop_exit cond body _ hc =>
    subst hx0
    exact (ExecRCodeDist.loop_exit hL_peak hc).congr_dist
      (by cases x; simp [ProbComp.eval_pure]) (by simp [ProbComp.expect_pure])
  | @loop_iter cond body _ m₁ m₂ hc _ _ ih₁ ih₂ =>
    subst hx0
    obtain ⟨hcont, hμ, hT⟩ := lift_bind_dist (extra := 2) x.frontier m₁ m₂
      (P := fun u => ExecRCodeDist w (RCode.ofCode (.loop cond body)) u
        ((m₂ u.toData).eval.map fun z => ⟨z.1.regs, z.1.mem, x.frontier⟩)
        (ProbComp.expect (m₂ u.toData) fun z => (z.2 : ℝ≥0∞)) L_peak)
      fun z₁ hz₁ => ih₂ z₁ hz₁ (x := ⟨z₁.1.regs, z₁.1.mem, x.frontier⟩) hL_peak hL rfl
    simp only [RCode.ofCode] at hcont ⊢
    exact (ExecRCodeDist.loop_iter hc (ih₁ hL_peak hL rfl) hcont).congr_dist hμ
      (le_of_eq (by simpa only [Nat.cast_ofNat] using hT))

/-- Lift a frontier-bounded randomized execution `ExecRandBounded w L c (x.toData.comap f) m` along
any injective register renaming `f : Fin r → Fin r'` directly into `ExecRCodeDist` on
`RCode.ofCode (c.rename f)`, preserving `x.frontier`. -/
theorem ExecRCodeDist.of_execRandBounded_rename {r' w L_peak L : ℕ}
    {f : Fin r → Fin r'} (hf : f.Injective) {c : Code B r} {x : RData r'}
    {m : ProbComp (Data r × ℕ)}
    (hL_peak : x.frontier ≤ L_peak) (hL : L ≤ x.frontier)
    (h : ExecRandBounded w L c (x.toData.comap f) m) :
    ExecRCodeDist w (RCode.ofCode (c.rename f)) x
      (m.eval.map fun z => ⟨(z.1.extend f x.toData).regs, z.1.mem, x.frontier⟩)
      (ProbComp.expect m fun z => (z.2 : ℝ≥0∞)) L_peak := by
  refine (of_execRandBounded hL_peak hL (h.rename hf)).congr_dist ?_ (le_of_eq ?_)
  · rw [ProbComp.eval_map, PMF.map_comp]; rfl
  · exact ProbComp.expect_map _ _ _

/-- Worst-case step-bound specialization of `ExecRCodeDist.of_execRandBounded_rename`. -/
theorem ExecRCodeDist.of_execRandBounded_rename_le {r' w L_peak L T : ℕ}
    {f : Fin r → Fin r'} (hf : f.Injective) {c : Code B r} {x : RData r'}
    {m : ProbComp (Data r × ℕ)}
    (hL_peak : x.frontier ≤ L_peak) (hL : L ≤ x.frontier)
    (h : ExecRandBounded w L c (x.toData.comap f) m)
    (hT : ∀ z ∈ m.support, z.2 ≤ T) :
    ExecRCodeDist w (RCode.ofCode (c.rename f)) x
      (m.eval.map fun z => ⟨(z.1.extend f x.toData).regs, z.1.mem, x.frontier⟩)
      (T : ℝ≥0∞) L_peak := by
  refine (of_execRandBounded_rename hf hL_peak hL h).mono ?_
  exact (ProbComp.expect_mono_on_support fun z hz => Nat.cast_le.mpr (hT z hz)).trans_eq
    (ProbComp.expect_const m T)

end Cslib.WordRAM.Resizable
