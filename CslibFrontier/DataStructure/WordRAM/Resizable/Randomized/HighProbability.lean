/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.ObliviousSequence
public import CslibFrontier.DataStructure.WordRAM.Randomized.HighProbability
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.SupportTsum

/-!
# With-High-Probability Resizable Word RAM Execution and Sequence Certificates

This module develops high-probability worst-case execution certificates on the word-granular
**Resizable Word RAM** (`Cslib.WordRAM.Resizable`), coupling structured `RCode` execution with
clocked flat-program evaluation (`evalRandDemonic`) across all time- and state-adaptive `.grow`
allocation adversaries `adv : RAdv r` and tracking every-step peak hardware frontiers
(`PeakFrontierLe`).

## Design

1. **Clocked adaptive-adversary halting lower bounds (`haltedWithin`, `ExecRCodeSteps`):**
   - `haltedWithin w p v d T pc y` takes the infimum over all adaptive adversaries `adv : RAdv r`
     of the probability `evalRandDemonic w adv p T ⟨pc, y⟩ (.halted v d)` at finite clock horizon
     `T`.
   - `RDemonicExec.le_haltedWithin_assemble` proves that any `RDemonicExec w L_peak c x n P`
     reaches `pc + c.size` within `n ≤ T` instructions across all `adv : RAdv r`.
   - `ExecRCodeSteps w c x μ L_peak` couples an adversary-independent outcome distribution
     `μ : PMF (RCodeStepOutcome r)` (recording `data : RData r`, `steps : ℕ`, and `timed : Bool`)
     with peak hardware frontier `L_peak`. Fast branches (`timed = true`, `steps ≤ B_hor`) are
     certified to halt at `RCfg.halted (y.regs out) y` in
     `evalRandDemonic w adv (c.program out) (B_hor + 1) ⟨0, x⟩` for **every** `adv : RAdv r`
     (`toOuterMeasure_le_evalRandDemonic_program`, `one_sub_le_evalRandDemonic_program`), while
     rare Las Vegas fallback branches (`ExecRCodeSteps.of_execRCodeDist`, `timed = false`) still
     satisfy `RDemonicFaultFree`, `PeakFrontierLe w L_peak`, and exact unbounded-horizon halting
     (`ExecRCodeSteps.toExecRProgramDist_top`).
2. **Operation- and trajectory-indexed WHP certificates (`HighProbObliviousImpl`):**
   - Supports **operation-dependent** worst-case step budgets `worstCaseTime : S.Op → ℕ` (allowing
     e.g. `O_c(1)` `query` alongside `O_c(k)` `insert`/`delete` in resizable `k`-kick trees, or
     uniform `O_c(1)` across all operations in SOSA 2024) and **trajectory-dependent** failure
     probabilities `failureProb : List S.Op → S.Op → ℝ≥0∞` (such as `max(n_t, N_0(c))^(-c)`),
     resting `spaceBound`, and stepwise `peakSpaceBound` under `ObliviousPeakFits`.
   - Provides basis transport (`mapSimulates`, `toStandard`), whole-sequence union bounds
     (`seq_whp`, `seq_toExecWhpProgramSteps`), and `.halt`-stub rejection
     (`not_execWhpProgramSteps_halt`).

## Main definitions

* `Cslib.WordRAM.Resizable.RCodeStepOutcome`, `Cslib.WordRAM.Resizable.haltedWithin`,
  `Cslib.WordRAM.Resizable.ExecRCodeSteps`: step-counted structured execution and finite-horizon
  demonic halting reachability.
* `Cslib.DataStructure.WordRAM.Resizable.Randomized.WhpStepROutcome`,
  `WhpSeqROutcome`, `ExecWhpSteps`, `ExecWhpProgramSteps`, `HighProbObliviousImpl`:
  Resizable Word RAM high-probability trajectory outcomes, multi-step execution relations, and
  reusable oblivious-sequence implementation certificate.

## Main results

* `Cslib.WordRAM.Resizable.RDemonicExec.le_haltedWithin_assemble`: finite-horizon halting
  propagation for `RDemonicExec`.
* `Cslib.WordRAM.Resizable.ExecRCodeSteps.toOuterMeasure_le_evalRandDemonic_program`,
  `Cslib.WordRAM.Resizable.ExecRCodeSteps.one_sub_le_evalRandDemonic_program`,
  `Cslib.WordRAM.Resizable.ExecRCodeSteps.toExecRProgramWhp`: clocked `B_hor + 1` halting bounds,
  `RDemonicFaultFree`, `PeakFrontierLe`, and almost-sure halting across all `adv : RAdv r`.
* `Cslib.DataStructure.WordRAM.Resizable.Randomized.not_execWhpProgramSteps_halt`:
  `.halt`-rejection soundness check on compiled flat `RProgram` sequences.
* `Cslib.DataStructure.WordRAM.Resizable.Randomized.HighProbObliviousImpl.seq_whp`,
  `seq_toExecWhpProgramSteps`: end-to-end whole-sequence union bound, `1 · OPT`-compatible resting
  and peak frontier bounds, caller `[0, base)` preservation, and `S.Contract` correctness.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 2.1 and 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

open scoped ENNReal

namespace Cslib.WordRAM.Resizable

open Cslib.WordRAM Cslib.Probability

variable {B B' : Basis} {r : ℕ}

/-! ## Section 1: Finite-horizon demonic halting (`haltedWithin`) and `RDemonicExec` bridge -/

/-- Outcome of a structured Resizable Word RAM execution `ExecRCodeSteps`: pairs the post-state
`data : RData r` with an upper bound `steps : ℕ` on executed body instructions whenever
`timed = true` (`timed = false` marks unbounded Las Vegas fallback branches lifted from
`ExecRCodeDist`). -/
structure RCodeStepOutcome (r : ℕ) where
  /-- Final Resizable Word RAM register, memory, and frontier state. -/
  data : RData r
  /-- Upper bound on executed body instructions when `timed = true`. -/
  steps : ℕ
  /-- Whether this branch carries a finite step-count certificate (`false` on unbounded slow
  fallback branches). -/
  timed : Bool := true

namespace RCodeStepOutcome

/-- Fast-branch predicate for deterministic instruction budget `B_hor : ℕ`. -/
@[expose] def WithinBudget (B_hor : ℕ) (z : RCodeStepOutcome r) : Prop :=
  z.timed = true ∧ z.steps ≤ B_hor

instance instDecidableWithinBudget (B_hor : ℕ) (z : RCodeStepOutcome r) :
    Decidable (z.WithinBudget B_hor) :=
  inferInstanceAs (Decidable (z.timed = true ∧ z.steps ≤ B_hor))

/-- Add `d` deterministic instructions to a step outcome, preserving `data` and `timed`. -/
abbrev addSteps (d : ℕ) (z : RCodeStepOutcome r) : RCodeStepOutcome r :=
  ⟨z.data, z.steps + d, z.timed⟩

/-- Combine two sequential step outcomes `(z₁, z₂)` by summing `steps` and conjoining `timed`. -/
abbrev seqCombine (z₁ z₂ : RCodeStepOutcome r) : RCodeStepOutcome r :=
  ⟨z₂.data, z₁.steps + z₂.steps, z₁.timed && z₂.timed⟩

/-- Combine loop body outcome `z₁` and remaining-loop outcome `z₂` (`+ 2` control instructions). -/
abbrev loopCombine (z₁ z₂ : RCodeStepOutcome r) : RCodeStepOutcome r :=
  ⟨z₂.data, z₁.steps + z₂.steps + 2, z₁.timed && z₂.timed⟩

end RCodeStepOutcome

/-- Infimum over all adaptive `.grow` adversaries `adv : RAdv r` of the probability of reaching
`.halted v d` within `T` clocked steps from `⟨pc, y⟩`. -/
noncomputable def haltedWithin (w : ℕ) (p : RProgram B r) (v : ℕ) (d : RData r)
    (T pc : ℕ) (y : RData r) : ℝ≥0∞ :=
  ⨅ adv : RAdv r, evalRandDemonic w adv p T ⟨pc, y⟩ (.halted v d)

theorem haltedWithin_mono {w v pc : ℕ} {p : RProgram B r} {d y : RData r} {T₁ T₂ : ℕ}
    (hT : T₁ ≤ T₂) :
    haltedWithin w p v d T₁ pc y ≤ haltedWithin w p v d T₂ pc y :=
  iInf_mono fun adv => evalRandDemonic_halted_mono w adv p ⟨pc, y⟩ v d hT

theorem haltedWithin_le_haltedReach (w : ℕ) (p : RProgram B r) (v : ℕ) (d : RData r)
    (T pc : ℕ) (y : RData r) :
    haltedWithin w p v d T pc y ≤ haltedReach w p v d pc y :=
  iInf_mono fun adv => le_iSup (fun t => evalRandDemonic w adv p t ⟨pc, y⟩ (.halted v d)) T

section HaltedWithinLemmas
attribute [local irreducible] haltedWithin

private theorem haltedWithin_le_of_pure {w v k : ℕ} {p : RProgram B r} {d : RData r}
    {s : RState r} {s' : (RState r → ℕ → ℕ) → RState r}
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running (s' f))) :
    (⨅ f, haltedWithin w p v d k (s' f).pc (s' f).data) ≤
      haltedWithin w p v d (k + 1) s.pc s.data := by
  unfold haltedWithin
  refine le_iInf fun adv => ?_
  refine (iInf_le _ (adv 0)).trans ((iInf_le _ (adv.shift 1)).trans ?_)
  simp [evalRandDemonic, runRandResizable_succ, hstep (adv 0)]

private theorem haltedWithin_le_of_const {w v k : ℕ} {p : RProgram B r} {d : RData r}
    {s s₁ : RState r}
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running s₁)) :
    haltedWithin w p v d k s₁.pc s₁.data ≤ haltedWithin w p v d (k + 1) s.pc s.data :=
  (le_iInf fun _ => le_rfl).trans (haltedWithin_le_of_pure hstep)

private theorem haltedWithin_le_of_rand {w v k pc : ℕ} {p : RProgram B r} {d x : RData r}
    {dst src : Fin r} (hp : p[pc]? = some (.rand dst src)) (hfit : Fits w (x.regs src)) :
    (∑' j : Fin (x.regs src + 1), (ProbComp.unifFin (x.regs src)).eval j *
      haltedWithin w p v d k (pc + 1) (x.set dst j.val)) ≤
      haltedWithin w p v d (k + 1) pc x := by
  unfold haltedWithin
  refine le_iInf fun adv => ?_
  have hstep_sum :
      (∑' j : Fin (x.regs src + 1), (ProbComp.unifFin (x.regs src)).eval j *
        evalRandDemonic w (adv.shift 1) p k ⟨pc + 1, x.set dst j.val⟩ (.halted v d)) =
        evalRandDemonic w adv p (k + 1) ⟨pc, x⟩ (.halted v d) := by
    simp only [evalRandDemonic, runRandResizable_succ,
      stepRandResizable_rand_of_fits (s := ⟨pc, x⟩) hp hfit, bind_assoc, pure_bind,
      ProbComp.eval_bind, PMF.bind_apply]
  rw [← hstep_sum]
  exact tsum_le_tsum fun j => mul_le_mul_right (iInf_le _ (adv.shift 1)) _

/-- **Finite-horizon assembly propagation for `RDemonicExec` (`le_haltedWithin_assemble`).**
Whenever `RDemonicExec w L_peak c x n P` holds and `n ≤ T`, every adaptive `.grow` adversary
reaches `pc + c.size` in a state satisfying `P` with at least `T - n` clock steps remaining. -/
theorem RDemonicExec.le_haltedWithin_assemble {w L_peak n T pc v : ℕ} {c : RCode B r}
    {x d : RData r} {P : RData r → Prop} (h : RDemonicExec w L_peak c x n P) {p : RProgram B r}
    (hp : p.Contains pc (c.assemble pc)) (hT : n ≤ T) :
    (⨅ (y : RData r) (_ : P y), haltedWithin w p v d (T - n) (pc + c.size) y) ≤
      haltedWithin w p v d T pc x := by
  induction h generalizing pc T with
  | @op o x y P _ he hp_y =>
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    refine (iInf₂_le y hp_y).trans ?_
    simpa [RCode.size] using haltedWithin_le_of_const (v := v) (d := d) (k := k)
      fun _ => stepRandResizable_op (s := ⟨pc, x⟩) hp.head he
  | @grow dst x P _ hfit hp_y =>
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    refine (le_iInf fun f : RState r → ℕ → ℕ =>
      iInf₂_le _ (hp_y _ (demonicGrow_advGrowMem w (f ⟨pc, x⟩) _ _ _))).trans ?_
    simpa [RCode.size] using haltedWithin_le_of_pure (v := v) (d := d) (k := k)
      fun f => stepRandResizable_grow_of_fits (s := ⟨pc, x⟩) hp.head hfit
  | @shrink x P _ hk hp_y =>
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    refine (iInf₂_le _ hp_y).trans ?_
    simpa [RCode.size] using haltedWithin_le_of_const (v := v) (d := d) (k := k)
      fun _ => stepRandResizable_shrink_of_pos (s := ⟨pc, x⟩) hp.head hk
  | @rand dst src x P _ hfit hp_y =>
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    set B_inf := ⨅ (y : RData r) (_ : P y), haltedWithin w p v d k (pc + 1) y
    have hsum : B_inf ≤ ∑' j : Fin (x.regs src + 1),
        (ProbComp.unifFin (x.regs src)).eval j *
          haltedWithin w p v d k (pc + 1) (x.set dst j.val) := by
      have h1 : B_inf = ∑' j : Fin (x.regs src + 1),
          (ProbComp.unifFin (x.regs src)).eval j * B_inf := by
        rw [ENNReal.tsum_mul_right, (ProbComp.unifFin (x.regs src)).eval.tsum_coe, one_mul]
      rw [h1]
      exact tsum_le_tsum fun j =>
        mul_le_mul_right (iInf₂_le _ (hp_y j.val (Nat.lt_succ_iff.mp j.isLt))) _
    simpa [RCode.size] using hsum.trans (haltedWithin_le_of_rand hp.head hfit)
  | @seq c₁ c₂ x T₁ T₂ Q P _ _ ih₁ ih₂ =>
    have hc₂ := hp.seq_right
    refine (le_iInf₂ fun y₁ hy₁ => ?_).trans (ih₁ hp.append_left (by omega))
    refine (le_of_eq ?_).trans (ih₂ y₁ hy₁ hc₂ (by omega))
    simp only [RCode.size, Nat.add_assoc, Nat.sub_sub]
  | @branch_pos c pos neg x T₀ P hc _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    have hbr := hp.branch_head
    have hc' := hp.branch_pos
    refine (le_of_eq ?_).trans ((ih hc' (by omega)).trans
      (haltedWithin_le_of_const (v := v) (d := d) (k := k)
        fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hbr hc))
    simp only [RCode.size, Nat.add_sub_add_right,
      show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
  | @branch_neg c pos neg x T₀ P hc _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 2 := ⟨T - 2, by omega⟩
    have hbr := hp.branch_head
    have hj := hp.branch_jump
    have hstep1 := haltedWithin_le_of_const (w := w) (v := v) (d := d) (k := k + 1)
      fun _ => stepRandResizable_branch_neg (s := ⟨pc, x⟩) hbr hc
    refine (le_iInf₂ fun y hy => (iInf₂_le y hy).trans ?_).trans
      ((ih hp.branch_neg (by omega)).trans hstep1)
    have hrem : k + 1 - T₀ = (k + 2 - (T₀ + 2)) + 1 := by omega
    rw [hrem]
    simpa [RCode.size, show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
      using haltedWithin_le_of_const (w := w) (v := v) (d := d) (k := k + 2 - (T₀ + 2))
        (s := ⟨pc + 1 + neg.size, y⟩)
        fun _ => stepRandResizable_jump (s := ⟨pc + 1 + neg.size, y⟩) hj
  | @loop_exit c body x P _ hc hp_y =>
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 2 := ⟨T - 2, by omega⟩
    have hj := hp.loop_exit
    refine ((iInf₂_le x hp_y).trans (le_of_eq ?_)).trans
      ((haltedWithin_le_of_const (w := w) (v := v) (d := d) (k := k)
          fun _ => stepRandResizable_jump (s := ⟨pc + 1, x⟩) hj).trans
        (haltedWithin_le_of_const (w := w) (v := v) (d := d) (k := k + 1)
          fun _ => stepRandResizable_branch_neg (s := ⟨pc, x⟩) hp.head hc))
    simp [RCode.size, show pc + body.size + 3 = pc + (body.size + 3) by omega]
  | @loop_iter c body x T₁ T₂ Q P hc _ _ ihb ihl =>
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 2 := ⟨T - 2, by omega⟩
    have hbody_c := hp.loop_body
    have hj_back := hp.loop_back
    have hstep1 := haltedWithin_le_of_const (w := w) (v := v) (d := d) (k := k + 1)
      fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.head hc
    refine (le_iInf₂ fun y hy => ?_).trans ((ihb hbody_c (by omega)).trans hstep1)
    have hrem1 : k + 1 - T₁ = (k - T₁) + 1 := by omega
    have hrem2 : k - T₁ - T₂ = k + 2 - (T₁ + 2 + T₂) := by omega
    rw [hrem1]
    refine (le_of_eq ?_).trans ((ihl y hy hp (by omega)).trans
      (haltedWithin_le_of_const (v := v) (d := d) (k := k - T₁)
        fun _ => stepRandResizable_jump (s := ⟨pc + 2 + body.size, y⟩) hj_back))
    simp only [hrem2]
  | mono _ hle hPQ ih =>
    refine (le_iInf₂ fun y hy => (iInf₂_le y (hPQ y hy)).trans ?_).trans
      (ih hp (hle.trans hT))
    exact haltedWithin_mono (by omega)

end HaltedWithinLemmas

/-! ## Section 2: Compositional step-counted execution (`ExecRCodeSteps`) -/

/-- **Compositional Step-Counted Execution on the Resizable Word RAM (`ExecRCodeSteps`).**
`ExecRCodeSteps w c x μ L_peak`: starting from `x : RData r` at word width `w`, structured program
`c : RCode B r` executes without faulting across all adaptive `.grow` adversaries `adv : RAdv r`,
keeps the hardware word frontier `≤ L_peak` at every intermediate step, realizes
adversary-independent fallthrough distribution `μ.map RCodeStepOutcome.data`, and on every branch
`z ∈ μ.support` with `z.timed = true` reaches `pc + c.size` within `z.steps` instructions. -/
inductive ExecRCodeSteps {B : Basis} {r : ℕ} (w : ℕ) :
    RCode B r → RData r → PMF (RCodeStepOutcome r) → ℕ → Prop where
  | of_demonicExec {L_peak n : ℕ} {c : RCode B r} {x y : RData r} :
      RDemonicExec w L_peak c x n (· = y) →
      ExecRCodeSteps w c x (PMF.pure ⟨y, n, true⟩) L_peak
  | of_execRCodeDist {L_peak : ℕ} {c : RCode B r} {x : RData r} {μ_data : PMF (RData r)}
      {T_exp : ℝ≥0∞} :
      ExecRCodeDist w c x μ_data T_exp L_peak →
      ExecRCodeSteps w c x (μ_data.map fun y => ⟨y, 0, false⟩) L_peak
  | rand {L_peak : ℕ} {dst src : Fin r} {x : RData r} :
      x.frontier ≤ L_peak → Fits w (x.regs src) →
      ExecRCodeSteps w (.rand dst src) x
        ((ProbComp.unifFin (x.regs src)).eval.map fun k => ⟨x.set dst k.val, 1, true⟩) L_peak
  | mono_peak {L₁ L₂ : ℕ} {c : RCode B r} {x : RData r} {μ : PMF (RCodeStepOutcome r)} :
      L₁ ≤ L₂ → ExecRCodeSteps w c x μ L₁ → ExecRCodeSteps w c x μ L₂
  | relax {L_peak : ℕ} {c : RCode B r} {x : RData r} {μ : PMF (RCodeStepOutcome r)}
      (f : RCodeStepOutcome r → RCodeStepOutcome r) :
      ExecRCodeSteps w c x μ L_peak →
      (∀ z ∈ μ.support, (f z).data = z.data ∧
        ((f z).timed = true → z.timed = true ∧ z.steps ≤ (f z).steps)) →
      ExecRCodeSteps w c x (μ.map f) L_peak
  | seq {L_peak : ℕ} {c₁ c₂ : RCode B r} {x : RData r} {μ₁ : PMF (RCodeStepOutcome r)}
      {μ₂ : RCodeStepOutcome r → PMF (RCodeStepOutcome r)} :
      ExecRCodeSteps w c₁ x μ₁ L_peak →
      (∀ z₁ ∈ μ₁.support, ExecRCodeSteps w c₂ z₁.data (μ₂ z₁) L_peak) →
      ExecRCodeSteps w (.seq c₁ c₂) x
        (μ₁.bind fun z₁ => (μ₂ z₁).map (RCodeStepOutcome.seqCombine z₁)) L_peak
  | branch_pos {L_peak : ℕ} {cond : Cond r} {pos neg : RCode B r} {x : RData r}
      {μ : PMF (RCodeStepOutcome r)} :
      cond.Holds x.toData → ExecRCodeSteps w pos x μ L_peak →
      ExecRCodeSteps w (.branch cond pos neg) x (μ.map (RCodeStepOutcome.addSteps 1)) L_peak
  | branch_neg {L_peak : ℕ} {cond : Cond r} {pos neg : RCode B r} {x : RData r}
      {μ : PMF (RCodeStepOutcome r)} :
      ¬cond.Holds x.toData → ExecRCodeSteps w neg x μ L_peak →
      ExecRCodeSteps w (.branch cond pos neg) x (μ.map (RCodeStepOutcome.addSteps 2)) L_peak
  | loop_iter {L_peak : ℕ} {cond : Cond r} {body : RCode B r} {x : RData r}
      {μ₁ : PMF (RCodeStepOutcome r)}
      {μ₂ : RCodeStepOutcome r → PMF (RCodeStepOutcome r)} :
      cond.Holds x.toData →
      ExecRCodeSteps w body x μ₁ L_peak →
      (∀ z₁ ∈ μ₁.support, ExecRCodeSteps w (.loop cond body) z₁.data (μ₂ z₁) L_peak) →
      ExecRCodeSteps w (.loop cond body) x
        (μ₁.bind fun z₁ => (μ₂ z₁).map (RCodeStepOutcome.loopCombine z₁)) L_peak

namespace ExecRCodeSteps

variable {w L_peak : ℕ} {c c₁ c₂ pos neg body : RCode B r} {cond : Cond r} {x y : RData r}
  {μ μ' μ₁ : PMF (RCodeStepOutcome r)}

theorem congr_dist (h : ExecRCodeSteps w c x μ L_peak) (hμ : μ = μ') :
    ExecRCodeSteps w c x μ' L_peak := hμ ▸ h

/-- Entry hardware frontier is bounded by `L_peak`. -/
theorem frontier_le (h : ExecRCodeSteps w c x μ L_peak) : x.frontier ≤ L_peak := by
  induction h with
  | of_demonicExec hd => exact hd.frontier_le
  | of_execRCodeDist hd => exact hd.frontier_le
  | rand hL _ => exact hL
  | mono_peak hL _ ih => exact ih.trans hL
  | relax _ _ _ ih | seq _ _ ih _ | branch_pos _ _ ih | branch_neg _ _ ih | loop_iter _ _ _ ih _ =>
    exact ih

/-- Every post-state in `μ.support` satisfies `z.data.frontier ≤ L_peak`. -/
theorem post_frontier_le (h : ExecRCodeSteps w c x μ L_peak) :
    ∀ z ∈ μ.support, z.data.frontier ≤ L_peak := by
  induction h with
  | of_demonicExec hd =>
    intro z hz
    rw [PMF.support_pure, Set.mem_singleton_iff] at hz; subst hz
    obtain ⟨_, rfl, hfr⟩ := hd.exists_post_frontier_le
    exact hfr
  | of_execRCodeDist hd =>
    intro z hz
    rw [PMF.mem_support_map_iff] at hz; obtain ⟨u, hu, rfl⟩ := hz
    exact hd.post_frontier_le u hu
  | rand hL _ =>
    intro z hz
    rw [PMF.mem_support_map_iff] at hz; obtain ⟨_, _, rfl⟩ := hz; exact hL
  | mono_peak hL _ ih => exact fun z hz => (ih z hz).trans hL
  | relax f _ hf ih =>
    intro z hz
    rw [PMF.mem_support_map_iff] at hz; obtain ⟨u, hu, rfl⟩ := hz
    rw [(hf u hu).1]; exact ih u hu
  | seq _ _ _ ih₂ | loop_iter _ _ _ _ ih₂ =>
    intro z hz
    rw [PMF.mem_support_bind_iff] at hz; obtain ⟨z₁, hz₁, hmap⟩ := hz
    rw [PMF.mem_support_map_iff] at hmap; obtain ⟨z₂, hz₂, rfl⟩ := hmap
    exact ih₂ z₁ hz₁ z₂ hz₂
  | branch_pos _ _ ih | branch_neg _ _ ih =>
    intro z hz
    rw [PMF.mem_support_map_iff] at hz; obtain ⟨u, hu, rfl⟩ := hz
    exact ih u hu

theorem loop_exit (hL : x.frontier ≤ L_peak) (hc : ¬cond.Holds x.toData) :
    ExecRCodeSteps w (.loop cond body) x (PMF.pure ⟨x, 2, true⟩) L_peak :=
  .of_demonicExec (RDemonicExec.loop_exit hL hc rfl)

/-- Sequential composition after a deterministic `RDemonicExec` prefix. -/
theorem seq_demonic {n₁ : ℕ} (h₁ : RDemonicExec w L_peak c₁ x n₁ (· = y))
    (h₂ : ExecRCodeSteps w c₂ y μ L_peak) :
    ExecRCodeSteps w (.seq c₁ c₂) x (μ.map (RCodeStepOutcome.addSteps n₁)) L_peak := by
  classical
  have hs := (ExecRCodeSteps.of_demonicExec h₁).seq (c₂ := c₂)
    (μ₂ := fun z₁ => if z₁.data = y then μ else PMF.pure z₁)
    fun z₁ hz₁ => by
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz₁; subst hz₁
      simp only [↓reduceIte]
      exact h₂
  refine hs.congr_dist ?_
  rw [PMF.pure_bind]
  simp only [↓reduceIte]
  refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z _ => ?_
  simp [RCodeStepOutcome.seqCombine, RCodeStepOutcome.addSteps, Nat.add_comm]

/-- Transport `ExecRCodeSteps` along any defined-evaluation basis simulation `φ : B.Simulates B'`.
-/
theorem mapSimulates (φ : B.Simulates B') (h : ExecRCodeSteps w c x μ L_peak) :
    ExecRCodeSteps w (c.mapSimulates φ) x μ L_peak := by
  induction h with
  | of_demonicExec hd => exact .of_demonicExec (hd.mapSimulates φ)
  | of_execRCodeDist hd => exact .of_execRCodeDist (hd.mapSimulates φ)
  | rand hL hfit => exact .rand hL hfit
  | mono_peak hL _ ih => exact ih.mono_peak hL
  | relax f _ hf ih => exact ih.relax f hf
  | seq _ _ ih₁ ih₂ => exact ih₁.seq ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_iter hc _ _ ihb ihr => exact .loop_iter hc ihb ihr

/-- Horizon-bounded safety and peak-frontier propagation for `ExecRCodeSteps`. -/
theorem demonicSafeWithin_assemble (h : ExecRCodeSteps w c x μ L_peak) {L_bound : ℕ}
    (hL_bound : L_peak ≤ L_bound) {p : RProgram B r} {pc T_hor : ℕ}
    (hp : p.Contains pc (c.assemble pc))
    (hcont : ∀ z ∈ μ.support, DemonicSafeWithin w L_bound T_hor p ⟨pc + c.size, z.data⟩) :
    DemonicSafeWithin w L_bound T_hor p ⟨pc, x⟩ := by
  induction h generalizing pc T_hor with
  | @of_demonicExec _ n _ _ _ hd =>
    exact (hd.mono_peak hL_bound).demonicSafeWithin_assemble hp fun u hu => by
      subst hu; exact hcont ⟨u, n, true⟩ (by simp)
  | of_execRCodeDist hd =>
    refine hd.demonicSafeWithin_assemble hL_bound hp fun u hu => ?_
    exact hcont ⟨u, 0, false⟩ ((PMF.mem_support_map_iff _ _ _).mpr ⟨u, hu, rfl⟩)
  | @rand _ dst src x hL hfit =>
    refine demonicSafeWithin_of_rand (hL.trans hL_bound) hp.head hfit fun j k hk => ?_
    refine (hcont ⟨x.set dst j.val, 1, true⟩ ?_).anti (by omega)
    rw [PMF.mem_support_map_iff]
    refine ⟨j, ?_, rfl⟩
    rw [ProbComp.support_eval]
    exact ProbComp.mem_support_unifFin _ j
  | mono_peak hL _ ih => exact ih (hL.trans hL_bound) hp hcont
  | relax f _ hf ih =>
    refine ih hL_bound hp fun u hu => ?_
    have hmem : f u ∈ (_ : PMF _).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨u, hu, rfl⟩
    rw [← (hf u hu).1]
    exact hcont (f u) hmem
  | @seq _ c₁ c₂ x μ₁ μ₂ _ _ ih₁ ih₂ =>
    have hc₂ := hp.seq_right
    refine ih₁ hL_bound hp.append_left fun z₁ hz₁ => ih₂ z₁ hz₁ hL_bound hc₂ fun z₂ hz₂ => ?_
    have hmem : RCodeStepOutcome.seqCombine z₁ z₂ ∈
        (μ₁.bind fun u₁ => (μ₂ u₁).map (RCodeStepOutcome.seqCombine u₁)).support := by
      rw [PMF.mem_support_bind_iff]
      exact ⟨z₁, hz₁, (PMF.mem_support_map_iff _ _ _).mpr ⟨z₂, hz₂, rfl⟩⟩
    simpa [RCode.size, Nat.add_assoc, RCodeStepOutcome.seqCombine] using hcont _ hmem
  | @branch_pos _ cond pos neg x μ hc hpos ih =>
    have hbr := hp.branch_head
    have hc' := hp.branch_pos
    refine demonicSafeWithin_of_pure (hpos.frontier_le.trans hL_bound)
      (fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hbr hc)
      fun _ k hk => ih hL_bound hc' fun z hz => ?_
    have hmem : z.addSteps 1 ∈ (μ.map (RCodeStepOutcome.addSteps 1)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hz, rfl⟩
    simpa [RCode.size, RCodeStepOutcome.addSteps,
      show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
      using (hcont _ hmem).anti (by omega)
  | @branch_neg _ cond pos neg x μ hc hneg ih =>
    have hbr := hp.branch_head
    have hj := hp.branch_jump
    refine demonicSafeWithin_of_pure (hneg.frontier_le.trans hL_bound)
      (fun _ => stepRandResizable_branch_neg (s := ⟨pc, x⟩) hbr hc)
      fun _ k hk => ih hL_bound hp.branch_neg fun z hz => ?_
    have hmem : z.addSteps 2 ∈ (μ.map (RCodeStepOutcome.addSteps 2)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hz, rfl⟩
    have hz_cont := hcont _ hmem
    refine demonicSafeWithin_of_pure hz_cont.frontier_le
      (fun _ => stepRandResizable_jump (s := ⟨pc + 1 + neg.size, z.data⟩) hj) fun _ k' hk' => ?_
    simpa [RCode.size, RCodeStepOutcome.addSteps,
      show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
      using hz_cont.anti (by omega)
  | @loop_iter _ cond body x μ₁ μ₂ hc hbody hrest ihb ihr =>
    have hbody_c := hp.loop_body
    have hj_back := hp.loop_back
    refine demonicSafeWithin_of_pure (hbody.frontier_le.trans hL_bound)
      (fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.head hc)
      fun _ k hk => ihb hL_bound hbody_c fun z₁ hz₁ => ?_
    refine demonicSafeWithin_of_pure ((hrest z₁ hz₁).frontier_le.trans hL_bound)
      (fun _ => stepRandResizable_jump (s := ⟨pc + 2 + body.size, z₁.data⟩) hj_back)
      fun _ k' hk' => ihr z₁ hz₁ hL_bound hp fun z₂ hz₂ => ?_
    have hmem : RCodeStepOutcome.loopCombine z₁ z₂ ∈
        (μ₁.bind fun u₁ => (μ₂ u₁).map (RCodeStepOutcome.loopCombine u₁)).support := by
      rw [PMF.mem_support_bind_iff]
      exact ⟨z₁, hz₁, (PMF.mem_support_map_iff _ _ _).mpr ⟨z₂, hz₂, rfl⟩⟩
    exact (hcont _ hmem).anti (by omega)

section HaltedReachSteps
attribute [local irreducible] haltedReach

/-- Unbounded-horizon halting-reachability propagation for `ExecRCodeSteps` (covering both timed
fast branches and `of_execRCodeDist` fallback branches). -/
theorem le_haltedReach_assemble (h : ExecRCodeSteps w c x μ L_peak) {p : RProgram B r}
    {pc v : ℕ} {d : RData r} (hp : p.Contains pc (c.assemble pc)) :
    (∑' z, μ z * haltedReach w p v d (pc + c.size) z.data) ≤ haltedReach w p v d pc x := by
  induction h generalizing pc with
  | @of_demonicExec _ n c x y_post hd =>
    rw [tsum_eq_single ⟨y_post, n, true⟩ (fun z hz => by simp [PMF.pure_apply, hz])]
    simp only [PMF.pure_apply_self, one_mul]
    exact (le_iInf₂ fun z hz => hz ▸ le_rfl).trans (hd.le_haltedReach_assemble hp)
  | of_execRCodeDist hd =>
    rw [Cslib.Probability.PMF.tsum_map_mul]
    exact hd.le_haltedReach_assemble hp
  | @rand _ dst src x _ hfit =>
    rw [Cslib.Probability.PMF.tsum_map_mul]
    exact haltedReach_le_of_rand (v := v) (d := d) hp.head hfit
  | mono_peak _ _ ih => exact ih hp
  | @relax _ _ _ μ₀ f _ hf ih =>
    rw [Cslib.Probability.PMF.tsum_map_mul]
    refine (tsum_le_tsum fun z => ?_).trans (ih hp)
    by_cases hz : z ∈ μ₀.support
    · rw [(hf z hz).1]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hz, zero_mul, zero_mul]
  | @seq _ c₁ c₂ x μ₁ μ₂ _ _ ih₁ ih₂ =>
    have hc₂ := hp.seq_right
    rw [Cslib.Probability.PMF.tsum_bind_mul]
    refine (tsum_le_tsum fun z₁ => ?_).trans (ih₁ hp.append_left)
    by_cases hz₁ : z₁ ∈ μ₁.support
    · rw [Cslib.Probability.PMF.tsum_map_mul]
      refine mul_le_mul_right ?_ _
      simpa [RCode.size, Nat.add_assoc, RCodeStepOutcome.seqCombine] using ih₂ z₁ hz₁ hc₂
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hz₁, zero_mul, zero_mul]
  | @branch_pos _ cond pos neg x μ hc _ ih =>
    have hbr := hp.branch_head
    have hc' := hp.branch_pos
    rw [Cslib.Probability.PMF.tsum_map_mul]
    refine (le_of_eq ?_).trans ((ih hc').trans
      (haltedReach_le_of_const (v := v) (d := d)
        fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hbr hc))
    refine tsum_congr fun z => by
      simp [RCode.size, show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
  | @branch_neg _ cond pos neg x μ hc _ ih =>
    have hbr := hp.branch_head
    have hj := hp.branch_jump
    rw [Cslib.Probability.PMF.tsum_map_mul]
    have hstep_sum :
        (∑' z, μ z * haltedReach w p v d (pc + (RCode.branch cond pos neg).size) z.data) ≤
          ∑' z, μ z * haltedReach w p v d (pc + 1 + neg.size) z.data := by
      refine tsum_le_tsum fun z => mul_le_mul_right ?_ (μ z)
      simpa [RCode.size, show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2)
        by omega] using haltedReach_le_of_const (v := v) (d := d) fun _ =>
          stepRandResizable_jump (s := ⟨pc + 1 + neg.size, z.data⟩) hj
    exact hstep_sum.trans ((ih hp.branch_neg).trans
      (haltedReach_le_of_const (v := v) (d := d)
        fun _ => stepRandResizable_branch_neg (s := ⟨pc, x⟩) hbr hc))
  | @loop_iter _ cond body x μ₁ μ₂ hc _ _ ihb ihr =>
    have hbody_c := hp.loop_body
    have hj_back := hp.loop_back
    rw [Cslib.Probability.PMF.tsum_bind_mul]
    refine (tsum_le_tsum fun z₁ => ?_).trans
      ((ihb hbody_c).trans (haltedReach_le_of_const (v := v) (d := d)
        fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.head hc))
    by_cases hz₁ : z₁ ∈ μ₁.support
    · rw [Cslib.Probability.PMF.tsum_map_mul]
      exact mul_le_mul_right ((ihr z₁ hz₁ hp).trans
        (haltedReach_le_of_const (v := v) (d := d)
          fun _ => stepRandResizable_jump (s := ⟨pc + 2 + body.size, z₁.data⟩) hj_back)) _
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hz₁, zero_mul, zero_mul]

end HaltedReachSteps

section HaltedWithinSteps
attribute [local irreducible] haltedWithin

/-- **Partial-horizon assembly lower bound (`tsum_le_haltedWithin_assemble`).**
For any `ExecRCodeSteps w c x μ L_peak` assembled at `pc` inside `p` and any horizon `T : ℕ`,
every timed branch `z` with `z.steps ≤ T` contributes its remaining `(T - z.steps)`-horizon
demonic halting probability at `pc + c.size` toward `haltedWithin w p v d T pc x`. -/
theorem tsum_le_haltedWithin_assemble (h : ExecRCodeSteps w c x μ L_peak) {p : RProgram B r}
    {pc v : ℕ} {d : RData r} (hp : p.Contains pc (c.assemble pc)) (T : ℕ) :
    (∑' z : RCodeStepOutcome r,
      μ z *
        (if z.WithinBudget T then
          haltedWithin w p v d (T - z.steps) (pc + c.size) z.data
        else 0)) ≤
      haltedWithin w p v d T pc x := by
  induction h generalizing pc T with
  | @of_demonicExec _ n c x y_post hd =>
    classical
    rw [tsum_eq_single ⟨y_post, n, true⟩ (fun z hz => by simp [PMF.pure_apply, hz])]
    simp only [PMF.pure_apply_self, one_mul]
    by_cases hn : n ≤ T
    · have hb : (RCodeStepOutcome.mk y_post n true).WithinBudget T := ⟨rfl, hn⟩
      rw [ite_eq_left hb]
      exact LE.le.trans (le_iInf₂ fun z hz => hz ▸ le_rfl)
        (hd.le_haltedWithin_assemble (v := v) (d := d) hp hn)
    · have hnb : ¬(RCodeStepOutcome.mk y_post n true).WithinBudget T := fun h => hn h.2
      simp [hnb]
  | of_execRCodeDist _ =>
    rw [Cslib.Probability.PMF.tsum_map_mul]
    simp [RCodeStepOutcome.WithinBudget]
  | @rand _ dst src x _ hfit =>
    rw [Cslib.Probability.PMF.tsum_map_mul]
    by_cases h1 : 1 ≤ T
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      have hb : ∀ j : Fin (x.regs src + 1),
          (RCodeStepOutcome.mk (x.set dst j.val) 1 true).WithinBudget (k + 1) :=
        fun _ => ⟨rfl, h1⟩
      simp only [hb, ↓reduceIte, Nat.add_sub_cancel, RCode.size]
      exact haltedWithin_le_of_rand hp.head hfit
    · have hnb : ∀ j : Fin (x.regs src + 1),
          ¬(RCodeStepOutcome.mk (x.set dst j.val) 1 true).WithinBudget T :=
        fun _ h => h1 h.2
      simp [hnb]
  | mono_peak _ _ ih => exact ih hp T
  | @relax _ _ _ μ₀ f _ hf ih =>
    rw [Cslib.Probability.PMF.tsum_map_mul]
    refine (tsum_le_tsum fun z => ?_).trans (ih hp T)
    by_cases hz : z ∈ μ₀.support
    · refine mul_le_mul_right ?_ _
      by_cases hfb : (f z).WithinBudget T
      · have ht_f : (f z).timed = true := hfb.1
        have hs_f : (f z).steps ≤ T := hfb.2
        obtain ⟨hd_eq, himp⟩ := hf z hz
        obtain ⟨ht_z, hs_le⟩ := himp ht_f
        have hzb : z.WithinBudget T := ⟨ht_z, hs_le.trans hs_f⟩
        simp only [hfb, hzb, ↓reduceIte, hd_eq]
        exact haltedWithin_mono (by omega)
      · simp only [hfb, ↓reduceIte]; exact zero_le
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hz, zero_mul, zero_mul]
  | @seq _ c₁ c₂ x μ₁ μ₂ _ _ ih₁ ih₂ =>
    have hc₂ := hp.seq_right
    rw [Cslib.Probability.PMF.tsum_bind_mul]
    refine (tsum_le_tsum fun z₁ => ?_).trans (ih₁ hp.append_left T)
    by_cases hz₁ : z₁ ∈ μ₁.support
    · rw [Cslib.Probability.PMF.tsum_map_mul]
      refine mul_le_mul_right ?_ _
      by_cases hb₁ : z₁.WithinBudget T
      · have ht₁ : z₁.timed = true := hb₁.1
        have hs₁ : z₁.steps ≤ T := hb₁.2
        simp only [hb₁, ↓reduceIte]
        refine (le_of_eq ?_).trans (ih₂ z₁ hz₁ hc₂ (T - z₁.steps))
        refine tsum_congr fun z₂ => congrArg (μ₂ z₁ z₂ * ·) ?_
        have hiff : (RCodeStepOutcome.seqCombine z₁ z₂).WithinBudget T ↔
            z₂.WithinBudget (T - z₁.steps) := by
          simp only [RCodeStepOutcome.WithinBudget, ht₁, Bool.true_and]
          exact and_congr_right fun _ => by omega
        simp only [hiff]
        split_ifs with hb₂
        · simp only [RCode.size, Nat.add_assoc, Nat.sub_add_eq]
        · rfl
      · simp only [hb₁, ↓reduceIte]
        refine le_of_eq (tsum_eq_zero_iff.mpr fun z₂ => ?_)
        have hnot : ¬(RCodeStepOutcome.seqCombine z₁ z₂).WithinBudget T := by
          rintro ⟨ht12, hs12⟩
          dsimp only [RCodeStepOutcome.seqCombine] at ht12 hs12
          simp only [Bool.and_eq_true] at ht12
          exact hb₁ ⟨ht12.1, by omega⟩
        simp [hnot]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hz₁, zero_mul, zero_mul]
  | @branch_pos _ cond pos neg x μ hc _ ih =>
    rw [Cslib.Probability.PMF.tsum_map_mul]
    by_cases h1 : 1 ≤ T
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      have hbr := hp.branch_head
      have hc' := hp.branch_pos
      refine (le_of_eq ?_).trans ((ih hc' k).trans
        (haltedWithin_le_of_const (w := w) (v := v) (d := d) (k := k)
          fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hbr hc))
      refine tsum_congr fun z => congrArg (μ z * ·) ?_
      have hiff : (z.addSteps 1).WithinBudget (k + 1) ↔ z.WithinBudget k := by
        simp only [RCodeStepOutcome.WithinBudget]
        exact and_congr_right fun _ => by omega
      simp only [hiff]
      split_ifs with hzk
      · simp only [Nat.add_sub_add_right, RCode.size,
          show pc + (neg.size + pos.size + 2) = pc + neg.size + 2 + pos.size by omega]
      · rfl
    · refine (le_of_eq ?_).trans zero_le
      refine tsum_eq_zero_iff.mpr fun z => ?_
      have hnot : ¬(z.addSteps 1).WithinBudget T := by
        rintro ⟨_, hs⟩; dsimp only [RCodeStepOutcome.addSteps] at hs; omega
      simp [hnot]
  | @branch_neg _ cond pos neg x μ hc _ ih =>
    rw [Cslib.Probability.PMF.tsum_map_mul]
    by_cases h2 : 2 ≤ T
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 2 := ⟨T - 2, by omega⟩
      have hbr := hp.branch_head
      have hj := hp.branch_jump
      have hstep1 := haltedWithin_le_of_const (w := w) (v := v) (d := d) (k := k + 1)
        fun _ => stepRandResizable_branch_neg (s := ⟨pc, x⟩) hbr hc
      refine (tsum_le_tsum fun z => ?_).trans ((ih hp.branch_neg (k + 1)).trans hstep1)
      refine mul_le_mul_right ?_ _
      by_cases hzk : z.WithinBudget k
      · have hle_z : z.steps ≤ k := hzk.2
        have hzk1 : z.WithinBudget (k + 1) := ⟨hzk.1, by omega⟩
        have hzk2 : (z.addSteps 2).WithinBudget (k + 2) := ⟨hzk.1, by
          dsimp only [RCodeStepOutcome.addSteps]; omega⟩
        have hrem : k + 1 - z.steps = (k + 2 - (z.steps + 2)) + 1 := by omega
        simp only [hzk2, hzk1, ↓reduceIte, RCode.size]
        rw [hrem]
        simpa [show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega] using
          haltedWithin_le_of_const (w := w) (v := v) (d := d) (k := k + 2 - (z.steps + 2))
            (s := ⟨pc + 1 + neg.size, z.data⟩)
            fun _ => stepRandResizable_jump (s := ⟨pc + 1 + neg.size, z.data⟩) hj
      · have hnot2 : ¬(z.addSteps 2).WithinBudget (k + 2) := by
          rintro ⟨ht, hs⟩
          dsimp only [RCodeStepOutcome.addSteps] at hs
          exact hzk ⟨ht, by omega⟩
        simp only [hnot2, ↓reduceIte]; exact zero_le
    · refine (le_of_eq ?_).trans zero_le
      refine tsum_eq_zero_iff.mpr fun z => ?_
      have hnot : ¬(z.addSteps 2).WithinBudget T := by
        rintro ⟨_, hs⟩; dsimp only [RCodeStepOutcome.addSteps] at hs; omega
      simp [hnot]
  | @loop_iter _ cond body x μ₁ μ₂ hc _ _ ihb ihr =>
    rw [Cslib.Probability.PMF.tsum_bind_mul]
    by_cases h2 : 2 ≤ T
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 2 := ⟨T - 2, by omega⟩
      have hbody_c := hp.loop_body
      have hj_back := hp.loop_back
      have hstep1 := haltedWithin_le_of_const (w := w) (v := v) (d := d) (k := k + 1)
        fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.head hc
      refine (tsum_le_tsum fun z₁ => ?_).trans ((ihb hbody_c (k + 1)).trans hstep1)
      by_cases hz₁ : z₁ ∈ μ₁.support
      · rw [Cslib.Probability.PMF.tsum_map_mul]
        refine mul_le_mul_right ?_ _
        by_cases hzk₁ : z₁.WithinBudget k
        · have ht₁ : z₁.timed = true := hzk₁.1
          have hle₁ : z₁.steps ≤ k := hzk₁.2
          have hzk₁' : z₁.WithinBudget (k + 1) := ⟨ht₁, by omega⟩
          have hrem : k + 1 - z₁.steps = (k - z₁.steps) + 1 := by omega
          simp only [hzk₁', ↓reduceIte]
          rw [hrem]
          refine (le_trans (tsum_le_tsum fun z₂ => ?_)
            (ihr z₁ hz₁ hp (k - z₁.steps))).trans
            (haltedWithin_le_of_const (w := w) (v := v) (d := d) (k := k - z₁.steps)
              fun _ => stepRandResizable_jump (s := ⟨pc + 2 + body.size, z₁.data⟩) hj_back)
          refine mul_le_mul_right ?_ _
          have hiff : (RCodeStepOutcome.loopCombine z₁ z₂).WithinBudget (k + 2) ↔
              z₂.WithinBudget (k - z₁.steps) := by
            simp only [RCodeStepOutcome.WithinBudget, ht₁, Bool.true_and]
            exact and_congr_right fun _ => by omega
          simp only [hiff]
          split_ifs with hzk₂
          · have hle₂ : z₂.steps ≤ k - z₁.steps := hzk₂.2
            have hsub : k + 2 - (z₁.steps + z₂.steps + 2) = k - z₁.steps - z₂.steps := by omega
            simp only [hsub, le_rfl]
          · exact le_rfl
        · refine (le_of_eq ?_).trans zero_le
          refine tsum_eq_zero_iff.mpr fun z₂ => ?_
          have hnot : ¬(RCodeStepOutcome.loopCombine z₁ z₂).WithinBudget (k + 2) := by
            rintro ⟨ht12, hs12⟩
            dsimp only [RCodeStepOutcome.loopCombine] at ht12 hs12
            simp only [Bool.and_eq_true] at ht12
            exact hzk₁ ⟨ht12.1, by omega⟩
          simp [hnot]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hz₁, zero_mul, zero_mul]
    · refine (le_of_eq ?_).trans zero_le
      refine tsum_eq_zero_iff.mpr fun z₁ => ?_
      by_cases hz₁ : z₁ ∈ μ₁.support
      · rw [Cslib.Probability.PMF.tsum_map_mul]
        refine mul_eq_zero.mpr (Or.inr (tsum_eq_zero_iff.mpr fun z₂ => ?_))
        have hnot : ¬(RCodeStepOutcome.loopCombine z₁ z₂).WithinBudget T := by
          rintro ⟨_, hs⟩; dsimp only [RCodeStepOutcome.loopCombine] at hs; omega
        simp [hnot]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hz₁, zero_mul]

end HaltedWithinSteps

/-- **Partial-horizon flat-program halting lower bound
(`toOuterMeasure_le_evalRandDemonic_program`).**
For any `ExecRCodeSteps w c x μ L_peak`, every adaptive adversary `adv : RAdv r`, and every `y`,
the probability mass of timed branches reaching `y` in `≤ B_hor` instructions lower-bounds
`evalRandDemonic w adv (c.program out) (B_hor + 1) ⟨0, x⟩ (.halted (y.regs out) y)`. -/
theorem toOuterMeasure_le_evalRandDemonic_program (h : ExecRCodeSteps w c x μ L_peak)
    (out : Fin r) (B_hor : ℕ) (adv : RAdv r) (y : RData r) :
    μ.toOuterMeasure {z | z.data = y ∧ z.WithinBudget B_hor} ≤
      evalRandDemonic w adv (c.program out) (B_hor + 1) ⟨0, x⟩ (.halted (y.regs out) y) := by
  classical
  have hp : ((c.program out)).Contains 0 (c.assemble 0) :=
    (RProgram.Contains.self (c.program out)).append_left
  have hhalt : (c.program out)[0 + c.size]? = some (.halt out) := by simp [RCode.program]
  have hasm := (h.tsum_le_haltedWithin_assemble (v := y.regs out) (d := y) hp (B_hor + 1)).trans
    (iInf_le _ adv)
  rw [PMF.toOuterMeasure_apply]
  refine (tsum_le_tsum fun z => ?_).trans hasm
  by_cases hz : z ∈ {z : RCodeStepOutcome r | z.data = y ∧ z.WithinBudget B_hor}
  · obtain ⟨rfl, ht, hle⟩ := hz
    have hb1 : z.WithinBudget (B_hor + 1) := ⟨ht, by omega⟩
    have hm : z ∈ {z' : RCodeStepOutcome r | z'.data = z.data ∧ z'.WithinBudget B_hor} :=
      ⟨rfl, ht, hle⟩
    rw [Set.indicator_of_mem hm, ite_eq_left hb1]
    have hrem : B_hor + 1 - z.steps = (B_hor - z.steps) + 1 := by omega
    have h1 : (1 : ℝ≥0∞) ≤
        haltedWithin w (c.program out) (z.data.regs out) z.data
          (B_hor + 1 - z.steps) (0 + c.size) z.data := by
      refine le_iInf fun adv' => le_of_eq ?_
      rw [hrem, evalRandDemonic, runRandResizable_succ,
        stepRandResizable_halt (s := ⟨0 + c.size, z.data⟩) hhalt, pure_bind,
        runRandResizable_halted, ProbComp.eval_pure, PMF.pure_apply_self]
    simpa using mul_le_mul_right h1 (μ z)
  · rw [Set.indicator_of_notMem hz]; exact zero_le

/-- **Event-level partial-horizon demonic halting bound (`one_sub_le_evalRandDemonic_program`).**
If `μ` satisfies `Q z.data` on every supported branch and fails `WithinBudget B_hor` with
probability at most `δ`, then under **every** adaptive `.grow` adversary `adv : RAdv r`,
`evalRandDemonic w adv (c.program out) (B_hor + 1) ⟨0, x⟩` halts cleanly in a state satisfying `Q`
with probability at least `1 - δ`. -/
theorem one_sub_le_evalRandDemonic_program (h : ExecRCodeSteps w c x μ L_peak)
    {Q : RData r → Prop} {δ : ℝ≥0∞} (out : Fin r) (B_hor : ℕ) (adv : RAdv r)
    (hQ : ∀ z ∈ μ.support, Q z.data)
    (hfail : μ.toOuterMeasure {z | ¬z.WithinBudget B_hor} ≤ δ) :
    1 - δ ≤ (evalRandDemonic w adv (c.program out) (B_hor + 1) ⟨0, x⟩).toOuterMeasure
      {cfg | ∃ y, cfg = .halted (y.regs out) y ∧ Q y} := by
  classical
  have hfast : 1 - δ ≤ μ.toOuterMeasure {z | Q z.data ∧ z.WithinBudget B_hor} := by
    have hcompl : 1 - δ ≤ μ.toOuterMeasure {z : RCodeStepOutcome r | ¬z.WithinBudget B_hor}ᶜ :=
      Cslib.Probability.PMF.one_sub_le_toOuterMeasure_compl μ _ hfail
    refine hcompl.trans ?_
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun z => ?_
    by_cases hz : z ∈ μ.support
    · by_cases hb : z.WithinBudget B_hor
      · have hm1 : z ∈ ({z' : RCodeStepOutcome r | ¬z'.WithinBudget B_hor}ᶜ :
            Set (RCodeStepOutcome r)) := by simp [hb]
        have hm2 : z ∈ {z' : RCodeStepOutcome r | Q z'.data ∧ z'.WithinBudget B_hor} :=
          ⟨hQ z hz, hb⟩
        rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
      · have hn1 : z ∉ ({z' : RCodeStepOutcome r | ¬z'.WithinBudget B_hor}ᶜ :
            Set (RCodeStepOutcome r)) := by simp [hb]
        rw [Set.indicator_of_notMem hn1]; exact zero_le
    · simp [Set.indicator_apply, (PMF.apply_eq_zero_iff _ _).mpr hz]
  refine hfast.trans ?_
  have hpart :
      μ.toOuterMeasure {z | Q z.data ∧ z.WithinBudget B_hor} =
        ∑' y : RData r,
          if Q y then μ.toOuterMeasure {z | z.data = y ∧ z.WithinBudget B_hor} else 0 := by
    rw [PMF.toOuterMeasure_apply]
    have hinner : ∀ y : RData r,
        (if Q y then μ.toOuterMeasure {z | z.data = y ∧ z.WithinBudget B_hor} else 0) =
          ∑' z : RCodeStepOutcome r,
            if z.data = y ∧ Q y ∧ z.WithinBudget B_hor then μ z else 0 := by
      intro y
      by_cases hQy : Q y
      · simp only [hQy, ↓reduceIte, true_and, PMF.toOuterMeasure_apply]
        refine tsum_congr fun z => ?_
        by_cases heq : z.data = y ∧ z.WithinBudget B_hor <;> simp [heq]
      · simp [hQy]
    simp_rw [hinner]
    rw [tsum_comm]
    refine tsum_congr fun z => ?_
    rw [tsum_eq_single z.data (fun y hy => by simp [hy.symm])]
    by_cases hzQ : Q z.data ∧ z.WithinBudget B_hor <;> simp [hzQ]
  rw [hpart, PMF.toOuterMeasure_apply]
  have hinj : Function.Injective (fun y : RData r => RCfg.halted (y.regs out) y) :=
    fun _ _ heq => by injection heq with _ hy
  calc
    (∑' y : RData r,
        if Q y then μ.toOuterMeasure {z | z.data = y ∧ z.WithinBudget B_hor} else 0)
      ≤ ∑' y : RData r,
          Set.indicator {cfg | ∃ y', cfg = .halted (y'.regs out) y' ∧ Q y'}
            (evalRandDemonic w adv (c.program out) (B_hor + 1) ⟨0, x⟩)
            (.halted (y.regs out) y) := by
        refine tsum_le_tsum fun y => ?_
        by_cases hQy : Q y
        · simp only [hQy, ↓reduceIte]
          have hmem_cfg :
              RCfg.halted (y.regs out) y ∈
                {cfg : RCfg r | ∃ y', cfg = .halted (y'.regs out) y' ∧ Q y'} :=
            ⟨y, rfl, hQy⟩
          rw [Set.indicator_of_mem hmem_cfg]
          exact h.toOuterMeasure_le_evalRandDemonic_program out B_hor adv y
        · simp [hQy]
    _ ≤ ∑' cfg : RCfg r,
          Set.indicator {cfg | ∃ y', cfg = .halted (y'.regs out) y' ∧ Q y'}
            (evalRandDemonic w adv (c.program out) (B_hor + 1) ⟨0, x⟩) cfg :=
        tsum_comp_le_tsum_of_injective hinj _

/-- **Full-horizon fault-freedom, `PeakFrontierLe`, and halting distribution for `ExecRCodeSteps`.**
Every `ExecRCodeSteps w c x μ L_peak` compiles via `c.program out` to a fault-free,
`L_peak`-frontier-bounded flat `RProgram` whose unbounded-horizon halting distribution equals
`μ.map RCodeStepOutcome.data` across all adaptive adversaries `adv : RAdv r`. -/
theorem toExecRProgramDist_top (h : ExecRCodeSteps w c x μ L_peak) (out : Fin r) :
    ExecRProgramDist w (c.program out) out x (μ.map RCodeStepOutcome.data) ⊤ L_peak := by
  have hp : (c.program out).Contains 0 (c.assemble 0) :=
    (RProgram.Contains.self (c.program out)).append_left
  have hhalt : (c.program out)[0 + c.size]? = some (.halt out) := by simp [RCode.program]
  have hsafe : ∀ T_hor, DemonicSafeWithin w L_peak T_hor (c.program out) ⟨0, x⟩ := fun T_hor => by
    refine h.demonicSafeWithin_assemble le_rfl hp fun z hz adv t _ cfg hcfg => ?_
    have hz_fr : z.data.frontier ≤ L_peak := h.post_frontier_le z hz
    cases t with
    | zero =>
      rw [evalRandDemonic, runRandResizable_zero, ProbComp.eval_pure,
        PMF.support_pure, Set.mem_singleton_iff] at hcfg
      subst hcfg; exact hz_fr
    | succ k =>
      rw [evalRandDemonic, runRandResizable_succ,
        stepRandResizable_halt (s := ⟨0 + c.size, z.data⟩) hhalt, pure_bind,
        runRandResizable_halted, ProbComp.eval_pure, PMF.support_pure,
        Set.mem_singleton_iff] at hcfg
      subst hcfg; exact hz_fr
  refine ⟨fun adv t => ?_, fun adv t cfg hcfg => (hsafe t adv t le_rfl cfg hcfg).frontierLe,
    le_top, fun adv y => ?_⟩
  · rw [PMF.apply_eq_zero_iff]
    exact fun hmem => (hsafe t adv t le_rfl .faulted hmem).ne_faulted rfl
  · have hle := (h.le_haltedReach_assemble (v := y.regs out) (d := y) hp).trans (iInf_le _ adv)
    have hmap : (μ.map RCodeStepOutcome.data) y ≤
        ∑' z, μ z * haltedReach w (c.program out) (y.regs out) y (0 + c.size) z.data := by
      rw [PMF.map_apply]
      refine tsum_le_tsum fun z => ?_
      by_cases hzy : y = z.data
      · subst hzy
        simp only [↓reduceIte]
        have h1 : (1 : ℝ≥0∞) ≤
            haltedReach w (c.program out) (z.data.regs out) z.data (0 + c.size) z.data := by
          refine le_iInf fun adv' => le_iSup_of_le 1 ?_
          rw [evalRandDemonic, runRandResizable_succ,
            stepRandResizable_halt (s := ⟨0 + c.size, z.data⟩) hhalt, pure_bind,
            runRandResizable_zero, ProbComp.eval_pure, PMF.pure_apply_self]
        simpa using mul_le_mul_right h1 (μ z)
      · simp [hzy]
    exact hmap.trans hle

end ExecRCodeSteps

/-- Flat-program WHP execution certificate on `RProgram B r`: combines `RDemonicFaultFree`,
every-step `PeakFrontierLe w L_peak`, exact unbounded-horizon halting law
`μ.map RCodeStepOutcome.data`, and deterministic `(B_hor + 1)`-step halting lower bounds across all
adaptive `.grow` adversaries `adv : RAdv r`. -/
structure ExecRProgramWhp (w : ℕ) (p : RProgram B r) (out : Fin r) (x : RData r)
    (μ : PMF (RCodeStepOutcome r)) (L_peak : ℕ) : Prop where
  /-- Full-horizon fault-freedom, `PeakFrontierLe`, and halting distribution. -/
  dist : ExecRProgramDist w p out x (μ.map RCodeStepOutcome.data) ⊤ L_peak
  /-- Pointwise clocked `(B_hor + 1)`-step halting lower bound across all `adv : RAdv r`. -/
  within_le : ∀ (B_hor : ℕ) (adv : RAdv r) (y : RData r),
    μ.toOuterMeasure {z | z.data = y ∧ z.WithinBudget B_hor} ≤
      evalRandDemonic w adv p (B_hor + 1) ⟨0, x⟩ (.halted (y.regs out) y)

/-- Compile any structured `ExecRCodeSteps` derivation to `ExecRProgramWhp` on `c.program out`. -/
theorem ExecRCodeSteps.toExecRProgramWhp {w L_peak : ℕ} {c : RCode B r} {x : RData r}
    {μ : PMF (RCodeStepOutcome r)} (h : ExecRCodeSteps w c x μ L_peak) (out : Fin r) :
    ExecRProgramWhp w (c.program out) out x μ L_peak :=
  ⟨h.toExecRProgramDist_top out, fun B_hor adv y =>
    h.toOuterMeasure_le_evalRandDemonic_program out B_hor adv y⟩

theorem not_execRProgramWhp_halt {w L_peak : ℕ} {out : Fin r} {x : RData r}
    {z : RCodeStepOutcome r} {μ : PMF (RCodeStepOutcome r)}
    (hz : z ∈ μ.support) (hne : z.data ≠ x) :
    ¬ExecRProgramWhp (B := B) w [.halt out] out x μ L_peak := fun h =>
  not_execRProgramDist_halt ((PMF.mem_support_map_iff _ _ _).mpr ⟨z, hz, rfl⟩) hne h.dist

end Cslib.WordRAM.Resizable

/-! ## Section 3: Resizable Word RAM WHP Oblivious-Sequence Certificates (`HighProbObliviousImpl`)
-/

namespace Cslib.DataStructure.WordRAM.Resizable.Randomized

open Cslib.WordRAM Cslib.WordRAM.Resizable Cslib.DataStructure Cslib.Probability
open Cslib.DataStructure.WordRAM.Resizable

universe u v z

/-- Single-step WHP subroutine outcome bundling updated latent state, `RData r`, decoded result,
and step-timing fields `(steps, timed)`. -/
structure WhpStepROutcome (Latent : Type z) (α : Type v) (r : ℕ) : Type (max v z) where
  /-- Updated internal latent state. -/
  latent : Latent
  /-- Updated concrete Resizable Word RAM state. -/
  data : RData r
  /-- Decoded observation returned by the operation. -/
  result : α
  /-- Executed body instruction bound when `timed = true`. -/
  steps : ℕ
  /-- Whether this execution branch met a finite step-count certificate. -/
  timed : Bool := true

/-- Extract the underlying `RCodeStepOutcome r` from a `WhpStepROutcome`. -/
@[expose] def WhpStepROutcome.toCodeOutcome {Latent : Type z} {α : Type v} {r : ℕ}
    (q : WhpStepROutcome Latent α r) : RCodeStepOutcome r :=
  ⟨q.data, q.steps, q.timed⟩

/-- Whether `q` finished within deterministic worst-case instruction budget `B_hor : ℕ`. -/
@[expose] def WhpStepROutcome.WithinBudget {Latent : Type z} {α : Type v} {r : ℕ}
    (B_hor : ℕ) (q : WhpStepROutcome Latent α r) : Prop :=
  q.timed = true ∧ q.steps ≤ B_hor

/-- Multi-operation WHP trajectory outcome recording the current latent state, concrete `RData r`,
accumulated input-output transcript, and `allWithinBudget : Bool` (whether **every** operation in
the sequence executed within its operation-specific `worstCaseTime o` budget). -/
structure WhpSeqROutcome (Latent : Type z) {Op : Type u} (Result : Op → Type v) (r : ℕ) :
    Type (max u v z) where
  /-- Current internal latent state. -/
  latent : Latent
  /-- Current concrete Resizable Word RAM state. -/
  data : RData r
  /-- Accumulated input-output transcript executed so far. -/
  transcript : List (Sigma Result)
  /-- `true` iff every executed operation `o_i` so far had `timed = true` and
  `steps ≤ worstCaseTime o_i`. -/
  allWithinBudget : Bool

/-- Initialize a `WhpSeqROutcome` from a `LatentRState` (`transcript = []`,
`allWithinBudget = true`). -/
@[expose] def WhpSeqROutcome.ofLatentRState {Latent : Type z} {Op : Type u}
    {Result : Op → Type v} {r : ℕ} (t : LatentRState Latent r) :
    WhpSeqROutcome Latent Result r where
  latent := t.latent
  data := t.data
  transcript := []
  allWithinBudget := true

/-- Append a single operation outcome `q` with worst-case budget `B_op : ℕ` to `tr`. -/
@[expose] def WhpSeqROutcome.appendStep {Latent : Type z} {Op : Type u}
    {Result : Op → Type v} {r : ℕ}
    (tr : WhpSeqROutcome Latent Result r) (o : Op) (B_op : ℕ)
    (q : WhpStepROutcome Latent (Result o) r) : WhpSeqROutcome Latent Result r where
  latent := q.latent
  data := q.data
  transcript := tr.transcript ++ [⟨o, q.result⟩]
  allWithinBudget := tr.allWithinBudget && (q.timed && decide (q.steps ≤ B_op))

/-- Cumulative sequence failure-probability sum across remaining operations `remOps` after prefix
`prefOps`. -/
@[expose] noncomputable def totalFailureProb {Op : Type u}
    (failureProb : List Op → Op → ℝ≥0∞) : List Op → List Op → ℝ≥0∞
  | _, [] => 0
  | prefOps, o :: ops => failureProb prefOps o + totalFailureProb failureProb (prefOps ++ [o]) ops

@[simp]
theorem totalFailureProb_nil {Op : Type u} (failureProb : List Op → Op → ℝ≥0∞)
    (prefOps : List Op) : totalFailureProb failureProb prefOps [] = 0 := rfl

@[simp]
theorem totalFailureProb_cons {Op : Type u} (failureProb : List Op → Op → ℝ≥0∞)
    (prefOps : List Op) (o : Op) (ops : List Op) :
    totalFailureProb failureProb prefOps (o :: ops) =
      failureProb prefOps o + totalFailureProb failureProb (prefOps ++ [o]) ops := rfl

/-- Multi-operation structured WHP execution across remaining operations `remOps` after `prefOps`:
at each operation `o`, `P.code` executes under `ExecRCodeSteps` within peak frontier
`base + peakSpaceBound prefOps o`, establishes resting frontier
`base ≤ q.data.frontier ≤ base + spaceBound (prefOps ++ [o])`, decodes `q.result`, preserves caller
memory `[0, base)`, and records whether `q` completed within `worstCaseTime o` instructions. -/
inductive ExecWhpSteps {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (S : DataStructure.ObliviousSequenceSpec.{u, v})
    (Latent : Type z) (w base : ℕ)
    (spaceBound : List S.Op → ℕ)
    (peakSpaceBound : List S.Op → S.Op → ℕ)
    (worstCaseTime : S.Op → ℕ)
    (encode : S.Op → Fin r_ds → ℕ)
    (decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)) :
    List S.Op → List S.Op → PMF (WhpSeqROutcome Latent S.Result r_ds) →
      PMF (WhpSeqROutcome Latent S.Result r_ds) → Prop where
  | nil (prefOps : List S.Op) (τ : PMF (WhpSeqROutcome Latent S.Result r_ds)) :
      ExecWhpSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
        prefOps [] τ τ
  | cons {prefOps : List S.Op} {o : S.Op} {ops : List S.Op}
      {τ τ_final : PMF (WhpSeqROutcome Latent S.Result r_ds)}
      {μ_step : WhpSeqROutcome Latent S.Result r_ds →
        PMF (WhpStepROutcome Latent (S.Result o) r_ds)} :
      (∀ tr ∈ τ.support,
        tr.data.Bounded w ∧
        (∀ i, P.input i = true → Fits w (encode o i)) ∧
        (P.prepare encode o tr.data).Bounded w ∧
        ExecRCodeSteps w P.code (P.prepare encode o tr.data)
          ((μ_step tr).map WhpStepROutcome.toCodeOutcome) (base + peakSpaceBound prefOps o) ∧
        ∀ q ∈ (μ_step tr).support,
          q.data.Bounded w ∧
          (base ≤ q.data.frontier ∧
            q.data.frontier ≤ base + spaceBound (prefOps ++ [o]) ∧
            q.data.regs P.baseReg = base) ∧
          decode o q.data.regs = some q.result ∧
          (∀ addr < base, q.data.mem addr = tr.data.mem addr)) →
      ExecWhpSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
        (prefOps ++ [o]) ops
        (τ.bind fun tr => (μ_step tr).map (tr.appendStep o (worstCaseTime o))) τ_final →
      ExecWhpSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
        prefOps (o :: ops) τ τ_final

/-- `ExecWhpSteps` preserves `RData.Bounded w` across all support trajectories. -/
theorem ExecWhpSteps.bounded {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {worstCaseTime : S.Op → ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {prefOps remOps : List S.Op}
    {τ τ_final : PMF (WhpSeqROutcome Latent S.Result r_ds)}
    (h : ExecWhpSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
      prefOps remOps τ τ_final)
    (hbdd : ∀ tr ∈ τ.support, tr.data.Bounded w) :
    ∀ tr ∈ τ_final.support, tr.data.Bounded w := by
  induction h with
  | nil _ _ => exact hbdd
  | cons hstep _ ih =>
    refine ih fun q_seq hq_seq => ?_
    rw [PMF.mem_support_bind_iff] at hq_seq; obtain ⟨tr, htr, hq_map⟩ := hq_seq
    rw [PMF.mem_support_map_iff] at hq_map; obtain ⟨q, hq, rfl⟩ := hq_map
    exact ((hstep tr htr).2.2.2.2 q hq).1

/-- `ExecWhpSteps` establishes resting frontier bounds `base ≤ tr.data.frontier ≤
base + spaceBound (prefOps ++ remOps)` and `tr.data.regs P.baseReg = base` on `τ_final.support`. -/
theorem ExecWhpSteps.frontier_le {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {worstCaseTime : S.Op → ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {prefOps remOps : List S.Op}
    {τ τ_final : PMF (WhpSeqROutcome Latent S.Result r_ds)}
    (h : ExecWhpSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
      prefOps remOps τ τ_final)
    (hfr : ∀ tr ∈ τ.support,
      base ≤ tr.data.frontier ∧ tr.data.frontier ≤ base + spaceBound prefOps ∧
        tr.data.regs P.baseReg = base) :
    ∀ tr ∈ τ_final.support,
      base ≤ tr.data.frontier ∧ tr.data.frontier ≤ base + spaceBound (prefOps ++ remOps) ∧
        tr.data.regs P.baseReg = base := by
  induction h with
  | nil prefOps _ => simpa only [List.append_nil] using hfr
  | @cons prefOps o ops τ _ μ_step hstep _ ih =>
    have h₁ : ∀ q_seq ∈
        (τ.bind fun tr => (μ_step tr).map (tr.appendStep o (worstCaseTime o))).support,
        base ≤ q_seq.data.frontier ∧
        q_seq.data.frontier ≤ base + spaceBound (prefOps ++ [o]) ∧
        q_seq.data.regs P.baseReg = base := by
      intro q_seq hq_seq
      rw [PMF.mem_support_bind_iff] at hq_seq; obtain ⟨tr, htr, hq_map⟩ := hq_seq
      rw [PMF.mem_support_map_iff] at hq_map; obtain ⟨q, hq, rfl⟩ := hq_map
      exact ((hstep tr htr).2.2.2.2 q hq).2.1
    simpa only [List.append_assoc, List.singleton_append] using ih h₁

/-- `ExecWhpSteps` preserves caller memory `[0, base)` across all support trajectories. -/
theorem ExecWhpSteps.caller_mem {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {worstCaseTime : S.Op → ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {prefOps remOps : List S.Op}
    {τ τ_final : PMF (WhpSeqROutcome Latent S.Result r_ds)}
    (h : ExecWhpSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
      prefOps remOps τ τ_final)
    {mem₀ : ℕ → ℕ} (h₀ : ∀ tr ∈ τ.support, ∀ addr < base, tr.data.mem addr = mem₀ addr) :
    ∀ tr ∈ τ_final.support, ∀ addr < base, tr.data.mem addr = mem₀ addr := by
  induction h with
  | nil _ _ => exact h₀
  | cons hstep _ ih =>
    refine ih fun q_seq hq_seq addr hlt => ?_
    rw [PMF.mem_support_bind_iff] at hq_seq; obtain ⟨tr, htr, hq_map⟩ := hq_seq
    rw [PMF.mem_support_map_iff] at hq_map; obtain ⟨q, hq, rfl⟩ := hq_map
    exact (((hstep tr htr).2.2.2.2 q hq).2.2.2 addr hlt).trans (h₀ tr htr addr hlt)

/-- Transport `ExecWhpSteps` along any basis simulation `φ : B.Simulates B'`. -/
theorem ExecWhpSteps.mapSimulates {B B' : Basis} {r_ds k_init : ℕ}
    (φ : B.Simulates B')
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {worstCaseTime : S.Op → ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {prefOps remOps : List S.Op}
    {τ τ_final : PMF (WhpSeqROutcome Latent S.Result r_ds)}
    (h : ExecWhpSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
      prefOps remOps τ τ_final) :
    ExecWhpSteps (P.mapSimulates φ) S Latent w base spaceBound peakSpaceBound worstCaseTime
      encode decode prefOps remOps τ τ_final := by
  induction h with
  | nil prefOps τ => exact .nil prefOps τ
  | cons hstep _ ih =>
    refine .cons (fun tr htr => ?_) ih
    obtain ⟨hbdd, hfit, hprep, he, hq⟩ := hstep tr htr
    exact ⟨hbdd, hfit, hprep, he.mapSimulates φ, hq⟩

/-- Multi-operation compiled flat-`RProgram` WHP execution relation over `ExecRProgramWhp`. -/
inductive ExecWhpProgramSteps {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (S : DataStructure.ObliviousSequenceSpec.{u, v})
    (Latent : Type z) (w base : ℕ)
    (spaceBound : List S.Op → ℕ)
    (peakSpaceBound : List S.Op → S.Op → ℕ)
    (worstCaseTime : S.Op → ℕ)
    (encode : S.Op → Fin r_ds → ℕ)
    (decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o))
    (p_op : RProgram B r_ds) (out : Fin r_ds) :
    List S.Op → List S.Op → PMF (WhpSeqROutcome Latent S.Result r_ds) →
      PMF (WhpSeqROutcome Latent S.Result r_ds) → Prop where
  | nil (prefOps : List S.Op) (τ : PMF (WhpSeqROutcome Latent S.Result r_ds)) :
      ExecWhpProgramSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
        p_op out prefOps [] τ τ
  | cons {prefOps : List S.Op} {o : S.Op} {ops : List S.Op}
      {τ τ_final : PMF (WhpSeqROutcome Latent S.Result r_ds)}
      {μ_step : WhpSeqROutcome Latent S.Result r_ds →
        PMF (WhpStepROutcome Latent (S.Result o) r_ds)} :
      (∀ tr ∈ τ.support,
        ExecRProgramWhp w p_op out (P.prepare encode o tr.data)
          ((μ_step tr).map WhpStepROutcome.toCodeOutcome) (base + peakSpaceBound prefOps o) ∧
        ∀ q ∈ (μ_step tr).support,
          q.data.Bounded w ∧
          (base ≤ q.data.frontier ∧
            q.data.frontier ≤ base + spaceBound (prefOps ++ [o]) ∧
            q.data.regs P.baseReg = base) ∧
          decode o q.data.regs = some q.result ∧
          (∀ addr < base, q.data.mem addr = tr.data.mem addr)) →
      ExecWhpProgramSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
        p_op out (prefOps ++ [o]) ops
        (τ.bind fun tr => (μ_step tr).map (tr.appendStep o (worstCaseTime o))) τ_final →
      ExecWhpProgramSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
        p_op out prefOps (o :: ops) τ τ_final

/-- Compile structured `ExecWhpSteps` to flat `ExecWhpProgramSteps` on `P.opProg out` (halting
within `worstCaseTime o + 1` clocked steps on every fast branch across all `adv : RAdv r_ds`). -/
theorem ExecWhpSteps.toExecWhpProgramSteps {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {worstCaseTime : S.Op → ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    (out : Fin r_ds) {prefOps remOps : List S.Op}
    {τ τ_final : PMF (WhpSeqROutcome Latent S.Result r_ds)}
    (h : ExecWhpSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
      prefOps remOps τ τ_final) :
    ExecWhpProgramSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
      (P.opProg out) out prefOps remOps τ τ_final := by
  induction h with
  | nil prefOps τ => exact .nil prefOps τ
  | @cons _ _ _ _ _ μ_step hstep _ ih =>
    refine .cons (μ_step := μ_step) (fun tr htr => ?_) ih
    obtain ⟨_, _, _, he, hq⟩ := hstep tr htr
    exact ⟨he.toExecRProgramWhp out, hq⟩

/-- Every support trajectory `tr ∈ τ.support` extends to some final trajectory `u ∈ τ_final.support`
whose transcript has `tr.transcript` as a prefix. -/
theorem ExecWhpProgramSteps.transcript_prefix {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {worstCaseTime : S.Op → ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {p_op : RProgram B r_ds} {out : Fin r_ds} {prefOps remOps : List S.Op}
    {τ τ_final : PMF (WhpSeqROutcome Latent S.Result r_ds)}
    (h : ExecWhpProgramSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode
      decode p_op out prefOps remOps τ τ_final)
    {tr : WhpSeqROutcome Latent S.Result r_ds} (htr : tr ∈ τ.support) :
    ∃ u ∈ τ_final.support, tr.transcript <+: u.transcript := by
  induction h generalizing tr with
  | nil _ _ => exact ⟨tr, htr, List.prefix_refl _⟩
  | @cons _ o _ τ _ μ_step _ _ ih =>
    obtain ⟨q, hq⟩ := (μ_step tr).support_nonempty
    have htr' : tr.appendStep o (worstCaseTime o) q ∈
        (τ.bind fun t => (μ_step t).map (t.appendStep o (worstCaseTime o))).support := by
      rw [PMF.mem_support_bind_iff]
      exact ⟨tr, htr, (PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩⟩
    obtain ⟨u, hu, hpref⟩ := ih htr'
    exact ⟨u, hu, (List.prefix_append tr.transcript [⟨o, q.result⟩]).trans hpref⟩

/-- **`.halt`-rejection soundness check (`not_execWhpProgramSteps_halt`):** a 1-instruction
`[.halt out]` stub cannot satisfy `ExecWhpProgramSteps` on `(o :: ops)` whenever for some
`tr ∈ τ.support`, no observation `a` decoded from `P.prepare encode o tr.data` can appear at the
next position of `τ_final`'s transcripts (or when `P.prepare encode o tr.data` violates the
post-step frontier bound). -/
theorem not_execWhpProgramSteps_halt {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {worstCaseTime : S.Op → ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    (out : Fin r_ds) {prefOps : List S.Op} {o : S.Op} {ops : List S.Op}
    {τ τ_final : PMF (WhpSeqROutcome Latent S.Result r_ds)}
    {tr : WhpSeqROutcome Latent S.Result r_ds} (htr : tr ∈ τ.support)
    (hbad : ∀ a,
      decode o (P.prepare encode o tr.data).regs = some a →
      base ≤ (P.prepare encode o tr.data).frontier →
      (P.prepare encode o tr.data).frontier ≤ base + spaceBound (prefOps ++ [o]) →
      ∀ u ∈ τ_final.support, tr.transcript ++ [⟨o, a⟩] <+: u.transcript → False) :
    ¬ExecWhpProgramSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode
      [.halt out] out prefOps (o :: ops) τ τ_final := by
  intro h; cases h with
  | @cons _ _ _ _ _ μ_step hstep hrest =>
    obtain ⟨hprog, hq_all⟩ := hstep tr htr
    obtain ⟨q, hq⟩ := (μ_step tr).support_nonempty
    obtain ⟨_, ⟨hlo, hhi, _⟩, hdec, _⟩ := hq_all q hq
    by_cases hqd : q.data = P.prepare encode o tr.data
    · rw [hqd] at hlo hhi hdec
      have htr' : tr.appendStep o (worstCaseTime o) q ∈
          (τ.bind fun t => (μ_step t).map (t.appendStep o (worstCaseTime o))).support := by
        rw [PMF.mem_support_bind_iff]
        exact ⟨tr, htr, (PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩⟩
      obtain ⟨u, hu, hpref⟩ := hrest.transcript_prefix htr'
      exact hbad q.result hdec hlo hhi u hu hpref
    · exact not_execRProgramWhp_halt ((PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩) hqd hprog

/-- Reusable Resizable Word RAM subroutine implementation certificate for a randomized data
structure `P : SubroutineCode B r_ds k_init` realizing an oblivious-sequence specification `S` with
**deterministic worst-case** operation step budgets `worstCaseTime : S.Op → ℕ`, trajectory-indexed
per-step failure probability `failureProb : List S.Op → S.Op → ℝ≥0∞`, resting word bound
`spaceBound : List S.Op → ℕ`, and intermediate peak word bound
`peakSpaceBound : List S.Op → S.Op → ℕ`. -/
structure HighProbObliviousImpl {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (S : DataStructure.ObliviousSequenceSpec.{u, v})
    (w base : ℕ) (params : Fin k_init → ℕ) : Type (max u v (z + 1)) where
  /-- Internal latent state type. -/
  Latent : Type z
  /-- Resting post-prefix word-footprint upper bound `x.frontier ≤ base + spaceBound prefOps`. -/
  spaceBound : List S.Op → ℕ
  /-- Peak intermediate word-footprint bound `y.frontier ≤ base + peakSpaceBound prefOps o`. -/
  peakSpaceBound : List S.Op → S.Op → ℕ
  /-- Worst-case instruction budget for `P.initCode`. -/
  initSteps : ℕ
  /-- Operation-indexed deterministic worst-case body instruction budget. -/
  worstCaseTime : S.Op → ℕ
  /-- Trajectory-indexed per-operation slow-path failure probability bound. -/
  failureProb : List S.Op → S.Op → ℝ≥0∞
  /-- Distributional invariant on the initial coupled distribution produced by `P.initCode`. -/
  initInv : PMF (LatentRState Latent r_ds) → Prop
  /-- Predicate under which `arguments_fit` bounds encoded arguments (`fun _ _ => True` default). -/
  validOp : Latent → S.Op → Prop := fun _ _ => True
  /-- Standalone register encoding for argument delivery. -/
  encode : S.Op → Fin r_ds → ℕ
  /-- Output decoder reading typed operation observations from final registers. -/
  decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)
  /-- Initial distributions satisfying `initInv` are supported on word-bounded states. -/
  bounded : ∀ {ν : PMF (LatentRState Latent r_ds)}, initInv ν → ∀ t ∈ ν.support, t.data.Bounded w
  /-- Initial distributions satisfying `initInv` establish resting frontier bounds at `[]`. -/
  frontier_le : ∀ {ν : PMF (LatentRState Latent r_ds)}, initInv ν →
    ∀ t ∈ ν.support,
      base ≤ t.data.frontier ∧ t.data.frontier ≤ base + spaceBound [] ∧ t.data.regs P.baseReg = base
  /-- Standalone encoded arguments fit in `w`-bit words on operations satisfying `validOp`. -/
  arguments_fit : ∀ {z : Latent} (o : S.Op),
    validOp z o → ∀ i, P.input i = true → Fits w (encode o i)
  /-- Worst-case bounded initialization of `P.initCode` from `x₀.frontier = base` within
  `initSteps` instructions, preserving caller memory `[0, base)`. -/
  init_exec : ∀ {x₀ : RData r_ds},
    x₀.Bounded w → x₀.frontier = base → (∀ j, x₀.regs (P.initParams j) = params j) →
    Fits w (base + spaceBound []) →
    ∃ ν₀ : PMF (LatentRState Latent r_ds),
      ExecRCodeSteps w P.initCode x₀
        (ν₀.map fun t => ⟨t.data, initSteps, true⟩) (base + spaceBound []) ∧
      initInv ν₀ ∧
      ∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = x₀.mem addr
  /-- Multi-operation WHP execution across any admissible oblivious sequence `ops : List S.Op` whose
  trajectory peaks fit in `w`-bit words (`ObliviousPeakFits w base peakSpaceBound [] ops`). -/
  steps_exec : ∀ (ops : List S.Op) (ν₀ : PMF (LatentRState Latent r_ds)),
    S.ValidOpSeq ops → ObliviousPeakFits w base peakSpaceBound [] ops → initInv ν₀ →
    ∃ τ_final : PMF (WhpSeqROutcome Latent S.Result r_ds),
      ExecWhpSteps P S Latent w base spaceBound peakSpaceBound worstCaseTime encode decode [] ops
        (ν₀.map WhpSeqROutcome.ofLatentRState) τ_final ∧
      S.Contract ops (τ_final.map WhpSeqROutcome.transcript) ∧
      τ_final.toOuterMeasure {tr | tr.allWithinBudget = false} ≤
        totalFailureProb failureProb [] ops

namespace HighProbObliviousImpl

variable {B B' : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init}
  {S : DataStructure.ObliviousSequenceSpec.{u, v}}
  {params : Fin k_init → ℕ}

/-- Specialization of `ExecWhpSteps` from prefix `[]` to `C : HighProbObliviousImpl`. -/
abbrev Steps (C : HighProbObliviousImpl.{u, v, z} P S w base params) :
    List S.Op → PMF (WhpSeqROutcome C.Latent S.Result r_ds) →
      PMF (WhpSeqROutcome C.Latent S.Result r_ds) → Prop :=
  ExecWhpSteps P S C.Latent w base C.spaceBound C.peakSpaceBound C.worstCaseTime C.encode C.decode
    []

/-- Specialization of `ExecWhpProgramSteps` from prefix `[]` to `C : HighProbObliviousImpl`. -/
abbrev ProgramSteps (C : HighProbObliviousImpl.{u, v, z} P S w base params)
    (p_op : RProgram B r_ds) (out : Fin r_ds) :
    List S.Op → PMF (WhpSeqROutcome C.Latent S.Result r_ds) →
      PMF (WhpSeqROutcome C.Latent S.Result r_ds) → Prop :=
  ExecWhpProgramSteps P S C.Latent w base C.spaceBound C.peakSpaceBound C.worstCaseTime
    C.encode C.decode p_op out []

/-- Transport a `HighProbObliviousImpl` certificate along `φ : B.Simulates B'`. -/
@[expose]
def mapSimulates (φ : B.Simulates B')
    (C : HighProbObliviousImpl.{u, v, z} P S w base params) :
    HighProbObliviousImpl.{u, v, z} (P.mapSimulates φ) S w base params where
  Latent := C.Latent
  spaceBound := C.spaceBound
  peakSpaceBound := C.peakSpaceBound
  initSteps := C.initSteps
  worstCaseTime := C.worstCaseTime
  failureProb := C.failureProb
  initInv := C.initInv
  validOp := C.validOp
  encode := C.encode
  decode := C.decode
  bounded := C.bounded
  frontier_le := C.frontier_le
  arguments_fit := C.arguments_fit
  init_exec hx₀ hfr hpar hfit := by
    obtain ⟨ν₀, he, hinv, hcaller⟩ := C.init_exec hx₀ hfr hpar hfit
    exact ⟨ν₀, he.mapSimulates φ, hinv, hcaller⟩
  steps_exec ops ν₀ hv hfit hinv := by
    obtain ⟨τ_final, hex, hcontract, hfail⟩ := C.steps_exec ops ν₀ hv hfit hinv
    exact ⟨τ_final, hex.mapSimulates φ, hcontract, hfail⟩

/-- Lift an exact-basis `HighProbObliviousImpl` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : HighProbObliviousImpl.{u, v, z} P S w base params) :
    HighProbObliviousImpl.{u, v, z} P.toStandard S w base params :=
  C.mapSimulates .exactStandard

/-- **End-to-end Resizable Word RAM whole-sequence WHP theorem (`seq_whp`).**
Across any admissible oblivious sequence `ops : List S.Op` satisfying `ObliviousPeakFits`,
`initCode`
executes in `≤ C.initSteps` deterministic worst-case instructions, every operation maintains
stepwise peak hardware frontier `≤ base + C.peakSpaceBound prefOps o` and resting frontier
`≤ base + C.spaceBound ops` while preserving caller memory `[0, base)` and realizing `S.Contract`,
and with probability at least `1 - totalFailureProb C.failureProb [] ops`, **every** operation `o`
in `ops` executes within `C.worstCaseTime o` body instructions. -/
theorem seq_whp (C : HighProbObliviousImpl.{u, v, z} P S w base params)
    {x₀ : RData r_ds} (ops : List S.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j)
    (hfit₀ : Fits w (base + C.spaceBound []))
    (hv : S.ValidOpSeq ops) (hfit_ops : ObliviousPeakFits w base C.peakSpaceBound [] ops) :
    ∃ (ν₀ : PMF (LatentRState C.Latent r_ds))
      (τ_final : PMF (WhpSeqROutcome C.Latent S.Result r_ds)),
      ExecRCodeSteps w P.initCode x₀
        (ν₀.map fun t => ⟨t.data, C.initSteps, true⟩) (base + C.spaceBound []) ∧
      (∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = x₀.mem addr) ∧
      C.Steps ops (ν₀.map WhpSeqROutcome.ofLatentRState) τ_final ∧
      (∀ tr ∈ τ_final.support,
        tr.data.Bounded w ∧
        (base ≤ tr.data.frontier ∧ tr.data.frontier ≤ base + C.spaceBound ops ∧
          tr.data.regs P.baseReg = base) ∧
        (∀ addr < base, tr.data.mem addr = x₀.mem addr)) ∧
      S.Contract ops (τ_final.map WhpSeqROutcome.transcript) ∧
      τ_final.toOuterMeasure {tr | tr.allWithinBudget = false} ≤
        totalFailureProb C.failureProb [] ops ∧
      1 - totalFailureProb C.failureProb [] ops ≤
        τ_final.toOuterMeasure {tr | tr.allWithinBudget = true} := by
  obtain ⟨ν₀, he_init, hinv, hcaller₀⟩ := C.init_exec hx₀ hfr₀ hpar hfit₀
  obtain ⟨τ_final, hex, hcontract, hfail⟩ := C.steps_exec ops ν₀ hv hfit_ops hinv
  have hbdd₀ : ∀ tr ∈ (ν₀.map (WhpSeqROutcome.ofLatentRState (Result := S.Result))).support,
      tr.data.Bounded w := by
    intro tr htr; rw [PMF.mem_support_map_iff] at htr; obtain ⟨u, hu, rfl⟩ := htr
    exact C.bounded hinv u hu
  have hfr_init : ∀ tr ∈ (ν₀.map (WhpSeqROutcome.ofLatentRState (Result := S.Result))).support,
      base ≤ tr.data.frontier ∧ tr.data.frontier ≤ base + C.spaceBound [] ∧
        tr.data.regs P.baseReg = base := by
    intro tr htr; rw [PMF.mem_support_map_iff] at htr; obtain ⟨u, hu, rfl⟩ := htr
    exact C.frontier_le hinv u hu
  have hcaller_init : ∀ tr ∈ (ν₀.map (WhpSeqROutcome.ofLatentRState (Result := S.Result))).support,
      ∀ addr < base, tr.data.mem addr = x₀.mem addr := by
    intro tr htr; rw [PMF.mem_support_map_iff] at htr; obtain ⟨u, hu, rfl⟩ := htr
    exact hcaller₀ u hu
  have hbdd_fin := hex.bounded hbdd₀
  have hfr_fin := hex.frontier_le hfr_init
  have hcaller_fin := hex.caller_mem hcaller_init
  rw [List.nil_append] at hfr_fin
  refine ⟨ν₀, τ_final, he_init, hcaller₀, hex,
    fun tr htr => ⟨hbdd_fin tr htr, hfr_fin tr htr, hcaller_fin tr htr⟩,
    hcontract, hfail, ?_⟩
  refine (Cslib.Probability.PMF.one_sub_le_toOuterMeasure_compl τ_final _ hfail).trans ?_
  refine MeasureTheory.measure_mono fun tr htr => ?_
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Bool.not_eq_false] at htr
  exact htr

/-- **Compiled flat-`RProgram` end-to-end WHP sequence theorem (`seq_toExecWhpProgramSteps`).** -/
theorem seq_toExecWhpProgramSteps (C : HighProbObliviousImpl.{u, v, z} P S w base params)
    (out : Fin r_ds) {x₀ : RData r_ds} (ops : List S.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j)
    (hfit₀ : Fits w (base + C.spaceBound []))
    (hv : S.ValidOpSeq ops) (hfit_ops : ObliviousPeakFits w base C.peakSpaceBound [] ops) :
    ∃ (ν₀ : PMF (LatentRState C.Latent r_ds))
      (τ_final : PMF (WhpSeqROutcome C.Latent S.Result r_ds)),
      ExecRProgramWhp w (P.initProg out) out x₀
        (ν₀.map fun t => ⟨t.data, C.initSteps, true⟩) (base + C.spaceBound []) ∧
      (∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = x₀.mem addr) ∧
      C.ProgramSteps (P.opProg out) out ops (ν₀.map WhpSeqROutcome.ofLatentRState) τ_final ∧
      (∀ tr ∈ τ_final.support,
        tr.data.Bounded w ∧
        (base ≤ tr.data.frontier ∧ tr.data.frontier ≤ base + C.spaceBound ops ∧
          tr.data.regs P.baseReg = base) ∧
        (∀ addr < base, tr.data.mem addr = x₀.mem addr)) ∧
      S.Contract ops (τ_final.map WhpSeqROutcome.transcript) ∧
      1 - totalFailureProb C.failureProb [] ops ≤
        τ_final.toOuterMeasure {tr | tr.allWithinBudget = true} := by
  obtain ⟨ν₀, τ_final, he_init, hcaller₀, hex, hpost, hcontract, _, hsucc⟩ :=
    C.seq_whp ops hx₀ hfr₀ hpar hfit₀ hv hfit_ops
  exact ⟨ν₀, τ_final, he_init.toExecRProgramWhp out, hcaller₀, hex.toExecWhpProgramSteps out,
    hpost, hcontract, hsucc⟩

end HighProbObliviousImpl

end Cslib.DataStructure.WordRAM.Resizable.Randomized
