/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Resizable.Basic
public import CslibFrontier.Languages.Probabilistic.Expect
public import CslibFrontier.Probability.PMF.Bind
public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map

/-!
# Clocked randomized execution and adaptive-adversary expected time on the Resizable Word RAM

Clocked probabilistic operational semantics, adaptive-adversary fault-freedom, every-step peak
hardware-frontier bounds (`PeakFrontierLe`), `ℝ≥0∞`-valued expected running time
(`expectedTimeDemonic`), and flat-program halting-distribution specifications (`ExecRProgramDist`)
for the word-granular **Resizable Word RAM** (`Cslib.WordRAM.Resizable`).

When a flat program `p : RProgram B r` executes single-word `.grow dst`, a time- and state-adaptive
adversary `adv : RAdv r` (`ℕ → RState r → ℕ → ℕ`), observing the step index `t` and the full
current machine state `s : RState r`, chooses an arbitrary `w`-bit initial word at address
`s.data.frontier` (`advGrowMem w (advStep s) s.data.frontier 1 s.data.mem`). Every flat-program
specification quantifies universally (or takes the supremum in `ℝ≥0∞`) over all `adv : RAdv r`.

## Main definitions

* `Cslib.WordRAM.Resizable.RAdv`, `Cslib.WordRAM.Resizable.advGrowMem`: time- and state-adaptive
  adversary for newly grown words on `.grow`.
* `Cslib.WordRAM.Resizable.stepRandResizable`, `Cslib.WordRAM.Resizable.runRandResizable`,
  `Cslib.WordRAM.Resizable.evalRandDemonic`: single-step and clocked `t`-step probabilistic
  execution in `ProbComp` and `PMF`.
* `Cslib.WordRAM.Resizable.RDemonicFaultFree`, `Cslib.WordRAM.Resizable.PeakFrontierLe`,
  `Cslib.WordRAM.Resizable.AlmostSurelyHaltsDemonic`,
  `Cslib.WordRAM.Resizable.expectedTimeDemonic`: fault-freedom, every-step peak hardware-frontier
  bound, almost-sure halting, and supremum expected instruction count across all adaptive
  adversaries.
* `Cslib.WordRAM.Resizable.ExecRProgramDist`: flat-program execution certificate coupling fault
  freedom, `PeakFrontierLe`, `expectedTimeDemonic ≤ T`, and exact halting-state distribution `μ`.

## Main results

* `Cslib.WordRAM.Resizable.ExecRProgramDist.iSup_evalRandDemonic_halted_eq`: `ExecRProgramDist`
  pins the limiting halting probability of every state `y` to `μ y` under every adversary `adv`.
* `Cslib.WordRAM.Resizable.ExecRProgramDist.almostSurelyHaltsDemonic`: every `ExecRProgramDist`
  halts almost surely across all adaptive adversaries.
* `Cslib.WordRAM.Resizable.not_execRProgramDist_halt`: a 1-instruction `[.halt out]` program cannot
  satisfy `ExecRProgramDist` for any target distribution assigning positive mass outside `x`.

## References

* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF pp. 16–20 / printed pp. 15–19; Theorem 5.2(6) and Footnote 10, PDF p. 18 /
  printed p. 17).
* [MitzenmacherUpfal2017] Michael Mitzenmacher and Eli Upfal, *Probability and Computing*, 2nd ed.,
  Cambridge University Press, 2017, Sections 2.1, 2.3, and 2.4.
-/
@[expose] public section

open scoped ENNReal

namespace Cslib.WordRAM.Resizable

variable {B B' : Basis} {r : ℕ}

/-! ## Adaptive adversary and clocked randomized execution -/

/-- Time- and state-adaptive adversary choosing initial word contents on `.grow` instructions as a
function of step index `t : ℕ`, active machine state `s : RState r`, and word address `a : ℕ`. -/
abbrev RAdv (r : ℕ) : Type := ℕ → RState r → ℕ → ℕ

/-- Shift an adaptive adversary forward by `d` execution steps. -/
def RAdv.shift (d : ℕ) (adv : RAdv r) : RAdv r := fun t s a => adv (t + d) s a

@[simp] theorem RAdv.shift_zero (adv : RAdv r) : adv.shift 0 = adv := rfl

theorem RAdv.shift_shift (d₁ d₂ : ℕ) (adv : RAdv r) :
    (adv.shift d₁).shift d₂ = adv.shift (d₁ + d₂) := by
  funext t s a; dsimp only [RAdv.shift]; congr 1; omega

/-- Prepend a single-step initializer `f` before `adv` so `(adv.prepend f).shift 1 = adv`. -/
def RAdv.prepend (f : RState r → ℕ → ℕ) (adv : RAdv r) : RAdv r
  | 0, s, a => f s a
  | t + 1, s, a => adv t s a

@[simp] theorem RAdv.prepend_zero (f : RState r → ℕ → ℕ) (adv : RAdv r) :
    (adv.prepend f) 0 = f := rfl

@[simp] theorem RAdv.shift_one_prepend (f : RState r → ℕ → ℕ) (adv : RAdv r) :
    (adv.prepend f).shift 1 = adv := by
  funext t s a; simp [RAdv.shift, RAdv.prepend]

/-- Adversarial memory initializer for `.grow`: preserves `mem a` for `a < L`, writes
`init a % 2 ^ w` in `[L, L + k)`, and zeroes `a ≥ L + k`. -/
def advGrowMem (w : ℕ) (init : ℕ → ℕ) (L k : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  fun a => if a < L then mem a else if a < L + k then init a % 2 ^ w else 0

/-- Every `advGrowMem` instance satisfies `DemonicGrow`. -/
theorem demonicGrow_advGrowMem (w : ℕ) (init : ℕ → ℕ) (L k : ℕ) (mem : ℕ → ℕ) :
    DemonicGrow w L k mem (advGrowMem w init L k mem) := by
  refine ⟨fun a ha => by simp [advGrowMem, ha], fun a hlo hhi => ?_, fun a ha => ?_⟩
  · simpa only [Fits, advGrowMem, Nat.not_lt.mpr hlo, ↓reduceIte, hhi] using
      Nat.mod_lt _ (Nat.two_pow_pos w)
  · simp [advGrowMem, show ¬a < L by omega, show ¬a < L + k by omega]

/-- Single step of randomized execution of `p : RProgram B r` at word width `w` under single-step
growth initializer `advStep : RState r → ℕ → ℕ`. Halted and faulted configurations are absorbing. -/
def stepRandResizable (w : ℕ) (advStep : RState r → ℕ → ℕ) (p : RProgram B r) :
    RCfg r → ProbComp (RCfg r)
  | .running s =>
    match p[s.pc]? with
    | none => pure .faulted
    | some (.op o) =>
      match evalResizable w o s.data with
      | some x => pure (.running ⟨s.pc + 1, x⟩)
      | none => pure .faulted
    | some (.jump target) => pure (.running ⟨target, s.data⟩)
    | some (.branch c target) =>
      pure (.running ⟨if c.Holds s.data.toData then target else s.pc + 1, s.data⟩)
    | some (.halt i) => pure (.halted (s.data.regs i) s.data)
    | some (.rand dst src) =>
      if Fits w (s.data.regs src) then do
        let k ← ProbComp.unifFin (s.data.regs src)
        pure (.running ⟨s.pc + 1, s.data.set dst k.val⟩)
      else pure .faulted
    | some (.grow dst) =>
      if Fits w (s.data.frontier + 1) then
        let mem' := advGrowMem w (advStep s) s.data.frontier 1 s.data.mem
        pure (.running ⟨s.pc + 1,
          ⟨Function.update s.data.regs dst s.data.frontier, mem', s.data.frontier + 1⟩⟩)
      else pure .faulted
    | some .shrink =>
      if 1 ≤ s.data.frontier then
        pure (.running ⟨s.pc + 1,
          ⟨s.data.regs, clear s.data.mem (s.data.frontier - 1) 1, s.data.frontier - 1⟩⟩)
      else pure .faulted
  | cfg => pure cfg

section StepLemmas

variable {w : ℕ} {advStep : RState r → ℕ → ℕ} {p : RProgram B r} {s : RState r}

theorem stepRandResizable_halted (v : ℕ) (d : RData r) :
    stepRandResizable w advStep p (.halted v d) = pure (.halted v d) := rfl

theorem stepRandResizable_faulted :
    stepRandResizable w advStep p .faulted = pure .faulted := rfl

theorem stepRandResizable_op {o : Op B r} {y : RData r} (hp : p[s.pc]? = some (.op o))
    (he : evalResizable w o s.data = some y) :
    stepRandResizable w advStep p (.running s) = pure (.running ⟨s.pc + 1, y⟩) := by
  simp [stepRandResizable, hp, he]

theorem stepRandResizable_jump {t : ℕ} (hp : p[s.pc]? = some (.jump t)) :
    stepRandResizable w advStep p (.running s) = pure (.running ⟨t, s.data⟩) := by
  simp [stepRandResizable, hp]

theorem stepRandResizable_branch {c : Cond r} {t : ℕ} (hp : p[s.pc]? = some (.branch c t)) :
    stepRandResizable w advStep p (.running s) =
      pure (.running ⟨if c.Holds s.data.toData then t else s.pc + 1, s.data⟩) := by
  simp [stepRandResizable, hp]

theorem stepRandResizable_branch_pos {c : Cond r} {t : ℕ} (hp : p[s.pc]? = some (.branch c t))
    (hc : c.Holds s.data.toData) :
    stepRandResizable w advStep p (.running s) = pure (.running ⟨t, s.data⟩) := by
  rw [stepRandResizable_branch hp]; simp [hc]

theorem stepRandResizable_branch_neg {c : Cond r} {t : ℕ} (hp : p[s.pc]? = some (.branch c t))
    (hc : ¬c.Holds s.data.toData) :
    stepRandResizable w advStep p (.running s) = pure (.running ⟨s.pc + 1, s.data⟩) := by
  rw [stepRandResizable_branch hp]; simp [hc]

theorem stepRandResizable_halt {i : Fin r} (hp : p[s.pc]? = some (.halt i)) :
    stepRandResizable w advStep p (.running s) = pure (.halted (s.data.regs i) s.data) := by
  simp [stepRandResizable, hp]

theorem stepRandResizable_rand_of_fits {dst src : Fin r} (hp : p[s.pc]? = some (.rand dst src))
    (hf : Fits w (s.data.regs src)) :
    stepRandResizable w advStep p (.running s) = (do
      let k ← ProbComp.unifFin (s.data.regs src)
      pure (.running ⟨s.pc + 1, s.data.set dst k.val⟩)) := by
  simp [stepRandResizable, hp, hf]

theorem stepRandResizable_grow_of_fits {dst : Fin r} (hp : p[s.pc]? = some (.grow dst))
    (hf : Fits w (s.data.frontier + 1)) :
    stepRandResizable w advStep p (.running s) =
      pure (.running ⟨s.pc + 1, ⟨Function.update s.data.regs dst s.data.frontier,
        advGrowMem w (advStep s) s.data.frontier 1 s.data.mem, s.data.frontier + 1⟩⟩) := by
  simp [stepRandResizable, hp, hf]

theorem stepRandResizable_grow_of_not_fits {dst : Fin r} (hp : p[s.pc]? = some (.grow dst))
    (hf : ¬Fits w (s.data.frontier + 1)) :
    stepRandResizable w advStep p (.running s) = pure .faulted := by
  simp [stepRandResizable, hp, hf]

theorem stepRandResizable_shrink_of_pos (hp : p[s.pc]? = some .shrink)
    (hk : 1 ≤ s.data.frontier) :
    stepRandResizable w advStep p (.running s) =
      pure (.running ⟨s.pc + 1, ⟨s.data.regs,
        clear s.data.mem (s.data.frontier - 1) 1, s.data.frontier - 1⟩⟩) := by
  simp [stepRandResizable, hp, hk]

theorem stepRandResizable_shrink_of_eq_zero (hp : p[s.pc]? = some .shrink)
    (hk : s.data.frontier = 0) :
    stepRandResizable w advStep p (.running s) = pure .faulted := by
  simp [stepRandResizable, hp, hk]

end StepLemmas

/-- Clocked `t`-step randomized execution of `p : RProgram B r` under adaptive adversary `adv`. -/
def runRandResizable (w : ℕ) (adv : RAdv r) (p : RProgram B r) :
    ℕ → RCfg r → ProbComp (RCfg r)
  | 0, cfg => pure cfg
  | t + 1, cfg => do
    let cfg' ← stepRandResizable w (adv 0) p cfg
    runRandResizable w (adv.shift 1) p t cfg'

@[simp] theorem runRandResizable_zero (w : ℕ) (adv : RAdv r) (p : RProgram B r) (cfg : RCfg r) :
    runRandResizable w adv p 0 cfg = pure cfg := rfl

theorem runRandResizable_succ (w : ℕ) (adv : RAdv r) (p : RProgram B r) (t : ℕ) (cfg : RCfg r) :
    runRandResizable w adv p (t + 1) cfg = (do
      let cfg' ← stepRandResizable w (adv 0) p cfg
      runRandResizable w (adv.shift 1) p t cfg') := rfl

@[simp] theorem runRandResizable_halted (w : ℕ) (adv : RAdv r) (p : RProgram B r) (t v : ℕ)
    (d : RData r) : runRandResizable w adv p t (.halted v d) = pure (.halted v d) := by
  induction t generalizing adv with
  | zero => rfl
  | succ t ih => simp [runRandResizable, stepRandResizable_halted, ih]

@[simp] theorem runRandResizable_faulted (w : ℕ) (adv : RAdv r) (p : RProgram B r) (t : ℕ) :
    runRandResizable w adv p t .faulted = pure .faulted := by
  induction t generalizing adv with
  | zero => rfl
  | succ t ih => simp [runRandResizable, stepRandResizable_faulted, ih]

theorem runRandResizable_add (w : ℕ) (adv : RAdv r) (p : RProgram B r) (t₁ t₂ : ℕ)
    (cfg : RCfg r) :
    runRandResizable w adv p (t₁ + t₂) cfg = (do
      let cfg' ← runRandResizable w adv p t₁ cfg
      runRandResizable w (adv.shift t₁) p t₂ cfg') := by
  induction t₁ generalizing adv cfg with
  | zero => simp [runRandResizable]
  | succ t₁ ih =>
    rw [Nat.succ_add, runRandResizable_succ, runRandResizable_succ, bind_assoc]
    refine congrArg (stepRandResizable w (adv 0) p cfg >>= ·) (funext fun cfg' => ?_)
    rw [ih, RAdv.shift_shift, Nat.add_comm 1 t₁]

/-- Configuration distribution after `t` steps from `.running s` under adaptive adversary `adv`. -/
noncomputable def evalRandDemonic (w : ℕ) (adv : RAdv r) (p : RProgram B r) (t : ℕ)
    (s : RState r) : PMF (RCfg r) :=
  (runRandResizable w adv p t (.running s)).eval

/-- Set of active (`.running`) configurations. -/
def RCfg.runningSet (r : ℕ) : Set (RCfg r) := {cfg | ∃ u, cfg = .running u}

/-- Set of cleanly halted (`.halted`) configurations. -/
def RCfg.haltedSet (r : ℕ) : Set (RCfg r) := {cfg | ∃ v d, cfg = .halted v d}

@[simp] theorem RCfg.mem_runningSet_iff {cfg : RCfg r} :
    cfg ∈ RCfg.runningSet r ↔ ∃ u, cfg = .running u := Iff.rfl

@[simp] theorem RCfg.mem_haltedSet_iff {cfg : RCfg r} :
    cfg ∈ RCfg.haltedSet r ↔ ∃ v d, cfg = .halted v d := Iff.rfl

/-- Pointwise halting probability at `.halted v d` is monotone in the horizon `t`. -/
theorem evalRandDemonic_halted_mono (w : ℕ) (adv : RAdv r) (p : RProgram B r) (s : RState r)
    (v : ℕ) (d : RData r) :
    Monotone fun t => evalRandDemonic w adv p t s (.halted v d) := by
  refine monotone_nat_of_le_succ fun t => ?_
  have hstep : evalRandDemonic w adv p (t + 1) s = (evalRandDemonic w adv p t s).bind
      fun cfg => (stepRandResizable w ((adv.shift t) 0) p cfg).eval := by
    simp only [evalRandDemonic, runRandResizable_add w adv p t 1, ProbComp.eval_bind,
      runRandResizable_succ, runRandResizable_zero, bind_pure]
  rw [hstep, PMF.bind_apply]
  refine le_of_eq_of_le ?_ (le_tsum (f := fun cfg => evalRandDemonic w adv p t s cfg *
    (stepRandResizable w ((adv.shift t) 0) p cfg).eval (.halted v d)) (.halted v d))
  simp [stepRandResizable_halted]

/-- Any deterministic transition `stepRandResizable w (adv 0) p (.running s) = pure (.running s')`
transports supremum halting probabilities from `(adv.shift 1, s')` to `(adv, s)`. -/
theorem iSup_evalRandDemonic_halted_le_of_step {w : ℕ} {adv : RAdv r} {p : RProgram B r}
    {s s' : RState r}
    (hstep : stepRandResizable w (adv 0) p (.running s) = pure (.running s'))
    (v : ℕ) (d : RData r) :
    (⨆ T_hor : ℕ, evalRandDemonic w (adv.shift 1) p T_hor s' (.halted v d)) ≤
      ⨆ T_hor : ℕ, evalRandDemonic w adv p T_hor s (.halted v d) := by
  refine iSup_le fun T_hor => le_iSup_of_le (T_hor + 1) ?_
  simp [evalRandDemonic, runRandResizable_succ, hstep]

/-! ## Fault-freedom, `PeakFrontierLe`, expected time, and `ExecRProgramDist` -/

/-- Configuration hardware-frontier upper bound (`≤ L_peak`). -/
def RCfg.FrontierLe (L_peak : ℕ) : RCfg r → Prop
  | .running s => s.data.frontier ≤ L_peak
  | .halted _ d => d.frontier ≤ L_peak
  | .faulted => True

/-- Joint non-faulting and frontier-bounded configuration invariant. -/
def RCfg.SafeBounded (L_peak : ℕ) : RCfg r → Prop
  | .running s => s.data.frontier ≤ L_peak
  | .halted _ d => d.frontier ≤ L_peak
  | .faulted => False

theorem RCfg.SafeBounded.ne_faulted {L_peak : ℕ} {cfg : RCfg r} (h : cfg.SafeBounded L_peak) :
    cfg ≠ .faulted := by
  rintro rfl; exact h

theorem RCfg.SafeBounded.frontierLe {L_peak : ℕ} {cfg : RCfg r} (h : cfg.SafeBounded L_peak) :
    cfg.FrontierLe L_peak := by
  cases cfg with
  | running _ | halted _ _ => exact h
  | faulted => exact h.elim

theorem RCfg.SafeBounded.mono {L₁ L₂ : ℕ} {cfg : RCfg r} (hL : L₁ ≤ L₂)
    (h : cfg.SafeBounded L₁) : cfg.SafeBounded L₂ := by
  cases cfg with
  | running _ | halted _ _ => exact h.trans hL
  | faulted => exact h

/-- Zero-fault invariant across all adaptive adversaries `adv : RAdv r` and all horizons `t : ℕ`. -/
def RDemonicFaultFree (w : ℕ) (p : RProgram B r) (s : RState r) : Prop :=
  ∀ (adv : RAdv r) (t : ℕ), evalRandDemonic w adv p t s .faulted = 0

/-- Every-step peak hardware-frontier bound: across every adaptive adversary `adv : RAdv r`, every
horizon `t : ℕ`, and every reachable configuration `cfg` (`.running` or `.halted`), the active
hardware word frontier never exceeds `L_peak`. -/
def PeakFrontierLe (w L_peak : ℕ) (p : RProgram B r) (s : RState r) : Prop :=
  ∀ (adv : RAdv r) (t : ℕ) (cfg : RCfg r),
    cfg ∈ (evalRandDemonic w adv p t s).support → cfg.FrontierLe L_peak

theorem PeakFrontierLe.mono {w L₁ L₂ : ℕ} {p : RProgram B r} {s : RState r}
    (hL : L₁ ≤ L₂) (h : PeakFrontierLe w L₁ p s) : PeakFrontierLe w L₂ p s := by
  intro adv t cfg hcfg
  cases cfg with
  | running _ | halted _ _ => exact (h adv t _ hcfg).trans hL
  | faulted => trivial

/-- Almost-sure halting across all adaptive adversaries `adv : RAdv r`. -/
def AlmostSurelyHaltsDemonic (w : ℕ) (p : RProgram B r) (s : RState r) : Prop :=
  RDemonicFaultFree w p s ∧
    ∀ adv : RAdv r, (⨆ t : ℕ, (evalRandDemonic w adv p t s).toOuterMeasure (RCfg.haltedSet r)) = 1

/-- Finite-horizon expected active steps under a fixed adaptive adversary `adv`. -/
noncomputable def expectedStepsWithinAdv (w : ℕ) (adv : RAdv r) (p : RProgram B r) (N : ℕ)
    (cfg : RCfg r) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range N,
    (runRandResizable w adv p t cfg).eval.toOuterMeasure (RCfg.runningSet r)

/-- Supremum finite-horizon expected active steps across all adaptive adversaries `adv`. -/
noncomputable def supExpectedStepsWithin (w : ℕ) (p : RProgram B r) (N : ℕ) (cfg : RCfg r) :
    ℝ≥0∞ :=
  ⨆ adv : RAdv r, expectedStepsWithinAdv w adv p N cfg

/-- Expected remaining active steps from `cfg` under a fixed adaptive adversary `adv`. -/
noncomputable def expectedStepsFromAdv (w : ℕ) (adv : RAdv r) (p : RProgram B r) (cfg : RCfg r) :
    ℝ≥0∞ :=
  ∑' t : ℕ, (runRandResizable w adv p t cfg).eval.toOuterMeasure (RCfg.runningSet r)

/-- Supremum expected remaining active steps from `cfg` across all adaptive adversaries `adv`. -/
noncomputable def expectedStepsFromDemonic (w : ℕ) (p : RProgram B r) (cfg : RCfg r) : ℝ≥0∞ :=
  ⨆ adv : RAdv r, expectedStepsFromAdv w adv p cfg

/-- Worst-case adaptive-adversary expected running time of `p` from `s` at word width `w`. -/
noncomputable def expectedTimeDemonic (w : ℕ) (p : RProgram B r) (s : RState r) : ℝ≥0∞ :=
  expectedStepsFromDemonic w p (.running s)

@[simp] theorem expectedStepsWithinAdv_zero (w : ℕ) (adv : RAdv r) (p : RProgram B r)
    (cfg : RCfg r) : expectedStepsWithinAdv w adv p 0 cfg = 0 := by
  simp [expectedStepsWithinAdv]

@[simp] theorem supExpectedStepsWithin_zero (w : ℕ) (p : RProgram B r) (cfg : RCfg r) :
    supExpectedStepsWithin w p 0 cfg = 0 := by
  simp [supExpectedStepsWithin]

@[simp] theorem expectedStepsFromAdv_halted (w : ℕ) (adv : RAdv r) (p : RProgram B r) (v : ℕ)
    (d : RData r) : expectedStepsFromAdv w adv p (.halted v d) = 0 := by
  simp [expectedStepsFromAdv, RCfg.runningSet, PMF.toOuterMeasure_pure_apply]

@[simp] theorem expectedStepsFromDemonic_halted (w : ℕ) (p : RProgram B r) (v : ℕ) (d : RData r) :
    expectedStepsFromDemonic w p (.halted v d) = 0 := by
  simp [expectedStepsFromDemonic]

theorem expectedStepsWithinAdv_mono (w : ℕ) (adv : RAdv r) (p : RProgram B r) (cfg : RCfg r) :
    Monotone fun N => expectedStepsWithinAdv w adv p N cfg :=
  fun _ _ hN => Finset.sum_le_sum_of_subset (Finset.range_mono hN)

theorem supExpectedStepsWithin_mono (w : ℕ) (p : RProgram B r) (cfg : RCfg r) :
    Monotone fun N => supExpectedStepsWithin w p N cfg :=
  fun _ _ hN => iSup_mono fun adv => expectedStepsWithinAdv_mono w adv p cfg hN

theorem iSup_supExpectedStepsWithin (w : ℕ) (p : RProgram B r) (cfg : RCfg r) :
    (⨆ N : ℕ, supExpectedStepsWithin w p N cfg) = expectedStepsFromDemonic w p cfg := by
  simp only [supExpectedStepsWithin, expectedStepsFromDemonic, expectedStepsFromAdv]
  rw [iSup_comm]
  exact iSup_congr fun adv => ENNReal.tsum_eq_iSup_nat.symm

theorem supExpectedStepsWithin_le_expectedStepsFromDemonic (w : ℕ) (p : RProgram B r) (N : ℕ)
    (cfg : RCfg r) :
    supExpectedStepsWithin w p N cfg ≤ expectedStepsFromDemonic w p cfg :=
  iSup_supExpectedStepsWithin w p cfg ▸ le_iSup (fun K => supExpectedStepsWithin w p K cfg) N

/-- 1-step Bellman equation for `expectedStepsWithinAdv`. -/
theorem expectedStepsWithinAdv_running_succ (w : ℕ) (adv : RAdv r) (p : RProgram B r) (N : ℕ)
    (s : RState r) :
    expectedStepsWithinAdv w adv p (N + 1) (.running s) =
      1 + ProbComp.expect (stepRandResizable w (adv 0) p (.running s))
        (expectedStepsWithinAdv w (adv.shift 1) p N) := by
  rw [expectedStepsWithinAdv, Finset.sum_range_succ', add_comm]
  simp only [runRandResizable_zero, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply,
    show RCfg.running s ∈ RCfg.runningSet r from ⟨s, rfl⟩, ↓reduceIte,
    runRandResizable_succ, ProbComp.eval_bind, PMF.toOuterMeasure_bind_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
  simp only [ProbComp.expect, expectedStepsWithinAdv, Finset.mul_sum]

theorem expectedStepsWithinAdv_running_le (w : ℕ) (adv : RAdv r) (p : RProgram B r) (N : ℕ)
    (s : RState r) :
    expectedStepsWithinAdv w adv p N (.running s) ≤
      1 + ProbComp.expect (stepRandResizable w (adv 0) p (.running s))
        (supExpectedStepsWithin w p N) := by
  cases N with
  | zero => simp
  | succ N =>
    rw [expectedStepsWithinAdv_running_succ]
    refine add_le_add le_rfl (ProbComp.expect_mono fun cfg => ?_)
    exact (expectedStepsWithinAdv_mono w (adv.shift 1) p cfg (Nat.le_succ N)).trans
      (le_iSup (fun adv' => expectedStepsWithinAdv w adv' p (N + 1) cfg) (adv.shift 1))

theorem expectedStepsFromAdv_running (w : ℕ) (adv : RAdv r) (p : RProgram B r) (s : RState r) :
    expectedStepsFromAdv w adv p (.running s) =
      1 + ProbComp.expect (stepRandResizable w (adv 0) p (.running s))
        (expectedStepsFromAdv w (adv.shift 1) p) := by
  rw [expectedStepsFromAdv, tsum_eq_zero_add' CompleteLattice.summable]
  simp only [runRandResizable_zero, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply,
    show RCfg.running s ∈ RCfg.runningSet r from ⟨s, rfl⟩, ↓reduceIte,
    runRandResizable_succ, ProbComp.eval_bind, PMF.toOuterMeasure_bind_apply,
    ProbComp.expect, expectedStepsFromAdv]
  rw [tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

/-- **Flat Resizable Word RAM Distributional Execution (`ExecRProgramDist`).**
Starting at `⟨0, x⟩` at word width `w`, `p : RProgram B r` with output register `out : Fin r`:
1. never faults under any adaptive adversary (`RDemonicFaultFree`),
2. keeps the active hardware frontier `≤ L_peak` at every step (`PeakFrontierLe`),
3. runs in at most `T` expected instructions (`expectedTimeDemonic w p ⟨0, x⟩ ≤ T`), and
4. reaches halting distribution `μ : PMF (RData r)` across every adaptive adversary `adv`. -/
structure ExecRProgramDist (w : ℕ) (p : RProgram B r) (out : Fin r) (x : RData r)
    (μ : PMF (RData r)) (T : ℝ≥0∞) (L_peak : ℕ) : Prop where
  /-- Zero faults across all adaptive adversaries and horizons. -/
  faultFree : RDemonicFaultFree w p ⟨0, x⟩
  /-- Hardware frontier stays `≤ L_peak` across all adaptive adversaries and horizons. -/
  peakFrontierLe : PeakFrontierLe w L_peak p ⟨0, x⟩
  /-- Supremum expected step count is at most `T`. -/
  expectedTime_le : expectedTimeDemonic w p ⟨0, x⟩ ≤ T
  /-- Every state `y` is reached at `.halted (y.regs out) y` with probability at least `μ y`. -/
  halted_le : ∀ (adv : RAdv r) (y : RData r),
    μ y ≤ ⨆ t : ℕ, evalRandDemonic w adv p t ⟨0, x⟩ (.halted (y.regs out) y)

/-- The halted part of the configuration law only grows with the clock. -/
private theorem indicator_haltedSet_evalRandDemonic_mono (w : ℕ) (adv : RAdv r)
    (p : RProgram B r) (s : RState r) (cfg : RCfg r) :
    Monotone fun t => Set.indicator (RCfg.haltedSet r) (evalRandDemonic w adv p t s) cfg := by
  intro t₁ t₂ ht
  by_cases hmem : cfg ∈ RCfg.haltedSet r
  · obtain ⟨v, d, rfl⟩ := hmem
    simpa [Set.indicator_of_mem (RCfg.mem_haltedSet_iff.mpr ⟨v, d, rfl⟩)] using
      evalRandDemonic_halted_mono w adv p s v d ht
  · simp [Set.indicator_of_notMem hmem]

/-- The sum of limiting halting probabilities over states is bounded by the total halted mass. -/
private theorem tsum_iSup_halted_le (w : ℕ) (adv : RAdv r) (p : RProgram B r) (out : Fin r)
    (x : RData r) :
    (∑' y : RData r, ⨆ t : ℕ, evalRandDemonic w adv p t ⟨0, x⟩ (.halted (y.regs out) y)) ≤
      ⨆ t : ℕ, (evalRandDemonic w adv p t ⟨0, x⟩).toOuterMeasure (RCfg.haltedSet r) := by
  classical
  let emb : RData r → RCfg r := fun y => .halted (y.regs out) y
  have hemb : Function.Injective emb := fun _ _ h => by injection h
  simp_rw [PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_iSup_of_monotone (indicator_haltedSet_evalRandDemonic_mono w adv p ⟨0, x⟩)]
  have hmem : ∀ y : RData r, emb y ∈ RCfg.haltedSet r := fun y => ⟨y.regs out, y, rfl⟩
  exact (tsum_congr fun y => iSup_congr fun t =>
    (Set.indicator_of_mem (hmem y) _).symm).trans_le
    (tsum_comp_le_tsum_of_injective hemb fun c =>
      ⨆ t : ℕ, Set.indicator (RCfg.haltedSet r) (evalRandDemonic w adv p t ⟨0, x⟩) c)

namespace ExecRProgramDist

theorem mono {w L₁ L₂ : ℕ} {p : RProgram B r} {out : Fin r} {x : RData r}
    {μ : PMF (RData r)} {T₁ T₂ : ℝ≥0∞}
    (h : ExecRProgramDist w p out x μ T₁ L₁) (hT : T₁ ≤ T₂) (hL : L₁ ≤ L₂) :
    ExecRProgramDist w p out x μ T₂ L₂ :=
  ⟨h.faultFree, h.peakFrontierLe.mono hL, h.expectedTime_le.trans hT, h.halted_le⟩

/-- `ExecRProgramDist` implies `AlmostSurelyHaltsDemonic` and pins the exact limiting halting
probability of every `y : RData r` to `μ y` under every adaptive adversary `adv : RAdv r`. -/
theorem iSup_evalRandDemonic_halted_eq {w L_peak : ℕ} {p : RProgram B r} {out : Fin r}
    {x : RData r} {μ : PMF (RData r)} {T : ℝ≥0∞}
    (h : ExecRProgramDist w p out x μ T L_peak) (adv : RAdv r) (y₀ : RData r) :
    (⨆ t : ℕ, evalRandDemonic w adv p t ⟨0, x⟩ (.halted (y₀.regs out) y₀)) = μ y₀ := by
  classical
  let f : RData r → ℝ≥0∞ := fun y => ⨆ t, evalRandDemonic w adv p t ⟨0, x⟩ (.halted (y.regs out) y)
  have htsum_f : ∑' y, f y ≤ 1 := (tsum_iSup_halted_le w adv p out x).trans
    (iSup_le fun _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
  refine le_antisymm ?_ (h.halted_le adv y₀)
  have hμ : μ y₀ + (∑' y, if y = y₀ then (0 : ℝ≥0∞) else μ y) = 1 :=
    (tsum_eq_add_tsum_ite (f := μ) y₀).symm.trans μ.tsum_coe
  have hrest : (∑' y, if y = y₀ then (0 : ℝ≥0∞) else μ y) ≤ ∑' y, if y = y₀ then 0 else f y :=
    tsum_le_tsum fun y => by split_ifs <;> [exact le_rfl; exact h.halted_le adv y]
  exact (ENNReal.add_le_add_iff_right
    (ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq hμ))).mp
    ((add_le_add le_rfl hrest).trans ((tsum_eq_add_tsum_ite y₀).symm.trans_le htsum_f |>.trans_eq
      hμ.symm))

/-- Every `ExecRProgramDist` halts almost surely under every adaptive adversary. -/
theorem almostSurelyHaltsDemonic {w L_peak : ℕ} {p : RProgram B r} {out : Fin r}
    {x : RData r} {μ : PMF (RData r)} {T : ℝ≥0∞}
    (h : ExecRProgramDist w p out x μ T L_peak) :
    AlmostSurelyHaltsDemonic w p ⟨0, x⟩ :=
  ⟨h.faultFree, fun adv => le_antisymm
    (iSup_le fun _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
    (μ.tsum_coe ▸ (tsum_le_tsum (h.halted_le adv)).trans (tsum_iSup_halted_le w adv p out x))⟩

end ExecRProgramDist

/-- **Soundness Check (`not_execRProgramDist_halt`).**
A 1-instruction `[.halt out]` stub cannot satisfy `ExecRProgramDist` for any target distribution
`μ` whose support contains a state `y ≠ x`. -/
theorem not_execRProgramDist_halt {w L_peak : ℕ} {out : Fin r} {x y : RData r}
    {μ : PMF (RData r)} {T : ℝ≥0∞} (hy : y ∈ μ.support) (hne : y ≠ x) :
    ¬ExecRProgramDist (B := B) w [.halt out] out x μ T L_peak := by
  intro h
  have hzero : (⨆ t : ℕ, evalRandDemonic (B := B) w (fun _ _ _ => 0) [.halt out] t ⟨0, x⟩
      (.halted (y.regs out) y)) ≤ 0 := iSup_le fun t => le_of_eq <| by
    cases t with
    | zero => simp [evalRandDemonic, PMF.pure_apply]
    | succ =>
      rw [evalRandDemonic, runRandResizable_succ, stepRandResizable_halt (s := ⟨0, x⟩) rfl,
        pure_bind, runRandResizable_halted, ProbComp.eval_pure]
      exact PMF.pure_apply_of_ne _ _ fun heq => hne (by injection heq)
  exact (PMF.mem_support_iff _ _).mp hy
    (nonpos_iff_eq_zero.mp ((h.halted_le (fun _ _ _ => 0) y).trans hzero))

/-- Every `evalResizable` step leaves the hardware word frontier unchanged. -/
theorem evalResizable_frontier_eq {w : ℕ} {o : Op B r} {x y : RData r}
    (he : evalResizable w o x = some y) : y.frontier = x.frontier := by
  cases o with
  | copy _ _ => cases he; rfl
  | alu _ _ _ =>
    obtain ⟨_, _, hput⟩ := Option.bind_eq_some_iff.mp he
    simp only [RData.put] at hput; split_ifs at hput; cases hput; rfl
  | const _ _ | load _ _ | store _ _ =>
    simp only [evalResizable, RData.put] at he; split_ifs at he; cases he; rfl

/-- Every `RDemonicExec w L_peak c x n P` witnesses at least one reachable post-state `y`
satisfying `P y` and `y.frontier ≤ L_peak`. -/
theorem RDemonicExec.exists_post_frontier_le {w L_peak n : ℕ} {c : RCode B r} {x : RData r}
    {P : RData r → Prop} (h : RDemonicExec w L_peak c x n P) :
    ∃ y, P y ∧ y.frontier ≤ L_peak := by
  induction h with
  | op hL he hp => exact ⟨_, hp, (evalResizable_frontier_eq he).trans_le hL⟩
  | @grow dst x P hL _ hp =>
    exact ⟨_, hp _ (demonicGrow_advGrowMem w (fun _ => 0) x.frontier 1 x.mem), hL⟩
  | shrink hL _ hp => exact ⟨_, hp, Nat.sub_le _ _ |>.trans hL⟩
  | rand hL _ hp => exact ⟨_, hp 0 (Nat.zero_le _), hL⟩
  | seq _ _ ih₁ ih₂ | loop_iter _ _ _ ih₁ ih₂ => exact ih₁.elim fun y₁ h => ih₂ y₁ h.1
  | branch_pos _ _ ih | branch_neg _ _ ih => exact ih
  | loop_exit hL _ hp => exact ⟨_, hp, hL⟩
  | mono _ _ hPQ ih => exact ih.imp fun y h => ⟨hPQ y h.1, h.2⟩


/-! ## Compilation of `RDemonicExec` and `ExecRCodeDist` to flat `RProgram` -/

/-- Horizon-bounded non-faulting and `≤ L_peak` frontier invariant on `evalRandDemonic`. -/
def DemonicSafeWithin (w L_peak T_hor : ℕ) (p : RProgram B r) (s : RState r) : Prop :=
  ∀ (adv : RAdv r), ∀ t ≤ T_hor, ∀ cfg ∈ (evalRandDemonic w adv p t s).support,
    cfg.SafeBounded L_peak

theorem DemonicSafeWithin.anti {w L_peak T₁ T₂ : ℕ} {p : RProgram B r} {s : RState r}
    (hT : T₁ ≤ T₂) (h : DemonicSafeWithin w L_peak T₂ p s) :
    DemonicSafeWithin w L_peak T₁ p s :=
  fun adv t ht => h adv t (ht.trans hT)

theorem DemonicSafeWithin.mono_peak {w L₁ L₂ T_hor : ℕ} {p : RProgram B r} {s : RState r}
    (hL : L₁ ≤ L₂) (h : DemonicSafeWithin w L₁ T_hor p s) :
    DemonicSafeWithin w L₂ T_hor p s :=
  fun adv t ht cfg hcfg => (h adv t ht cfg hcfg).mono hL

theorem DemonicSafeWithin.frontier_le {w L_peak T_hor : ℕ} {p : RProgram B r} {s : RState r}
    (h : DemonicSafeWithin w L_peak T_hor p s) : s.data.frontier ≤ L_peak :=
  h (fun _ _ _ => 0) 0 (Nat.zero_le _) (.running s) (by simp [evalRandDemonic])

theorem demonicSafeWithin_of_pure {w L_peak T_hor : ℕ} {p : RProgram B r}
    {s : RState r} {s' : (RState r → ℕ → ℕ) → RState r} (hfr : s.data.frontier ≤ L_peak)
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running (s' f)))
    (hnext : ∀ f k, k + 1 ≤ T_hor → DemonicSafeWithin w L_peak k p (s' f)) :
    DemonicSafeWithin w L_peak T_hor p s := by
  rintro adv (_ | k) ht cfg hcfg
  · exact (by simpa [evalRandDemonic] using hcfg : cfg = .running s) ▸ hfr
  · rw [evalRandDemonic, runRandResizable_succ, hstep (adv 0), pure_bind] at hcfg
    exact hnext (adv 0) k ht (adv.shift 1) k le_rfl cfg hcfg

theorem demonicSafeWithin_of_rand {w L_peak T_hor : ℕ} {p : RProgram B r}
    {pc : ℕ} {x : RData r} {dst src : Fin r} (hfr : x.frontier ≤ L_peak)
    (hp : p[pc]? = some (.rand dst src)) (hfit : Fits w (x.regs src))
    (hnext : ∀ (j : Fin (x.regs src + 1)) (k : ℕ), k + 1 ≤ T_hor →
      DemonicSafeWithin w L_peak k p ⟨pc + 1, x.set dst j.val⟩) :
    DemonicSafeWithin w L_peak T_hor p ⟨pc, x⟩ := by
  rintro adv (_ | k) ht cfg hcfg
  · exact (by simpa [evalRandDemonic] using hcfg : cfg = .running ⟨pc, x⟩) ▸ hfr
  · rw [evalRandDemonic, runRandResizable_succ,
      stepRandResizable_rand_of_fits (s := ⟨pc, x⟩) hp hfit, bind_assoc, ProbComp.eval_bind,
      PMF.mem_support_bind_iff] at hcfg
    obtain ⟨j, _, hcfg'⟩ := hcfg
    exact hnext j k ht (adv.shift 1) k le_rfl cfg (by rwa [pure_bind] at hcfg')

theorem supExpectedStepsWithin_le_of_pure {w N : ℕ} {p : RProgram B r}
    {s : RState r} {s' : (RState r → ℕ → ℕ) → RState r}
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running (s' f))) :
    supExpectedStepsWithin w p N (.running s) ≤
      1 + ⨆ f, supExpectedStepsWithin w p N (.running (s' f)) := by
  refine iSup_le fun adv => (expectedStepsWithinAdv_running_le w adv p N s).trans ?_
  rw [hstep (adv 0), ProbComp.expect_pure]
  exact add_le_add le_rfl
    (le_iSup (fun f => supExpectedStepsWithin w p N (.running (s' f))) (adv 0))

theorem supExpectedStepsWithin_le_of_const {w N : ℕ} {p : RProgram B r}
    {s s₁ : RState r}
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running s₁)) :
    supExpectedStepsWithin w p N (.running s) ≤
      1 + supExpectedStepsWithin w p N (.running s₁) :=
  (supExpectedStepsWithin_le_of_pure hstep).trans (add_le_add le_rfl (iSup_le fun _ => le_rfl))

/-- Worst-case-adversary supremum halting probability at `.halted v d` from `⟨pc, y⟩`. -/
noncomputable def haltedReach (w : ℕ) (p : RProgram B r) (v : ℕ) (d : RData r)
    (pc : ℕ) (y : RData r) : ℝ≥0∞ :=
  ⨅ adv : RAdv r, ⨆ T_hor : ℕ, evalRandDemonic w adv p T_hor ⟨pc, y⟩ (.halted v d)

theorem haltedReach_le_of_pure {w v : ℕ} {p : RProgram B r} {d : RData r}
    {s : RState r} {s' : (RState r → ℕ → ℕ) → RState r}
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running (s' f))) :
    (⨅ f, haltedReach w p v d (s' f).pc (s' f).data) ≤ haltedReach w p v d s.pc s.data := by
  refine le_iInf fun adv => (iInf_le _ (adv 0)).trans ((iInf_le _ (adv.shift 1)).trans ?_)
  exact iSup_evalRandDemonic_halted_le_of_step (hstep (adv 0)) v d

theorem haltedReach_le_of_const {w v : ℕ} {p : RProgram B r} {d : RData r}
    {s s₁ : RState r}
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running s₁)) :
    haltedReach w p v d s₁.pc s₁.data ≤ haltedReach w p v d s.pc s.data :=
  (le_iInf fun _ => le_rfl).trans (haltedReach_le_of_pure hstep)

theorem haltedReach_le_of_rand {w v pc : ℕ} {p : RProgram B r} {d x : RData r}
    {dst src : Fin r} (hp : p[pc]? = some (.rand dst src)) (hfit : Fits w (x.regs src)) :
    (∑' k : Fin (x.regs src + 1), (ProbComp.unifFin (x.regs src)).eval k *
      haltedReach w p v d (pc + 1) (x.set dst k.val)) ≤
      haltedReach w p v d pc x := by
  refine le_iInf fun adv => ?_
  have hstep_sum : ∀ T_hor : ℕ,
      (∑' k : Fin (x.regs src + 1), (ProbComp.unifFin (x.regs src)).eval k *
        evalRandDemonic w (adv.shift 1) p T_hor ⟨pc + 1, x.set dst k.val⟩ (.halted v d)) =
        evalRandDemonic w adv p (T_hor + 1) ⟨pc, x⟩ (.halted v d) := fun T_hor => by
    simp only [evalRandDemonic, runRandResizable_succ,
      stepRandResizable_rand_of_fits (s := ⟨pc, x⟩) hp hfit, bind_assoc, pure_bind,
      ProbComp.eval_bind, PMF.bind_apply]
  calc
    (∑' k, (ProbComp.unifFin (x.regs src)).eval k *
        haltedReach w p v d (pc + 1) (x.set dst k.val))
      ≤ ∑' k, (ProbComp.unifFin (x.regs src)).eval k *
          ⨆ T_hor : ℕ, evalRandDemonic w (adv.shift 1) p T_hor
            ⟨pc + 1, x.set dst k.val⟩ (.halted v d) :=
        tsum_le_tsum fun k => mul_le_mul_right (iInf_le _ (adv.shift 1)) _
    _ = ⨆ T_hor : ℕ, ∑' k, (ProbComp.unifFin (x.regs src)).eval k *
          evalRandDemonic w (adv.shift 1) p T_hor ⟨pc + 1, x.set dst k.val⟩ (.halted v d) := by
        simp_rw [ENNReal.mul_iSup]
        exact ENNReal.tsum_iSup_of_monotone fun k _ _ hT =>
          mul_le_mul_right (evalRandDemonic_halted_mono w (adv.shift 1) p _ v d hT) _
    _ = ⨆ T_hor : ℕ, evalRandDemonic w adv p (T_hor + 1) ⟨pc, x⟩ (.halted v d) := by
        simp_rw [hstep_sum]
    _ ≤ ⨆ T_hor : ℕ, evalRandDemonic w adv p T_hor ⟨pc, x⟩ (.halted v d) :=
        iSup_le fun T_hor => le_iSup
          (fun t => evalRandDemonic w adv p t ⟨pc, x⟩ (.halted v d)) (T_hor + 1)

theorem RDemonicExec.supExpectedStepsWithin_assemble {w L_peak n pc N : ℕ} {c : RCode B r}
    {x : RData r} {P : RData r → Prop} (h : RDemonicExec w L_peak c x n P) {p : RProgram B r}
    (hp : p.Contains pc (c.assemble pc)) :
    supExpectedStepsWithin w p N (.running ⟨pc, x⟩) ≤
      (n : ℝ≥0∞) + ⨆ (y : RData r) (_ : P y),
        supExpectedStepsWithin w p N (.running ⟨pc + c.size, y⟩) := by
  induction h generalizing pc with
  | @op o x y P _ he hp_y =>
    exact (supExpectedStepsWithin_le_of_const fun _ => stepRandResizable_op hp.head he).trans
      (add_le_add (by simp) (le_iSup₂_of_le y hp_y le_rfl))
  | @grow dst x P _ hfit hp_y =>
    refine (supExpectedStepsWithin_le_of_pure fun _ =>
      stepRandResizable_grow_of_fits hp.head hfit).trans (add_le_add (by simp) ?_)
    exact iSup_le fun f =>
      le_iSup₂_of_le _ (hp_y _ (demonicGrow_advGrowMem w (f ⟨pc, x⟩) _ _ _)) le_rfl
  | @shrink x P _ hk hp_y =>
    exact (supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_shrink_of_pos hp.head hk).trans
        (add_le_add (by simp) (le_iSup₂_of_le _ hp_y le_rfl))
  | @rand dst src x P _ hfit hp_y =>
    refine iSup_le fun adv => (expectedStepsWithinAdv_running_le w adv p N ⟨pc, x⟩).trans ?_
    rw [stepRandResizable_rand_of_fits hp.head hfit, ProbComp.expect_bind]
    simp only [ProbComp.expect_pure, RCode.size, Nat.cast_one]
    exact add_le_add le_rfl ((ProbComp.expect_mono (g := fun _ =>
      ⨆ (y : RData r) (_ : P y), supExpectedStepsWithin w p N (.running ⟨pc + 1, y⟩))
      fun k : Fin (x.regs src + 1) =>
        le_iSup₂_of_le (x.set dst k.val) (hp_y k.val k.is_le) le_rfl).trans_eq
      (ProbComp.expect_const _ _))
  | @seq c₁ c₂ x T₁ T₂ Q P _ _ ih₁ ih₂ =>
    refine (ih₁ hp.append_left).trans ?_
    rw [Nat.cast_add, add_assoc]
    refine add_le_add le_rfl (iSup₂_le fun y₁ hy₁ => (ih₂ y₁ hy₁ hp.seq_right).trans ?_)
    simp only [RCode.size, Nat.add_assoc, le_rfl]
  | @branch_pos c pos neg x T P hc _ ih =>
    refine (supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_pos hp.branch_head hc).trans ?_
    refine (add_le_add le_rfl (ih hp.branch_pos)).trans_eq ?_
    rw [Nat.cast_add, Nat.cast_one, show pc + neg.size + 2 + pos.size =
      pc + (RCode.branch c pos neg).size by simp only [RCode.size]; omega, add_left_comm, add_assoc]
  | @branch_neg c pos neg x T P hc _ ih =>
    refine (supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_neg hp.branch_head hc).trans ?_
    refine (add_le_add le_rfl ((ih hp.branch_neg).trans (add_le_add le_rfl (iSup₂_le fun y hy =>
      (supExpectedStepsWithin_le_of_const fun _ =>
        stepRandResizable_jump hp.branch_jump).trans (add_le_add le_rfl
          (le_iSup₂_of_le y hy le_rfl)))))).trans_eq ?_
    rw [show pc + neg.size + pos.size + 2 = pc + (RCode.branch c pos neg).size by
      simp only [RCode.size]; omega, Nat.cast_add, Nat.cast_ofNat, ← one_add_one_eq_two]
    ac_rfl
  | @loop_exit c body x P _ hc hp_y =>
    refine (supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_neg hp.head hc).trans ?_
    refine (add_le_add le_rfl (supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_jump hp.loop_exit)).trans ?_
    rw [← add_assoc, one_add_one_eq_two, show pc + body.size + 3 = pc + (RCode.loop c body).size
      by simp only [RCode.size]; omega]
    exact add_le_add (by simp) (le_iSup₂_of_le x hp_y le_rfl)
  | @loop_iter c body x T₁ T₂ Q P hc _ _ ihb ihl =>
    refine (supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_pos hp.head hc).trans ?_
    refine (add_le_add le_rfl ((ihb hp.loop_body).trans (add_le_add le_rfl (iSup₂_le fun y hy =>
      (supExpectedStepsWithin_le_of_const fun _ => stepRandResizable_jump hp.loop_back).trans
        (add_le_add le_rfl (ihl y hy hp)))))).trans_eq ?_
    simp only [Nat.cast_add, Nat.cast_one, ← one_add_one_eq_two]
    ac_rfl
  | mono _ hT hPQ ih =>
    exact (ih hp).trans (add_le_add (Nat.cast_le.mpr hT)
      (iSup₂_le fun y hy => le_iSup₂_of_le y (hPQ y hy) le_rfl))

theorem RDemonicExec.demonicSafeWithin_assemble {w L_peak n pc T_hor : ℕ} {c : RCode B r}
    {x : RData r} {P : RData r → Prop} (h : RDemonicExec w L_peak c x n P) {p : RProgram B r}
    (hp : p.Contains pc (c.assemble pc))
    (hcont : ∀ y, P y → DemonicSafeWithin w L_peak T_hor p ⟨pc + c.size, y⟩) :
    DemonicSafeWithin w L_peak T_hor p ⟨pc, x⟩ := by
  induction h generalizing pc T_hor with
  | @op o x y P hL he hp_y =>
    exact demonicSafeWithin_of_pure hL (fun _ => stepRandResizable_op hp.head he)
      fun _ _ _ => (hcont y hp_y).anti (by omega)
  | @grow dst x P hL hfit hp_y =>
    exact demonicSafeWithin_of_pure (s := ⟨pc, x⟩) (by dsimp only; omega)
      (fun _ => stepRandResizable_grow_of_fits hp.head hfit) fun f _ _ =>
        (hcont _ (hp_y _ (demonicGrow_advGrowMem w (f ⟨pc, x⟩) _ _ _))).anti (by omega)
  | @shrink x P hL hk hp_y =>
    exact demonicSafeWithin_of_pure hL (fun _ => stepRandResizable_shrink_of_pos hp.head hk)
      fun _ _ _ => (hcont _ hp_y).anti (by omega)
  | @rand dst src x P hL hfit hp_y =>
    exact demonicSafeWithin_of_rand hL hp.head hfit fun j _ _ =>
      (hcont _ (hp_y j.val j.is_le)).anti (by omega)
  | @seq c₁ c₂ _ _ _ _ _ _ _ ih₁ ih₂ =>
    exact ih₁ hp.append_left fun y₁ hy₁ => ih₂ y₁ hy₁ hp.seq_right fun y₂ hy₂ => by
      simpa [RCode.size, Nat.add_assoc] using hcont y₂ hy₂
  | @branch_pos _ pos neg _ _ _ hc hpos ih =>
    refine demonicSafeWithin_of_pure hpos.frontier_le
      (fun _ => stepRandResizable_branch_pos hp.branch_head hc) fun _ _ _ =>
      ih hp.branch_pos fun y hy => ?_
    simpa [RCode.size, show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
      using (hcont y hy).anti (by omega)
  | @branch_neg _ pos neg _ _ _ hc hneg ih =>
    refine demonicSafeWithin_of_pure hneg.frontier_le
      (fun _ => stepRandResizable_branch_neg hp.branch_head hc) fun _ _ _ =>
      ih hp.branch_neg fun y hy =>
        demonicSafeWithin_of_pure (hcont y hy).frontier_le
          (fun _ => stepRandResizable_jump hp.branch_jump) fun _ _ _ => ?_
    simpa [RCode.size, show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
      using (hcont y hy).anti (by omega)
  | @loop_exit _ body _ _ hL hc hp_y =>
    refine demonicSafeWithin_of_pure hL (fun _ => stepRandResizable_branch_neg hp.head hc)
      fun _ _ _ => demonicSafeWithin_of_pure hL (fun _ => stepRandResizable_jump hp.loop_exit)
        fun _ _ _ => ?_
    simpa [RCode.size, show pc + body.size + 3 = pc + (body.size + 3) by omega]
      using (hcont _ hp_y).anti (by omega)
  | @loop_iter _ body _ _ _ _ _ hc hbody hloop ihb ihl =>
    exact demonicSafeWithin_of_pure hbody.frontier_le
      (fun _ => stepRandResizable_branch_pos hp.head hc) fun _ _ _ =>
      ihb hp.loop_body fun y hy => demonicSafeWithin_of_pure (hloop y hy).frontier_le
        (fun _ => stepRandResizable_jump hp.loop_back) fun _ _ _ =>
        ihl y hy hp fun z hz => (hcont z hz).anti (by omega)
  | mono _ _ hPQ ih => exact ih hp fun y hy => hcont y (hPQ y hy)


end Cslib.WordRAM.Resizable
