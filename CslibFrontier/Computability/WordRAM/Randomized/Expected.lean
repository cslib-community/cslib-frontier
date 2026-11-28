/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Randomized.Structured
public import CslibFrontier.Languages.Probabilistic.Expect
public import CslibFrontier.Probability.PMF.Bind
public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.SupportTsum
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Tactic.SuppCases

/-!
# Expected running time for randomized word RAMs

Expected instruction counts for flat (`Program`) and structured (`Code`) randomized word RAM
programs, valued in the extended nonnegative reals `ℝ≥0∞` so expectations are total without
summability side conditions; nonsummable running-probability tails have value `⊤`.

For a flat program `p` starting at state `s`, the expected running time is defined via the
discrete tail-sum formula over clocked horizons:
`expectedTime w p s = ∑' t : ℕ, (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u}`.
Because `.halted` and `.faulted` are absorbing, each horizon `t` contributes the probability that
execution is still running before either halt or fault after `t` steps. Summing over `t : ℕ` yields
the exact 1-step Bellman equation `expectedStepsFrom_running`, connects directly to structured
`ExecRand` trees via
`ExecRand.expectedTime_program`, reduces to a finite sum under `RandHaltsWithin`
(`RandHaltsWithin.expectedTime_eq_sum`, `expectedTime_le_of_randHaltsWithin`), and recovers exact
deterministic step counts (`Executes.expectedTime_eq`).

For structured `Code B r` programs, `expectedCodeTime` measures the expected instruction count of
`codeComp w c x` when a finite, fault-free `ExecRand` tree exists, and is `⊤` otherwise. Thus
unbounded almost-surely terminating loops can receive a conservative infinite structured cost.
It satisfies exact sequential
additivity (`expectedCodeTime_seq`), branch laws (`expectedCodeTime_branch_pos`,
`expectedCodeTime_branch_neg`, `expectedCodeTime_branch_le`), and a potential/drift bound for
`while` loops (`expectedCodeTime_loop_le_of_drift`).

## Main definitions

* `Cslib.WordRAM.AlmostSurelyHalts`: zero faults at all horizons and supremum halting probability
  equal to `1`.
* `Cslib.WordRAM.expectedStepsFrom`, `Cslib.WordRAM.expectedTime`: `ℝ≥0∞`-valued expected
  remaining instructions from a `RandCfg r` or initial `State r`.
* `Cslib.WordRAM.expectedCodeTime`: `ℝ≥0∞`-valued expected instruction count of a structured
  `Code B r`.
* `Cslib.WordRAM.ExecCodeDist`: compositional structured execution certificate pairing an output
  distribution `μ : PMF (Data r)` with an expected step bound `T : ℝ≥0∞`, closed under unbounded
  almost-surely terminating geometric `while` loops (`ExecCodeDist.loop_geometric`).

## Main results

* `Cslib.WordRAM.expectedStepsFrom_running`: 1-step Bellman equation for `expectedStepsFrom`.
* `Cslib.WordRAM.RandHaltsWithin.almostSurelyHalts`,
  `Cslib.WordRAM.AlmostSurelyHalts.of_expectedTime_ne_top`: sufficient conditions for almost-sure
  halting.
* `Cslib.WordRAM.RandHaltsWithin.expectedTime_eq_sum`,
  `Cslib.WordRAM.expectedTime_le_of_randHaltsWithin`: finite-horizon reduction under
  `RandHaltsWithin`.
* `Cslib.WordRAM.Executes.expectedTime_eq`: deterministic halting runs have `expectedTime = n`.
* `Cslib.WordRAM.ExecRand.expectedTime_program`: exact bridge between compiled `c.program out` and
  `expectedCodeTime`.
* `Cslib.WordRAM.expectedCodeTime_seq`, `Cslib.WordRAM.expectedCodeTime_branch_le`,
  `Cslib.WordRAM.expectedCodeTime_loop_le_of_drift`: compositional expected-time rules for
  structured `Code`.
* `Cslib.WordRAM.ExecCodeDist.loop_geometric`,
  `Cslib.WordRAM.expectedStepsFrom_loop_le_of_geometric`,
  `Cslib.WordRAM.ExecCodeDist.program_halts`: expected-time and almost-sure halting rules for
  geometric Las Vegas `while` loops and structured programs.

Discrete and conditional expectation principles are classical background; see
[MitzenmacherUpfal2017], Sections 2.1, 2.3, and 2.4. The particular native tail-sum/Bellman
definitions, finite structured-execution-tree bridge and ranked-loop expected-cost formalization are
original library constructions in this module.

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017],
  Sections 2.1, 2.3, and 2.4.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib

/-! ## Almost-sure halting and `ℝ≥0∞`-valued expected running time -/

namespace WordRAM

variable {B : Basis} {r : ℕ}

/-- Set of active (`.running`) configurations. -/
def RandCfg.runningSet (r : ℕ) : Set (RandCfg r) := {cfg | ∃ u, cfg = .running u}

/-- Set of cleanly halted (`.halted`) configurations. -/
def RandCfg.haltedSet (r : ℕ) : Set (RandCfg r) := {cfg | ∃ v d, cfg = .halted v d}

@[simp]
theorem RandCfg.mem_runningSet_iff {cfg : RandCfg r} :
    cfg ∈ RandCfg.runningSet r ↔ ∃ u, cfg = .running u :=
  Iff.rfl

@[simp]
theorem RandCfg.mem_haltedSet_iff {cfg : RandCfg r} :
    cfg ∈ RandCfg.haltedSet r ↔ ∃ v d, cfg = .halted v d :=
  Iff.rfl

/-- Starting from `s`, `p` never faults and halts with probability tending to `1`. -/
def AlmostSurelyHalts (w : ℕ) (p : Program B r) (s : State r) : Prop :=
  RandFaultFree w p s ∧
    (⨆ T : ℕ, (evalRand w p T s).toOuterMeasure (RandCfg.haltedSet r)) = 1

/-- Halting probability is monotone in the horizon `T` because `.halted` is absorbing. -/
theorem evalRand_haltedSet_mono (w : ℕ) (p : Program B r) (s : State r) :
    Monotone fun T => (evalRand w p T s).toOuterMeasure (RandCfg.haltedSet r) := by
  refine monotone_nat_of_le_succ fun T => ?_
  conv_rhs => rw [evalRand, runRand_add w p T 1, ProbComp.eval_bind]
  simp only [runRand_succ, runRand_zero, bind_pure]
  refine (le_of_eq (mul_one _).symm).trans ?_
  refine Cslib.Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal _ _ _ _ le_rfl ?_
  intro cfg _ hhalt
  obtain ⟨v, d, rfl⟩ := hhalt
  simp [stepRand_halted, PMF.toOuterMeasure_pure_apply, RandCfg.haltedSet]

/-- Any worst-case bounded execution halts almost surely. -/
theorem RandHaltsWithin.almostSurelyHalts {w T : ℕ} {p : Program B r} {s : State r}
    (h : RandHaltsWithin w p s T) : AlmostSurelyHalts w p s :=
  ⟨h.randFaultFree, le_antisymm (iSup_le fun _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
    (le_iSup_of_le T ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr fun cfg hmem =>
      h cfg (by rwa [support_evalRand] at hmem)).ge)⟩

/-- Expected number of remaining instructions starting from configuration `cfg`, defined via the
tail sum of active-configuration probabilities. -/
noncomputable def expectedStepsFrom (w : ℕ) (p : Program B r) (cfg : RandCfg r) : ℝ≥0∞ :=
  ∑' t : ℕ, (runRand w p t cfg).eval.toOuterMeasure {cfg' | ∃ u, cfg' = .running u}

/-- Expected running time of `p` at word size `w` from initial state `s`, valued in `ℝ≥0∞`. -/
noncomputable def expectedTime (w : ℕ) (p : Program B r) (s : State r) : ℝ≥0∞ :=
  ∑' t : ℕ, (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u}

theorem expectedTime_eq_expectedStepsFrom (w : ℕ) (p : Program B r) (s : State r) :
    expectedTime w p s = expectedStepsFrom w p (.running s) :=
  rfl

@[simp]
theorem expectedStepsFrom_halted (w : ℕ) (p : Program B r) (v : ℕ) (d : Data r) :
    expectedStepsFrom w p (.halted v d) = 0 := by
  simp [expectedStepsFrom, PMF.toOuterMeasure_pure_apply]

@[simp]
theorem expectedStepsFrom_faulted (w : ℕ) (p : Program B r) :
    expectedStepsFrom w p .faulted = 0 := by
  simp [expectedStepsFrom, PMF.toOuterMeasure_pure_apply]

/-- 1-step Bellman equation: an active state `s` incurs `1` immediate step plus the expected
remaining steps from `stepRand w p (.running s)`. -/
theorem expectedStepsFrom_running (w : ℕ) (p : Program B r) (s : State r) :
    expectedStepsFrom w p (.running s) =
      1 + ProbComp.expect (stepRand w p (.running s)) (expectedStepsFrom w p) := by
  rw [expectedStepsFrom, tsum_eq_add_tsum_ite 0]
  have hzero : (runRand w p 0 (.running s)).eval.toOuterMeasure
      {cfg' | ∃ u, cfg' = .running u} = 1 := by simp [PMF.toOuterMeasure_pure_apply]
  have hshift := Nat.succ_injective.tsum_eq (f := fun t : ℕ => if t = 0 then 0 else
      (runRand w p t (.running s)).eval.toOuterMeasure {cfg' | ∃ u, cfg' = .running u})
    fun t ht => match t with | 0 => absurd rfl ht | k + 1 => ⟨k, rfl⟩
  simp only [Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at hshift
  rw [hzero]; congr 1
  rw [(tsum_congr fun _ => by split_ifs <;> rfl).trans hshift.symm]
  simp_rw [runRand_succ, ProbComp.eval_bind, PMF.toOuterMeasure_bind_apply]
  rw [tsum_comm]
  simp only [ProbComp.expect, expectedStepsFrom, ENNReal.tsum_mul_left]

/-- Under `RandFaultFree`, every horizon partitions probability `1` between `.running` and
`.halted`. -/
theorem RandFaultFree.running_add_halted_eq_one {w : ℕ} {p : Program B r} {s : State r}
    (hf : RandFaultFree w p s) (t : ℕ) :
    (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u} +
      (evalRand w p t s).toOuterMeasure (RandCfg.haltedSet r) = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
  refine (tsum_congr fun cfg => ?_).trans (evalRand w p t s).tsum_coe
  cases cfg with
  | running _ | halted _ _ => simp [RandCfg.haltedSet]
  | faulted => simp [RandCfg.haltedSet, hf.evalRand_faulted_eq_zero t]

/-- A fault-free execution with finite expected running time halts almost surely. -/
theorem AlmostSurelyHalts.of_expectedTime_ne_top {w : ℕ} {p : Program B r} {s : State r}
    (hf : RandFaultFree w p s) (htop : expectedTime w p s ≠ ⊤) :
    AlmostSurelyHalts w p s := by
  refine ⟨hf, le_antisymm (iSup_le fun _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
    (tsub_eq_zero_iff_le.mp <| by_contra fun hne => htop <| top_unique ?_)⟩
  rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) hne]
  refine tsum_le_tsum fun t => tsub_le_iff_right.mpr ?_
  have hpart := hf.running_add_halted_eq_one t
  exact hpart.ge.trans <| add_le_add le_rfl <|
    le_iSup (fun k => (evalRand w p k s).toOuterMeasure (RandCfg.haltedSet r)) t

/-- Under `RandHaltsWithin w p s T`, the active-configuration tail sum vanishes from `T` onward and
reduces to a finite sum over `Finset.range T`. -/
theorem RandHaltsWithin.expectedTime_eq_sum {w T : ℕ} {p : Program B r} {s : State r}
    (h : RandHaltsWithin w p s T) :
    expectedTime w p s =
      ∑ t ∈ Finset.range T,
        (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u} := by
  rw [expectedTime, tsum_eq_sum (s := Finset.range T)]
  intro t ht
  rw [evalRand_eq_of_randHaltsWithin h (Nat.le_of_not_lt (Finset.mem_range.not.mp ht)),
    PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  rintro _ hmem ⟨u, rfl⟩
  rw [support_evalRand] at hmem
  obtain ⟨_, _, hvd⟩ := h _ hmem
  cases hvd

/-- A worst-case step bound `RandHaltsWithin w p s T` immediately bounds `expectedTime` by `T`. -/
theorem expectedTime_le_of_randHaltsWithin {w T : ℕ} {p : Program B r} {s : State r}
    (h : RandHaltsWithin w p s T) :
    expectedTime w p s ≤ T := by
  rw [h.expectedTime_eq_sum]
  exact (Finset.sum_le_sum fun _ _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _).trans_eq
    (by simp)

/-- Along any deterministic `Runs` of length `m`, `expectedStepsFrom` adds `m` to the expected
remaining steps at the destination state. -/
theorem Runs.expectedStepsFrom_eq {w m : ℕ} {p : Program B r} {s t : State r}
    (hrun : Runs w p s t m) :
    expectedStepsFrom w p (.running s) = m + expectedStepsFrom w p (.running t) := by
  induction hrun using Relation.RelatesInSteps.head_induction_on with
  | hrefl => simp
  | @hhead s u m' hsc _ ih =>
    rw [expectedStepsFrom_running, stepRand_of_step_eq_next hsc, ProbComp.expect_pure, ih,
      Nat.cast_add, Nat.cast_one, add_comm (m' : ℝ≥0∞) 1, add_assoc]

/-- Any deterministic halting execution `Executes w p s v n` has exact expected running time `n`. -/
theorem Executes.expectedTime_eq {w n : ℕ} {p : Program B r} {s : State r} {v : ℕ}
    (h : Executes w p s v n) :
    expectedTime w p s = n := by
  obtain ⟨t, m, hrun, hhalt, rfl⟩ := h
  rw [expectedTime_eq_expectedStepsFrom, hrun.expectedStepsFrom_eq, expectedStepsFrom_running,
    stepRand_of_step_eq_halt hhalt, ProbComp.expect_pure, expectedStepsFrom_halted, add_zero,
    Nat.cast_add, Nat.cast_one]

/-! ## Structured `expectedCodeTime` and compilation bridge -/

private theorem contains_seq_right {c₁ c₂ : Code B r} {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.seq c₁ c₂).assemble pc)) :
    p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
  simpa [Code.length_assemble] using hp.append_right

private theorem contains_branch_pos {cond : Cond r} {pos neg : Code B r} {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.branch cond pos neg).assemble pc)) :
    p.Contains (pc + neg.size + 2) (pos.assemble (pc + neg.size + 2)) := by
  have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
  rwa [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'

private theorem stepRand_branch_pos {w : ℕ} {cond : Cond r} {pos neg : Code B r} {x : Data r}
    {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.branch cond pos neg).assemble pc)) (hc : cond.Holds x) :
    stepRand w p (.running ⟨pc, x⟩) = pure (.running ⟨pc + neg.size + 2, x⟩) := by
  have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
  simp [stepRand_branch (s := ⟨pc, x⟩) hbr, hc]

private theorem stepRand_branch_neg {w : ℕ} {cond : Cond r} {pos neg : Code B r} {x : Data r}
    {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.branch cond pos neg).assemble pc)) (hc : ¬cond.Holds x) :
    stepRand w p (.running ⟨pc, x⟩) = pure (.running ⟨pc + 1, x⟩) := by
  have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
  simp [stepRand_branch (s := ⟨pc, x⟩) hbr, hc]

private theorem stepRand_branch_neg_jump {w : ℕ} {cond : Cond r} {pos neg : Code B r}
    {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.branch cond pos neg).assemble pc)) (y : Data r) :
    stepRand w p (.running ⟨pc + 1 + neg.size, y⟩) =
      pure (.running ⟨pc + (Code.branch cond pos neg).size, y⟩) := by
  have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
    simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
  simpa [Code.size, show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
    using stepRand_jump (s := ⟨pc + 1 + neg.size, y⟩) hj

private theorem contains_loop_body {cond : Cond r} {body : Code B r} {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc)) :
    p.Contains (pc + 2) (body.assemble (pc + 2)) := by
  simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left

private theorem stepRand_loop_holds {w : ℕ} {cond : Cond r} {body : Code B r} {x : Data r}
    {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc)) (hc : cond.Holds x) :
    stepRand w p (.running ⟨pc, x⟩) = pure (.running ⟨pc + 2, x⟩) := by
  simp [stepRand_branch (s := ⟨pc, x⟩) hp.head, hc]

private theorem stepRand_loop_not_holds {w : ℕ} {cond : Cond r} {body : Code B r} {x : Data r}
    {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc)) (hc : ¬cond.Holds x) :
    stepRand w p (.running ⟨pc, x⟩) = pure (.running ⟨pc + 1, x⟩) := by
  simp [stepRand_branch (s := ⟨pc, x⟩) hp.head, hc]

private theorem stepRand_loop_exit_jump {w : ℕ} {cond : Cond r} {body : Code B r}
    {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc)) (y : Data r) :
    stepRand w p (.running ⟨pc + 1, y⟩) =
      pure (.running ⟨pc + (Code.loop cond body).size, y⟩) := by
  simpa [Code.size, show pc + body.size + 3 = pc + (body.size + 3) by omega]
    using stepRand_jump (s := ⟨pc + 1, y⟩) hp.cons_tail.head

private theorem stepRand_loop_back {w : ℕ} {cond : Cond r} {body : Code B r}
    {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc)) (y : Data r) :
    stepRand w p (.running ⟨pc + 2 + body.size, y⟩) = pure (.running ⟨pc, y⟩) := by
  have hj : p[pc + 2 + body.size]? = some (.jump pc) := by
    simpa using hp.cons_tail.cons_tail.append_right.head
  exact stepRand_jump (s := ⟨pc + 2 + body.size, y⟩) hj

/-- Along an assembled structured execution `ExecRand w c x m` inside `p`, the expected remaining
steps from `⟨pc, x⟩` equal the expected step count of `m` plus the expected continuation steps from
`⟨pc + c.size, y⟩`. -/
theorem ExecRand.expectedStepsFrom_assemble {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) :
    expectedStepsFrom w p (.running ⟨pc, x⟩) =
      ProbComp.expect m (fun z =>
        (z.2 : ℝ≥0∞) + expectedStepsFrom w p (.running ⟨pc + c.size, z.1⟩)) := by
  induction h generalizing pc with
  | op ho =>
    rw [expectedStepsFrom_running, stepRand_op hp.head ho, ProbComp.expect_pure,
      ProbComp.expect_pure]
    simp [Code.size]
  | @rand dst src x hfit =>
    rw [expectedStepsFrom_running, stepRand_rand_of_fits hp.head hfit, ProbComp.expect_bind,
      ProbComp.expect_bind]
    simp only [ProbComp.expect_pure, Code.size, Nat.cast_one]
    rw [ProbComp.expect_add, ProbComp.expect_const]
  | @seq c₁ c₂ x m₁ m₂ _ _ ih₁ ih₂ =>
    rw [ih₁ hp.append_left, ProbComp.expect_bind]
    refine ProbComp.expect_congr_on_support fun z₁ hz₁ => ?_
    rw [ih₂ z₁ hz₁ (contains_seq_right hp), ProbComp.expect_bind,
      ← ProbComp.expect_const (m₂ z₁.1) (z₁.2 : ℝ≥0∞), ← ProbComp.expect_add]
    exact ProbComp.expect_congr_on_support fun z₂ _ => by
      simp only [ProbComp.expect_pure, Code.size, Nat.cast_add, add_assoc]
  | @branch_pos cond pos neg x m hc _ ih =>
    rw [expectedStepsFrom_running, stepRand_branch_pos hp hc, ProbComp.expect_pure,
      ih (contains_branch_pos hp), ProbComp.expect_map,
      ← ProbComp.expect_const m 1, ← ProbComp.expect_add]
    have hpc : pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) := by omega
    exact ProbComp.expect_congr_on_support fun z _ => by
      simp only [Code.size, hpc, Nat.cast_add, Nat.cast_one]; ac_rfl
  | @branch_neg cond pos neg x m hc _ ih =>
    rw [expectedStepsFrom_running, stepRand_branch_neg hp hc, ProbComp.expect_pure,
      ih hp.cons_tail.append_left, ProbComp.expect_map,
      ← ProbComp.expect_const m 1, ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z _ => ?_
    rw [expectedStepsFrom_running, stepRand_branch_neg_jump hp z.1, ProbComp.expect_pure]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    rw [show (2 : ℝ≥0∞) = 1 + 1 from one_add_one_eq_two.symm]; ac_rfl
  | @loop_exit cond body x hc =>
    rw [expectedStepsFrom_running, stepRand_loop_not_holds hp hc, ProbComp.expect_pure,
      expectedStepsFrom_running, stepRand_loop_exit_jump hp x, ProbComp.expect_pure,
      ProbComp.expect_pure, Nat.cast_ofNat, ← add_assoc, one_add_one_eq_two]
  | @loop_iter cond body x mb ml hc _ _ ihb ihl =>
    rw [expectedStepsFrom_running, stepRand_loop_holds hp hc, ProbComp.expect_pure,
      ihb (contains_loop_body hp), ProbComp.expect_bind,
      ← ProbComp.expect_const mb 1, ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z₁ hz₁ => ?_
    rw [expectedStepsFrom_running, stepRand_loop_back hp z₁.1, ProbComp.expect_pure,
      ihl z₁ hz₁ hp, ProbComp.expect_bind,
      ← add_assoc, ← add_assoc, ← add_comm (z₁.2 : ℝ≥0∞), add_assoc (z₁.2 : ℝ≥0∞) 1 1,
      one_add_one_eq_two, ← ProbComp.expect_const (ml z₁.1) ((z₁.2 : ℝ≥0∞) + 2),
      ← ProbComp.expect_add]
    exact ProbComp.expect_congr_on_support fun z₂ _ => by
      simp only [ProbComp.expect_pure, Nat.cast_add, Nat.cast_ofNat]
      rw [← add_assoc ((z₁.2 : ℝ≥0∞) + 2) (z₂.2 : ℝ≥0∞), add_right_comm (z₁.2 : ℝ≥0∞) 2]

/-- Exact bridge: compiling `c` with `c.program out` adds `1` (for the final `halt out`
instruction) to the expected step count of `ExecRand w c x m`. -/
theorem ExecRand.expectedTime_program {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) (out : Fin r) :
    expectedTime w (c.program out) ⟨0, x⟩ =
      ProbComp.expect m (fun z => (z.2 : ℝ≥0∞)) + 1 := by
  rw [expectedTime_eq_expectedStepsFrom,
    h.expectedStepsFrom_assemble (Program.Contains.self (c.program out)).append_left,
    ← ProbComp.expect_const m 1, ← ProbComp.expect_add]
  refine ProbComp.expect_congr_on_support fun z _ => ?_
  have hhalt : (c.program out)[0 + c.size]? = some (.halt out) := by
    simp [Code.program]
  rw [expectedStepsFrom_running, stepRand_halt (s := ⟨0 + c.size, z.1⟩) hhalt,
    ProbComp.expect_pure, expectedStepsFrom_halted, add_zero]

/-- When some `ExecRand w c x m` exists, `codeComp w c x` satisfies `ExecRand`. -/
theorem codeComp_execRand {w : ℕ} {c : Code B r} {x : Data r}
    (hex : ∃ m, ExecRand w c x m) : ExecRand w c x (codeComp w c x) := by
  obtain ⟨m, hm⟩ := hex
  rwa [hm.codeComp_eq]

/-- Expected instruction count of a structured program `c` from data `x` at word size `w`, or `⊤`
if `c` can fault or diverge on some path from `x`. -/
noncomputable def expectedCodeTime (w : ℕ) (c : Code B r) (x : Data r) : ℝ≥0∞ :=
  open Classical in
  if ∃ m, ExecRand w c x m then
    ProbComp.expect (codeComp w c x) (fun z => (z.2 : ℝ≥0∞))
  else ⊤

theorem ExecRand.expectedCodeTime_eq {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) :
    expectedCodeTime w c x = ProbComp.expect m (fun z => (z.2 : ℝ≥0∞)) := by
  classical
  have hex : ∃ m', ExecRand w c x m' := ⟨m, h⟩
  simp only [expectedCodeTime, hex, ↓reduceIte, h.codeComp_eq]

theorem expectedCodeTime_eq_top {w : ℕ} {c : Code B r} {x : Data r}
    (h : ¬∃ m, ExecRand w c x m) : expectedCodeTime w c x = ⊤ := by
  classical
  simp only [expectedCodeTime, h, ↓reduceIte]

theorem Exec.expectedCodeTime_eq {w n : ℕ} {c : Code B r} {x y : Data r}
    (h : Exec w c x y n) :
    expectedCodeTime w c x = n := by
  rw [h.execRand.expectedCodeTime_eq, ProbComp.expect_pure]

theorem expectedCodeTime_program {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) (out : Fin r) :
    expectedTime w (c.program out) ⟨0, x⟩ = expectedCodeTime w c x + 1 := by
  rw [h.expectedTime_program, h.expectedCodeTime_eq]

@[simp]
theorem expectedCodeTime_op {w : ℕ} {o : Op B r} {x y : Data r} (ho : o.eval w x = some y) :
    expectedCodeTime w (.op o) x = 1 := by
  simpa only [Nat.cast_one] using (Exec.op ho).expectedCodeTime_eq

@[simp]
theorem expectedCodeTime_rand {w : ℕ} {dst src : Fin r} {x : Data r} (h : Fits w (x.regs src)) :
    expectedCodeTime (B := B) w (.rand dst src) x = 1 := by
  rw [(ExecRand.rand (B := B) (dst := dst) h).expectedCodeTime_eq, ProbComp.expect_bind]
  simp only [ProbComp.expect_pure, Nat.cast_one, ProbComp.expect_const]

/-- Sequential additivity of `expectedCodeTime`: when `c₁` executes via `m₁`, the expected time of
`Code.seq c₁ c₂` equals the expected time of `c₁` plus the `m₁`-expected time of `c₂`. -/
theorem expectedCodeTime_seq {w : ℕ} {c₁ c₂ : Code B r} {x : Data r}
    {m₁ : ProbComp (Data r × ℕ)} (h₁ : ExecRand w c₁ x m₁) :
    expectedCodeTime w (.seq c₁ c₂) x =
      expectedCodeTime w c₁ x + ProbComp.expect m₁ (fun z => expectedCodeTime w c₂ z.1) := by
  classical
  by_cases h₂ : ∀ z ∈ m₁.support, ∃ m₂, ExecRand w c₂ z.1 m₂
  · have h₂_comp := fun z hz => codeComp_execRand (h₂ z hz)
    rw [(h₁.seq h₂_comp).expectedCodeTime_eq, h₁.expectedCodeTime_eq, ProbComp.expect_bind,
      ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z hz => ?_
    rw [ProbComp.expect_bind, (h₂_comp z hz).expectedCodeTime_eq,
      ← ProbComp.expect_const (codeComp w c₂ z.1) (z.2 : ℝ≥0∞), ← ProbComp.expect_add]
    exact ProbComp.expect_congr_on_support fun _ _ => by
      simp only [ProbComp.expect_pure, Nat.cast_add]
  · simp only [not_forall] at h₂; obtain ⟨z₀, hz₀, hnot₂⟩ := h₂
    have hnot_seq : ¬∃ m, ExecRand w (.seq c₁ c₂) x m := fun ⟨_, hm⟩ => by
      cases hm with
      | seq h₁' h₂' => obtain rfl := h₁.unique h₁'; exact hnot₂ ⟨_, h₂' z₀ hz₀⟩
    rw [expectedCodeTime_eq_top hnot_seq,
      ProbComp.expect_eq_top_of_mem_support hz₀ (expectedCodeTime_eq_top hnot₂), add_top]

/-- Sequential additivity after a deterministic prefix `Exec w c₁ x y n₁`. -/
theorem expectedCodeTime_seq_of_exec {w n₁ : ℕ} {c₁ c₂ : Code B r} {x y : Data r}
    (h₁ : Exec w c₁ x y n₁) :
    expectedCodeTime w (.seq c₁ c₂) x = n₁ + expectedCodeTime w c₂ y := by
  rw [expectedCodeTime_seq h₁.execRand, h₁.expectedCodeTime_eq, ProbComp.expect_pure]

theorem expectedCodeTime_branch_pos {w : ℕ} {cond : Cond r} {pos neg : Code B r} {x : Data r}
    (hc : cond.Holds x) :
    expectedCodeTime w (.branch cond pos neg) x = expectedCodeTime w pos x + 1 := by
  classical
  by_cases hp : ∃ m, ExecRand w pos x m
  · obtain ⟨m, hm⟩ := hp
    rw [(hm.branch_pos hc).expectedCodeTime_eq, hm.expectedCodeTime_eq, ProbComp.expect_map,
      ← ProbComp.expect_const m 1, ← ProbComp.expect_add]
    simp [Nat.cast_add]
  · have hnot : ¬∃ m, ExecRand w (.branch cond pos neg) x m := fun ⟨_, hm⟩ => by
      cases hm with
      | branch_pos _ h => exact hp ⟨_, h⟩
      | branch_neg hc' _ => exact hc' hc
    simp only [expectedCodeTime, hnot, hp, ↓reduceIte, top_add]

theorem expectedCodeTime_branch_neg {w : ℕ} {cond : Cond r} {pos neg : Code B r} {x : Data r}
    (hc : ¬cond.Holds x) :
    expectedCodeTime w (.branch cond pos neg) x = expectedCodeTime w neg x + 2 := by
  classical
  by_cases hn : ∃ m, ExecRand w neg x m
  · obtain ⟨m, hm⟩ := hn
    rw [(hm.branch_neg hc).expectedCodeTime_eq, hm.expectedCodeTime_eq, ProbComp.expect_map,
      ← ProbComp.expect_const m 2, ← ProbComp.expect_add]
    simp [Nat.cast_add]
  · have hnot : ¬∃ m, ExecRand w (.branch cond pos neg) x m := fun ⟨_, hm⟩ => by
      cases hm with
      | branch_pos hc' _ => exact hc hc'
      | branch_neg _ h => exact hn ⟨_, h⟩
    simp only [expectedCodeTime, hnot, hn, ↓reduceIte, top_add]

/-- Branch convexity / uniform upper bound on `expectedCodeTime (.branch cond pos neg)`. -/
theorem expectedCodeTime_branch_le {w : ℕ} {cond : Cond r} {pos neg : Code B r} {x : Data r}
    {B_steps : ℝ≥0∞}
    (hpos : cond.Holds x → expectedCodeTime w pos x + 1 ≤ B_steps)
    (hneg : ¬cond.Holds x → expectedCodeTime w neg x + 2 ≤ B_steps) :
    expectedCodeTime w (.branch cond pos neg) x ≤ B_steps := by
  by_cases hc : cond.Holds x
  · rw [expectedCodeTime_branch_pos hc]; exact hpos hc
  · rw [expectedCodeTime_branch_neg hc]; exact hneg hc

/-- Convex combination of branch expected times under a random input distribution `m`. -/
theorem expect_expectedCodeTime_branch {w : ℕ} {cond : Cond r} {pos neg : Code B r}
    (m : ProbComp (Data r)) :
    ProbComp.expect m (fun x => expectedCodeTime w (.branch cond pos neg) x) =
      ProbComp.expect m (fun x =>
        open Classical in
        if cond.Holds x then expectedCodeTime w pos x + 1 else expectedCodeTime w neg x + 2) :=
  ProbComp.expect_congr_on_support fun x _ => by
    by_cases hc : cond.Holds x <;>
      simp [hc, expectedCodeTime_branch_pos, expectedCodeTime_branch_neg]

theorem expectedCodeTime_loop_exit {w : ℕ} {cond : Cond r} {body : Code B r} {x : Data r}
    (hc : ¬cond.Holds x) :
    expectedCodeTime w (.loop cond body) x = 2 := by
  rw [(ExecRand.loop_exit (body := body) hc).expectedCodeTime_eq, ProbComp.expect_pure]; rfl

theorem expectedCodeTime_loop_iter {w : ℕ} {cond : Cond r} {body : Code B r} {x : Data r}
    {mb : ProbComp (Data r × ℕ)} (hc : cond.Holds x) (hb : ExecRand w body x mb) :
    expectedCodeTime w (.loop cond body) x =
      expectedCodeTime w body x + 2 +
        ProbComp.expect mb (fun z => expectedCodeTime w (.loop cond body) z.1) := by
  classical
  by_cases hl : ∀ z ∈ mb.support, ∃ ml, ExecRand w (.loop cond body) z.1 ml
  · have hl_comp := fun z hz => codeComp_execRand (hl z hz)
    rw [(ExecRand.loop_iter hc hb hl_comp).expectedCodeTime_eq, hb.expectedCodeTime_eq,
      ProbComp.expect_bind, ← ProbComp.expect_const mb 2, ← ProbComp.expect_add,
      ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z hz => ?_
    rw [ProbComp.expect_bind, (hl_comp z hz).expectedCodeTime_eq,
      ← ProbComp.expect_const (codeComp w (.loop cond body) z.1) ((z.2 : ℝ≥0∞) + 2),
      ← ProbComp.expect_add]
    exact ProbComp.expect_congr_on_support fun _ _ => by
      simp only [ProbComp.expect_pure, Nat.cast_add, Nat.cast_ofNat]; ac_rfl
  · simp only [not_forall] at hl; obtain ⟨z₀, hz₀, hnot_l⟩ := hl
    have hnot_loop : ¬∃ m, ExecRand w (.loop cond body) x m := fun ⟨_, hm⟩ => by
      cases hm with
      | loop_exit hc' => exact hc' hc
      | loop_iter _ hb' hl' => obtain rfl := hb.unique hb'; exact hnot_l ⟨_, hl' z₀ hz₀⟩
    rw [expectedCodeTime_eq_top hnot_loop,
      ProbComp.expect_eq_top_of_mem_support hz₀ (expectedCodeTime_eq_top hnot_l), add_top]

/-- Potential/drift bound for `Code.loop`: if an invariant `I` holds, every iteration decreases a
well-founded `ℕ` ranking `Φ`, and the expected single-iteration cost `(z.2 : ℝ≥0∞) + 2` plus next
potential `Ψ z.1` is at most `Ψ s`, then the loop executes cleanly (`∃ m, ExecRand ...`) and its
`expectedCodeTime` is at most `Ψ x + 2` (accounting for the final `2`-step loop exit). -/
theorem expectedCodeTime_loop_le_of_drift {w : ℕ} {cond : Cond r} {body : Code B r}
    (I : Data r → Prop) (Φ : Data r → ℕ) (Ψ : Data r → ℝ≥0∞) {x : Data r}
    (hx : I x)
    (hstep : ∀ s, I s → cond.Holds s →
      ∃ mb, ExecRand w body s mb ∧
        (∀ z ∈ mb.support, I z.1 ∧ Φ z.1 < Φ s) ∧
        ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞) + 2 + Ψ z.1) ≤ Ψ s) :
    (∃ m, ExecRand w (.loop cond body) x m) ∧
      expectedCodeTime w (.loop cond body) x ≤ Ψ x + 2 := by
  have hstrong : ∀ k s, Φ s = k → I s →
      (∃ m, ExecRand w (.loop cond body) s m) ∧
        expectedCodeTime w (.loop cond body) s ≤ Ψ s + 2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s rfl hs
      by_cases hc : cond.Holds s
      · obtain ⟨mb, hb, hsup, hdrift⟩ := hstep s hs hc
        have hrec := fun z hz => ih (Φ z.1) (hsup z hz).2 z.1 rfl (hsup z hz).1
        refine ⟨⟨_, ExecRand.loop_iter hc hb fun z hz => codeComp_execRand (hrec z hz).1⟩, ?_⟩
        rw [expectedCodeTime_loop_iter hc hb, hb.expectedCodeTime_eq]
        refine (add_le_add le_rfl (ProbComp.expect_mono_on_support fun z hz =>
          (hrec z hz).2)).trans ?_
        rw [add_right_comm _ 2 _, ← ProbComp.expect_add]
        have heq : ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞) + (Ψ z.1 + 2)) =
            ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞) + 2 + Ψ z.1) :=
          ProbComp.expect_congr_on_support fun _ _ => by ac_rfl
        exact heq ▸ add_le_add hdrift le_rfl
      · exact ⟨⟨_, ExecRand.loop_exit hc⟩, by rw [expectedCodeTime_loop_exit hc]; exact le_add_self⟩
  exact hstrong (Φ x) x rfl hx

/-! ## Distributional structured execution (`ExecCodeDist`) and geometric Las Vegas loops -/

/-- Non-faulting structured randomized executions transfer instruction-for-instruction along any
defined-evaluation basis simulation `ψ : B.Simulates B'`. -/
theorem ExecRand.mapSimulates {B' : Basis} (ψ : B.Simulates B') {w : ℕ} {c : Code B r}
    {x : Data r} {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) :
    ExecRand w (c.mapSimulates ψ) x m := by
  induction h with
  | op ho => exact .op (Op.eval_mapSimulates_of_some ψ ho)
  | rand hfit => exact .rand hfit
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl

/-- Pointwise halting probability at `.halted v d` is monotone in the horizon `T`. -/
theorem evalRand_halted_mono (w : ℕ) (p : Program B r) (s : State r) (v : ℕ) (d : Data r) :
    Monotone fun T => evalRand w p T s (.halted v d) := by
  refine monotone_nat_of_le_succ fun T => ?_
  conv_rhs => rw [evalRand, runRand_add w p T 1, ProbComp.eval_bind, PMF.bind_apply]
  simp only [runRand_succ, runRand_zero, bind_pure]
  have hself : (runRand w p T (.running s)).eval (.halted v d) *
      (stepRand w p (.halted v d)).eval (.halted v d) = evalRand w p T s (.halted v d) := by
    simp [evalRand, stepRand_halted]
  exact hself ▸ le_tsum (f := fun cfg => (runRand w p T (.running s)).eval cfg *
    (stepRand w p cfg).eval (.halted v d)) (.halted v d)

/-- Finite-horizon approximation of `expectedStepsFrom`: expected number of active (`.running`)
steps within the first `N` steps starting from configuration `cfg`. -/
noncomputable def expectedStepsWithin (w : ℕ) (p : Program B r) (N : ℕ) (cfg : RandCfg r) :
    ℝ≥0∞ :=
  ∑ t ∈ Finset.range N, (runRand w p t cfg).eval.toOuterMeasure {cfg' | ∃ u, cfg' = .running u}

@[simp]
theorem expectedStepsWithin_zero (w : ℕ) (p : Program B r) (cfg : RandCfg r) :
    expectedStepsWithin w p 0 cfg = 0 := by
  simp [expectedStepsWithin]

@[simp]
theorem expectedStepsWithin_halted (w : ℕ) (p : Program B r) (N v : ℕ) (d : Data r) :
    expectedStepsWithin w p N (.halted v d) = 0 := by
  simp [expectedStepsWithin, PMF.toOuterMeasure_pure_apply]

@[simp]
theorem expectedStepsWithin_faulted (w : ℕ) (p : Program B r) (N : ℕ) :
    expectedStepsWithin w p N .faulted = 0 := by
  simp [expectedStepsWithin, PMF.toOuterMeasure_pure_apply]

theorem expectedStepsWithin_mono (w : ℕ) (p : Program B r) (cfg : RandCfg r) :
    Monotone fun N => expectedStepsWithin w p N cfg := by
  intro N₁ N₂ hN
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hN)

theorem iSup_expectedStepsWithin (w : ℕ) (p : Program B r) (cfg : RandCfg r) :
    (⨆ N : ℕ, expectedStepsWithin w p N cfg) = expectedStepsFrom w p cfg :=
  (ENNReal.tsum_eq_iSup_nat).symm

theorem expectedStepsWithin_le_expectedStepsFrom (w : ℕ) (p : Program B r) (N : ℕ)
    (cfg : RandCfg r) :
    expectedStepsWithin w p N cfg ≤ expectedStepsFrom w p cfg := by
  rw [← iSup_expectedStepsWithin]
  exact le_iSup (fun K => expectedStepsWithin w p K cfg) N

/-- 1-step horizon recursion for `expectedStepsWithin`: at horizon `N + 1`, an active state `s`
incurs `1` step plus the `N`-step continuation expectation. -/
theorem expectedStepsWithin_running_succ (w : ℕ) (p : Program B r) (N : ℕ) (s : State r) :
    expectedStepsWithin w p (N + 1) (.running s) =
      1 + ProbComp.expect (stepRand w p (.running s)) (expectedStepsWithin w p N) := by
  rw [expectedStepsWithin, Finset.sum_range_succ', add_comm]
  have hzero : (runRand w p 0 (.running s)).eval.toOuterMeasure
      {cfg' | ∃ u, cfg' = .running u} = 1 := by simp [PMF.toOuterMeasure_pure_apply]
  rw [hzero]
  simp_rw [runRand_succ, ProbComp.eval_bind, PMF.toOuterMeasure_bind_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
  simp only [ProbComp.expect, expectedStepsWithin, Finset.mul_sum]

theorem expectedStepsWithin_running_le (w : ℕ) (p : Program B r) (N : ℕ) (s : State r) :
    expectedStepsWithin w p N (.running s) ≤
      1 + ProbComp.expect (stepRand w p (.running s)) (expectedStepsWithin w p N) := by
  cases N with
  | zero => simp
  | succ N =>
    rw [expectedStepsWithin_running_succ]
    gcongr
    exact ProbComp.expect_mono fun cfg => expectedStepsWithin_mono w p cfg (Nat.le_succ N)

private theorem expectedStepsWithin_le_of_step {w : ℕ} {p : Program B r} {s s' : State r}
    (hstep : stepRand w p (.running s) = pure (.running s')) (N : ℕ) :
    expectedStepsWithin w p N (.running s) ≤
      1 + expectedStepsWithin w p N (.running s') := by
  refine (expectedStepsWithin_running_le w p N s).trans ?_
  rw [hstep, ProbComp.expect_pure]

private theorem tsum_expectedStepsWithin_le_of_step (w : ℕ) {p : Program B r}
    {pc_from pc_to : ℕ}
    (hstep : ∀ y, stepRand w p (.running ⟨pc_from, y⟩) = pure (.running ⟨pc_to, y⟩))
    (μ : PMF (Data r)) (N : ℕ) :
    (∑' y, μ y * expectedStepsWithin w p N (.running ⟨pc_from, y⟩)) ≤
      1 + ∑' y, μ y * expectedStepsWithin w p N (.running ⟨pc_to, y⟩) := by
  calc
    (∑' y, μ y * expectedStepsWithin w p N (.running ⟨pc_from, y⟩))
      ≤ ∑' y, μ y * (1 + expectedStepsWithin w p N (.running ⟨pc_to, y⟩)) :=
        tsum_le_tsum fun y => mul_le_mul_right (expectedStepsWithin_le_of_step (hstep y) N) _
    _ = 1 + ∑' y, μ y * expectedStepsWithin w p N (.running ⟨pc_to, y⟩) := by
        simp_rw [mul_add, tsum_add, mul_one, μ.tsum_coe]

private theorem evalRand_faulted_eq_zero_of_step {w : ℕ} {p : Program B r} {s s' : State r}
    (hstep : stepRand w p (.running s) = pure (.running s')) {T : ℕ}
    (hcont : ∀ t ≤ T - 1, evalRand w p t s' .faulted = 0) :
    ∀ t ≤ T, evalRand w p t s .faulted = 0
  | 0, _ => by simp [evalRand]
  | k + 1, hk => by
    rw [evalRand, runRand_succ, hstep, pure_bind]
    exact hcont k (by omega)

private theorem iSup_evalRand_halted_le_of_step {w : ℕ} {p : Program B r} {s s' : State r}
    (hstep : stepRand w p (.running s) = pure (.running s')) (v : ℕ) (d : Data r) :
    (⨆ T : ℕ, evalRand w p T s' (.halted v d)) ≤ ⨆ T : ℕ, evalRand w p T s (.halted v d) := by
  refine iSup_le fun T => le_iSup_of_le (T + 1) ?_
  simp only [evalRand, runRand_succ, hstep, pure_bind, le_rfl]

/-! ### Absorbing Markov chain for geometric Las Vegas loops -/

/-- One step of the stopped loop Markov kernel on `Data r`: active states (`cond.Holds x`) step
according to `μ_body x`, while exiting states (`¬cond.Holds x`) are absorbing. -/
noncomputable def loopStepPMF (cond : Cond r) (μ_body : Data r → PMF (Data r)) (x : Data r) :
    PMF (Data r) :=
  open Classical in
  if cond.Holds x then μ_body x else PMF.pure x

theorem loopStepPMF_of_holds {cond : Cond r} {μ_body : Data r → PMF (Data r)} {x : Data r}
    (hc : cond.Holds x) :
    loopStepPMF cond μ_body x = μ_body x := by
  classical
  simp [loopStepPMF, hc]

theorem loopStepPMF_of_not_holds {cond : Cond r} {μ_body : Data r → PMF (Data r)} {x : Data r}
    (hc : ¬cond.Holds x) :
    loopStepPMF cond μ_body x = PMF.pure x := by
  classical
  simp [loopStepPMF, hc]

/-- `K`-step iterate of `loopStepPMF`. -/
noncomputable def loopIterPMF (cond : Cond r) (μ_body : Data r → PMF (Data r)) :
    ℕ → Data r → PMF (Data r)
  | 0, x => PMF.pure x
  | K + 1, x => (loopStepPMF cond μ_body x).bind (loopIterPMF cond μ_body K)

@[simp]
theorem loopIterPMF_zero (cond : Cond r) (μ_body : Data r → PMF (Data r)) (x : Data r) :
    loopIterPMF cond μ_body 0 x = PMF.pure x := rfl

theorem loopIterPMF_succ (cond : Cond r) (μ_body : Data r → PMF (Data r)) (K : ℕ) (x : Data r) :
    loopIterPMF cond μ_body (K + 1) x =
      (loopStepPMF cond μ_body x).bind (loopIterPMF cond μ_body K) := rfl

theorem loopIterPMF_of_not_holds {cond : Cond r} {μ_body : Data r → PMF (Data r)} {x : Data r}
    (hc : ¬cond.Holds x) (K : ℕ) :
    loopIterPMF cond μ_body K x = PMF.pure x := by
  induction K with
  | zero => rfl
  | succ K ih => rw [loopIterPMF_succ, loopStepPMF_of_not_holds hc, PMF.pure_bind, ih]

theorem loopIterPMF_succ_right (cond : Cond r) (μ_body : Data r → PMF (Data r)) (K : ℕ)
    (x : Data r) :
    loopIterPMF cond μ_body (K + 1) x =
      (loopIterPMF cond μ_body K x).bind (loopStepPMF cond μ_body) := by
  induction K generalizing x with
  | zero => simp [loopIterPMF]
  | succ K ih =>
    rw [loopIterPMF_succ (K := K), PMF.bind_bind]
    exact congrArg ((loopStepPMF cond μ_body x).bind ·) (funext ih)

theorem loopIterPMF_mono_of_not_holds (cond : Cond r) (μ_body : Data r → PMF (Data r))
    (x : Data r) {y : Data r} (hy : ¬cond.Holds y) :
    Monotone fun K => loopIterPMF cond μ_body K x y := by
  refine monotone_nat_of_le_succ fun K => ?_
  rw [loopIterPMF_succ_right, PMF.bind_apply]
  have hself : loopIterPMF cond μ_body K x y * loopStepPMF cond μ_body y y =
      loopIterPMF cond μ_body K x y := by
    rw [loopStepPMF_of_not_holds hy, PMF.pure_apply_self, mul_one]
  exact hself ▸ le_tsum
    (f := fun z => loopIterPMF cond μ_body K x z * loopStepPMF cond μ_body z y) y

theorem loopIterPMF_indicator_mono (cond : Cond r) (μ_body : Data r → PMF (Data r))
    (x y : Data r) :
    Monotone fun K => Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y := by
  intro K₁ K₂ hK
  by_cases hy : y ∈ {z | ¬cond.Holds z}
  · simpa only [Set.indicator_of_mem hy] using loopIterPMF_mono_of_not_holds cond μ_body x hy hK
  · simp [Set.indicator_of_notMem hy]

/-- Combined loop state invariant: either active (`cond.Holds x ∧ I x`) or exited
(`¬cond.Holds x ∧ Q x`). -/
def LoopStateInv (cond : Cond r) (I Q : Data r → Prop) (x : Data r) : Prop :=
  (cond.Holds x ∧ I x) ∨ (¬cond.Holds x ∧ Q x)

/-- A property `S` that every active body step preserves holds on the whole support of every
loop iterate started from a state satisfying `S` and the loop state invariant. -/
private theorem loopIterPMF_support_of_preserves {cond : Cond r} {I Q S : Data r → Prop}
    {μ_body : Data r → PMF (Data r)}
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (hS : ∀ x, I x → cond.Holds x → S x → ∀ y ∈ (μ_body x).support, S y)
    (K : ℕ) {x : Data r} (hx : LoopStateInv cond I Q x) (hSx : S x) :
    ∀ y ∈ (loopIterPMF cond μ_body K x).support, S y := by
  induction K generalizing x with
  | zero => intro y hy; supp_cases hy [loopIterPMF_zero]; exact hSx
  | succ K ih =>
    intro y hy
    supp_cases hy [loopIterPMF_succ] with ⟨z, hz, hyz⟩
    rcases hx with ⟨hcx, hIx⟩ | ⟨hcx, hQx⟩
    · rw [loopStepPMF_of_holds hcx] at hz
      exact ih (hinv x hIx hcx z hz) (hS x hIx hcx hSx z hz) y hyz
    · supp_cases hz [loopStepPMF_of_not_holds hcx]
      exact ih (Or.inr ⟨hcx, hQx⟩) hSx y hyz

theorem loopIterPMF_support_inv {cond : Cond r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)}
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (K : ℕ) {x : Data r} (hx : LoopStateInv cond I Q x) :
    ∀ y ∈ (loopIterPMF cond μ_body K x).support, LoopStateInv cond I Q y :=
  loopIterPMF_support_of_preserves hinv (fun x hIx hcx _ => hinv x hIx hcx) K hx hx

private theorem pmf_step_drift_bound (μ : PMF (Data r)) (cond : Cond r)
    {C p_exit : ℝ≥0∞} (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hp_exit : p_exit ≤ μ.toOuterMeasure {y | ¬cond.Holds y}) :
    C + ∑' y, μ y * (if cond.Holds y then C / p_exit else 0) ≤ C / p_exit := by
  have hact : (∑' y, μ y * (if cond.Holds y then C / p_exit else 0)) =
      μ.toOuterMeasure {y | cond.Holds y} * (C / p_exit) := by
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun y => by by_cases hc : cond.Holds y <;> simp [hc]
  calc C + ∑' y, μ y * (if cond.Holds y then C / p_exit else 0)
      = (p_exit + μ.toOuterMeasure {y | cond.Holds y}) * (C / p_exit) := by
        rw [hact, add_mul, mul_comm p_exit, ENNReal.div_mul_cancel hp_pos.ne' hp_top]
    _ ≤ (μ.toOuterMeasure {y | cond.Holds y}ᶜ +
          μ.toOuterMeasure {y | cond.Holds y}) * (C / p_exit) :=
        mul_le_mul_left (add_le_add hp_exit le_rfl) _
    _ = C / p_exit := by
        rw [add_comm, Cslib.Probability.PMF.toOuterMeasure_add_compl_ennreal, one_mul]

/-- Expected number of active loop iterations within the first `N` steps of `loopIterPMF`. -/
private noncomputable def loopActiveSteps (cond : Cond r) (μ_body : Data r → PMF (Data r))
    (N : ℕ) (x : Data r) : ℝ≥0∞ :=
  ∑ K ∈ Finset.range N, (loopIterPMF cond μ_body K x).toOuterMeasure {y | cond.Holds y}

private theorem loopActiveSteps_le {cond : Cond r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x → p_exit ≤ (μ_body x).toOuterMeasure {y | ¬cond.Holds y})
    (N : ℕ) {x : Data r} (hx : LoopStateInv cond I Q x) :
    loopActiveSteps cond μ_body N x ≤ if cond.Holds x then 1 / p_exit else 0 := by
  induction N generalizing x with
  | zero => simp [loopActiveSteps]
  | succ N ih =>
    rcases hx with ⟨hcx, hIx⟩ | ⟨hcx, _⟩
    · simp only [hcx, ↓reduceIte, loopActiveSteps, Finset.sum_range_succ', loopIterPMF_zero,
        PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, add_comm]
      simp_rw [loopIterPMF_succ, loopStepPMF_of_holds hcx, PMF.toOuterMeasure_bind_apply]
      rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
      simp_rw [← Finset.mul_sum]
      exact (add_le_add le_rfl (Cslib.Probability.PMF.tsum_mul_mono_support (μ_body x) fun z hz =>
        ih (hinv x hIx hcx z hz))).trans
        (pmf_step_drift_bound (μ_body x) cond hp_pos hp_top (hp_exit x hIx hcx))
    · simp only [hcx, ↓reduceIte, nonpos_iff_eq_zero, loopActiveSteps]
      exact Finset.sum_eq_zero fun K _ => by
        simp [loopIterPMF_of_not_holds hcx, PMF.toOuterMeasure_pure_apply, hcx]

theorem hasSum_loopExitDensity {cond : Cond r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x → p_exit ≤ (μ_body x).toOuterMeasure {y | ¬cond.Holds y})
    {x : Data r} (hx : LoopStateInv cond I Q x) :
    HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y) 1 := by
  rw [CompleteLattice.summable.hasSum_iff,
    ENNReal.tsum_iSup_of_monotone (loopIterPMF_indicator_mono cond μ_body x)]
  simp_rw [← PMF.toOuterMeasure_apply]
  set b := ⨆ K : ℕ, (loopIterPMF cond μ_body K x).toOuterMeasure {z | ¬cond.Holds z}
  refine le_antisymm (iSup_le fun _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
    (tsub_eq_zero_iff_le.mp <| by_contra fun hne => ?_)
  have hN : ∀ N : ℕ, (N : ℝ≥0∞) * (1 - b) ≤ 1 / p_exit := fun N => by
    have hconst : (N : ℝ≥0∞) * (1 - b) = ∑ _ ∈ Finset.range N, (1 - b) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsum : (N : ℝ≥0∞) * (1 - b) ≤ loopActiveSteps cond μ_body N x := by
      rw [hconst]
      refine Finset.sum_le_sum fun K _ => tsub_le_iff_left.mpr ?_
      have hc := Cslib.Probability.PMF.toOuterMeasure_add_compl_ennreal
        (loopIterPMF cond μ_body K x) {z | cond.Holds z}
      have hK := le_iSup
        (fun J => (loopIterPMF cond μ_body J x).toOuterMeasure {z | ¬cond.Holds z}) K
      exact hc.ge.trans (by rw [add_comm]; exact add_le_add hK le_rfl)
    exact hsum.trans <| (loopActiveSteps_le hp_pos hp_top hinv hp_exit N hx).trans
      (by split_ifs <;> simp)
  exact ENNReal.div_ne_top ENNReal.one_ne_top hp_pos.ne' <| top_le_iff.mp <| by
    rw [← ENNReal.top_mul hne, ← ENNReal.iSup_natCast, ENNReal.iSup_mul]
    exact iSup_le hN

/-- Limiting exit distribution of `Code.loop cond body` starting from `x` under one-step body
distribution family `μ_body`. -/
noncomputable def loopExitPMF (cond : Cond r) (μ_body : Data r → PMF (Data r)) (x : Data r) :
    PMF (Data r) :=
  open Classical in
  if h : HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y) 1 then
    ⟨_, h⟩
  else
    PMF.pure x

theorem loopExitPMF_apply_of_hasSum {cond : Cond r} {μ_body : Data r → PMF (Data r)} {x : Data r}
    (h : HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y) 1)
    (y : Data r) :
    loopExitPMF cond μ_body x y =
      ⨆ K : ℕ, Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y := by
  classical simp only [loopExitPMF, h, ↓reduceDIte]; rfl

theorem loopExitPMF_of_not_holds {cond : Cond r} {μ_body : Data r → PMF (Data r)} {x : Data r}
    (hc : ¬cond.Holds x) :
    loopExitPMF cond μ_body x = PMF.pure x := by
  have hfun : (fun y => ⨆ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y) = PMF.pure x :=
    funext fun y => by
      suffices ∀ K, Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y =
          PMF.pure x y by simp [this]
      intro K; rw [loopIterPMF_of_not_holds hc]
      by_cases hyx : y = x <;> simp [hyx, hc, PMF.pure_apply]
  ext y; rw [loopExitPMF_apply_of_hasSum (hfun ▸ (PMF.pure x).2), congrFun hfun y]

theorem loopExitPMF_of_holds {cond : Cond r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x → p_exit ≤ (μ_body x).toOuterMeasure {y | ¬cond.Holds y})
    {x : Data r} (hIx : I x) (hcx : cond.Holds x) :
    loopExitPMF cond μ_body x = (μ_body x).bind (loopExitPMF cond μ_body) := by
  ext y
  rw [loopExitPMF_apply_of_hasSum
    (hasSum_loopExitDensity hp_pos hp_top hinv hp_exit (Or.inl ⟨hcx, hIx⟩)), PMF.bind_apply]
  have hshift : (⨆ K : ℕ, Set.indicator {z | ¬cond.Holds z}
      (loopIterPMF cond μ_body K x) y) =
      ⨆ K : ℕ, Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body (K + 1) x) y :=
    le_antisymm
      (iSup_le fun K => le_iSup_of_le K
        (loopIterPMF_indicator_mono cond μ_body x y (Nat.le_succ K)))
      (iSup_le fun K => le_iSup_of_le (K + 1) le_rfl)
  have hstep (K : ℕ) : Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body (K + 1) x) y =
      ∑' z, μ_body x z * Set.indicator {w' | ¬cond.Holds w'} (loopIterPMF cond μ_body K z) y := by
    rw [loopIterPMF_succ, loopStepPMF_of_holds hcx]
    by_cases hy : ¬cond.Holds y <;> simp [hy, PMF.bind_apply]
  rw [hshift]; simp_rw [hstep]
  rw [← ENNReal.tsum_iSup_of_monotone
    (f := fun K z => μ_body x z *
      Set.indicator {w' | ¬cond.Holds w'} (loopIterPMF cond μ_body K z) y)
    (fun z _ _ hK => mul_le_mul_right (loopIterPMF_indicator_mono cond μ_body z y hK) _)]
  simp_rw [← ENNReal.mul_iSup]
  exact Cslib.Probability.PMF.tsum_mul_congr_support (μ_body x) fun z hz =>
    (loopExitPMF_apply_of_hasSum
      (hasSum_loopExitDensity hp_pos hp_top hinv hp_exit (hinv x hIx hcx z hz)) y).symm

theorem mem_support_loopExitPMF {cond : Cond r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x → p_exit ≤ (μ_body x).toOuterMeasure {y | ¬cond.Holds y})
    {x : Data r} (hx : LoopStateInv cond I Q x)
    {y : Data r} (hy : y ∈ (loopExitPMF cond μ_body x).support) :
    (¬cond.Holds y ∧ Q y) ∧ ∃ K, y ∈ (loopIterPMF cond μ_body K x).support := by
  rw [PMF.mem_support_iff,
    loopExitPMF_apply_of_hasSum (hasSum_loopExitDensity hp_pos hp_top hinv hp_exit hx)] at hy
  have ⟨K, hK⟩ : ∃ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y ≠ 0 := by
    by_contra! h
    exact hy (nonpos_iff_eq_zero.mp (iSup_le fun K => (h K).le))
  rw [Set.indicator_apply_ne_zero] at hK
  rcases loopIterPMF_support_inv hinv K hx y hK.2 with ⟨hcy, _⟩ | ⟨_, hQy⟩
  · exact absurd hcy hK.1
  · exact ⟨⟨hK.1, hQy⟩, K, hK.2⟩

/-! ### Compositional distributional execution (`ExecCodeDist`) -/

/-- `ExecCodeDist w c x μ T`: at word size `w`, running structured program `c` from data `x`
terminates almost surely without faulting, realizes exit distribution `μ : PMF (Data r)` at the
fallthrough address `pc + c.size` of any containing flat program, and uses at most `T : ℝ≥0∞`
expected instructions.

Unlike `ExecRand`, which requires a finite-depth computation tree, `ExecCodeDist` includes
unbounded Las Vegas `while` loops whose each active iteration exits with probability bounded below
by `p_exit > 0` (`ExecCodeDist.loop_geometric`). -/
inductive ExecCodeDist {B : Basis} {r : ℕ} (w : ℕ) : Code B r → Data r → PMF (Data r) →
    ℝ≥0∞ → Prop where
  | of_execRand {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)} :
      ExecRand w c x m →
      ExecCodeDist w c x (Prod.fst <$> m).eval (ProbComp.expect m fun z => (z.2 : ℝ≥0∞))
  | mono {c : Code B r} {x : Data r} {μ : PMF (Data r)} {T T' : ℝ≥0∞} :
      ExecCodeDist w c x μ T → T ≤ T' → ExecCodeDist w c x μ T'
  | seq {c₁ c₂ : Code B r} {x : Data r} {μ₁ : PMF (Data r)}
      {μ₂ : Data r → PMF (Data r)} {T₁ : ℝ≥0∞} {T₂ : Data r → ℝ≥0∞} :
      ExecCodeDist w c₁ x μ₁ T₁ →
      (∀ y ∈ μ₁.support, ExecCodeDist w c₂ y (μ₂ y) (T₂ y)) →
      ExecCodeDist w (.seq c₁ c₂) x (μ₁.bind μ₂) (T₁ + ∑' y, μ₁ y * T₂ y)
  | branch_pos {cond : Cond r} {pos neg : Code B r} {x : Data r}
      {μ : PMF (Data r)} {T : ℝ≥0∞} :
      cond.Holds x → ExecCodeDist w pos x μ T →
      ExecCodeDist w (.branch cond pos neg) x μ (T + 1)
  | branch_neg {cond : Cond r} {pos neg : Code B r} {x : Data r}
      {μ : PMF (Data r)} {T : ℝ≥0∞} :
      ¬cond.Holds x → ExecCodeDist w neg x μ T →
      ExecCodeDist w (.branch cond pos neg) x μ (T + 2)
  | loop_geometric {cond : Cond r} {body : Code B r}
      (I Q : Data r → Prop) {μ_body : Data r → PMF (Data r)} {T_body : Data r → ℝ≥0∞}
      {B_body p_exit : ℝ≥0∞} {x : Data r} :
      0 < p_exit → p_exit ≠ ⊤ →
      (∀ z, I z → cond.Holds z → ExecCodeDist w body z (μ_body z) (T_body z)) →
      (∀ z, I z → cond.Holds z → T_body z ≤ B_body) →
      (∀ z, I z → cond.Holds z →
        ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y) →
      (∀ z, I z → cond.Holds z →
        p_exit ≤ (μ_body z).toOuterMeasure {y | ¬cond.Holds y}) →
      LoopStateInv cond I Q x →
      ExecCodeDist w (.loop cond body) x (loopExitPMF cond μ_body x)
        ((B_body + 2) / p_exit + 2)

namespace ExecCodeDist

variable {w : ℕ} {c c₁ c₂ pos neg body : Code B r} {cond : Cond r} {x y : Data r}
  {μ μ₁ μ' : PMF (Data r)} {T T' T₁ T₂ : ℝ≥0∞}

theorem congr_dist (h : ExecCodeDist w c x μ T) (hμ : μ = μ') (hT : T ≤ T') :
    ExecCodeDist w c x μ' T' := by
  subst hμ
  exact h.mono hT

/-- Every deterministic `Exec w c x y n` gives `ExecCodeDist w c x (PMF.pure y) n`. -/
theorem of_exec {n : ℕ} (h : Exec w c x y n) :
    ExecCodeDist w c x (PMF.pure y) n := by
  simpa [ProbComp.expect_pure] using of_execRand h.execRand

/-- Every deterministic `ExecWithin w c x y n` gives `ExecCodeDist w c x (PMF.pure y) n`. -/
theorem of_execWithin {n : ℕ} (h : ExecWithin w c x y n) :
    ExecCodeDist w c x (PMF.pure y) n := by
  obtain ⟨m, hm, he⟩ := h
  exact (of_exec he).mono (Nat.cast_le.mpr hm)

/-- Single deterministic operation instruction. -/
theorem op {o : Op B r} (ho : o.eval w x = some y) :
    ExecCodeDist w (.op o) x (PMF.pure y) 1 := by
  simpa using of_exec (Exec.op ho)

/-- Single `rand dst src` instruction. -/
theorem rand {dst src : Fin r} (hfit : Fits w (x.regs src)) :
    ExecCodeDist (B := B) w (.rand dst src) x
      ((ProbComp.unifFin (x.regs src)).eval.map fun k => x.set dst k.val) 1 := by
  have h := of_execRand (ExecRand.rand (B := B) (dst := dst) (src := src) hfit)
  refine h.congr_dist ?_ ?_
  · ext z
    simp [ProbComp.eval_map, PMF.map_apply]
  · simp [ProbComp.expect_map, ProbComp.expect_const]

/-- Exiting a loop immediately when `¬cond.Holds x` takes `2` steps and leaves `x` unchanged. -/
theorem loop_exit (hc : ¬cond.Holds x) :
    ExecCodeDist w (.loop cond body) x (PMF.pure x) 2 := by
  simpa using of_exec (Exec.loop_exit hc)

/-- Sequencing with a uniform continuation step bound `T₂`. -/
theorem seq_const {μ₂ : Data r → PMF (Data r)} {T₂ : Data r → ℝ≥0∞} {B₂ : ℝ≥0∞}
    (h₁ : ExecCodeDist w c₁ x μ₁ T₁)
    (h₂ : ∀ y ∈ μ₁.support, ExecCodeDist w c₂ y (μ₂ y) (T₂ y))
    (hB₂ : ∀ y ∈ μ₁.support, T₂ y ≤ B₂) :
    ExecCodeDist w (.seq c₁ c₂) x (μ₁.bind μ₂) (T₁ + B₂) := by
  refine (h₁.seq h₂).mono (add_le_add le_rfl ?_)
  exact Cslib.Probability.PMF.tsum_mul_le_of_support μ₁ hB₂

/-- Sequencing after a deterministic first stage (`PMF.pure y`). -/
theorem seq_pure (h₁ : ExecCodeDist w c₁ x (PMF.pure y) T₁)
    (h₂ : ExecCodeDist w c₂ y μ T₂) :
    ExecCodeDist w (.seq c₁ c₂) x μ (T₁ + T₂) := by
  classical
  have h := h₁.seq (c₂ := c₂) (μ₂ := fun z => if z = y then μ else PMF.pure z)
    (T₂ := fun z => if z = y then T₂ else 0) fun z hz => by
      supp_cases hz
      simpa only [↓reduceIte] using h₂
  exact h.congr_dist (by simp) (by simp)

private theorem mem_support_eval_fst_iff {m : ProbComp (Data r × ℕ)} {y : Data r} :
    y ∈ (Prod.fst <$> m).eval.support ↔ ∃ z ∈ m.support, z.1 = y := by
  simp only [ProbComp.eval_map, PMF.mem_support_map_iff, ProbComp.support_eval]

private theorem eval_fst_bindSteps (m₁ : ProbComp (Data r × ℕ))
    (m₂ : Data r → ProbComp (Data r × ℕ)) (step : ℕ → ℕ → ℕ) :
    (Prod.fst <$> (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, step z₁.2 z₂.2))).eval =
      (Prod.fst <$> m₁).eval.bind (fun y => (Prod.fst <$> m₂ y).eval) := by
  simp only [ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

private theorem expect_snd_bindSteps (m₁ : ProbComp (Data r × ℕ))
    (m₂ : Data r → ProbComp (Data r × ℕ)) (d : ℕ) :
    ProbComp.expect (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + d)) (fun z => (z.2 : ℝ≥0∞)) =
      ProbComp.expect m₁ (fun z => (z.2 : ℝ≥0∞)) + d +
        ∑' y, (Prod.fst <$> m₁).eval y * ProbComp.expect (m₂ y) (fun z => (z.2 : ℝ≥0∞)) := by
  simp only [ProbComp.expect_bind, ProbComp.expect_pure, Nat.cast_add]
  have hinner (z₁ : Data r × ℕ) :
      ProbComp.expect (m₂ z₁.1) (fun z₂ => (z₁.2 : ℝ≥0∞) + (z₂.2 : ℝ≥0∞) + d) =
        ((z₁.2 : ℝ≥0∞) + d) + ProbComp.expect (m₂ z₁.1) (fun z₂ => (z₂.2 : ℝ≥0∞)) := by
    rw [show (fun z₂ : Data r × ℕ => (z₁.2 : ℝ≥0∞) + (z₂.2 : ℝ≥0∞) + d) =
        fun z₂ => ((z₁.2 : ℝ≥0∞) + d) + (z₂.2 : ℝ≥0∞) from funext fun _ => by ac_rfl,
      ProbComp.expect_add, ProbComp.expect_const]
  simp_rw [hinner]
  rw [ProbComp.expect_add, ProbComp.expect_add, ProbComp.expect_const,
    ← ProbComp.expect_map Prod.fst m₁ (fun y => ProbComp.expect (m₂ y) fun z₂ => (z₂.2 : ℝ≥0∞))]
  rfl

/-- Eliminate `ExecCodeDist` into primitive instruction/loop cases, discharging `of_execRand` once
via structural induction on `ExecRand`. -/
private theorem elim_prim {P : Code B r → Data r → PMF (Data r) → ℝ≥0∞ → Prop}
    (h_congr : ∀ {c x μ μ' T T'}, P c x μ T → μ = μ' → T ≤ T' → P c x μ' T')
    (h_op : ∀ {o : Op B r} {x y : Data r}, o.eval w x = some y → P (.op o) x (PMF.pure y) 1)
    (h_rand : ∀ {dst src : Fin r} {x : Data r}, Fits w (x.regs src) →
      P (.rand dst src) x ((ProbComp.unifFin (x.regs src)).eval.map fun k => x.set dst k.val) 1)
    (h_seq : ∀ {c₁ c₂ : Code B r} {x : Data r} {μ₁ : PMF (Data r)}
      {μ₂ : Data r → PMF (Data r)} {T₁ : ℝ≥0∞} {T₂ : Data r → ℝ≥0∞},
      P c₁ x μ₁ T₁ → (∀ y ∈ μ₁.support, P c₂ y (μ₂ y) (T₂ y)) →
      P (.seq c₁ c₂) x (μ₁.bind μ₂) (T₁ + ∑' y, μ₁ y * T₂ y))
    (h_branch_pos : ∀ {cond : Cond r} {pos neg : Code B r} {x : Data r}
      {μ : PMF (Data r)} {T : ℝ≥0∞},
      cond.Holds x → P pos x μ T → P (.branch cond pos neg) x μ (T + 1))
    (h_branch_neg : ∀ {cond : Cond r} {pos neg : Code B r} {x : Data r}
      {μ : PMF (Data r)} {T : ℝ≥0∞},
      ¬cond.Holds x → P neg x μ T → P (.branch cond pos neg) x μ (T + 2))
    (h_loop_exit : ∀ {cond : Cond r} {body : Code B r} {x : Data r},
      ¬cond.Holds x → P (.loop cond body) x (PMF.pure x) 2)
    (h_loop_iter : ∀ {cond : Cond r} {body : Code B r} {x : Data r} {μb : PMF (Data r)}
      {μl : Data r → PMF (Data r)} {Tb : ℝ≥0∞} {Tl : Data r → ℝ≥0∞},
      cond.Holds x → P body x μb Tb →
      (∀ y ∈ μb.support, P (.loop cond body) y (μl y) (Tl y)) →
      P (.loop cond body) x (μb.bind μl) (Tb + 2 + ∑' y, μb y * Tl y))
    (h_loop_geom : ∀ {cond : Cond r} {body : Code B r}
      (I Q : Data r → Prop) {μ_body : Data r → PMF (Data r)} {T_body : Data r → ℝ≥0∞}
      {B_body p_exit : ℝ≥0∞} {x : Data r},
      0 < p_exit → p_exit ≠ ⊤ →
      (∀ z, I z → cond.Holds z → P body z (μ_body z) (T_body z)) →
      (∀ z, I z → cond.Holds z → T_body z ≤ B_body) →
      (∀ z, I z → cond.Holds z → ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y) →
      (∀ z, I z → cond.Holds z → p_exit ≤ (μ_body z).toOuterMeasure {y | ¬cond.Holds y}) →
      LoopStateInv cond I Q x →
      P (.loop cond body) x (loopExitPMF cond μ_body x) ((B_body + 2) / p_exit + 2))
    (h : ExecCodeDist w c x μ T) : P c x μ T := by
  induction h with
  | @of_execRand c x m hm =>
    induction hm with
    | op ho => simpa [ProbComp.expect_pure] using h_op ho
    | @rand dst src x hfit =>
      exact h_congr (h_rand (dst := dst) hfit)
        (by ext z; simp [ProbComp.eval_map, PMF.map_apply])
        (by simp [ProbComp.expect_map, ProbComp.expect_const])
    | @seq c₁ c₂ x m₁ m₂ _ _ ih₁ ih₂ =>
      exact h_congr (h_seq (T₂ := fun y => ProbComp.expect (m₂ y) fun z => (z.2 : ℝ≥0∞))
        ih₁ fun _ hy => let ⟨z, hz, hzy⟩ := mem_support_eval_fst_iff.mp hy; hzy ▸ ih₂ z hz)
        (eval_fst_bindSteps m₁ m₂ (· + ·)).symm (by simpa using (expect_snd_bindSteps m₁ m₂ 0).ge)
    | @branch_pos cond pos neg x m hc _ ih =>
      exact h_congr (h_branch_pos (neg := neg) hc ih) (by simp [Functor.map_map])
        (by simp [ProbComp.expect_map, ProbComp.expect_add, ProbComp.expect_const])
    | @branch_neg cond pos neg x m hc _ ih =>
      exact h_congr (h_branch_neg (pos := pos) hc ih) (by simp [Functor.map_map])
        (by simp [ProbComp.expect_map, ProbComp.expect_add, ProbComp.expect_const])
    | @loop_exit cond body x hc =>
      simpa [ProbComp.expect_pure] using h_loop_exit (body := body) hc
    | @loop_iter cond body x mb ml hc _ _ ihb ihl =>
      exact h_congr (h_loop_iter (Tl := fun y => ProbComp.expect (ml y) fun z => (z.2 : ℝ≥0∞))
        hc ihb fun _ hy => let ⟨z, hz, hzy⟩ := mem_support_eval_fst_iff.mp hy; hzy ▸ ihl z hz)
        (eval_fst_bindSteps mb ml (fun a b => a + b + 2)).symm
        (by simpa using (expect_snd_bindSteps mb ml 2).ge)
  | mono _ hle ih => exact h_congr ih rfl hle
  | seq _ _ ih₁ ih₂ => exact h_seq ih₁ ih₂
  | branch_pos hc _ ih => exact h_branch_pos hc ih
  | branch_neg hc _ ih => exact h_branch_neg hc ih
  | loop_geometric I Q hp_pos hp_top _ hB hinv hp_exit hx ih_body =>
    exact h_loop_geom I Q hp_pos hp_top ih_body hB hinv hp_exit hx

private theorem support_of_execRand_preserves {R : Code B r → Prop} {S : Data r → Prop}
    (h_rand : ∀ {c : Code B r} {u : Data r} {m : ProbComp (Data r × ℕ)},
      ExecRand w c u m → R c → S u → ∀ z ∈ m.support, S z.1)
    (h_seq : ∀ {c₁ c₂}, R (.seq c₁ c₂) → R c₁ ∧ R c₂)
    (h_bpos : ∀ {cond pos neg}, R (.branch cond pos neg) → R pos)
    (h_bneg : ∀ {cond pos neg}, R (.branch cond pos neg) → R neg)
    (h_loop : ∀ {cond body}, R (.loop cond body) → R body)
    (h : ExecCodeDist w c x μ T) (hR : R c) (hS : S x) :
    ∀ y ∈ μ.support, S y := by
  induction h with
  | of_execRand hm =>
    intro _ hy; obtain ⟨z, hz, rfl⟩ := mem_support_eval_fst_iff.mp hy; exact h_rand hm hR hS z hz
  | mono _ _ ih => exact ih hR hS
  | seq _ _ ih₁ ih₂ =>
    intro y hy; supp_cases hy with ⟨z, hz, hyz⟩
    exact ih₂ z hz (h_seq hR).2 (ih₁ (h_seq hR).1 hS z hz) y hyz
  | branch_pos _ _ ih => exact ih (h_bpos hR) hS
  | branch_neg _ _ ih => exact ih (h_bneg hR) hS
  | loop_geometric _ _ hp_pos hp_top _ _ hinv hp_exit hx_inv ih_body =>
    intro y hy
    obtain ⟨_, K, hK⟩ := mem_support_loopExitPMF hp_pos hp_top hinv hp_exit hx_inv hy
    exact loopIterPMF_support_of_preserves hinv
      (fun z hIz hcz hz _ hu => ih_body z hIz hcz (h_loop hR) hz _ hu) K hx_inv hS y hK

/-- Every state in the support of `μ` preserves `Data.Bounded w` when `x.Bounded w`. -/
theorem bounded (h : ExecCodeDist w c x μ T) (hx : x.Bounded w) :
    ∀ y ∈ μ.support, y.Bounded w :=
  h.support_of_execRand_preserves (R := fun _ => True)
    (fun hm _ hu _ hz => hm.bounded hu hz) (fun _ => ⟨trivial, trivial⟩)
    (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) trivial hx

/-- Any register `i` not written by `c` (`c.Preserves i`) is preserved across the support of `μ`. -/
theorem regs_eq {i : Fin r} (h : ExecCodeDist w c x μ T) (hi : c.Preserves i) :
    ∀ y ∈ μ.support, y.regs i = x.regs i :=
  h.support_of_execRand_preserves (R := (·.Preserves i))
    (fun hm hR hu _ hz => (hm.regs_eq hR hz).trans hu) id And.left And.right id hi rfl

/-- Distributional executions transfer along any defined-evaluation basis simulation
`ψ : B.Simulates B'`. -/
theorem mapSimulates {B' : Basis} (ψ : B.Simulates B') (h : ExecCodeDist w c x μ T) :
    ExecCodeDist w (c.mapSimulates ψ) x μ T := by
  induction h with
  | of_execRand hm => exact of_execRand (hm.mapSimulates ψ)
  | mono _ hle ih => exact ih.mono hle
  | seq _ _ ih₁ ih₂ => exact ih₁.seq ih₂
  | branch_pos hc _ ih => exact branch_pos hc ih
  | branch_neg hc _ ih => exact branch_neg hc ih
  | loop_geometric I Q hp_pos hp_top _ hB hinv hp_exit hx ih_body =>
    exact loop_geometric I Q hp_pos hp_top ih_body hB hinv hp_exit hx

private theorem extend_left_injective {r' : ℕ} {f : Fin r → Fin r'} (hf : f.Injective)
    (x : Data r') : Function.Injective (fun y : Data r => y.extend f x) := by
  intro y₁ y₂ h
  have h' := congrArg (Data.comap f) h
  simpa [Data.comap_extend hf] using h'

private theorem pmf_map_apply_not_mem_range {α β : Type*} (p : PMF α) (g : α → β) {b : β}
    (hb : b ∉ Set.range g) :
    p.map g b = 0 :=
  (PMF.apply_eq_zero_iff _ _).mpr fun h => by
    supp_cases h with ⟨a, _, rfl⟩
    exact hb ⟨a, rfl⟩

private theorem loopIterPMF_rename {r' : ℕ} {f : Fin r → Fin r'} (hf : f.Injective)
    (cond : Cond r) (μ_body : Data r → PMF (Data r)) (x : Data r') (K : ℕ) (u : Data r) :
    loopIterPMF (cond.rename f) (fun x' => (μ_body (x'.comap f)).map (fun y => y.extend f x))
      K (u.extend f x) =
      (loopIterPMF cond μ_body K u).map (fun y => y.extend f x) := by
  induction K generalizing u with
  | zero => simp [loopIterPMF]
  | succ K ih =>
    have hcond : (cond.rename f).Holds (u.extend f x) ↔ cond.Holds u := by
      rw [Cond.holds_rename, Data.comap_extend hf]
    by_cases hc : cond.Holds u
    · rw [loopIterPMF_succ, loopStepPMF_of_holds (hcond.mpr hc), Data.comap_extend hf,
        loopIterPMF_succ, loopStepPMF_of_holds hc, PMF.bind_map, PMF.map_bind]
      exact congrArg ((μ_body u).bind ·) (funext ih)
    · rw [loopIterPMF_succ, loopStepPMF_of_not_holds (mt hcond.mp hc),
        loopIterPMF_succ, loopStepPMF_of_not_holds hc, PMF.pure_bind, PMF.pure_bind, ih]

private theorem rename_loop_geometric {r' : ℕ} {f : Fin r → Fin r'} (hf : f.Injective)
    {cond : Cond r} {body : Code B r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {T_body : Data r → ℝ≥0∞}
    {B_body p_exit : ℝ≥0∞} {x : Data r'}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hB : ∀ z, I z → cond.Holds z → T_body z ≤ B_body)
    (hinv : ∀ z, I z → cond.Holds z → ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ z, I z → cond.Holds z → p_exit ≤ (μ_body z).toOuterMeasure {y | ¬cond.Holds y})
    (ih_body : ∀ z, I z → cond.Holds z → ∀ {x' : Data r'}, x'.comap f = z →
      ExecCodeDist w (body.rename f) x' ((μ_body z).map fun y => y.extend f x') (T_body z))
    (hx_inv : LoopStateInv cond I Q (x.comap f)) :
    ExecCodeDist w (.loop (cond.rename f) (body.rename f)) x
      ((loopExitPMF cond μ_body (x.comap f)).map fun y => y.extend f x)
      ((B_body + 2) / p_exit + 2) := by
  let g : Data r → Data r' := (·.extend f x)
  have hg : g.Injective := extend_left_injective hf x
  have hcond (u : Data r) : (cond.rename f).Holds (g u) ↔ cond.Holds u := by
    rw [Cond.holds_rename, Data.comap_extend hf]
  let I' : Data r' → Prop := fun x' => ∃ u, I u ∧ x' = g u
  let Q' : Data r' → Prop := fun x' => ∃ u, Q u ∧ x' = g u
  let μ_body' : Data r' → PMF (Data r') := fun x' => (μ_body (x'.comap f)).map g
  have hinv_img {u : Data r} (h : LoopStateInv cond I Q u) :
      LoopStateInv (cond.rename f) I' Q' (g u) :=
    h.elim (fun ⟨hc, hI⟩ => Or.inl ⟨(hcond u).mpr hc, u, hI, rfl⟩)
      (fun ⟨hc, hQ⟩ => Or.inr ⟨mt (hcond u).mp hc, u, hQ, rfl⟩)
  have hinv' : ∀ z', I' z' → (cond.rename f).Holds z' →
      ∀ y' ∈ (μ_body' z').support, LoopStateInv (cond.rename f) I' Q' y' := by
    rintro _ ⟨u, hIu, rfl⟩ hcz' y' hy'
    dsimp only [μ_body', g] at hy'
    rw [Data.comap_extend hf] at hy'
    supp_cases hy' with ⟨y, hy, rfl⟩
    exact hinv_img (hinv u hIu ((hcond u).mp hcz') y hy)
  have hp_exit' : ∀ z', I' z' → (cond.rename f).Holds z' →
      p_exit ≤ (μ_body' z').toOuterMeasure {y' | ¬(cond.rename f).Holds y'} := by
    rintro _ ⟨u, hIu, rfl⟩ hcz'
    have hset : g ⁻¹' {y' | ¬(cond.rename f).Holds y'} = {y | ¬cond.Holds y} :=
      Set.ext fun y => by simp [hcond y]
    simpa only [μ_body', g, Data.comap_extend hf, PMF.toOuterMeasure_map_apply, hset] using
      hp_exit u hIu ((hcond u).mp hcz')
  have hx_inv' : LoopStateInv (cond.rename f) I' Q' x :=
    Data.extend_comap hf x ▸ hinv_img hx_inv
  refine (loop_geometric I' Q' hp_pos hp_top (μ_body := μ_body')
    (T_body := fun x' => T_body (x'.comap f)) (B_body := B_body) (x := x)
    (fun _ ⟨u, hIu, hzu⟩ hcz' => hzu ▸ by
      simpa only [μ_body', g, Data.comap_extend hf, Data.extend_extend hf] using
        ih_body u hIu ((hcond u).mp (hzu ▸ hcz')) (Data.comap_extend hf u x))
    (fun _ ⟨u, hIu, hzu⟩ hcz' => hzu ▸ by
      simpa only [g, Data.comap_extend hf] using hB u hIu ((hcond u).mp (hzu ▸ hcz')))
    hinv' hp_exit' hx_inv').congr_dist (PMF.ext fun y' => ?_) le_rfl
  rw [loopExitPMF_apply_of_hasSum (hasSum_loopExitDensity hp_pos hp_top hinv' hp_exit' hx_inv')]
  have hiter (K : ℕ) : loopIterPMF (cond.rename f) μ_body' K x =
      (loopIterPMF cond μ_body K (x.comap f)).map g := by
    conv_lhs => rw [← Data.extend_comap hf x]
    exact loopIterPMF_rename hf cond μ_body x K (x.comap f)
  by_cases hy' : y' ∈ Set.range g
  · obtain ⟨y, rfl⟩ := hy'
    rw [Probability.PMF.map_apply_of_injective _ hg,
      loopExitPMF_apply_of_hasSum (hasSum_loopExitDensity hp_pos hp_top hinv hp_exit hx_inv)]
    refine iSup_congr fun K => ?_
    rw [hiter K]
    by_cases hcy : ¬cond.Holds y
    · simp [hcy, mt (hcond y).mp hcy, Probability.PMF.map_apply_of_injective _ hg]
    · simp [Set.indicator_of_notMem, hcy, hcond y]
  · rw [pmf_map_apply_not_mem_range _ g hy']
    refine nonpos_iff_eq_zero.mp <| iSup_le fun K => by
      rw [hiter K]; by_cases hcy' : ¬(cond.rename f).Holds y' <;>
        simp [hcy', pmf_map_apply_not_mem_range _ g hy']

/-- Renaming a distributional execution along an injective register map `f : Fin r → Fin r'`
transforms the output distribution via `Data.extend f x` and preserves the expected step bound. -/
theorem rename {r' : ℕ} {f : Fin r → Fin r'} (hf : f.Injective) {x : Data r'}
    (h : ExecCodeDist w c (x.comap f) μ T) :
    ExecCodeDist w (c.rename f) x (μ.map fun y => y.extend f x) T := by
  generalize hx₀ : x.comap f = x₀ at h
  induction h generalizing x with
  | @of_execRand c _ m hm =>
    subst hx₀
    exact (of_execRand (hm.rename hf)).congr_dist
      (by rw [Functor.map_map, ProbComp.eval_map, ProbComp.eval_map, PMF.map_comp]; rfl)
      (by rw [ProbComp.expect_map])
  | mono _ hle ih => exact (ih hx₀).mono hle
  | @seq c₁ c₂ _ μ₁ μ₂ T₁ T₂ _ _ ih₁ ih₂ =>
    subst hx₀
    have hseq := (ih₁ rfl).seq (μ₂ := fun y' => (μ₂ (y'.comap f)).map fun z => z.extend f x)
      (T₂ := fun y' => T₂ (y'.comap f)) fun y' hy' => by
        supp_cases hy' with ⟨y₁, hy₁, rfl⟩
        simpa only [Data.comap_extend hf, Data.extend_extend hf] using
          ih₂ y₁ hy₁ (x := y₁.extend f x) (Data.comap_extend hf y₁ x)
    refine hseq.congr_dist ?_ ?_
    · rw [PMF.map_bind, PMF.bind_map]
      exact congrArg (μ₁.bind ·) (funext fun _ => by simp [Data.comap_extend hf])
    · rw [Cslib.Probability.PMF.tsum_map_mul]; simp [Data.comap_extend hf]
  | branch_pos hc _ ih =>
    subst hx₀; exact branch_pos ((Cond.holds_rename _ _).2 hc) (ih rfl)
  | branch_neg hc _ ih =>
    subst hx₀; exact branch_neg (fun h => hc ((Cond.holds_rename _ _).1 h)) (ih rfl)
  | loop_geometric _ _ hp_pos hp_top _ hB hinv hp_exit hx_inv ih_body =>
    subst hx₀; exact rename_loop_geometric hf hp_pos hp_top hB hinv hp_exit ih_body hx_inv

/-! ### Compilation of `ExecCodeDist` to flat `Program` semantics -/

private theorem expectedStepsWithin_loop_exit {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc))
    {z : Data r} (hcz : ¬cond.Holds z) (N : ℕ) :
    expectedStepsWithin w p N (.running ⟨pc, z⟩) ≤
      2 + expectedStepsWithin w p N (.running ⟨pc + (Code.loop cond body).size, z⟩) :=
  ((expectedStepsWithin_le_of_step (stepRand_loop_not_holds hp hcz) N).trans
    (add_le_add le_rfl (expectedStepsWithin_le_of_step (stepRand_loop_exit_jump hp z) N))).trans_eq
    (by rw [← add_assoc, one_add_one_eq_two])

private theorem expectedStepsWithin_loop_geometric {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {T_body : Data r → ℝ≥0∞} {B_body p_exit : ℝ≥0∞}
    {p : Program B r} {pc N : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc))
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hB : ∀ z, I z → cond.Holds z → T_body z ≤ B_body)
    (hinv : ∀ z, I z → cond.Holds z → ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ z, I z → cond.Holds z → p_exit ≤ (μ_body z).toOuterMeasure {y | ¬cond.Holds y})
    (ih_body : ∀ z, I z → cond.Holds z → ∀ n,
      expectedStepsWithin w p n (.running ⟨pc + 2, z⟩) ≤ T_body z +
        ∑' u, μ_body z u * expectedStepsWithin w p n (.running ⟨pc + 2 + body.size, u⟩))
    (hx_inv : LoopStateInv cond I Q x) :
    expectedStepsWithin w p N (.running ⟨pc, x⟩) ≤ (B_body + 2) / p_exit + 2 +
      ∑' y, loopExitPMF cond μ_body x y *
        expectedStepsWithin w p N (.running ⟨pc + (Code.loop cond body).size, y⟩) := by
  set K_cont : Data r → ℝ≥0∞ := fun y =>
    expectedStepsWithin w p N (.running ⟨pc + (Code.loop cond body).size, y⟩)
  set M := (B_body + 2) / p_exit
  have hmain : ∀ n ≤ N, ∀ z : Data r, LoopStateInv cond I Q z →
      expectedStepsWithin w p n (.running ⟨pc, z⟩) ≤
        (if cond.Holds z then M else 0) + 2 + ∑' y, loopExitPMF cond μ_body z y * K_cont y := by
    intro n; induction n with
    | zero => simp
    | succ n ihn =>
      intro hn z hz_inv
      rcases hz_inv with ⟨hcz, hIz⟩ | ⟨hcz, _⟩
      · simp only [hcz, ↓reduceIte]
        rw [expectedStepsWithin_running_succ, stepRand_loop_holds hp hcz, ProbComp.expect_pure]
        have hbody := (ih_body z hIz hcz n).trans (add_le_add (hB z hIz hcz) le_rfl)
        have hback := tsum_expectedStepsWithin_le_of_step w (stepRand_loop_back hp) (μ_body z) n
        have hih : (∑' u, μ_body z u * expectedStepsWithin w p n (.running ⟨pc, u⟩)) ≤
            (∑' u, μ_body z u * (if cond.Holds u then M else 0)) + 2 +
              ∑' y, loopExitPMF cond μ_body z y * K_cont y :=
          (Cslib.Probability.PMF.tsum_mul_mono_support (μ_body z) fun u hu =>
            ihn (Nat.le_of_succ_le hn) u (hinv z hIz hcz u hu)).trans_eq <| by
            simp_rw [mul_add, tsum_add, ENNReal.tsum_mul_right, (μ_body z).tsum_coe, one_mul,
              loopExitPMF_of_holds hp_pos hp_top hinv hp_exit hIz hcz,
              Cslib.Probability.PMF.tsum_bind_mul]
        have hdrift := pmf_step_drift_bound (μ_body z) cond (C := B_body + 2)
          hp_pos hp_top (hp_exit z hIz hcz)
        calc 1 + expectedStepsWithin w p n (.running ⟨pc + 2, z⟩)
            ≤ 1 + (B_body + (1 + ∑' u, μ_body z u *
                expectedStepsWithin w p n (.running ⟨pc, u⟩))) :=
              add_le_add le_rfl (hbody.trans (add_le_add le_rfl hback))
          _ = B_body + 2 + ∑' u, μ_body z u * expectedStepsWithin w p n (.running ⟨pc, u⟩) := by
              rw [← one_add_one_eq_two]; ac_rfl
          _ ≤ (B_body + 2 + ∑' u, μ_body z u * (if cond.Holds u then M else 0)) + 2 +
                ∑' y, loopExitPMF cond μ_body z y * K_cont y :=
              (add_le_add le_rfl hih).trans_eq (by ac_rfl)
          _ ≤ M + 2 + ∑' y, loopExitPMF cond μ_body z y * K_cont y :=
              add_le_add (add_le_add hdrift le_rfl) le_rfl
      · classical
        simp only [hcz, ↓reduceIte, zero_add, loopExitPMF_of_not_holds hcz, PMF.pure_apply,
          ite_mul, one_mul, zero_mul, tsum_ite_eq]
        exact (expectedStepsWithin_loop_exit hp hcz (n + 1)).trans
          (add_le_add le_rfl (expectedStepsWithin_mono w p _ hn))
  refine (hmain N le_rfl x hx_inv).trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  split_ifs <;> simp

/-- Finite-horizon Bellman inequality for `ExecCodeDist` inside any containing flat program `p`. -/
theorem expectedStepsWithin_assemble (h : ExecCodeDist w c x μ T) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) (N : ℕ) :
    expectedStepsWithin w p N (.running ⟨pc, x⟩) ≤
      T + ∑' y, μ y * expectedStepsWithin w p N (.running ⟨pc + c.size, y⟩) := by
  revert pc N
  refine h.elim_prim
    (P := fun c x μ T => ∀ {pc : ℕ}, p.Contains pc (c.assemble pc) → ∀ N : ℕ,
      expectedStepsWithin w p N (.running ⟨pc, x⟩) ≤
        T + ∑' y, μ y * expectedStepsWithin w p N (.running ⟨pc + c.size, y⟩))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ _ _ ih hμ hT _ hp N; exact hμ ▸ (ih hp N).trans (add_le_add hT le_rfl)
  · intro _ _ _ ho _ hp N
    classical simpa [Code.size, PMF.pure_apply] using
      expectedStepsWithin_le_of_step (stepRand_op (s := ⟨_, _⟩) hp.head ho) N
  · intro _ _ _ hfit _ hp N
    refine (expectedStepsWithin_running_le w p N _).trans_eq ?_
    rw [stepRand_rand_of_fits hp.head hfit, ProbComp.expect_bind]
    simp only [ProbComp.expect_pure]
    simp only [Code.size, Cslib.Probability.PMF.tsum_map_mul, ProbComp.expect]
  · intro c₁ c₂ _ μ₁ μ₂ _ _ ih₁ ih₂ pc hp N
    refine (ih₁ hp.append_left N).trans <| (add_le_add le_rfl ?_).trans_eq (add_assoc _ _ _).symm
    refine (Cslib.Probability.PMF.tsum_mul_mono_support μ₁ fun y hy =>
      ih₂ y hy (contains_seq_right hp) N).trans_eq ?_
    simp_rw [mul_add, tsum_add]
    congr 1; simp only [Code.size, Nat.add_assoc]
    exact (Cslib.Probability.PMF.tsum_bind_mul μ₁ μ₂ _).symm
  · intro _ pos neg _ _ _ hc ih pc hp N
    have hpc : pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) := by omega
    refine ((expectedStepsWithin_le_of_step (stepRand_branch_pos hp hc) N).trans
      (add_le_add le_rfl (ih (contains_branch_pos hp) N))).trans_eq ?_
    simp only [Code.size, hpc]; ac_rfl
  · intro _ _ _ _ μ _ hc ih _ hp N
    exact ((expectedStepsWithin_le_of_step (stepRand_branch_neg hp hc) N).trans
      (add_le_add le_rfl ((ih hp.cons_tail.append_left N).trans (add_le_add le_rfl
        (tsum_expectedStepsWithin_le_of_step w (stepRand_branch_neg_jump hp) μ N))))).trans_eq <|
      by rw [← one_add_one_eq_two]; ac_rfl
  · intro _ _ _ hc _ hp N
    classical simpa [PMF.pure_apply] using expectedStepsWithin_loop_exit hp hc N
  · intro _ _ _ μb μl _ _ hc ihb ihl _ hp N
    refine ((expectedStepsWithin_le_of_step (stepRand_loop_holds hp hc) N).trans
      (add_le_add le_rfl ((ihb (contains_loop_body hp) N).trans (add_le_add le_rfl <|
        (tsum_expectedStepsWithin_le_of_step w (stepRand_loop_back hp) μb N).trans
          (add_le_add le_rfl (Cslib.Probability.PMF.tsum_mul_mono_support μb fun y hy =>
            ihl y hy hp N)))))).trans_eq ?_
    simp_rw [mul_add, tsum_add, Cslib.Probability.PMF.tsum_bind_mul]
    rw [← one_add_one_eq_two]; ac_rfl
  · intro _ _ _ _ _ _ _ _ _ hp_pos hp_top ih_body hB hinv hp_exit hx_inv _ hp N
    exact expectedStepsWithin_loop_geometric hp hp_pos hp_top hB hinv hp_exit
      (fun z hIz hcz n => ih_body z hIz hcz (contains_loop_body hp) n) hx_inv

/-- Full-horizon Bellman inequality for `ExecCodeDist` inside any containing flat program `p`. -/
theorem expectedStepsFrom_assemble (h : ExecCodeDist w c x μ T) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) :
    expectedStepsFrom w p (.running ⟨pc, x⟩) ≤
      T + ∑' y, μ y * expectedStepsFrom w p (.running ⟨pc + c.size, y⟩) := by
  rw [← iSup_expectedStepsWithin w p (.running ⟨pc, x⟩)]
  refine iSup_le fun N => (h.expectedStepsWithin_assemble hp N).trans ?_
  refine add_le_add le_rfl (tsum_le_tsum fun y => mul_le_mul_right ?_ _)
  exact expectedStepsWithin_le_expectedStepsFrom w p N (.running ⟨pc + c.size, y⟩)

/-- Continuation upper-bound form of `expectedStepsFrom_assemble`. -/
theorem expectedStepsFrom_le (h : ExecCodeDist w c x μ T) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) {k : Data r → ℝ≥0∞}
    (hk : ∀ y ∈ μ.support, expectedStepsFrom w p (.running ⟨pc + c.size, y⟩) ≤ k y) :
    expectedStepsFrom w p (.running ⟨pc, x⟩) ≤ T + ∑' y, μ y * k y :=
  (h.expectedStepsFrom_assemble hp).trans
    (add_le_add le_rfl (Cslib.Probability.PMF.tsum_mul_mono_support μ hk))

private theorem evalRand_faulted_loop_exit {p : Program B r} {pc T_hor : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc))
    {z : Data r} (hcz : ¬cond.Holds z)
    (hcont : ∀ t ≤ T_hor, evalRand w p t ⟨pc + (Code.loop cond body).size, z⟩ .faulted = 0) :
    ∀ t ≤ T_hor, evalRand w p t ⟨pc, z⟩ .faulted = 0 :=
  evalRand_faulted_eq_zero_of_step (stepRand_loop_not_holds hp hcz)
    (evalRand_faulted_eq_zero_of_step (stepRand_loop_exit_jump hp z)
      fun t ht => hcont t (by omega))

private theorem evalRand_faulted_loop_geometric {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {p_exit : ℝ≥0∞} {p : Program B r} {pc T_hor : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc))
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ z, I z → cond.Holds z → ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ z, I z → cond.Holds z → p_exit ≤ (μ_body z).toOuterMeasure {y | ¬cond.Holds y})
    (ih_body : ∀ z, I z → cond.Holds z → ∀ k,
      (∀ u ∈ (μ_body z).support, ∀ t ≤ k, evalRand w p t ⟨pc + 2 + body.size, u⟩ .faulted = 0) →
      ∀ t ≤ k, evalRand w p t ⟨pc + 2, z⟩ .faulted = 0)
    (hx_inv : LoopStateInv cond I Q x)
    (hcont : ∀ y ∈ (loopExitPMF cond μ_body x).support, ∀ t ≤ T_hor,
      evalRand w p t ⟨pc + (Code.loop cond body).size, y⟩ .faulted = 0) :
    ∀ t ≤ T_hor, evalRand w p t ⟨pc, x⟩ .faulted = 0 := by
  have hmain : ∀ n ≤ T_hor, ∀ z, LoopStateInv cond I Q z →
      (∀ y ∈ (loopExitPMF cond μ_body z).support, ∀ t ≤ T_hor,
        evalRand w p t ⟨pc + (Code.loop cond body).size, y⟩ .faulted = 0) →
      evalRand w p n ⟨pc, z⟩ .faulted = 0 := by
    intro n; induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro hn z hz_inv hcont_z
      rcases hz_inv with ⟨hcz, hIz⟩ | ⟨hcz, _⟩
      · cases n with
        | zero => simp [evalRand]
        | succ k =>
          rw [evalRand, runRand_succ, stepRand_loop_holds hp hcz, pure_bind]
          refine ih_body z hIz hcz k (fun u hu =>
            evalRand_faulted_eq_zero_of_step (stepRand_loop_back hp u) fun k' hk' =>
              ihn k' (by omega) (by omega) u (hinv z hIz hcz u hu) fun y hy t'' ht'' =>
                hcont_z y ?_ t'' ht'') k le_rfl
          rw [loopExitPMF_of_holds hp_pos hp_top hinv hp_exit hIz hcz, PMF.mem_support_bind_iff]
          exact ⟨u, hu, hy⟩
      · exact evalRand_faulted_loop_exit hp hcz
          (hcont_z z (by simp [loopExitPMF_of_not_holds hcz])) n hn
  exact fun t ht => hmain t ht x hx_inv hcont

/-- Along `ExecCodeDist w c x μ T`, if no continuation from `⟨pc + c.size, y⟩` faults within
`T_hor` steps for any supported `y ∈ μ.support`, then running `p` from `⟨pc, x⟩` does not fault
within `T_hor` steps. -/
theorem evalRand_faulted_eq_zero (h : ExecCodeDist w c x μ T) {p : Program B r} {pc T_hor : ℕ}
    (hp : p.Contains pc (c.assemble pc))
    (hcont : ∀ y ∈ μ.support, ∀ t ≤ T_hor, evalRand w p t ⟨pc + c.size, y⟩ .faulted = 0) :
    ∀ t ≤ T_hor, evalRand w p t ⟨pc, x⟩ .faulted = 0 := by
  revert pc T_hor
  refine h.elim_prim
    (P := fun c x μ _T => ∀ {pc T_hor : ℕ}, p.Contains pc (c.assemble pc) →
      (∀ y ∈ μ.support, ∀ t ≤ T_hor, evalRand w p t ⟨pc + c.size, y⟩ .faulted = 0) →
      ∀ t ≤ T_hor, evalRand w p t ⟨pc, x⟩ .faulted = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ _ _ ih hμ _ _ _ hp hcont; subst hμ; exact ih hp hcont
  · intro _ _ y ho _ _ hp hcont
    exact evalRand_faulted_eq_zero_of_step (stepRand_op (s := ⟨_, _⟩) hp.head ho) fun t ht =>
      by simpa [Code.size] using hcont y (by simp) t (by omega)
  · intro dst src x hfit pc _ hp hcont t ht
    cases t with
    | zero => simp [evalRand]
    | succ k =>
      rw [evalRand, runRand_succ, stepRand_rand_of_fits (s := ⟨pc, x⟩) hp.head hfit, bind_assoc]
      simp only [pure_bind]
      rw [ProbComp.eval_bind, PMF.bind_apply, tsum_eq_zero_iff]
      intro j
      by_cases hj : j ∈ (ProbComp.unifFin (x.regs src)).eval.support
      · have hzero : (runRand w p k (.running ⟨pc + 1, x.set dst j.val⟩)).eval .faulted = 0 := by
          simpa [evalRand, Code.size] using
            hcont _ ((PMF.mem_support_map_iff _ _ _).mpr ⟨j, hj, rfl⟩) k (by omega)
        rw [hzero, mul_zero]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hj, zero_mul]
  · intro _ _ _ _ _ _ _ ih₁ ih₂ _ _ hp hcont
    refine ih₁ hp.append_left fun y₁ hy₁ =>
      ih₂ y₁ hy₁ (contains_seq_right hp) fun y₂ hy₂ t ht => ?_
    simpa [Code.size, Nat.add_assoc] using
      hcont y₂ ((PMF.mem_support_bind_iff _ _ _).mpr ⟨y₁, hy₁, hy₂⟩) t ht
  · intro _ pos neg _ _ _ hc ih pc _ hp hcont
    have hpc : pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) := by omega
    exact evalRand_faulted_eq_zero_of_step (stepRand_branch_pos hp hc)
      (ih (contains_branch_pos hp) fun y hy t ht => by
        simpa [Code.size, hpc] using hcont y hy t (by omega))
  · intro _ _ _ _ _ _ hc ih _ _ hp hcont
    exact evalRand_faulted_eq_zero_of_step (stepRand_branch_neg hp hc)
      (ih hp.cons_tail.append_left fun y hy =>
        evalRand_faulted_eq_zero_of_step (stepRand_branch_neg_jump hp y)
          fun t ht => hcont y hy t (by omega))
  · intro _ _ x hc _ _ hp hcont; exact evalRand_faulted_loop_exit hp hc (hcont x (by simp))
  · intro _ _ _ _ _ _ _ hc ihb ihl _ _ hp hcont
    exact evalRand_faulted_eq_zero_of_step (stepRand_loop_holds hp hc)
      (ihb (contains_loop_body hp) fun y hy =>
        evalRand_faulted_eq_zero_of_step (stepRand_loop_back hp y)
          (ihl y hy hp fun z hz t ht =>
            hcont z ((PMF.mem_support_bind_iff _ _ _).mpr ⟨y, hy, hz⟩) t (by omega)))
  · intro _ _ _ _ _ _ _ _ _ hp_pos hp_top ih_body _ hinv hp_exit hx_inv _ _ hp hcont
    exact evalRand_faulted_loop_geometric hp hp_pos hp_top hinv hp_exit
      (fun z hIz hcz _ => ih_body z hIz hcz (contains_loop_body hp)) hx_inv hcont

/-- If every continuation from `⟨pc + c.size, y⟩` (`y ∈ μ.support`) is fault-free at all horizons,
then running `p` from `⟨pc, x⟩` is fault-free at all horizons. -/
theorem randFaultFree_assemble (h : ExecCodeDist w c x μ T) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc))
    (hcont : ∀ y ∈ μ.support, RandFaultFree w p ⟨pc + c.size, y⟩) :
    RandFaultFree w p ⟨pc, x⟩ := by
  intro T_hor
  rw [← support_evalRand, ← PMF.apply_eq_zero_iff]
  exact h.evalRand_faulted_eq_zero hp
    (fun y hy t _ => (hcont y hy).evalRand_faulted_eq_zero t)
    T_hor le_rfl

private theorem iSup_evalRand_halted_loop_exit {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc))
    {z : Data r} (hcz : ¬cond.Holds z) (v : ℕ) (d : Data r) :
    (⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + (Code.loop cond body).size, z⟩ (.halted v d)) ≤
      ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc, z⟩ (.halted v d) :=
  (iSup_evalRand_halted_le_of_step (stepRand_loop_exit_jump hp z) v d).trans
    (iSup_evalRand_halted_le_of_step (stepRand_loop_not_holds hp hcz) v d)

private theorem iSup_evalRand_halted_loop_step {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc))
    {z : Data r} {μb : PMF (Data r)} (hcz : cond.Holds z) (v : ℕ) (d : Data r)
    (ihb : (∑' u, μb u * ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + 2 + body.size, u⟩ (.halted v d)) ≤
      ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + 2, z⟩ (.halted v d)) :
    (∑' u, μb u * ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc, u⟩ (.halted v d)) ≤
      ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc, z⟩ (.halted v d) :=
  (tsum_le_tsum fun u =>
    mul_le_mul_right (iSup_evalRand_halted_le_of_step (stepRand_loop_back hp u) v d) _).trans
    (ihb.trans (iSup_evalRand_halted_le_of_step (stepRand_loop_holds hp hcz) v d))

private theorem le_iSup_evalRand_halted_loop_geometric {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {p_exit : ℝ≥0∞} {p : Program B r} {pc v : ℕ} {d : Data r}
    (hp : p.Contains pc ((Code.loop cond body).assemble pc))
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ z, I z → cond.Holds z → ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ z, I z → cond.Holds z → p_exit ≤ (μ_body z).toOuterMeasure {y | ¬cond.Holds y})
    (ih_body : ∀ z, I z → cond.Holds z →
      (∑' u, μ_body z u * ⨆ T_hor : ℕ,
        evalRand w p T_hor ⟨pc + 2 + body.size, u⟩ (.halted v d)) ≤
      ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + 2, z⟩ (.halted v d))
    (hx_inv : LoopStateInv cond I Q x) :
    (∑' y, loopExitPMF cond μ_body x y *
      ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + (Code.loop cond body).size, y⟩ (.halted v d)) ≤
      ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc, x⟩ (.halted v d) := by
  set H_loop : Data r → ℝ≥0∞ := fun z => ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc, z⟩ (.halted v d)
  set H_exit : Data r → ℝ≥0∞ := fun z =>
    ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + (Code.loop cond body).size, z⟩ (.halted v d)
  have hiter_le : ∀ K z, LoopStateInv cond I Q z →
      (∑' y, loopIterPMF cond μ_body K z y * H_loop y) ≤ H_loop z := by
    intro K; induction K with
    | zero => intro _ _; simp
    | succ K ihK =>
      intro z hz_inv
      rcases hz_inv with ⟨hcz, hIz⟩ | ⟨hcz, _⟩
      · rw [loopIterPMF_succ, loopStepPMF_of_holds hcz, Cslib.Probability.PMF.tsum_bind_mul]
        exact (Cslib.Probability.PMF.tsum_mul_mono_support (μ_body z) fun u hu =>
          ihK u (hinv z hIz hcz u hu)).trans
          (iSup_evalRand_halted_loop_step hp hcz v d (ih_body z hIz hcz))
      · simp [loopIterPMF_of_not_holds hcz]
  have hrewrite : (∑' y, loopExitPMF cond μ_body x y * H_exit y) =
      ⨆ K : ℕ, ∑' y,
        Set.indicator {w' | ¬cond.Holds w'} (loopIterPMF cond μ_body K x) y * H_exit y := by
    simp_rw [loopExitPMF_apply_of_hasSum
      (hasSum_loopExitDensity hp_pos hp_top hinv hp_exit hx_inv), ENNReal.iSup_mul]
    exact ENNReal.tsum_iSup_of_monotone fun y _ _ hK =>
      mul_le_mul_left (loopIterPMF_indicator_mono cond μ_body x y hK) (H_exit y)
  rw [hrewrite]
  refine iSup_le fun K => (tsum_le_tsum fun y => ?_).trans (hiter_le K x hx_inv)
  by_cases hcy : ¬cond.Holds y
  · rw [Set.indicator_of_mem hcy]
    exact mul_le_mul_right (iSup_evalRand_halted_loop_exit hp hcy v d) _
  · simp [Set.indicator_of_notMem, hcy]

/-- Along `ExecCodeDist w c x μ T`, the `μ`-weighted supremum halting probability from
`⟨pc + c.size, y⟩` is a lower bound on the supremum halting probability from `⟨pc, x⟩`. -/
theorem le_iSup_evalRand_halted (h : ExecCodeDist w c x μ T) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) (v : ℕ) (d : Data r) :
    (∑' y, μ y * ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + c.size, y⟩ (.halted v d)) ≤
      ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc, x⟩ (.halted v d) := by
  revert pc
  refine h.elim_prim
    (P := fun c x μ _T => ∀ {pc : ℕ}, p.Contains pc (c.assemble pc) →
      (∑' y, μ y * ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + c.size, y⟩ (.halted v d)) ≤
        ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc, x⟩ (.halted v d))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ _ _ ih hμ _ _ hp; exact hμ ▸ ih hp
  · intro _ _ _ ho _ hp
    classical simpa [Code.size, PMF.pure_apply] using
      iSup_evalRand_halted_le_of_step (stepRand_op (s := ⟨_, _⟩) hp.head ho) v d
  · intro dst src x hfit pc hp
    rw [Cslib.Probability.PMF.tsum_map_mul]
    simp_rw [ENNReal.mul_iSup]
    rw [ENNReal.tsum_iSup_of_monotone
      (f := fun T_hor k => (ProbComp.unifFin (x.regs src)).eval k *
        evalRand w p T_hor ⟨pc + (Code.rand dst src).size, x.set dst k.val⟩ (.halted v d))
      fun _ _ _ hT => mul_le_mul_right (evalRand_halted_mono w p _ v d hT) _]
    refine iSup_le fun T_hor => le_iSup_of_le (T_hor + 1) ?_
    rw [evalRand, runRand_succ, stepRand_rand_of_fits (s := ⟨pc, x⟩) hp.head hfit, bind_assoc]
    simp only [pure_bind, ProbComp.eval_bind, PMF.bind_apply, evalRand, Code.size, le_rfl]
  · intro _ _ _ μ₁ μ₂ _ _ ih₁ ih₂ _ hp
    rw [Cslib.Probability.PMF.tsum_bind_mul]
    simp_rw [Code.size, ← Nat.add_assoc]
    exact (Cslib.Probability.PMF.tsum_mul_mono_support μ₁ fun y₁ hy₁ =>
      ih₂ y₁ hy₁ (contains_seq_right hp)).trans (ih₁ hp.append_left)
  · intro cond pos neg _ _ _ hc ih pc hp
    rw [show pc + (Code.branch cond pos neg).size = pc + neg.size + 2 + pos.size by
      simp only [Code.size]; omega]
    exact (ih (contains_branch_pos hp)).trans
      (iSup_evalRand_halted_le_of_step (stepRand_branch_pos hp hc) v d)
  · intro _ _ _ _ _ _ hc ih _ hp
    exact (tsum_le_tsum fun y => mul_le_mul_right
      (iSup_evalRand_halted_le_of_step (stepRand_branch_neg_jump hp y) v d) _).trans
      ((ih hp.cons_tail.append_left).trans
        (iSup_evalRand_halted_le_of_step (stepRand_branch_neg hp hc) v d))
  · intro _ _ _ hc _ hp
    classical simpa [PMF.pure_apply] using iSup_evalRand_halted_loop_exit hp hc v d
  · intro _ _ _ μb _ _ _ hc ihb ihl _ hp
    rw [Cslib.Probability.PMF.tsum_bind_mul]
    exact (Cslib.Probability.PMF.tsum_mul_mono_support μb fun y hy => ihl y hy hp).trans
      (iSup_evalRand_halted_loop_step hp hc v d (ihb (contains_loop_body hp)))
  · intro _ _ _ _ _ _ _ _ _ hp_pos hp_top ih_body _ hinv hp_exit hx_inv _ hp
    exact le_iSup_evalRand_halted_loop_geometric hp hp_pos hp_top hinv hp_exit
      (fun z hIz hcz => ih_body z hIz hcz (contains_loop_body hp)) hx_inv

/-- Compiling `ExecCodeDist w c x μ T` with `c.program out` yields:
1. `expectedTime w (c.program out) ⟨0, x⟩ ≤ T + 1`,
2. `RandFaultFree w (c.program out) ⟨0, x⟩`,
3. `AlmostSurelyHalts w (c.program out) ⟨0, x⟩` whenever `T ≠ ⊤`, and
4. for every `y : Data r`,
   `μ y ≤ ⨆ T_hor : ℕ, evalRand w (c.program out) T_hor ⟨0, x⟩ (.halted (y.regs out) y)`. -/
theorem program_halts (h : ExecCodeDist w c x μ T) (out : Fin r) :
    expectedTime w (c.program out) ⟨0, x⟩ ≤ T + 1 ∧
    RandFaultFree w (c.program out) ⟨0, x⟩ ∧
    (T ≠ ⊤ → AlmostSurelyHalts w (c.program out) ⟨0, x⟩) ∧
    ∀ y : Data r,
      μ y ≤ ⨆ T_hor : ℕ, evalRand w (c.program out) T_hor ⟨0, x⟩ (.halted (y.regs out) y) := by
  have hp : (c.program out).Contains 0 (c.assemble 0) :=
    (Program.Contains.self (c.program out)).append_left
  have hhalt : (c.program out)[0 + c.size]? = some (.halt out) := by simp [Code.program]
  have hexp : expectedTime w (c.program out) ⟨0, x⟩ ≤ T + 1 :=
    (h.expectedStepsFrom_le (k := fun _ => 1) hp fun y _ => by
      rw [expectedStepsFrom_running, stepRand_halt (s := ⟨0 + c.size, y⟩) hhalt,
        ProbComp.expect_pure, expectedStepsFrom_halted, add_zero]).trans_eq (by simp [μ.tsum_coe])
  have hff : RandFaultFree w (c.program out) ⟨0, x⟩ :=
    h.randFaultFree_assemble hp fun y _ t => by
      rw [← support_evalRand, ← PMF.apply_eq_zero_iff]
      cases t with
      | zero => simp [evalRand]
      | succ k =>
        rw [evalRand, runRand_succ, stepRand_halt (s := ⟨0 + c.size, y⟩) hhalt, pure_bind,
          runRand_halted]
        simp [PMF.pure_apply]
  refine ⟨hexp, hff, fun hT => AlmostSurelyHalts.of_expectedTime_ne_top hff
      (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hT, ENNReal.one_ne_top⟩) hexp), fun y => ?_⟩
  have h1 : (1 : ℝ≥0∞) ≤
      ⨆ T_hor : ℕ, evalRand w (c.program out) T_hor ⟨0 + c.size, y⟩ (.halted (y.regs out) y) :=
    le_iSup_of_le 1 <| by
      rw [evalRand, runRand_succ, stepRand_halt (s := ⟨0 + c.size, y⟩) hhalt, pure_bind,
        runRand_zero, ProbComp.eval_pure, PMF.pure_apply_self]
  have hμ : μ y ≤ μ y *
      ⨆ T_hor : ℕ, evalRand w (c.program out) T_hor ⟨0 + c.size, y⟩ (.halted (y.regs out) y) := by
    simpa using mul_le_mul_right h1 (μ y)
  exact (hμ.trans (le_tsum (f := fun z => μ z *
      ⨆ T_hor : ℕ, evalRand w (c.program out) T_hor ⟨0 + c.size, z⟩ (.halted (y.regs out) y))
    y)).trans (h.le_iSup_evalRand_halted hp (y.regs out) y)

end ExecCodeDist

theorem ExecRand.expectedStepsWithin_assemble {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) (N : ℕ) :
    expectedStepsWithin w p N (.running ⟨pc, x⟩) ≤
      ProbComp.expect m (fun z =>
        (z.2 : ℝ≥0∞) + expectedStepsWithin w p N (.running ⟨pc + c.size, z.1⟩)) := by
  refine ((ExecCodeDist.of_execRand h).expectedStepsWithin_assemble hp N).trans_eq ?_
  rw [ProbComp.expect_add,
    ← ProbComp.expect_map Prod.fst m (fun y =>
      expectedStepsWithin w p N (.running ⟨pc + c.size, y⟩))]
  rfl

/-- Along `ExecRand w c x m`, if no continuation from `⟨pc + c.size, y⟩` faults within `T` steps
for any supported outcome `y`, then running `p` from `⟨pc, x⟩` does not fault within `T` steps. -/
theorem ExecRand.evalRand_faulted_eq_zero {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) {p : Program B r} {pc T : ℕ}
    (hp : p.Contains pc (c.assemble pc))
    (hcont : ∀ z ∈ m.support, ∀ t ≤ T, evalRand w p t ⟨pc + c.size, z.1⟩ .faulted = 0) :
    ∀ t ≤ T, evalRand w p t ⟨pc, x⟩ .faulted = 0 :=
  (ExecCodeDist.of_execRand h).evalRand_faulted_eq_zero hp fun _ hy => by
    obtain ⟨z, hz, rfl⟩ := ExecCodeDist.mem_support_eval_fst_iff.mp hy
    exact hcont z hz

/-- Along `ExecRand w c x m`, the expected supremum halting probability from `⟨pc + c.size, y⟩` is a
lower bound on the supremum halting probability from `⟨pc, x⟩`. -/
theorem ExecRand.le_iSup_evalRand_halted {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) (v : ℕ) (d : Data r) :
    ProbComp.expect m (fun z => ⨆ T : ℕ, evalRand w p T ⟨pc + c.size, z.1⟩ (.halted v d)) ≤
      ⨆ T : ℕ, evalRand w p T ⟨pc, x⟩ (.halted v d) :=
  (ProbComp.expect_map Prod.fst m
    (fun y => ⨆ T : ℕ, evalRand w p T ⟨pc + c.size, y⟩ (.halted v d))).symm.trans_le
    ((ExecCodeDist.of_execRand h).le_iSup_evalRand_halted hp v d)

/-- Geometric Las Vegas loop expected-step bound inside any flat program `p` containing
`(Code.loop cond body).assemble pc`. -/
theorem expectedStepsFrom_loop_le_of_geometric {w : ℕ} {cond : Cond r} {body : Code B r}
    (I Q : Data r → Prop) {μ_body : Data r → PMF (Data r)} {T_body : Data r → ℝ≥0∞}
    {B_body p_exit : ℝ≥0∞} {x : Data r}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hbody : ∀ z, I z → cond.Holds z → ExecCodeDist w body z (μ_body z) (T_body z))
    (hB : ∀ z, I z → cond.Holds z → T_body z ≤ B_body)
    (hinv : ∀ z, I z → cond.Holds z →
      ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ z, I z → cond.Holds z →
      p_exit ≤ (μ_body z).toOuterMeasure {y | ¬cond.Holds y})
    (hx_inv : LoopStateInv cond I Q x)
    {p : Program B r} {pc : ℕ} (hp : p.Contains pc ((Code.loop cond body).assemble pc))
    {k : Data r → ℝ≥0∞}
    (hk : ∀ y, ¬cond.Holds y → Q y →
      expectedStepsFrom w p (.running ⟨pc + (Code.loop cond body).size, y⟩) ≤ k y) :
    expectedStepsFrom w p (.running ⟨pc, x⟩) ≤
      ((B_body + 2) / p_exit + 2) + ∑' y, loopExitPMF cond μ_body x y * k y := by
  have hloop := ExecCodeDist.loop_geometric I Q hp_pos hp_top hbody hB hinv hp_exit hx_inv
  refine hloop.expectedStepsFrom_le hp fun y hy => ?_
  obtain ⟨⟨hcy, hQy⟩, _⟩ := mem_support_loopExitPMF hp_pos hp_top hinv hp_exit hx_inv hy
  exact hk y hcy hQy

end Cslib.WordRAM

end
