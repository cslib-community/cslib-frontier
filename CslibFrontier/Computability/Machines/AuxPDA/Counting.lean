/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.AuxPDA.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Space
public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Counting auxiliary pushdown automata

`Turing.CountingAuxPDA` equips an auxiliary pushdown automaton with an ordered list of transition
occurrences at each local view (control state, input symbol, work-tape symbols, top stack symbol),
mirroring `Turing.MultiTapeCTM` and `Turing.MultiTapeCTM.CountsInSpace`. Repeated entries in the
transition list count as distinct branches.

A branch is a list of occurrence indices stopping at the first halted configuration. An out-of-range
index or an action attempting `StackOp.pop` on an empty stack fails (`step? = none`) and is never
counted as an accepting or rejecting branch. `CountingAuxPDA.HaltsWithin` requires every reachable
running configuration to have a nonempty transition list, every listed transition to avoid stack
underflow, and every branch to halt within the clock bound.

This is original machine infrastructure for cslib-frontier #7920 (Work Package 3), supplying the
exact accepting-path count behind `Cslib.Complexity.UAuxPDA` and `Cslib.Complexity.coUAuxPDA`.

## Main definitions

* `Turing.CountingAuxPDA`: counting auxiliary pushdown automaton with ordered transition lists.
* `Turing.CountingAuxPDA.toAuxPDA`: forget transition multiplicity to obtain an `AuxPDA`.
* `Turing.CountingAuxPDA.step?`, `Turing.CountingAuxPDA.lts`, `Turing.CountingAuxPDA.runBranch`,
  `Turing.CountingAuxPDA.branches`: occurrence-labelled transitions and bounded terminal branches.
* `Turing.CountingAuxPDA.HaltsWithin`: all-branches clock bound excluding stuck states and stack
  underflow.
* `Turing.CountingAuxPDA.branchCount`, `Turing.CountingAuxPDA.acceptCount`,
  `Turing.CountingAuxPDA.rejectCount`: exact terminal branch counts.
* `Turing.CountingAuxPDA.CountsInTimeAndSpace`: accepting-count witness with work space and
  all-branches clock bounds.
* `Turing.CountingAuxPDA.ofMultiTapeCTM`: embedding of a `MultiTapeCTM` with an unused stack.

## Main results

* `Turing.CountingAuxPDA.mem_branches_iff`: `branches` enumerates exactly the bounded first-halting
  traces.
* `Turing.CountingAuxPDA.HaltsWithin.branches_eq`,
  `Turing.CountingAuxPDA.HaltsWithin.branchCount_eq`: sufficient clocks are stable under increase.
* `Turing.CountingAuxPDA.HaltsWithin.branchCount_pos_iff`: positive count equals existence of a
  halted unlabelled run path with the verdict.
* `Turing.CountingAuxPDA.CountsInTimeAndSpace.decidesInTimeAndSpace`: forgetting multiplicity gives
  a nondeterministic `AuxPDA` decider within the same space and time bounds.
* `Turing.CountingAuxPDA.ofMultiTapeCTM_acceptCount`,
  `Turing.CountingAuxPDA.ofMultiTapeCTM_haltsWithin_iff`: exact branch-count preservation from
  `MultiTapeCTM`.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [K. Reinhardt, E. Allender, *Making Nondeterminism Unambiguous*][ReinhardtAllender2000]
-/

@[expose] public section

namespace Turing

/-- A counting auxiliary pushdown automaton: at each local view (control state, input head symbol,
work-tape head symbols, top stack symbol), `tr` gives an ordered list of transition occurrences.
Repeated entries in the list count as distinct branches. -/
structure CountingAuxPDA (k : ℕ) (Symbol StackSym State : Type*) where
  /-- The initial control state. -/
  q₀ : State
  /-- Ordered list of transition occurrences at each local view. -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol)
    (top : Option StackSym) : List (AuxPDA.Action k Symbol StackSym State)

namespace CountingAuxPDA

variable {k : ℕ} {Symbol StackSym State : Type*} {input : List Symbol}

/-- The ordered list of live transition occurrences at `cfg`; empty when halted. -/
def actions (M : CountingAuxPDA k Symbol StackSym State)
    (cfg : AuxPDA.Cfg k Symbol StackSym State input) :
    List (AuxPDA.Action k Symbol StackSym State) :=
  match cfg.tapes.state with
  | none => []
  | some q => M.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.topSym

/-- Forget transition multiplicity to obtain the underlying nondeterministic `AuxPDA`. -/
def toAuxPDA (M : CountingAuxPDA k Symbol StackSym State) :
    AuxPDA k Symbol StackSym State where
  q₀ := M.q₀
  Tr q inp work top act := act ∈ M.tr q inp work top

/-- Execute occurrence `index` at `cfg`. Returns `none` when halted, out of range, or on stack
underflow. -/
def step? (M : CountingAuxPDA k Symbol StackSym State)
    (cfg : AuxPDA.Cfg k Symbol StackSym State input) (index : ℕ) :
    Option (AuxPDA.Cfg k Symbol StackSym State input) :=
  ((M.actions cfg)[index]?).bind (fun act => act.apply? cfg)

/-- The labelled transition system of `M` on `input`, labelled by occurrence index. -/
def lts (M : CountingAuxPDA k Symbol StackSym State) (input : List Symbol) :
    Cslib.LTS (AuxPDA.Cfg k Symbol StackSym State input) ℕ where
  Tr cfg index next := M.step? cfg index = some next

/-- Replay a list of occurrence indices from `cfg`, stopping without padding after halting. -/
def runBranch (M : CountingAuxPDA k Symbol StackSym State) :
    AuxPDA.Cfg k Symbol StackSym State input → List ℕ →
      Option (AuxPDA.Cfg k Symbol StackSym State input)
  | cfg, [] => some cfg
  | cfg, index :: rest => do
      let next ← M.step? cfg index
      M.runBranch next rest

@[simp]
theorem runBranch_nil (M : CountingAuxPDA k Symbol StackSym State)
    (cfg : AuxPDA.Cfg k Symbol StackSym State input) :
    M.runBranch cfg [] = some cfg := rfl

theorem runBranch_cons (M : CountingAuxPDA k Symbol StackSym State)
    (cfg : AuxPDA.Cfg k Symbol StackSym State input) (index : ℕ) (rest : List ℕ) :
    M.runBranch cfg (index :: rest) =
      (M.step? cfg index).bind (fun next => M.runBranch next rest) := rfl

theorem actions_of_halted (M : CountingAuxPDA k Symbol StackSym State)
    {cfg : AuxPDA.Cfg k Symbol StackSym State input} (h : cfg.Halted) :
    M.actions cfg = [] := by
  simp [actions, h]

theorem step?_of_halted (M : CountingAuxPDA k Symbol StackSym State)
    {cfg : AuxPDA.Cfg k Symbol StackSym State input} (h : cfg.Halted) (index : ℕ) :
    M.step? cfg index = none := by
  simp [step?, M.actions_of_halted h]

theorem runBranch_of_halted (M : CountingAuxPDA k Symbol StackSym State)
    {cfg : AuxPDA.Cfg k Symbol StackSym State input} (h : cfg.Halted) (choices : List ℕ) :
    M.runBranch cfg choices = if choices = [] then some cfg else none := by
  cases choices with
  | nil => simp
  | cons index rest => simp [runBranch_cons, M.step?_of_halted h]

theorem runBranch_append (M : CountingAuxPDA k Symbol StackSym State)
    (cfg : AuxPDA.Cfg k Symbol StackSym State input) (first second : List ℕ) :
    M.runBranch cfg (first ++ second) =
      (M.runBranch cfg first).bind (fun next => M.runBranch next second) := by
  induction first generalizing cfg with
  | nil => rfl
  | cons index rest ih =>
    simp only [List.cons_append, runBranch_cons, ih, Option.bind_assoc]

theorem runBranch_eq_some_iff (M : CountingAuxPDA k Symbol StackSym State)
    (cfg final : AuxPDA.Cfg k Symbol StackSym State input) (choices : List ℕ) :
    M.runBranch cfg choices = some final ↔ (M.lts input).MTr cfg choices final := by
  induction choices generalizing cfg with
  | nil => simp [runBranch, Cslib.LTS.MTr.nil_iff]
  | cons index rest ih =>
    simp only [runBranch_cons, Option.bind_eq_some_iff, Cslib.LTS.MTr.cons_iff, lts]
    exact exists_congr fun next => and_congr_right fun _ => ih next

theorem step?_eq_some_iff (M : CountingAuxPDA k Symbol StackSym State)
    (cfg final : AuxPDA.Cfg k Symbol StackSym State input) (index : ℕ) :
    M.step? cfg index = some final ↔
      ∃ h : index < (M.actions cfg).length, (M.actions cfg)[index].apply? cfg = some final := by
  simp only [step?, Option.bind_eq_some_iff, List.getElem?_eq_some_iff]
  exact ⟨fun ⟨_, ⟨h, rfl⟩, hact⟩ => ⟨h, hact⟩, fun ⟨h, hact⟩ => ⟨_, ⟨h, rfl⟩, hact⟩⟩

/-- Before halting, an unlabelled `toAuxPDA` step is precisely a valid occurrence index. -/
theorem step_toAuxPDA_iff (M : CountingAuxPDA k Symbol StackSym State)
    {cfg next : AuxPDA.Cfg k Symbol StackSym State input} (hrun : ¬cfg.Halted) :
    M.toAuxPDA.Step cfg next ↔ ∃ i, M.step? cfg i = some next := by
  cases hstate : cfg.tapes.state with
  | none => exact (hrun hstate).elim
  | some q =>
    simp only [AuxPDA.Step, hstate, toAuxPDA, step?_eq_some_iff, actions, List.mem_iff_getElem]
    exact ⟨fun ⟨_, ⟨i, hi, rfl⟩, hact⟩ => ⟨i, hi, hact⟩,
      fun ⟨i, hi, hact⟩ => ⟨_, ⟨i, hi, rfl⟩, hact⟩⟩

/-- Enumerate all first-halting occurrence traces of length at most `fuel` starting from `cfg`.
Underflowing transitions (`apply? = none`) contribute no branches. -/
def branches (M : CountingAuxPDA k Symbol StackSym State) :
    ℕ → AuxPDA.Cfg k Symbol StackSym State input → Finset (List ℕ)
  | fuel, cfg => match cfg.tapes.state with
    | none => {[]}
    | some _ => match fuel with
      | 0 => ∅
      | fuel + 1 =>
        Finset.univ.biUnion fun index : Fin (M.actions cfg).length =>
          match (M.actions cfg)[index.val].apply? cfg with
          | none => ∅
          | some next => (M.branches fuel next).image (List.cons index.val)

theorem branches_of_halted (M : CountingAuxPDA k Symbol StackSym State)
    {cfg : AuxPDA.Cfg k Symbol StackSym State input} (h : cfg.Halted) (fuel : ℕ) :
    M.branches fuel cfg = {[]} := by
  cases fuel <;> simp [branches, h]

@[simp]
theorem nil_mem_branches (M : CountingAuxPDA k Symbol StackSym State)
    (cfg : AuxPDA.Cfg k Symbol StackSym State input) (fuel : ℕ) :
    [] ∈ M.branches fuel cfg ↔ cfg.Halted := by
  cases fuel with
  | zero =>
    cases hs : cfg.tapes.state <;> simp [branches, hs, AuxPDA.Cfg.Halted, Turing.Cfg.Halted]
  | succ fuel =>
    cases hs : cfg.tapes.state with
    | none => simp [branches, hs, AuxPDA.Cfg.Halted, Turing.Cfg.Halted]
    | some _ =>
      simp only [branches, hs, Finset.mem_biUnion, Finset.mem_univ, true_and, AuxPDA.Cfg.Halted,
        Turing.Cfg.Halted, reduceCtorEq, iff_false, not_exists]
      exact fun i => by cases (M.actions cfg)[i.val].apply? cfg <;> simp

theorem cons_mem_branches (M : CountingAuxPDA k Symbol StackSym State)
    (cfg : AuxPDA.Cfg k Symbol StackSym State input) (fuel index : ℕ) (rest : List ℕ) :
    index :: rest ∈ M.branches (fuel + 1) cfg ↔
      ∃ next, M.step? cfg index = some next ∧ rest ∈ M.branches fuel next := by
  cases hs : cfg.tapes.state with
  | none =>
    simp [M.branches_of_halted hs, M.step?_of_halted hs]
  | some q =>
    simp only [branches, hs, Finset.mem_biUnion, Finset.mem_univ, true_and, step?_eq_some_iff]
    refine ⟨?_, fun ⟨_, ⟨hidx, hact⟩, hrest⟩ => ⟨⟨index, hidx⟩, by simpa [hact] using hrest⟩⟩
    rintro ⟨i, hi⟩
    cases hact : (M.actions cfg)[i.val].apply? cfg <;> rw [hact] at hi
    · exact absurd hi (Finset.notMem_empty _)
    · obtain ⟨r, hr, ⟨⟩⟩ := Finset.mem_image.mp hi
      exact ⟨_, ⟨i.isLt, hact⟩, hr⟩

/-- `branches` enumerates precisely the first-halting occurrence traces within `fuel` steps. -/
theorem mem_branches_iff (M : CountingAuxPDA k Symbol StackSym State)
    (cfg : AuxPDA.Cfg k Symbol StackSym State input) (fuel : ℕ) (choices : List ℕ) :
    choices ∈ M.branches fuel cfg ↔ choices.length ≤ fuel ∧
      ∃ final, M.runBranch cfg choices = some final ∧ final.Halted := by
  induction fuel generalizing cfg choices with
  | zero =>
    cases choices with
    | nil => simp
    | cons index rest => cases hs : cfg.tapes.state <;> simp [branches, hs]
  | succ fuel ih =>
    cases choices with
    | nil => simp
    | cons index rest =>
      simp only [cons_mem_branches, ih, List.length_cons, Nat.add_le_add_iff_right,
        runBranch_cons, Option.bind_eq_some_iff]
      aesop

/-- A path of running `toAuxPDA` steps can be replayed by occurrence indices. -/
theorem exists_runBranch_of_runningPath (M : CountingAuxPDA k Symbol StackSym State)
    (p : RelSeries (M.toAuxPDA.runningStepRel input)) :
    ∃ indices, M.runBranch p.head indices = some p.last ∧ indices.length = p.length := by
  induction p using RelSeries.inductionOn' with
  | singleton cfg => exact ⟨[], rfl, rfl⟩
  | snoc p next hs ih =>
    obtain ⟨indices, hi, hlen⟩ := ih
    obtain ⟨i, hstep⟩ := (M.step_toAuxPDA_iff hs.1).mp hs.2
    refine ⟨indices ++ [i], ?_, by simp [hlen]⟩
    simp [runBranch_append, hi, runBranch_cons, hstep]

/-- A successful occurrence replay yields a path of running `toAuxPDA` steps. -/
theorem exists_runningPath_of_runBranch (M : CountingAuxPDA k Symbol StackSym State)
    {c d : AuxPDA.Cfg k Symbol StackSym State input} {indices : List ℕ}
    (h : M.runBranch c indices = some d) :
    ∃ p : RelSeries (M.toAuxPDA.runningStepRel input),
      p.head = c ∧ p.last = d ∧ p.length = indices.length := by
  induction indices generalizing c with
  | nil => exact ⟨RelSeries.singleton _ c, rfl, Option.some.inj h, rfl⟩
  | cons i is ih =>
    obtain ⟨next, hs, ht⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨p, hp, hlast, hlen⟩ := ih ht
    have hnot : ¬c.Halted := fun hc => by simp [M.step?_of_halted hc] at hs
    have hstep : M.toAuxPDA.Step c p.head := hp ▸ (M.step_toAuxPDA_iff hnot).mpr ⟨i, hs⟩
    exact ⟨p.cons c ⟨hnot, hstep⟩, rfl, by simpa using hlast, by simp [hlen]⟩

/-- Every branch from `cfg` halts within `fuel` steps, with no stuck configurations and no stack
underflow on any reachable transition occurrence. -/
inductive HaltsWithin (M : CountingAuxPDA k Symbol StackSym State) :
    ℕ → AuxPDA.Cfg k Symbol StackSym State input → Prop
  | halt {fuel cfg} (halted : cfg.Halted) : HaltsWithin M fuel cfg
  | step {fuel cfg}
      (nonempty : M.actions cfg ≠ [])
      (valid : ∀ index : Fin (M.actions cfg).length,
        ((M.actions cfg)[index.val].apply? cfg).isSome)
      (next : ∀ (index : Fin (M.actions cfg).length)
        (nextCfg : AuxPDA.Cfg k Symbol StackSym State input),
        (M.actions cfg)[index.val].apply? cfg = some nextCfg →
        HaltsWithin M fuel nextCfg) :
      HaltsWithin M (fuel + 1) cfg

/-- A counting-machine clock bounds every unlabelled `toAuxPDA` path from `cfg`. -/
theorem HaltsWithin.paths_halted {M : CountingAuxPDA k Symbol StackSym State}
    {fuel : ℕ} {cfg : AuxPDA.Cfg k Symbol StackSym State input} (h : M.HaltsWithin fuel cfg) :
    ∀ p : M.toAuxPDA.RunPath input, p.head = cfg → fuel ≤ p.length → p.last.Halted := by
  induction h with
  | halt hh =>
    rintro p rfl _
    exact p.last_eq_of_halted ⟨0, by omega⟩ hh ▸ hh
  | @step fuel cfg nonempty _ next ih =>
    rintro p rfl hlen
    have hnext : 1 < p.length + 1 := by omega
    have hlive : ¬p.head.Halted := fun hh => nonempty (M.actions_of_halted hh)
    obtain ⟨index, hstep⟩ := (M.step_toAuxPDA_iff hlive).mp (p.step ⟨0, by omega⟩)
    obtain ⟨hi, heq⟩ := (M.step?_eq_some_iff _ _ _).mp hstep
    simpa using ih ⟨index, hi⟩ (p ⟨1, hnext⟩) heq (p.drop ⟨1, hnext⟩)
      rfl (by simp only [RelSeries.drop_length]; omega)

/-- Enlarging a sufficient clock preserves `HaltsWithin`. -/
theorem HaltsWithin.mono {M : CountingAuxPDA k Symbol StackSym State}
    {cfg : AuxPDA.Cfg k Symbol StackSym State input} {fuel larger : ℕ}
    (h : M.HaltsWithin fuel cfg) (hle : fuel ≤ larger) :
    M.HaltsWithin larger cfg := by
  induction h generalizing larger with
  | halt halted => exact .halt halted
  | @step fuel cfg nonempty valid next ih =>
    obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [show fuel + 1 + rest = (fuel + rest) + 1 by omega]
    exact .step nonempty valid fun index nextCfg hact =>
      ih index nextCfg hact (Nat.le_add_right fuel rest)

/-- No valid replay can exceed an all-branches halting clock. -/
theorem HaltsWithin.length_le {M : CountingAuxPDA k Symbol StackSym State}
    {cfg final : AuxPDA.Cfg k Symbol StackSym State input} {fuel : ℕ}
    (h : M.HaltsWithin fuel cfg) {choices : List ℕ}
    (hrun : M.runBranch cfg choices = some final) :
    choices.length ≤ fuel := by
  induction h generalizing choices final with
  | halt halted =>
    cases choices with
    | nil => simp
    | cons index rest => simp [runBranch_cons, M.step?_of_halted halted] at hrun
  | @step fuel cfg nonempty _ next ih =>
    cases choices with
    | nil => simp
    | cons index rest =>
      obtain ⟨nextCfg, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hrun
      obtain ⟨hi, hact⟩ := (M.step?_eq_some_iff cfg nextCfg index).mp hstep
      simpa only [List.length_cons, Nat.add_le_add_iff_right] using
        ih ⟨index, hi⟩ nextCfg hact hrest

/-- Increasing a sufficient clock does not change the finite set of terminal branches. -/
theorem HaltsWithin.branches_eq {M : CountingAuxPDA k Symbol StackSym State}
    {cfg : AuxPDA.Cfg k Symbol StackSym State input} {fuel larger : ℕ}
    (h : M.HaltsWithin fuel cfg) (hle : fuel ≤ larger) :
    M.branches larger cfg = M.branches fuel cfg := by
  ext choices
  simp only [mem_branches_iff]
  exact ⟨fun ⟨_, final, hrun, hhalt⟩ => ⟨h.length_le hrun, final, hrun, hhalt⟩,
    fun ⟨hlen, hrun⟩ => ⟨hlen.trans hle, hrun⟩⟩

/-- A `HaltsWithin` clock guarantees at least one terminal branch. -/
theorem HaltsWithin.branches_nonempty {M : CountingAuxPDA k Symbol StackSym State}
    {cfg : AuxPDA.Cfg k Symbol StackSym State input} {fuel : ℕ}
    (h : M.HaltsWithin fuel cfg) : (M.branches fuel cfg).Nonempty := by
  induction h with
  | halt halted => simp [M.branches_of_halted halted]
  | @step fuel cfg nonempty valid next ih =>
    have hlen : 0 < (M.actions cfg).length := List.length_pos_iff.mpr nonempty
    obtain ⟨nextCfg, hact⟩ := Option.isSome_iff_exists.mp (valid ⟨0, hlen⟩)
    obtain ⟨rest, hrest⟩ := ih ⟨0, hlen⟩ nextCfg hact
    refine ⟨0 :: rest, (M.cons_mem_branches cfg fuel 0 rest).mpr ⟨nextCfg, ?_, hrest⟩⟩
    exact (M.step?_eq_some_iff cfg nextCfg 0).mpr ⟨hlen, hact⟩

/-- Count terminal branches whose final output satisfies `verdict`. Failed replays (stuck states
or stack underflow) are never counted. -/
def branchCount (M : CountingAuxPDA k Symbol StackSym State) (verdict : List Symbol → Bool)
    (fuel : ℕ) (cfg : AuxPDA.Cfg k Symbol StackSym State input) : ℕ :=
  ((M.branches fuel cfg).filter fun choices =>
    (M.runBranch cfg choices).any (fun final => verdict final.tapes.output)).card

theorem HaltsWithin.branchCount_eq {M : CountingAuxPDA k Symbol StackSym State}
    {cfg : AuxPDA.Cfg k Symbol StackSym State input} {fuel larger : ℕ}
    (h : M.HaltsWithin fuel cfg) (hle : fuel ≤ larger) (verdict : List Symbol → Bool) :
    M.branchCount verdict larger cfg = M.branchCount verdict fuel cfg := by
  simp only [branchCount, h.branches_eq hle]

/-- A positive branch count within a sufficient clock is equivalent to existence of a halted
unlabelled `toAuxPDA` run path realizing `verdict`. -/
theorem HaltsWithin.branchCount_pos_iff {M : CountingAuxPDA k Symbol StackSym State}
    {fuel : ℕ} {cfg : AuxPDA.Cfg k Symbol StackSym State input} (h : M.HaltsWithin fuel cfg)
    (verdict : List Symbol → Bool) :
    0 < M.branchCount verdict fuel cfg ↔
      ∃ p : M.toAuxPDA.RunPath input, p.head = cfg ∧ p.last.Halted ∧
        verdict p.last.tapes.output := by
  refine ⟨fun hpos => ?_, fun ⟨p, hp, hh, hv⟩ => ?_⟩
  · obtain ⟨indices, hmem⟩ := Finset.card_pos.mp hpos
    obtain ⟨⟨_, final, hrun, hh⟩, hv⟩ :=
      (Finset.mem_filter.mp hmem).imp_left (M.mem_branches_iff _ _ _).mp
    obtain ⟨q, hhead, hlast, _⟩ := M.exists_runningPath_of_runBranch hrun
    exact ⟨q.map ⟨id, fun hs => hs.2⟩, hhead, hlast ▸ hh, by simpa [hlast, hrun] using hv⟩
  · obtain ⟨q, hhead, hlast, _, _⟩ := p.exists_running hh
    obtain ⟨indices, hi, _⟩ := M.exists_runBranch_of_runningPath q
    rw [hhead, hp, hlast] at hi
    refine Finset.card_pos.mpr ⟨indices, Finset.mem_filter.mpr ⟨?_, by simpa [hi] using hv⟩⟩
    exact (M.mem_branches_iff _ _ _).mpr ⟨h.length_le hi, _, hi, hh⟩

/-- Complementary verdicts partition the terminal branches without counting stuck or underflowing
traces. -/
theorem branchCount_add_not (M : CountingAuxPDA k Symbol StackSym State)
    (verdict : List Symbol → Bool) (fuel : ℕ)
    (cfg : AuxPDA.Cfg k Symbol StackSym State input) :
    M.branchCount verdict fuel cfg + M.branchCount (fun out => !verdict out) fuel cfg =
      (M.branches fuel cfg).card := by
  unfold branchCount
  have hfilter :
      (M.branches fuel cfg).filter (fun choices =>
        (M.runBranch cfg choices).any (fun final => !verdict final.tapes.output)) =
      (M.branches fuel cfg).filter (fun choices =>
        ¬(M.runBranch cfg choices).any (fun final => verdict final.tapes.output)) :=
    Finset.filter_congr fun choices hchoices => by
      obtain ⟨_, final, hrun, _⟩ := (M.mem_branches_iff cfg fuel choices).mp hchoices
      simp [hrun]
  rw [hfilter]
  exact Finset.card_filter_add_card_filter_not _

/-- Branch counts at a running configuration sum over transition occurrences (skipping any
underflowing occurrences). -/
theorem branchCount_succ (M : CountingAuxPDA k Symbol StackSym State)
    (verdict : List Symbol → Bool) (cfg : AuxPDA.Cfg k Symbol StackSym State input)
    (fuel : ℕ) (state : State) (h : cfg.tapes.state = some state) :
    M.branchCount verdict (fuel + 1) cfg =
      ∑ index : Fin (M.actions cfg).length,
        match (M.actions cfg)[index.val].apply? cfg with
        | none => 0
        | some next => M.branchCount verdict fuel next := by
  have hfilter (index : Fin (M.actions cfg).length) :
      ((match (M.actions cfg)[index.val].apply? cfg with
        | none => (∅ : Finset (List ℕ))
        | some next => (M.branches fuel next).image (List.cons index.val)).filter
          (fun choices => (M.runBranch cfg choices).any
            (fun (final : AuxPDA.Cfg k Symbol StackSym State input) =>
              verdict final.tapes.output))).card =
      match (M.actions cfg)[index.val].apply? cfg with
      | none => 0
      | some next => M.branchCount verdict fuel next := by
    cases hact : (M.actions cfg)[index.val].apply? cfg with
    | none => simp
    | some next =>
      have hstep : M.step? cfg index.val = some next :=
        (M.step?_eq_some_iff cfg next index.val).mpr ⟨index.isLt, hact⟩
      rw [Finset.filter_image, Finset.card_image_of_injective _ List.cons_injective]
      exact congrArg Finset.card
        (Finset.filter_congr fun choices _ => by simp [runBranch_cons, hstep])
  unfold branchCount
  simp only [branches, h, Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun index _ => hfilter index
  · intro left _ right _ hne
    refine Finset.disjoint_left.mpr fun choices hleft hright => hne (Fin.ext ?_)
    simp only [Finset.mem_filter] at hleft hright
    split at hleft <;> split at hright <;>
      try simp only [Finset.notMem_empty, false_and] at hleft hright
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hleft.1
    obtain ⟨_, _, h⟩ := Finset.mem_image.mp hright.1
    exact (List.cons.inj h).1.symm

/-- Accepting branch count under the standard `[true]` output convention. -/
def acceptCount (M : CountingAuxPDA k Bool StackSym State)
    {input : List Bool} (fuel : ℕ) (cfg : AuxPDA.Cfg k Bool StackSym State input) : ℕ :=
  M.branchCount (· == [true]) fuel cfg

/-- Rejecting branch count: terminal outputs other than `[true]` (excluding stuck or underflowing
branches). -/
def rejectCount (M : CountingAuxPDA k Bool StackSym State)
    {input : List Bool} (fuel : ℕ) (cfg : AuxPDA.Cfg k Bool StackSym State input) : ℕ :=
  M.branchCount (fun out => !(out == [true])) fuel cfg

theorem acceptCount_add_rejectCount (M : CountingAuxPDA k Bool StackSym State)
    {input : List Bool} (fuel : ℕ) (cfg : AuxPDA.Cfg k Bool StackSym State input) :
    M.acceptCount fuel cfg + M.rejectCount fuel cfg = (M.branches fuel cfg).card :=
  M.branchCount_add_not _ _ _

/-- `M` realizes the accepting count `f` within work space `s` and all-branches clock `t` relative
to `enc`: every prefix visits at most `s a` work-tape cells, every branch halts within `t a` steps
without stuck states or stack underflow, and `f a` equals `M.acceptCount (t a)` from the initial
configuration. -/
def CountsInTimeAndSpace {α : Type*} (M : CountingAuxPDA k Bool StackSym State)
    (enc : α ↪ List Bool) (f : α → ℕ) (s t : α → ℕ) : Prop :=
  ∀ a, M.toAuxPDA.RunsInSpace (enc a) (s a) ∧
    M.HaltsWithin (t a) (M.toAuxPDA.initCfg (enc a)) ∧
    f a = M.acceptCount (t a) (M.toAuxPDA.initCfg (enc a))

/-- Monotone resource closure for `CountsInTimeAndSpace`: increasing either the space bound or the
clock bound preserves the exact accepting count. -/
theorem CountsInTimeAndSpace.mono {α : Type*} {M : CountingAuxPDA k Bool StackSym State}
    {enc : α ↪ List Bool} {f : α → ℕ} {s s' t t' : α → ℕ}
    (h : M.CountsInTimeAndSpace enc f s t)
    (hs : ∀ a, s a ≤ s' a) (ht : ∀ a, t a ≤ t' a) :
    M.CountsInTimeAndSpace enc f s' t' := fun a => by
  obtain ⟨hspace, hclock, hcount⟩ := h a
  exact ⟨hspace.mono (hs a), hclock.mono (ht a),
    hcount.trans (hclock.branchCount_eq (ht a) (· == [true])).symm⟩

/-- **Forgetting transition multiplicity gives a nondeterministic `AuxPDA` decider** within the
same work space and clock bounds. -/
theorem CountsInTimeAndSpace.decidesInTimeAndSpace {α : Type*}
    {M : CountingAuxPDA k Bool StackSym State} {enc : α ↪ List Bool} {f : α → ℕ}
    {s t : α → ℕ} {A : Set α} (h : M.CountsInTimeAndSpace enc f s t)
    (hA : ∀ a, a ∈ A ↔ 0 < f a) :
    M.toAuxPDA.DecidesInTimeAndSpace enc A s t := fun a => by
  obtain ⟨hspace, hclock, hf⟩ := h a
  refine ⟨hspace, fun p hp => hclock.paths_halted p.toRunPath p.head_eq hp, (hA a).trans ?_⟩
  rw [hf, acceptCount, hclock.branchCount_pos_iff]
  exact ⟨fun ⟨p, hp, hh, hout⟩ => ⟨⟨p, hp⟩, hh, beq_iff_eq.mp hout⟩,
    fun ⟨p, hh, hout⟩ => ⟨p.toRunPath, p.head_eq, hh, beq_iff_eq.mpr hout⟩⟩

/-! ### Embedding multi-tape counting Turing machines -/

/-- Embed any `MultiTapeCTM` into a `CountingAuxPDA` with dummy stack alphabet `PUnit` that leaves
the stack unchanged (`StackOp.stay`) on every occurrence. -/
def ofMultiTapeCTM (M : MultiTapeCTM k Symbol State) :
    CountingAuxPDA k Symbol PUnit State where
  q₀ := M.initial
  tr q inp work _ :=
    (M.tr q inp work Empty.elim).map fun act =>
      ⟨MultiTapeMachine.Action.emptyOracleEquiv act, .stay⟩

lemma ofMultiTapeCTM_actions (M : MultiTapeCTM k Symbol State)
    (c : Turing.Cfg k Symbol State input) (s : List PUnit) :
    (ofMultiTapeCTM M).actions ⟨c, s⟩ = (M.actions c).map (fun act => ⟨act, .stay⟩) := by
  cases hs : c.state <;> simp [actions, MultiTapeCTM.actions, ofMultiTapeCTM, hs]

theorem ofMultiTapeCTM_toAuxPDA (M : MultiTapeCTM k Symbol State) :
    (ofMultiTapeCTM M).toAuxPDA = AuxPDA.ofMultiTapeNTM M.toNTM := by
  cases M
  simp only [toAuxPDA, ofMultiTapeCTM, AuxPDA.ofMultiTapeNTM, MultiTapeCTM.toNTM]
  congr 1
  funext q inp work top ⟨tape, stackOp⟩
  simp only [List.mem_map, AuxPDA.Action.mk.injEq, eq_iff_iff]
  exact ⟨fun ⟨a, ha, h1, h2⟩ => ⟨h2.symm, by simpa [← h1] using ha⟩,
    fun ⟨rfl, ha⟩ => ⟨MultiTapeMachine.Action.emptyOracleEquiv.symm tape, ha, by simp, rfl⟩⟩

lemma ofMultiTapeCTM_step? (M : MultiTapeCTM k Symbol State)
    (c : Turing.Cfg k Symbol State input) (s : List PUnit) (i : ℕ) :
    (ofMultiTapeCTM M).step? ⟨c, s⟩ i = (M.step? c i).map (fun c' => ⟨c', s⟩) := by
  simp only [step?, MultiTapeCTM.step?, ofMultiTapeCTM_actions, List.getElem?_map,
    Option.bind_map, Option.map_map]
  cases (M.actions c)[i]? <;> rfl

lemma ofMultiTapeCTM_runBranch (M : MultiTapeCTM k Symbol State)
    (c : Turing.Cfg k Symbol State input) (s : List PUnit) (choices : List ℕ) :
    (ofMultiTapeCTM M).runBranch ⟨c, s⟩ choices =
      (M.runBranch c choices).map (fun c' => ⟨c', s⟩) := by
  induction choices generalizing c with
  | nil => rfl
  | cons i rest ih =>
    simp only [runBranch_cons, MultiTapeCTM.runBranch_cons, ofMultiTapeCTM_step?]
    cases M.step? c i <;> [rfl; exact ih _]

theorem ofMultiTapeCTM_branches (M : MultiTapeCTM k Symbol State) (fuel : ℕ)
    (c : Turing.Cfg k Symbol State input) (s : List PUnit) :
    (ofMultiTapeCTM M).branches fuel ⟨c, s⟩ = M.branches fuel c := by
  ext choices
  simp only [mem_branches_iff, MultiTapeCTM.mem_branches_iff, ofMultiTapeCTM_runBranch,
    Option.map_eq_some_iff]
  exact ⟨fun ⟨hlen, _, ⟨c', hc', rfl⟩, hh⟩ => ⟨hlen, c', hc', hh⟩,
    fun ⟨hlen, c', hc', hh⟩ => ⟨hlen, ⟨c', s⟩, ⟨c', hc', rfl⟩, hh⟩⟩

theorem ofMultiTapeCTM_haltsWithin_iff (M : MultiTapeCTM k Symbol State) (fuel : ℕ)
    (c : Turing.Cfg k Symbol State input) (s : List PUnit) :
    (ofMultiTapeCTM M).HaltsWithin fuel ⟨c, s⟩ ↔ M.HaltsWithin fuel c := by
  induction fuel generalizing c with
  | zero => constructor <;> rintro ⟨hh⟩ <;> exact .halt hh
  | succ fuel ih =>
    refine ⟨?_, ?_⟩
    · rintro (⟨hh⟩ | ⟨hne, _, hnext⟩)
      · exact .halt hh
      · refine .step (by simpa only [ofMultiTapeCTM_actions, ne_eq, List.map_eq_nil_iff] using hne)
          fun idx => (ih _).mp (hnext ⟨idx.val, ?_⟩ ⟨(M.actions c)[idx].apply c, s⟩
            (by simp [ofMultiTapeCTM_actions, AuxPDA.Action.apply?]))
        simpa only [ofMultiTapeCTM_actions, List.length_map] using idx.isLt
    · rintro (⟨hh⟩ | ⟨hne, hnext⟩)
      · exact .halt hh
      · refine .step (by simpa only [ofMultiTapeCTM_actions, ne_eq, List.map_eq_nil_iff] using hne)
          (fun _ => by simp [ofMultiTapeCTM_actions, AuxPDA.Action.apply?])
          fun idx nextCfg hact => ?_
        have hlt : idx.val < (M.actions c).length := by
          simpa only [ofMultiTapeCTM_actions, List.length_map] using idx.isLt
        simp only [ofMultiTapeCTM_actions, List.getElem_map, AuxPDA.Action.apply?,
          AuxPDA.StackOp.apply?_stay, Option.map_some, Option.some.injEq] at hact
        exact hact ▸ (ih _).mpr (hnext ⟨idx.val, hlt⟩)

theorem ofMultiTapeCTM_acceptCount (M : MultiTapeCTM k Bool State) {input : List Bool}
    (fuel : ℕ) (c : Turing.Cfg k Bool State input) (s : List PUnit) :
    (ofMultiTapeCTM M).acceptCount fuel ⟨c, s⟩ = M.acceptCount fuel c := by
  simp only [acceptCount, MultiTapeCTM.acceptCount, branchCount, MultiTapeCTM.branchCount,
    ofMultiTapeCTM_branches, ofMultiTapeCTM_runBranch]
  exact congrArg Finset.card
    (Finset.filter_congr fun choices _ => by cases M.runBranch c choices <;> rfl)

end CountingAuxPDA

end Turing
