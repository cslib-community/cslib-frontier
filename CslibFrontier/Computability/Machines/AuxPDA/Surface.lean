/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.AuxPDA.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Surface configurations and realizable pairs for auxiliary pushdown automata

A *surface configuration* (`Turing.AuxPDA.SurfaceCfg`) of a binary auxiliary pushdown automaton
retains the control state, input head position, work-tape contents and head positions
(`Turing.Storage`), the top stack symbol (`Option StackSym`), and the three-value acceptance summary
of the write-only output tape (`Turing.AuxPDA.OutputSummary`), discarding the stack contents below
the top.

A *realizable pair* (`Turing.AuxPDA.Realizable M input s₁ s₂ d`) characterizes same-height
non-dipping subcomputations of length `d` from surface configuration `s₁` to `s₂`:
* `0` steps (`refl`),
* a single `stay` or halted step (`stay`),
* a matched `push`/`pop` pair wrapping a length-`(d - 2)` realizable pair at one higher stack level
  (`pushPop`), or
* composition at an intermediate surface configuration (`trans`).

This file proves:
1. **Exact soundness and completeness** (`realizable_iff_exists_sameHeightRun`): `Realizable` holds
   iff there exists a concrete same-height non-dipping `RunPath` of length `d` from any matching
   starting configuration, and every such path preserves the stack verbatim.
2. **Decomposition** (`realizable_decomp`): every realizable pair of length `d ≥ 2` splits either
   into a matched push/pop pair or at an intermediate surface configuration `s_mid` with positive
   sublengths `d₁ + d₂ = d` — the exact inductive structure needed for the semi-unbounded circuit
   reduction in Work Package 4 of #7920.
3. **Empty-stack halting normalization** (`withEmptyStackHalt`,
   `accepts_iff_exists_realizable_of_emptyStackHalt`): adding one draining state preserves space
   and acceptance while emptying the stack before halting within `2 * t + 1` steps.
4. **Finiteness and polynomial cardinality** (`encard_reachable_surfaceCfg_le`,
   `encard_reachable_surfaceCfg_le_pow`, `surfaceCfgBound_log_polynomiallyBounded`): under space
   `s`, at most `(n + 2) * 2 ^ O(s)` surface configurations are reachable — polynomial in `n` when
   `s(n) = O(log n)`.

This is original formalization infrastructure for cslib-frontier #7920 (Work Package 3), preparing
the surface-configuration / realizable-pair interface of Ruzzo and Venkateswaran for Work Package 4.

## Main definitions

* `Turing.AuxPDA.OutputSummary`: three-value acceptance summary of the write-only binary output.
* `Turing.AuxPDA.SurfaceCfg`: surface configurations.
* `Turing.AuxPDA.StayStep`, `Turing.AuxPDA.PushStep`, `Turing.AuxPDA.PopStep`: elementary surface
  transitions.
* `Turing.AuxPDA.SameHeightRun`, `Turing.AuxPDA.Realizable`: concrete same-height non-dipping runs
  and their inductive characterization.
* `Turing.AuxPDA.withEmptyStackHalt`: single-state stack-draining normal form.
* `Turing.AuxPDA.surfaceCfgBound`: explicit cardinality bound on bounded-space surface
  configurations.

## Main results

* `Turing.AuxPDA.SameHeightRun.last_stack_eq`: same-height non-dipping runs preserve the stack.
* `Turing.AuxPDA.realizable_iff_exists_sameHeightRun`: soundness and completeness of `Realizable`.
* `Turing.AuxPDA.realizable_decomp`: push-pop vs intermediate-midpoint decomposition for `d ≥ 2`.
* `Turing.AuxPDA.withEmptyStackHalt_accepts_iff`, `Turing.AuxPDA.withEmptyStackHalt_runsInSpace`,
  `Turing.AuxPDA.withEmptyStackHalt_runsInTime`: empty-stack halting preserves space, acceptance,
  and polynomial time.
* `Turing.AuxPDA.encard_reachable_surfaceCfg_le_pow`,
  `Turing.AuxPDA.surfaceCfgBound_log_polynomiallyBounded`: `2 ^ O(s)` and polynomial logspace
  cardinality bounds on surface configurations.

## References

* [K. Reinhardt, E. Allender, *Making Nondeterminism Unambiguous*][ReinhardtAllender2000]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.AuxPDA

/-! ### Output summary and surface configurations -/

/-- Three-value summary of the write-only binary output tape sufficient to determine `[true]`
acceptance: empty (`[]`), exactly `[true]`, or any other word. -/
inductive OutputSummary where
  /-- Empty output `[]`. -/
  | empty
  /-- Exactly the accepting output `[true]`. -/
  | accept
  /-- Any output other than `[]` and `[true]`. -/
  | other
  deriving DecidableEq, Repr

namespace OutputSummary

instance : Fintype OutputSummary where
  elems := {.empty, .accept, .other}
  complete x := by cases x <;> simp

@[simp]
lemma card : Fintype.card OutputSummary = 3 := rfl

/-- Summarize a binary output word. -/
def ofList (w : List Bool) : OutputSummary :=
  if w = [] then .empty else if w = [true] then .accept else .other

/-- A canonical representative word realizing a given `OutputSummary`. -/
def toList : OutputSummary → List Bool
  | .empty => []
  | .accept => [true]
  | .other => [false]

@[simp]
lemma ofList_toList (o : OutputSummary) : ofList o.toList = o := by
  cases o <;> rfl

@[simp]
lemma ofList_nil : ofList [] = .empty := rfl

lemma ofList_eq_accept_iff {w : List Bool} : ofList w = .accept ↔ w = [true] := by
  unfold ofList
  split_ifs <;> simp_all

/-- Update an output summary when appending an optional output bit. -/
def append (o : OutputSummary) : Option Bool → OutputSummary
  | none => o
  | some true => match o with
    | .empty => .accept
    | .accept => .other
    | .other => .other
  | some false => .other

/-- `ofList` is a homomorphism with respect to appending an optional output bit. -/
lemma ofList_append (w : List Bool) (sym : Option Bool) :
    ofList (w ++ sym.toList) = (ofList w).append sym := by
  cases sym with
  | none => simp [append]
  | some b =>
    cases w with
    | nil => cases b <;> rfl
    | cons a rest =>
      cases a <;> cases rest <;> cases b <;> rfl

end OutputSummary

/-- A surface configuration of a binary `AuxPDA` on `input`: input head position, work-tape storage
(control state, tape contents and head positions), top stack symbol (`none` if empty), and
three-value output summary. -/
@[ext]
structure SurfaceCfg (k : ℕ) (StackSym State : Type*) (input : List Bool) where
  /-- Input head position (shifted by one, matching `Turing.Cfg.inputPos`). -/
  inputPos : Fin (input.length + 2)
  /-- Control state, work-tape contents and work-tape head positions. -/
  storage : Turing.Storage Bool State k
  /-- Top symbol of the pushdown stack, or `none` when the stack is empty. -/
  topSym : Option StackSym
  /-- Acceptance summary of the write-only binary output tape. -/
  outputSummary : OutputSummary

namespace SurfaceCfg

variable {k : ℕ} {StackSym State : Type*} {input : List Bool}

/-- The input symbol under the head of a surface configuration (identical to
`Turing.Cfg.inputSymbol`). -/
def inputSymbol (s : SurfaceCfg k StackSym State input) : Option Bool :=
  if h₁ : s.inputPos = 0 then none
  else if h₂ : s.inputPos = input.length + 1 then none
  else input[s.inputPos.val - 1]'(by grind)

/-- The symbols under the work-tape heads of a surface configuration. -/
def workTapeSymbols (s : SurfaceCfg k StackSym State input) (i : Fin k) : Option Bool :=
  s.storage.workTapes i (s.storage.workTapePos i)

/-- A surface configuration is halted when its control state is `none`. -/
abbrev Halted (s : SurfaceCfg k StackSym State input) : Prop :=
  s.storage.state = none

/-- A surface configuration is accepting when it is halted with output summary `.accept`. -/
abbrev IsAccepting (s : SurfaceCfg k StackSym State input) : Prop :=
  s.Halted ∧ s.outputSummary = .accept

/-- A canonical concrete configuration having surface `s` (stack `s.topSym.toList` and canonical
output word `s.outputSummary.toList`). -/
def toRepresentativeCfg (s : SurfaceCfg k StackSym State input) :
    Cfg k Bool StackSym State input where
  tapes :=
    ⟨s.storage.state, s.inputPos, s.storage.workTapes, s.storage.workTapePos,
      s.outputSummary.toList⟩
  stack := s.topSym.toList

end SurfaceCfg

/-- Project a concrete binary `AuxPDA` configuration to its surface configuration. -/
def Cfg.surface {k : ℕ} {StackSym State : Type*} {input : List Bool}
    (c : Cfg k Bool StackSym State input) : SurfaceCfg k StackSym State input where
  inputPos := c.tapes.inputPos
  storage := c.tapes.storage
  topSym := c.topSym
  outputSummary := OutputSummary.ofList c.tapes.output

lemma Cfg.surface_toRepresentativeCfg {k : ℕ} {StackSym State : Type*} {input : List Bool}
    (s : SurfaceCfg k StackSym State input) :
    s.toRepresentativeCfg.surface = s := by
  refine SurfaceCfg.ext rfl (Turing.Storage.ext rfl rfl rfl) ?_
    (OutputSummary.ofList_toList s.outputSummary)
  cases h : s.topSym <;> simp [SurfaceCfg.toRepresentativeCfg, Cfg.surface, Cfg.topSym, h]

lemma Cfg.surface_inputSymbol {k : ℕ} {StackSym State : Type*} {input : List Bool}
    (c : Cfg k Bool StackSym State input) :
    c.surface.inputSymbol = c.tapes.inputSymbol := rfl

lemma Cfg.surface_workTapeSymbols {k : ℕ} {StackSym State : Type*} {input : List Bool}
    (c : Cfg k Bool StackSym State input) :
    c.surface.workTapeSymbols = c.tapes.workTapeSymbols := rfl

lemma Cfg.isAccepting_surface_iff {k : ℕ} {StackSym State : Type*} {input : List Bool}
    (c : Cfg k Bool StackSym State input) :
    c.surface.IsAccepting ↔ c.Halted ∧ c.tapes.output = [true] :=
  and_congr Iff.rfl OutputSummary.ofList_eq_accept_iff

/-- The initial surface configuration of `M` on `input`. -/
def initSurface {k : ℕ} {StackSym State : Type*}
    (M : AuxPDA k Bool StackSym State) (input : List Bool) :
    SurfaceCfg k StackSym State input :=
  (M.initCfg input).surface

/-- Apply the tape and output components of a `Turing.Action` to a surface configuration, installing
`newTop` as the resulting top stack symbol. -/
def applySurfaceTapes {k : ℕ} {StackSym State : Type*} {input : List Bool}
    (act : Turing.Action k Bool State)
    (s : SurfaceCfg k StackSym State input) (newTop : Option StackSym) :
    SurfaceCfg k StackSym State input where
  inputPos := moveInputPos s.inputPos act.inputTape
  storage :=
    { state := act.state
      workTapes := fun i => match (act.workTapes i).1 with
        | none => s.storage.workTapes i
        | some sym => Function.update (s.storage.workTapes i) (s.storage.workTapePos i) sym
      workTapePos := fun i => s.storage.workTapePos i + (act.workTapes i).2 }
  topSym := newTop
  outputSummary := s.outputSummary.append act.output

lemma surface_apply_eq_applySurfaceTapes {k : ℕ} {StackSym State : Type*} {input : List Bool}
    (act : Turing.Action k Bool State) (c : Cfg k Bool StackSym State input)
    (stack' : List StackSym) :
    (⟨act.apply c.tapes, stack'⟩ : Cfg k Bool StackSym State input).surface =
      applySurfaceTapes act c.surface stack'.head? := by
  refine SurfaceCfg.ext rfl (Turing.Storage.ext rfl ?_ rfl) rfl
    (OutputSummary.ofList_append c.tapes.output act.output)
  funext i
  simp only [Cfg.surface, Turing.Cfg.storage, Turing.Action.apply, applySurfaceTapes]
  cases (act.workTapes i).1 <;> rfl

/-! ### Elementary surface steps and realizable pairs -/

variable {k : ℕ} {StackSym State : Type*} {input : List Bool}

/-- A single height-preserving surface transition (either a halted self-loop or a `.stay` step). -/
def StayStep (M : AuxPDA k Bool StackSym State)
    (s₁ s₂ : SurfaceCfg k StackSym State input) : Prop :=
  (s₁.Halted ∧ s₂ = s₁) ∨
    ∃ q act, s₁.storage.state = some q ∧
      M.Tr q s₁.inputSymbol s₁.workTapeSymbols s₁.topSym act ∧
      act.stackOp = .stay ∧
      s₂ = applySurfaceTapes act.tape s₁ s₁.topSym

/-- A single `.push γ` surface transition from `s₁` to `s₂` (so `s₂.topSym = some γ`). -/
def PushStep (M : AuxPDA k Bool StackSym State)
    (s₁ : SurfaceCfg k StackSym State input) (γ : StackSym)
    (s₂ : SurfaceCfg k StackSym State input) : Prop :=
  ∃ q act, s₁.storage.state = some q ∧
    M.Tr q s₁.inputSymbol s₁.workTapeSymbols s₁.topSym act ∧
    act.stackOp = .push γ ∧
    s₂ = applySurfaceTapes act.tape s₁ (some γ)

/-- A single `.pop` surface transition from `s₁` (whose top is `some γ`) exposing underlying stack
top `baseTop` in `s₂`. -/
def PopStep (M : AuxPDA k Bool StackSym State)
    (s₁ : SurfaceCfg k StackSym State input) (γ : StackSym) (baseTop : Option StackSym)
    (s₂ : SurfaceCfg k StackSym State input) : Prop :=
  s₁.topSym = some γ ∧
    ∃ q act, s₁.storage.state = some q ∧
      M.Tr q s₁.inputSymbol s₁.workTapeSymbols (some γ) act ∧
      act.stackOp = .pop ∧
      s₂ = applySurfaceTapes act.tape s₁ baseTop

/-- A concrete run path is a *same-height non-dipping run* when its final stack height equals its
initial stack height and no intermediate configuration drops below that height. -/
def SameHeightRun {M : AuxPDA k Bool StackSym State} (p : M.RunPath input) : Prop :=
  p.last.stack.length = p.head.stack.length ∧
    ∀ i : Fin (p.length + 1), p.head.stack.length ≤ (p i).stack.length

/-- Inductive characterization of realizable surface pairs of exact step length `d`:
`M.Realizable input s₁ s₂ d` holds iff `s₁` reaches `s₂` in `d` steps while never dropping below
its starting stack height and ending at the same stack height. -/
inductive Realizable (M : AuxPDA k Bool StackSym State) (input : List Bool) :
    SurfaceCfg k StackSym State input → SurfaceCfg k StackSym State input → ℕ → Prop
  /-- Zero-step realizability. -/
  | refl (s : SurfaceCfg k StackSym State input) : Realizable M input s s 0
  /-- A single height-preserving (`stay` or halted) step. -/
  | stay {s₁ s₂ : SurfaceCfg k StackSym State input} (h : M.StayStep s₁ s₂) :
      Realizable M input s₁ s₂ 1
  /-- A matched push-pop pair wrapping a realizable pair at one higher stack level. -/
  | pushPop {s₁ s₂ s' s'' : SurfaceCfg k StackSym State input} {γ : StackSym} {d : ℕ}
      (hpush : M.PushStep s₁ γ s')
      (hmid : Realizable M input s' s'' d)
      (hpop : M.PopStep s'' γ s₁.topSym s₂) :
      Realizable M input s₁ s₂ (d + 2)
  /-- Sequential composition at an intermediate surface configuration `s_mid`. -/
  | trans {s₁ s_mid s₂ : SurfaceCfg k StackSym State input} {d₁ d₂ : ℕ}
      (h₁ : Realizable M input s₁ s_mid d₁)
      (h₂ : Realizable M input s_mid s₂ d₂) :
      Realizable M input s₁ s₂ (d₁ + d₂)

/-- A one-step run path from a single step `h : M.Step c₁ c₂`. -/
private def runPathOfStep {Symbol : Type*} {input : List Symbol}
    {M : AuxPDA k Symbol StackSym State}
    {c₁ c₂ : Cfg k Symbol StackSym State input} (h : M.Step c₁ c₂) : M.RunPath input where
  length := 1
  toFun
    | ⟨0, _⟩ => c₁
    | ⟨1, _⟩ => c₂
  step i := by fin_cases i; exact h

/-- Soundness of `Realizable`: every realizable pair lifts from any matching concrete starting
configuration `c₁` to a same-height non-dipping run path preserving the stack verbatim. -/
theorem Realizable.exists_sameHeightRun {M : AuxPDA k Bool StackSym State}
    {s₁ s₂ : SurfaceCfg k StackSym State input} {d : ℕ} (h : M.Realizable input s₁ s₂ d)
    {c₁ : Cfg k Bool StackSym State input} (hc₁ : c₁.surface = s₁) :
    ∃ p : M.RunPath input, p.head = c₁ ∧ p.last.surface = s₂ ∧ p.last.stack = c₁.stack ∧
      p.length = d ∧ SameHeightRun p := by
  induction h generalizing c₁ with
  | refl s =>
    refine ⟨RelSeries.singleton _ c₁, rfl, hc₁, rfl, rfl, rfl, fun _ => ?_⟩
    rw [RelSeries.head_singleton]
    exact le_rfl
  | stay hstay =>
    subst hc₁
    rcases hstay with ⟨hhalt, rfl⟩ | ⟨q, act, hq, htr, hstay, rfl⟩
    · refine ⟨runPathOfStep ((step_of_halt hhalt).mpr rfl), rfl, rfl, rfl, rfl, rfl, fun i => ?_⟩
      fin_cases i <;> exact le_rfl
    · let c₂ : Cfg k Bool StackSym State input := ⟨act.tape.apply c₁.tapes, c₁.stack⟩
      have hstep : M.Step c₁ c₂ := by
        simp only [Step, show c₁.tapes.state = some q from hq]
        exact ⟨act, htr, Action.apply?_eq_some_iff.mpr ⟨c₁.stack, by rw [hstay]; rfl, rfl⟩⟩
      refine ⟨runPathOfStep hstep, rfl, surface_apply_eq_applySurfaceTapes act.tape c₁ c₁.stack,
        rfl, rfl, rfl, fun i => ?_⟩
      fin_cases i <;> exact le_rfl
  | @pushPop s₁ s₂ s' s'' γ d hpush hmid hpop ih =>
    subst hc₁
    obtain ⟨q₁, act₁, hq₁, htr₁, hpushOp, hs'⟩ := hpush
    let c' : Cfg k Bool StackSym State input := ⟨act₁.tape.apply c₁.tapes, γ :: c₁.stack⟩
    have hstep₁ : M.Step c₁ c' := by
      simp only [Step, show c₁.tapes.state = some q₁ from hq₁]
      exact ⟨act₁, htr₁, Action.apply?_eq_some_iff.mpr ⟨γ :: c₁.stack, by rw [hpushOp]; rfl, rfl⟩⟩
    have hc'surf : c'.surface = s' :=
      (surface_apply_eq_applySurfaceTapes act₁.tape c₁ (γ :: c₁.stack)).trans hs'.symm
    obtain ⟨pmid, hmidHead, hmidSurf, hmidStack, hmidLen, -, hmidGe⟩ := ih hc'surf
    obtain ⟨_, q₂, act₂, hq₂, htr₂, hpopOp, hs₂⟩ := hpop
    have htop₂' : pmid.last.topSym = some γ := congrArg List.head? hmidStack
    have hq₂' : pmid.last.tapes.state = some q₂ := by rwa [← hmidSurf] at hq₂
    have htr₂' : M.Tr q₂ pmid.last.tapes.inputSymbol pmid.last.tapes.workTapeSymbols
        pmid.last.topSym act₂ := by
      rw [← hmidSurf] at htr₂
      rwa [htop₂']
    let c₂ : Cfg k Bool StackSym State input := ⟨act₂.tape.apply pmid.last.tapes, c₁.stack⟩
    have hstep₂ : M.Step pmid.last c₂ := by
      simp only [Step, hq₂']
      refine ⟨act₂, htr₂', Action.apply?_eq_some_iff.mpr ⟨c₁.stack, ?_, rfl⟩⟩
      rw [hpopOp, hmidStack]
      rfl
    have hc₂surf : c₂.surface = s₂ := by
      rw [hs₂, ← hmidSurf]
      exact surface_apply_eq_applySurfaceTapes act₂.tape pmid.last c₁.stack
    let p : M.RunPath input :=
      (pmid.cons c₁ (hmidHead.symm ▸ hstep₁)).snoc c₂ (by simpa using hstep₂)
    refine ⟨p, by simp [p], by simpa [p] using hc₂surf, by simp [p, c₂], by simp [p, hmidLen],
      by simp [p, c₂], fun i => ?_⟩
    rw [show p.head = c₁ by simp [p]]
    rcases RelSeries.mem_snoc.mp (⟨i, rfl⟩ : p i ∈ p) with hcons | heq
    · rw [← RelSeries.mem_toList, RelSeries.toList_cons, List.mem_cons,
        RelSeries.mem_toList] at hcons
      rcases hcons with heq₁ | ⟨j, hj⟩
      · rw [heq₁]
      · have hkGe := hmidGe j
        rw [hj, hmidHead] at hkGe
        simp only [c', List.length_cons] at hkGe
        omega
    · rw [heq]
  | @trans s₁ s_mid s₂ d₁ d₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨p₁, hp₁Head, hp₁Surf, hp₁Stack, hp₁Len, -, hp₁Ge⟩ := ih₁ hc₁
    obtain ⟨p₂, hp₂Head, hp₂Surf, hp₂Stack, hp₂Len, -, hp₂Ge⟩ := ih₂ hp₁Surf
    let p : M.RunPath input := p₁.smash p₂ hp₂Head.symm
    refine ⟨p, by simp [p, hp₁Head], by simpa [p] using hp₂Surf,
      by rw [RelSeries.last_smash, hp₂Stack, hp₁Stack], by simp [p, hp₁Len, hp₂Len],
      by rw [RelSeries.last_smash, RelSeries.head_smash, hp₁Head, hp₂Stack, hp₁Stack], fun i => ?_⟩
    rw [show p.head = c₁ by simp [p, hp₁Head]]
    rcases RelSeries.mem_or_mem_of_mem_smash (⟨i, rfl⟩ : p i ∈ p) with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [← hj, ← hp₁Head]
      exact hp₁Ge j
    · rw [← hj]
      have hge := hp₂Ge j
      rwa [hp₂Head, hp₁Stack] at hge

private lemma stackOp_pop_length {s s' : List StackSym}
    (h : StackOp.pop.apply? s = some s') : s'.length + 1 = s.length := by
  cases s with
  | nil => cases h
  | cons _ _ =>
    simp only [StackOp.apply?_pop_cons, Option.some.injEq] at h
    subst h
    simp

/-- Structural split of any `SameHeightRun` of length `d' + 2`: either it hits the base stack
height at an interior index `0 < j < p.length`, or it consists of a first `push γ`, an interior
`SameHeightRun` of length `d'` one level higher whose configurations all belong to `p`, and a
final `pop` step. -/
theorem sameHeightRun_split_ge_two {M : AuxPDA k Bool StackSym State} {d' : ℕ}
    (p : M.RunPath input) (hlen : p.length = d' + 2) (hsame : SameHeightRun p) :
    (∃ j : Fin (p.length + 1), 0 < j.val ∧ j.val < p.length ∧
      SameHeightRun (p.take j) ∧ SameHeightRun (p.drop j)) ∨
    (∃ (γ : StackSym) (pmid : M.RunPath input),
      pmid.length = d' ∧
      SameHeightRun pmid ∧
      (∀ c ∈ pmid, c ∈ p) ∧
      pmid.head.stack = γ :: p.head.stack ∧
      M.PushStep p.head.surface γ pmid.head.surface ∧
      (pmid.last.stack = γ :: p.head.stack →
        p.last.stack = p.head.stack ∧
        M.PopStep pmid.last.surface γ p.head.surface.topSym p.last.surface)) := by
  obtain ⟨hlastLen, hge⟩ := hsame
  by_cases hmid : ∃ j : Fin (p.length + 1), 0 < j.val ∧ j.val < p.length ∧
      (p j).stack.length = p.head.stack.length
  · left
    obtain ⟨j, hjpos, hjlt, hjlen⟩ := hmid
    refine ⟨j, hjpos, hjlt, ?_, ?_⟩
    · refine ⟨by simpa only [RelSeries.last_take, RelSeries.head_take] using hjlen, fun i => ?_⟩
      rw [RelSeries.head_take]
      exact hge (Fin.castLE j.isLt i)
    · refine ⟨by simpa only [RelSeries.last_drop, RelSeries.head_drop, hjlen] using hlastLen,
        fun ⟨iv, hiv⟩ => ?_⟩
      rw [RelSeries.head_drop, hjlen]
      exact hge ⟨iv + j.val, by dsimp only [RelSeries.drop] at hiv; omega⟩
  · right
    push Not at hmid
    have hstrict (j : Fin (p.length + 1)) (hj0 : 0 < j.val) (hjlt : j.val < p.length) :
        p.head.stack.length + 1 ≤ (p j).stack.length :=
      Nat.lt_of_le_of_ne (hge j) (Ne.symm (hmid j hj0 hjlt))
    have h1lt : 1 < p.length + 1 := by omega
    have hstep1 : M.Step p.head (p ⟨1, h1lt⟩) := p.step ⟨0, by omega⟩
    have h1eq : (p ⟨1, h1lt⟩).stack.length = p.head.stack.length + 1 := by
      have := hstrict ⟨1, h1lt⟩ Nat.zero_lt_one (by simp; omega)
      have := Step.stackHeight_le hstep1
      omega
    obtain ⟨γ, h1stack, hpush⟩ : ∃ γ, (p ⟨1, h1lt⟩).stack = γ :: p.head.stack ∧
        M.PushStep p.head.surface γ (p ⟨1, h1lt⟩).surface := by
      cases hq : p.head.tapes.state with
      | none => rw [(step_of_halt hq).mp hstep1] at h1eq; omega
      | some q =>
        simp only [Step, hq] at hstep1
        obtain ⟨act, htr, hact⟩ := hstep1
        obtain ⟨stack', hstack, h1cfg⟩ := Action.apply?_eq_some_iff.mp hact
        cases hop : act.stackOp with
        | stay =>
          rw [hop, StackOp.apply?_stay, Option.some.injEq] at hstack
          subst hstack; simp [h1cfg] at h1eq
        | pop =>
          have := stackOp_pop_length (hop ▸ hstack)
          simp only [h1cfg] at h1eq
          omega
        | push γ =>
          rw [hop, StackOp.apply?_push, Option.some.injEq] at hstack
          subst hstack
          exact ⟨γ, by simp [h1cfg], ⟨q, act, hq, htr, hop,
            h1cfg ▸ surface_apply_eq_applySurfaceTapes act.tape p.head (γ :: p.head.stack)⟩⟩
    have hpenlt : p.length - 1 < p.length + 1 := by omega
    have hstepLast : M.Step (p ⟨p.length - 1, hpenlt⟩) p.last := by
      have hl : p ⟨p.length - 1 + 1, by omega⟩ = p.last :=
        congrArg p (Fin.ext (by simp; omega))
      exact hl ▸ p.step ⟨p.length - 1, by omega⟩
    have hpeneq : (p ⟨p.length - 1, hpenlt⟩).stack.length = p.head.stack.length + 1 := by
      have hpen : 0 < p.length - 1 ∧ p.length - 1 < p.length := by omega
      have := hstrict ⟨p.length - 1, hpenlt⟩ hpen.1 hpen.2
      have := Step.le_stackHeight_add_one hstepLast
      omega
    let pmid : M.RunPath input :=
      ⟨d', fun i => p ⟨i.val + 1, by omega⟩, fun i => p.step ⟨i.val + 1, by omega⟩⟩
    have hmidLast : pmid.last = p ⟨p.length - 1, hpenlt⟩ :=
      congrArg p (Fin.ext (by simp [pmid]; omega))
    have hmidSame : SameHeightRun pmid :=
      ⟨(congrArg List.length (congrArg Cfg.stack hmidLast)).trans (hpeneq.trans h1eq.symm),
        fun i => by
          have : i.val < d' + 1 := i.isLt
          exact h1eq.trans_le (hstrict ⟨i.val + 1, by omega⟩ (Nat.succ_pos _)
            (by simp; omega))⟩
    refine ⟨γ, pmid, rfl, hmidSame,
      fun _ ⟨i, hi⟩ => ⟨⟨i.val + 1, by have := i.isLt; dsimp only [pmid] at this; omega⟩, hi⟩,
      h1stack, hpush, fun hpenStack => ?_⟩
    rw [hmidLast] at hpenStack ⊢
    cases hq : (p ⟨p.length - 1, hpenlt⟩).tapes.state with
    | none => rw [(step_of_halt hq).mp hstepLast] at hlastLen; omega
    | some q =>
      simp only [Step, hq] at hstepLast
      obtain ⟨act, htr, hact⟩ := hstepLast
      obtain ⟨stack', hstack, hlastCfg⟩ := Action.apply?_eq_some_iff.mp hact
      cases hop : act.stackOp with
      | stay =>
        rw [hop, StackOp.apply?_stay, Option.some.injEq] at hstack
        subst hstack; simp [hlastCfg, hpenStack] at hlastLen
      | push γ' =>
        rw [hop, StackOp.apply?_push, Option.some.injEq] at hstack
        subst hstack; simp [hlastCfg, hpenStack] at hlastLen; omega
      | pop =>
        rw [hop, hpenStack, StackOp.apply?_pop_cons, Option.some.injEq] at hstack
        subst hstack
        have htopPen : (p ⟨p.length - 1, hpenlt⟩).surface.topSym = some γ := by
          simp [Cfg.surface, Cfg.topSym, hpenStack]
        exact ⟨by simp [hlastCfg], htopPen, q, act, hq, htopPen ▸ htr, hop,
          hlastCfg ▸ surface_apply_eq_applySurfaceTapes act.tape _ p.head.stack⟩

/-- Completeness and stack preservation for concrete same-height non-dipping runs. -/
private theorem sameHeightRun_stack_and_realizable {M : AuxPDA k Bool StackSym State} (d : ℕ) :
    ∀ (p : M.RunPath input), p.length = d → SameHeightRun p →
      p.last.stack = p.head.stack ∧ M.Realizable input p.head.surface p.last.surface d := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro p hlen hsame
    match d with
    | 0 =>
      rw [show p.last = p.head from congrArg p (Fin.ext hlen)]
      exact ⟨rfl, .refl _⟩
    | 1 =>
      have hstep : M.Step p.head p.last := by
        have h1 : p ⟨1, by omega⟩ = p.last :=
          congrArg p (Fin.ext (by simp; omega))
        exact h1 ▸ p.step ⟨0, by omega⟩
      cases hq : p.head.tapes.state with
      | none =>
        rw [(step_of_halt hq).mp hstep]
        exact ⟨rfl, .stay (.inl ⟨hq, rfl⟩)⟩
      | some q =>
        simp only [Step, hq] at hstep
        obtain ⟨act, htr, hact⟩ := hstep
        obtain ⟨stack', hstack, hpLast⟩ := Action.apply?_eq_some_iff.mp hact
        cases hop : act.stackOp with
        | stay =>
          rw [hop, StackOp.apply?_stay, Option.some.injEq] at hstack
          subst hstack
          exact ⟨by simp [hpLast], .stay (.inr ⟨q, act, hq, htr, hop,
            hpLast ▸ surface_apply_eq_applySurfaceTapes act.tape p.head p.head.stack⟩)⟩
        | push γ =>
          rw [hop, StackOp.apply?_push, Option.some.injEq] at hstack
          subst hstack; have := hsame.1; simp [hpLast] at this
        | pop =>
          have := stackOp_pop_length (hop ▸ hstack)
          have := hsame.1
          simp only [hpLast] at this
          omega
    | d' + 2 =>
      rcases sameHeightRun_split_ge_two p hlen hsame with
        ⟨j, hjpos, hjlt, h1, h2⟩ | ⟨γ, pmid, hmidLen, hmidSame, -, hmidHeadStack, hpush, hpopFn⟩
      · obtain ⟨h1Stack, h1Real⟩ := ih j.val (by omega) (p.take j) rfl h1
        obtain ⟨h2Stack, h2Real⟩ :=
          ih (p.length - j.val) (by omega) (p.drop j) (RelSeries.drop_length p j) h2
        rw [RelSeries.head_take, RelSeries.last_take] at h1Stack h1Real
        rw [RelSeries.head_drop, RelSeries.last_drop] at h2Stack h2Real
        exact ⟨h2Stack.trans h1Stack, (show j.val + (p.length - j.val) = d' + 2 by omega) ▸
          .trans h1Real h2Real⟩
      · obtain ⟨hmidStack, hmidReal⟩ := ih d' (by omega) pmid hmidLen hmidSame
        obtain ⟨hlastStack, hpop⟩ := hpopFn (hmidStack.trans hmidHeadStack)
        exact ⟨hlastStack, .pushPop hpush hmidReal hpop⟩

/-- **Stack preservation**: every concrete same-height non-dipping run preserves the stack
verbatim. -/
theorem SameHeightRun.last_stack_eq {M : AuxPDA k Bool StackSym State}
    {p : M.RunPath input} (h : SameHeightRun p) : p.last.stack = p.head.stack :=
  (sameHeightRun_stack_and_realizable p.length p rfl h).1

/-- **Soundness and completeness of `Realizable`**: from any concrete configuration `c₁` with
surface `s₁`, `M.Realizable input s₁ s₂ d` holds iff there is a length-`d` same-height non-dipping
run path from `c₁` to a configuration with surface `s₂`. -/
theorem realizable_iff_exists_sameHeightRun {M : AuxPDA k Bool StackSym State}
    {s₁ s₂ : SurfaceCfg k StackSym State input} {d : ℕ}
    {c₁ : Cfg k Bool StackSym State input} (hc₁ : c₁.surface = s₁) :
    M.Realizable input s₁ s₂ d ↔
      ∃ p : M.RunPath input, p.head = c₁ ∧ p.last.surface = s₂ ∧ p.length = d ∧
        SameHeightRun p := by
  refine ⟨fun h => ?_, fun ⟨p, hhead, hsurf, hlen, hsame⟩ => ?_⟩
  · obtain ⟨p, hhead, hsurf, -, hlen, hsame⟩ := h.exists_sameHeightRun hc₁
    exact ⟨p, hhead, hsurf, hlen, hsame⟩
  · simpa only [hhead, hc₁, hsurf] using (sameHeightRun_stack_and_realizable d p hlen hsame).2

/-- **Surface-pair realizability decomposition** (Ruzzo / Venkateswaran): for `d ≥ 2`, a surface
pair `(s₁, s₂)` is realizable in `d` steps iff it either splits as a matched push-pop pair
wrapping a `(d - 2)`-step realizable pair, or splits at an intermediate surface configuration
`s_mid` with positive sublengths `d₁ + d₂ = d`. -/
theorem realizable_decomp {M : AuxPDA k Bool StackSym State}
    {s₁ s₂ : SurfaceCfg k StackSym State input} {d : ℕ} (hd : 2 ≤ d) :
    M.Realizable input s₁ s₂ d ↔
      (∃ γ s' s'', M.PushStep s₁ γ s' ∧ M.Realizable input s' s'' (d - 2) ∧
        M.PopStep s'' γ s₁.topSym s₂) ∨
      (∃ s_mid d₁ d₂, 0 < d₁ ∧ 0 < d₂ ∧ d₁ + d₂ = d ∧
        M.Realizable input s₁ s_mid d₁ ∧ M.Realizable input s_mid s₂ d₂) := by
  constructor
  · intro h
    obtain ⟨p, hhead, hsurf, hlen, hsame⟩ :=
      (realizable_iff_exists_sameHeightRun (Cfg.surface_toRepresentativeCfg s₁)).mp h
    have hheadSurf : p.head.surface = s₁ := by rw [hhead, Cfg.surface_toRepresentativeCfg]
    rcases sameHeightRun_split_ge_two (d' := d - 2) p (by omega) hsame with
      ⟨j, hjpos, hjlt, h1, h2⟩ | ⟨γ, pmid, hmidLen, hmidSame, -, hmidHeadStack, hpush, hpopFn⟩
    · right
      have h1Real := (sameHeightRun_stack_and_realizable j.val (p.take j) rfl h1).2
      have h2Real := (sameHeightRun_stack_and_realizable (p.length - j.val) (p.drop j)
        (RelSeries.drop_length p j) h2).2
      rw [RelSeries.head_take, RelSeries.last_take, hheadSurf] at h1Real
      rw [RelSeries.head_drop, RelSeries.last_drop, hsurf] at h2Real
      exact ⟨(p j).surface, j.val, p.length - j.val, hjpos, by omega, by omega, h1Real, h2Real⟩
    · left
      obtain ⟨hmidStack, hmidReal⟩ :=
        sameHeightRun_stack_and_realizable (d - 2) pmid hmidLen hmidSame
      obtain ⟨-, hpop⟩ := hpopFn (hmidStack.trans hmidHeadStack)
      rw [hheadSurf] at hpush hpop
      rw [hsurf] at hpop
      exact ⟨γ, pmid.head.surface, pmid.last.surface, hpush, hmidReal, hpop⟩
  · rintro (⟨γ, s', s'', hpush, hmid, hpop⟩ | ⟨s_mid, d₁, d₂, -, -, hsum, h₁, h₂⟩)
    · have heq : (d - 2) + 2 = d := by omega
      exact heq ▸ .pushPop hpush hmid hpop
    · exact hsum ▸ .trans h₁ h₂

/-- When every halted computation path of `M` ends with an empty stack, acceptance is equivalent
to realizability from `initSurface` to some empty-stack accepting surface configuration. -/
theorem accepts_iff_exists_realizable_of_emptyStackHalt {M : AuxPDA k Bool StackSym State}
    (hempty : ∀ p : M.ComputationPath input, p.last.Halted → p.last.stack = []) :
    M.Accepts input ↔
      ∃ s_acc d, s_acc.IsAccepting ∧ s_acc.topSym = none ∧
        M.Realizable input (M.initSurface input) s_acc d := by
  constructor
  · rintro ⟨p, hhalt, hout⟩
    have hstack : p.last.stack = [] := hempty p hhalt
    have hsame : SameHeightRun p.toRunPath := by
      refine ⟨by simp [hstack, p.head_eq], fun i => by simp [p.head_eq]⟩
    refine ⟨p.last.surface, p.length,
      (Cfg.isAccepting_surface_iff p.last).mpr ⟨hhalt, hout⟩,
      by simp [Cfg.surface, hstack], ?_⟩
    exact (realizable_iff_exists_sameHeightRun rfl).mpr
      ⟨p.toRunPath, p.head_eq, rfl, rfl, hsame⟩
  · rintro ⟨s_acc, d, hacc, -, hreal⟩
    obtain ⟨p, hhead, hsurf, -, -⟩ := (realizable_iff_exists_sameHeightRun rfl).mp hreal
    obtain ⟨hhalt, hout⟩ := (Cfg.isAccepting_surface_iff p.last).mp (hsurf ▸ hacc)
    exact ⟨⟨p, hhead⟩, hhalt, hout⟩

/-! ### Empty-stack halting normalization -/

/-- Normalize an `AuxPDA` so every halted computation path ends with an empty stack: add one
stack-draining state (`none : Option State`) entered whenever the original machine would halt,
popping until the stack is empty without moving any tape heads or emitting output. -/
def withEmptyStackHalt {Symbol : Type*} (M : AuxPDA k Symbol StackSym State) :
    AuxPDA k Symbol StackSym (Option State) where
  q₀ := some M.q₀
  Tr q inp work top act :=
    match q with
    | some q' =>
      ∃ orig : AuxPDA.Action k Symbol StackSym State,
        M.Tr q' inp work top orig ∧
        act.stackOp = orig.stackOp ∧
        act.tape =
          { inputTape := orig.tape.inputTape
            workTapes := orig.tape.workTapes
            output := orig.tape.output
            state := some orig.tape.state }
    | none =>
      act.tape =
        { inputTape := 0
          workTapes := fun _ => (none, 0)
          output := none
          state := if top.isSome then some none else none } ∧
      act.stackOp = if top.isSome then .pop else .stay

private def liftCfgToDrain {Symbol : Type*} {input : List Symbol}
    (c : Cfg k Symbol StackSym State input) :
    Cfg k Symbol StackSym (Option State) input :=
  ⟨c.tapes.mapState some, c.stack⟩

private def projectDrainCfg {Symbol : Type*} {input : List Symbol}
    (c : Cfg k Symbol StackSym (Option State) input) :
    Cfg k Symbol StackSym State input :=
  ⟨c.tapes.mapState Option.join, c.stack⟩

private lemma withEmptyStackHalt_step_cases {Symbol : Type*} {input : List Symbol}
    {M : AuxPDA k Symbol StackSym State}
    {c₁ c₂ : Cfg k Symbol StackSym (Option State) input}
    (h : M.withEmptyStackHalt.Step c₁ c₂) :
    (c₁.tapes.state = none ∧ c₂ = c₁) ∨
    (c₁.tapes.state = some none ∧
      c₂.tapes.workTapes = c₁.tapes.workTapes ∧
      c₂.tapes.workTapePos = c₁.tapes.workTapePos ∧
      c₂.tapes.inputPos = c₁.tapes.inputPos ∧
      c₂.tapes.output = c₁.tapes.output ∧
      ((c₁.stack = [] ∧ c₂.tapes.state = none ∧ c₂.stack = []) ∨
       (∃ γ rest, c₁.stack = γ :: rest ∧ c₂.tapes.state = some none ∧ c₂.stack = rest))) ∨
    (∃ q, c₁.tapes.state = some (some q) ∧ M.Step (projectDrainCfg c₁) (projectDrainCfg c₂) ∧
      ∃ q', c₂.tapes.state = some q') := by
  cases hs : c₁.tapes.state with
  | none => exact .inl ⟨rfl, (step_of_halt hs).mp h⟩
  | some qs =>
    cases qs with
    | none =>
      right; left
      simp only [Step, withEmptyStackHalt, hs] at h
      obtain ⟨act, ⟨htape, hop⟩, hact⟩ := h
      obtain ⟨stack', hstack, rfl⟩ := Action.apply?_eq_some_iff.mp hact
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      · funext i; simp [Turing.Action.apply, htape]
      · funext i; simp [Turing.Action.apply, htape]
      · simp [Turing.Action.apply, htape]
      · simp [Turing.Action.apply, htape]
      · cases hst : c₁.stack with
        | nil =>
          left
          simp only [Cfg.topSym, hst, List.head?_nil, Option.isSome_none, Bool.false_eq_true,
            ↓reduceIte] at htape hop
          rw [hop, hst, StackOp.apply?_stay, Option.some.injEq] at hstack
          exact ⟨rfl, by simp [Turing.Action.apply, htape], hstack.symm⟩
        | cons γ rest =>
          right
          simp only [Cfg.topSym, hst, List.head?_cons, Option.isSome_some, ↓reduceIte] at htape hop
          rw [hop, hst, StackOp.apply?_pop_cons, Option.some.injEq] at hstack
          exact ⟨γ, rest, rfl, by simp [Turing.Action.apply, htape], hstack.symm⟩
    | some q =>
      right; right
      simp only [Step, withEmptyStackHalt, hs] at h
      obtain ⟨act, ⟨orig, htr, hop, htape⟩, hact⟩ := h
      obtain ⟨stack', hstack, rfl⟩ := Action.apply?_eq_some_iff.mp hact
      refine ⟨q, rfl, ?_, orig.tape.state, by simp [Turing.Action.apply, htape]⟩
      simp only [Step, projectDrainCfg, Turing.Cfg.mapState, hs, Option.join_some]
      refine ⟨orig, htr, Action.apply?_eq_some_iff.mpr ⟨stack', hop ▸ hstack, ?_⟩⟩
      ext <;> simp [Turing.Action.apply, htape]

/-- Every halted computation path of `M.withEmptyStackHalt` has an empty stack. -/
theorem withEmptyStackHalt_halted_stack_nil {Symbol : Type*} {input : List Symbol}
    {M : AuxPDA k Symbol StackSym State} (p : M.withEmptyStackHalt.ComputationPath input)
    (hhalt : p.last.Halted) : p.last.stack = [] := by
  suffices h : ∀ (q : M.withEmptyStackHalt.RunPath input),
      (q.head.Halted → q.head.stack = []) → q.last.Halted → q.last.stack = [] by
    refine h p.toRunPath (fun hh => ?_) hhalt
    rw [p.head_eq] at hh
    simp [withEmptyStackHalt, Cfg.Halted, Turing.Cfg.Halted] at hh
  intro q
  induction q using RelSeries.inductionOn' with
  | singleton c => exact fun h0 h => h0 h
  | snoc q c hc ih =>
    intro h0 hlast
    have hih := ih (by simpa using h0)
    rcases withEmptyStackHalt_step_cases hc with
      ⟨hq, rfl⟩ | ⟨-, -, -, -, -, hcase⟩ | ⟨-, -, -, q', hq'⟩
    · simpa using hih hq
    · rcases hcase with ⟨-, -, hcStack⟩ | ⟨_, _, -, hstate, -⟩
      · simpa using hcStack
      · simp [Cfg.Halted, Turing.Cfg.Halted, hstate] at hlast
    · simp [Cfg.Halted, Turing.Cfg.Halted, hq'] at hlast

private theorem withEmptyStackHalt_drain_from {Symbol : Type*} {input : List Symbol}
    (M : AuxPDA k Symbol StackSym State) (c : Cfg k Symbol StackSym (Option State) input)
    (hc : c.tapes.state = some none) :
    ∃ q : M.withEmptyStackHalt.RunPath input,
      q.head = c ∧ q.length = c.stack.length + 1 ∧ q.last.Halted ∧
      q.last.stack = [] ∧ q.last.tapes.output = c.tapes.output := by
  generalize hn : c.stack.length = n
  induction n generalizing c with
  | zero =>
    have hnil : c.stack = [] := List.eq_nil_of_length_eq_zero hn
    let act : AuxPDA.Action k Symbol StackSym (Option State) :=
      ⟨{ inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }, .stay⟩
    let c' : Cfg k Symbol StackSym (Option State) input := ⟨act.tape.apply c.tapes, []⟩
    have hstep : M.withEmptyStackHalt.Step c c' := by
      simp only [Step, withEmptyStackHalt, hc]
      refine ⟨act, ⟨by simp [act, Cfg.topSym, hnil], by simp [act, Cfg.topSym, hnil]⟩, ?_⟩
      exact Action.apply?_eq_some_iff.mpr ⟨[], by simp [act, hnil], rfl⟩
    exact ⟨runPathOfStep hstep, rfl, rfl, rfl, rfl,
      show c'.tapes.output = c.tapes.output by simp [c', act]⟩
  | succ n ih =>
    cases hst : c.stack with
    | nil => rw [hst] at hn; simp at hn
    | cons γ rest =>
      rw [hst, List.length_cons, Nat.add_right_cancel_iff] at hn
      let act : AuxPDA.Action k Symbol StackSym (Option State) :=
        ⟨{ inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := some none },
          .pop⟩
      let c₁ : Cfg k Symbol StackSym (Option State) input := ⟨act.tape.apply c.tapes, rest⟩
      have hstep : M.withEmptyStackHalt.Step c c₁ := by
        simp only [Step, withEmptyStackHalt, hc]
        refine ⟨act, ⟨by simp [act, Cfg.topSym, hst], by simp [act, Cfg.topSym, hst]⟩, ?_⟩
        exact Action.apply?_eq_some_iff.mpr ⟨rest, by simp [act, hst], rfl⟩
      obtain ⟨q, hqHead, hqLen, hqHalt, hqStack, hqOut⟩ := ih c₁ rfl hn
      have hstep' : M.withEmptyStackHalt.Step c q.head := hqHead.symm ▸ hstep
      refine ⟨q.cons c hstep', rfl, by simp [hqLen], by simpa using hqHalt,
        by simpa using hqStack, by simpa [c₁, act] using hqOut⟩

private theorem withEmptyStackHalt_lift_running {Symbol : Type*} {input : List Symbol}
    (M : AuxPDA k Symbol StackSym State) (q : RelSeries (M.runningStepRel input)) :
    ∃ r : M.withEmptyStackHalt.RunPath input,
      r.head = liftCfgToDrain q.head ∧ r.last = liftCfgToDrain q.last := by
  induction q using RelSeries.inductionOn' with
  | singleton c => exact ⟨RelSeries.singleton _ (liftCfgToDrain c), rfl, rfl⟩
  | snoc q c hc ih =>
    obtain ⟨r, hrHead, hrLast⟩ := ih
    obtain ⟨hrun, hstep⟩ := hc
    obtain ⟨st, hq⟩ := Option.ne_none_iff_exists'.mp hrun
    simp only [Step, hq] at hstep
    obtain ⟨orig, htr, hact⟩ := hstep
    obtain ⟨stack', hstack, rfl⟩ := Action.apply?_eq_some_iff.mp hact
    let act : AuxPDA.Action k Symbol StackSym (Option State) :=
      ⟨{ inputTape := orig.tape.inputTape
         workTapes := orig.tape.workTapes
         output := orig.tape.output
         state := some orig.tape.state }, orig.stackOp⟩
    have hstep' : M.withEmptyStackHalt.Step (liftCfgToDrain q.last)
        (liftCfgToDrain ⟨orig.tape.apply q.last.tapes, stack'⟩) := by
      simp only [Step, withEmptyStackHalt, liftCfgToDrain, Turing.Cfg.mapState, hq]
      refine ⟨act, ⟨orig, htr, rfl, rfl⟩, Action.apply?_eq_some_iff.mpr ⟨stack', hstack, ?_⟩⟩
      ext <;> simp [act, Turing.Action.apply]
    refine ⟨r.snoc _ (hrLast.symm ▸ hstep'), ?_, by simp⟩
    simpa using hrHead

private theorem visitedByTapeHead_snoc_of_pos_eq {Symbol : Type*} {input : List Symbol}
    {M : AuxPDA k Symbol StackSym State} {r : M.RunPath input}
    {c : Cfg k Symbol StackSym State input} (hc : M.Step r.last c)
    (hwp : c.tapes.workTapePos = r.last.tapes.workTapePos) (i : Fin k) :
    RunPath.visitedByTapeHead (r.snoc c hc) i = RunPath.visitedByTapeHead r i := by
  rw [RunPath.visitedByTapeHead_snoc, hwp, Finset.insert_eq_of_mem]
  rw [RunPath.mem_visitedByTapeHead]
  exact ⟨r.last, r.last_mem, rfl⟩

/-- Project a computation path of `M.withEmptyStackHalt` onto a computation path `q` of `M` that
takes no post-halting steps and visits the exact same work-tape cells. -/
private theorem withEmptyStackHalt_project {Symbol : Type*} {input : List Symbol}
    {M : AuxPDA k Symbol StackSym State} (r : M.withEmptyStackHalt.RunPath input)
    (hr : r.head = M.withEmptyStackHalt.initCfg input) :
    ∃ (q : M.ComputationPath input) (drainSteps : ℕ),
      (∀ i : Fin (q.length + 1), i.val < q.length → ¬(q.toRunPath i).Halted) ∧
      (∀ i, RunPath.visitedByTapeHead q.toRunPath i = RunPath.visitedByTapeHead r i) ∧
      (r.last.tapes.state = none →
        q.last.Halted ∧ q.last.tapes.output = r.last.tapes.output) ∧
      (r.last.tapes.state = some none →
        q.last.Halted ∧ q.last.tapes.output = r.last.tapes.output ∧
        r.last.stack.length + drainSteps = q.last.stack.length ∧
        q.time + drainSteps = r.length) ∧
      (∀ s, r.last.tapes.state = some (some s) →
        projectDrainCfg r.last = q.last ∧ q.time = r.length) := by
  induction r using RelSeries.inductionOn' with
  | singleton c =>
    simp only [RelSeries.head_singleton] at hr
    subst hr
    refine ⟨⟨RelSeries.singleton _ (M.initCfg input), rfl⟩, 0,
      fun _ hi => by simp at hi, fun _ => Finset.image_congr fun _ _ => rfl,
      fun h => by simp [withEmptyStackHalt] at h,
      fun h => by simp [withEmptyStackHalt] at h,
      fun _ hs => ?_⟩
    simp only [RelSeries.last_singleton, initCfg, Cfg.init, Turing.Cfg.init, withEmptyStackHalt,
      Option.some.injEq] at hs
    subst hs
    exact ⟨by ext <;> rfl, rfl⟩
  | snoc r c hc ih =>
    obtain ⟨q, d, hnoPost, hvis, hnone, hdrain, hrun⟩ := ih (by simpa using hr)
    rcases withEmptyStackHalt_step_cases hc with
      ⟨hrNone, rfl⟩ | ⟨hrDrain, _, hwp, _, hout, hcase⟩ | ⟨st, hrRun, hstep, q', hq'⟩
    · exact ⟨q, d, hnoPost,
        fun i => (hvis i).trans (visitedByTapeHead_snoc_of_pos_eq hc rfl i).symm,
        fun _ => by simpa using hnone hrNone,
        fun h => by simp [hrNone] at h,
        fun _ h => by simp [hrNone] at h⟩
    · obtain ⟨hqHalt, hqOut, hstEq, htmEq⟩ := hdrain hrDrain
      have hvis' (i : Fin k) := (hvis i).trans (visitedByTapeHead_snoc_of_pos_eq hc hwp i).symm
      rcases hcase with ⟨_, hcNone, _⟩ | ⟨_, _, hrStack, hcDrain, hcStack⟩
      · exact ⟨q, d, hnoPost, hvis', fun _ => ⟨hqHalt, by simpa [hout] using hqOut⟩,
          fun h => by simp [hcNone] at h,
          fun _ h => by simp [hcNone] at h⟩
      · refine ⟨q, d + 1, hnoPost, hvis', fun h => by simp [hcDrain] at h,
          fun _ => ⟨hqHalt, by simpa [hout] using hqOut, ?_, ?_⟩,
          fun _ h => by simp [hcDrain] at h⟩
        · simp only [RelSeries.last_snoc, hcStack]
          rw [hrStack, List.length_cons] at hstEq
          omega
        · simp only [RelSeries.snoc_length]; omega
    · obtain ⟨hproj, htm⟩ := hrun st hrRun
      have hstep' : M.Step q.last (projectDrainCfg c) := hproj ▸ hstep
      let q'Path : M.ComputationPath input :=
        ⟨q.toRunPath.snoc (projectDrainCfg c) hstep', by simpa using q.head_eq⟩
      have hnoPost' : ∀ i : Fin (q'Path.length + 1), i.val < q'Path.length →
          ¬(q'Path.toRunPath i).Halted := by
        intro i hi
        simp only [q'Path, RelSeries.snoc_length] at hi
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
        · have hi' : i.val < q.length + 1 := by omega
          have he : q'Path.toRunPath i = q.toRunPath ⟨i.val, hi'⟩ :=
            (congrArg (q.toRunPath.snoc (projectDrainCfg c) hstep') (Fin.ext rfl)).trans
              (RelSeries.snoc_castSucc q.toRunPath (projectDrainCfg c) hstep' ⟨i.val, hi'⟩)
          exact he ▸ hnoPost ⟨i.val, hi'⟩ hlt
        · have he : q'Path.toRunPath i = q.last :=
            (congrArg (q.toRunPath.snoc (projectDrainCfg c) hstep') (Fin.ext heq)).trans
              (RelSeries.snoc_castSucc q.toRunPath (projectDrainCfg c) hstep' (Fin.last _))
          rw [he, ← hproj]
          simp [projectDrainCfg, Cfg.Halted, Turing.Cfg.Halted, hrRun]
      have hvis' (i : Fin k) : RunPath.visitedByTapeHead q'Path.toRunPath i =
          RunPath.visitedByTapeHead (r.snoc c hc) i := by
        simp only [q'Path, RunPath.visitedByTapeHead_snoc, hvis i]; rfl
      have htm' : q'Path.time = (r.snoc c hc).length := by
        simp only [q'Path, ComputationPath.time, RunPath.time, RelSeries.snoc_length] at htm ⊢
        omega
      refine ⟨q'Path, 0, hnoPost', hvis', fun h => by simp [hq'] at h,
        fun h => ?_, fun _ _ => ⟨by simp [q'Path], htm'⟩⟩
      simp only [RelSeries.last_snoc, hq', Option.some.injEq] at h
      subst h
      refine ⟨?_, by simp [q'Path, projectDrainCfg], ?_, htm'⟩
      · simp [q'Path, projectDrainCfg, Cfg.Halted, Turing.Cfg.Halted, hq']
      · simp [q'Path, projectDrainCfg]

/-- `withEmptyStackHalt` preserves work-tape space bounds identically. -/
theorem withEmptyStackHalt_runsInSpace {Symbol : Type*} {input : List Symbol} {s : ℕ}
    {M : AuxPDA k Symbol StackSym State} (h : M.RunsInSpace input s) :
    M.withEmptyStackHalt.RunsInSpace input s := by
  intro p
  obtain ⟨q, -, -, hvis, -, -, -⟩ := withEmptyStackHalt_project p.toRunPath p.head_eq
  have hspace : p.space = q.space := by
    simp only [ComputationPath.space, RunPath.space, RunPath.spaceUsedByTape]
    exact Finset.sum_congr rfl fun i _ => congrArg Finset.card (hvis i).symm
  exact hspace ▸ h q

/-- `withEmptyStackHalt` preserves all-branches time bounds with at most `2 * t + 1` steps. -/
theorem withEmptyStackHalt_runsInTime {Symbol : Type*} {input : List Symbol} {t : ℕ}
    {M : AuxPDA k Symbol StackSym State} (h : M.RunsInTime input t) :
    M.withEmptyStackHalt.RunsInTime input (2 * t + 1) := by
  intro p hp
  obtain ⟨q, d, hnoPost, -, -, hdrain, hrun⟩ := withEmptyStackHalt_project p.toRunPath p.head_eq
  have hqTime : q.time ≤ t := by
    by_contra hgt
    push Not at hgt
    have htlt : t < q.length + 1 := by simp only [ComputationPath.time, RunPath.time] at hgt; omega
    let qt : M.ComputationPath input :=
      ⟨q.toRunPath.take ⟨t, htlt⟩, by rw [RelSeries.head_take]; exact q.head_eq⟩
    exact hnoPost ⟨t, htlt⟩ hgt
      ((RelSeries.last_take _ _) ▸ h qt (by simp [qt, ComputationPath.time, RunPath.time]))
  rcases hs : p.last.tapes.state with _ | (_ | st)
  · exact hs
  · obtain ⟨-, -, hstEq, htmEq⟩ := hdrain hs
    have hstack := q.stackHeight_le
    simp only [ComputationPath.time, RunPath.time] at hp hqTime hstack htmEq; omega
  · obtain ⟨_, htm⟩ := hrun st hs
    simp only [ComputationPath.time, RunPath.time] at hp hqTime htm; omega

/-- `withEmptyStackHalt` preserves acceptance exactly. -/
theorem withEmptyStackHalt_accepts_iff {M : AuxPDA k Bool StackSym State} :
    M.withEmptyStackHalt.Accepts input ↔ M.Accepts input := by
  constructor
  · rintro ⟨p, hhalt, hout⟩
    obtain ⟨q, -, -, -, hnone, -, -⟩ := withEmptyStackHalt_project p.toRunPath p.head_eq
    exact ⟨q, (hnone hhalt).1, (hnone hhalt).2.trans hout⟩
  · rintro ⟨p, hhalt, hout⟩
    obtain ⟨qrun, hhead, hlast, -, -⟩ := RunPath.exists_running p.toRunPath hhalt
    obtain ⟨r, hrHead, hrLast⟩ := withEmptyStackHalt_lift_running M qrun
    have hrDrainState : r.last.tapes.state = some none := by
      simp only [hrLast, hlast, liftCfgToDrain, Turing.Cfg.mapState_state, hhalt]
    obtain ⟨qdrain, hdHead, -, hdHalt, -, hdOut⟩ :=
      withEmptyStackHalt_drain_from M r.last hrDrainState
    let full : M.withEmptyStackHalt.RunPath input := r.smash qdrain hdHead.symm
    refine ⟨⟨full, by rw [RelSeries.head_smash, hrHead, hhead, p.head_eq]; rfl⟩,
      by simpa [full] using hdHalt, ?_⟩
    rw [show full.last = qdrain.last from RelSeries.last_smash hdHead.symm, hdOut, hrLast, hlast]
    exact hout

/-! ### Finiteness and polynomial cardinality of surface configurations -/

/-- Upper bound on the number of surface configurations of a `k`-tape binary `AuxPDA` on an input
of length `n` whose work-tape storage fits in per-tape windows of total size `s`. -/
def surfaceCfgBound (StackSym State : Type*) [Fintype StackSym] [Fintype State]
    (k n s : ℕ) : ℕ :=
  (n + 2) * (Fintype.card StackSym + 1) * 3 * Turing.storageBound Bool State k s

/-- Surface configurations whose storage fits in per-tape windows `w` with `∑ i, w i ≤ s` have
cardinality at most `surfaceCfgBound StackSym State k input.length s`. -/
theorem encard_surfaceCfg_fitsIn_le [Fintype StackSym] [Fintype State]
    {w : Fin k → ℕ} {s : ℕ} (hsum : ∑ i, w i ≤ s) :
    {sc : SurfaceCfg k StackSym State input | sc.storage.FitsIn w}.encard ≤
      surfaceCfgBound StackSym State k input.length s := by
  let f : SurfaceCfg k StackSym State input →
      (Fin (input.length + 2) × Option StackSym × OutputSummary) × Turing.Storage Bool State k :=
    fun sc => ((sc.inputPos, sc.topSym, sc.outputSummary), sc.storage)
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk.injEq] at hab
    obtain ⟨⟨hpos, htop, hout⟩, hstor⟩ := hab
    exact SurfaceCfg.ext hpos hstor htop hout
  calc {sc : SurfaceCfg k StackSym State input | sc.storage.FitsIn w}.encard
      = (f '' {sc | sc.storage.FitsIn w}).encard := (hinj.injOn.encard_image).symm
    _ ≤ ((Set.univ : Set (Fin (input.length + 2) × Option StackSym × OutputSummary)) ×ˢ
          {x : Turing.Storage Bool State k | x.FitsIn w}).encard := by
        apply Set.encard_le_encard
        rintro _ ⟨sc, hsc, rfl⟩
        exact ⟨Set.mem_univ _, hsc⟩
    _ = (Set.univ : Set (Fin (input.length + 2) × Option StackSym × OutputSummary)).encard *
          {x : Turing.Storage Bool State k | x.FitsIn w}.encard := Set.encard_prod
    _ ≤ ((input.length + 2) * (Fintype.card StackSym + 1) * 3 : ℕ) *
          Turing.storageBound Bool State k s := by
        refine mul_le_mul' ?_ (Turing.encard_fitsIn_le hsum)
        simp [Set.encard_univ, ENat.card_eq_coe_fintype_card, mul_assoc]
    _ = surfaceCfgBound StackSym State k input.length s := by
        simp [surfaceCfgBound, Nat.cast_mul]

/-- Under work-tape space bound `s`, at most `surfaceCfgBound StackSym State k n (k * s)` surface
configurations are reachable from the initial configuration (regardless of stack height). -/
theorem encard_reachable_surfaceCfg_le [Fintype StackSym] [Fintype State]
    {M : AuxPDA k Bool StackSym State} {s : ℕ} (hs : M.RunsInSpace input s) :
    (Set.range fun p : M.ComputationPath input => p.last.surface).encard ≤
      surfaceCfgBound StackSym State k input.length (k * s) := by
  refine (Set.encard_le_encard ?_).trans (encard_surfaceCfg_fitsIn_le (w := fun _ => s) (by simp))
  rintro _ ⟨p, rfl⟩
  have hle : ∀ i, p.spaceUsedByTape i ≤ s := fun i =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (p.spaceUsedByTape j)) (Finset.mem_univ i)).trans
      (hs p)
  exact Turing.Storage.FitsIn_mono hle p.storage_fitsIn

/-- Exponential form: the number of reachable surface configurations under work space `s` is at
most `(n + 2) * a * 2 ^ (c * s)` with constants `a, c` depending only on `k`, `StackSym`, and
`State`. -/
theorem encard_reachable_surfaceCfg_le_pow [Finite StackSym] [Finite State]
    (M : AuxPDA k Bool StackSym State) :
    ∃ a c : ℕ, ∀ (input : List Bool) (s : ℕ), M.RunsInSpace input s →
      (Set.range fun p : M.ComputationPath input => p.last.surface).encard ≤
        (input.length + 2) * a * 2 ^ (c * s) := by
  have : Fintype StackSym := Fintype.ofFinite StackSym
  have : Fintype State := Fintype.ofFinite State
  obtain ⟨a₀, c₀, hpow⟩ := Turing.storageBound_le_pow (Symbol := Bool) (State := State) (k := k)
  refine ⟨(Fintype.card StackSym + 1) * 3 * a₀, c₀ * k, fun input s hs => ?_⟩
  refine (encard_reachable_surfaceCfg_le hs).trans ?_
  have hle : surfaceCfgBound StackSym State k input.length (k * s) ≤
      (input.length + 2) * ((Fintype.card StackSym + 1) * 3 * a₀) * 2 ^ (c₀ * k * s) := by
    calc surfaceCfgBound StackSym State k input.length (k * s)
        = (input.length + 2) * (Fintype.card StackSym + 1) * 3 *
            Turing.storageBound Bool State k (k * s) := rfl
      _ ≤ (input.length + 2) * (Fintype.card StackSym + 1) * 3 * (a₀ * 2 ^ (c₀ * (k * s))) := by
            gcongr; exact hpow (k * s)
      _ = (input.length + 2) * ((Fintype.card StackSym + 1) * 3 * a₀) * 2 ^ (c₀ * k * s) := by
            ring
  exact_mod_cast hle

/-- **Polynomial surface-configuration bound in logarithmic space**: for `s(n) = c * (log₂ n + 1)`,
the surface-configuration bound `surfaceCfgBound StackSym State k n (k * s n)` is polynomially
bounded in `n`. -/
theorem surfaceCfgBound_log_polynomiallyBounded [Fintype StackSym] [Fintype State]
    (k c : ℕ) :
    Cslib.PolynomiallyBounded fun n =>
      surfaceCfgBound StackSym State k n (k * (c * (Nat.log2 n + 1))) := by
  obtain ⟨a₀, c₀, hpow⟩ := Turing.storageBound_le_pow (Symbol := Bool) (State := State) (k := k)
  set D := c₀ * k * c
  set A := 2 * (Fintype.card StackSym + 1) * 3 * a₀ * 2 ^ D
  refine Cslib.PolynomiallyBounded.of_forall_le A (D + 1) fun n => ?_
  have h2 : 2 ^ (D * (Nat.log2 n + 1)) ≤ (2 * (n + 1)) ^ D := by
    rw [mul_comm D, pow_mul]
    exact Nat.pow_le_pow_left (Nat.two_pow_log2_succ_le n) D
  have hn2 : n + 2 ≤ 2 * (n + 1) := by omega
  calc surfaceCfgBound StackSym State k n (k * (c * (Nat.log2 n + 1)))
      = (n + 2) * (Fintype.card StackSym + 1) * 3 *
          Turing.storageBound Bool State k (k * (c * (Nat.log2 n + 1))) := rfl
    _ ≤ (n + 2) * (Fintype.card StackSym + 1) * 3 *
          (a₀ * 2 ^ (c₀ * (k * (c * (Nat.log2 n + 1))))) := by
        gcongr; exact hpow _
    _ = (n + 2) * ((Fintype.card StackSym + 1) * 3 * a₀) * 2 ^ (D * (Nat.log2 n + 1)) := by
        simp only [D]; ring
    _ ≤ (2 * (n + 1)) * ((Fintype.card StackSym + 1) * 3 * a₀) * (2 * (n + 1)) ^ D := by
        gcongr
    _ = A * (n + 1) ^ (D + 1) := by
        simp only [A, mul_pow, pow_succ]
        ring

end Turing.AuxPDA
