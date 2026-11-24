/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.Classes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.InPlace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Space

/-!
# Simulating an oracle machine with universal steps

A deterministic oracle machine `M` with finitely many states is simulated, step by step, on the
configurations `Turing.MultiTapeTM.Universal.SCfg` of Complexitylib's universal machine together
with the content of the query tape. Every ordinary step of `M` is a step
`Turing.MultiTapeTM.Universal.stepWith` of the description of the CSLib machine
`OracleTM.plainTM M` of its ordinary actions; the symbols that `M` writes on its query and output
tapes, whether it queries, and its answer states are read off steps of the descriptions of auxiliary
machines that differ from `M` only in these symbols (`OracleTM.outTM`, `OracleTM.answerTM`). The
oracle `A` answers the queries (`OracleTM.simNext`).

## Main definitions

* `Cslib.Complexity.NtimeDspace.Oracle.OracleTM.simNext`, `.simEmit`: the step of the simulation and
the symbol it
  writes on the output tape.
* `Cslib.Complexity.NtimeDspace.Oracle.OracleTM.Rel`: a simulation state represents a configuration
of `M`.

## Main results

* `Cslib.Complexity.NtimeDspace.Oracle.stepWith_desc`: one universal step of the description of a
CSLib machine.
* `Cslib.Complexity.NtimeDspace.Oracle.OracleTM.rel_simNext`: the simulation follows `M`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-! ### One universal step of a description -/

section DescStep

variable {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)

/-- **One universal step of a description.** If the simulation state `s` represents the
configuration `c` of `tm`, the universal step of the description of `tm`, reading the input symbol
under the simulated input head, represents the step of `tm`, and emits its output symbol. -/
theorem stepWith_desc (tm : MultiTapeTM k Bool State) {x : List Bool} {s : SCfg}
    {c : Cfg k Bool State x} (hs : s.WellShaped k (x.map eBit))
    (hc : s.toCfg k (x.map eBit) (c.output.map eBit) = c.map eS eBit) :
    (stepWith (desc eS eBit tm) s (inputSymbol (x.map eBit) s.inputPos)).1.WellShaped k
        (x.map eBit) ∧
      (stepWith (desc eS eBit tm) s (inputSymbol (x.map eBit) s.inputPos)).1.toCfg k (x.map eBit)
        ((tm.step c).output.map eBit) = (tm.step c).map eS eBit ∧
      (tm.step c).output.map eBit = c.output.map eBit ++
        (stepWith (desc eS eBit tm) s (inputSymbol (x.map eBit) s.inputPos)).2.toList := by
  rw [← step_eq_stepWith]
  have h := toCfg_step (tm := tm.map eS eBit) (d := desc eS eBit tm) (out := c.output.map eBit) hs
    (fun q hq => by
      rw [hc] at hq ⊢
      obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hq
      rw [Cfg.inputSymbol_map]
      exact holds_desc eS eBit tm q _ c.workTapeSymbols)
  rw [hc, step_map] at h
  have hout : (tm.step c).output.map eBit = c.output.map eBit ++
      (step (desc eS eBit tm) (x.map eBit) s).2.toList := by
    have := congrArg Cfg.output h.1
    simpa [SCfg.toCfg] using this.symm
  refine ⟨h.2, ?_, hout⟩
  rw [hout]
  exact h.1

/-- The universal step reads the input symbol at the head of the simulation. -/
lemma inputSymbol_map_eBit (x : List Bool) (p : ℕ) :
    inputSymbol (x.map eBit) p = if p = 0 then none else (x[p - 1]?).map eBit := by
  unfold inputSymbol
  split_ifs with h
  · rfl
  · rw [← List.map_drop, List.head?_map, List.head?_drop]

end DescStep

/-! ### Auxiliary machines -/

namespace OracleTM

variable {k : ℕ} {State : Type} (M : OracleTM k State)

/-- Whether an instruction is a query. -/
def isAsk : OAction k State → Bool
  | .ask _ _ => true
  | .step _ _ => false

/-- A machine that halts at once, emitting `g` of the instruction of `M`. -/
noncomputable def outTM (g : OAction k State → Option Bool) : MultiTapeTM k Bool State :=
  MultiTapeTM.ofTr M.q₀ fun q i w => ⟨0, fun _ => (none, 0), g (M.tr q i w), none⟩

/-- The instruction answering a query of `M` positively (`yes`) or negatively. -/
def answerAct (yes : Bool) : OAction k State → Turing.Action k Bool State
  | .ask y n => ⟨0, fun _ => (none, 0), none, some (if yes then y else n)⟩
  | .step a _ => a

/-- The machine moving from a query state of `M` to its answer state. -/
noncomputable def answerTM (yes : Bool) : MultiTapeTM k Bool State :=
  MultiTapeTM.ofTr M.q₀ fun q i w => answerAct yes (M.tr q i w)

/-- `some true` exactly at queries. -/
def flagSym : OAction k State → Option Bool
  | .ask _ _ => some true
  | .step _ _ => none

/-- `some true` exactly when an ordinary instruction writes `b` on the query tape. -/
def querySym (b : Bool) : OAction k State → Option Bool
  | .step _ (some b') => if b' = b then some true else none
  | _ => none

/-- `some true` exactly when an ordinary instruction writes `b` on the output tape. -/
def outSym (b : Bool) : OAction k State → Option Bool
  | .step a _ => if a.output = some b then some true else none
  | _ => none

/-! ### The step of the simulation -/

variable [Fintype State] (eS : State ↪ ℕ) (A : Set (List Bool))

/-- The input symbol of a step: blank at the left boundary, the bit read otherwise. -/
def symOf (s : SCfg) (r : Option Bool) : Option ℕ := if s.inputPos = 0 then none else r.map eBit

/-- The symbol written by a step: `[true]`, `[false]` or nothing, read off two flags. -/
def bitOf (t f : Bool) : List Bool := if t then [true] else if f then [false] else []

open scoped Classical in
/-- **The step of the simulation**: at a query (read off `outTM flagSym`), the oracle answers and
the answer machine moves to the answer state; the query tape is erased. Otherwise the ordinary step
of `M` (`plainTM`) is taken and the symbol written on the query tape is appended. -/
noncomputable def simNext (p : (SCfg × List Bool) × Option Bool) : SCfg × List Bool :=
  if (stepWith (desc eS eBit (M.outTM flagSym)) p.1.1 (symOf p.1.1 p.2)).2.isSome then
    (if p.1.2 ∈ A then (stepWith (desc eS eBit (M.answerTM true)) p.1.1 (symOf p.1.1 p.2)).1
      else (stepWith (desc eS eBit (M.answerTM false)) p.1.1 (symOf p.1.1 p.2)).1, [])
  else ((stepWith (desc eS eBit M.plainTM) p.1.1 (symOf p.1.1 p.2)).1,
    p.1.2 ++ bitOf
      (stepWith (desc eS eBit (M.outTM (querySym true))) p.1.1 (symOf p.1.1 p.2)).2.isSome
      (stepWith (desc eS eBit (M.outTM (querySym false))) p.1.1 (symOf p.1.1 p.2)).2.isSome)

/-- The symbol that the step of the simulation writes on the output tape. -/
noncomputable def simEmit (p : (SCfg × List Bool) × Option Bool) : List Bool :=
  if (stepWith (desc eS eBit (M.outTM flagSym)) p.1.1 (symOf p.1.1 p.2)).2.isSome then []
  else bitOf
    (stepWith (desc eS eBit (M.outTM (outSym true))) p.1.1 (symOf p.1.1 p.2)).2.isSome
    (stepWith (desc eS eBit (M.outTM (outSym false))) p.1.1 (symOf p.1.1 p.2)).2.isSome

/-- The simulation state `p` represents the configuration `c` of `M` on `x`: the universal
configuration represents its tapes, and the query tapes agree. -/
def Rel {x : List Bool} (p : SCfg × List Bool) (c : OCfg k State x) : Prop :=
  p.1.WellShaped k (x.map eBit) ∧
    p.1.toCfg k (x.map eBit) (c.tapes.output.map eBit) = c.tapes.map eS eBit ∧ p.2 = c.query

variable {M eS A}

omit [Fintype State] in
lemma Rel.state {x : List Bool} {p : SCfg × List Bool} {c : OCfg k State x} (h : Rel eS p c) :
    p.1.state = c.tapes.state.map eS := by
  have := congrArg Cfg.state h.2.1
  simpa [SCfg.toCfg] using this

omit [Fintype State] in
lemma Rel.inputPos {x : List Bool} {p : SCfg × List Bool} {c : OCfg k State x}
    (h : Rel eS p c) : p.1.inputPos = c.tapes.inputPos.val := by
  have h1 := congrArg (fun c => (Cfg.inputPos c).val) h.2.1
  have h2 := h.1.inputPos_le
  simp only [SCfg.toCfg, Cfg.map_inputPos, Fin.val_cast, List.length_map] at h1 h2
  omega

omit [Fintype State] in
lemma symOf_of_rel {x : List Bool} {p : SCfg × List Bool} {c : OCfg k State x}
    (_h : Rel eS p c) : symOf p.1 (x[p.1.inputPos - 1]?) = inputSymbol (x.map eBit)
        p.1.inputPos := by
  rw [symOf, inputSymbol_map_eBit]

/-- The universal step of `tm` from a represented running configuration. -/
lemma step_of_rel (tm : MultiTapeTM k Bool State) {x : List Bool} {p : SCfg × List Bool}
    {c : OCfg k State x} (h : Rel eS p c) {q : State} (hq : c.tapes.state = some q) :
    (stepWith (desc eS eBit tm) p.1 (symOf p.1 (x[p.1.inputPos - 1]?))).1.WellShaped k
        (x.map eBit) ∧
      (stepWith (desc eS eBit tm) p.1 (symOf p.1 (x[p.1.inputPos - 1]?))).1.toCfg k (x.map eBit)
        ((tm.step c.tapes).output.map eBit) = (tm.step c.tapes).map eS eBit ∧
      (stepWith (desc eS eBit tm) p.1 (symOf p.1 (x[p.1.inputPos - 1]?))).2 =
        (tm.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols).output.map eBit := by
  rw [symOf_of_rel h]
  obtain ⟨h1, h2, h3⟩ := stepWith_desc eS tm h.1 h.2.1
  refine ⟨h1, h2, ?_⟩
  rw [MultiTapeTM.step_of_state hq, Action.apply_output, List.map_append] at h3
  have := List.append_cancel_left h3
  cases ho : (tm.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols).output <;>
    cases hs : (stepWith (desc eS eBit tm) p.1 (inputSymbol (x.map eBit) p.1.inputPos)).2 <;>
    simp_all

omit [Fintype State] in
lemma outTM_tr (g : OAction k State → Option Bool) (q : State) (i : Option Bool)
    (w : Fin k → Option Bool) : ((M.outTM g).tr q i w).output = g (M.tr q i w) := by
  simp [outTM]

/-- **The simulation follows `M`.** -/
theorem rel_simNext {x : List Bool} {p : SCfg × List Bool} {c : OCfg k State x}
    (h : Rel eS p c) {q : State} (hq : c.tapes.state = some q) :
    Rel eS (M.simNext eS A (p, x[p.1.inputPos - 1]?)) (M.step A c) ∧
      M.simEmit eS (p, x[p.1.inputPos - 1]?) ++ [] =
        ((M.step A c).tapes.output.drop c.tapes.output.length) := by
  have hflag := (step_of_rel (M.outTM flagSym) h hq).2.2
  rw [outTM_tr] at hflag
  have hst := M.step_of_state A hq
  cases hM : M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols with
  | ask y n =>
    have hf : (stepWith (desc eS eBit (M.outTM flagSym)) p.1
        (symOf p.1 (x[p.1.inputPos - 1]?))).2.isSome = true := by
      rw [hflag, hM]; rfl
    rw [hM] at hst
    simp only [simNext, simEmit, hf, ite_true]
    refine ⟨?_, ?_⟩
    · have hans : ∀ yes, (M.answerTM yes).step c.tapes =
          c.tapes.withState (some (if yes then y else n)) := by
        intro yes
        rw [MultiTapeTM.step_of_state hq]
        simp only [answerTM, MultiTapeTM.tr_ofTr, hM, answerAct]
        exact Cfg.ext rfl (by simp) (funext fun j => rfl) (funext fun j => by simp) (by simp)
      have key : ∀ yes, Rel eS ((stepWith (desc eS eBit (M.answerTM yes)) p.1
          (symOf p.1 (x[p.1.inputPos - 1]?))).1, []) ⟨c.tapes.withState
            (some (if yes then y else n)), []⟩ := by
        intro yes
        obtain ⟨h1, h2, -⟩ := step_of_rel (M.answerTM yes) h hq
        rw [hans yes] at h2
        exact ⟨h1, by simpa using h2, rfl⟩
      rw [hst, OAction.apply_ask, ← h.2.2]
      split_ifs with hA
      · exact key true
      · exact key false
    · rw [hst, OAction.apply_ask]
      simp
  | step a o =>
    have hf : (stepWith (desc eS eBit (M.outTM flagSym)) p.1
        (symOf p.1 (x[p.1.inputPos - 1]?))).2.isSome = false := by
      rw [hflag, hM]; rfl
    rw [hM] at hst
    simp only [simNext, simEmit, hf, Bool.false_eq_true, ite_false]
    have hplain : M.plainTM.step c.tapes = a.apply c.tapes := by
      rw [MultiTapeTM.step_of_state hq]
      simp [plainTM, hM, OAction.action]
    have hq1 := (step_of_rel (M.outTM (querySym true)) h hq).2.2
    have hq0 := (step_of_rel (M.outTM (querySym false)) h hq).2.2
    have ho1 := (step_of_rel (M.outTM (outSym true)) h hq).2.2
    have ho0 := (step_of_rel (M.outTM (outSym false)) h hq).2.2
    rw [outTM_tr, hM] at hq1 hq0 ho1 ho0
    obtain ⟨h1, h2, -⟩ := step_of_rel M.plainTM h hq
    rw [hplain] at h2
    refine ⟨⟨h1, ?_, ?_⟩, ?_⟩
    · rw [hst]; exact h2
    · rw [hst, OAction.apply_step, hq1, hq0, h.2.2]
      rcases o with _ | _ | _ <;> rfl
    · rw [ho1, ho0, hst, OAction.apply_step, Action.apply_output, List.drop_left]
      rcases ha : a.output with _ | _ | _ <;> simp [outSym, bitOf, ha]

end OracleTM

end Cslib.Complexity.NtimeDspace.Oracle
