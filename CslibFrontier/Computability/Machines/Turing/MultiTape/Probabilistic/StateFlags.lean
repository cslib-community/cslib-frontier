/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.AcceptCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput

/-!
# Replaying the state of a fair-coin table

The replay of a closed fair-coin table (`Turing.MultiTapePTM.runClosedCoins`) returns its output,
not the state it reaches. The flag table of a table (`Turing.MultiTapePTM.flag`) takes the same
steps, but at each step emits a flag `φ` of the state it enters instead of the table's output. So
the last symbol of its replay is the flag of the state that the table reaches
(`Turing.MultiTapePTM.getLastD_runClosedCoins_flag`), for instance whether the table has halted.
Over the binary alphabet this flag is computable within space linear in the coins and the input
(`Turing.MultiTapeTM.ComputableInSpace.lastFlag`).

## Main definitions

* `Turing.MultiTapePTM.flag`: the table that emits the flag of each state it enters.

## Main results

* `Turing.MultiTapePTM.getLastD_runClosedCoins_flag`: the last symbol of the replay of the flag
  table is the flag of the state reached.
* `Turing.MultiTapeTM.ComputableInSpace.lastFlag`: this flag is computable within linear space.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeMachine

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- The **flag table** of `machine`: the steps of `machine`, emitting the flag `φ` of the state
entered at each step instead of the output of `machine`. -/
def flag (machine : MultiTapePTM k Symbol State) (φ : Option State → Symbol) :
    MultiTapePTM k Symbol State where
  initial := machine.initial
  tr s symbol work answer bit :=
    let a := Action.emptyOracleEquiv (machine.tr s symbol work answer bit)
    Action.emptyOracleEquiv.symm ⟨a.inputTape, a.workTapes, some (φ a.state), a.state⟩

variable (machine : MultiTapePTM k Symbol State) (φ : Option State → Symbol)

/-- A step of the flag table from a configuration whose output ends with the flag of its state
leads to a configuration of the same kind, with the same tapes as the step of `machine`. -/
private theorem step_flag (bit : Bool) (c : Cfg k Symbol State input) (w : List Symbol)
    (hw : w.getLastD (φ (some machine.initial)) = φ c.state) :
    ∃ w', w'.getLastD (φ (some machine.initial)) = φ ((machine.withCoin bit).toTM.step c).state ∧
      ((machine.flag φ).withCoin bit).toTM.step { c with output := w } =
        { (machine.withCoin bit).toTM.step c with output := w' } := by
  rcases Option.eq_none_or_eq_some c.state with hs | ⟨q, hs⟩
  · refine ⟨w, ?_, ?_⟩
    · rw [MultiTapeTM.step_of_halt hs, hw]
    · rw [MultiTapeTM.step_of_halt (cfg := { c with output := w }) hs,
        MultiTapeTM.step_of_halt hs]
  · let a := Action.emptyOracleEquiv (machine.tr q c.inputSymbol c.workTapeSymbols Empty.elim bit)
    have h₁ : (machine.withCoin bit).toTM.step c = a.apply c := by
      rw [MultiTapeTM.step_of_state hs, MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
      rfl
    have h₂ : ((machine.flag φ).withCoin bit).toTM.step { c with output := w } =
        (⟨a.inputTape, a.workTapes, some (φ a.state), a.state⟩ : Turing.Action k Symbol State).apply
          { c with output := w } := by
      rw [MultiTapeTM.step_of_state (cfg := { c with output := w }) hs, MultiTapeMachine.toTM,
        MultiTapeTM.tr_ofTr]
      rfl
    refine ⟨w ++ [φ a.state], ?_, ?_⟩
    · rw [h₁, List.getLastD_concat]
      rfl
    · rw [h₁, h₂]
      rfl

/-- Replaying coins on the flag table, from a configuration whose output ends with the flag of its
state, keeps the tapes of `machine` and ends with the flag of the state reached. -/
private theorem stepCoins_flag (coins : List Bool) (c : Cfg k Symbol State input) (w : List Symbol)
    (hw : w.getLastD (φ (some machine.initial)) = φ c.state) :
    ∃ w', w'.getLastD (φ (some machine.initial)) = φ (machine.stepCoins coins c).state ∧
      (machine.flag φ).stepCoins coins { c with output := w } =
        { machine.stepCoins coins c with output := w' } := by
  induction coins generalizing c w with
  | nil => exact ⟨w, hw, rfl⟩
  | cons bit coins ih =>
    obtain ⟨w₁, hw₁, h₁⟩ := machine.step_flag φ bit c w hw
    obtain ⟨w₂, hw₂, h₂⟩ := ih _ w₁ hw₁
    refine ⟨w₂, hw₂, ?_⟩
    rw [stepCoins_cons, h₁, h₂, stepCoins_cons]

/-- **The last flag of the replay is the flag of the state reached**: the last symbol of the replay
of the flag table, `φ` of the initial state when it is empty, is `φ` of the state that `machine`
reaches. -/
theorem getLastD_runClosedCoins_flag (machine : MultiTapePTM k Bool State)
    (φ : Option State → Bool) (coins : List Bool) (input : List Bool) :
    ((machine.flag φ).runClosedCoins coins input).getLastD (φ (some machine.initial)) =
      φ (machine.stepCoins coins (Cfg.init machine.initial input)).state := by
  obtain ⟨w, hw, h⟩ := machine.stepCoins_flag φ coins (Cfg.init machine.initial input) [] rfl
  rw [runClosedCoins_eq_output_stepCoins]
  change ((machine.flag φ).stepCoins coins
    { Cfg.init machine.initial input with output := [] }).output.getLastD _ = _
  rw [h]
  exact hw

end Turing.MultiTapePTM

namespace Turing.MultiTapeTM.ComputableInSpace

variable {k : ℕ} {State : Type} [Finite State]

/-- **The flag of the state reached is computable within linear space**: replaying the flag table
and reading its last bit. -/
theorem lastFlag (machine : MultiTapePTM k Bool State) (φ : Option State → Bool) :
    ComputableInSpace
      (fun p : List Bool × List Bool =>
        φ (machine.stepCoins p.1 (Cfg.init machine.initial p.2)).state)
      (encPair encBits encBits) encBool fun p => (encPair encBits encBits p).length := by
  have hrun := of_inO (MultiTapePTM.computableInDegree_runClosedCoins (machine.flag φ)).inO_one
  have hrev := budget_comp_linear bitsReverse hrun
  have hbits : ComputableInSpace (fun l : List Bool => l) encBits (encList encBool)
      fun l => (encBits l).length :=
    of_inO ComputableInDegree.bitsToList.inO_one
  refine (budget_headD (φ (some machine.initial)) (budget_comp_linear hbits hrev)).of_enc_eq
    fun p => congrArg encBool ?_
  rw [← MultiTapePTM.getLastD_runClosedCoins_flag machine φ]
  simp

end Turing.MultiTapeTM.ComputableInSpace
