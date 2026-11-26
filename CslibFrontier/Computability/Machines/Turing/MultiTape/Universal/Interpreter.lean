/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.DescriptionSize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# An encoded deterministic universal interpreter

This module selects the deterministic finite-state machine constructed by
`Turing.MultiTapeTM.Universal.computableInO_universal` through the retained machine normal form,
numbers its states, and exposes its complete `Turing.MultiTapeTM.Universal.Desc`. Running that
description realizes the existing
`Turing.MultiTapeTM.Universal.universal` function on its binary-clock encoding.

The selected native construction still comes from an existential computability theorem. Its tape
count, state count and common time/space factor are therefore exposed as named constants rather
than claimed to be concrete numerals. `encodedUniversalInterpreterSizeBound` is an arithmetic
transition-table bound in those constants. Static interpreter bits are never added silently to a
run clock.

## Main definitions

* `Turing.MultiTapeTM.Universal.encodedUniversalInterpreter`: one encoded deterministic
  interpreter.
* `Turing.MultiTapeTM.Universal.encodedUniversalInterpreterSizeBound`: its construction-derived
  transition-table bound.
* `Turing.MultiTapeTM.Universal.encodedUniversalInterpreterTime`,
  `Turing.MultiTapeTM.Universal.encodedUniversalInterpreterSpace`: the native certificate bounds,
  including its named common factor.

## Main results

* `Turing.MultiTapeTM.Universal.descLen_encodedUniversalInterpreter_le`: the static interpreter
  description satisfies its arithmetic bound.
* `Turing.MultiTapeTM.Universal.simSpace_encodedUniversalInterpreter_le`: every observed run
  prefix respects the actual workspace bound.
* `Turing.MultiTapeTM.Universal.universal_encodedUniversalInterpreter`: the description realizes
  the encoded output of `universal` at every clock at least its certified native runtime.
-/

public section

namespace Turing.MultiTapeTM.Universal

private structure NativeInterpreter where
  factor : ℕ
  tapes : ℕ
  State : Type
  stateFinite : Finite State
  machine : MultiTapeTM tapes Bool State
  computes : ComputesFunTidilyInTimeAndSpace machine eIn eOut universal
    (fun i => factor * (universalImplementationTime i + 1))
    (fun i => factor * (universalImplementationSpace i + 1))

private theorem nativeInterpreter_nonempty : Nonempty NativeInterpreter := by
  obtain ⟨factor, ⟨tapes, State, stateFinite, machine, computes⟩, -⟩ :=
    Internal.NormalForm.inO computableInO_universal
  exact ⟨⟨factor, tapes, State, stateFinite, machine, fun i => by
    simpa only [universalImplementationTime, universalImplementationSpace] using computes i⟩⟩

private noncomputable def nativeInterpreter : NativeInterpreter :=
  Classical.choice nativeInterpreter_nonempty

private noncomputable instance : Finite nativeInterpreter.State :=
  nativeInterpreter.stateFinite

private noncomputable instance : Fintype nativeInterpreter.State :=
  Fintype.ofFinite nativeInterpreter.State

private noncomputable def nativeInterpreterStateEncoding : nativeInterpreter.State ↪ ℕ :=
  (Fintype.equivFin nativeInterpreter.State).toEmbedding.trans Fin.valEmbedding

/-- The common constant factor in the selected native interpreter's time and workspace
certificate. It is first-class because the existing construction proves existence but does not
reduce this factor to a numeral. -/
noncomputable def encodedUniversalInterpreterFactor : ℕ := nativeInterpreter.factor

/-- The selected construction factor is positive. A zero factor could not emit even the final
Boolean field of `eOut`. -/
theorem encodedUniversalInterpreterFactor_pos : 0 < encodedUniversalInterpreterFactor := by
  let i : Desc × List ℕ × ℕ := (⟨0, 0, []⟩, [], 0)
  have hlen := (nativeInterpreter.computes i).length_output_le
  have hout : 0 < (eOut (universal i)).length := by
    simp only [eOut, length_encPair, encBool_apply, List.length_singleton]; omega
  change 0 < nativeInterpreter.factor
  by_contra hfactor
  simp only [Nat.eq_zero_of_not_pos hfactor, Nat.zero_mul] at hlen; omega

/-- The number of work tapes in the selected native interpreter. -/
noncomputable def encodedUniversalInterpreterTapes : ℕ := nativeInterpreter.tapes

/-- The number of finite-control states in the selected native interpreter. -/
noncomputable def encodedUniversalInterpreterStates : ℕ :=
  Fintype.card nativeInterpreter.State

/-- One complete encoded deterministic finite-control machine realizing `universal` on `eIn`.
The input to this description is the bit word `eIn i`, renamed through `eBit`. -/
noncomputable def encodedUniversalInterpreter : Desc :=
  desc nativeInterpreterStateEncoding eBit nativeInterpreter.machine

/-- A construction-derived arithmetic bound on the static `eDesc` bits of
`encodedUniversalInterpreter`. The exposed tape and state constants remain separate from online
resources. -/
@[expose] noncomputable def encodedUniversalInterpreterSizeBound : ℕ :=
  descSizeBound encodedUniversalInterpreterTapes encodedUniversalInterpreterStates

/-- The certified native running clock of the selected interpreter on the binary-clock request
`eIn i`. -/
@[expose] noncomputable def encodedUniversalInterpreterTime (i : Desc × List ℕ × ℕ) : ℕ :=
  encodedUniversalInterpreterFactor * (universalImplementationTime i + 1)

/-- The certified native workspace of the selected interpreter on the binary-clock request
`eIn i`. -/
@[expose] noncomputable def encodedUniversalInterpreterSpace (i : Desc × List ℕ × ℕ) : ℕ :=
  encodedUniversalInterpreterFactor * (universalImplementationSpace i + 1)

/-- The selected interpreter's complete static description satisfies the explicit table-size
formula in its named tape and state counts. -/
theorem descLen_encodedUniversalInterpreter_le :
    descLen encodedUniversalInterpreter ≤ encodedUniversalInterpreterSizeBound := by
  have hstates (q : nativeInterpreter.State) :
      nativeInterpreterStateEncoding q < encodedUniversalInterpreterStates :=
    (Fintype.equivFin nativeInterpreter.State q).isLt
  exact descLen_desc_le nativeInterpreterStateEncoding hstates nativeInterpreter.machine

/-- The selected native machine computes `universal` within its exposed time and workspace
bounds. This statement keeps the native certificate separate from encoding that machine as a
program for another universal run. -/
private theorem encodedUniversalInterpreter_computes :
    ComputesFunTidilyInTimeAndSpace nativeInterpreter.machine eIn eOut universal
      encodedUniversalInterpreterTime encodedUniversalInterpreterSpace :=
  nativeInterpreter.computes

/-- Every finite prefix of the encoded interpreter visits at most its certified number of work
cells. This directly connects the public description to the selected native machine's workspace
certificate, independently of the observation clock. -/
theorem simSpace_encodedUniversalInterpreter_le (i : Desc × List ℕ × ℕ) (clock : ℕ) :
    simSpace encodedUniversalInterpreter ((eIn i).map eBit) clock ≤
      encodedUniversalInterpreterSpace i := by
  unfold encodedUniversalInterpreter
  rw [simSpace_desc]
  exact space_le_of_runsInSpace
    (encodedUniversalInterpreter_computes i).computesInTimeAndSpace.2.2 clock

/-- **The encoded interpreter realizes the existing universal function.** At any outer clock at
least the selected native interpreter's certified runtime, it has halted and emitted the encoded
value `eOut (universal i)`. -/
theorem universal_encodedUniversalInterpreter (i : Desc × List ℕ × ℕ) (clock : ℕ)
    (hclock : encodedUniversalInterpreterTime i ≤ clock) :
    universal (encodedUniversalInterpreter, (eIn i).map eBit, clock) =
      ((eOut (universal i)).map eBit, true) := by
  unfold encodedUniversalInterpreter
  rw [universal_desc]
  have hrun := (encodedUniversalInterpreter_computes i).computesInTimeAndSpace.runFrom_of_le hclock
  have hstate : (nativeInterpreter.machine.runFrom
      (nativeInterpreter.machine.initCfg (eIn i)) clock).state.isNone = true := by
    simpa only [Cfg.Halted, Option.isNone_iff_eq_none] using hrun.1
  rw [hrun.2, hstate]

end Turing.MultiTapeTM.Universal
