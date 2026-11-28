/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeOracleProgram

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Static bounds for named native oracle programs

The first-order description of a native oracle machine stores one row for every control, input
symbol, work-head observation and answer-head observation
(`Turing.MultiTapePTM.Internal.Description.table_length_ofMachine`). For a state type of
cardinality `s`, `k` work tapes and `r` oracle channels that is `s * 3 * 3 ^ k * 3 ^ r` rows. This
module bounds the encoded description by that row count and the largest encoded row.

The family-level theorem `Description.staticBits_polynomiallyBounded_of_le` compares a size
schedule with `Description.scheduledBitsBound` and assumes that the row schedule is
polynomially bounded. Polynomial state, tape and channel schedules do not imply this: the factor
`3 ^ (k + r)` can be exponential. For fixed `k` and `r` the row count is a constant multiple of the
state cardinality, so the premise follows from a polynomial state schedule. An application whose
number of channels grows must prove the row premise separately.

## Main definitions

* `Turing.MultiTapePTM.Internal.Description.maxEncodedRowBits`: largest encoded row of the table.
* `Turing.MultiTapePTM.Internal.Description.structuralBitsBound`: arithmetic description bound.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.staticBitsBound`: the bound specialized to a
  retained witness.

## Main results

* `Turing.MultiTapePTM.Internal.Description.descLen_ofMachine_le`: the generated description fits
  the structural bound.

## References

The structural accounting interface is original to this module.
-/

public section

namespace Turing.MultiTapePTM.Internal

open Cslib Turing.MultiTapeMachine Turing.MultiTapeTM

namespace Description

open Turing.MultiTapePTM.Universal
open Turing.MultiTapeTM.Internal.NativeCompiler (stateEncodingBound)

variable {k r : ℕ} {State : Type} [Fintype State]

/-- Largest encoded length of a row of `table`. -/
@[expose] def maxEncodedRowBits (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) : ℕ :=
  ((table stateEncoding machine).map fun row =>
    (encPair Universal.eKey Universal.eBranches row).length).foldr max 0

private theorem encoded_row_le_maxEncodedRowBits (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r))
    {row : Universal.Key × Universal.Branches}
    (hrow : row ∈ table stateEncoding machine) :
    (encPair Universal.eKey Universal.eBranches row).length ≤
      maxEncodedRowBits stateEncoding machine :=
  List.le_max_of_le (List.mem_map_of_mem hrow) le_rfl

/-- Arithmetic upper bound for a right-associated description encoding with the given structural
coordinates. `rowCount` and `maxRowBits` are kept independent so asymptotic users must justify the
chosen table representation explicitly. -/
@[expose] def structuralBitsBound (tapeCount stateTagCount operationCount initialTag rowCount
    maxRowBits : ℕ) : ℕ :=
  2 * tapeCount + 1 + 2 * stateTagCount + 1 + 2 * operationCount + 1 +
    2 * initialTag + 1 + rowCount * (2 * maxRowBits + 1)

/-- Construction-derived upper bound for the complete encoded description of a native machine. -/
@[expose] def descriptionBitsBound (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) : ℕ :=
  structuralBitsBound k (stateEncodingBound stateEncoding) r (stateEncoding machine.initial)
    (observationRowCount (Fintype.card State) k r)
    (maxEncodedRowBits stateEncoding machine)

/-- The exact generated first-order description fits its construction-derived structural bound. -/
theorem descLen_ofMachine_le (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) :
    Universal.descLen (ofMachine stateEncoding machine) ≤
      descriptionBitsBound stateEncoding machine := by
  have htable := Turing.MultiTapeTM.length_encList_le
    (encPair Universal.eKey Universal.eBranches) (ofMachine stateEncoding machine).table
    (fun _ hrow => encoded_row_le_maxEncodedRowBits stateEncoding machine hrow)
  rw [table_length_ofMachine] at htable
  simp only [Universal.descLen, Universal.eDesc_apply, length_encPair, encUnary_apply,
    List.length_replicate] at htable ⊢
  unfold descriptionBitsBound structuralBitsBound
  omega

/-- Structural bound for a family of descriptions. The exact exhaustive row count is visible in
the formula rather than inferred from the component schedules. -/
@[expose] def scheduledBitsBound
    (stateCard tapeCount stateTagCount operationCount initialTag maxRowBits : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  structuralBitsBound (tapeCount n) (stateTagCount n) (operationCount n) (initialTag n)
    (observationRowCount (stateCard n) (tapeCount n) (operationCount n)) (maxRowBits n)

/-- A static-size schedule pointwise bounded by the structural schedule is polynomially bounded
when the structural coordinates, the exhaustive row schedule and the maximum encoded row schedule
are. The row hypothesis is separate because it does not follow from polynomial `tapeCount` and
`operationCount`. The statement takes plain schedules, so it applies to an indexed family of
witnesses without packaging their dependent state types. -/
theorem staticBits_polynomiallyBounded_of_le
    {staticBits stateCard tapeCount stateTagCount operationCount initialTag maxRowBits : ℕ → ℕ}
    (htapes : Cslib.PolynomiallyBounded tapeCount)
    (hstates : Cslib.PolynomiallyBounded stateTagCount)
    (hoperations : Cslib.PolynomiallyBounded operationCount)
    (hinitial : Cslib.PolynomiallyBounded initialTag)
    (hrows : Cslib.PolynomiallyBounded (fun n =>
      observationRowCount (stateCard n) (tapeCount n) (operationCount n)))
    (hmaxRow : Cslib.PolynomiallyBounded maxRowBits)
    (hle : ∀ n, staticBits n ≤
      scheduledBitsBound stateCard tapeCount stateTagCount operationCount initialTag maxRowBits n) :
    Cslib.PolynomiallyBounded staticBits := by
  have hbound : Cslib.PolynomiallyBounded (scheduledBitsBound stateCard tapeCount stateTagCount
      operationCount initialTag maxRowBits) := by
    unfold scheduledBitsBound structuralBitsBound
    fun_prop
  exact hbound.mono_of_le hle

end Description

namespace NativeOracleProgram

open Cslib.Probability

universe u

variable {r : ℕ} {Alpha : Type u} {Beta : Type}
  {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
  {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}

/-- Cardinality of the retained native control type. -/
@[expose] noncomputable def stateCard
    (witness : NativeOracleProgram r program encIn encOut) : ℕ :=
  letI := witness.stateFintype
  Fintype.card witness.State

/-- Declared natural-tag control count of the retained first-order description. -/
@[expose] noncomputable def stateTagCount
    (witness : NativeOracleProgram r program encIn encOut) : ℕ :=
  letI := witness.stateFintype
  Turing.MultiTapeTM.Internal.NativeCompiler.stateEncodingBound witness.stateEncoding

/-- Natural tag of the retained machine's initial control. -/
@[expose] def initialStateTag
    (witness : NativeOracleProgram r program encIn encOut) : ℕ :=
  witness.stateEncoding witness.machine.initial

/-- Exact number of rows exhaustively stored by the retained witness description. -/
@[expose] noncomputable def observationRowCount
    (witness : NativeOracleProgram r program encIn encOut) : ℕ :=
  Description.observationRowCount witness.stateCard witness.tapeCount r

/-- Maximum encoded generated row of the retained witness description. -/
@[expose] noncomputable def maxEncodedRowBits
    (witness : NativeOracleProgram r program encIn encOut) : ℕ :=
  letI := witness.stateFintype
  Description.maxEncodedRowBits witness.stateEncoding witness.machine

/-- Construction-derived static upper bound exposing tapes, channels, finite-state coordinates,
the exhaustive row count and maximum encoded row length. -/
@[expose] noncomputable def staticBitsBound
    (witness : NativeOracleProgram r program encIn encOut) : ℕ :=
  Description.structuralBitsBound witness.tapeCount witness.stateTagCount r
    witness.initialStateTag witness.observationRowCount witness.maxEncodedRowBits

/-- The retained artifact's exact `descLen` static charge fits its structural upper bound. -/
theorem staticBits_le_staticBitsBound
    (witness : NativeOracleProgram r program encIn encOut) :
    witness.staticBits ≤ witness.staticBitsBound := by
  let _ := witness.stateFintype
  exact Description.descLen_ofMachine_le witness.stateEncoding witness.machine

/-- The retained table has exactly the exposed exhaustive row count. -/
theorem description_table_length
    (witness : NativeOracleProgram r program encIn encOut) :
    witness.description.table.length = witness.observationRowCount := by
  let _ := witness.stateFintype
  exact Description.table_length_ofMachine witness.stateEncoding witness.machine

end NativeOracleProgram

end Turing.MultiTapePTM.Internal
