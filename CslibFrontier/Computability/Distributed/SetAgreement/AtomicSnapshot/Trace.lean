/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Machine
import Cslib.Foundations.Semantics.LTS.Execution

/-!
# Execution traces of the atomic snapshot implementation

Defines `SnapshotTrace`, indexed state projection `stateAt`, and conversion from `snapshotLTS.MTr`
derivations (`of_mtr`).

## Main definitions

* `Cslib.Distributed.SetAgreement.SnapshotTrace`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.stateAt`: indexed trace representation.

## Main results

* `Cslib.Distributed.SetAgreement.SnapshotTrace.stateAt_zero`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.stateAt_step`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.of_mtr`: basic trace and `MTr` conversion lemmas.
-/

public section

namespace Cslib.Distributed.SetAgreement

/-! ### Execution traces and register write monotonicity (`Lemma 3.1`) -/

/-- An indexed execution trace of `snapshotLTS ord dInit` starting from `SnapshotState.init dInit`:
`states` has length `events.length + 1`, `states[0] = init`, and each `events[t]` steps `states[t]`
to `states[t + 1]`. -/
structure SnapshotTrace {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) where
  /-- Sequence of executed atomic events. -/
  events : List (SnapshotEvent P Data)
  /-- Sequence of visited configurations (`length = events.length + 1`). -/
  states : List (SnapshotState P Data)
  /-- Length alignment. -/
  states_length : states.length = events.length + 1
  /-- Initial configuration is `SnapshotState.init dInit`. -/
  head_eq : states[0]'(by omega) = SnapshotState.init dInit
  /-- Valid step relation at every index `t < events.length`. -/
  step_valid : ∀ t (ht : t < events.length),
    stepSnapshot ord dInit (states[t]'(by omega)) events[t] =
      some (states[t + 1]'(by omega))

namespace SnapshotTrace

variable {P Data : Type*} [Fintype P] [DecidableEq P] {ord : ScanOrder P} {dInit : Data}

/-- State at index `t` of trace `τ` (clamped at the final state if `t ≥ τ.states.length`). -/
@[expose]
def stateAt (τ : SnapshotTrace ord dInit) (t : ℕ) : SnapshotState P Data :=
  if ht : t < τ.states.length then τ.states[t]
  else τ.states[τ.events.length]'(by have := τ.states_length; omega)

@[simp]
theorem stateAt_zero (τ : SnapshotTrace ord dInit) : τ.stateAt 0 = SnapshotState.init dInit := by
  have h0 : 0 < τ.states.length := by have := τ.states_length; omega
  simp only [stateAt, h0, ↓reduceDIte, τ.head_eq]

theorem stateAt_step (τ : SnapshotTrace ord dInit) {t : ℕ} (ht : t < τ.events.length) :
    stepSnapshot ord dInit (τ.stateAt t) τ.events[t] = some (τ.stateAt (t + 1)) := by
  have ht₁ : t < τ.states.length := by have := τ.states_length; omega
  have ht₂ : t + 1 < τ.states.length := by have := τ.states_length; omega
  simp only [stateAt, ht₁, ht₂, ↓reduceDIte]
  exact τ.step_valid t ht

/-- Convert any `MTr` reachability derivation from `init` into a `SnapshotTrace`. -/
theorem of_mtr {tr : List (SnapshotEvent P Data)} {s : SnapshotState P Data}
    (hmtr : (snapshotLTS ord dInit).MTr (SnapshotState.init dInit) tr s) :
    ∃ τ : SnapshotTrace ord dInit, τ.events = tr ∧ τ.stateAt tr.length = s := by
  obtain ⟨states, hex⟩ := Cslib.LTS.Execution.of_mTr hmtr
  refine ⟨⟨tr, states, hex.length, hex.start, hex.trans⟩, rfl, ?_⟩
  have hlt : tr.length < states.length := by have := hex.length; omega
  simp only [stateAt, hlt, ↓reduceDIte, hex.last']

end SnapshotTrace

end Cslib.Distributed.SetAgreement
