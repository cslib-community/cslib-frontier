/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.DijkstraScholten.Correctness

/-! Checked `module` client tests for `Cslib.Distributed.DijkstraScholten` using ordinary imports:
1. `Fin 4` diamond-and-cycle diffusing execution exercising tree attachment (`0 → 1 → 3`, `0 → 2`),
   non-tree diamond chord immediate signalling (`2 → 3`), cyclic back-edges to `root` (`3 → 0`) and
   an engaged ancestor (`3 → 1`), `ComputationIdle` potential `drainMeasure = 9`, and exact 9-step
   bottom-up leaf detachment to `Terminated` and `GlobalQuiescent`.
2. `Fin 3` re-activation before detachment (an idle node with `deficit = 0` and `parent = some 0`
   receiving a second basic message emits an immediate signal, preserving exact deficit
   conservation).
3. `Fin 3` sequential-polling false-termination trace (`0 → 2 → 1`) checked by `decide`, alongside
   instantiations of `exists_phantom_termination_naive_poll` and `Reachable.*` dot-notation checks.
-/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.DijkstraScholten

open Cslib Cslib.Distributed.DijkstraScholten

/-! ### 1. `Fin 4` diamond + cyclic back-edge diffusing trace -/

/-- Active diffusing phase on `Fin 4` (`root = 0`):
tree edges `0 → 1`, `0 → 2`, `1 → 3`, diamond chord `2 → 3` (immediate signal to `2`), and cyclic
back-edges `3 → 0` and `3 → 1` (immediate signals to `3`), followed by all four nodes turning idle.
-/
def fin4ActivePhase : List (Action (Fin 4)) :=
  [ .sendBasic 0 1
  , .sendBasic 0 2
  , .recvBasic 0 1
  , .recvBasic 0 2
  , .sendBasic 1 3
  , .sendBasic 2 3
  , .recvBasic 1 3
  , .recvBasic 2 3
  , .sendBasic 3 0
  , .sendBasic 3 1
  , .recvBasic 3 0
  , .recvBasic 3 1
  , .becomeIdle 0
  , .becomeIdle 1
  , .becomeIdle 2
  , .becomeIdle 3 ]

/-- 9-step control drain on `Fin 4` reducing `drainMeasure = 2 * 3 + 3 = 9` by `1` at each step:
`2` consumes its chord signal and detaches from `0`; `3` consumes both cycle signals and detaches
from `1`; `1` consumes `3`'s signal and detaches from `0`; `0` consumes the two root signals. -/
def fin4DrainPhase : List (Action (Fin 4)) :=
  [ .recvSignal 2
  , .detach 2 0
  , .recvSignal 3
  , .recvSignal 3
  , .detach 3 1
  , .recvSignal 1
  , .detach 1 0
  , .recvSignal 0
  , .recvSignal 0 ]

def fin4IdleState : State (Fin 4) :=
  (runTrace? (0 : Fin 4) (initState 0) fin4ActivePhase).getD (initState 0)

def fin4FinalState : State (Fin 4) :=
  (runTrace? (0 : Fin 4) fin4IdleState fin4DrainPhase).getD fin4IdleState

theorem fin4_diamond_cycle_checkpoint_and_drain :
    (lts (0 : Fin 4)).MTr (initState 0) fin4ActivePhase fin4IdleState ∧
    (fin4IdleState.proc 0).parent = none ∧
    (fin4IdleState.proc 1).parent = some 0 ∧
    (fin4IdleState.proc 2).parent = some 0 ∧
    (fin4IdleState.proc 3).parent = some 1 ∧
    fin4IdleState.ancestor? 2 3 = some 0 ∧
    (fin4IdleState.proc 0).deficit = 2 ∧
    (fin4IdleState.proc 1).deficit = 1 ∧
    (fin4IdleState.proc 2).deficit = 1 ∧
    (fin4IdleState.proc 3).deficit = 2 ∧
    fin4IdleState.ComputationIdle ∧
    fin4IdleState.engagedCount 0 = 3 ∧
    fin4IdleState.inFlightSignals = 3 ∧
    fin4IdleState.drainMeasure 0 = 9 ∧
    ¬ fin4IdleState.Terminated 0 ∧
    (lts (0 : Fin 4)).MTr fin4IdleState fin4DrainPhase fin4FinalState ∧
    fin4DrainPhase.length = 9 ∧
    fin4FinalState.Terminated 0 ∧
    fin4FinalState.GlobalQuiescent := by
  have hmIdle : (lts (0 : Fin 4)).MTr (initState 0) fin4ActivePhase fin4IdleState :=
    mtr_iff_runTrace?_eq_some.mpr (by decide)
  have hmFinal : (lts (0 : Fin 4)).MTr fin4IdleState fin4DrainPhase fin4FinalState :=
    mtr_iff_runTrace?_eq_some.mpr (by decide)
  refine ⟨hmIdle, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmFinal, ?_, ?_, ?_⟩ <;>
    decide

/-! ### 2. `Fin 3` re-activation while idle-but-still-engaged (`parent ≠ none`) -/

def fin3ReactivateBeforeDetach : List (Action (Fin 3)) :=
  [ .sendBasic 0 1
  , .recvBasic 0 1
  , .becomeIdle 1
  , .sendBasic 0 1
  , .recvBasic 0 1 ]

def fin3ReactivatedState : State (Fin 3) :=
  (runTrace? (0 : Fin 3) (initState 0) fin3ReactivateBeforeDetach).getD (initState 0)

-- Node `1` is idle with `deficit = 0` after step 3, yet still holds `parent = some 0`; when the
-- second basic message `0 → 1` arrives before `1` detaches, `1` emits an immediate signal to `0`,
-- keeping `deficit 0 = 2 = 0 + 1 + 1` conserved.
example :
    (lts (0 : Fin 3)).MTr (initState 0) fin3ReactivateBeforeDetach fin3ReactivatedState ∧
    (fin3ReactivatedState.proc 1).active = true ∧
    (fin3ReactivatedState.proc 1).parent = some 0 ∧
    (fin3ReactivatedState.proc 0).deficit = 2 ∧
    fin3ReactivatedState.inFlightSignalTo 0 = 1 ∧
    (fin3ReactivatedState.children 0 0).card = 1 :=
  ⟨mtr_iff_runTrace?_eq_some.mpr (by decide),
    by decide, by decide, by decide, by decide, by decide⟩

/-! ### 3. `Fin 3` sequential-polling phantom termination trace (`0 → 2 → 1`) -/

def fin3PollS1 : State (Fin 3) :=
  (runTrace? (0 : Fin 3) (initState 0) [.sendBasic 0 2, .becomeIdle 0]).getD (initState 0)

def fin3PollS2 : State (Fin 3) :=
  (runTrace? (0 : Fin 3) fin3PollS1 [.recvBasic 0 2]).getD fin3PollS1

def fin3PollS3 : State (Fin 3) :=
  (runTrace? (0 : Fin 3) fin3PollS2 [.sendBasic 2 1, .becomeIdle 2]).getD fin3PollS2

def fin3PollS4 : State (Fin 3) :=
  (step? (0 : Fin 3) fin3PollS3 (.recvBasic 2 1)).getD fin3PollS3

theorem fin3_naive_poll_phantom_trace :
    (lts (0 : Fin 3)).MTr (initState 0) [.sendBasic 0 2, .becomeIdle 0] fin3PollS1 ∧
    (lts (0 : Fin 3)).MTr fin3PollS1 [.recvBasic 0 2] fin3PollS2 ∧
    (lts (0 : Fin 3)).MTr fin3PollS2 [.sendBasic 2 1, .becomeIdle 2] fin3PollS3 ∧
    (lts (0 : Fin 3)).Tr fin3PollS3 (.recvBasic 2 1) fin3PollS4 ∧
    (fin3PollS1.proc 0).active = false ∧
    (fin3PollS2.proc 1).active = false ∧ (fin3PollS2.proc 2).active = true ∧
    (fin3PollS3.proc 2).active = false ∧ ⟨2, 1⟩ ∈ fin3PollS3.basicMsgs ∧
    (fin3PollS4.proc 1).active = true ∧
    ¬ fin3PollS1.Terminated 0 ∧ ¬ fin3PollS2.Terminated 0 ∧
    ¬ fin3PollS3.Terminated 0 ∧ ¬ fin3PollS4.Terminated 0 :=
  ⟨mtr_iff_runTrace?_eq_some.mpr (by decide),
    mtr_iff_runTrace?_eq_some.mpr (by decide),
    mtr_iff_runTrace?_eq_some.mpr (by decide),
    by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

-- Instantiations of `exists_phantom_termination_naive_poll` on `Fin 3` (distinct chord `2 → 1`)
-- and `Fin 2` (return message `1 → 0`).
example :
    ∃ (tr₁ tr₂ tr₃ : List (Action (Fin 3))) (s₁ s₂ s₃ s₄ : State (Fin 3)),
      (lts 0).MTr (initState 0) tr₁ s₁ ∧ (lts 0).MTr s₁ tr₂ s₂ ∧
      (lts 0).MTr s₂ tr₃ s₃ ∧ (lts 0).Tr s₃ (.recvBasic 2 1) s₄ ∧
      (s₁.proc 0).active = false ∧ (s₂.proc 1).active = false ∧
      (s₃.proc 2).active = false ∧ (s₄.proc 1).active = true ∧ ¬ s₃.Terminated 0 := by
  obtain ⟨tr₁, tr₂, tr₃, s₁, s₂, s₃, s₄, hm₁, hm₂, hm₃, htr₄, h0, h1, _, _, h2, _, h1',
      _, _, hnt₃, _⟩ :=
    exists_phantom_termination_naive_poll (0 : Fin 3) 1 2 (by decide) (by decide)
  exact ⟨tr₁, tr₂, tr₃, s₁, s₂, s₃, s₄, hm₁, hm₂, hm₃, htr₄, h0, h1, h2, h1', hnt₃⟩

example :
    ∃ (tr₁ tr₂ tr₃ : List (Action (Fin 2))) (s₁ s₂ s₃ s₄ : State (Fin 2)),
      (lts 0).MTr (initState 0) tr₁ s₁ ∧ (lts 0).MTr s₁ tr₂ s₂ ∧
      (lts 0).MTr s₂ tr₃ s₃ ∧ (lts 0).Tr s₃ (.recvBasic 1 0) s₄ ∧
      (s₁.proc 0).active = false ∧ (s₃.proc 1).active = false ∧
      (s₄.proc 0).active = true ∧ ¬ s₃.Terminated 0 := by
  obtain ⟨tr₁, tr₂, tr₃, s₁, s₂, s₃, s₄, hm₁, hm₂, hm₃, htr₄, h0, _, _, _, h1, _, h0',
      _, _, hnt₃, _⟩ :=
    exists_phantom_termination_naive_poll (0 : Fin 2) 0 1 (by decide) (by decide)
  exact ⟨tr₁, tr₂, tr₃, s₁, s₂, s₃, s₄, hm₁, hm₂, hm₃, htr₄, h0, h1, h0', hnt₃⟩

/-! ### 4. Ordinary-import `Reachable.*` dot-notation and general API checks -/

example {P : Type*} [Fintype P] [DecidableEq P] {root : P} {s : State P}
    (hr : Reachable root s) :
    (s.proc root).parent = none ∧
      (∀ dst, (dst ≠ root ∧ (s.proc dst).parent = none) ↔
        (dst ≠ root ∧ (s.proc dst).active = false ∧ (s.proc dst).deficit = 0 ∧
          (s.proc dst).parent = none)) ∧
      (∀ p, (s.proc p).deficit =
        s.inFlightBasicFrom p + s.inFlightSignalTo p + (s.children root p).card) ∧
      (∀ p, ∀ m, 0 < m → s.ancestor? m p ≠ some p) ∧
      (s.Terminated root ↔ s.GlobalQuiescent) :=
  ⟨hr.root_parent_eq_none, hr.attach_iff, hr.deficit_eq_inFlight_add_children,
    fun p _ hm => hr.ancestor?_ne_self_of_pos p hm, hr.terminated_iff_globalQuiescence⟩

example {P : Type*} [Fintype P] [DecidableEq P] {root p : P} {s : State P}
    (hr : Reachable root s) (hp : p ≠ root) (hpar : (s.proc p).parent ≠ none) :
    ∃ k < Fintype.card P, 0 < k ∧ s.ancestor? k p = some root :=
  hr.engaged_reaches_root hp hpar

example {P : Type*} [Fintype P] [DecidableEq P] {root : P} {s : State P}
    (hr : Reachable root s) (hidle : s.ComputationIdle) :
    ((lts root).IsTerminal s ↔ s.Terminated root) ∧
      ∃ tr s', (lts root).MTr s tr s' ∧ s'.GlobalQuiescent ∧
        s'.drainMeasure root + tr.length = s.drainMeasure root ∧
        tr.length ≤ 2 * Fintype.card P + s.inFlightSignals := by
  refine ⟨hr.isTerminal_iff_terminated_of_computationIdle hidle, ?_⟩
  obtain ⟨⟨tr, s', hmtr, ht, hlen⟩, _⟩ := hr.quiescent_drains_to_terminated hidle
  exact ⟨tr, s', hmtr, (hr.mtr hmtr).terminated_implies_quiescent ht,
    (hidle.mtr_drainMeasure hmtr).2, hlen⟩

end CslibFrontierTests.Distributed.DijkstraScholten
