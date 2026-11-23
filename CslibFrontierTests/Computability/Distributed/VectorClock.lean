/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.VectorClock.LowerBound
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fin.VecNotation

/-! Lamport scalar clocks, Mattern vector clocks, consistent cuts, and crown-execution
clock-dimension lower-bound steps (checked as a `module` client with ordinary imports):
`decide`-validated causal execution checks on `Fin 3` and `Fin 4`, Lamport false-causality
concurrent pairs, tie-broken `lamportTotalOrder`, Mattern exact causal & concurrent
characterizations and single-coordinate comparison of given timestamps, consistent vs
inconsistent cuts with Mattern's frontier condition, explicit `decide`-checked crown executions
on `Fin 3` and `Fin 4`, and client instantiations of `not_exists_1d_characterization`,
`unicast_clock_dim_lower_bound`, and `exists_unicast_orderEmbedding_clock_iff`. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.VectorClock

open Cslib.Distributed Cslib.Distributed.VectorClock
open scoped Cslib.Distributed.VectorClock

/-! ### Executable causal well-formedness validation (`IsValidSteps`) -/

-- Future/self receive (`sIdx ≥ i`), wrong destination, and duplicate receive are rejected.
example : Execution.IsValidSteps ([.recv (0 : Fin 3) 0] : List (Step (Fin 3))) = false := by decide
example : Execution.IsValidSteps ([.send (0 : Fin 3) 1, .recv 2 0] : List (Step (Fin 3))) = false :=
  by decide
example : Execution.IsValidSteps
    ([.send (0 : Fin 3) 1, .recv 1 0, .recv 1 0] : List (Step (Fin 3))) = false := by decide

/-! ### `Fin 3` asynchronous trace: Lamport false causality, Fidge–Mattern `vc`, and cuts -/

/-- Seven-event execution on `Fin 3`:
* `e₀` (idx 0): `0` sends to `1` (`L = 1`, `vc = ![1, 0, 0]`)
* `e₁` (idx 1): internal on `2` (`L = 1`, `vc = ![0, 0, 1]`)
* `e₂` (idx 2): `1` receives from `e₀` (`L = 2`, `vc = ![1, 1, 0]`)
* `e₃` (idx 3): `1` sends to `2` (`L = 3`, `vc = ![1, 2, 0]`)
* `e₄` (idx 4): internal on `0` (`L = 2`, `vc = ![2, 0, 0]`)
* `e₅` (idx 5): `2` receives from `e₃` (`L = 4`, `vc = ![1, 2, 2]`)
* `e₆` (idx 6): internal on `2` (`L = 5`, `vc = ![1, 2, 3]`) -/
def exFin3 : Execution (Fin 3) :=
  Execution.ofValidSteps
    [.send 0 1, .internal 2, .recv 1 0, .send 1 2, .internal 0, .recv 2 3, .internal 2]
    (by decide)

def ev3 (i : Fin 7) : exFin3.Event := ⟨⟨i.val, i.isLt⟩⟩

-- Lamport false-causality pair: `L(e₄) = 2 < 4 = L(e₅)` even though `e₄` and `e₅` are concurrent!
example :
    exFin3.lamportClock (ev3 4) = 2 ∧
    exFin3.lamportClock (ev3 5) = 4 ∧
    exFin3.lamportClock (ev3 4) < exFin3.lamportClock (ev3 5) ∧
    exFin3.Concurrent (ev3 4) (ev3 5) := by decide

-- Lamport tie-breaking total order on concurrent equal-timestamp events (`L(e₀) = 1 = L(e₁)`).
example :
    exFin3.lamportClock (ev3 0) = 1 ∧
    exFin3.lamportClock (ev3 1) = 1 ∧
    exFin3.Concurrent (ev3 0) (ev3 1) ∧
    exFin3.lamportTotalOrder (ev3 0) (ev3 1) ∧
    ¬ exFin3.lamportTotalOrder (ev3 1) (ev3 0) := by decide

-- Fidge–Mattern vector timestamps and exact causal/concurrent checks across all 49 event pairs.
example :
    exFin3.vc (ev3 0) = ![1, 0, 0] ∧
    exFin3.vc (ev3 3) = ![1, 2, 0] ∧
    exFin3.vc (ev3 4) = ![2, 0, 0] ∧
    exFin3.vc (ev3 5) = ![1, 2, 2] ∧
    exFin3.vc (ev3 6) = ![1, 2, 3] ∧
    (ev3 0 < ev3 5) ∧
    exFin3.vc (ev3 0) < exFin3.vc (ev3 5) ∧
    ¬ (exFin3.vc (ev3 4) ≤ exFin3.vc (ev3 5)) ∧
    ¬ (exFin3.vc (ev3 5) ≤ exFin3.vc (ev3 4)) := by decide

example :
    ∀ x y : exFin3.Event,
      ((x ≤ y) ↔ exFin3.vc x ≤ exFin3.vc y) ∧
      ((x < y) ↔ exFin3.vc x < exFin3.vc y) ∧
      (exFin3.Concurrent x y ↔ ¬ exFin3.vc x ≤ exFin3.vc y ∧ ¬ exFin3.vc y ≤ exFin3.vc x) :=
  by decide

-- Causal past of `e₅` (`recv 2 3`): `{e₀, e₁, e₂, e₃}` (excludes concurrent `e₄` and later `e₆`).
example : exFin3.causalPast (ev3 5) = {ev3 0, ev3 1, ev3 2, ev3 3} := by decide

-- Consistent vs inconsistent cuts and Mattern's owner-maximum frontier criterion (`Fin 3`).
def goodFrontier : Fin 3 → exFin3.Event := ![ev3 4, ev3 2, ev3 1]
def badFrontier : Fin 3 → exFin3.Event := ![ev3 4, ev3 2, ev3 5]

example :
    exFin3.IsConsistentCut (exFin3.cutOfFrontier goodFrontier) ∧
    (∀ p q : Fin 3, exFin3.vc (goodFrontier q) p ≤ exFin3.vc (goodFrontier p) p) ∧
    ¬ exFin3.IsConsistentCut (exFin3.cutOfFrontier badFrontier) ∧
    ¬ (∀ p q : Fin 3, exFin3.vc (badFrontier q) p ≤ exFin3.vc (badFrontier p) p) := by decide

-- Lattice closure of consistent cuts under `∪` and `∩`, and absence of orphan receives.
example :
    let C₁ := exFin3.causalPastLe (ev3 4)
    let C₂ := exFin3.causalPastLe (ev3 5)
    exFin3.IsConsistentCut (C₁ ∪ C₂) ∧ exFin3.IsConsistentCut (C₁ ∩ C₂) := by
  exact ⟨(exFin3.isConsistentCut_causalPastLe _).union (exFin3.isConsistentCut_causalPastLe _),
    (exFin3.isConsistentCut_causalPastLe _).inter (exFin3.isConsistentCut_causalPastLe _)⟩

/-! ### `Fin 4` trace: diamond causality and pairwise concurrency -/

def exFin4 : Execution (Fin 4) :=
  Execution.ofValidSteps
    [.send 0 1, .send 0 2, .internal 3, .recv 1 0, .recv 2 1, .send 1 3, .recv 3 5, .internal 2]
    (by decide)

def ev4 (i : Fin 8) : exFin4.Event := ⟨⟨i.val, i.isLt⟩⟩

example :
    exFin4.HappensBefore (ev4 0) (ev4 6) ∧
    exFin4.Concurrent (ev4 4) (ev4 6) ∧
    exFin4.lamportClock (ev4 4) < exFin4.lamportClock (ev4 6) ∧
    exFin4.vc (ev4 6) = ![1, 2, 0, 2] ∧
    exFin4.vc (ev4 7) = ![2, 0, 2, 0] := by decide

/-! ### Explicit `decide`-checked Charron-Bost crown executions on `Fin 3` and `Fin 4` -/

-- On `Fin 3` (24 events): `a_p ≼ b_q ↔ q ≠ (p + 1) mod 3`, and `a_p ∥ b_{(p + 1) mod 3}`.
example :
    let h3 : 2 ≤ 3 := by decide
    (∀ p q : Fin 3,
      (crownFin 3 h3).HappensBeforeLe (crownPhase1 h3 p) (crownPhase2 h3 q) ↔
        q ≠ crownShift h3 p) ∧
    (∀ p : Fin 3,
      (crownFin 3 h3).Concurrent (crownPhase1 h3 p) (crownPhase2 h3 (crownShift h3 p))) :=
  by decide

-- On `Fin 4` (40 events): `a_p ≼ b_q ↔ q ≠ (p + 1) mod 4`, and `a_p ∥ b_{(p + 1) mod 4}`.
example :
    let h4 : 2 ≤ 4 := by decide
    (∀ p q : Fin 4,
      (crownFin 4 h4).HappensBeforeLe (crownPhase1 h4 p) (crownPhase2 h4 q) ↔
        q ≠ crownShift h4 p) ∧
    (∀ p : Fin 4,
      (crownFin 4 h4).Concurrent (crownPhase1 h4 p) (crownPhase2 h4 (crownShift h4 p))) :=
  by decide

/-! ### Theorem-level client checks (incompleteness, crown dimension step, universes) -/

-- No 1D rational clock on `Fin 3`, no 2D clock on `crownFin 3`, no 3D clock on `crownFin 4`.
example : ∃ E : Execution (Fin 3), ∀ f : E.Event → ℚ,
    ¬ ∀ e₁ e₂ : E.Event, E.HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂ := by
  obtain ⟨E, hE⟩ := not_exists_1d_characterization (P := Fin 3) (by decide)
  exact ⟨E, fun f => hE f⟩

example : ¬ ∃ f : (crownFin 3 (by decide)).Event → (Fin 2 → ℚ),
    ∀ e₁ e₂, (crownFin 3 (by decide)).HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂ := by
  rintro ⟨f, hf⟩
  have h := crownFin_dim_lower_bound (by decide) f hf
  omega

example : ¬ ∃ f : (crownFin 4 (by decide)).Event → (Fin 3 → ℚ),
    ∀ e₁ e₂, (crownFin 4 (by decide)).HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂ := by
  rintro ⟨f, hf⟩
  have h := crownFin_dim_lower_bound (by decide) f hf
  omega

-- `unicast_clock_dim_lower_bound` and `exists_unicast_orderEmbedding_clock_iff` across universes.
example : ¬ ∀ E : Execution (Fin 3), ∃ f : E.Event → (Fin 2 → ℚ),
    ∀ e₁ e₂, E.HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂ := by
  intro h
  exact absurd (unicast_clock_dim_lower_bound h) (by decide)

example : ∀ E : Execution (Fin 0), ∃ f : E.Event → (Fin 0 → ℕ),
    ∀ e₁ e₂, E.HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂ :=
  exists_unicast_orderEmbedding_clock_iff.mpr (by simp)

example : (∀ E : Execution (Fin 1), ∃ f : E.Event → (Fin 0 → ℕ),
    ∀ e₁ e₂, E.HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂) ↔ False := by
  rw [exists_unicast_orderEmbedding_clock_iff]
  decide

example : ∀ E : Execution (Fin 4), ∃ f : E.Event → (Fin 4 → ℕ),
    ∀ e₁ e₂, E.HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂ :=
  exists_unicast_orderEmbedding_clock_iff.mpr (by decide)

example : ∀ E : Execution (ULift.{1} (Fin 3)), ∃ f : E.Event → (Fin 3 → ℕ),
    ∀ e₁ e₂, E.HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂ :=
  exists_unicast_orderEmbedding_clock_iff.mpr (by simp)

end CslibFrontierTests.Distributed.VectorClock
