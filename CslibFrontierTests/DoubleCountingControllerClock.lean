/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Reachability.DoubleCounting.ControllerClock

/-! # Ordinary-import controller action counters and streaming-scan composition -/
namespace CslibFrontierTests.DoubleCountingControllerClock
open Cslib.DoubleCounting

private structure Counts where
  edges : ℕ
  members : ℕ
  deriving DecidableEq

-- These wrappers instrument callbacks; every control decision still runs the real controller.
private def edge (answer : Option Bool) : OptionT (StateM Counts) Bool :=
  OptionT.mk fun s => (answer, { s with edges := s.edges + 1 })
private def member (answer : Option Bool) : OptionT (StateM Counts) Bool :=
  OptionT.mk fun s => (answer, { s with members := s.members + 1 })

private def allEdges (_ _ : Fin 3) := edge (some true)
private def outsideZero (_ : ℕ) (_ : Tally) (v : Fin 3) := member (some (v != 0))
private def oneEdge (u v : Fin 3) := edge (some (u == 1 && v == 0))

-- A tie counts the newly reached vertex once, scans the round, then skips the terminal query.
example : (runController allEdges outsideZero 2).run ⟨0, 0⟩ =
    (some (some (.bad 1)), ⟨3, 6⟩) := by apply Prod.ext <;> decide +kernel

-- A rejecting membership call keeps its charge, along with all preceding edge calls.
example : (runController allEdges
    (fun _ _ v => member (if v = 2 then none else some (v != 0))) 2).run ⟨0, 0⟩ =
    (none, ⟨3, 4⟩) := by apply Prod.ext <;> decide +kernel

example : (runController (fun _ _ : Fin 3 => edge none) outsideZero 2).run ⟨0, 0⟩ =
    (none, ⟨1, 1⟩) := by apply Prod.ext <;> decide +kernel

-- Incorrect replies can add the same vertex for every round and exhaust all fuel.
example : (runController oneEdge outsideZero 2).run ⟨0, 0⟩ =
    (some none, ⟨9, 12⟩) := by apply Prod.ext <;> decide +kernel

-- A successful negative verdict pays for the final membership call.
example : (runController (fun _ _ : Fin 3 => edge (some false))
    (fun _ _ v => member (some (v == 0))) 2).run ⟨0, 0⟩ =
    (some (some (.decided false)), ⟨6, 4⟩) := by apply Prod.ext <;> decide +kernel

-- Weighted clocks give the explicit separate polynomial call bounds, for every reply script.
example (edgeReply : Fin 3 → Fin 3 → Option Bool)
    (memberReply : ℕ → Tally → Fin 3 → Option Bool) :
    ((runController (fun u v => edge (edgeReply u v))
      (fun k t v => member (memberReply k t v)) 2).run ⟨0, 0⟩).2.edges ≤ 27 ∧
    ((runController (fun u v => edge (edgeReply u v))
      (fun k t v => member (memberReply k t v)) 2).run ⟨0, 0⟩).2.members ≤ 37 := by
  constructor
  · exact runController_clock Counts.edges 1 0 _ _
      (fun _ _ _ => Nat.le_refl _) (fun _ _ _ _ _ => Nat.le_refl _) 2 ⟨0, 0⟩
  · exact runController_clock Counts.members 0 1 _ _
      (fun _ _ _ => Nat.le_refl _) (fun _ _ _ _ _ => Nat.le_refl _) 2 ⟨0, 0⟩

private def tick {α : Type} (value : α) : StateM ℕ α := fun s => (value, s + 1)
private def outer (_ _ : Fin 1) : OptionT (StateM ℕ) Bool := OptionT.mk (tick (some true))
private def select (_ : Fin 1) : StateM ℕ Bool := tick true
private def next : StateM ℕ (Option (Fin 1)) := tick (some 0)
private def inner (_ _ : Fin 1) : StateM ℕ Bool := tick true

-- With no round budget, a destination read rejects before an inner edge query.
-- The charged state survives through both scan and controller rejection.
example : (runController outer
    (fun k t v => OptionT.mk (Scan.runM select next inner 0 v k t)) 0).run 0 =
    (none, 2) := by apply Prod.ext <;> decide +kernel

-- This is the same program, bounded by composing the membership scan's action theorem.
example : ((runController outer
    (fun k t v => OptionT.mk (Scan.runM select next inner 0 v k t)) 0).run 0).2 ≤ 13 := by
  exact runController_scan_clock id outer select next inner 0 0
    (fun _ _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _) 0

end CslibFrontierTests.DoubleCountingControllerClock
