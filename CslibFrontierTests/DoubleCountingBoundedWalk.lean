/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.BoundedWalk

/-! # Bounded walk on the original input

The supplied edge routine reads bit zero of the original input. Changing that bit changes
the result of the same walk. The clock and workspace checks cover arbitrary selectors.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingBoundedWalk

open Turing MultiTapeTM ComputableInSpace NondeterministicQueryMachine
open Turing.DoubleCounting.BoundedWalk
open Cslib.DoubleCounting.Scan

private def edge : QueryMachine (Option Bool) where
  init := none
  query _ := 0
  next := fun (_, answer) => some (answer.getD false)
  halted := Option.isSome
  emit _ := []
  finish _ := []

private def start (_ _ : Fin 3) : Option Bool := none

private def verdict (s : Option Bool) : Bool := s.getD false

private theorem edge_halts (input : List Bool) (u v : Fin 3) :
    edge.halted (edge.runFrom input (start u v) 1) = true := by
  cases input <;> rfl

private theorem edge_agrees (input : List Bool) (u v : Fin 3) :
    verdict (edge.runFrom input (start u v) 1) = input.headD false := by
  cases input <;> rfl

private def moving : Registers 3 := ⟨0, 1, 1⟩

/-- Stopping at the initial target is valid at zero remaining fuel. -/
example :
    (machine edge start verdict 1 ⟨0, 0, 0⟩).run [] (selectors 1 ([] : List (Fin 3))) =
      .done (some 0) := by
  rw [run_selectors edge start verdict 1 _ [] (fun _ _ => false)
    (edge_halts []) (edge_agrees [])]
  simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure]

/-- A continuation with exhausted fuel rejects even if the edge callback would agree. -/
example :
    (machine edge start verdict 1 ⟨0, 1, 0⟩).run [true] (selectors (N := 3) 1 [1]) =
      .done none := by
  rw [run_selectors edge start verdict 1 _ [true] (fun _ _ => true)
    (edge_halts [true]) (edge_agrees [true])]
  simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure]

/-- A suspended caller can enter the same transition machine with a new target and fuel. -/
example :
    (machine edge start verdict 1 moving).replay [false] (selectors (N := 3) 1 [])
      (machine edge start verdict 1 ⟨0, 0, 0⟩).init = .done (some 0) := by
  rw [← run_withInit, machine_withInit]
  rw [run_selectors edge start verdict 1 _ [false] (fun _ _ => false)
    (edge_halts [false]) (edge_agrees [false])]
  simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure]

/-- A complete one-edge selector on the input identifies its destination even in a longer word. -/
example (tail : List (Fin 3)) (h : selectors (N := 3) 1 [1] <+: selectors 1 tail) :
    tail = [1] :=
  (eq_of_selectors_prefix 1 h).symm

/-- Rank three is outside the three-vertex domain. -/
example :
    (machine edge start verdict 1 moving).run [true] [true, true, true, false] = .done none :=
  run_invalid_vertex edge start verdict 1 moving [true] [true, true] rfl rfl

/-- The same proposed edge succeeds on a one bit and fails on a zero bit of the original tape. -/
example :
    (machine edge start verdict 1 moving).run [true] (selectors (N := 3) 1 [1]) = .done (some 0) ∧
    (machine edge start verdict 1 moving).run [false] (selectors (N := 3) 1 [1]) = .done none := by
  constructor
  · rw [run_selectors edge start verdict 1 _ [true] (fun _ _ => true)
      (edge_halts [true]) (edge_agrees [true])]
    simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure, moving]
  · rw [run_selectors edge start verdict 1 _ [false] (fun _ _ => false)
      (edge_halts [false]) (edge_agrees [false])]
    simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure, moving]

/-- The same bounds also apply to invalid destination and failed-call prefixes. -/
example (input bits : List Bool) :
    (machine edge start verdict 1 moving).HaltsWithin input 10 ∧
      (encState (encOption encBool) ((machine edge start verdict 1 moving).run input bits)).length
        ≤ 61 := by
  have hlength (u v : Fin 3) (t : ℕ) (_ : t ≤ 1) :
      (encOption encBool (edge.runFrom input (start u v) t)).length ≤ 2 := by
    cases edge.runFrom input (start u v) t with
    | none => decide
    | some answer => cases answer <;> decide
  exact ⟨haltsWithin edge start verdict 1 moving input,
    length_run_le edge start verdict 1 moving input (encOption encBool) 2 hlength bits⟩

private def budget (input : List Bool) : ℕ := Nat.log2 input.length + 10

/-- An enclosing caller can load the boundary and decode the returned fuel in native space. -/
example :
    ComputableInSpace (fun (r : Registers 3) => (machine edge start verdict 1 r).init)
      (encRegisters 3) (encState (encOption encBool)) (fun r => (encRegisters 3 r).length) ∧
    ComputableInSpace (remainingFuel (N := 3) (τ := Option Bool))
      (encState (encOption encBool)) (encOption encNat)
      (fun s => (encState (encOption encBool) s).length) :=
  ⟨init_budget edge start verdict 1 (of_inO ComputableInDegree.id'.inO_one),
    remainingFuel_inSpace (encOption encBool)⟩

/-- The same walk has native routines with one space envelope for all selector paths. -/
private theorem routines : Nonempty (Routines (machine edge start verdict 1 moving)
    (fun _ : List Bool => (machine edge start verdict 1 moving).init) encBits budget) := by
  have hstart : ComputableInSpace (fun p : Fin 3 × Fin 3 => start p.1 p.2)
      (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat))
      (encOption encBool) (fun p =>
        (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat) p).length) :=
    budget_const none (.refl _)
  have hresult : ComputableInSpace id (encOption encBool) (encOption encBool)
      (fun s => (encOption encBool s).length) := of_inO ComputableInDegree.id'.inO_one
  have hnext : ComputableInSpace edge.next (QueryMachine.encStateRead (encOption encBool))
      (encOption encBool) (fun p => (QueryMachine.encStateRead (encOption encBool) p).length) :=
    budget_optionSome (budget_optionGetD false (snd (encOption encBool) (encOption encBool)))
  refine Turing.DoubleCounting.BoundedWalk.exists_routines edge start verdict 1 moving
    (encOption encBool) hstart (budget_const 0 (.refl _)) hnext (budget_optionIsSome hresult)
    (budget_optionGetD false hresult) (fun _ => moving) ?_ ?_ ?_ ?_
  · exact (ComputableInSpace.constZero moving).mono_le fun _ => Nat.zero_le _
  · intro input
    rw [budget, encBits_apply]
    omega
  · intro input
    unfold budget
    have h : 6 ≤ 10 := by decide
    exact h.trans (Nat.le_add_left _ _)
  · intro input u v t _
    have h : (encOption encBool (edge.runFrom input (start u v) t)).length ≤ 2 := by
      cases edge.runFrom input (start u v) t with
      | none => decide
      | some answer => cases answer <;> decide
    exact h.trans (by unfold budget; omega)

/-- Compiling the same-input test gives one successful occurrence list for the valid walk. -/
example : ∃ R : Routines (machine edge start verdict 1 moving)
    (fun _ : List Bool => (machine edge start verdict 1 moving).init) encBits budget,
    R.machine.RunsInSpace [true] (R.k * (2 * (R.c * budget [true]) + 1)) ∧
      (∃ t, R.machine.RunsInTime [true] t) ∧
      ∃! indices, ∃ final,
        Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg [true]) indices =
          some (selectors (N := 3) 1 [1], final) ∧ final.Halted ∧ final.output = [true] := by
  obtain ⟨R⟩ := routines
  refine ⟨R, R.runsInSpace [true], ?_, ?_⟩
  · exact R.exists_runsInTime [true] (haltsWithin edge start verdict 1 moving [true])
  refine (native_firstHalting_accept_iff edge start verdict 1 moving (fun _ => moving) R
    [true] (fun _ _ => true) (edge_halts [true]) (edge_agrees [true]) _).mpr ⟨[1], 0, rfl, ?_⟩
  simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure, moving]

end CslibFrontierTests.DoubleCountingBoundedWalk
