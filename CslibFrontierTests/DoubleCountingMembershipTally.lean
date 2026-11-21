/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally

/-! Checks for the membership tally's passing negative answer and rejecting terminal check. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingMembershipTally

open Turing Turing.DoubleCounting.MembershipTally
open MultiTapeTM ComputableInSpace NondeterministicQueryMachine
open Cslib.DoubleCounting

private def unusedWalk : NondeterministicQueryMachine Unit where
  init := ()
  query := fun _ => 0
  next := fun _ => ()
  halted := fun _ => true
  accept := fun _ => true

private def run (count : ℕ) :=
  (machine ⟨1, 0, 0, 0, ⟨count, 0⟩⟩ unusedWalk (fun _ => ()) (fun _ => some 0)).run []

-- Skipping the only vertex is a successful negative answer when the expected tally is empty.
example : run 0 [false, false] = .inr (.inr (some false)) := rfl

example :
    let ctx : Context := ⟨1, 0, 0, 0, ⟨0, 0⟩⟩
    let M := machine ctx unusedWalk (fun _ => ()) (fun _ => some 0)
    M.FirstHalting [] [false, false] M.init :=
  (firstHalting_finish ⟨1, 0, 0, 0, ⟨0, 0⟩⟩ unusedWalk (fun _ => ()) (fun _ => some 0)
    [] [false] Cslib.DoubleCounting.Scan.Result.zero false rfl rfl).1

-- The same choices reject when the expected count is one.
example : run 1 [false, false] = .inr (.inr none) := rfl

-- A selected walk returns through one deterministic boundary step.
example : run 1 [true, false, false] = .inr (.inr (some true)) := rfl

-- Decode the selected zero-step walk and check the same result in the typed scanner.
example : ∃ branch : Cslib.DoubleCounting.Scan.Branch 1,
    Cslib.DoubleCounting.Scan.run (fun _ _ => false) 0 0 0 ⟨1, 0⟩ branch = some true := by
  suffices ∃ branch : Cslib.DoubleCounting.Scan.Branch 1,
      [true, false, false] = selectors (fun _ => []) branch ∧
        Cslib.DoubleCounting.Scan.run (fun _ _ => false) 0 0 0 ⟨1, 0⟩ branch = some true by
    obtain ⟨branch, _, h⟩ := this
    exact ⟨branch, h⟩
  refine exists_scan_of_firstHalting unusedWalk (fun _ => ()) (fun _ => some 0)
    [] (fun _ _ => false) 0 0 0 ⟨1, 0⟩ (fun _ => []) ?_ [true, false, false] true ?_ ?_
  · intro v _ bits remaining _ hfirst hfuel
    change some 0 = some remaining at hfuel
    cases hfuel
    have hv : v = 0 := Fin.eq_zero v
    subst v
    have hbits : bits = [] := by
      cases bits with
      | nil => rfl
      | cons b bs =>
        have ht := ((unusedWalk.firstHalting_cons_iff [] b bs ()).mp hfirst).1
        cases ht
    exact ⟨[], hbits, Cslib.DoubleCounting.Scan.walkM_replay_eq_some.mpr
      ⟨List.isChainFromTo_singleton, rfl⟩⟩
  · exact (firstHalting_finish ⟨1, 0, 0, 0, ⟨1, 0⟩⟩ unusedWalk (fun _ => ())
      (fun _ => some 0) [] [true, false] ⟨⟨1, 0⟩, true⟩ true rfl rfl).1
  · rfl

private def edge : QueryMachine Unit where
  init := ()
  query := fun _ => 0
  next := fun _ => ()
  halted := fun _ => true
  emit := fun _ => []
  finish := fun _ => []

private def adjacent : Fin 2 → Fin 2 → Bool := fun _ _ => false

private def start (_ _ : Fin 2) : Unit := ()

private def verdict (_ : Unit) : Bool := false

private def negativeContext : Context := ⟨2, 0, 1, 0, ⟨1, 0⟩⟩

private def negativeBranch : Scan.Branch 2 := fun v =>
  if v = 0 then some [] else none

private def negativeSelectors : List Bool :=
  selectors (Turing.DoubleCounting.BoundedWalk.selectors 0) negativeBranch

private theorem negativeScan : Scan.run adjacent 0 1 0 ⟨1, 0⟩ negativeBranch = some false := by
  rw [Scan.run_eq_finish, Scan.tallyPrefix_succ adjacent 0 1 0 negativeBranch (n := 1) (by decide),
    Scan.tallyPrefix_succ adjacent 0 1 0 negativeBranch (n := 0) (by decide), Scan.tallyPrefix_zero]
  simp [negativeBranch, Scan.walkM, Scan.readNext, bind, StateT.bind, pure, StateT.pure,
    Scan.Result.finish, Scan.Result.recordWalk, Scan.Result.zero, Tally.matches_iff]

private theorem negativeBranch_unique (other : Scan.Branch 2)
    (h : negativeSelectors = selectors (Turing.DoubleCounting.BoundedWalk.selectors 0) other) :
    other = negativeBranch :=
  selectors_injective _ (Turing.DoubleCounting.BoundedWalk.eq_of_selectors_prefix 0) h.symm

-- A checked zero-step walk is selected, but the queried vertex is skipped.
example :
    let M := withBoundedWalk edge start verdict 0 0 negativeContext
    M.FirstHalting [] negativeSelectors M.init ∧
      M.run [] negativeSelectors = .inr (.inr (some false)) :=
  (withBoundedWalk_firstHalting_iff edge start verdict 0 0 []
    adjacent 0 1 0 ⟨1, 0⟩ negativeSelectors false (fun _ _ => rfl) (fun _ _ => rfl)).mpr
    ⟨negativeBranch, ⟨rfl, negativeScan⟩, fun other h => negativeBranch_unique other h.1⟩

private def budget (input : List Bool) : ℕ :=
  Nat.log2 input.length + boundedWalkStateBound 2 0 negativeContext 0 + 1

private theorem routines : Nonempty
    (Routines (withBoundedWalk edge start verdict 0 0 negativeContext)
      (fun _ : List Bool => initial negativeContext) encBits budget) := by
  refine withBoundedWalk_exists_routines edge start verdict 0 0 encBits budget
    negativeContext (fun _ => negativeContext) encUnit ?_ ?_
    (budget_const () (.refl _)) (budget_const 0 (.refl _)) (budget_const () (.refl _))
    (budget_const true (.refl _)) (budget_const false (.refl _)) (fun _ => 0) ?_ ?_
  · exact (ComputableInSpace.constZero negativeContext).mono_le fun _ => Nat.zero_le _
  · intro input
    rw [encBits_apply]
    unfold budget
    omega
  · intro input u v t ht
    rw [encUnit_apply]
    rfl
  · intro input
    unfold budget
    omega

/-- A passing negative result is one accepting native callback occurrence. -/
example : ∃ R : Routines (withBoundedWalk edge start verdict 0 0 negativeContext)
    (fun _ : List Bool => initial negativeContext) encBits budget,
    ∃! indices, ∃ final,
      Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg []) indices =
        some (negativeSelectors, final) ∧ final.Halted ∧ final.output = [true] := by
  obtain ⟨R⟩ := routines
  refine ⟨R, (withBoundedWalk_native_firstHalting_iff edge start verdict 0 0 negativeContext
    (fun _ => negativeContext) R [] adjacent 0 1 0 ⟨1, 0⟩ negativeSelectors rfl
    (fun _ _ => rfl) (fun _ _ => rfl)).mpr ?_⟩
  exact ⟨negativeBranch, ⟨rfl, false, negativeScan⟩,
    fun other h => negativeBranch_unique other h.1⟩

end CslibFrontierTests.DoubleCountingMembershipTally
