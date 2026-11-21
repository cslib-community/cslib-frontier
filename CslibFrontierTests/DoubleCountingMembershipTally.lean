/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally.Runtime

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
example : run 1 [false, false] = .inr (.inr none) ∧
    reply (run 1 [false, false]) = none := ⟨rfl, rfl⟩

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
private theorem negativeReplay :
    let M := withBoundedWalk edge start verdict 0 0 negativeContext
    M.FirstHalting [] negativeSelectors M.init ∧
      M.run [] negativeSelectors = .inr (.inr (some false)) :=
  (withBoundedWalk_firstHalting_iff edge start verdict 0 0 []
    adjacent 0 1 0 ⟨1, 0⟩ negativeSelectors false (fun _ _ => rfl) (fun _ _ => rfl)).mpr
    ⟨negativeBranch, ⟨rfl, negativeScan⟩, fun other h => negativeBranch_unique other h.1⟩

/-- A caller can re-enter the same tally and read the passing negative result. -/
example :
    let M := withBoundedWalk edge start verdict 0 0
      { negativeContext with expected := ⟨0, 0⟩ }
    reply (M.replay [] negativeSelectors (initial negativeContext)) = some false := by
  dsimp only
  rw [← run_withInit, withBoundedWalk_withInit, reply_eq_some_iff]
  exact negativeReplay.2

open Turing.DoubleCounting in
/-- The same tally re-enters at a larger dimension and selects a walk to a vertex outside
the original carrier. The queried vertex is skipped, so the tally returns `some false`.
The clock and encoded-state bounds cover every branch from the new entry. -/
example :
    let start := fun (_ : Unit) (_ _ : ℕ) => ()
    let acceptEdge := fun (_ : Unit) => true
    let entry := BoundedWalk.Runtime.entry edge start acceptEdge 0 () (N := 1) ⟨0, 0, 0⟩
    let single := withRuntimeWalk edge start acceptEdge 0 entry () ⟨1, 0, 0, 0, ⟨0, 0⟩⟩
    let expanded : Context := ⟨2, 0, 0, 1, ⟨1, 1⟩⟩
    let double := single.withInit (initial expanded)
    let enc := MembershipTally.encState (BoundedWalk.Runtime.encState encUnit encUnit)
    let branch : Scan.Branch 2 := fun v => if v = 1 then some [1] else none
    let bits := MembershipTally.selectors (BoundedWalk.selectors 0) branch
    (double.FirstHalting [true] bits double.init ∧ reply (double.run [true] bits) = some false) ∧
      double.HaltsWithin [true] 23 ∧
      ∀ choices, (enc (double.run [true] choices)).length ≤
        runtimeWalkStateBound 0 expanded 0 0 := by
  intro start acceptEdge entry single expanded double enc branch bits
  let allEdges (_ _ : Fin 2) := true
  have hscan : Scan.run allEdges 0 0 1 ⟨1, 1⟩ branch = some false := by
    rw [Scan.run_eq_finish, Scan.tallyPrefix_succ allEdges 0 0 1 branch (n := 1) (by decide),
      Scan.tallyPrefix_succ allEdges 0 0 1 branch (n := 0) (by decide), Scan.tallyPrefix_zero]
    simp [branch, allEdges, Scan.walkM, Scan.readNext, bind, StateT.bind, pure, StateT.pure,
      Scan.Result.finish, Scan.Result.recordWalk, Scan.Result.zero, Tally.matches_iff]
  dsimp only [double, single]
  rw [withRuntimeWalk_withInit]
  have hsource : expanded.source < expanded.size := by decide
  refine ⟨?_, ?_, ?_⟩
  · exact (withRuntimeWalk_firstHalting_iff edge start acceptEdge 0 entry () [true]
      allEdges 0 0 1 ⟨1, 1⟩ (fun _ _ => rfl) (fun _ _ => rfl) bits false).mpr
      ⟨branch, ⟨rfl, hscan⟩, fun other h =>
        selectors_injective _ (BoundedWalk.eq_of_selectors_prefix 0) h.1.symm⟩
  · refine HaltsWithin.mono _ _
      (withRuntimeWalk_haltsWithin edge start acceptEdge 0 entry () expanded hsource [true]) ?_
    change 2 * (1 * ((2 : ℕ).size + 0 + 3) + ((2 : ℕ).size + 2) + 2) + 1 ≤ 23
    rw [← Nat.size_eq_bits_len]
    decide
  · intro choices
    simpa only [enc, encUnit_apply, List.length_nil] using
      withRuntimeWalk_length_run_le edge start acceptEdge 0 entry () encUnit encUnit expanded
        hsource [true] 0 (fun _ _ _ _ => by simp only [encUnit_apply, List.length_nil, le_refl])
        choices

example :
    let E := encState (Turing.DoubleCounting.BoundedWalk.encState (N := 2) encUnit)
    ComputableInSpace reply E (encOption encBool) (fun s => (E s).length) :=
  reply_inSpace _

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
