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

/-- The walk entry can consume a variable context in the encoded transition request. -/
example :
    let walk : NondeterministicQueryMachine Bool :=
      { init := false, query := fun _ => 0, next := Prod.fst
        halted := fun _ => true, accept := id }
    let enter := fun (context : Bool) (_ : Registers) => context
    let fuel := fun (_ : Bool) => (some 0 : Option ℕ)
    let step (p : State Bool × Bool × Option Bool × Bool) :=
      (machine negativeContext walk (enter p.2.1) fuel).next (p.1, p.2.2)
    let enc := encPair (encState encBool) (encPair encBool encReadChoice)
    ComputableInSpace step enc (encState encBool) (fun p => (enc p).length) ∧
      ∀ context, step (initial negativeContext, context, none, true) =
        .inr (.inl (⟨negativeContext, 0, Scan.Result.zero⟩, context)) := by
  intro walk enter fuel step enc
  refine ⟨?_, ?_⟩
  · exact next_withParameter_inSpace encBool encBool negativeContext walk enter fuel
      (fst encBool encRegisters) (fst encBool encReadChoice)
      (budget_const true (.refl _)) (budget_const (some 0) (.refl _))
  · intro context
    rfl

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

private def contextEdge : QueryMachine Bool where
  init := false
  query := fun _ => 0
  next := fun p => p.1
  halted := fun _ => true
  emit := fun _ => []
  finish := fun _ => []

open Turing.DoubleCounting in
/-- The same tally re-enters with a larger carrier and an adjacency context that permits
the selected edge. The queried vertex is skipped, so the tally returns a passing negative.
The clock and encoded-state bounds cover every branch from the new entry. -/
example :
    let start := fun (flag : Bool) (_ _ : ℕ) => flag
    let entry := BoundedWalk.Runtime.entry contextEdge start id 0 false (N := 1) ⟨0, 0, 0⟩
    let single := retainedMachine contextEdge start id 0 entry false ⟨1, 0, 0, 0, ⟨0, 0⟩⟩
    let expanded : Context := ⟨2, 0, 0, 1, ⟨1, 1⟩⟩
    let double := single.withInit (retainedInitial true expanded)
    let enc := encRetainedState encBool encBool
    let branch : Scan.Branch 2 := fun v => if v = 1 then some [1] else none
    let bits := MembershipTally.selectors (BoundedWalk.selectors 0) branch
    (double.FirstHalting [true] bits double.init ∧ retainedReply (double.run [true] bits) =
      some false) ∧ double.HaltsWithin [true] 23 ∧
      ∀ choices, (enc (double.run [true] choices)).length ≤ retainedStateBound 0 expanded 1 1 := by
  intro start entry single expanded double enc branch bits
  let allEdges (_ _ : Fin 2) := true
  have hscan : Scan.run allEdges 0 0 1 ⟨1, 1⟩ branch = some false := by
    rw [Scan.run_eq_finish, Scan.tallyPrefix_succ allEdges 0 0 1 branch (n := 1) (by decide),
      Scan.tallyPrefix_succ allEdges 0 0 1 branch (n := 0) (by decide), Scan.tallyPrefix_zero]
    simp [branch, allEdges, Scan.walkM, Scan.readNext, bind, StateT.bind, pure, StateT.pure,
      Scan.Result.finish, Scan.Result.recordWalk, Scan.Result.zero, Tally.matches_iff]
  dsimp only [double, single]
  rw [retainedMachine_withInit]
  have hsource : expanded.source < expanded.size := by decide
  refine ⟨?_, ?_, ?_⟩
  · apply (retainedMachine_firstHalting_reply_iff contextEdge start id 0 entry true expanded
      [true] bits false).mpr
    exact (withRuntimeWalk_firstHalting_iff contextEdge start id 0 entry true [true]
      allEdges 0 0 1 ⟨1, 1⟩ (fun _ _ => rfl) (fun _ _ => rfl) bits false).mpr
      ⟨branch, ⟨rfl, hscan⟩, fun other h =>
        selectors_injective _ (BoundedWalk.eq_of_selectors_prefix 0) h.1.symm⟩
  · refine HaltsWithin.mono _ _
      (retainedMachine_haltsWithin contextEdge start id 0 entry true expanded hsource [true]) ?_
    change 2 * (1 * ((2 : ℕ).size + 0 + 3) + ((2 : ℕ).size + 2) + 2) + 1 ≤ 23
    rw [← Nat.size_eq_bits_len]
    decide
  · intro choices
    simpa only [enc, encBool_apply, List.length_singleton] using
      retainedMachine_length_run_le contextEdge start id 0 entry true encBool encBool expanded
        hsource [true] 1
        (fun _ _ _ _ => by simp only [encBool_apply, List.length_singleton, le_refl]) choices

open Turing.DoubleCounting in
/-- A caller can initialize a retained tally and invoke its observers under one input budget. -/
example :
    let start := fun (flag : Bool) (_ _ : ℕ) => flag
    let entry := BoundedWalk.Runtime.entry contextEdge start id 0 false (N := 1) ⟨0, 0, 0⟩
    let M := retainedMachine contextEdge start id 0 entry false ⟨1, 0, 0, 0, ⟨0, 0⟩⟩
    let encIn := encPair encBool encContext
    let enc := encRetainedState encBool encBool
    let budget (p : Bool × Context) := (encIn p).length
    let enter (p : Bool × Context) : RetainedState Bool Bool := retainedInitial p.1 p.2
    ComputableInSpace enter encIn enc budget ∧
      ComputableInSpace (fun p => M.query (enter p)) encIn encNat budget ∧
      ComputableInSpace (fun p => M.halted (enter p)) encIn encBool budget ∧
      ComputableInSpace (fun p => retainedReply (enter p)) encIn (encOption encBool) budget := by
  intro start entry M encIn enc budget enter
  have hentry : ComputableInSpace enter encIn enc budget :=
    retainedInitial_budget encBool encBool (fst encBool encContext) (snd encBool encContext)
  have hquery := retainedMachine_query_inSpace contextEdge start id 0 entry false encBool encBool
    ⟨1, 0, 0, 0, ⟨0, 0⟩⟩ (budget_const (encIn := encBool) (encB := encNat) 0 (.refl _))
  have hhalt := retainedMachine_halted_inSpace contextEdge start id 0 entry false encBool encBool
    ⟨1, 0, 0, 0, ⟨0, 0⟩⟩
  exact ⟨hentry, budget_comp_linear hquery hentry, budget_comp_linear hhalt hentry,
    budget_comp_linear (retainedReply_inSpace encBool encBool) hentry⟩

open Turing.DoubleCounting in
/-- Exact totals at radius zero yield one successful selector list, which may answer false. -/
example :
    let start := fun (_ : Unit) (_ _ : ℕ) => ()
    let entry := BoundedWalk.Runtime.entry edge start verdict 0 () (N := 1) ⟨0, 0, 0⟩
    let M := withRuntimeWalk edge start verdict 0 entry ()
      ⟨2, (0 : Fin 2).val, (1 : Fin 2).val, 0, ⟨1, 0⟩⟩
    (∃! bits, M.FirstHalting [] bits M.init ∧ (reply (M.run [] bits)).isSome) ∧
      M.FirstHalting [] negativeSelectors M.init ∧
      reply (M.run [] negativeSelectors) = some false := by
  intro start entry M
  have hunique := withRuntimeWalk_existsUnique_firstHalting edge start verdict 0 entry () []
    adjacent 0 1 0 (fun _ _ => rfl) (fun _ _ => rfl)
    (existsUnique_passes_zero (fun u v => adjacent u v = true) 0)
  have hnegative := (withRuntimeWalk_firstHalting_iff edge start verdict 0 entry () []
    adjacent 0 1 0 ⟨1, 0⟩ (fun _ _ => rfl) (fun _ _ => rfl) negativeSelectors false).mpr
      ⟨negativeBranch, ⟨rfl, negativeScan⟩, fun other h => negativeBranch_unique other h.1⟩
  exact ⟨by simpa only [expected_zero, M] using hunique, hnegative⟩

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
