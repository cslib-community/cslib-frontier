/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceContext

/-! Re-enter the Justesen tally at a variable seed and check replay and encoded length. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONJustesenTally

open Cslib.Code.JustesenFamily Cslib.Complexity.STCON Cslib.DoubleCounting
open Turing Turing.MultiTapeTM Turing.DoubleCounting

/-- Re-entry at a different subdivision dimension still returns a passing negative reply. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (radius : ℕ) (expected : Tally) (branch : Scan.Branch size.vertexCount),
      Scan.run (configurationJustesenSubdivisionAdjacent ntm c w seed)
          source target radius expected branch = some false →
      let params : MembershipTally.Context :=
        ⟨size.vertexCount, source.val, target.val, radius, expected⟩
      let baseParams := { params with size := params.size + 1 }
      let base := configurationJustesenMembershipTally ntm c [] 0 baseParams
      let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
      let M := base.withInit (MembershipTally.retainedInitial ctx params)
      let bits := MembershipTally.selectors (BoundedWalk.selectors 3) branch
      baseParams.size ≠ params.size ∧ M.FirstHalting w bits M.init ∧
        MembershipTally.retainedReply (M.run w bits) = some false := by
  intro I size seed source target radius expected branch hscan params baseParams base ctx M bits
  refine ⟨Nat.ne_of_gt (Nat.lt_succ_self params.size), ?_⟩
  dsimp only [M, base, ctx]
  rw [configurationJustesenMembershipTally_withInit]
  exact (configurationJustesenMembershipTally_firstHalting_iff ntm c w seed source target
    radius expected bits false).mpr
    ⟨branch, ⟨rfl, hscan⟩, fun other h =>
      MembershipTally.selectors_injective _ (BoundedWalk.eq_of_selectors_prefix 3) h.1.symm⟩

/-- Final membership at the loop's initial exact totals has one successful selector list
at any valid seed and endpoints. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (fuel : ℕ),
      let ctx : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let regs := SourceRoundLoop.start ctx fuel
      let base := justesenSourceMembershipMachine ntm c
      let M := base.withInit (justesenSourceMembershipStart regs)
      ∃! bits, M.FirstHalting w bits M.init ∧
        (MembershipTally.retainedReply (M.run w bits)).isSome := by
  intro I size seed source target fuel ctx regs base M
  dsimp only [M, base, regs, SourceRoundLoop.start, ctx]
  rw [justesenSourceMembershipMachine_withInit]
  let adjacent := configurationJustesenSubdivisionAdjacent ntm c w seed
  simpa only [expected_zero, adjacent] using
    configurationJustesenMembershipTally_existsUnique_firstHalting ntm c w
      seed source target 0 (existsUnique_passes_zero (fun u v => adjacent u v = true) source)

/-- A common polynomial clock and logarithmic state bound apply after re-entry at
the radius and tally limits. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenMembershipTallyClock ntm c) ∧
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
        let params : MembershipTally.Context := ⟨n, source.val, target.val, n, ⟨n, n * n⟩⟩
        let base := configurationJustesenMembershipTally ntm c [] 0 params
        let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
        let M := base.withInit (MembershipTally.retainedInitial ctx params)
        M.HaltsWithin w (configurationJustesenMembershipTallyClock ntm c w) ∧
          ∀ bits, (MembershipTally.encRetainedState encJustesenSubdivisionContext
            encJustesenSubdivisionState (M.run w bits)).length ≤ C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, h⟩ := configurationJustesenMembershipTally_length_run_le_log ntm c
  refine ⟨configurationJustesenMembershipTallyClock_polyBounded ntm c, C, fun w => ?_⟩
  intro I n seed source target params base ctx M
  dsimp only [M, base, ctx]
  rw [configurationJustesenMembershipTally_withInit]
  exact ⟨configurationJustesenMembershipTally_haltsWithin_clock ntm c w
    seed source target n ⟨n, n * n⟩ le_rfl,
    h w seed source target n ⟨n, n * n⟩ le_rfl le_rfl le_rfl⟩

open Cslib.Reachability.Hoza Turing.NondeterministicQueryMachine ComputableInSpace

private noncomputable def zeroRadiusParams {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : MembershipTally.Context :=
  let setup := configurationSeedSearchSetup ntm c w
  ⟨setup.parameters.search.subdivision.vertexCount, setup.sourceID, setup.targetID, 0, ⟨0, 0⟩⟩

private theorem run_skip {n : ℕ} (edge : Fin n → Fin n → Bool) (source target : Fin n) :
    Scan.run edge source target 0 ⟨0, 0⟩ (fun _ => none) = some false := by
  have hprefix (i : ℕ) (hi : i ≤ n) :
      Scan.tallyPrefix edge source target 0 (fun _ => none) hi = some Scan.Result.zero := by
    induction i with
    | zero => exact Scan.tallyPrefix_zero edge source target 0 _
    | succ i ih =>
      rw [Scan.tallyPrefix_succ edge source target 0 _ (Nat.lt_of_succ_le hi),
        ih (Nat.le_of_succ_le hi)]
      rfl
  rw [Scan.run_eq_finish, hprefix]
  rfl

/-- The final callback returns a passing negative reply and preserves the next selectors. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount),
      let ctx : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let entry := justesenSourceMembershipStart ⟨ctx, 1, 0, ⟨0, 0⟩⟩
      let bits := MembershipTally.selectors (BoundedWalk.selectors 3)
        (fun _ : Fin size.vertexCount => none)
      (justesenSourceMembershipMachine ntm c).readReply MembershipTally.retainedReply
        w entry (bits ++ [false, true, false]) = some (false, [true, false]) := by
  intro I size seed source target ctx entry bits
  exact (justesenSourceMembership_readReply_iff ntm c w seed source target 1 0 ⟨0, 0⟩
    _ false [true, false]).mpr ⟨fun _ => none, rfl, run_skip _ _ _⟩

/-- Compile queries at seed zero using the designated endpoints computed from the original
word. The same machine has a native workspace bound, halts on every input, and has one
accepting occurrence for the passing negative selector list. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let M := configurationJustesenMembershipTally ntm c [] 0 ⟨0, 0, 0, 0, ⟨0, 0⟩⟩
    let init := fun w => MembershipTally.retainedInitial
      (configurationJustesenSubdivisionContext ntm c (encBits w) 0) (zeroRadiusParams ntm c w)
    ∃ K, ∃ R : Routines M init encBits (fun w => K * (Nat.log2 (encBits w).length + 1)),
      ∀ w, R.machine.RunsInSpace (encBits w)
        (R.k * (2 * (R.c * (K * (Nat.log2 (encBits w).length + 1))) + 1)) ∧
        (∃ t, R.machine.RunsInTime (encBits w) t) ∧
        let n := (zeroRadiusParams ntm c w).size
        let bits := MembershipTally.selectors (BoundedWalk.selectors 3) (fun _ : Fin n => none)
        ∃! indices, ∃ final,
          Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (encBits w)) indices =
            some (bits, final) ∧ final.Halted ∧ final.output = [true] := by
  let budget (w : List Bool) := Nat.log2 (encBits w).length
  obtain ⟨t, A, hspace⟩ := configurationSeedSearchSetup_inLogSpace ntm c
  obtain ⟨D, hlength⟩ := length_configurationSeedSearchSetup_le_log ntm c
  have hsetup : ComputableInSpace (configurationSeedSearchSetup ntm c) encBits
      encSeedSearchSetup budget :=
    ⟨t, max A D,
      hspace.mono (fun _ => le_rfl) fun _ => Nat.mul_le_mul_right _ (le_max_left A D),
      fun w => (hlength w).trans (Nat.mul_le_mul_right _ (le_max_right A D))⟩
  have hn := encSubdivisionSize_vertexCount_budget
    (encSeedSearchSize_subdivision_budget (encSeedSearchParameters_search_budget
      (encSeedSearchSetup_parameters_budget hsetup)))
  have hparams : ComputableInSpace (zeroRadiusParams ntm c) encBits
      MembershipTally.encContext budget :=
    MembershipTally.encContext_mk_budget hn (encSeedSearchSetup_sourceID_budget hsetup)
      (encSeedSearchSetup_targetID_budget hsetup)
      ((ComputableInSpace.constZero 0).mono_le fun _ => Nat.zero_le _)
      ((ComputableInSpace.constZero (⟨0, 0⟩ : Tally)).mono_le fun _ => Nat.zero_le _)
  have hrank (w : List Bool) :
      0 < (configurationSeedSearchParameters ntm c (encBits w)).search.seedLimit :=
    Nat.two_pow_pos _
  obtain ⟨K, ⟨R⟩⟩ := configurationJustesenMembershipTally_exists_routines ntm c
    (ComputableInLogSpace.const 0) hrank hparams (fun w => by
      obtain ⟨hs, ht⟩ := configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w
      simp only [encBits_apply, zeroRadiusParams]
      exact ⟨True.intro, hs, ht, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩)
  refine ⟨K, R, fun w => ⟨R.runsInSpace w, ?_, ?_⟩⟩
  · apply R.exists_runsInTime w (time := configurationJustesenMembershipTallyClock ntm c w)
    rw [encBits_apply, configurationJustesenMembershipTally_withInit]
    let setup := configurationSeedSearchSetup ntm c w
    obtain ⟨hs, ht⟩ := configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w
    exact configurationJustesenMembershipTally_haltsWithin_clock ntm c w
      ⟨0, Nat.two_pow_pos _⟩ ⟨setup.sourceID, hs⟩ ⟨setup.targetID, ht⟩
      0 ⟨0, 0⟩ (Nat.zero_le _)
  · let setup := configurationSeedSearchSetup ntm c (encBits w)
    obtain ⟨hs, ht⟩ := configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c (encBits w)
    apply (configurationJustesenMembershipTally_native_firstHalting_iff ntm c R w
      ⟨0, Nat.two_pow_pos _⟩ ⟨setup.sourceID, hs⟩ ⟨setup.targetID, ht⟩
      0 ⟨0, 0⟩ _ rfl rfl).mpr
    exact ⟨fun _ => none, ⟨rfl, false, run_skip _ _ _⟩, fun _ h =>
      MembershipTally.selectors_injective _ (BoundedWalk.eq_of_selectors_prefix 3) h.1.symm⟩

/-- A supplied round and concrete final membership can share the existing source-loop
transition and query certificates. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    {ρ : Type} (encRound : ρ ↪ List Bool)
    (initial : SourceRoundLoop.Registers JustesenSourceContext)
    (round : NondeterministicQueryMachine ρ)
    (roundStart : SourceRoundLoop.Registers JustesenSourceContext → ρ)
    (roundReply : ρ → Option RoundUpdate) :
    let R := SourceRoundLoop.encRegisters encJustesenSourceContext
    let encMember := MembershipTally.encRetainedState encJustesenSubdivisionContext
      encJustesenSubdivisionState
    let E := SourceRoundLoop.encState encJustesenSourceContext encRound encMember
    let encRoundStep := encPair encRound encReadChoice
    let encStep := encPair E encReadChoice
    let M := SourceRoundLoop.machine initial round roundStart roundReply
      (justesenSourceMembershipMachine ntm c) justesenSourceMembershipStart
      MembershipTally.retainedReply
    ComputableInSpace round.query encRound encNat (fun s => (encRound s).length) →
    ComputableInSpace roundStart R encRound (fun r => (R r).length) →
    ComputableInSpace roundReply encRound (encOption encRoundUpdate)
      (fun s => (encRound s).length) →
    ComputableInSpace round.halted encRound encBool (fun s => (encRound s).length) →
    ComputableInSpace round.next encRoundStep encRound (fun p => (encRoundStep p).length) →
    ComputableInSpace M.query E encNat (fun s => (E s).length) ∧
      ComputableInSpace M.next encStep E (fun p => (encStep p).length) := by
  intro R encMember E encRoundStep encStep M hquery hstart hreply hhalt hnext
  obtain ⟨hq, hn, hh, hr⟩ := justesenSourceMembershipMachine_parts_inSpace ntm c
  exact ⟨SourceRoundLoop.query_inSpace encJustesenSourceContext encRound encMember
      initial round roundStart roundReply (justesenSourceMembershipMachine ntm c)
      justesenSourceMembershipStart MembershipTally.retainedReply hquery hq,
    SourceRoundLoop.next_inSpace encJustesenSourceContext encRound encMember
      initial round roundStart roundReply (justesenSourceMembershipMachine ntm c)
      justesenSourceMembershipStart MembershipTally.retainedReply
      hstart justesenSourceMembershipStart_inSpace hreply hr hhalt hh hnext hn⟩

end CslibFrontierTests.STCONJustesenTally
