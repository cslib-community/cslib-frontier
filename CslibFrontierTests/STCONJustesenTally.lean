/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceLoop

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

/-- A round's membership entry queries its candidate and preserves the caller's suffix. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source candidate : Fin n),
      let ctx : SourceRound.Context := ⟨n, source.val, 0, ⟨0, 0⟩⟩
      let adjacency := configurationJustesenSubdivisionContext ntm c w seed.val
      let entry := justesenRoundCallbackStart adjacency ctx (.member candidate.val)
      let bits := MembershipTally.selectors (BoundedWalk.selectors 3) (fun _ : Fin n => none)
      (justesenRoundCallback ntm c).readReply justesenRoundCallbackReply
        w entry (bits ++ [false, true]) = some (false, [true]) := by
  intro I n seed source candidate ctx adjacency entry bits
  dsimp only [entry]
  rw [justesenRoundCallback_readReply]
  exact (justesenRoundMembership_readReply_iff ntm c w seed source candidate
    0 ⟨0, 0⟩ _ false [true]).mpr ⟨fun _ => none, rfl, run_skip _ _ _⟩

/-- A tagged edge request returns adjacency on the original word and keeps the suffix. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (u v : Fin n) (ctx : SourceRound.Context)
      (suffix : List Bool),
      let adjacency := configurationJustesenSubdivisionContext ntm c w seed.val
      let entry := justesenRoundCallbackStart adjacency ctx (.edge u.val v.val)
      (justesenRoundCallback ntm c).readReply justesenRoundCallbackReply
        w entry ([false, false, false, false] ++ suffix) =
        some (configurationJustesenSubdivisionAdjacent ntm c w seed u v, suffix) := by
  intro I n seed u v ctx suffix adjacency entry
  dsimp only [entry]
  rw [justesenRoundCallback_readReply]
  refine (configurationJustesenSubdivisionEdge_readReply_iff ntm c w seed u v _ suffix _).mpr
    ⟨rfl, ?_⟩
  simp only [configurationJustesenSubdivisionAdjacent, decide_eq_true_eq]

-- Parsed replies can be used directly as adjacency and reachability facts.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source u v : Fin n) (radius : ℕ),
      let adjacent := configurationJustesenSubdivisionAdjacent ntm c w seed
      let edge := fun i j => adjacent i j = true
      let ctx : SourceRound.Context := ⟨n, source.val, radius, expected edge source radius⟩
      let adjacency := configurationJustesenSubdivisionContext ntm c w seed.val
      let parse := fun req => (justesenRoundCallback ntm c).readReply justesenRoundCallbackReply
        w (justesenRoundCallbackStart adjacency ctx req)
      ∀ (bits : List Bool) (hit : Bool) (suffix : List Bool),
        (parse (.edge u.val v.val) bits = some (hit, suffix) → hit = adjacent u v) ∧
        (parse (.member v.val) bits = some (hit, suffix) →
          (hit ↔ v ∈ Relation.reachableWithin edge source radius)) := by
  intro I n seed source u v radius adjacent edge ctx adjacency parse bits hit suffix
  have h := configurationJustesenRoundCallback_readReply_correct ntm c w seed source radius
  exact ⟨h (.edge u.val v.val) ⟨u.isLt, v.isLt⟩ bits hit suffix,
    h (.member v.val) v.isLt bits hit suffix⟩

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

/-- Exact radius-zero membership at a different target returns false and preserves
the caller's suffix. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount),
      target ≠ source → ∀ suffix : List Bool,
      let adjacent := configurationJustesenSubdivisionAdjacent ntm c w seed
      let edge := fun u v => adjacent u v = true
      let ctx : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let entry := justesenSourceMembershipStart ⟨ctx, 1, 0, expected edge source 0⟩
      let M := justesenSourceMembershipMachine ntm c
      ∃ bits, M.readReply MembershipTally.retainedReply w entry bits = some (false, suffix) := by
  intro I size seed source target hne suffix adjacent edge ctx entry M
  obtain ⟨callBits, ⟨hfirst, hret⟩, _⟩ := justesenSourceMembership_existsUnique_firstHalting
    ntm c w seed source target 1 0 (existsUnique_passes_zero edge source)
  obtain ⟨hit, hhit⟩ := Option.isSome_iff_exists.mp hret
  let bits := callBits ++ false :: suffix
  have hparsed := (readReply_iff M MembershipTally.retainedReply w bits entry hit suffix).mpr
    ⟨callBits, rfl, hfirst, hhit⟩
  have hspec := justesenSourceMembership_readReply_correct ntm c w seed source target
    1 0 bits hit suffix hparsed
  have hfalse : hit = false := Bool.eq_false_iff.mpr fun htrue =>
    hne (by simpa only [Relation.reachableWithin_zero, Set.mem_singleton_iff] using hspec.mp htrue)
  exact ⟨bits, hfalse ▸ hparsed⟩

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

/-- At exact radius-zero totals the compiled tally has one accepting native branch across
all selector lists, at a clock obtained from the concrete selector bound. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) {rank budget : List Bool → ℕ} {params : List Bool → MembershipTally.Context}
    (R : Routines (configurationJustesenMembershipTally ntm c [] 0 ⟨0, 0, 0, 0, ⟨0, 0⟩⟩)
      (fun w => MembershipTally.retainedInitial
        (configurationJustesenSubdivisionContext ntm c (encBits w) (rank w)) (params w))
      encBits budget) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount),
      rank w = seed.val →
      params w = ⟨size.vertexCount, source.val, target.val, 0, ⟨1, 0⟩⟩ →
      ∃ fuel, R.machine.RunsInTime (encBits w) fuel ∧
        (Native.countingMachine R.I R.P R.F R.C).acceptCount fuel
          (R.machine.initCfg (encBits w)) = 1 := by
  intro I size seed source target hrank hparams
  obtain ⟨fuel, hclock⟩ := R.exists_runsInTime w
    (time := configurationJustesenMembershipTallyClock ntm c w) (by
      rw [encBits_apply, configurationJustesenMembershipTally_withInit, hrank, hparams]
      exact configurationJustesenMembershipTally_haltsWithin_clock ntm c w
        seed source target 0 ⟨1, 0⟩ (Nat.zero_le _))
  refine ⟨fuel, hclock, ?_⟩
  refine configurationJustesenMembershipTally_acceptCount_eq_one ntm c R w hclock
    seed source target 0 hrank ?_ (existsUnique_passes_zero
      (fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true) source)
  change params w = ⟨size.vertexCount, source.val, target.val, 0,
    expected (fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true)
      source 0⟩
  rwa [expected_zero]

/-- The final membership callback fits its bounds at the source loop's scalar limits,
even for a tally larger than any exact round total. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
        let ctx : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        let r : SourceRoundLoop.Registers JustesenSourceContext :=
          ⟨ctx, 0, n, ⟨1 + n * n, n * n * n⟩⟩
        let M := justesenSourceMembershipMachine ntm c
        let entry := justesenSourceMembershipStart r
        (M.withInit entry).HaltsWithin w (configurationJustesenMembershipTallyClock ntm c w) ∧
          ∀ bits, (MembershipTally.encRetainedState encJustesenSubdivisionContext
            encJustesenSubdivisionState (M.replay w bits entry)).length ≤
              C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, h⟩ := justesenSourceMembership_bounds ntm c
  refine ⟨C, fun w => ?_⟩
  intro I n seed source target ctx r M entry
  have hsize : ctx.size = n :=
    configurationJustesenSourceContext_size ntm c w seed.val source.val target.val
  have hr : SourceRoundLoop.Admissible ctx ctx.size n r := by
    simp only [SourceRoundLoop.Admissible, r, hsize, Nat.zero_add, and_self, le_refl]
  exact h w seed source target n le_rfl r hr

-- Every prefix fits the shared budget, and zero fuel stops without a verdict.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
        (limit : ℕ), limit ≤ n →
        let ctx : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        let M := justesenSourceLoop ntm c ctx limit
        M.HaltsWithin w (configurationJustesenSourceLoopClock ntm c w) ∧
          (∀ bits, (encJustesenSourceLoopState (M.run w bits)).length ≤
            C * (Nat.log2 w.length + 1)) ∧
          (limit = 0 → ∀ bits, M.run w bits = .inr none) := by
  obtain ⟨C, hspace⟩ := configurationJustesenSourceLoop_length_run_le_log ntm c
  refine ⟨C, fun w => ?_⟩
  intro I n seed source target limit hlimit ctx M
  refine ⟨configurationJustesenSourceLoop_haltsWithin_clock ntm c w
    seed source target limit hlimit, hspace w seed source target limit hlimit,
    fun hzero bits => ?_⟩
  subst limit
  exact justesenSourceLoop_run_zero ntm c ctx w bits

/-- A round with retained Justesen adjacency has native query and transition certificates. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (adjacency : JustesenSubdivisionContext) (initial : SourceRound.Context) :
    let E := SourceRound.encMachineState JustesenRoundCallbackState encJustesenRoundCallbackState
    let encStep := encPair E encReadChoice
    let round := SourceRound.machine initial (justesenRoundCallback ntm c)
      (justesenRoundCallbackStart adjacency) justesenRoundCallbackReply
    ComputableInSpace round.query E encNat (fun s => (E s).length) ∧
      ComputableInSpace round.next encStep E (fun p => (encStep p).length) := by
  intro E encStep round
  obtain ⟨hq, hn, hh, hr⟩ := justesenRoundCallback_parts_inSpace ntm c
  have hadj := budget_const (encIn := SourceRound.encState)
    (encB := encJustesenSubdivisionContext) adjacency (.refl _)
  have hid := budget_id (enc := SourceRound.encState) (.refl _)
  have hentry := budget_comp_linear justesenRoundCallbackStart_inSpace (budget_prod hadj hid)
  exact ⟨SourceRound.machine_query_inSpace encJustesenRoundCallbackState initial
      (justesenRoundCallback ntm c) (justesenRoundCallbackStart adjacency)
      justesenRoundCallbackReply hq,
    SourceRound.machine_next_inSpace encJustesenRoundCallbackState initial
      (justesenRoundCallback ntm c) (justesenRoundCallbackStart adjacency)
      justesenRoundCallbackReply hentry hr hh hn⟩

-- The two request tags give at most one successful complete round at exact totals.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source : Fin n) (radius : ℕ),
      let edge := fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true
      (∃! transcript, Passes edge source radius transcript) →
      let ctx : SourceRound.Context := ⟨n, source.val, radius, expected edge source radius⟩
      let adjacency := configurationJustesenSubdivisionContext ntm c w seed.val
      let M := SourceRound.machine ctx (justesenRoundCallback ntm c)
        (justesenRoundCallbackStart adjacency) justesenRoundCallbackReply
      {bits : List Bool | M.FirstHalting w bits M.init ∧
        (SourceRound.answer (M.run w bits)).isSome}.Subsingleton := by
  intro I n seed source radius edge hpass ctx adjacency M
  apply SourceRound.subsingleton_successful_firstHalting
  intro req hr left hleft right hright
  exact (configurationJustesenRoundCallback_existsUnique_firstHalting ntm c w
    seed source radius hpass req hr).unique hleft hright

-- The first complete round either ends the scan or preserves its exact-tally invariant.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) (base : SourceRoundLoop.Registers JustesenSourceContext) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
      let edge := fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true
      let ctx : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let r := SourceRoundLoop.start ctx n
      let M := (justesenRetainedSourceRound ntm c base).withInit
        (justesenRetainedSourceRoundEntry r)
      ∃! bits, ∃ update, M.FirstHalting w bits M.init ∧
        justesenRetainedSourceRoundReply (M.run w bits) = some update ∧
        update.tally = expected edge source 1 ∧
        (update.bad = false ↔ ∃! transcript, Passes edge source 1 transcript) ∧
        (update.bad = false → update.tally.count ≠ r.tally.count →
          JustesenSourceRoundExact ctx edge source (r.advance update.tally)) := by
  intro I n seed source target edge ctx r M
  have hreentry : M = justesenRetainedSourceRound ntm c r :=
    justesenRetainedSourceRound_withInit ntm c base r
  rw [hreentry]
  have hpass := existsUnique_passes_zero edge source
  have hinit : JustesenSourceRoundExact ctx edge source r :=
    justesenSourceRoundExact_start ctx edge source
  have htally : r = ⟨ctx, n, 0, expected edge source 0⟩ := by
    simp only [r, SourceRoundLoop.start, expected_zero]
  obtain ⟨bits, ⟨update, hfirst, hreply⟩, hunique⟩ :=
    configurationJustesenRetainedSourceRound_existsUnique_firstHalting ntm c w
      seed source target n 0 hpass
  have hnext := configurationJustesenRetainedSourceRound_correct ntm c w
    seed source target n 0 hpass bits update hfirst hreply
  have hfirst' : (justesenRetainedSourceRound ntm c r).FirstHalting w bits
      (justesenRetainedSourceRound ntm c r).init := htally.symm ▸ hfirst
  have hreply' : justesenRetainedSourceRoundReply
      ((justesenRetainedSourceRound ntm c r).run w bits) = some update := htally.symm ▸ hreply
  refine ⟨bits, ⟨update, hfirst', hreply', hnext.1, hnext.2, ?_⟩, ?_⟩
  · exact configurationJustesenRetainedSourceRound_exact_advance ntm c w
      seed source target r hinit bits update hfirst' hreply'
  · rintro other ⟨result, hother, hret, _, _, _⟩
    exact hunique other ⟨result, htally ▸ hother, htally ▸ hret⟩

-- Use the shared clock for the actual round and check both callback tags at the loop caps.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
        let adjacency := configurationJustesenSubdivisionContext ntm c w seed.val
        let ctx : SourceRound.Context := ⟨n, source.val, n, ⟨1 + n * n, n * n * n⟩⟩
        let N := justesenRoundCallback ntm c
        let start := justesenRoundCallbackStart adjacency
        let clock := configurationJustesenRoundCallbackClock ntm c w
        (SourceRound.machine ctx N start justesenRoundCallbackReply).HaltsWithin w
            (SourceRound.roundClock n clock) ∧
          ∀ bits, (encJustesenRoundCallbackState
              (N.replay w bits (start ctx (.edge source.val target.val)))).length ≤
                C * (Nat.log2 w.length + 1) ∧
            (encJustesenRoundCallbackState
              (N.replay w bits (start ctx (.member target.val)))).length ≤
                C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, h⟩ := configurationJustesenRoundCallback_bounds ntm c
  refine ⟨C, fun w => ?_⟩
  intro I n seed source target adjacency ctx N start clock
  have hc := h w seed source n ⟨1 + n * n, n * n * n⟩ le_rfl le_rfl le_rfl
  exact ⟨SourceRound.haltsWithin ctx N start justesenRoundCallbackReply w clock
      (fun req hr => (hc req hr).1), fun bits =>
    ⟨(hc (.edge source.val target.val) ⟨source.isLt, target.isLt⟩).2 bits,
      (hc (.member target.val) target.isLt).2 bits⟩⟩

-- Re-enter the same round at admissible registers and bound every prefix logarithmically.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (initial : SourceRoundLoop.Registers JustesenSourceContext) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
        let context : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        ∀ r, SourceRoundLoop.Admissible context context.size n r →
          let M := (justesenRetainedSourceRound ntm c initial).withInit
            (justesenRetainedSourceRoundEntry r)
          M.HaltsWithin w (configurationJustesenRetainedSourceRoundClock ntm c w) ∧
            ∀ bits, (encJustesenRetainedSourceRoundState (M.run w bits)).length ≤
              C * (Nat.log2 w.length + 1) := by
  obtain ⟨A, hround⟩ := configurationJustesenRetainedSourceRound_bounds ntm c
  obtain ⟨B, hsize⟩ := configurationJustesenRetainedSourceRound_envelopes_le_log ntm c
  refine ⟨B + A, fun w => ?_⟩
  intro I n seed source target context r hr M
  dsimp only [M]
  rw [justesenRetainedSourceRound_withInit]
  obtain ⟨hhalt, hpref⟩ := hround w seed source target n le_rfl r hr
  refine ⟨hhalt, fun bits => (hpref bits).trans ?_⟩
  simpa only [Nat.add_mul] using
    (hsize w seed source target n le_rfl).2 (A * (Nat.log2 w.length + 1))

-- A native scan with computed full fuel has one accepting occurrence at its polynomial clock.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let ctx (w : List Bool) : JustesenSourceContext :=
      ⟨configurationJustesenSubdivisionContext ntm c w 0, 0, 0⟩
    let M := justesenSourceLoop ntm c (ctx []) 0
    let entry (w : List Bool) := (justesenSourceLoop ntm c (ctx w) (ctx w).size).init
    ∃ R : Routines M entry encBits (fun w => Nat.log2 w.length + 1),
      ∃ L d, ∀ w, R.machine.RunsInSpace w (L * (Nat.log2 w.length + 1)) ∧
        R.machine.RunsInTime w (polyClock d w.length) ∧
        (Native.countingMachine R.I R.P R.F R.C).acceptCount (polyClock d w.length)
          (R.machine.initCfg w) = 1 := by
  intro ctx M entry
  let budget (w : List Bool) := Nat.log2 w.length + 1
  have hadj := configurationJustesenSubdivisionContext_inSpace ntm c (enc := encBits)
    (ComputableInLogSpace.const 0) (fun _ => Nat.two_pow_pos _)
  have hadj' : ComputableInSpace (fun w => (ctx w).adjacency) encBits
      encJustesenSubdivisionContext budget :=
    hadj.mono_le fun _ => Nat.le_succ _
  have hzero : ComputableInSpace (fun _ => 0) encBits encNat budget :=
    (ComputableInSpace.constZero 0).mono_le fun _ => Nat.zero_le _
  have hc := encJustesenSourceContext_mk_budget hadj' hzero hzero
  have hreg := SourceRoundLoop.start_budget encJustesenSourceContext hc
    (encJustesenSourceContext_size_budget hc)
  have hsize (w : List Bool) : (ctx w).size =
      (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount :=
    configurationJustesenSourceContext_size ntm c w 0 0 0
  have hpos (w : List Bool) :
      0 < (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount :=
    Nat.zero_lt_of_lt (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).1
  obtain ⟨R, L, d, hR⟩ :=
    configurationJustesenSourceLoop_exists_routines ntm c ctx (fun w => (ctx w).size) hreg
      (fun w => ⟨⟨0, Nat.two_pow_pos _⟩, ⟨0, hpos w⟩, ⟨0, hpos w⟩, rfl, (hsize w).le⟩)
  refine ⟨R, L, d, fun w => ⟨(hR w).1, (hR w).2, ?_⟩⟩
  exact configurationJustesenSourceLoop_acceptCount_eq_one ntm c R w (hR w).2
    ⟨0, Nat.two_pow_pos _⟩ ⟨0, hpos w⟩ ⟨0, hpos w⟩ rfl (hsize w)

-- With no fuel, no accepting native occurrence can record any selector list.
example {k : ℕ} {State : Type} [Fintype State] {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (baseline : JustesenSourceContext) (fuel : ℕ)
    (contextOf : α → JustesenSourceContext)
    (R : Routines (justesenSourceLoop ntm c baseline fuel)
      (fun a => (justesenSourceLoop ntm c (contextOf a) 0).init) enc S)
    (a : α) (bits : List Bool) :
    ¬ ∃ indices final,
      Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (enc a)) indices =
        some (bits, final) ∧ final.Halted ∧ final.output = [true] := by
  rintro ⟨indices, final, hr, hh, hout⟩
  obtain ⟨verdict, _, hret⟩ :=
    (justesenSourceLoop_native_firstHalting_accept_iff ntm c R a bits).mp
      ⟨indices, ⟨final, hr, hh, hout⟩, fun other ⟨_, hother, hhalt, _⟩ =>
        Native.eq_occurrences_of_replayChoices R.I R.P R.F R.C hother hr hhalt hh⟩
  rw [justesenSourceLoop_run_zero] at hret
  cases hret

-- Only one selector list can yield an accepting native occurrence and source verdict.
example {k : ℕ} {State : Type} [Fintype State] {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (baseline : JustesenSourceContext) (fuel : ℕ)
    (contextOf : α → JustesenSourceContext) (limitOf : α → ℕ)
    (R : Routines (justesenSourceLoop ntm c baseline fuel)
      (fun a => (justesenSourceLoop ntm c (contextOf a) (limitOf a)).init) enc S)
    (a : α) :
    let w := enc a
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
      contextOf a =
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩ →
      limitOf a = n →
      let edge := fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true
      let M := justesenSourceLoop ntm c (contextOf a) n
      ∃! bits, ∃ verdict, M.run w bits = .inr (some verdict) ∧
        (∃! indices, ∃ final,
          Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg w) indices =
            some (bits, final) ∧ final.Halted ∧ final.output = [true]) ∧
        match verdict with
        | .bad radius =>
          (∀ j < radius, ∃! transcript, Passes edge source j transcript) ∧
            ¬ (∃! transcript, Passes edge source radius transcript)
        | .decided hit =>
          (∀ radius, ∃! transcript, Passes edge source radius transcript) ∧
            (hit = true ↔ Relation.ReflTransGen edge source target) := by
  intro w I n seed source target hcontext hlimit edge M
  obtain ⟨bits, ⟨verdict, hfirst, hresult⟩, hunique⟩ :=
    configurationJustesenSourceLoop_existsUnique_firstHalting ntm c w seed source target
  have hspec := configurationJustesenSourceLoop_correct ntm c w seed source target
    bits verdict hfirst hresult
  have hfirst' : M.FirstHalting w bits M.init := by
    simpa only [M, hcontext] using hfirst
  have hresult' : M.run w bits = .inr (some verdict) := by
    simpa only [M, hcontext] using hresult
  refine ⟨bits, ⟨verdict, hresult', ?_, hspec⟩, ?_⟩
  · apply (justesenSourceLoop_native_firstHalting_accept_iff ntm c R a bits).mpr
    refine ⟨verdict, ?_⟩
    rw [hlimit]
    exact ⟨hfirst', hresult'⟩
  · rintro other ⟨_, _, hother, _⟩
    obtain ⟨v, hf, hr⟩ :=
      (justesenSourceLoop_native_firstHalting_accept_iff ntm c R a other).mp hother
    rw [hlimit, hcontext] at hf hr
    exact hunique other ⟨v, hf, hr⟩

end CslibFrontierTests.STCONJustesenTally
