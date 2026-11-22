/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceRound
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.PolyClock

/-!
# Justesen source loop

The source loop retains the initialized subdivision. It runs the tagged round until it
stabilizes, rejects, exhausts its fuel or finds a tie. On stabilization it calls the
membership tally at the designated target.

## Main definitions

* `Cslib.Complexity.STCON.justesenSourceLoop`: the fixed round and final membership loop.
* `Cslib.Complexity.STCON.encJustesenSourceLoopState`: the existing framed loop encoding.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoopClock`: a uniform selector clock.

## Main results

* `Cslib.Complexity.STCON.justesenSourceLoop_parts_inSpace`: query, transition, halt and
  verdict decoding certificates under the framed loop encoding.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoop_haltsWithin_clock`: every
  branch at a valid initialized entry halts within the common polynomial clock.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoop_length_run_le_log`: every
  encoded prefix state, including rejection, has logarithmic length.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoop_exists_routines`: compile the
  loop on the original encoded input with logarithmic workspace and polynomial time.
* `Cslib.Complexity.STCON.justesenSourceLoop_native_firstHalting_accept_iff`: a
  first-halting selector list returning a verdict has one accepting native occurrence.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoop_correct`: a returned verdict
  gives the first nonunique radius or the correct subdivision reachability answer.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoop_existsUnique_firstHalting`:
  a full-fuel loop has exactly one first-halting selector list returning a verdict.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoop_acceptCount_eq_one`:
  the compiled full-fuel loop has one accepting branch at any sufficient native clock.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.DoubleCounting
open _root_.Turing _root_.Turing.DoubleCounting _root_.Turing.NondeterministicQueryMachine
open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace

variable {k : ℕ} {State : Type} [Fintype State]

/-- The concrete round and final tally use the existing loop state sum. -/
abbrev JustesenSourceLoopState :=
  SourceRoundLoop.State JustesenSourceContext JustesenRetainedSourceRoundState
    (MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState)

/-- Frame the suspended loop registers and the active round or membership state. -/
@[expose] def encJustesenSourceLoopState : JustesenSourceLoopState ↪ List Bool :=
  SourceRoundLoop.encState encJustesenSourceContext encJustesenRetainedSourceRoundState
    (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)

/-- Run the concrete retained round and final membership callback on the original input. -/
@[expose] noncomputable def justesenSourceLoop
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (context : JustesenSourceContext) (limit : ℕ) :
    NondeterministicQueryMachine JustesenSourceLoopState :=
  let initial := SourceRoundLoop.start context limit
  SourceRoundLoop.machine initial (justesenRetainedSourceRound ntm c initial)
    justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply
    (justesenSourceMembershipMachine ntm c) justesenSourceMembershipStart
    MembershipTally.retainedReply

/-- Query, step, halt and decode the source loop in workspace linear in the encoded argument. -/
theorem justesenSourceLoop_parts_inSpace (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (context : JustesenSourceContext) (limit : ℕ) :
    let E := encJustesenSourceLoopState
    let encStep := encPair E encReadChoice
    let M := justesenSourceLoop ntm c context limit
    ComputableInSpace M.query E encNat (fun s => (E s).length) ∧
      ComputableInSpace M.next encStep E (fun p => (encStep p).length) ∧
      ComputableInSpace M.halted E encBool (fun s => (E s).length) ∧
      ComputableInSpace SourceRoundLoop.reply E (encOption SourceRoundLoop.encVerdict)
        (fun s => (E s).length) := by
  intro E encStep M
  let encRound := encJustesenRetainedSourceRoundState
  let encMember := MembershipTally.encRetainedState encJustesenSubdivisionContext
    encJustesenSubdivisionState
  let initial := SourceRoundLoop.start context limit
  let round := justesenRetainedSourceRound ntm c initial
  let member := justesenSourceMembershipMachine ntm c
  obtain ⟨hrq, hrn, hrh, hrr⟩ := justesenRetainedSourceRound_parts_inSpace ntm c initial
  obtain ⟨hq, hn, hh, hr⟩ := justesenSourceMembershipMachine_parts_inSpace ntm c
  exact SourceRoundLoop.parts_inSpace encJustesenSourceContext encRound encMember
    initial round justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply
    member justesenSourceMembershipStart MembershipTally.retainedReply
    justesenRetainedSourceRoundEntry_inSpace justesenSourceMembershipStart_inSpace
    hrr hr hrq hq hrh hh hrn hn

/-- Zero fuel returns no verdict and never starts a callback. -/
theorem justesenSourceLoop_run_zero (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (context : JustesenSourceContext) (w bits : List Bool) :
    (justesenSourceLoop ntm c context 0).run w bits = .inr none := by
  let M := justesenSourceLoop ntm c context 0
  change M.replay w bits M.init = .inr none
  rw [M.replay_of_halted w (by rfl)]
  rfl

/-- Re-entry changes the retained context and loop limit of the fixed source-loop machine. -/
theorem justesenSourceLoop_withInit (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (context next : JustesenSourceContext) (limit nextLimit : ℕ) :
    (justesenSourceLoop ntm c context limit).withInit
      (justesenSourceLoop ntm c next nextLimit).init =
      justesenSourceLoop ntm c next nextLimit :=
  SourceRoundLoop.machine_withInit _ _ _ justesenRetainedSourceRoundEntry
    justesenRetainedSourceRoundReply _ justesenSourceMembershipStart MembershipTally.retainedReply

/-- Charge at most one round per vertex and one final tally, including the return selectors. -/
noncomputable def configurationJustesenSourceLoopClock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : ℕ :=
  let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
  n * (configurationJustesenRetainedSourceRoundClock ntm c w + 1) +
    configurationJustesenMembershipTallyClock ntm c w + 1

/-- The source-loop clock is polynomial in the length of the original input. -/
theorem configurationJustesenSourceLoopClock_polyBounded
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenSourceLoopClock ntm c) :=
  (((configurationSubdivisionVertexCount_polyBounded ntm c).mul
    ((configurationJustesenRetainedSourceRoundClock_polyBounded ntm c).add (.const 1))).add
    (configurationJustesenMembershipTallyClock_polyBounded ntm c)).add (.const 1)

private theorem justesenSourceLoop_closed
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (context : JustesenSourceContext)
    (limit : ℕ) (w : List Bool) :
    SourceRoundLoop.Closed (justesenRetainedSourceRound ntm c (SourceRoundLoop.start context limit))
      justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply w
      (SourceRoundLoop.Admissible context context.size limit) :=
  SourceRoundLoop.retainedRound_admissible_closed JustesenSourceContext.size
    JustesenSourceContext.sourceID (justesenRoundCallback ntm c)
    (fun ctx => justesenRoundCallbackStart ctx.adjacency) justesenRoundCallbackReply context limit w

/-- Every source-loop branch halts within the common clock, including rejection and limits
smaller than the subdivision size. -/
theorem configurationJustesenSourceLoop_haltsWithin_clock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
      (limit : ℕ), limit ≤ n →
      let context : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      (justesenSourceLoop ntm c context limit).HaltsWithin w
        (configurationJustesenSourceLoopClock ntm c w) := by
  intro I n seed source target limit hlimit context
  obtain ⟨_, hround⟩ := configurationJustesenRetainedSourceRound_bounds ntm c
  obtain ⟨_, hmember⟩ := justesenSourceMembership_bounds ntm c
  let initial := SourceRoundLoop.start context limit
  let round := justesenRetainedSourceRound ntm c initial
  let member := justesenSourceMembershipMachine ntm c
  let roundClock := configurationJustesenRetainedSourceRoundClock ntm c w
  let memberClock := configurationJustesenMembershipTallyClock ntm c w
  have hclosed := justesenSourceLoop_closed ntm c context limit w
  have hrun := SourceRoundLoop.haltsWithin initial round justesenRetainedSourceRoundEntry
    justesenRetainedSourceRoundReply member justesenSourceMembershipStart
    MembershipTally.retainedReply w _
    (SourceRoundLoop.start_admissible context context.size limit) hclosed roundClock memberClock
    (fun r hr => by
      rw [justesenRetainedSourceRound_withInit]
      exact (hround w seed source target limit hlimit r hr).1)
    (fun r hr => (hmember w seed source target limit hlimit r hr).1)
  refine HaltsWithin.mono (justesenSourceLoop ntm c context limit) w hrun ?_
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_right (roundClock + 1) hlimit) memberClock) 1

/-- At valid initialized entries, every prefix of the concrete source loop has logarithmic
encoded length. The bound includes the retained registers and either suspended call. -/
theorem configurationJustesenSourceLoop_length_run_le_log
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
        (limit : ℕ), limit ≤ n →
        let context : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        let M := justesenSourceLoop ntm c context limit
        ∀ bits, (encJustesenSourceLoopState (M.run w bits)).length ≤
          C * (Nat.log2 w.length + 1) := by
  obtain ⟨A, hround⟩ := configurationJustesenRetainedSourceRound_bounds ntm c
  obtain ⟨B, henvelope⟩ := configurationJustesenRetainedSourceRound_envelopes_le_log ntm c
  obtain ⟨D, hmember⟩ := justesenSourceMembership_bounds ntm c
  obtain ⟨E, hsize⟩ := length_configurationSubdivisionVertexCount_le_log ntm c
  refine ⟨3 * B + A + D + E + 4, fun w => ?_⟩
  intro I n seed source target limit hlimit context M bits
  let b := Nat.log2 w.length + 1
  let initial := SourceRoundLoop.start context limit
  let round := justesenRetainedSourceRound ntm c initial
  let member := justesenSourceMembershipMachine ntm c
  have hctx : context.size = n :=
    configurationJustesenSourceContext_size ntm c w seed.val source.val target.val
  obtain ⟨hreg, hroundSize⟩ := henvelope w seed source target limit hlimit
  have hlength := SourceRoundLoop.length_run_le initial round justesenRetainedSourceRoundEntry
    justesenRetainedSourceRoundReply member justesenSourceMembershipStart
    MembershipTally.retainedReply w encJustesenSourceContext encJustesenRetainedSourceRoundState
    (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)
    _ (SourceRoundLoop.start_admissible context context.size limit)
    (justesenSourceLoop_closed ntm c context limit w) (B * b) (B * b + A * b) (D * b)
    (fun r hr => by
      have h := SourceRoundLoop.length_encRegisters_le encJustesenSourceContext hr
      rw [hctx] at h
      exact h.trans hreg)
    (fun r hr choices => by
      rw [← run_withInit, justesenRetainedSourceRound_withInit]
      exact ((hround w seed source target limit hlimit r hr).2 choices).trans
        (hroundSize (A * b)))
    (fun r hr => (hmember w seed source target limit hlimit r hr).2) bits
  refine hlength.trans ?_
  simp only [initial, SourceRoundLoop.start, Nat.add_zero, Nat.add_mul, Nat.mul_assoc]
  have hfuel : (encNat limit).length ≤ E * b :=
    (length_encNat_mono hlimit).trans (hsize w)
  have hb : 1 ≤ b := Nat.succ_le_succ (Nat.zero_le _)
  change 2 * (B * b) + max (B * b + A * b) (D * b) + (encNat limit).length + 4 ≤
    3 * (B * b) + A * b + D * b + E * b + 4 * b
  omega

/-- Compile one native source loop from a producer of valid initial registers. The fixed
machine runs on the original encoded input, with a logarithmic workspace bound and a
polynomial native time bound. -/
theorem configurationJustesenSourceLoop_exists_routines
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) {α : Type} {enc : α ↪ List Bool}
    (contextOf : α → JustesenSourceContext) (limitOf : α → ℕ)
    (hregisters : ComputableInSpace (fun a => SourceRoundLoop.start (contextOf a) (limitOf a))
      enc (SourceRoundLoop.encRegisters encJustesenSourceContext)
      (fun a => Nat.log2 (enc a).length + 1))
    (hvalid : ∀ a,
      let w := enc a
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∃ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
        contextOf a =
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩ ∧
        limitOf a ≤ n) :
    let baseline : JustesenSourceContext :=
      ⟨configurationJustesenSubdivisionContext ntm c [] 0, 0, 0⟩
    let M := justesenSourceLoop ntm c baseline 0
    let entry := fun a => (justesenSourceLoop ntm c (contextOf a) (limitOf a)).init
    ∃ R : Routines M entry enc (fun a => Nat.log2 (enc a).length + 1),
      ∃ L d, ∀ a, R.machine.RunsInSpace (enc a) (L * (Nat.log2 (enc a).length + 1)) ∧
        R.machine.RunsInTime (enc a) (polyClock d (enc a).length) := by
  intro baseline M entry
  let initial := SourceRoundLoop.start baseline 0
  let round := justesenRetainedSourceRound ntm c initial
  let member := justesenSourceMembershipMachine ntm c
  let encMember := MembershipTally.encRetainedState encJustesenSubdivisionContext
    encJustesenSubdivisionState
  obtain ⟨hrq, hrn, hrh, hrr⟩ := justesenRetainedSourceRound_parts_inSpace ntm c initial
  obtain ⟨hmq, hmn, hmh, hmr⟩ := justesenSourceMembershipMachine_parts_inSpace ntm c
  obtain ⟨C, hspace⟩ := configurationJustesenSourceLoop_length_run_le_log ntm c
  have hstates : ∀ a bits, (encJustesenSourceLoopState
      ((justesenSourceLoop ntm c (contextOf a) (limitOf a)).run (enc a) bits)).length ≤
        C * (Nat.log2 (enc a).length + 1) := by
    intro a bits
    obtain ⟨seed, source, target, hctx, hlimit⟩ := hvalid a
    rw [hctx]
    exact hspace (enc a) seed source target (limitOf a) hlimit bits
  obtain ⟨R⟩ : Nonempty (Routines M entry enc (fun a => Nat.log2 (enc a).length + 1)) :=
    SourceRoundLoop.exists_routines encJustesenSourceContext encJustesenRetainedSourceRoundState
      encMember initial round justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply
      member justesenSourceMembershipStart MembershipTally.retainedReply enc _
      (fun a => SourceRoundLoop.start (contextOf a) (limitOf a)) hregisters (fun _ => le_rfl)
      justesenRetainedSourceRoundEntry_inSpace justesenSourceMembershipStart_inSpace hrr hmr
      hrq hmq hrh hmh hrn hmn ⟨C, hstates⟩
  refine ⟨R, R.exists_logSpace_polyClock
    (time := fun a => configurationJustesenSourceLoopClock ntm c (enc a)) ?_⟩
  intro a
  obtain ⟨seed, source, target, hctx, hlimit⟩ := hvalid a
  dsimp only [M, entry]
  rw [justesenSourceLoop_withInit, hctx]
  exact configurationJustesenSourceLoop_haltsWithin_clock ntm c (enc a)
    seed source target (limitOf a) hlimit

/-- For each selector list, an accepting native occurrence is unique exactly when the
re-entered source loop first halts on that list and returns a verdict. A negative verdict
is a successful return. -/
theorem justesenSourceLoop_native_firstHalting_accept_iff
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) {α : Type} {enc : α ↪ List Bool}
    {S : α → ℕ} {contextOf : α → JustesenSourceContext} {limitOf : α → ℕ}
    {baseline : JustesenSourceContext} {fuel : ℕ}
    (R : Routines (justesenSourceLoop ntm c baseline fuel)
      (fun a => (justesenSourceLoop ntm c (contextOf a) (limitOf a)).init) enc S)
    (a : α) (bits : List Bool) :
    (∃! indices, ∃ final,
      Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (enc a)) indices =
        some (bits, final) ∧ final.Halted ∧ final.output = [true]) ↔
      ∃ verdict,
        let M := justesenSourceLoop ntm c (contextOf a) (limitOf a)
        M.FirstHalting (enc a) bits M.init ∧ M.run (enc a) bits = .inr (some verdict) := by
  let initial := SourceRoundLoop.start baseline fuel
  let registers (a : α) := SourceRoundLoop.start (contextOf a) (limitOf a)
  let round := justesenRetainedSourceRound ntm c initial
  let member := justesenSourceMembershipMachine ntm c
  rw [SourceRoundLoop.native_firstHalting_accept_iff initial round justesenRetainedSourceRoundEntry
    justesenRetainedSourceRoundReply member justesenSourceMembershipStart
    MembershipTally.retainedReply registers R a bits]
  apply exists_congr
  intro verdict
  exact (SourceRoundLoop.firstHalting_iff_replayRounds (registers a) round
    justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply member
    justesenSourceMembershipStart MembershipTally.retainedReply (enc a) bits verdict).symm

/-- A completed full-fuel scan returns the first nonunique radius, or a reachability verdict
with a unique passing transcript at every radius. -/
theorem configurationJustesenSourceLoop_correct
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
      let edge := fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true
      let context : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let M := justesenSourceLoop ntm c context n
      ∀ (bits : List Bool) (verdict : ControllerVerdict), M.FirstHalting w bits M.init →
        M.run w bits = .inr (some verdict) →
        verdict.Correct edge source target := by
  intro I n seed source target edge context M bits verdict hfirst hresult
  let initial := SourceRoundLoop.start context n
  let round := justesenRetainedSourceRound ntm c initial
  let member := justesenSourceMembershipMachine ntm c
  have hscan := (SourceRoundLoop.firstHalting_iff_replayRounds initial round
    justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply member
    justesenSourceMembershipStart MembershipTally.retainedReply w bits verdict).mp
      ⟨hfirst, hresult⟩
  have hspec := SourceRoundLoop.replayRounds_correct round justesenRetainedSourceRoundEntry
    justesenRetainedSourceRoundReply member justesenSourceMembershipStart
    MembershipTally.retainedReply w (r := edge) (source := source) (target := target) context
    (by
      intro fuel radius hpass selectors update rest hreply
      let r : SourceRoundLoop.Registers JustesenSourceContext :=
        ⟨context, fuel, radius, expected edge source radius⟩
      obtain ⟨callBits, _, hhalt, hret⟩ :=
        (round.readReply_iff justesenRetainedSourceRoundReply w selectors
          (justesenRetainedSourceRoundEntry r) update rest).mp hreply
      rw [← firstHalting_withInit, justesenRetainedSourceRound_withInit] at hhalt
      rw [← run_withInit, justesenRetainedSourceRound_withInit] at hret
      exact configurationJustesenRetainedSourceRound_correct ntm c w
        seed source target fuel radius hpass callBits update hhalt hret)
    (by
      intro fuel radius _ selectors hit rest hreply
      exact (justesenSourceMembership_readReply_correct ntm c w seed source target
        fuel radius selectors hit rest hreply).trans mem_round.symm)
    hscan
  exact hspec

/-- Every valid full-fuel source scan has exactly one first-halting selector list
that returns a verdict. -/
theorem configurationJustesenSourceLoop_existsUnique_firstHalting
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
      let context : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let M := justesenSourceLoop ntm c context n
      ∃! bits, ∃ verdict, M.FirstHalting w bits M.init ∧ M.run w bits = .inr (some verdict) := by
  intro I n seed source target context M
  let edge := fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true
  let initial := SourceRoundLoop.start context n
  let round := justesenRetainedSourceRound ntm c initial
  let member := justesenSourceMembershipMachine ntm c
  let P := JustesenSourceRoundExact context edge source
  have hinit (r : SourceRoundLoop.Registers JustesenSourceContext) :
      round.withInit (justesenRetainedSourceRoundEntry r) =
        justesenRetainedSourceRound ntm c r :=
    justesenRetainedSourceRound_withInit ntm c initial r
  have hnormalized (r : SourceRoundLoop.Registers JustesenSourceContext) (hr : P r) :
      r = ⟨context, r.fuel, r.radius, expected edge source r.radius⟩ := by
    obtain ⟨hctx, _, _, htally, _⟩ := hr
    rw [← hctx, ← htally]
  have hclosed : SourceRoundLoop.Closed round justesenRetainedSourceRoundEntry
      justesenRetainedSourceRoundReply w P := by
    intro r hr _ bits update hfirst hreply hbad hcount
    rw [← firstHalting_withInit, hinit r] at hfirst
    rw [← run_withInit, hinit r] at hreply
    exact configurationJustesenRetainedSourceRound_exact_advance ntm c w
      seed source target r hr bits update hfirst hreply hbad hcount
  have hround (r : SourceRoundLoop.Registers JustesenSourceContext) (hr : P r) :
      ∃! bits, ∃ update, round.FirstHalting w bits (justesenRetainedSourceRoundEntry r) ∧
        justesenRetainedSourceRoundReply
          (round.replay w bits (justesenRetainedSourceRoundEntry r)) = some update := by
    have h := configurationJustesenRetainedSourceRound_existsUnique_firstHalting ntm c w
      seed source target r.fuel r.radius (hr.2.2.2.2 r.radius le_rfl)
    dsimp only at h
    rw [← hnormalized r hr, ← hinit r] at h
    simpa only [firstHalting_withInit, run_withInit, init_withInit] using h
  have hmember (r : SourceRoundLoop.Registers JustesenSourceContext) (hr : P r) :
      ∃! bits, member.FirstHalting w bits (justesenSourceMembershipStart r) ∧
        (MembershipTally.retainedReply
          (member.replay w bits (justesenSourceMembershipStart r))).isSome := by
    have h := justesenSourceMembership_existsUnique_firstHalting ntm c w
      seed source target r.fuel r.radius (hr.2.2.2.2 r.radius le_rfl)
    dsimp only at h
    rw [← hnormalized r hr] at h
    exact h
  have hp : P initial := justesenSourceRoundExact_start context edge source
  obtain ⟨bits, verdict, hfirst, hreply⟩ := SourceRoundLoop.exists_successful_firstHalting
    initial round justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply member
    justesenSourceMembershipStart MembershipTally.retainedReply w P hp (fun _ hr => hr.2.2.1)
    hclosed (fun r hr => (hround r hr).exists) (fun r hr => by
      obtain ⟨choices, hfirst, hsome⟩ := (hmember r hr).exists
      obtain ⟨hit, hhit⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨choices, hit, hfirst, hhit⟩)
  have hunique := SourceRoundLoop.subsingleton_successful_firstHalting
    initial round justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply member
    justesenSourceMembershipStart MembershipTally.retainedReply w P hp hclosed
    (fun r hr _ _ hl _ hr' => by
      obtain ⟨left, hleft⟩ := Option.isSome_iff_exists.mp hl.2
      obtain ⟨right, hright⟩ := Option.isSome_iff_exists.mp hr'.2
      exact (hround r hr).unique ⟨left, hl.1, hleft⟩ ⟨right, hr'.1, hright⟩)
    (fun r hr _ _ hl _ hr' => (hmember r hr).unique hl hr')
  refine ⟨bits, ⟨verdict, hfirst, hreply⟩, ?_⟩
  rintro other ⟨result, hother, hret⟩
  have haccept := SourceRoundLoop.machine_accept_iff initial round
    justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply member
    justesenSourceMembershipStart MembershipTally.retainedReply
  exact hunique ⟨hother, (haccept _).mpr ⟨result, hret⟩⟩
    ⟨hfirst, (haccept _).mpr ⟨verdict, hreply⟩⟩

/-- Every valid full-fuel source scan has a complete first-halting trace with a verdict. -/
theorem configurationJustesenSourceLoop_exists_firstHalting
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
      let context : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let M := justesenSourceLoop ntm c context n
      ∃ bits verdict, M.FirstHalting w bits M.init ∧ M.run w bits = .inr (some verdict) := by
  intro I n seed source target
  exact (configurationJustesenSourceLoop_existsUnique_firstHalting
    ntm c w seed source target).exists

/-- A first-halting run returns a reply exactly when its terminal state carries a verdict. -/
theorem justesenSourceLoop_firstHalting_reply_iff
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (context : JustesenSourceContext)
    (fuel : ℕ) (w bits : List Bool) :
    let M := justesenSourceLoop ntm c context fuel
    M.FirstHalting w bits M.init ∧ (SourceRoundLoop.reply (M.run w bits)).isSome ↔
      ∃ verdict, M.FirstHalting w bits M.init ∧ M.run w bits = .inr (some verdict) := by
  intro M
  let initial := SourceRoundLoop.start context fuel
  have haccept := SourceRoundLoop.machine_accept_iff initial
    (justesenRetainedSourceRound ntm c initial)
    justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply
    (justesenSourceMembershipMachine ntm c) justesenSourceMembershipStart
    MembershipTally.retainedReply (M.run w bits)
  exact (and_congr_right fun _ => haccept).trans exists_and_left.symm

/-- At any sufficient native clock, the compiled full-fuel source loop has exactly
one accepting occurrence across all selector lists. -/
theorem configurationJustesenSourceLoop_acceptCount_eq_one
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) {α : Type} {enc : α ↪ List Bool}
    {S : α → ℕ} {contextOf : α → JustesenSourceContext} {limitOf : α → ℕ}
    {baseline : JustesenSourceContext} {fuel : ℕ}
    (R : Routines (justesenSourceLoop ntm c baseline fuel)
      (fun a => (justesenSourceLoop ntm c (contextOf a) (limitOf a)).init) enc S)
    (a : α) {clock : ℕ} (hclock : R.machine.RunsInTime (enc a) clock) :
    let w := enc a
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
      contextOf a =
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩ →
      limitOf a = n →
      (Native.countingMachine R.I R.P R.F R.C).acceptCount clock (R.machine.initCfg w) = 1 := by
  intro w I n seed source target hcontext hlimit
  rw [R.acceptCount_eq_one_iff a hclock]
  refine (existsUnique_congr fun bits => ?_).mpr
    (configurationJustesenSourceLoop_existsUnique_firstHalting ntm c w seed source target)
  let entered := (justesenSourceLoop ntm c baseline fuel).withInit
    (justesenSourceLoop ntm c (contextOf a) (limitOf a)).init
  change (entered.FirstHalting w bits entered.init ∧
    entered.accept (entered.run w bits) = true) ↔ _
  dsimp only [entered]
  rw [justesenSourceLoop_withInit, hcontext, hlimit]
  let context : JustesenSourceContext :=
    ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
  exact justesenSourceLoop_firstHalting_reply_iff ntm c context n w bits

end Cslib.Complexity.STCON
