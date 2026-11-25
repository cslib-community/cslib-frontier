/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenRoundCallback.Resource
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Retained
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Retained Justesen source round

One source round retains the initialized subdivision and the source-loop endpoints. Its
tagged edge and membership callbacks use the original input and the current round registers.

## Main definitions

* `Cslib.Complexity.STCON.justesenRetainedSourceRound`: the fixed round with tagged callbacks.
* `Cslib.Complexity.STCON.justesenRetainedSourceRoundEntry`: initialize it from loop registers.
* `Cslib.Complexity.STCON.justesenRetainedSourceRoundReply`: read its optional round update.
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRoundClock`: a common selector clock.

## Main results

* `Cslib.Complexity.STCON.justesenRetainedSourceRoundEntry_inSpace`: linear workspace for entry.
* `Cslib.Complexity.STCON.justesenRetainedSourceRound_parts_inSpace`: linear workspace for
  query, transition, halt and reply on the encoded round state.
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRound_correct`: a successful
  round at exact totals returns the next tally and the tie flag.
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRound_existsUnique_firstHalting`:
  at exact totals, a unique membership transcript gives one complete successful round trace.
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRound_bounds`: the clock and
  uniform state envelope hold at every admissible round entry.
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRound_envelopes_le_log`:
  the round and loop register envelopes are logarithmic apart from the charged callback.
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRound_exact_advance`:
  a completed, untied growing round preserves the exact tally and positive fuel.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.DoubleCounting
open _root_.Turing _root_.Turing.DoubleCounting _root_.Turing.NondeterministicQueryMachine
open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace

/-- The round retains the same source context as its enclosing loop. -/
abbrev JustesenRetainedSourceRoundState :=
  JustesenSourceContext × SourceRound.MachineState JustesenRoundCallbackState

/-- Frame the retained context and the existing tagged round state. -/
@[expose] def encJustesenRetainedSourceRoundState :
    JustesenRetainedSourceRoundState ↪ List Bool :=
  encPair encJustesenSourceContext
    (SourceRound.encMachineState JustesenRoundCallbackState encJustesenRoundCallbackState)

/-- Use each entry's original subdivision when starting either tagged callback. -/
@[expose] noncomputable def justesenRetainedSourceRound {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r : SourceRoundLoop.Registers JustesenSourceContext) :
    NondeterministicQueryMachine JustesenRetainedSourceRoundState :=
  SourceRoundLoop.retainedRound JustesenSourceContext.size JustesenSourceContext.sourceID
    (justesenRoundCallback ntm c) (fun ctx => justesenRoundCallbackStart ctx.adjacency)
    justesenRoundCallbackReply r

/-- Re-enter the round at the current source-loop registers. -/
@[expose] def justesenRetainedSourceRoundEntry
    (r : SourceRoundLoop.Registers JustesenSourceContext) : JustesenRetainedSourceRoundState :=
  SourceRoundLoop.retainedRoundEntry JustesenSourceContext.size JustesenSourceContext.sourceID r

/-- Read a completed update, with a tie distinct from callback rejection. -/
@[expose] def justesenRetainedSourceRoundReply
    (q : JustesenRetainedSourceRoundState) : Option RoundUpdate :=
  SourceRound.answer q.2

/-- The round entry is computable in linear workspace in the encoded loop registers. -/
theorem justesenRetainedSourceRoundEntry_inSpace :
    let E := SourceRoundLoop.encRegisters encJustesenSourceContext
    ComputableInSpace justesenRetainedSourceRoundEntry E encJustesenRetainedSourceRoundState
      (fun r => (E r).length) := by
  have hctx := budget_id (enc := encJustesenSourceContext) (.refl _)
  exact SourceRoundLoop.retainedRoundEntry_inSpace JustesenSourceContext.size
    JustesenSourceContext.sourceID encJustesenSourceContext encJustesenRoundCallbackState
    (encJustesenSourceContext_size_budget hctx) (encJustesenSourceContext_sourceID_budget hctx)

/-- The retained round inherits scalar operations and its context-dependent transition. -/
theorem justesenRetainedSourceRound_parts_inSpace {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r : SourceRoundLoop.Registers JustesenSourceContext) :
    let M := justesenRetainedSourceRound ntm c r
    let E := encJustesenRetainedSourceRoundState
    let encStep := encPair E encReadChoice
    ComputableInSpace M.query E encNat (fun q => (E q).length) ∧
      ComputableInSpace M.next encStep E (fun p => (encStep p).length) ∧
      ComputableInSpace M.halted E encBool (fun q => (E q).length) ∧
      ComputableInSpace justesenRetainedSourceRoundReply E (encOption encRoundUpdate)
        (fun q => (E q).length) := by
  intro M E encStep
  let C := encJustesenRoundCallbackState
  let N := justesenRoundCallback ntm c
  let ctx :=
    SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r
  let start := justesenRoundCallbackStart r.context.adjacency
  obtain ⟨hq, hn, hh, hf⟩ := justesenRoundCallback_parts_inSpace ntm c
  have hsnd := snd encJustesenSourceContext (SourceRound.encMachineState _ C)
  have hentry := budget_comp_linear justesenRoundCallbackStart_inSpace
    (budget_prod (encJustesenSourceContext_adjacency_budget
      (fst encJustesenSourceContext SourceRound.encState))
      (snd encJustesenSourceContext SourceRound.encState))
  exact ⟨(budget_comp_linear
      (SourceRound.machine_query_inSpace C ctx N start justesenRoundCallbackReply hq) hsnd : _),
    (SourceRoundLoop.retainedRound_next_inSpace JustesenSourceContext.size
      JustesenSourceContext.sourceID N (fun k => justesenRoundCallbackStart k.adjacency)
      justesenRoundCallbackReply r encJustesenSourceContext C hentry hf hh hn : _),
    (budget_comp_linear
      (SourceRound.machine_halted_inSpace C ctx N start justesenRoundCallbackReply) hsnd : _),
    (budget_comp_linear (SourceRound.answer_inSpace C) hsnd : _)⟩

private theorem justesenRetainedSourceRound_firstHalting_iff_scalar
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r : SourceRoundLoop.Registers JustesenSourceContext) (w bits : List Bool)
    (update : RoundUpdate) :
    let M := justesenRetainedSourceRound ntm c r
    let ctx :=
      SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r
    let scalar := SourceRound.machine ctx (justesenRoundCallback ntm c)
      (justesenRoundCallbackStart r.context.adjacency) justesenRoundCallbackReply
    M.FirstHalting w bits M.init ∧ justesenRetainedSourceRoundReply (M.run w bits) = some update ↔
      scalar.FirstHalting w bits scalar.init ∧
        SourceRound.answer (scalar.run w bits) = some update := by
  intro M ctx scalar
  change (SourceRoundLoop.retainedRound _ _ _ _ _ r).FirstHalting w bits
      (SourceRoundLoop.retainedRoundEntry _ _ r) ∧
    justesenRetainedSourceRoundReply
      ((SourceRoundLoop.retainedRound _ _ _ _ _ r).run w bits) = some update ↔ _
  rw [SourceRoundLoop.retainedRound_firstHalting, SourceRoundLoop.retainedRound_run]
  rfl

/-- The retained round consumes exactly the selectors of the corresponding scalar replay. -/
theorem justesenRetainedSourceRound_firstHalting_iff_replayScan
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r : SourceRoundLoop.Registers JustesenSourceContext) (w bits : List Bool)
    (update : RoundUpdate) :
    let M := justesenRetainedSourceRound ntm c r
    let ctx :=
      SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r
    M.FirstHalting w bits M.init ∧ justesenRetainedSourceRoundReply (M.run w bits) = some update ↔
      SourceRound.replayScan ctx (justesenRoundCallback ntm c)
        (justesenRoundCallbackStart r.context.adjacency) justesenRoundCallbackReply w bits =
          some (update, []) :=
  (justesenRetainedSourceRound_firstHalting_iff_scalar ntm c r w bits update).trans
    (SourceRound.firstHalting_iff_replayScan _ _ _ _ w bits update)

private theorem initializedRoundContext {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (seed source target fuel radius : ℕ) (tally : Tally) :
    let ctx : JustesenSourceContext :=
      ⟨configurationJustesenSubdivisionContext ntm c w seed, source, target⟩
    SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID
      ⟨ctx, fuel, radius, tally⟩ =
      ⟨(configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount,
        source, radius, tally⟩ := by
  intro ctx
  simp only [SourceRoundLoop.roundContext, ctx, configurationJustesenSourceContext_size]

/-- At exact totals with a unique passing transcript, every successful retained round returns
the next tally and reports whether the next transcript is unique. -/
theorem configurationJustesenRetainedSourceRound_correct
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
      (fuel radius : ℕ),
      let edge := fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true
      (∃! transcript, Passes edge source radius transcript) →
      let context : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let r : SourceRoundLoop.Registers JustesenSourceContext :=
        ⟨context, fuel, radius, expected edge source radius⟩
      let M := justesenRetainedSourceRound ntm c r
      ∀ (bits : List Bool) (update : RoundUpdate), M.FirstHalting w bits M.init →
        justesenRetainedSourceRoundReply (M.run w bits) = some update →
        update.tally = expected edge source (radius + 1) ∧
          (update.bad = false ↔ ∃! transcript, Passes edge source (radius + 1) transcript) := by
  intro I n seed source target fuel radius edge hpass context r M bits update hfirst hreply
  have hscan := (justesenRetainedSourceRound_firstHalting_iff_replayScan ntm c r w bits update).mp
    ⟨hfirst, hreply⟩
  let adj := configurationJustesenSubdivisionContext ntm c w seed.val
  let ctx : SourceRound.Context := ⟨n, source.val, radius, expected edge source radius⟩
  have hctx : SourceRoundLoop.roundContext JustesenSourceContext.size
      JustesenSourceContext.sourceID r = ctx :=
    initializedRoundContext ntm c w seed.val source.val target.val fuel radius _
  rw [hctx] at hscan
  refine SourceRound.replayScan_correct ctx source edge (justesenRoundCallback ntm c)
    (justesenRoundCallbackStart adj) justesenRoundCallbackReply w rfl hpass ?_ ?_ hscan
  · intro u v call hit rest hcall
    rw [(configurationJustesenRoundCallback_readReply_correct ntm c w seed source radius
      (.edge u.val v.val) ⟨u.isLt, v.isLt⟩ call hit rest hcall : hit = _)]
  · intro v call hit rest hcall
    exact (configurationJustesenRoundCallback_readReply_correct ntm c w seed source radius
      (.member v.val) v.isLt call hit rest hcall).trans mem_round.symm

/-- At exact totals, a unique passing membership transcript gives exactly one selector list
that first halts and returns an update from the retained round. A tied update is a return. -/
theorem configurationJustesenRetainedSourceRound_existsUnique_firstHalting
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n) (fuel radius : ℕ),
      let edge := fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true
      (∃! transcript, Passes edge source radius transcript) →
      let context : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let r : SourceRoundLoop.Registers JustesenSourceContext :=
        ⟨context, fuel, radius, expected edge source radius⟩
      let M := justesenRetainedSourceRound ntm c r
      ∃! bits, ∃ update, M.FirstHalting w bits M.init ∧
        justesenRetainedSourceRoundReply (M.run w bits) = some update := by
  intro I n seed source target fuel radius edge hpass context r M
  let ctx : SourceRound.Context := ⟨n, source.val, radius, expected edge source radius⟩
  let N := justesenRoundCallback ntm c
  let start := justesenRoundCallbackStart context.adjacency
  let scalar := SourceRound.machine ctx N start justesenRoundCallbackReply
  have hreq (req : SourceRound.Request) (hv : req.InRange ctx.size) :
      ∃! bits, N.FirstHalting w bits (start ctx req) ∧
        (justesenRoundCallbackReply (N.replay w bits (start ctx req))).isSome :=
    configurationJustesenRoundCallback_existsUnique_firstHalting ntm c w
      seed source radius hpass req hv
  have hunique := SourceRound.subsingleton_successful_firstHalting ctx N start
    justesenRoundCallbackReply w (fun req hv _ hl _ hr => (hreq req hv).unique hl hr)
  obtain ⟨bits, update, hfirst, hanswer⟩ := SourceRound.exists_successful_firstHalting ctx N start
    justesenRoundCallbackReply w (fun req hv => by
      obtain ⟨choices, ⟨hfirst, hsome⟩, _⟩ := hreq req hv
      obtain ⟨hit, hhit⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨choices, hit, hfirst, hhit⟩)
  have hctx : SourceRoundLoop.roundContext JustesenSourceContext.size
      JustesenSourceContext.sourceID r = ctx :=
    initializedRoundContext ntm c w seed.val source.val target.val fuel radius _
  have htransfer (selectors : List Bool) (result : RoundUpdate) :
      M.FirstHalting w selectors M.init ∧
        justesenRetainedSourceRoundReply (M.run w selectors) = some result ↔
      scalar.FirstHalting w selectors scalar.init ∧
        SourceRound.answer (scalar.run w selectors) = some result := by
    have h := justesenRetainedSourceRound_firstHalting_iff_scalar ntm c r w selectors result
    dsimp only at h
    rwa [hctx] at h
  refine ⟨bits, ⟨update, (htransfer bits update).mpr ⟨hfirst, hanswer⟩⟩, ?_⟩
  rintro other ⟨result, hresult⟩
  obtain ⟨hfirst', hanswer'⟩ := (htransfer other result).mp hresult
  exact hunique ⟨hfirst', Option.isSome_iff_exists.mpr ⟨result, hanswer'⟩⟩
    ⟨hfirst, Option.isSome_iff_exists.mpr ⟨update, hanswer⟩⟩

open Cslib.Code.JustesenFamily

variable {k : ℕ} {State : Type} [Fintype State]

/-- Use the same fixed round machine with any new retained context and scalar registers. -/
theorem justesenRetainedSourceRound_withInit
    (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r next : SourceRoundLoop.Registers JustesenSourceContext) :
    (justesenRetainedSourceRound ntm c r).withInit (justesenRetainedSourceRoundEntry next) =
      justesenRetainedSourceRound ntm c next :=
  SourceRoundLoop.retainedRound_withInit JustesenSourceContext.size JustesenSourceContext.sourceID
    (justesenRoundCallback ntm c) (fun ctx => justesenRoundCallbackStart ctx.adjacency)
    justesenRoundCallbackReply r next

/-- Charge round routing and the common tagged callback clock on the original input. -/
noncomputable def configurationJustesenRetainedSourceRoundClock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : ℕ :=
  SourceRound.roundClock
    (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    (configurationJustesenRoundCallbackClock ntm c w)

/-- The retained round's common selector clock is polynomial in the original word length. -/
theorem configurationJustesenRetainedSourceRoundClock_polyBounded
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenRetainedSourceRoundClock ntm c) := by
  growth_poly [configurationSubdivisionVertexCount_polyBounded ntm c,
    configurationJustesenRoundCallbackClock_polyBounded ntm c]

/-- For an initialized subdivision, every admissible round entry shares a selector clock and
an encoded-state envelope. The latter charges the retained context and the scalar round at
the maximum radius and tally allowed by the loop limit. -/
theorem configurationJustesenRetainedSourceRound_bounds
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
        (limit : ℕ), limit ≤ n →
        let context : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        ∀ r, SourceRoundLoop.Admissible context context.size limit r →
          let M := justesenRetainedSourceRound ntm c r
          let D := C * (Nat.log2 w.length + 1)
          M.HaltsWithin w (configurationJustesenRetainedSourceRoundClock ntm c w) ∧
            ∀ bits, (encJustesenRetainedSourceRoundState (M.run w bits)).length ≤
              2 * (encJustesenSourceContext context).length + 1 +
                SourceRound.roundStateBound
                  ⟨n, source.val, limit, ⟨1 + limit * n, n * limit * limit⟩⟩ D := by
  obtain ⟨C, hcallback⟩ := configurationJustesenRoundCallback_bounds ntm c
  refine ⟨C, fun w => ?_⟩
  intro I n seed source target limit hlimit context r hr M D
  have hsize : context.size = n :=
    configurationJustesenSourceContext_size ntm c w seed.val source.val target.val
  obtain ⟨_, hrad, hcount, hsum⟩ := SourceRoundLoop.admissible_caps_le hr hlimit
  rw [hsize] at hcount hsum
  let N := justesenRoundCallback ntm c
  let start := fun k : JustesenSourceContext => justesenRoundCallbackStart k.adjacency
  let clock := configurationJustesenRoundCallbackClock ntm c w
  have hcall (req : SourceRound.Request) (hv : req.InRange r.context.size) :
      let entry := start r.context
        (SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r)
        req
      N.HaltsFrom w entry clock ∧
        ∀ bits, (encJustesenRoundCallbackState (N.replay w bits entry)).length ≤ D := by
    simp only [SourceRoundLoop.roundContext, hr.1, hsize] at hv ⊢
    exact hcallback w seed source r.radius r.tally hrad hcount hsum req hv
  have hhalt := SourceRoundLoop.retainedRound_haltsWithin JustesenSourceContext.size
    JustesenSourceContext.sourceID N start justesenRoundCallbackReply r w clock
    (fun req hv => (hcall req hv).1)
  refine ⟨?_, fun bits => ?_⟩
  · simpa only [M, justesenRetainedSourceRound, N, start, clock, n,
      configurationJustesenRetainedSourceRoundClock, hr.1, hsize] using hhalt
  · refine (SourceRoundLoop.retainedRound_length_run_le JustesenSourceContext.size
      JustesenSourceContext.sourceID N start justesenRoundCallbackReply r encJustesenSourceContext
      encJustesenRoundCallbackState w bits D (fun req hv => (hcall req hv).2)).trans ?_
    simpa only [SourceRoundLoop.retainedRoundStateBound, hr.1, hsize] using
      Nat.add_le_add_left (SourceRoundLoop.roundStateBound_le JustesenSourceContext.size
        JustesenSourceContext.sourceID context limit r hr D)
        (2 * (encJustesenSourceContext context).length + 1)

/-- The round and register envelopes are logarithmic in the input length, with a separate
charge for the suspended callback's encoded state. -/
theorem configurationJustesenRetainedSourceRound_envelopes_le_log
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
        (limit : ℕ), limit ≤ n →
        let context : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        let budget := C * (Nat.log2 w.length + 1)
        SourceRoundLoop.registerStateBound encJustesenSourceContext context n limit ≤ budget ∧
          ∀ D, 2 * (encJustesenSourceContext context).length + 1 +
            SourceRound.roundStateBound ⟨n, source.val, limit, ⟨1 + limit * n, n * limit * limit⟩⟩
              D ≤ budget + D := by
  obtain ⟨A, hA⟩ := length_configurationJustesenSourceContext_le_log ntm c
  obtain ⟨B, hB⟩ := length_configurationSubdivisionVertexCount_le_log ntm c
  refine ⟨2 * A + 432 * B + 369, fun w => ?_⟩
  intro I n seed source target limit hl context budget
  let b := Nat.log2 w.length + 1
  let width := (encNat n).length
  have hctx : (encJustesenSourceContext context).length ≤ A * b := hA w seed source target
  have hn : width ≤ B * b := hB w
  have hs : (encNat source.val).length ≤ width := length_encNat_mono source.isLt.le
  have hk : (encNat limit).length ≤ width := length_encNat_mono hl
  obtain ⟨hcount, hsum⟩ := length_encTally_fields_le_of_caps
    (tally := ⟨1 + limit * n, n * limit * limit⟩) hl le_rfl le_rfl
  change (encNat (1 + limit * n)).length ≤ 2 * width + 2 at hcount
  change (encNat (n * limit * limit)).length ≤ 3 * width at hsum
  have hone : (encNat 1).length = 1 := rfl
  have hreg : SourceRoundLoop.registerStateBound encJustesenSourceContext context n limit ≤
      2 * (encJustesenSourceContext context).length + 11 * width + 8 := by
    rw [SourceRoundLoop.registerStateBound]
    omega
  let round : SourceRound.Context := ⟨n, source.val, limit, ⟨1 + limit * n, n * limit * limit⟩⟩
  have hround : (SourceRound.encContext round).length ≤ 13 * width + 8 := by
    simp only [round, SourceRound.encContext_apply, SourceRound.encContextFields,
      encTally_apply, encTallyFields, length_encPair]
    dsimp only [width] at hs hk hcount hsum ⊢
    omega
  let count := 1 + limit * n + n
  let total := n * limit * limit + n * (limit + 1)
  let V := max count total
  have hcountWidth : (encNat count).length ≤ 3 * width + 3 := by
    have hadd := length_encNat_add_le_add (1 + limit * n) n
    dsimp only [width, count] at hcount ⊢
    omega
  have htotalWidth : (encNat total).length ≤ 5 * width + 3 := by
    have hadd := length_encNat_add_le_add limit 1
    have hmul := length_encNat_mul_le n (limit + 1)
    have htotal := length_encNat_add_le_add (n * limit * limit) (n * (limit + 1))
    dsimp only [width, total] at hk hsum ⊢
    omega
  have hV : (encNat V).length ≤ 5 * width + 3 := by
    rcases le_total count total with h | h
    · simpa only [V, max_eq_right h] using htotalWidth
    · rw [show V = count from max_eq_left h]
      omega
  have hlogN : Nat.log2 n ≤ width := (Nat.log2_le_size n).trans_eq (length_encNat_eq_size n).symm
  have hlogV : Nat.log2 (V * V) ≤ 10 * width + 6 := by
    have hlog := Nat.log2_le_size (V * V)
    rw [← length_encNat_eq_size] at hlog
    have hmul := length_encNat_mul_le V V
    omega
  have hscalar (D : ℕ) : SourceRound.roundStateBound round D ≤ 432 * width + 368 + D := by
    change 2 * (6 * (SourceRound.encContext round).length + 18 * (Nat.log2 n + 1) +
      12 * (Nat.log2 (V * V) + 1) + 33) + D + 2 ≤ _
    omega
  have hb : 1 ≤ b := Nat.succ_le_succ (Nat.zero_le _)
  have hbudget : budget = 2 * (A * b) + 432 * (B * b) + 369 * b := by
    simp only [budget, b, Nat.add_mul, Nat.mul_assoc]
  refine ⟨hreg.trans ?_, fun D => ?_⟩
  · omega
  · have hstate := hscalar D
    change 2 * (encJustesenSourceContext context).length + 1 +
      SourceRound.roundStateBound round D ≤ budget + D
    omega

/-- A full-fuel source scan retains its context, exact totals and transcript uniqueness
through the current radius. A round may start only while fuel remains. -/
@[expose] def JustesenSourceRoundExact {n : ℕ} (context : JustesenSourceContext)
    (edge : Fin n → Fin n → Prop) (source : Fin n)
    (r : SourceRoundLoop.Registers JustesenSourceContext) : Prop :=
  r.context = context ∧ r.fuel + r.radius = n ∧ 0 < r.fuel ∧
    r.tally = expected edge source r.radius ∧
    ∀ j ≤ r.radius, ∃! transcript, Passes edge source j transcript

/-- Full subdivision fuel starts with the exact radius-zero tally and positive fuel. -/
theorem justesenSourceRoundExact_start {n : ℕ} (context : JustesenSourceContext)
    (edge : Fin n → Fin n → Prop) (source : Fin n) :
    JustesenSourceRoundExact context edge source (SourceRoundLoop.start context n) := by
  exact ⟨rfl, Nat.add_zero _, Nat.zero_lt_of_lt source.isLt, (expected_zero edge source).symm,
    fun j hj => (Nat.eq_zero_of_le_zero hj).symm ▸ existsUnique_passes_zero edge source⟩

/-- When the round returns a larger untied set, the next round is exact and still has fuel.
A change in count can occur only before the last radius of the full-fuel scan. -/
theorem configurationJustesenRetainedSourceRound_exact_advance
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
      let context : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let edge := fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true
      ∀ r, JustesenSourceRoundExact context edge source r →
        let M := justesenRetainedSourceRound ntm c r
        ∀ (bits : List Bool) (update : RoundUpdate), M.FirstHalting w bits M.init →
          justesenRetainedSourceRoundReply (M.run w bits) = some update →
          update.bad = false → update.tally.count ≠ r.tally.count →
          JustesenSourceRoundExact context edge source (r.advance update.tally) := by
  intro I n seed source target context edge r hexact M bits update hfirst hreply hgoodUpdate hgrew
  obtain ⟨hcontext, hfuel, hpos, htally, hgood⟩ := hexact
  rcases r with ⟨actual, fuel, radius, tally⟩
  dsimp only at hcontext hfuel hpos htally hgood
  subst actual tally
  obtain ⟨hnext, hpass⟩ := configurationJustesenRetainedSourceRound_correct ntm c w
    seed source target fuel radius (hgood radius le_rfl) bits update hfirst hreply
  rw [hnext] at hgrew
  have hradius : radius + 1 < n := radius_succ_lt_of_expected_count_ne hgrew
  refine ⟨rfl, ?_, ?_, hnext, fun j hj => ?_⟩
  · dsimp only [SourceRoundLoop.Registers.advance]; omega
  · dsimp only [SourceRoundLoop.Registers.advance]; omega
  · rcases Nat.eq_or_lt_of_le (hj : j ≤ radius + 1) with rfl | hj
    · exact hpass.mp hgoodUpdate
    · exact hgood j (Nat.lt_succ_iff.mp hj)

end Cslib.Complexity.STCON
