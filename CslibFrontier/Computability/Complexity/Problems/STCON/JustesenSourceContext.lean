/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenMembershipTally
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Resource

/-!
# Retained context for a Justesen source scan

The source loop retains the initialized weighted adjacency context and the two query endpoints.
On stabilization, the membership entry takes the current radius and tally from the loop
registers. The dimension comes from the retained subdivision, so the entry uses the same
carrier as the adjacency callback.

## Main definitions

* `Cslib.Complexity.STCON.JustesenSourceContext`: the data retained across source rounds.
* `Cslib.Complexity.STCON.justesenRoundMembershipStart`: membership at a requested vertex.
* `Cslib.Complexity.STCON.justesenSourceMembershipStart`: membership at the designated target.
* `Cslib.Complexity.STCON.justesenSourceMembershipMachine`: the fixed re-entrant tally.

## Main results

* `Cslib.Complexity.STCON.justesenSourceMembershipStart_inSpace`: construct the final
  membership entry in linear workspace in the encoded loop registers.
* `Cslib.Complexity.STCON.justesenRoundMembership_readReply_iff` and
  `Cslib.Complexity.STCON.justesenSourceMembership_readReply_iff`: a complete typed scan and
  the return selector give the same reply and leave the same suffix.
* `Cslib.Complexity.STCON.justesenSourceMembership_bounds`: a common selector clock and
  logarithmic state bound at every admissible loop entry.
* `Cslib.Complexity.STCON.justesenSourceMembership_existsUnique_firstHalting`: one
  successful selector list at a unique passing transcript.
* `Cslib.Complexity.STCON.justesenSourceMembership_readReply_correct`: a successful reply at
  the exact round totals reports bounded reachability.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.DoubleCounting Cslib.Reachability.Hoza
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open _root_.Turing.DoubleCounting _root_.Turing.QueryMachine.Subdivision

/-- The data retained across all rounds for one source query. -/
structure JustesenSourceContext where
  /-- The initialized subdivision context shared by adjacency and membership calls. -/
  adjacency : JustesenSubdivisionContext
  /-- The subdivision ID of the current source. -/
  sourceID : ℕ
  /-- The subdivision ID of the designated membership target. -/
  targetID : ℕ

/-- Frame the adjacency context and the two binary endpoint IDs. -/
enc_structure encJustesenSourceContext : JustesenSourceContext where
  adjacency : encJustesenSubdivisionContext, sourceID : encNat, targetID : encNat

/-- Number of vertices in the retained subdivision. -/
@[expose] def JustesenSourceContext.size (ctx : JustesenSourceContext) : ℕ :=
  ctx.adjacency.parameters.search.subdivision.vertexCount

/-- The initialized source context uses the scheduler setup's subdivision dimension. -/
theorem configurationJustesenSourceContext_size {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) (rank source target : ℕ) :
    (⟨configurationJustesenSubdivisionContext ntm c w rank, source, target⟩ :
      JustesenSourceContext).size =
        (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount := by
  simp only [JustesenSourceContext.size, configurationJustesenSubdivisionContext,
    (configurationSeedSearchSetup_endpoints ntm c w).1]

/-- Read the subdivision size from the existing adjacency context encoding. -/
theorem encJustesenSourceContext_size_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {ctx : α → JustesenSourceContext}
    (hctx : ComputableInSpace ctx enc encJustesenSourceContext S) :
    ComputableInSpace (fun a => (ctx a).size) enc encNat S :=
  encSubdivisionSize_vertexCount_budget
    (encJustesenSubdivisionContext_subdivision_budget
      (encJustesenSourceContext_adjacency_budget hctx))

/-- Enter membership at the candidate vertex, using the round's current tally. -/
@[expose] def justesenRoundMembershipStart (adjacency : JustesenSubdivisionContext)
    (ctx : SourceRound.Context) (target : ℕ) :
    MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState :=
  MembershipTally.retainedInitial adjacency
    ⟨ctx.size, ctx.source, target, ctx.radius, ctx.expected⟩

/-- Membership entry uses the shared budget of its adjacency, round, and target producers. -/
theorem justesenRoundMembershipStart_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {adjacency : α → JustesenSubdivisionContext} {ctx : α → SourceRound.Context}
    {target : α → ℕ} (hadj : ComputableInSpace adjacency enc encJustesenSubdivisionContext S)
    (hctx : ComputableInSpace ctx enc SourceRound.encContext S)
    (htarget : ComputableInSpace target enc encNat S) :
    ComputableInSpace (fun a => justesenRoundMembershipStart (adjacency a) (ctx a) (target a))
      enc (MembershipTally.encRetainedState encJustesenSubdivisionContext
        encJustesenSubdivisionState) S :=
  MembershipTally.retainedInitial_budget encJustesenSubdivisionContext encJustesenSubdivisionState
    hadj (MembershipTally.encContext_mk_budget (SourceRound.encContext_size_budget hctx)
      (SourceRound.encContext_source_budget hctx) htarget
      (SourceRound.encContext_radius_budget hctx) (SourceRound.encContext_expected_budget hctx))

/-- Enter final membership at the loop's current radius and verified tally. -/
@[expose] def justesenSourceMembershipStart (r : SourceRoundLoop.Registers JustesenSourceContext) :
    MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState :=
  justesenRoundMembershipStart r.context.adjacency
    (SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r)
    r.context.targetID

/-- Final membership entry uses linear workspace in the encoded source-loop registers. -/
theorem justesenSourceMembershipStart_inSpace :
    let E := SourceRoundLoop.encRegisters encJustesenSourceContext
    ComputableInSpace justesenSourceMembershipStart E
      (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)
      (fun r => (E r).length) := by
  intro E
  have hr := budget_id (enc := E) (.refl _)
  have hctx := SourceRoundLoop.encRegisters_context_budget encJustesenSourceContext hr
  have hid := budget_id (enc := encJustesenSourceContext) (.refl _)
  have hround := SourceRoundLoop.roundContext_inSpace
    JustesenSourceContext.size JustesenSourceContext.sourceID encJustesenSourceContext
    (encJustesenSourceContext_size_budget hid) (encJustesenSourceContext_sourceID_budget hid)
  exact justesenRoundMembershipStart_budget (encJustesenSourceContext_adjacency_budget hctx)
    hround (encJustesenSourceContext_targetID_budget hctx)

variable {k : ℕ} {State : Type} [Fintype State]

/-- A round's membership request keeps the round parameters and changes the query target. -/
theorem justesenRoundMembershipMachine_withInit
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) (rank : ℕ)
    (ctx : SourceRound.Context) (target : ℕ) :
    (justesenSourceMembershipMachine ntm c).withInit
      (justesenRoundMembershipStart (configurationJustesenSubdivisionContext ntm c w rank)
        ctx target) =
      configurationJustesenMembershipTally ntm c w rank
        ⟨ctx.size, ctx.source, target, ctx.radius, ctx.expected⟩ :=
  configurationJustesenMembershipTally_withInit ntm c [] w 0 rank _ _

/-- Re-entry in the final membership call uses the source scan's word, rank, and tally. -/
theorem justesenSourceMembershipMachine_withInit
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (rank source target fuel radius : ℕ) (totals : Tally) :
    let ctx : JustesenSourceContext :=
      ⟨configurationJustesenSubdivisionContext ntm c w rank, source, target⟩
    (justesenSourceMembershipMachine ntm c).withInit
      (justesenSourceMembershipStart ⟨ctx, fuel, radius, totals⟩) =
        configurationJustesenMembershipTally ntm c w rank
          ⟨(configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount,
            source, target, radius, totals⟩ := by
  intro ctx
  simp only [justesenSourceMembershipStart, ctx, justesenRoundMembershipMachine_withInit,
    SourceRoundLoop.roundContext, configurationJustesenSourceContext_size]

open NondeterministicQueryMachine in
/-- A round membership return consumes the canonical typed tally selectors and the false
return selector. The Boolean scan reply and the unused suffix are returned unchanged. -/
theorem justesenRoundMembership_readReply_iff
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (radius : ℕ) (totals : Tally) (bits : List Bool) (hit : Bool) (suffix : List Bool),
      let ctx : SourceRound.Context := ⟨size.vertexCount, source.val, radius, totals⟩
      let adjacency := configurationJustesenSubdivisionContext ntm c w seed.val
      let entry := justesenRoundMembershipStart adjacency ctx target.val
      (justesenSourceMembershipMachine ntm c).readReply MembershipTally.retainedReply
        w entry bits = some (hit, suffix) ↔
      ∃ branch,
        bits = MembershipTally.selectors (BoundedWalk.selectors 3) branch ++ false :: suffix ∧
        Scan.run (configurationJustesenSubdivisionAdjacent ntm c w seed)
          source target radius totals branch = some hit := by
  intro I size seed source target radius totals bits hit suffix ctx adjacency entry
  rw [readReply_iff]
  let M := justesenSourceMembershipMachine ntm c
  have hspec (callBits : List Bool) :
      M.FirstHalting w callBits entry ∧
        MembershipTally.retainedReply (M.replay w callBits entry) = some hit ↔
      ∃! branch, callBits = MembershipTally.selectors (BoundedWalk.selectors 3) branch ∧
        Scan.run (configurationJustesenSubdivisionAdjacent ntm c w seed)
          source target radius totals branch = some hit := by
    let entered := M.withInit entry
    change entered.FirstHalting w callBits entered.init ∧
      MembershipTally.retainedReply (entered.run w callBits) = some hit ↔ _
    dsimp only [entered, M, entry, adjacency, ctx]
    rw [justesenRoundMembershipMachine_withInit]
    exact configurationJustesenMembershipTally_firstHalting_iff ntm c w seed source target
      radius totals callBits hit
  constructor
  · rintro ⟨callBits, hbits, hfirst, hreply⟩
    obtain ⟨branch, ⟨rfl, hscan⟩, _⟩ := (hspec callBits).mp ⟨hfirst, hreply⟩
    exact ⟨branch, hbits, hscan⟩
  · rintro ⟨branch, hbits, hscan⟩
    refine ⟨_, hbits, (hspec _).mpr ⟨branch, ⟨rfl, hscan⟩, ?_⟩⟩
    exact fun _ h =>
      MembershipTally.selectors_injective _ (BoundedWalk.eq_of_selectors_prefix 3) h.1.symm

open NondeterministicQueryMachine in
/-- A final membership return consumes the canonical typed tally selectors and the false
return selector. The Boolean scan reply and the unused suffix are returned unchanged. -/
theorem justesenSourceMembership_readReply_iff
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (fuel radius : ℕ) (totals : Tally) (bits : List Bool) (hit : Bool) (suffix : List Bool),
      let ctx : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let entry := justesenSourceMembershipStart ⟨ctx, fuel, radius, totals⟩
      (justesenSourceMembershipMachine ntm c).readReply MembershipTally.retainedReply
        w entry bits = some (hit, suffix) ↔
      ∃ branch,
        bits = MembershipTally.selectors (BoundedWalk.selectors 3) branch ++ false :: suffix ∧
        Scan.run (configurationJustesenSubdivisionAdjacent ntm c w seed)
          source target radius totals branch = some hit := by
  intro I size seed source target fuel radius totals bits hit suffix ctx entry
  simpa only [entry, ctx, justesenSourceMembershipStart, SourceRoundLoop.roundContext,
    configurationJustesenSourceContext_size] using
    justesenRoundMembership_readReply_iff ntm c w seed source target radius totals bits hit suffix

open NondeterministicQueryMachine in
/-- A unique passing transcript at the exact totals gives one successful selector list for
the source loop's final membership callback. -/
theorem justesenSourceMembership_existsUnique_firstHalting
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (fuel radius : ℕ),
      let adjacent := configurationJustesenSubdivisionAdjacent ntm c w seed
      let edge := fun u v => adjacent u v = true
      (∃! transcript, Passes edge source radius transcript) →
      let ctx : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let entry := justesenSourceMembershipStart ⟨ctx, fuel, radius, expected edge source radius⟩
      let M := justesenSourceMembershipMachine ntm c
      ∃! bits, M.FirstHalting w bits entry ∧
        (MembershipTally.retainedReply (M.replay w bits entry)).isSome := by
  intro I size seed source target fuel radius adjacent edge hpass ctx entry M
  let entered := M.withInit entry
  change ∃! bits, entered.FirstHalting w bits entered.init ∧
    (MembershipTally.retainedReply (entered.run w bits)).isSome
  dsimp only [entered, M, entry]
  rw [justesenSourceMembershipMachine_withInit]
  exact configurationJustesenMembershipTally_existsUnique_firstHalting ntm c w
    seed source target radius hpass

open NondeterministicQueryMachine in
/-- At the exact totals, a parsed final reply is true precisely when the target is reachable
from the source within the current radius. -/
theorem justesenSourceMembership_readReply_correct
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (fuel radius : ℕ) (bits : List Bool) (hit : Bool) (suffix : List Bool),
      let adjacent := configurationJustesenSubdivisionAdjacent ntm c w seed
      let edge := fun u v => adjacent u v = true
      let ctx : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let entry := justesenSourceMembershipStart ⟨ctx, fuel, radius, expected edge source radius⟩
      (justesenSourceMembershipMachine ntm c).readReply MembershipTally.retainedReply
        w entry bits = some (hit, suffix) →
      (hit ↔ target ∈ Relation.reachableWithin edge source radius) := by
  intro I size seed source target fuel radius bits hit suffix adjacent edge ctx entry hreply
  obtain ⟨branch, _, hscan⟩ :=
    (justesenSourceMembership_readReply_iff ntm c w seed source target fuel radius
      (expected edge source radius) bits hit suffix).mp hreply
  exact Scan.hit_iff_reachable adjacent source target radius branch hit (by
    rw [Scan.runM_replay]
    exact hscan)

open NondeterministicQueryMachine in
/-- The final membership callback has a common selector clock and logarithmic encoded-state
bound at every admissible loop entry, including when earlier callbacks returned inexact totals. -/
theorem justesenSourceMembership_bounds (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
        (limit : ℕ), limit ≤ size.vertexCount →
        let ctx : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        ∀ r, SourceRoundLoop.Admissible ctx ctx.size limit r →
          let M := justesenSourceMembershipMachine ntm c
          let entry := justesenSourceMembershipStart r
          (M.withInit entry).HaltsWithin w (configurationJustesenMembershipTallyClock ntm c w) ∧
            ∀ bits, (MembershipTally.encRetainedState encJustesenSubdivisionContext
              encJustesenSubdivisionState (M.replay w bits entry)).length ≤
                C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, hlength⟩ := configurationJustesenMembershipTally_length_run_le_log_of_loop_caps ntm c
  refine ⟨C, fun w => ?_⟩
  intro I size seed source target limit hlimit ctx r hr M entry
  have hsize : ctx.size = size.vertexCount :=
    configurationJustesenSourceContext_size ntm c w seed.val source.val target.val
  rcases r with ⟨actual, fuel, radius, totals⟩
  obtain ⟨hctx, hfuel, hc, hs⟩ := hr
  change actual = ctx at hctx
  subst actual
  change fuel + radius = limit at hfuel
  change totals.count ≤ 1 + radius * ctx.size at hc
  change totals.lengthSum ≤ ctx.size * radius * radius at hs
  rw [hsize] at hc hs
  have hrad : radius ≤ size.vertexCount := by omega
  have hc' := hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hrad) 1)
  have hs' := hs.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hrad) hrad)
  dsimp only [M, entry]
  constructor
  · rw [justesenSourceMembershipMachine_withInit]
    exact configurationJustesenMembershipTally_haltsWithin_clock ntm c w
      seed source target radius totals hrad
  · intro bits
    rw [← run_withInit, justesenSourceMembershipMachine_withInit]
    exact hlength w seed source target radius totals hrad hc' hs' bits

end Cslib.Complexity.STCON
