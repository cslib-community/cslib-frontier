/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally.Runtime
import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenBoundedWalk
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Justesen subdivision membership tally

The retained tally reads the original word. It supplies the same initialized Justesen context
to every bounded walk, so the typed scan uses the subdivision adjacency for the chosen rank.

## Main definitions

* `Cslib.Complexity.STCON.justesenSourceMembershipMachine`: the fixed re-entrant tally.

## Main results

* `Cslib.Complexity.STCON.justesenSourceMembershipMachine_parts_inSpace`: linear-space
  operation certificates for the source loop's re-entrant tally.

* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_firstHalting_iff`: exact
  first-halting selector and membership-reply correspondence for the weighted tally.
* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_existsUnique_firstHalting`:
  one successful selector list at the exact round totals given a unique passing transcript.
* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_native_firstHalting_iff`:
  one accepting native occurrence list per passing selector list.
* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_acceptCount_eq_one`:
  one native accepting branch across all selectors when the passing transcript is unique.
* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_length_run_le_log`:
  logarithmic encoded length on every prefix of a bounded tally query.
* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_length_run_le_log_of_loop_caps`:
  the same bound for the larger tally parameters admitted by the enclosing loop.
* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_haltsWithin_clock`:
  a common polynomial selector clock for those queries.
* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_exists_routines`:
  native compilation with logarithmic workspace from valid rank and tally producers.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.DoubleCounting
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open _root_.Turing.DoubleCounting _root_.Turing.QueryMachine.Subdivision

variable {k : ℕ} {State : Type} [Fintype State]

private noncomputable def tallyWalkInitial (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    BoundedWalk.Runtime.State JustesenSubdivisionContext JustesenSubdivisionState :=
  ⟨configurationJustesenSubdivisionContext ntm c [] 0, 1, Nat.zero_lt_one, .done none⟩

/-- The membership tally for the initialized Justesen-weighted subdivision of the original
input. Its adjacency calls use the common clock three. -/
noncomputable def configurationJustesenMembershipTally (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) (rank : ℕ) (params : MembershipTally.Context) :
    NondeterministicQueryMachine
      (MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState) :=
  MembershipTally.retainedMachine (justesenWeightedSubdivisionCallback ntm)
    (fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)) callbackVerdict 3
    (tallyWalkInitial ntm c) (configurationJustesenSubdivisionContext ntm c w rank) params

/-- The source loop supplies the actual tally entry through its current registers. -/
@[expose] noncomputable def justesenSourceMembershipMachine
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    NondeterministicQueryMachine
      (MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState) :=
  configurationJustesenMembershipTally ntm c [] 0 ⟨0, 0, 0, 0, ⟨0, 0⟩⟩

open NondeterministicQueryMachine (encReadChoice) in
/-- The fixed callback's query, transition, halt, and optional reply run in linear
workspace in their encoded operation requests. -/
theorem justesenSourceMembershipMachine_parts_inSpace
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let M := justesenSourceMembershipMachine ntm c
    let E := MembershipTally.encRetainedState encJustesenSubdivisionContext
      encJustesenSubdivisionState
    let encStep := encPair E encReadChoice
    ComputableInSpace M.query E encNat (fun s => (E s).length) ∧
      ComputableInSpace M.next encStep E (fun p => (encStep p).length) ∧
      ComputableInSpace M.halted E encBool (fun s => (E s).length) ∧
      ComputableInSpace MembershipTally.retainedReply E (encOption encBool)
        (fun s => (E s).length) := by
  intro M E encStep
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx := configurationJustesenSubdivisionContext ntm c [] 0
  obtain ⟨hq, hn, hh, _, _⟩ := justesenWeightedSubdivisionCallback_parts_inSpace ntm
  exact ⟨MembershipTally.retainedMachine_query_inSpace edge start callbackVerdict 3
      (tallyWalkInitial ntm c) ctx encJustesenSubdivisionContext encJustesenSubdivisionState _ hq,
    MembershipTally.retainedMachine_next_inSpace edge start callbackVerdict 3
      (tallyWalkInitial ntm c) ctx encJustesenSubdivisionContext encJustesenSubdivisionState _
      justesenSubdivisionEdgeStart_inSpace hn hh (callbackVerdict_inSpace _ _),
    MembershipTally.retainedMachine_halted_inSpace edge start callbackVerdict 3
      (tallyWalkInitial ntm c) ctx encJustesenSubdivisionContext encJustesenSubdivisionState _,
    MembershipTally.retainedReply_inSpace encJustesenSubdivisionContext
      encJustesenSubdivisionState⟩

/-- Changing the original word, rank, and query parameters changes only the tally entry. -/
theorem configurationJustesenMembershipTally_withInit (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w w' : List Bool) (rank rank' : ℕ) (params params' : MembershipTally.Context) :
    (configurationJustesenMembershipTally ntm c w rank params).withInit
      (MembershipTally.retainedInitial (configurationJustesenSubdivisionContext ntm c w' rank')
        params') =
    configurationJustesenMembershipTally ntm c w' rank' params' :=
  MembershipTally.retainedMachine_withInit (justesenWeightedSubdivisionCallback ntm)
    (fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)) callbackVerdict 3
    (tallyWalkInitial ntm c) (configurationJustesenSubdivisionContext ntm c w rank)
    params params' (configurationJustesenSubdivisionContext ntm c w' rank')

/-- At a valid seed and endpoints, a successful tally uses the selectors of exactly one
passing typed scan and preserves its membership reply. -/
theorem configurationJustesenMembershipTally_firstHalting_iff
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (radius : ℕ) (expected : Tally) (bits : List Bool) (hit : Bool),
      let M := configurationJustesenMembershipTally ntm c w seed.val
        ⟨size.vertexCount, source.val, target.val, radius, expected⟩
      M.FirstHalting w bits M.init ∧ MembershipTally.retainedReply (M.run w bits) = some hit ↔
        ∃! branch, bits = MembershipTally.selectors (BoundedWalk.selectors 3) branch ∧
          Scan.run (configurationJustesenSubdivisionAdjacent ntm c w seed)
            source target radius expected branch = some hit := by
  intro I size seed source target radius expected bits hit M
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
  let initial := tallyWalkInitial ntm c
  have hcall := configurationJustesenSubdivisionEdge_halts_and_agrees ntm c w seed
  exact (MembershipTally.retainedMachine_firstHalting_reply_iff edge start callbackVerdict 3
    initial ctx ⟨size.vertexCount, source.val, target.val, radius, expected⟩ w bits hit).trans
    (MembershipTally.withRuntimeWalk_firstHalting_iff edge start callbackVerdict 3 initial ctx
      w (configurationJustesenSubdivisionAdjacent ntm c w seed) source target radius expected
      (fun u v => (hcall u v).1) (fun u v => (hcall u v).2) bits hit)

/-- The Justesen tally has exactly one successful first-halting selector list when the
transcript at the exact round totals is unique. -/
theorem configurationJustesenMembershipTally_existsUnique_firstHalting
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (radius : ℕ),
      let adjacent := configurationJustesenSubdivisionAdjacent ntm c w seed
      let edge := fun u v => adjacent u v = true
      (∃! transcript, Passes edge source radius transcript) →
      let M := configurationJustesenMembershipTally ntm c w seed.val
        ⟨size.vertexCount, source.val, target.val, radius, expected edge source radius⟩
      ∃! bits, M.FirstHalting w bits M.init ∧
        (MembershipTally.retainedReply (M.run w bits)).isSome := by
  intro I size seed source target radius adjacent edge hpass M
  have hcall := configurationJustesenSubdivisionEdge_halts_and_agrees ntm c w seed
  exact MembershipTally.retainedMachine_existsUnique_firstHalting
    (justesenWeightedSubdivisionCallback ntm)
    (fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)) callbackVerdict 3
    (tallyWalkInitial ntm c) (configurationJustesenSubdivisionContext ntm c w seed.val)
    w adjacent source target radius (fun u v => (hcall u v).1) (fun u v => (hcall u v).2) hpass

open NondeterministicQueryMachine in
/-- A fixed selector list has exactly one accepting native occurrence list precisely when
it encodes a passing typed tally at the initialized seed. Both membership replies pass. -/
theorem configurationJustesenMembershipTally_native_firstHalting_iff
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) {α : Type} {enc : α ↪ List Bool}
    {S : α → ℕ} {rank : α → ℕ} {params : α → MembershipTally.Context}
    {w₀ : List Bool} {rank₀ : ℕ} {params₀ : MembershipTally.Context}
    (R : Routines (configurationJustesenMembershipTally ntm c w₀ rank₀ params₀)
      (fun a => MembershipTally.retainedInitial
        (configurationJustesenSubdivisionContext ntm c (enc a) (rank a)) (params a)) enc S)
    (a : α) :
    let I := configurationInstance ntm c (enc a)
    let size := (configurationSeedSearchSetup ntm c (enc a)).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (radius : ℕ) (expected : Tally) (bits : List Bool),
      rank a = seed.val →
      params a = ⟨size.vertexCount, source.val, target.val, radius, expected⟩ →
      ((∃! indices, ∃ final,
        Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (enc a)) indices =
          some (bits, final) ∧ final.Halted ∧ final.output = [true]) ↔
        ∃! branch, bits = MembershipTally.selectors (BoundedWalk.selectors 3) branch ∧
          ∃ hit, Scan.run (configurationJustesenSubdivisionAdjacent ntm c (enc a) seed)
            source target radius expected branch = some hit) := by
  intro I size seed source target radius expected bits hrank hparams
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx a := configurationJustesenSubdivisionContext ntm c (enc a) (rank a)
  have hcall := configurationJustesenSubdivisionEdge_halts_and_agrees ntm c (enc a) seed
  exact MembershipTally.retainedMachine_native_firstHalting_iff edge start callbackVerdict 3
    (tallyWalkInitial ntm c) (configurationJustesenSubdivisionContext ntm c w₀ rank₀)
    params₀ ctx params R a _ source target radius expected bits hparams
    (fun u v => by simpa only [ctx, hrank] using (hcall u v).1)
    (fun u v => by simpa only [ctx, hrank] using (hcall u v).2)

open NondeterministicQueryMachine in
/-- At the exact round totals with a unique passing transcript, the compiled Justesen tally
has one accepting branch at any sufficient native clock. The count includes a false reply. -/
theorem configurationJustesenMembershipTally_acceptCount_eq_one
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) {α : Type} {enc : α ↪ List Bool}
    {S : α → ℕ} {rank : α → ℕ} {params : α → MembershipTally.Context}
    {w₀ : List Bool} {rank₀ : ℕ} {params₀ : MembershipTally.Context}
    (R : Routines (configurationJustesenMembershipTally ntm c w₀ rank₀ params₀)
      (fun a => MembershipTally.retainedInitial
        (configurationJustesenSubdivisionContext ntm c (enc a) (rank a)) (params a)) enc S)
    (a : α) {fuel : ℕ} (hclock : R.machine.RunsInTime (enc a) fuel) :
    let I := configurationInstance ntm c (enc a)
    let size := (configurationSeedSearchSetup ntm c (enc a)).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (radius : ℕ),
      let adjacent := configurationJustesenSubdivisionAdjacent ntm c (enc a) seed
      let edge := fun u v => adjacent u v = true
      rank a = seed.val →
      params a = ⟨size.vertexCount, source.val, target.val, radius, expected edge source radius⟩ →
      (∃! transcript, Passes edge source radius transcript) →
      (Native.countingMachine R.I R.P R.F R.C).acceptCount fuel
        (R.machine.initCfg (enc a)) = 1 := by
  intro I size seed source target radius adjacent edge hrank hparams hpass
  apply (R.acceptCount_eq_one_iff a hclock).mpr
  simp only [hrank, hparams]
  let entered := (configurationJustesenMembershipTally ntm c w₀ rank₀ params₀).withInit
    (MembershipTally.retainedInitial
      (configurationJustesenSubdivisionContext ntm c (enc a) seed.val)
      ⟨size.vertexCount, source.val, target.val, radius, expected edge source radius⟩)
  change ∃! bits, entered.FirstHalting (enc a) bits entered.init ∧
    entered.accept (entered.run (enc a) bits) = true
  simp only [entered, configurationJustesenMembershipTally_withInit]
  simpa only [configurationJustesenMembershipTally, MembershipTally.retainedMachine_accept] using
    configurationJustesenMembershipTally_existsUnique_firstHalting ntm c (enc a) seed source
      target radius hpass

private theorem loopCaps_of_tightCaps {n : ℕ} {totals : Tally} (hn : 0 < n)
    (hc : totals.count ≤ n) (hs : totals.lengthSum ≤ n * n) :
    totals.count ≤ 1 + n * n ∧ totals.lengthSum ≤ n * n * n := by
  have hmul (a : ℕ) : a ≤ a * n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left a (Nat.succ_le_of_lt hn)
  exact ⟨hc.trans ((hmul n).trans (Nat.le_add_left _ _)), hs.trans (hmul (n * n))⟩

/-- The tally envelope is logarithmic at the source loop's coarse tally caps,
apart from the charged adjacency callback state. -/
theorem configurationJustesenMembershipTally_stateBound_le_log_of_loop_caps
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
        (radius : ℕ) (expected : Tally) (calleeBound : ℕ),
        radius ≤ size.vertexCount →
        expected.count ≤ 1 + size.vertexCount * size.vertexCount →
        expected.lengthSum ≤ size.vertexCount * size.vertexCount * size.vertexCount →
        let params : MembershipTally.Context :=
          ⟨size.vertexCount, source.val, target.val, radius, expected⟩
        let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
        MembershipTally.retainedStateBound 3 params
          (encJustesenSubdivisionContext ctx).length calleeBound ≤
          C * (Nat.log2 w.length + 1) + calleeBound := by
  obtain ⟨W, hwalk⟩ := configurationJustesenBoundedWalk_stateBound_le_log ntm c
  obtain ⟨D, hcontext⟩ := length_configurationJustesenSubdivisionContext_le_log ntm c
  obtain ⟨P, hvertices⟩ := length_configurationSubdivisionVertexCount_le_log ntm c
  refine ⟨2 * D + 80 * P + W + 68, fun w => ?_⟩
  intro I size seed source target radius expected calleeBound hr hc hs params ctx
  let n := size.vertexCount
  let b := Nat.log2 w.length + 1
  have hn : (encNat n).length ≤ P * b := hvertices w
  have hctx : (encJustesenSubdivisionContext ctx).length ≤ D * b :=
    hcontext w seed.val seed.isLt
  have hW : BoundedWalk.Runtime.stateBound n radius 3
      (encJustesenSubdivisionContext ctx).length calleeBound ≤ W * b + calleeBound :=
    hwalk w seed radius calleeBound hr
  have hsource := length_encNat_mono source.isLt.le
  have htarget := length_encNat_mono target.isLt.le
  have hradius := length_encNat_mono hr
  obtain ⟨hcount, hsum⟩ := length_encTally_fields_le_of_caps le_rfl hc hs
  have hparams : (MembershipTally.encContext params).length ≤ 15 * (encNat n).length + 9 := by
    simp only [params, MembershipTally.encContext_apply, MembershipTally.encContextFields,
      encTally_apply, encTallyFields, length_encPair]
    dsimp only [n] at hcount hsum ⊢
    omega
  have hlogN : Nat.log2 n ≤ (encNat n).length :=
    (Nat.log2_le_size _).trans_eq (length_encNat_eq_size _).symm
  have hlogSum : Nat.log2 (n * radius) ≤ 2 * (encNat n).length := by
    have hlen := length_encNat_mul_le n radius
    have hlog := (Nat.log2_le_size (n * radius)).trans_eq (length_encNat_eq_size _).symm
    dsimp only [n] at hlen hlog ⊢; omega
  have hb : 1 ≤ b := Nat.succ_le_succ (Nat.zero_le _)
  change MembershipTally.retainedStateBound 3 params
    (encJustesenSubdivisionContext ctx).length calleeBound ≤ _ * b + _
  simp only [MembershipTally.retainedStateBound, MembershipTally.runtimeWalkStateBound,
    MembershipTally.stateBound, Nat.add_mul, Nat.mul_assoc]
  change 2 * (encJustesenSubdivisionContext ctx).length + 1 +
    (4 * (MembershipTally.encContext params).length + 12 * (Nat.log2 n + 1) +
      4 * (Nat.log2 (n * radius) + 1) +
      BoundedWalk.Runtime.stateBound n radius 3
        (encJustesenSubdivisionContext ctx).length calleeBound + 15) ≤ _
  dsimp only [n] at hn hW hparams hlogN hlogSum ⊢; omega

/-- The tally envelope is logarithmic apart from the charged adjacency callback state. -/
theorem configurationJustesenMembershipTally_stateBound_le_log
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
        (radius : ℕ) (expected : Tally) (calleeBound : ℕ),
        radius ≤ size.vertexCount →
        expected.count ≤ size.vertexCount →
        expected.lengthSum ≤ size.vertexCount * size.vertexCount →
        let params : MembershipTally.Context :=
          ⟨size.vertexCount, source.val, target.val, radius, expected⟩
        let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
        MembershipTally.retainedStateBound 3 params
          (encJustesenSubdivisionContext ctx).length calleeBound ≤
          C * (Nat.log2 w.length + 1) + calleeBound := by
  obtain ⟨C, h⟩ := configurationJustesenMembershipTally_stateBound_le_log_of_loop_caps ntm c
  refine ⟨C, fun w seed source target radius expected calleeBound hr hc hs => ?_⟩
  obtain ⟨hc', hs'⟩ := loopCaps_of_tightCaps (Nat.zero_lt_of_lt source.isLt) hc hs
  exact h w seed source target radius expected calleeBound hr hc' hs'

/-- Every prefix of an initialized tally fits a logarithmic encoded-state bound under
the source loop's coarse tally caps. -/
theorem configurationJustesenMembershipTally_length_run_le_log_of_loop_caps
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
        (radius : ℕ) (expected : Tally),
        radius ≤ size.vertexCount →
        expected.count ≤ 1 + size.vertexCount * size.vertexCount →
        expected.lengthSum ≤ size.vertexCount * size.vertexCount * size.vertexCount →
        let params : MembershipTally.Context :=
          ⟨size.vertexCount, source.val, target.val, radius, expected⟩
        let M := configurationJustesenMembershipTally ntm c w seed.val params
        ∀ bits, (MembershipTally.encRetainedState encJustesenSubdivisionContext
          encJustesenSubdivisionState (M.run w bits)).length ≤ C * (Nat.log2 w.length + 1) := by
  obtain ⟨A, hcall⟩ := configurationJustesenSubdivisionEdge_contract ntm c
  obtain ⟨C, hbound⟩ := configurationJustesenMembershipTally_stateBound_le_log_of_loop_caps ntm c
  refine ⟨C + A, fun w => ?_⟩
  intro I size seed source target radius expected hr hc hs params M bits
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
  let b := Nat.log2 w.length + 1
  have hcallee (u v : Fin size.vertexCount) (t : ℕ) (ht : t ≤ 3) :
      (encJustesenSubdivisionState (edge.runFrom w (start ctx u.val v.val) t)).length ≤ A * b :=
    (hcall w seed u v).2.2.2 t ht
  have hrun := MembershipTally.retainedMachine_length_run_le edge start callbackVerdict 3
    (tallyWalkInitial ntm c) ctx encJustesenSubdivisionContext encJustesenSubdivisionState
    params source.isLt w (A * b) hcallee bits
  refine hrun.trans ?_
  simpa only [b, Nat.add_mul] using hbound w seed source target radius expected (A * b) hr hc hs

/-- Every prefix of an initialized tally fits the uniform logarithmic encoded-state bound. -/
theorem configurationJustesenMembershipTally_length_run_le_log
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
        (radius : ℕ) (expected : Tally),
        radius ≤ size.vertexCount →
        expected.count ≤ size.vertexCount →
        expected.lengthSum ≤ size.vertexCount * size.vertexCount →
        let params : MembershipTally.Context :=
          ⟨size.vertexCount, source.val, target.val, radius, expected⟩
        let M := configurationJustesenMembershipTally ntm c w seed.val params
        ∀ bits, (MembershipTally.encRetainedState encJustesenSubdivisionContext
          encJustesenSubdivisionState (M.run w bits)).length ≤ C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, h⟩ := configurationJustesenMembershipTally_length_run_le_log_of_loop_caps ntm c
  refine ⟨C, fun w seed source target radius expected hr hc hs => ?_⟩
  obtain ⟨hc', hs'⟩ := loopCaps_of_tightCaps (Nat.zero_lt_of_lt source.isLt) hc hs
  exact h w seed source target radius expected hr hc' hs'

/-- Charge one bounded walk and its entry and return at each candidate, then the final check. -/
noncomputable def configurationJustesenMembershipTallyClock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : ℕ :=
  let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
  n * (configurationJustesenBoundedWalkClock ntm c w + 2) + 1

/-- The common tally selector clock is polynomial in the length of the original input. -/
theorem configurationJustesenMembershipTallyClock_polyBounded
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenMembershipTallyClock ntm c) :=
  ((configurationSubdivisionVertexCount_polyBounded ntm c).mul
      ((configurationJustesenBoundedWalkClock_polyBounded ntm c).add (.const 2))).add (.const 1)

/-- The clock covers all tally branches uniformly over valid seed and endpoint IDs
and radii at most the subdivision vertex count. -/
theorem configurationJustesenMembershipTally_haltsWithin_clock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (radius : ℕ) (expected : Tally), radius ≤ size.vertexCount →
      let params : MembershipTally.Context :=
        ⟨size.vertexCount, source.val, target.val, radius, expected⟩
      (configurationJustesenMembershipTally ntm c w seed.val params).HaltsWithin w
        (configurationJustesenMembershipTallyClock ntm c w) := by
  intro I size seed source target radius expected hr params
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
  have h := MembershipTally.retainedMachine_haltsWithin edge start callbackVerdict 3
    (tallyWalkInitial ntm c) ctx params source.isLt w
  refine NondeterministicQueryMachine.HaltsWithin.mono _ _ h ?_
  simp only [MembershipTally.runtimeWalkClock, params, configurationJustesenMembershipTallyClock,
    configurationJustesenBoundedWalkClock, Nat.add_assoc, Nat.reduceAdd]
  gcongr

open NondeterministicQueryMachine in
/-- Compile one native tally on the original encoded input. The valid rank and tally
producers provide the retained entry, and the weighted callback is fixed across inputs. -/
theorem configurationJustesenMembershipTally_exists_routines
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) {α : Type} {enc : α ↪ List Bool}
    {rank : α → ℕ} {params : α → MembershipTally.Context}
    (hrank : ComputableInLogSpace rank enc encNat)
    (hrank_lt : ∀ a, rank a < (configurationSeedSearchParameters ntm c (enc a)).search.seedLimit)
    (hparams : ComputableInSpace params enc MembershipTally.encContext
      (fun a => Nat.log2 (enc a).length))
    (hvalid : ∀ a,
      let setup := configurationSeedSearchSetup ntm c (enc a)
      let n := setup.parameters.search.subdivision.vertexCount
      (params a).size = n ∧ (params a).source < n ∧ (params a).target < n ∧
        (params a).radius ≤ n ∧ (params a).expected.count ≤ n ∧
        (params a).expected.lengthSum ≤ n * n) :
    let baseline : MembershipTally.Context := ⟨0, 0, 0, 0, ⟨0, 0⟩⟩
    let M := configurationJustesenMembershipTally ntm c [] 0 baseline
    let init a := MembershipTally.retainedInitial
      (configurationJustesenSubdivisionContext ntm c (enc a) (rank a)) (params a)
    ∃ K, Nonempty (Routines M init enc (fun a => K * (Nat.log2 (enc a).length + 1))) := by
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx a := configurationJustesenSubdivisionContext ntm c (enc a) (rank a)
  let seed (a : α) :
      Fin (2 ^ codeLength (configurationInstance ntm c (enc a)).n
        ((configurationInstance ntm c (enc a)).n - 1)) :=
    ⟨rank a, hrank_lt a⟩
  let n a := (configurationSeedSearchSetup ntm c (enc a)).parameters.search.subdivision.vertexCount
  let b a := Nat.log2 (enc a).length + 1
  obtain ⟨A, hcall⟩ := configurationJustesenSubdivisionEdge_contract ntm c
  obtain ⟨C, hbound⟩ := configurationJustesenMembershipTally_stateBound_le_log ntm c
  let S a := (C + A + 1) * b a
  have hlog (a : α) : b a ≤ S a := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hsmall (a : α) : Nat.log2 (enc a).length ≤ S a := (Nat.le_succ _).trans (hlog a)
  have hctx : ComputableInSpace ctx enc encJustesenSubdivisionContext S :=
    (configurationJustesenSubdivisionContext_inSpace ntm c hrank hrank_lt).mono_le hsmall
  have hsource (a : α) : (params a).source < (params a).size := (hvalid a).1 ▸ (hvalid a).2.1
  have hcallee (a : α) (u v : Fin (params a).size) (t : ℕ) (ht : t ≤ 3) :
      (encJustesenSubdivisionState (edge.runFrom (enc a) (start (ctx a) u.val v.val) t)).length ≤
        A * b a := by
    have hu : u.val < n a := by simpa only [(hvalid a).1] using u.isLt
    have hv : v.val < n a := by simpa only [(hvalid a).1] using v.isLt
    exact (hcall (enc a) (seed a) ⟨u.val, hu⟩ ⟨v.val, hv⟩).2.2.2 t ht
  have hstate (a : α) :
      MembershipTally.retainedStateBound 3 (params a) (encJustesenSubdivisionContext (ctx a)).length
        (A * b a) ≤ S a := by
    obtain ⟨hsize, hsrc, hdst, hr, hc, hs⟩ := hvalid a
    let source : Fin (n a) := ⟨(params a).source, hsrc⟩
    let target : Fin (n a) := ⟨(params a).target, hdst⟩
    have hshape :
        params a = ⟨n a, source.val, target.val, (params a).radius, (params a).expected⟩ := by
      cases hp : params a
      simpa [hp, source, target] using hsize
    rw [hshape]
    refine (hbound (enc a) (seed a) source target (params a).radius (params a).expected
      (A * b a) hr hc hs).trans ?_
    simp only [S, b, Nat.add_mul, Nat.one_mul]
    exact Nat.le_add_right _ _
  obtain ⟨hq, hn, hh, _, _⟩ := justesenWeightedSubdivisionCallback_parts_inSpace ntm
  exact ⟨C + A + 1, MembershipTally.retainedMachine_exists_routines edge start callbackVerdict 3
    (tallyWalkInitial ntm c) (configurationJustesenSubdivisionContext ntm c [] 0)
    encJustesenSubdivisionContext encJustesenSubdivisionState enc S ⟨0, 0, 0, 0, ⟨0, 0⟩⟩
    ctx params hctx (hparams.mono_le hsmall) hlog
    justesenSubdivisionEdgeStart_inSpace hq hn hh (callbackVerdict_inSpace _ _)
    hsource (fun a => A * b a) hcallee hstate⟩

end Cslib.Complexity.STCON
