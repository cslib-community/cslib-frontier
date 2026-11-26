/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenRoundCallback
public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision.Replay
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Dispatch.Resource
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Resources of the tagged Justesen callback

The callback uses the existing encodings for the rejecting-choice edge state and retained
membership state, preceded by the dispatch tag. The same read response and selector encoding
is used in both branches.

## Main definitions

* `Cslib.Complexity.STCON.encJustesenRoundCallbackState`: the tagged state encoding.
* `Cslib.Complexity.STCON.configurationJustesenRoundCallbackClock`: the common selector clock.

## Main results

* `Cslib.Complexity.STCON.justesenRoundCallback_parts_inSpace`: the query, transition,
  halt test, and optional Boolean reply consume linear workspace in their encoded requests.
* `Cslib.Complexity.STCON.justesenRoundCallbackStart_inSpace`: enter the requested callback
  from retained adjacency and the encoded source-round state.
* `Cslib.Complexity.STCON.configurationJustesenRoundCallback_bounds`: all valid requests
  halt within the common clock and have logarithmic encoded length at every replay prefix.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open _root_.Turing.DoubleCounting _root_.Turing.NondeterministicQueryMachine

/-- Use the existing edge and membership state encodings with a single dispatch tag. -/
@[expose] def encJustesenRoundCallbackState : JustesenRoundCallbackState ↪ List Bool :=
  encSum (encOption encJustesenSubdivisionState)
    (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)

/-- Dispatch preserves the linear-space operation certificates of both callbacks. -/
theorem justesenRoundCallback_parts_inSpace {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let M := justesenRoundCallback ntm c
    let E := encJustesenRoundCallbackState
    let encStep := encPair E encReadChoice
    ComputableInSpace M.query E encNat (fun s => (E s).length) ∧
      ComputableInSpace M.next encStep E (fun p => (encStep p).length) ∧
      ComputableInSpace M.halted E encBool (fun s => (E s).length) ∧
      ComputableInSpace justesenRoundCallbackReply E (encOption encBool)
        (fun s => (E s).length) := by
  intro M E encStep
  obtain ⟨heq, hen, heh, her⟩ := justesenWeightedSubdivisionChoice_parts_inSpace ntm
  obtain ⟨hmq, hmn, hmh, hmr⟩ := justesenSourceMembershipMachine_parts_inSpace ntm c
  have hnext := dispatch_next_inSpace (justesenWeightedSubdivisionCallback ntm).withRejectingChoice
    (justesenSourceMembershipMachine ntm c) _ _ hen hmn
  exact ⟨sumElim heq hmq, hnext, sumElim heh hmh, sumElim her hmr⟩

private theorem memberStart_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {adjacency : α → JustesenSubdivisionContext} {ctx : α → SourceRound.Context}
    {target : α → ℕ} (hadj : ComputableInSpace adjacency enc encJustesenSubdivisionContext S)
    (hctx : ComputableInSpace ctx enc SourceRound.encContext S)
    (htarget : ComputableInSpace target enc encNat S) :
    ComputableInSpace
      (fun a => justesenRoundCallbackStart (adjacency a) (ctx a) (.member (target a)))
      enc encJustesenRoundCallbackState S :=
  budget_comp_linear (of_inO (ComputableInO.inr _ _))
    (justesenRoundMembershipStart_budget hadj hctx htarget)

/-- Enter either requested callback using linear workspace in the retained adjacency and
scalar round state. The request is read from the existing round state encoding. -/
theorem justesenRoundCallbackStart_inSpace :
    let E := encPair encJustesenSubdivisionContext SourceRound.encState
    ComputableInSpace (fun p : JustesenSubdivisionContext × SourceRound.State =>
      justesenRoundCallbackStart p.1 p.2.context (SourceRound.request p.2))
      E encJustesenRoundCallbackState (fun p => (E p).length) := by
  intro E
  let P := encPair E Predecessor.encState
  have hadj := fst encJustesenSubdivisionContext SourceRound.encState
  have hstate := snd encJustesenSubdivisionContext SourceRound.encState
  have houter := memberStart_budget hadj (SourceRound.encState_context_budget hstate)
    (SourceRound.encState_cursor_budget hstate)
  have hpair := fst E Predecessor.encState
  have hpred := snd E Predecessor.encState
  have hadj' := budget_comp_linear hadj hpair
  have hstate' := budget_comp_linear hstate hpair
  have hcursor := Predecessor.encState_cursor_budget hpred
  have hmember := memberStart_budget hadj' (SourceRound.encState_context_budget hstate') hcursor
  have hedge : ComputableInSpace
      (fun p : (JustesenSubdivisionContext × SourceRound.State) × Predecessor.State =>
        justesenRoundCallbackStart p.1.1 p.1.2.context (.edge p.2.cursor p.1.2.cursor))
      P encJustesenRoundCallbackState (fun p => (P p).length) :=
    budget_comp_linear (of_inO (ComputableInO.inl _ _)) (budget_optionSome
      (budget_comp_linear justesenSubdivisionEdgeStart_inSpace
        (budget_prod hadj' (budget_prod hcursor (SourceRound.encState_cursor_budget hstate')))))
  refine (budget_comp_linear (optionElimSnd houter
      (budget_ite (Predecessor.encState_memberPhase_budget hpred) hmember hedge))
    (budget_prod (budget_id (enc := E) (.refl _))
      (SourceRound.encState_predecessor_budget hstate))).of_enc_eq ?_
  rintro ⟨adjacency, q⟩
  cases hp : q.predecessor with
  | none => simp only [hp, SourceRound.request, Option.elim_none]
  | some p =>
    cases hphase : p.memberPhase <;> simp only [hp, hphase, SourceRound.request,
      Option.elim_some, Bool.false_eq_true, ite_false, ite_true]

open Cslib.Code.JustesenFamily Cslib.DoubleCounting

variable {k : ℕ} {State : Type} [Fintype State]

/-- Both callback alternatives fit the larger of their selector clocks. -/
noncomputable def configurationJustesenRoundCallbackClock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : ℕ :=
  max 3 (configurationJustesenMembershipTallyClock ntm c w)

/-- The common callback selector clock is polynomial in the length of the original input. -/
theorem configurationJustesenRoundCallbackClock_polyBounded
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenRoundCallbackClock ntm c) :=
  PolyBounded.max (.const 3) (configurationJustesenMembershipTallyClock_polyBounded ntm c)

/-- From any in-range request in an initialized round, all branches halt within the common
clock and every selector prefix has logarithmic encoded length, including after rejection. -/
theorem configurationJustesenRoundCallback_bounds
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source : Fin n)
        (radius : ℕ) (expected : Tally),
        radius ≤ n → expected.count ≤ 1 + n * n → expected.lengthSum ≤ n * n * n →
        ∀ request : SourceRound.Request, request.InRange n →
          let adjacency := configurationJustesenSubdivisionContext ntm c w seed.val
          let ctx : SourceRound.Context := ⟨n, source.val, radius, expected⟩
          let M := justesenRoundCallback ntm c
          let entry := justesenRoundCallbackStart adjacency ctx request
          M.HaltsFrom w entry (configurationJustesenRoundCallbackClock ntm c w) ∧
            ∀ bits, (encJustesenRoundCallbackState (M.replay w bits entry)).length ≤
              C * (Nat.log2 w.length + 1) := by
  obtain ⟨A, hedge⟩ := configurationJustesenSubdivisionEdge_choice_bounds ntm c
  obtain ⟨B, hmember⟩ :=
    configurationJustesenMembershipTally_length_run_le_log_of_loop_caps ntm c
  refine ⟨max A B + 1, fun w => ?_⟩
  intro I n seed source radius expected hrad hcount hsum request hr adjacency ctx M entry
  have htag {D length : ℕ} (hD : D ≤ max A B)
      (hlength : length ≤ D * (Nat.log2 w.length + 1)) :
      length + 1 ≤ (max A B + 1) * (Nat.log2 w.length + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add (hlength.trans (Nat.mul_le_mul_right _ hD))
      (Nat.succ_le_succ (Nat.zero_le _))
  cases request with
  | edge u v =>
    obtain ⟨hu, hv⟩ := hr
    obtain ⟨hclock, hlength⟩ := hedge w seed ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨fun bits hlen => ?_, fun bits => ?_⟩
    · simp only [M, entry, justesenRoundCallback, justesenRoundCallbackStart, replay_dispatch,
        Sum.map_inl]
      exact HaltsWithin.mono ((justesenWeightedSubdivisionCallback ntm).withRejectingChoice.withInit
        (some (justesenSubdivisionEdgeStart (adjacency, u, v)))) w hclock
        (Nat.le_max_left _ _) bits hlen
    · simp only [M, entry, justesenRoundCallback, justesenRoundCallbackStart, replay_dispatch,
        Sum.map_inl, encJustesenRoundCallbackState, encSum_inl, List.length_cons]
      exact htag (Nat.le_max_left _ _) (hlength bits)
  | member v =>
    have hhalt : ((justesenSourceMembershipMachine ntm c).withInit
        (justesenRoundMembershipStart adjacency ctx v)).HaltsWithin w
        (configurationJustesenMembershipTallyClock ntm c w) := by
      dsimp only [adjacency]
      rw [justesenRoundMembershipMachine_withInit]
      exact configurationJustesenMembershipTally_haltsWithin_clock ntm c w
        seed source ⟨v, hr⟩ radius expected hrad
    refine ⟨fun bits hlen => ?_, fun bits => ?_⟩
    · simp only [M, entry, justesenRoundCallback, justesenRoundCallbackStart, replay_dispatch,
        Sum.map_inr]
      exact HaltsWithin.mono _ _ hhalt (Nat.le_max_right _ _) bits hlen
    · simp only [M, entry, justesenRoundCallback, justesenRoundCallbackStart, replay_dispatch,
        Sum.map_inr, encJustesenRoundCallbackState, encSum_inr, List.length_cons]
      rw [← run_withInit, justesenRoundMembershipMachine_withInit]
      exact htag (Nat.le_max_right _ _) (hmember w seed source ⟨v, hr⟩
        radius expected hrad hcount hsum bits)

end Cslib.Complexity.STCON
