/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.Predecessor
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.BranchReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Scalar controller for one double-counting round

The outer cursor requests membership before testing incoming edges. A negative membership
reply starts the predecessor loop for that vertex. The outer cursor advances only after a
positive membership reply or a completed predecessor count. A rejected request terminates
the round, distinct from a completed round that encountered a tie.
-/

public section

namespace Turing.DoubleCounting.SourceRound

open Cslib.DoubleCounting MultiTapeTM ComputableInSpace
open NondeterministicQueryMachine (encReadChoice)

/-- Immutable arguments for a round of membership and adjacency calls. -/
structure Context where
  /-- Number of vertices. -/
  size : ℕ
  /-- Source for membership requests. -/
  source : ℕ
  /-- Radius used for every membership request in this round. -/
  radius : ℕ
  /-- Tally supplied to membership requests throughout this round. -/
  expected : Tally

/-- The current round prefix and any active predecessor loop. -/
structure State where
  /-- Original callback arguments. -/
  context : Context
  /-- Number of completed vertices. -/
  cursor : ℕ
  /-- Updated tally and tie flag for the completed prefix. -/
  update : RoundUpdate
  /-- Present while testing the incoming edges of the current vertex. -/
  predecessor : Option Predecessor.State
  /-- A callback rejected. -/
  rejected : Bool

/-- Binary graph size, source, radius and expected tally. -/
enc_structure encContext : Context where
  size : encNat, source : encNat, radius : encNat, expected : encTally

/-- Binary outer cursor and tally, with the active predecessor loop if present. -/
enc_structure encState : State where
  context : encContext, cursor : encNat, update : encRoundUpdate,
  predecessor : (encOption Predecessor.encState), rejected : encBool

/-- Arguments of the currently requested same-input callback. -/
inductive Request where
  /-- Test the directed edge from one vertex to another. -/
  | edge (source target : ℕ)
  /-- Test membership in the original round for this vertex. -/
  | member (vertex : ℕ)

/-- Every vertex ID in the callback request is within the round's carrier. -/
@[expose] def Request.InRange (req : Request) (size : ℕ) : Prop :=
  match req with
  | .edge u v => u < size ∧ v < size
  | .member v => v < size

/-- Start with the supplied tally and no completed vertices. -/
@[expose] def initial (ctx : Context) : State :=
  ⟨ctx, 0, ⟨ctx.expected, false⟩, none, false⟩

/-- Rejection and completion of the outer cursor stop the controller. -/
@[expose] def halted (q : State) : Bool :=
  q.rejected || decide (q.context.size ≤ q.cursor)

/-- Dispatch the outer membership test or the current predecessor request. -/
@[expose] def request (q : State) : Request :=
  match q.predecessor with
  | none => .member q.cursor
  | some p => if p.memberPhase then .member p.cursor else .edge p.cursor q.cursor

private def predecessorContext (q : State) : Predecessor.Context :=
  ⟨q.context.size, q.context.source, q.cursor, q.context.radius, q.context.expected⟩

/-- Consume one result from the selected callback. The active predecessor loop uses its
landed reply handler, and every finished count contributes through `RoundUpdate.addVertex`. -/
@[expose] def advance (q : State) (reply : Option Bool) : State :=
  let nextVertex (update : RoundUpdate) : State :=
    { q with cursor := q.cursor + 1, update := update, predecessor := none }
  match reply with
  | none => { q with rejected := true }
  | some hit =>
    match q.predecessor with
    | none =>
      if hit then nextVertex q.update
      else
        { q with predecessor := some (Predecessor.initial
            ⟨q.context.size, q.context.source, q.cursor, q.context.radius, q.context.expected⟩) }
    | some p =>
      let next := Predecessor.advance p (some hit)
      if Predecessor.halted next then
        nextVertex (q.update.addVertex q.context.radius next.count)
      else { q with predecessor := some next }

/-- The original callback arguments are unchanged by any reply. -/
theorem advance_context (q : State) (reply : Option Bool) :
    (advance q reply).context = q.context := by
  cases reply with
  | none => rfl
  | some hit =>
    cases hp : q.predecessor with
    | none => cases hit <;> simp [advance, hp]
    | some p =>
      simp only [advance, hp]
      split <;> rfl

/-- The cursor never exceeds the number of vertices, including after a rejected reply. -/
theorem advance_cursor_le {q : State} (hlive : halted q = false) (reply : Option Bool) :
    (advance q reply).cursor ≤ q.context.size := by
  have hlt : q.cursor < q.context.size := by
    simp only [halted, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hlive
    exact hlive.2
  cases reply with
  | none => exact hlt.le
  | some hit =>
    cases hp : q.predecessor with
    | none =>
      cases hit
      · simpa only [advance, hp, Bool.false_eq_true, ite_false] using hlt.le
      · simpa only [advance, hp, ite_true] using Nat.succ_le_of_lt hlt
    | some p =>
      simp only [advance, hp]
      split
      · exact hlt
      · exact hlt.le

/-- A completed round retains its tie flag. A rejected round has no update. -/
@[expose] def result (q : State) : Option RoundUpdate :=
  if q.rejected then none else some q.update

/-- The controller retains its scalar registers while a callback reads the same input. -/
structure MachineState (τ : Type) where
  /-- Active or suspended controller. -/
  controller : State
  /-- Callback state while a request is pending. -/
  callee : Option τ

/-- The framed controller and, during a call, the entire encoded callee state. -/
enc_structure encMachineState (τ : Type) (encT : τ ↪ List Bool) : MachineState τ where
  controller : encState, callee : (encOption encT)

/-- A bound on the entire round machine state, including the suspended caller and live callee. -/
theorem length_encMachineState_le {τ : Type} (encT : τ ↪ List Bool)
    (q : MachineState τ) (C D : ℕ) (hc : (encState q.controller).length ≤ C)
    (ht : ∀ t ∈ q.callee, (encT t).length ≤ D) :
    (encMachineState τ encT q).length ≤ 2 * C + D + 2 := by
  rw [encMachineState_apply]
  simp only [encMachineStateFields, length_encPair]
  cases hcall : q.callee with
  | none =>
    rw [encOption_none]
    simp only [List.length_nil]
    omega
  | some t =>
    have hlen := ht t (by simp [hcall])
    rw [encOption_some]
    simp only [List.length_cons]
    omega

/-- Enter the fixed round transition machine with the supplied radius and tally. -/
@[expose] def entry {τ : Type} (ctx : Context) : MachineState τ :=
  ⟨initial ctx, none⟩

/-- Read the optional update after a completed round. -/
@[expose] def answer {τ : Type} (q : MachineState τ) : Option RoundUpdate :=
  result q.controller

/-- Run calls on the original input. Entering and returning use the false selector.
An active callback receives each choice unchanged until it halts. -/
@[expose] def machine {τ : Type} (ctx : Context) (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool) :
    NondeterministicQueryMachine (MachineState τ) where
  init := entry ctx
  query q := q.callee.elim 0 N.query
  next := fun ⟨q, bit, choice⟩ =>
    let reject := ⟨advance q.controller none, none⟩
    match q.callee with
    | none =>
      if choice then reject else
        ⟨q.controller, some (start q.controller.context (request q.controller))⟩
    | some callee =>
      if N.halted callee then
        if choice then reject else ⟨advance q.controller (finish callee), none⟩
      else ⟨q.controller, some (N.next (callee, bit, choice))⟩
  halted q := halted q.controller
  accept q := !q.controller.rejected

/-- Changing the round context changes only the entry state. -/
theorem machine_withInit {τ : Type} (ctx next : Context) (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool) :
    (machine ctx N start finish).withInit (entry next) = machine next N start finish :=
  rfl

private theorem reject_inSpace :
    ComputableInSpace (fun q => advance q none) encState encState
      (fun q => (encState q).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encState)).inO_one
  exact (encState_mk_budget (encState_context_budget hid) (encState_cursor_budget hid)
    (encState_update_budget hid) (encState_predecessor_budget hid)
    (budget_const true (.refl _))).of_enc_eq fun _ => rfl

private theorem advance_withoutPredecessor_inSpace :
    ComputableInSpace
      (fun (p : State × Bool) => advance { p.1 with predecessor := none } (some p.2))
      (encPair encState encBool) encState (fun p => (encPair encState encBool p).length) := by
  have hq := fst encState encBool
  have hb := snd encState encBool
  have hc := encState_context_budget hq
  have hi := encState_cursor_budget hq
  have hu := encState_update_budget hq
  have hr := encState_rejected_budget hq
  have one := budget_const (encIn := encPair encState encBool) (encB := encNat) 1 (.refl _)
  have hpc := Predecessor.encContext_mk_budget (encContext_size_budget hc)
    (encContext_source_budget hc) hi (encContext_radius_budget hc) (encContext_expected_budget hc)
  have hp := budget_optionSome (budget_comp_linear Predecessor.initial_inSpace hpc)
  have hnext := encState_mk_budget hc (budget_natAdd hi one) hu (budget_const none (.refl _)) hr
  exact (budget_ite hb hnext (encState_mk_budget hc hi hu hp hr)).of_enc_eq fun ⟨q, b⟩ => by
    cases b <;> rfl

private theorem advance_withPredecessor_inSpace :
    ComputableInSpace
      (fun (p : (State × Bool) × Predecessor.State) =>
        advance { p.1.1 with predecessor := some p.2 } (some p.1.2))
      (encPair (encPair encState encBool) Predecessor.encState) encState
      (fun p => (encPair (encPair encState encBool) Predecessor.encState p).length) := by
  let encIn := encPair (encPair encState encBool) Predecessor.encState
  have hargs := fst (encPair encState encBool) Predecessor.encState
  have hp := snd (encPair encState encBool) Predecessor.encState
  have hnext := budget_comp_linear Predecessor.advance_inSpace
    (budget_prod hp (budget_optionSome hargs.snd'))
  have hc := encState_context_budget hargs.fst'
  have hi := encState_cursor_budget hargs.fst'
  have hu := encState_update_budget hargs.fst'
  have hr := encState_rejected_budget hargs.fst'
  have one := budget_const (encIn := encIn) (encB := encNat) 1 (.refl _)
  have hupdate := budget_comp_linear addVertex_inSpace
    (budget_prod hu (budget_prod (encContext_radius_budget hc)
      (Predecessor.encState_count_budget hnext)))
  have hdone := encState_mk_budget hc (budget_natAdd hi one) hupdate
    (budget_const none (.refl _)) hr
  have hpending := encState_mk_budget hc hi hu (budget_optionSome hnext) hr
  refine (budget_ite (budget_comp_linear Predecessor.halted_inSpace hnext)
    hdone hpending).of_enc_eq ?_
  rintro ⟨⟨q, hit⟩, p⟩
  simp only [advance]

/-- Resume the round using the optional reply, updating only its binary scalar registers. -/
theorem advance_inSpace :
    ComputableInSpace (fun p : State × Option Bool => advance p.1 p.2)
      (encPair encState (encOption encBool)) encState
      (fun p => (encPair encState (encOption encBool) p).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encPair encState encBool)).inO_one
  have hq := fst encState encBool
  have hsome := budget_comp_linear
    (optionElimSnd advance_withoutPredecessor_inSpace advance_withPredecessor_inSpace)
    (budget_prod hid (encState_predecessor_budget hq))
  refine (optionElimSnd reject_inSpace hsome).of_enc_eq ?_
  rintro ⟨⟨ctx, cursor, update, p, rejected⟩, _ | b⟩
  · rfl
  · cases p <;> rfl

/-- Re-enter a fixed round controller using only the supplied binary context. -/
theorem entry_inSpace {τ : Type} (encT : τ ↪ List Bool) :
    ComputableInSpace (entry (τ := τ)) encContext (encMachineState τ encT)
      (fun ctx => (encContext ctx).length) := by
  have hctx := of_inO (ComputableInDegree.id' (enc := encContext)).inO_one
  have zero := budget_const (encIn := encContext) (encB := encNat) 0 (.refl _)
  have no := budget_const (encIn := encContext) (encB := encBool) false (.refl _)
  have hupdate := encRoundUpdate_mk_budget (encContext_expected_budget hctx) no
  have hcaller := encState_mk_budget hctx zero hupdate (budget_const none (.refl _)) no
  exact (encMachineState_mk_budget τ encT hcaller (budget_const none (.refl _))).of_enc_eq
    fun _ => rfl

/-- Query the original input at the callee's position, or at zero between calls. -/
theorem machine_query_inSpace {τ : Type} (encT : τ ↪ List Bool)
    (ctx : Context) (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool)
    (hq : ComputableInSpace N.query encT encNat (fun t => (encT t).length)) :
    ComputableInSpace (machine ctx N start finish).query (encMachineState τ encT) encNat
      (fun q => (encMachineState τ encT q).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encMachineState τ encT)).inO_one
  have hpair := budget_prod (encMachineState_controller_budget τ encT hid)
    (encMachineState_callee_budget τ encT hid)
  exact (budget_comp_linear
    (optionElimSnd (budget_const 0 (.refl _)) (budget_comp_linear hq (snd encState encT)))
    hpair).of_enc_eq fun q => by cases q; rfl

/-- The native halt test compares the binary cursor and size and checks the rejection bit. -/
theorem machine_halted_inSpace {τ : Type} (encT : τ ↪ List Bool)
    (ctx : Context) (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool) :
    ComputableInSpace (machine ctx N start finish).halted (encMachineState τ encT) encBool
      (fun q => (encMachineState τ encT q).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encMachineState τ encT)).inO_one
  have hc := encMachineState_controller_budget τ encT hid
  have hi := encState_cursor_budget hc
  have hn := encContext_size_budget (encState_context_budget hc)
  have hr := encState_rejected_budget hc
  exact (budget_boolOr hr (budget_natLe hn hi)).of_enc_eq fun _ => rfl

/-- A completed tied round accepts, while an explicit callback rejection does not. -/
theorem machine_accept_inSpace {τ : Type} (encT : τ ↪ List Bool)
    (ctx : Context) (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool) :
    ComputableInSpace (machine ctx N start finish).accept (encMachineState τ encT) encBool
      (fun q => (encMachineState τ encT q).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encMachineState τ encT)).inO_one
  have hc := encMachineState_controller_budget τ encT hid
  exact (budget_boolNot (encState_rejected_budget hc)).of_enc_eq fun _ => rfl

/-- Decode the reply for a caller while preserving the distinction between a tie and rejection. -/
theorem answer_inSpace {τ : Type} (encT : τ ↪ List Bool) :
    ComputableInSpace (answer (τ := τ)) (encMachineState τ encT) (encOption encRoundUpdate)
      (fun q => (encMachineState τ encT q).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encMachineState τ encT)).inO_one
  have hc := encMachineState_controller_budget τ encT hid
  exact (budget_ite (encState_rejected_budget hc) (budget_const none (.refl _))
    (budget_optionSome (encState_update_budget hc))).of_enc_eq fun _ => rfl

/-- Step the scalar round with an extra immutable parameter for callback entry. -/
theorem machine_next_withParameter_inSpace {κ τ : Type} (encK : κ ↪ List Bool)
    (encT : τ ↪ List Bool)
    (ctx : Context) (N : NondeterministicQueryMachine τ)
    (start : κ → Context → Request → τ) (finish : τ → Option Bool)
    (hs : ComputableInSpace (fun (k, q) => start k q.context (request q))
      (encPair encK encState) encT (fun p => (encPair encK encState p).length))
    (hf : ComputableInSpace finish encT (encOption encBool) (fun t => (encT t).length))
    (hh : ComputableInSpace N.halted encT encBool (fun t => (encT t).length))
    (hn : ComputableInSpace N.next (encPair encT encReadChoice) encT
      (fun p => (encPair encT encReadChoice p).length)) :
    let encStep := encPair (encPair encK (encMachineState τ encT)) encReadChoice
    ComputableInSpace (fun ((k, q), read, choice) => (machine ctx N (start k) finish).next
      (q, read, choice)) encStep (encMachineState τ encT) (fun p => (encStep p).length) := by
  let encCaller := encPair (encPair encK encState) encReadChoice
  have hcaller := fst (encPair encK encState) encReadChoice
  have hstate := snd' hcaller
  have hchoice := snd' (snd (encPair encK encState) encReadChoice)
  have henter := encMachineState_mk_budget τ encT hstate
    (budget_optionSome (budget_comp_linear hs hcaller))
  have hreject := encMachineState_mk_budget τ encT (budget_comp_linear reject_inSpace hstate)
    (budget_const none (.refl _))
  have hbetween := budget_ite hchoice hreject henter
  have hframe := fst encCaller encT
  have hcallee := snd encCaller encT
  have hcontroller := snd' (fst' hframe)
  have hreadChoice := snd' hframe
  have hreturn := budget_comp_linear advance_inSpace
    (budget_prod hcontroller (budget_comp_linear hf hcallee))
  have hreturned := encMachineState_mk_budget τ encT hreturn (budget_const none (.refl _))
  have hcontinue := encMachineState_mk_budget τ encT hcontroller
    (budget_optionSome (budget_comp_linear hn (budget_prod hcallee hreadChoice)))
  have hactive := budget_ite (budget_comp_linear hh hcallee)
    (budget_ite (snd' hreadChoice) (budget_comp_linear hreject hframe) hreturned) hcontinue
  let encRound := encPair encK (encMachineState τ encT)
  have hround := fst encRound encReadChoice
  have hmachine := snd' hround
  have hpair := budget_prod
    (budget_prod (budget_prod (fst' hround) (encMachineState_controller_budget τ encT hmachine))
      (snd encRound encReadChoice))
    (encMachineState_callee_budget τ encT hmachine)
  refine (budget_comp_linear (optionElimSnd hbetween hactive) hpair).of_enc_eq ?_
  rintro ⟨⟨k, ⟨q, _ | t⟩⟩, read, choice⟩
  · cases choice <;> rfl
  · cases choice <;> cases N.halted t <;> rfl

/-- Advance the suspended caller or the active callee in linear space in their joint encoding. -/
theorem machine_next_inSpace {τ : Type} (encT : τ ↪ List Bool)
    (ctx : Context) (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool)
    (hs : ComputableInSpace (fun q : State => start q.context (request q)) encState encT
      (fun q => (encState q).length))
    (hf : ComputableInSpace finish encT (encOption encBool) (fun t => (encT t).length))
    (hh : ComputableInSpace N.halted encT encBool (fun t => (encT t).length))
    (hn : ComputableInSpace N.next (encPair encT encReadChoice) encT
      (fun p => (encPair encT encReadChoice p).length)) :
    ComputableInSpace (machine ctx N start finish).next
      (encPair (encMachineState τ encT) encReadChoice) (encMachineState τ encT)
      (fun p => (encPair (encMachineState τ encT) encReadChoice p).length) := by
  have hentry := budget_comp_linear hs (snd encUnit encState)
  have hnext := machine_next_withParameter_inSpace encUnit encT ctx N (fun _ => start) finish
    hentry hf hh hn
  have hstep := budget_prod
    (budget_prod (budget_const (encB := encUnit) () (.refl _))
      (fst (encMachineState τ encT) encReadChoice))
    (snd (encMachineState τ encT) encReadChoice)
  exact (budget_comp_linear hnext hstep).of_enc_eq fun _ => rfl

open NondeterministicQueryMachine in
/-- Compile one round with a supplied input-dependent initializer and native same-input callbacks.
The state budget must cover all selector prefixes, including those on rejecting branches. -/
theorem exists_routines {α τ : Type} (enc : α ↪ List Bool) (encT : τ ↪ List Bool)
    (ctx : Context) (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool)
    (contextOf : α → Context) (S : α → ℕ)
    (hinit : ComputableInSpace contextOf enc encContext S)
    (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hs : ComputableInSpace (fun q : State => start q.context (request q)) encState encT
      (fun q => (encState q).length))
    (hf : ComputableInSpace finish encT (encOption encBool) (fun t => (encT t).length))
    (hq : ComputableInSpace N.query encT encNat (fun t => (encT t).length))
    (hh : ComputableInSpace N.halted encT encBool (fun t => (encT t).length))
    (hn : ComputableInSpace N.next (encPair encT encReadChoice) encT
      (fun p => (encPair encT encReadChoice p).length))
    (hstates : ∃ c, ∀ a bits, (encMachineState τ encT
      ((machine (contextOf a) N start finish).run (enc a) bits)).length ≤ c * S a) :
    Nonempty (Routines (machine ctx N start finish) (fun a => entry (contextOf a)) enc S) := by
  obtain ⟨c, hstates⟩ := hstates
  refine (machine ctx N start finish).exists_routines (machine_query_inSpace encT _ _ _ _ hq)
    (machine_next_inSpace encT _ _ _ _ hs hf hh hn) (machine_halted_inSpace encT _ _ _ _)
    (machine_accept_inSpace encT _ _ _ _) _ S hlog (budget_comp_linear (entry_inSpace encT) hinit)
    ⟨c, fun a bits => ?_⟩
  rw [machine_withInit]
  exact hstates a bits

private theorem step_active {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ) (finish : τ → Option Bool)
    (input : List Bool) (q : State) (hq : halted q = false) (s : τ) (choice : Bool)
    (hs : N.halted s = false) :
    (machine ctx N start finish).step input ⟨q, some s⟩ choice =
      ⟨q, some (N.step input s choice)⟩ := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, machine, hq, hs]

/-- Replay a first-halting callback on the original input. One false selector enters the
call and one returns. The final reply may be negative or may reject. -/
theorem replay_request {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ) (finish : τ → Option Bool)
    (input : List Bool) (q : State) (hq : halted q = false) (bits : List Bool)
    (hcall : N.FirstHalting input bits (start q.context (request q))) :
    (machine ctx N start finish).replay input (false :: bits ++ [false]) ⟨q, none⟩ =
      ⟨advance q (finish (N.replay input bits (start q.context (request q)))), none⟩ := by
  rw [List.cons_append, NondeterministicQueryMachine.replay_cons]
  have henter : (machine ctx N start finish).step input ⟨q, none⟩ false =
      ⟨q, some (start q.context (request q))⟩ := by
    simp [NondeterministicQueryMachine.step, machine, hq]
  have hr := (machine ctx N start finish).replay_map_of_live input N (fun s => ⟨q, some s⟩)
    (step_active ctx N start finish input q hq) bits _ hcall.2
  rw [henter, NondeterministicQueryMachine.replay_append, hr]
  simp [NondeterministicQueryMachine.replay_cons, NondeterministicQueryMachine.step, machine,
    hq, hcall.1]

/-- Every completed vertex contributes at most one count and one distance increment,
independently of the callback's replies. -/
private theorem advance_tally_bounds {q : State} (reply : Option Bool)
    (hc : q.update.tally.count ≤ q.context.expected.count + q.cursor)
    (hs : q.update.tally.lengthSum ≤
      q.context.expected.lengthSum + q.cursor * (q.context.radius + 1)) :
    let next := advance q reply
    next.update.tally.count ≤ q.context.expected.count + next.cursor ∧
    next.update.tally.lengthSum ≤
      q.context.expected.lengthSum + next.cursor * (q.context.radius + 1) := by
  have unchanged :
      q.update.tally.count ≤ q.context.expected.count + (q.cursor + 1) ∧
      q.update.tally.lengthSum ≤
        q.context.expected.lengthSum + (q.cursor + 1) * (q.context.radius + 1) := by
    rw [Nat.add_mul]
    omega
  have updated (count : ℕ) :
      (q.update.addVertex q.context.radius count).tally.count ≤
        q.context.expected.count + (q.cursor + 1) ∧
      (q.update.addVertex q.context.radius count).tally.lengthSum ≤
        q.context.expected.lengthSum + (q.cursor + 1) * (q.context.radius + 1) := by
    by_cases h : count = 0
    · simpa [RoundUpdate.addVertex, h] using unchanged
    · simp only [RoundUpdate.addVertex, h, ite_false, Nat.add_mul]
      omega
  cases reply with
  | none => exact ⟨hc, hs⟩
  | some hit =>
    cases hp : q.predecessor with
    | none =>
      cases hit
      · simpa only [advance, hp, Bool.false_eq_true, ite_false] using And.intro hc hs
      · simpa only [advance, hp, ite_true] using unchanged
    | some p =>
      simp only [advance, hp]
      split
      · exact updated _
      · exact ⟨hc, hs⟩


private def PredecessorBounded (q : State) : Prop :=
  ∀ p ∈ q.predecessor, p.context = predecessorContext q ∧
    Predecessor.Bounded p ∧ Predecessor.halted p = false

private theorem advance_predecessorBounded {q : State} (hlive : halted q = false)
    (hpre : PredecessorBounded q) (reply : Option Bool) :
    PredecessorBounded (advance q reply) := by
  have hsize : 0 < q.context.size := by
    simp only [halted, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hlive
    exact Nat.zero_lt_of_lt hlive.2
  cases reply with
  | none => exact hpre
  | some hit =>
    cases hp : q.predecessor with
    | none =>
      cases hit
      · intro p hmem
        simp only [advance, hp, Bool.false_eq_true, ite_false, Option.mem_some_iff] at hmem
        subst p
        exact ⟨by simp [predecessorContext, advance, hp, Predecessor.initial],
          Predecessor.initial_bounded _,
          by simp [Predecessor.halted, Predecessor.initial, Nat.not_le.mpr hsize]⟩
      · simp [PredecessorBounded, advance, hp]
    | some p =>
      obtain ⟨hctx, hbounded, hactive⟩ := hpre p (by simp [hp])
      simp only [PredecessorBounded, advance, hp]
      split
      · simp
      · rename_i hnext
        intro next hmem
        rw [Option.mem_some_iff] at hmem
        subst next
        exact ⟨(Predecessor.advance_context _ _).trans hctx,
          Predecessor.advance_bounded hbounded hactive _, Bool.eq_false_iff.mpr hnext⟩

private def remaining {m : Type → Type} [Monad m] {n : ℕ}
    (edge : Fin n → Fin n → m Bool) (member : Fin n → m Bool)
    (failCount : m ℕ) (failRound : m RoundUpdate) (q : State) : m RoundUpdate :=
  let loop := Fin.foldlMFrom (scanVertex edge member q.context.radius)
  if q.rejected then failRound else
    match q.predecessor with
    | none => loop q.update q.cursor
    | some p =>
      if hv : q.cursor < n then do
        let c ← Predecessor.remaining edge member failCount ⟨q.cursor, hv⟩ p
        loop (q.update.addVertex q.context.radius c) (q.cursor + 1)
      else pure q.update

private theorem remaining_initial {m : Type → Type} [Monad m] (ctx : Context)
    (edge : Fin ctx.size → Fin ctx.size → m Bool) (member : MembershipScan m ctx.size)
    (failCount : m ℕ) (failRound : m RoundUpdate) :
    remaining edge (member ctx.radius ctx.expected) failCount failRound (initial ctx) =
      scanNextRound edge member ctx.radius ctx.expected := by
  simp only [remaining, initial, Bool.false_eq_true, ↓reduceIte, Fin.foldlMFrom_zero, scanNextRound]

private theorem remaining_of_done {m : Type → Type} [Monad m] {n : ℕ}
    (edge : Fin n → Fin n → m Bool) (member : Fin n → m Bool)
    (failCount : m ℕ) (failRound : m RoundUpdate) (q : State)
    (hr : q.rejected = false) (hi : n ≤ q.cursor) :
    remaining edge member failCount failRound q = pure q.update := by
  cases hp : q.predecessor <;> simp [remaining, hr, hi.not_gt, hp, Fin.foldlMFrom_of_le _ _ hi]

private theorem remaining_bind {m : Type → Type} [Monad m] [LawfulMonad m] {n : ℕ}
    (read : Request → m Bool) (failCount : m ℕ) (failRound : m RoundUpdate)
    (q : State) (hs : q.context.size = n) (hlive : halted q = false)
    (hp : PredecessorBounded q) :
    let edge (u v : Fin n) := read (.edge u v)
    let member (v : Fin n) := read (.member v)
    remaining edge member failCount failRound q =
      (read (request q) >>= fun hit =>
        remaining edge member failCount failRound (advance q (some hit))) := by
  obtain ⟨hr, hv⟩ := Bool.or_eq_false_iff.mp hlive
  have hi : q.cursor < n := by simpa [hs] using hv
  let edge (u v : Fin n) := read (.edge u v)
  let member (v : Fin n) := read (.member v)
  change remaining edge member failCount failRound q =
    (read (request q) >>= fun hit =>
      remaining edge member failCount failRound (advance q (some hit)))
  cases hpre : q.predecessor with
  | none =>
    simp only [remaining, hr, hpre, Bool.false_eq_true, ↓reduceIte, request]
    rw [Fin.foldlMFrom_step _ _ hi]
    simp only [scanVertex, bind_assoc]
    congr 1
    funext hit
    cases hit
    · simp [advance, hpre, Predecessor.remaining_initial, member, hi, hr]
    · simp [advance, hpre, hr]
  | some p =>
    obtain ⟨hctx, _, hplive⟩ := hp p (by simp [hpre])
    have hsize : p.context.size = n := by
      simpa [predecessorContext, hs] using congrArg Predecessor.Context.size hctx
    obtain ⟨hpr, hpc⟩ := Bool.or_eq_false_iff.mp hplive
    have hj : p.cursor < n := by simpa [hsize] using hpc
    conv_lhs => simp only [remaining, hr, hpre, Bool.false_eq_true, ↓reduceIte, dite_eq_left hi]
    rw [Predecessor.remaining_bind edge member failCount ⟨q.cursor, hi⟩ p hj hpr, bind_assoc]
    have hread : (if p.memberPhase then member ⟨p.cursor, hj⟩
        else edge ⟨p.cursor, hj⟩ ⟨q.cursor, hi⟩) = read (request q) := by
      cases hphase : p.memberPhase <;> simp [request, hpre, hphase, member, edge]
    rw [hread]
    congr 1
    funext hit
    let next := Predecessor.advance p (some hit)
    have hnextSize : next.context.size = n := by
      rw [Predecessor.advance_context, hsize]
    have hnextReject : next.rejected = false := by
      cases he : Predecessor.observe p hit <;> simp [next, Predecessor.advance, he, hpr]
    change (_ >>= _) = remaining edge member failCount failRound (advance q (some hit))
    by_cases hdone : Predecessor.halted next = true
    · have hd : n ≤ next.cursor := by
        simpa [Predecessor.halted, hnextSize, hnextReject] using hdone
      rw [Predecessor.remaining_of_done edge member failCount _ _ hnextReject hd, pure_bind]
      simp [advance, hpre, ← show Predecessor.advance p (some hit) = next from rfl,
        show Predecessor.halted (Predecessor.advance p (some hit)) = true from hdone, hr, remaining]
    · simp [advance, hpre,
        show ¬ Predecessor.halted (Predecessor.advance p (some hit)) = true from hdone,
        hr, remaining, hi]

private def readRequest {τ : Type} (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool)
    (input : List Bool) (ctx : Context) (req : Request) : StateT (List Bool) Option Bool :=
  fun
    | false :: bits => N.readReply finish input (start ctx req) bits
    | _ => none

private theorem readRequest_of_success {τ : Type} (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool)
    (input : List Bool) (ctx : Context) (req : Request)
    (bits rest : List Bool) (hit : Bool)
    (hread : (readRequest N start finish input ctx req).run bits = some (hit, rest)) :
    ∃ tail, bits = false :: tail ∧
      N.readReply finish input (start ctx req) tail = some (hit, rest) := by
  rcases bits with _ | ⟨_ | _, tail⟩
  · cases hread
  · exact ⟨tail, rfl, hread⟩
  · cases hread

private theorem readRequest_length_lt {τ : Type} (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool)
    (input : List Bool) (ctx : Context) (req : Request)
    (bits rest : List Bool) (hit : Bool)
    (hread : (readRequest N start finish input ctx req).run bits = some (hit, rest)) :
    rest.length < bits.length := by
  obtain ⟨tail, rfl, htail⟩ :=
    readRequest_of_success N start finish input ctx req bits rest hit hread
  obtain ⟨callBits, rfl, _, _⟩ := (N.readReply_iff finish input tail _ hit rest).mp htail
  simp
  omega

private theorem successful_request_iff {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ) (finish : τ → Option Bool)
    (input : List Bool) (q : State) (bits : List Bool) (final : MachineState τ)
    (hlive : halted q = false) (hh : halted final.controller = true)
    (ha : (answer final).isSome = true) :
    let M := machine ctx N start finish
    M.FirstHalting input bits ⟨q, none⟩ ∧ M.replay input bits ⟨q, none⟩ = final ↔
      ∃ hit rest, (readRequest N start finish input q.context (request q)).run bits =
          some (hit, rest) ∧
        M.FirstHalting input rest ⟨advance q (some hit), none⟩ ∧
        M.replay input rest ⟨advance q (some hit), none⟩ = final := by
  let M := machine ctx N start finish
  let reject : MachineState τ := ⟨advance q none, none⟩
  have hreject : M.halted reject = true := by simp [M, reject, machine, halted, advance]
  have hne : reject ≠ final := by
    intro he
    rw [← he] at ha
    cases ha
  cases bits with
  | nil =>
    simp [NondeterministicQueryMachine.FirstHalting, machine, hlive, readRequest, StateT.run]
  | cons b bits =>
    dsimp only
    rw [M.firstHalting_cons_iff, M.replay_cons]
    change (halted q = false ∧ M.FirstHalting input bits (M.step input ⟨q, none⟩ b)) ∧
      M.replay input bits (M.step input ⟨q, none⟩ b) = final ↔ _
    simp only [hlive, true_and]
    cases b
    · have henter : M.step input ⟨q, none⟩ false =
          ⟨q, some (start q.context (request q))⟩ := by
        simp [M, machine, NondeterministicQueryMachine.step, hlive]
      rw [henter]
      apply M.successful_call_iff N input (fun s => ⟨q, some s⟩) finish
        (fun hit => ⟨advance q (some hit), none⟩) reject final hreject hne hh
        (fun _ => hlive) (step_active ctx N start finish input q hlive) ?_
      intro s bit hs
      cases bit <;> cases he : finish s <;>
        simp [M, machine, NondeterministicQueryMachine.step, hlive, hs, he, reject]
    · have henter : M.step input ⟨q, none⟩ true = reject := by
        simp [M, machine, NondeterministicQueryMachine.step, hlive, reject]
      rw [henter, M.replay_of_halted input hreject]
      simp [hne, readRequest, StateT.run]

/-- Interpret the finite round scan with the original input and a stream of selectors.
A result carries the unused suffix, so equality of return values cannot identify occurrences. -/
def replayScan {τ : Type} (ctx : Context) (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool)
    (input bits : List Bool) : Option (RoundUpdate × List Bool) :=
  (scanNextRound
    (fun u v : Fin ctx.size => readRequest N start finish input ctx (.edge u v))
    (fun _ _ v => readRequest N start finish input ctx (.member v))
    ctx.radius ctx.expected).run bits

-- Forget the selector suffix while keeping failure possible.
private def ReturnsOnSuccess {σ α : Type} (run : StateT σ Option α) (value : α) : Prop :=
  ∀ before actual after, run.run before = some (actual, after) → actual = value

private theorem returns_pure {σ α : Type} (value : α) :
    ReturnsOnSuccess (pure value : StateT σ Option α) value :=
  fun _ _ _ h => congrArg Prod.fst (Option.some.inj h).symm

private theorem returns_bind {σ α β : Type} {run : StateT σ Option α}
    {next : α → StateT σ Option β} {a : α} {b : β}
    (hrun : ReturnsOnSuccess run a) (hnext : ReturnsOnSuccess (next a) b) :
    ReturnsOnSuccess (run >>= next) b := by
  intro before actual after h
  change (run.run before).bind (fun p => (next p.1).run p.2) = some (actual, after) at h
  obtain ⟨⟨value, middle⟩, hv, hn⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := hrun before value middle hv
  exact hnext middle actual after hn

private theorem returns_foldlM {σ α : Type} {n : ℕ}
    (step : α → Fin n → StateT σ Option α) (spec : α → Fin n → α) (initial : α)
    (hstep : ∀ a i, ReturnsOnSuccess (step a i) (spec a i)) :
    ReturnsOnSuccess (Fin.foldlM n step initial) (Fin.foldlM (m := Id) n spec initial) := by
  induction n with
  | zero =>
    simp only [Fin.foldlM_zero]
    exact returns_pure initial
  | succ n ih =>
    simp only [Fin.foldlM_succ_last]
    exact returns_bind (ih (fun a i => step a i.castSucc) (fun a i => spec a i.castSucc)
      (fun a i => hstep a i.castSucc)) (hstep _ (Fin.last n))

private theorem replayScan_returns {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input : List Bool)
    (edge : Fin ctx.size → Fin ctx.size → Bool) (member : Fin ctx.size → Bool)
    (hedge : ∀ u v : Fin ctx.size, ∀ bits hit rest,
      N.readReply finish input (start ctx (.edge u v)) bits = some (hit, rest) → hit = edge u v)
    (hmember : ∀ v : Fin ctx.size, ∀ bits hit rest,
      N.readReply finish input (start ctx (.member v)) bits = some (hit, rest) → hit = member v) :
    ReturnsOnSuccess (fun bits => replayScan ctx N start finish input bits)
      (scanNextRound (m := Id) edge (fun _ _ => member) ctx.radius ctx.expected) := by
  let read := readRequest N start finish input ctx
  let E (u v : Fin ctx.size) := read (.edge u v)
  let M (v : Fin ctx.size) := read (.member v)
  have hread (req : Request) (value : Bool)
      (hgood : ∀ bits hit rest, N.readReply finish input (start ctx req) bits =
        some (hit, rest) → hit = value) : ReturnsOnSuccess (read req) value := by
    rintro (_ | ⟨_ | _, bits⟩) hit rest h
    · cases h
    · exact hgood bits hit rest h
    · cases h
  have hE (u v : Fin ctx.size) := hread (.edge u v) (edge u v) (hedge u v)
  have hM (v : Fin ctx.size) := hread (.member v) (member v) (hmember v)
  have hpred (v : Fin ctx.size) : ReturnsOnSuccess (countPredecessors E M v)
      (countPredecessors (m := Id) edge member v) := by
    unfold countPredecessors
    apply returns_foldlM
    intro count u
    unfold predecessorStep
    refine returns_bind (hE u v) ?_
    cases h : edge u v
    · exact returns_pure _
    · refine returns_bind (hM u) ?_
      cases member u <;> exact returns_pure _
  have hstep (a : RoundUpdate) (v : Fin ctx.size) :
      ReturnsOnSuccess (scanVertex E M ctx.radius a v)
        (scanVertex (m := Id) edge member ctx.radius a v) := by
    unfold scanVertex
    refine returns_bind (hM v) ?_
    cases h : member v
    · exact returns_bind (hpred v) (returns_pure _)
    · exact returns_pure _
  change ReturnsOnSuccess (scanNextRound E (fun _ _ => M) ctx.radius ctx.expected) _
  unfold scanNextRound
  exact returns_foldlM _ _ _ hstep

/-- At exact current totals and a unique passing transcript, every successful round replay
returns the exact next tally and reports whether the next passing transcript is unique.
Each successful supplied callback parse must return the corresponding mathematical bit. -/
theorem replayScan_correct {τ : Type} (ctx : Context) (source : Fin ctx.size)
    (r : Fin ctx.size → Fin ctx.size → Prop)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input : List Bool)
    (hexact : ctx.expected = expected r source ctx.radius)
    (hpass : ∃! w, Passes r source ctx.radius w)
    (hedge : ∀ u v : Fin ctx.size, ∀ bits hit rest,
      N.readReply finish input (start ctx (.edge u v)) bits = some (hit, rest) →
        (hit = true ↔ r u v))
    (hmember : ∀ v : Fin ctx.size, ∀ bits hit rest,
      N.readReply finish input (start ctx (.member v)) bits = some (hit, rest) →
        (hit = true ↔ v ∈ round r source ctx.radius))
    {bits rest : List Bool} {update : RoundUpdate}
    (h : replayScan ctx N start finish input bits = some (update, rest)) :
    update.tally = expected r source (ctx.radius + 1) ∧
      (update.bad = false ↔ ∃! w, Passes r source (ctx.radius + 1) w) := by
  classical
  let edge (u v : Fin ctx.size) := decide (r u v)
  let member (v : Fin ctx.size) := decide (v ∈ round r source ctx.radius)
  have he u v bits hit rest h :=
    Bool.eq_iff_iff.mpr (by simpa only [edge, decide_eq_true_eq] using hedge u v bits hit rest h :
      hit = true ↔ edge u v = true)
  have hm v bits hit rest h :=
    Bool.eq_iff_iff.mpr (by simpa only [member, decide_eq_true_eq] using hmember v bits hit rest h :
      hit = true ↔ member v = true)
  have hout := replayScan_returns ctx N start finish input edge member he hm bits update rest h
  obtain ⟨ideal, hideal, htally, hbad⟩ := scanNextRound_correct (m := Id)
    (edge := edge) (member := fun _ _ => member) (fun _ _ => rfl) (fun _ => rfl) hpass
  rw [hout, hexact, hideal]
  exact ⟨htally, hbad⟩

private theorem firstHalting_iff_remaining {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ) (finish : τ → Option Bool)
    (input : List Bool) (update : RoundUpdate) (q : State) (bits : List Bool)
    (hc : q.context = ctx) (hp : PredecessorBounded q) :
    let M := machine ctx N start finish
    (M.FirstHalting input bits ⟨q, none⟩ ∧ answer (M.replay input bits ⟨q, none⟩) = some update) ↔
    (remaining
      (fun u v : Fin ctx.size => readRequest N start finish input ctx (.edge u v))
      (fun v => readRequest N start finish input ctx (.member v))
      (fun _ => none) (fun _ => none) q).run bits = some (update, []) := by
  let M := machine ctx N start finish
  let read := readRequest N start finish input ctx
  let rem := remaining (fun u v : Fin ctx.size => read (.edge u v)) (fun v => read (.member v))
    (fun _ => none) (fun _ => none)
  change (M.FirstHalting input bits ⟨q, none⟩ ∧ answer (M.replay input bits ⟨q, none⟩) =
    some update) ↔ (rem q).run bits = some (update, [])
  induction bits using (measure (List.length : List Bool → ℕ)).wf.induction generalizing q with
  | h bits ih =>
    cases hlive : halted q with
    | false =>
      have he : rem q = (read (request q) >>= fun hit => rem (advance q (some hit))) :=
        remaining_bind read _ _ q (congrArg Context.size hc) hlive hp
      rw [he]
      have hrun (hit : Bool) (rest : List Bool)
          (hr : (read (request q)).run bits = some (hit, rest)) :
          (read (request q) >>= fun hit => rem (advance q (some hit))).run bits =
            (rem (advance q (some hit))).run rest := by
        simpa only [StateT.run, bind, StateT.bind, Option.bind_some] using
          congrArg (fun value => value >>= fun ⟨b, bs⟩ => (rem (advance q (some b))).run bs) hr
      have hnext (hit : Bool) (rest : List Bool)
          (hr : (read (request q)).run bits = some (hit, rest)) :=
        ih rest (readRequest_length_lt N start finish input ctx _ bits rest hit hr)
          (q := advance q (some hit)) ((advance_context _ _).trans hc)
          (advance_predecessorBounded hlive hp _)
      constructor
      · rintro ⟨hf, ha⟩
        let final := M.replay input bits ⟨q, none⟩
        have hsome : (answer final).isSome = true := by simp [final, ha]
        obtain ⟨hit, rest, hr, hf', hfinal⟩ :=
          (successful_request_iff ctx N start finish input q bits final hlive hf.1 hsome).mp
            ⟨hf, rfl⟩
        have hr' : (read (request q)).run bits = some (hit, rest) := by simpa [read, hc] using hr
        rw [hrun hit rest hr']
        exact (hnext hit rest hr').mp ⟨hf', hfinal ▸ ha⟩
      · intro h
        cases hr : (read (request q)).run bits with
        | none =>
          have hrunNone :
              (read (request q) >>= fun hit => rem (advance q (some hit))).run bits = none := by
            change ((read (request q)).run bits >>= _) = none
            rw [hr]
            rfl
          simp [hrunNone] at h
        | some pair =>
          obtain ⟨hit, rest⟩ := pair
          rw [hrun hit rest hr] at h
          obtain ⟨hf, ha⟩ := (hnext hit rest hr).mpr h
          let final := M.replay input rest ⟨advance q (some hit), none⟩
          have hsome : (answer final).isSome = true := by simp [final, ha]
          have hr' :
              (readRequest N start finish input q.context (request q)).run bits =
                some (hit, rest) := by simpa [read, hc] using hr
          obtain ⟨hf', hfinal⟩ :=
            (successful_request_iff ctx N start finish input q bits final hlive hf.1 hsome).mpr
              ⟨hit, rest, hr', hf, rfl⟩
          exact ⟨hf', hfinal.symm ▸ ha⟩
    | true =>
      have hh : M.halted ⟨q, none⟩ = true := hlive
      rw [M.firstHalting_iff_nil_of_halted input bits ⟨q, none⟩ hh, M.replay_of_halted input hh]
      cases hr : q.rejected with
      | true =>
        simp [answer, result, hr, rem, remaining, StateT.run]
      | false =>
        have hge : ctx.size ≤ q.cursor := by simpa [halted, hr, hc] using hlive
        have hrem : rem q = pure q.update := remaining_of_done _ _ _ _ _ hr hge
        rw [hrem]
        simp [answer, result, hr, StateT.run, pure, StateT.pure, and_comm]

/-- A successful first halt is precisely an occurrence of `scanNextRound` that consumes
the entire selector list. The equality identifies its full tally and tie flag. -/
theorem firstHalting_iff_replayScan {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ) (finish : τ → Option Bool)
    (input bits : List Bool) (update : RoundUpdate) :
    (machine ctx N start finish).FirstHalting input bits (entry ctx) ∧
        answer ((machine ctx N start finish).run input bits) = some update ↔
      replayScan ctx N start finish input bits = some (update, []) := by
  have h := firstHalting_iff_remaining ctx N start finish input update (initial ctx) bits rfl
    (by simp [PredecessorBounded, initial])
  rw [remaining_initial ctx _ (fun _ _ v => readRequest N start finish input ctx (.member v))] at h
  exact h

open NondeterministicQueryMachine in
/-- At a sufficient native clock, count exactly the selector lists on which the typed scan
returns a round update and consumes the whole list. Tied updates contribute and rejected
callbacks do not. -/
theorem branchCount_eq_encard_replayScan {α τ : Type}
    {enc : α ↪ List Bool} {S : α → ℕ} {ctx : Context}
    {N : NondeterministicQueryMachine τ} {start : Context → Request → τ}
    {finish : τ → Option Bool} {contextOf : α → Context}
    (R : Routines (machine ctx N start finish) (fun a => entry (contextOf a)) enc S)
    (a : α) {fuel : ℕ} (hclock : R.machine.RunsInTime (enc a) fuel) :
    ((Native.countingMachine R.I R.P R.F R.C).branchCount
      (fun out => decide (out = [true])) fuel (R.machine.initCfg (enc a)) : ℕ∞) =
      {bits : List Bool | ∃ update,
        replayScan (contextOf a) N start finish (enc a) bits = some (update, [])}.encard := by
  rw [R.branchCount_eq_encard_firstHalting a hclock]
  congr 1
  ext bits
  simp only [Set.mem_ofPred_eq, decide_eq_true_eq, List.cons.injEq, and_true]
  change ((machine (contextOf a) N start finish).FirstHalting (enc a) bits (entry (contextOf a)) ∧
    (!((machine (contextOf a) N start finish).run (enc a) bits).controller.rejected) = true) ↔ _
  have he (s : MachineState τ) : (!s.controller.rejected) = true ↔
      ∃ u, answer s = some u := by
    cases h : s.controller.rejected <;> simp [answer, result, h]
  rw [he, ← exists_and_left]
  exact exists_congr (firstHalting_iff_replayScan (contextOf a) N start finish (enc a) bits)

private def ScalarBounds (ctx : Context) (q : State) : Prop :=
  q.context = ctx ∧ q.cursor ≤ ctx.size ∧
    q.update.tally.count ≤ ctx.expected.count + q.cursor ∧
    q.update.tally.lengthSum ≤ ctx.expected.lengthSum + q.cursor * (ctx.radius + 1) ∧
    PredecessorBounded q

private theorem step_scalarBounds {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input : List Bool) (q : MachineState τ) (choice : Bool)
    (hq : ScalarBounds ctx q.controller) :
    ScalarBounds ctx ((machine ctx N start finish).step input q choice).controller := by
  by_cases hs : halted q.controller = true
  · rw [(machine ctx N start finish).step_of_halted input hs]
    exact hq
  have hlive := Bool.eq_false_iff.mpr hs
  have hadv (reply : Option Bool) : ScalarBounds ctx (advance q.controller reply) := by
    obtain ⟨hc, _, ht, hl, hp⟩ := hq
    rw [← hc] at ht hl ⊢
    obtain ⟨ht', hl'⟩ := advance_tally_bounds reply ht hl
    exact ⟨advance_context _ _, advance_cursor_le hlive reply, ht', hl',
      advance_predecessorBounded hlive hp reply⟩
  obtain ⟨state, callee⟩ := q
  change halted state = false at hlive
  cases callee with
  | none =>
    cases choice
    · simpa [NondeterministicQueryMachine.step, machine, hlive] using hq
    · simpa [NondeterministicQueryMachine.step, machine, hlive] using hadv none
  | some callee =>
    cases hc : N.halted callee
    · simpa [NondeterministicQueryMachine.step, machine, hlive, hc] using hq
    · cases choice
      · simpa [NondeterministicQueryMachine.step, machine, hlive, hc] using hadv (finish callee)
      · simpa [NondeterministicQueryMachine.step, machine, hlive, hc] using hadv none

private theorem run_scalarInvariant {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input choices : List Bool) :
    ScalarBounds ctx ((machine ctx N start finish).run input choices).controller := by
  have replay_bounds (bits : List Bool) (q : MachineState τ) (hq : ScalarBounds ctx q.controller) :
      ScalarBounds ctx ((machine ctx N start finish).replay input bits q).controller := by
    induction bits generalizing q with
    | nil => exact hq
    | cons b bits ih =>
      rw [NondeterministicQueryMachine.replay_cons]
      exact ih _ (step_scalarBounds ctx N start finish input q b hq)
  exact replay_bounds choices _ (by
    simp [ScalarBounds, PredecessorBounded, machine, entry, initial])

/-- Every selector prefix retains the original context and bounds the cursor and tally.
These bounds also apply when a selector or callback rejects. -/
theorem run_scalar_bounds {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input choices : List Bool) :
    let q := ((machine ctx N start finish).run input choices).controller
    q.context = ctx ∧ q.cursor ≤ ctx.size ∧
      q.update.tally.count ≤ ctx.expected.count + q.cursor ∧
      q.update.tally.lengthSum ≤ ctx.expected.lengthSum + q.cursor * (ctx.radius + 1) := by
  obtain ⟨hc, hcursor, hcount, hsum, _⟩ := run_scalarInvariant ctx N start finish input choices
  exact ⟨hc, hcursor, hcount, hsum⟩

/-- On every branch any retained predecessor state has bounded cursor and count and belongs
to the current outer vertex. -/
theorem run_predecessor_bounds {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input choices : List Bool) :
    let q := ((machine ctx N start finish).run input choices).controller
    ∀ p : Predecessor.State, p ∈ q.predecessor →
      p.context = ⟨ctx.size, ctx.source, q.cursor, ctx.radius, ctx.expected⟩ ∧
      Predecessor.Bounded p ∧ Predecessor.halted p = false := by
  obtain ⟨hc, _, _, _, hp⟩ := run_scalarInvariant ctx N start finish input choices
  dsimp only
  intro p hmem
  simpa only [predecessorContext, hc] using hp p hmem

/-- Space for the encoded round caller, including its context, tally and suspended predecessor. -/
@[expose] def callerStateBound (ctx : Context) : ℕ :=
  let B := Nat.log2 ctx.size + 1
  let V := max (ctx.expected.count + ctx.size)
    (ctx.expected.lengthSum + ctx.size * (ctx.radius + 1))
  6 * (encContext ctx).length + 18 * B + 12 * (Nat.log2 (V * V) + 1) + 33

/-- The framed caller and a fully encoded callee of length at most `D`. -/
@[expose] def roundStateBound (ctx : Context) (D : ℕ) : ℕ :=
  2 * callerStateBound ctx + D + 2

/-- The caller workspace charges its context, the finite indices, and the binary tally
envelope. The bound includes an active predecessor loop and also holds after rejection. -/
theorem length_encState_run_le {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input choices : List Bool) :
    let q := ((machine ctx N start finish).run input choices).controller
    (encState q).length ≤ callerStateBound ctx := by
  intro q
  let B := Nat.log2 ctx.size + 1
  let V := max (ctx.expected.count + ctx.size)
    (ctx.expected.lengthSum + ctx.size * (ctx.radius + 1))
  change (encState q).length ≤
    6 * (encContext ctx).length + 18 * B + 12 * (Nat.log2 (V * V) + 1) + 33
  obtain ⟨hc, hcursor, hcount, hsum, hp⟩ := run_scalarInvariant ctx N start finish input choices
  change q.context = ctx at hc
  change q.cursor ≤ ctx.size at hcursor
  change PredecessorBounded q at hp
  have hi : (encNat q.cursor).length ≤ B := length_encNat_le_log2 hcursor
  have hcount' : q.update.tally.count ≤ V :=
    hcount.trans ((Nat.add_le_add_left hcursor _).trans (le_max_left _ _))
  have hsq : V ≤ V * V := by cases V <;> simp
  have hsum' : q.update.tally.lengthSum ≤ V * V :=
    hsum.trans ((Nat.add_le_add_left (Nat.mul_le_mul_right _ hcursor) _).trans
      ((le_max_right _ _).trans hsq))
  have hupdate := length_encRoundUpdate_le hcount' hsum'
  have hpred : ((encOption Predecessor.encState) q.predecessor).length ≤
      2 * (encContext ctx).length + 8 * B + 10 := by
    cases hq : q.predecessor with
    | none => simp [encOption_none]
    | some p =>
      obtain ⟨hctx, hb, _⟩ := hp p (by simp only [hq, Option.mem_some_iff])
      have hctxLen : (Predecessor.encContext p.context).length ≤
          (encContext ctx).length + 2 * B + 1 := by
        rw [hctx]
        simp only [predecessorContext, hc, Predecessor.encContext_apply,
          Predecessor.encContextFields, encContext_apply, encContextFields, length_encPair]
        omega
      have h := Predecessor.length_encState_le hb
      have hn : p.context.size = ctx.size := by simp [hctx, predecessorContext, hc]
      rw [hn] at h
      rw [encOption_some, List.length_cons]
      omega
  simp only [encState_apply, encStateFields, length_encPair, encBool_apply, List.length_singleton]
  rw [hc]
  omega

private theorem request_inRange {q : State} (hlive : halted q = false)
    (hp : PredecessorBounded q) : (request q).InRange q.context.size := by
  have hi : q.cursor < q.context.size := by
    simpa using (Bool.or_eq_false_iff.mp hlive).2
  cases hq : q.predecessor with
  | none => simpa only [request, hq, Request.InRange] using hi
  | some p =>
    obtain ⟨hctx, _, hplive⟩ := hp p (by simp [hq])
    have hj : p.cursor < p.context.size := by
      simpa using (Bool.or_eq_false_iff.mp hplive).2
    rw [hctx] at hj
    change p.cursor < q.context.size at hj
    cases hphase : p.memberPhase
    · simpa only [request, hq, hphase, Bool.false_eq_true, ite_false, Request.InRange] using
        And.intro hj hi
    · simpa only [request, hq, hphase, ite_true, Request.InRange] using hj

/-- A round has at most one successful first-halting selector list when every in-range request
has at most one first-halting callback trace with a reply. A tied update still counts as success. -/
theorem subsingleton_successful_firstHalting {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input : List Bool)
    (hrequest : ∀ req, req.InRange ctx.size →
      {bits : List Bool | N.FirstHalting input bits (start ctx req) ∧
        (finish (N.replay input bits (start ctx req))).isSome}.Subsingleton) :
    let M := machine ctx N start finish
    {bits : List Bool | M.FirstHalting input bits M.init ∧
      (answer (M.run input bits)).isSome}.Subsingleton := by
  let M := machine ctx N start finish
  have aux (left right : List Bool) (q : State) (hctx : q.context = ctx)
      (hp : PredecessorBounded q)
      (hl : M.FirstHalting input left ⟨q, none⟩ ∧
        (answer (M.replay input left ⟨q, none⟩)).isSome)
      (hr : M.FirstHalting input right ⟨q, none⟩ ∧
        (answer (M.replay input right ⟨q, none⟩)).isSome) :
      left = right := by
    induction left using (measure (List.length : List Bool → ℕ)).wf.induction
      generalizing q right with
    | h left ih =>
      cases hh : halted q with
      | true =>
        exact ((M.firstHalting_iff_nil_of_halted input _ ⟨q, none⟩ hh).mp hl.1).trans
          ((M.firstHalting_iff_nil_of_halted input _ ⟨q, none⟩ hh).mp hr.1).symm
      | false =>
        obtain ⟨hit, suffix, hlread, hlf, hlend⟩ :=
          (successful_request_iff ctx N start finish input q left _ hh hl.1.1 hl.2).mp
            ⟨hl.1, rfl⟩
        obtain ⟨hit', suffix', hrread, hrf, hrend⟩ :=
          (successful_request_iff ctx N start finish input q right _ hh hr.1.1 hr.2).mp
            ⟨hr.1, rfl⟩
        have hlen := readRequest_length_lt N start finish input q.context (request q)
          left suffix hit hlread
        have hv := request_inRange hh hp
        rw [hctx] at hv
        obtain ⟨l, hlentry, hlreply⟩ :=
          readRequest_of_success N start finish input q.context _ _ _ _ hlread
        obtain ⟨r, hrentry, hrreply⟩ :=
          readRequest_of_success N start finish input q.context _ _ _ _ hrread
        rw [hctx] at hlreply hrreply
        obtain ⟨callBits, hlsplit, hrsplit, _, rfl⟩ :=
          N.readReply_commonPrefix finish input (start ctx (request q))
            (hrequest (request q) hv) hlreply hrreply
        have hs : suffix = suffix' :=
          ih suffix hlen suffix' (advance q (some hit)) ((advance_context _ _).trans hctx)
            (advance_predecessorBounded hh hp _) ⟨hlf, hlend ▸ hl.2⟩ ⟨hrf, hrend ▸ hr.2⟩
        rw [hlentry, hrentry, hlsplit, hrsplit, hs]
  change {bits : List Bool | M.FirstHalting input bits M.init ∧
    (answer (M.run input bits)).isSome}.Subsingleton
  intro left hl right hr
  exact aux left right (initial ctx) rfl (by simp [PredecessorBounded, initial]) hl hr

/-- Every suspended callee came from an in-range request on the original round context and input. -/
theorem run_callee_replay {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input choices : List Bool) :
    ∀ t ∈ ((machine ctx N start finish).run input choices).callee,
      ∃ req bits, req.InRange ctx.size ∧ N.replay input bits (start ctx req) = t := by
  let M := machine ctx N start finish
  change ∀ t ∈ (M.run input choices).callee, _
  induction choices using List.reverseRecOn with
  | nil =>
    simp [M, NondeterministicQueryMachine.run, machine, entry]
  | append_singleton pre choice ih =>
    rw [NondeterministicQueryMachine.run_append, NondeterministicQueryMachine.replay_cons,
      NondeterministicQueryMachine.replay_nil]
    let p := M.run input pre
    obtain ⟨hctx, _, _, _, hpre⟩ := run_scalarInvariant ctx N start finish input pre
    change p.controller.context = ctx at hctx
    change ∀ t ∈ (M.step input p choice).callee, _
    change ∀ t ∈ p.callee, _ at ih
    by_cases hh : M.halted p = true
    · rwa [M.step_of_halted input hh]
    have hlive : halted p.controller = false := Bool.eq_false_iff.mpr hh
    cases hs : p.callee with
    | none =>
      cases choice
      · intro t ht
        simp only [M, NondeterministicQueryMachine.step, machine, hlive, hs,
          Bool.false_eq_true, ite_false, Option.mem_some_iff] at ht
        have hv := request_inRange hlive hpre
        exact ⟨request p.controller, [], hctx ▸ hv, by
          simpa only [NondeterministicQueryMachine.replay_nil, ← hctx] using ht⟩
      · simp [M, NondeterministicQueryMachine.step, machine, hlive, hs]
    | some s =>
      cases hhalt : N.halted s
      · intro t ht
        simp only [M, NondeterministicQueryMachine.step, NondeterministicQueryMachine.read,
          machine, hlive, hs, hhalt, Bool.false_eq_true, ite_false, Option.mem_some_iff] at ht
        obtain ⟨req, bits, hv, hb⟩ := ih s (by simp [hs])
        refine ⟨req, bits ++ [choice], hv, ?_⟩
        rw [NondeterministicQueryMachine.replay_append, hb]
        simpa [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read,
          NondeterministicQueryMachine.replay_cons, hhalt] using ht
      · cases choice <;> simp [M, NondeterministicQueryMachine.step, machine, hlive, hs, hhalt]

/-- The complete machine state charges the scalar round envelope and an all-prefix bound for
the supplied same-input callbacks. The bound covers rejected selectors and replies. -/
theorem length_encMachineState_run_le {τ : Type} (encT : τ ↪ List Bool) (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input choices : List Bool) (D : ℕ)
    (hcallee : ∀ req, req.InRange ctx.size → ∀ bits,
      (encT (N.replay input bits (start ctx req))).length ≤ D) :
    (encMachineState τ encT ((machine ctx N start finish).run input choices)).length ≤
      roundStateBound ctx D := by
  apply length_encMachineState_le
  · exact length_encState_run_le ctx N start finish input choices
  · intro t ht
    obtain ⟨req, bits, hv, rfl⟩ := run_callee_replay ctx N start finish input choices t ht
    exact hcallee req hv bits

private def remainingReplies (q : State) : ℕ :=
  if halted q then 0 else
    let block := 2 * q.context.size + 1
    (q.context.size - q.cursor) * block +
      q.predecessor.elim block Predecessor.remainingCalls

private theorem remainingReplies_pos {q : State} (hlive : halted q = false) :
    0 < remainingReplies q := by
  have hi : q.cursor < q.context.size := by
    simp only [halted, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hlive
    exact hlive.2
  have hp : 0 < (q.context.size - q.cursor) * (2 * q.context.size + 1) :=
    Nat.mul_pos (Nat.sub_pos_of_lt hi) (by omega)
  simp only [remainingReplies, hlive, Bool.false_eq_true, ite_false]
  omega

private theorem remainingReplies_advance_lt {q : State} (hp : PredecessorBounded q)
    (hlive : halted q = false) (reply : Option Bool) :
    remainingReplies (advance q reply) < remainingReplies q := by
  by_cases hhalt : halted (advance q reply) = true
  · simpa only [remainingReplies, hhalt, ite_true] using remainingReplies_pos hlive
  have hn := Bool.eq_false_iff.mpr hhalt
  have hi : q.cursor < q.context.size := by
    simp only [halted, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hlive
    exact hlive.2
  have hshift :
      (q.context.size - (q.cursor + 1)) * (2 * q.context.size + 1) +
        (2 * q.context.size + 1) = (q.context.size - q.cursor) * (2 * q.context.size + 1) := by
    rw [← Nat.add_one_mul, show q.context.size - (q.cursor + 1) + 1 =
      q.context.size - q.cursor by omega]
  simp only [remainingReplies, hlive, hn, Bool.false_eq_true, ite_false, advance_context]
  cases reply with
  | none => simp [halted, advance] at hn
  | some hit =>
    cases hq : q.predecessor with
    | none =>
      cases hit
      · simp [advance, hq, Predecessor.remainingCalls_initial]
      · simp [advance, hq, hshift]
    | some p =>
      obtain ⟨hctx, _, hl⟩ := hp p (by simp [hq])
      by_cases hf : Predecessor.halted (Predecessor.advance p (some hit)) = true
      · have hpos := Predecessor.remainingCalls_pos hl
        simp [advance, hq, hf, hshift, hpos]
      · have hlt := Predecessor.advance_progress hl (some hit) (Bool.eq_false_iff.mpr hf)
        simpa [advance, hq, hf] using hlt

private theorem advance_some_not_rejected (q : State) (hit : Bool)
    (h : q.rejected = false) : (advance q (some hit)).rejected = false := by
  cases hp : q.predecessor with
  | none => cases hit <;> simp [advance, hp, h]
  | some p =>
    simp only [advance, hp]
    split <;> exact h

/-- If every in-range callback has a successful first-halt trace, the round has one too.
A tied round update is a successful reply. -/
theorem exists_successful_firstHalting {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input : List Bool)
    (hrequest : ∀ req, req.InRange ctx.size → ∃ callBits hit,
      N.FirstHalting input callBits (start ctx req) ∧
        finish (N.replay input callBits (start ctx req)) = some hit) :
    let M := machine ctx N start finish
    ∃ bits update, M.FirstHalting input bits M.init ∧
      answer (M.run input bits) = some update := by
  let M := machine ctx N start finish
  have aux (q : State) (hctx : q.context = ctx) (hp : PredecessorBounded q)
      (hvalid : q.rejected = false) :
      ∃ bits update, M.FirstHalting input bits ⟨q, none⟩ ∧
        answer (M.replay input bits ⟨q, none⟩) = some update := by
    induction q using (measure remainingReplies).wf.induction with
    | h q ih =>
      cases hlive : halted q with
      | true =>
        have hfirst := (M.firstHalting_iff_nil_of_halted input [] ⟨q, none⟩ hlive).mpr rfl
        exact ⟨[], q.update, hfirst, by simp [answer, result, hvalid]⟩
      | false =>
        have hreq := request_inRange hlive hp
        rw [hctx] at hreq
        obtain ⟨callBits, hit, hfirst, hreply⟩ := hrequest (request q) hreq
        let next := advance q (some hit)
        obtain ⟨rest, update, hrest, hanswer⟩ :=
          ih next (remainingReplies_advance_lt hp hlive _)
            ((advance_context _ _).trans hctx) (advance_predecessorBounded hlive hp _)
            (advance_some_not_rejected q hit hvalid)
        let bits := false :: (callBits ++ false :: rest)
        have hread : (readRequest N start finish input q.context (request q)).run bits =
            some (hit, rest) := by
          change N.readReply finish input (start q.context (request q))
            (callBits ++ false :: rest) = some (hit, rest)
          rw [hctx]
          exact (N.readReply_iff finish input _ _ _ _).mpr ⟨callBits, rfl, hfirst, hreply⟩
        have hsome : (answer (M.replay input rest ⟨next, none⟩)).isSome = true := by
          rw [hanswer]
          rfl
        obtain ⟨hfull, hfinal⟩ :=
          (successful_request_iff ctx N start finish input q bits _ hlive hrest.1 hsome).mpr
            ⟨hit, rest, hread, hrest, rfl⟩
        exact ⟨bits, update, hfull, hfinal.symm ▸ hanswer⟩
  exact aux (initial ctx) rfl (by simp [PredecessorBounded, initial]) rfl

/-- A common clock for the round, charging the maximum number of requests and their routing. -/
@[expose] def roundClock (size clock : ℕ) : ℕ :=
  (size + 1) * (2 * size + 1) * (clock + 2) + (clock + 1)

/-- The common round clock charges every callback selector and both deterministic routing
steps. The bound holds for rejecting replies and noncanonical selectors as well. -/
theorem haltsWithin {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ)
    (finish : τ → Option Bool) (input : List Bool) (clock : ℕ)
    (hclock : ∀ req, req.InRange ctx.size → N.HaltsFrom input (start ctx req) clock) :
    (machine ctx N start finish).HaltsWithin input (roundClock ctx.size clock) := by
  let M := machine ctx N start finish
  let rank (q : MachineState τ) :=
    if halted q.controller then 0 else remainingReplies q.controller * (clock + 2) +
      q.callee.elim (clock + 1) (N.remainingSteps input)
  have hpos (q : MachineState τ) (h : M.halted q = false) : 0 < rank q := by
    change halted q.controller = false at h
    have := Nat.mul_pos (remainingReplies_pos h) (show 0 < clock + 2 by omega)
    simp only [rank, h, Bool.false_eq_true, ite_false]
    omega
  have hadvance (pre : List Bool) (choice : Bool) (hlive : M.halted (M.run input pre) = false) :
      rank (M.step input (M.run input pre) choice) < rank (M.run input pre) := by
    let q := M.run input pre
    change halted q.controller = false at hlive
    obtain ⟨hctx, _, _, _, hpre⟩ := run_scalarInvariant ctx N start finish input pre
    change q.controller.context = ctx at hctx
    change PredecessorBounded q.controller at hpre
    have hreturn (r : Option Bool) :
        rank ⟨advance q.controller r, none⟩ < rank q := by
      by_cases hh : halted (advance q.controller r) = true
      · simpa only [rank, hh, ite_true] using hpos q hlive
      · have hlt := remainingReplies_advance_lt hpre hlive r
        have hm := Nat.mul_le_mul_right (clock + 2) (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at hm
        simp only [rank, hh, ite_false, hlive, Bool.false_eq_true, Option.elim_none]
        omega
    change rank (M.step input q choice) < rank q
    cases hq : q.callee with
    | none =>
      cases choice
      · have hv := request_inRange hlive hpre
        rw [hctx] at hv
        have hcallee := N.remainingSteps_le input (hclock (request q.controller) hv)
        simpa [rank, M, NondeterministicQueryMachine.step, machine, hlive, hq, hctx] using
          Nat.lt_succ_of_le hcallee
      · simpa [M, NondeterministicQueryMachine.step, machine, hlive, hq] using hreturn none
    | some s =>
      cases hs : N.halted s
      · have hm : s ∈ (M.run input pre).callee := by
          change s ∈ q.callee
          simp [hq]
        obtain ⟨req, bits, hv, hbits⟩ := run_callee_replay ctx N start finish input pre s hm
        have hr : (N.withInit (start ctx req)).Reachable input s :=
          ⟨bits, by rw [NondeterministicQueryMachine.run_withInit, hbits]⟩
        have ht : N.HaltsFrom input s clock := by
          intro bits' hlen
          have hstart : (N.withInit (start ctx req)).HaltsWithin input clock := by
            intro coins hc
            change N.halted ((N.withInit (start ctx req)).run input coins) = true
            rw [NondeterministicQueryMachine.run_withInit]
            exact hclock req hv coins hc
          exact (N.withInit (start ctx req)).haltsFrom_of_reachable input hstart hr bits' hlen
        have hlt := N.remainingSteps_step_lt input ⟨clock, ht⟩ hs choice
        simpa [rank, M, NondeterministicQueryMachine.step, NondeterministicQueryMachine.read,
          machine, hlive, hq, hs] using hlt
      · cases choice
        · simpa [M, NondeterministicQueryMachine.step, machine, hlive, hq, hs] using
            hreturn (finish s)
        · simpa [M, NondeterministicQueryMachine.step, machine, hlive, hq, hs] using hreturn none
  have hbound (bits : List Bool) (h : M.halted (M.run input bits) = false) :
      rank (M.run input bits) + bits.length ≤ rank M.init := by
    induction bits using List.reverseRecOn with
    | nil => simp [NondeterministicQueryMachine.run]
    | append_singleton pre choice ih =>
      have hrun : M.run input (pre ++ [choice]) = M.step input (M.run input pre) choice := by
        rw [NondeterministicQueryMachine.run_append, NondeterministicQueryMachine.replay_cons,
          NondeterministicQueryMachine.replay_nil]
      rw [hrun] at h
      have hlive : M.halted (M.run input pre) = false := by
        cases hh : M.halted (M.run input pre)
        · rfl
        · rw [M.step_of_halted input hh, hh] at h
          contradiction
      have hind := ih hlive
      have hstep := hadvance pre choice hlive
      rw [hrun, List.length_append, List.length_singleton]
      omega
  have hinit : rank M.init ≤ roundClock ctx.size clock := by
    unfold roundClock
    by_cases h : ctx.size = 0
    · simp [rank, M, machine, entry, initial, halted, h]
    · simp [rank, M, machine, entry, initial, halted, h, remainingReplies,
        Nat.add_mul, Nat.mul_add, Nat.add_assoc]
      omega
  intro bits hlen
  by_contra hh
  have hlive := Bool.eq_false_iff.mpr hh
  have hp := hpos (M.run input bits) hlive
  have hb := hbound bits hlive
  omega

end Turing.DoubleCounting.SourceRound
