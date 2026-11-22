/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRound
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Source controller resources with the supplied single-round machine

The loop keeps a binary radius and tally. Each round enters the same transition machine
with the current registers and runs it on the original input. The scalar invariant makes
the round and final membership envelopes available at every entry reached by the loop.
The compiler combines native certificates for both callbacks with a common state budget.
-/

public section

namespace Turing.DoubleCounting.SourceRoundLoop

open Cslib.DoubleCounting MultiTapeTM ComputableInSpace NondeterministicQueryMachine

variable {κ τ μ : Type}

/-- A single round uses the retained graph size and source and the loop's current tally. -/
@[expose] def roundContext (size source : κ → ℕ) (r : Registers κ) : SourceRound.Context :=
  ⟨size r.context, source r.context, r.radius, r.tally⟩

/-- Read the round arguments in workspace linear in the suspended loop registers. -/
theorem roundContext_inSpace (size source : κ → ℕ) (encContext : κ ↪ List Bool)
    (hsize : ComputableInSpace size encContext encNat (fun c => (encContext c).length))
    (hsource : ComputableInSpace source encContext encNat (fun c => (encContext c).length)) :
    ComputableInSpace (roundContext size source) (encRegisters encContext)
      SourceRound.encContext (fun r => (encRegisters encContext r).length) := by
  have hr := budget_id (enc := encRegisters encContext) (.refl _)
  have hc := encRegisters_context_budget encContext hr
  exact SourceRound.encContext_mk_budget (budget_comp_linear hsize hc)
    (budget_comp_linear hsource hc) (encRegisters_radius_budget encContext hr)
    (encRegisters_tally_budget encContext hr)

/-- Prepare the source-round entry in workspace linear in the suspended loop registers. -/
theorem roundEntry_inSpace (size source : κ → ℕ) (encContext : κ ↪ List Bool)
    (encCallee : τ ↪ List Bool)
    (hsize : ComputableInSpace size encContext encNat (fun c => (encContext c).length))
    (hsource : ComputableInSpace source encContext encNat (fun c => (encContext c).length)) :
    ComputableInSpace (fun r => SourceRound.entry (roundContext size source r))
      (encRegisters encContext) (SourceRound.encMachineState τ encCallee)
      (fun r => (encRegisters encContext r).length) :=
  budget_comp_linear (SourceRound.entry_inSpace encCallee)
    (roundContext_inSpace size source encContext hsize hsource)

/-- Reachable scalar loop boundaries have the original context and polynomial count and sum. -/
@[expose] def Admissible (context : κ) (size limit : ℕ) (r : Registers κ) : Prop :=
  r.context = context ∧ r.fuel + r.radius = limit ∧
    r.tally.count ≤ 1 + r.radius * size ∧ r.tally.lengthSum ≤ size * r.radius * r.radius

/-- The initial registers satisfy the scalar loop invariant. -/
theorem start_admissible (context : κ) (size limit : ℕ) :
    Admissible context size limit (start context limit) := by
  simp [Admissible, start]

private theorem admissible_caps {context : κ} {size limit : ℕ} {r : Registers κ}
    (hr : Admissible context size limit r) :
    r.fuel ≤ limit ∧ r.radius ≤ limit ∧
      r.tally.count ≤ 1 + limit * size ∧ r.tally.lengthSum ≤ size * limit * limit := by
  obtain ⟨_, htotal, hcount, hsum⟩ := hr
  have hk : r.radius ≤ limit := by omega
  exact ⟨by omega, hk,
    hcount.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _),
    hsum.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hk) hk)⟩

/-- Encoded workspace for the retained context, loop fuel, radius and current tally. -/
def registerStateBound (encContext : κ ↪ List Bool) (context : κ) (size limit : ℕ) : ℕ :=
  2 * (encContext context).length + 4 * (encNat limit).length +
    2 * (encNat (1 + limit * size)).length + (encNat (size * limit * limit)).length + 4

/-- The retained registers fit the envelope on every admissible boundary. -/
theorem length_encRegisters_le (encContext : κ ↪ List Bool) {context : κ} {size limit : ℕ}
    {r : Registers κ} (hr : Admissible context size limit r) :
    (encRegisters encContext r).length ≤ registerStateBound encContext context size limit := by
  obtain ⟨hf, hk, hc, hs⟩ := admissible_caps hr
  have hf' := length_encNat_mono hf
  have hk' := length_encNat_mono hk
  have hc' := length_encNat_mono hc
  have hs' := length_encNat_mono hs
  simp only [encRegisters_apply, encRegistersFields, encTally_apply, encTallyFields,
    length_encPair, registerStateBound, hr.1]
  omega

/-- A scalar round's returned update fits the loop's tally, radius and fuel invariant. -/
theorem admissible_advance_of_round_answer (size source : κ → ℕ)
    (callee : NondeterministicQueryMachine τ)
    (calleeStart : SourceRound.Context → SourceRound.Request → τ)
    (calleeReply : τ → Option Bool) {context : κ} {limit : ℕ} {r : Registers κ}
    (hr : Admissible context (size context) limit r) (hpositive : 0 < r.fuel)
    (input bits : List Bool) {a : RoundUpdate}
    (hanswer : SourceRound.answer ((SourceRound.machine (roundContext size source r)
      callee calleeStart calleeReply).run input bits) = some a) :
    Admissible context (size context) limit (r.advance a.tally) := by
  let ctx := roundContext size source r
  let M := SourceRound.machine ctx callee calleeStart calleeReply
  have hscalar := SourceRound.run_scalar_bounds ctx callee calleeStart calleeReply input bits
  change (M.run input bits).controller.context = ctx ∧ _ at hscalar
  obtain ⟨_, hcursor, hcount, hsum⟩ := hscalar
  have hu : (M.run input bits).controller.update = a := by
    simp only [SourceRound.answer, SourceRound.result] at hanswer
    split at hanswer
    · cases hanswer
    · exact Option.some.inj hanswer
  rw [hu] at hcount hsum
  obtain ⟨hcontext, hfuel, hc, hs⟩ := hr
  have hdim : ctx.size = size context := congrArg size hcontext
  have hcursor' : (M.run input bits).controller.cursor ≤ size context :=
    hcursor.trans_eq hdim
  have hcount' : a.tally.count ≤ r.tally.count + size context := hcount.trans
    (Nat.add_le_add_left hcursor' _)
  have hsum' : a.tally.lengthSum ≤ r.tally.lengthSum + size context * (r.radius + 1) := by
    exact hsum.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcursor') _)
  refine ⟨hcontext, ?_, ?_, ?_⟩
  · simp only [Registers.advance]
    omega
  · simp only [Registers.advance]
    nlinarith
  · simp only [Registers.advance]
    nlinarith

section Composition

variable (size source : κ → ℕ)
  (callee : NondeterministicQueryMachine τ)
  (calleeStart : SourceRound.Context → SourceRound.Request → τ)
  (calleeReply : τ → Option Bool) (context : κ) (limit : ℕ)

local notation "entryRound" => fun r => SourceRound.entry (roundContext size source r)
local notation "singleRound" => SourceRound.machine (roundContext size source (start context limit))
  callee calleeStart calleeReply

/-- A source loop with the supplied single-round machine and final membership callback. -/
@[expose] def withSourceRound (member : NondeterministicQueryMachine μ)
    (memberStart : Registers κ → μ)
    (memberReply : μ → Option Bool) :
    NondeterministicQueryMachine (State κ (SourceRound.MachineState τ) μ) :=
  machine (start context limit) (singleRound) (entryRound) SourceRound.answer
    member memberStart memberReply

private theorem singleRound_withInit (r : Registers κ) :
    (singleRound).withInit ((entryRound) r) =
      SourceRound.machine (roundContext size source r) callee calleeStart calleeReply :=
  SourceRound.machine_withInit _ _ callee calleeStart calleeReply

/-- The checked scalar round bounds preserve the outer invariant on continuing replies. -/
theorem admissible_closed (input : List Bool) :
    Closed (singleRound) (entryRound) SourceRound.answer input
      (Admissible context (size context) limit) := by
  intro r hr hpositive bits a _ hanswer _ _
  have hreentry := singleRound_withInit size source callee calleeStart calleeReply context limit r
  rw [← run_withInit, hreentry] at hanswer
  exact admissible_advance_of_round_answer size source callee calleeStart calleeReply
    hr hpositive input bits hanswer

/-- Compose the concrete source-round clock with the final membership clock on all branches.
The round callback only receives requests in range for the retained dimension. -/
theorem withSourceRound_haltsWithin (member : NondeterministicQueryMachine μ)
    (memberStart : Registers κ → μ) (memberReply : μ → Option Bool) (input : List Bool)
    (callbackClock memberClock : ℕ)
    (hcall : ∀ r, Admissible context (size context) limit r → ∀ req,
      req.InRange (size r.context) →
      callee.HaltsFrom input (calleeStart (roundContext size source r) req) callbackClock)
    (hmember : ∀ r, Admissible context (size context) limit r →
      (member.withInit (memberStart r)).HaltsWithin input memberClock) :
    (withSourceRound size source callee calleeStart calleeReply context limit
      member memberStart memberReply).HaltsWithin input
      (limit * (SourceRound.roundClock (size context) callbackClock + 1) + memberClock + 1) := by
  apply haltsWithin _ _ _ _ _ _ _ _
    (Admissible context (size context) limit)
    (start_admissible context (size context) limit)
    (admissible_closed size source callee calleeStart calleeReply context limit input)
    (SourceRound.roundClock (size context) callbackClock) memberClock _ hmember
  intro r hr
  rw [singleRound_withInit]
  have h := SourceRound.haltsWithin (roundContext size source r) callee calleeStart calleeReply
    input callbackClock (hcall r hr)
  simpa only [roundContext, hr.1] using h

private theorem roundStateBound_le (r : Registers κ)
    (hr : Admissible context (size context) limit r) (calleeBound : ℕ) :
    SourceRound.roundStateBound (roundContext size source r) calleeBound ≤
      SourceRound.roundStateBound ⟨size context, source context, limit,
        ⟨1 + limit * size context, size context * limit * limit⟩⟩ calleeBound := by
  obtain ⟨_, hk, hc, hs⟩ := admissible_caps hr
  let n := size context
  have hk' := length_encNat_mono hk
  have hc' := length_encNat_mono hc
  have hs' := length_encNat_mono hs
  have hv : max (r.tally.count + n) (r.tally.lengthSum + n * (r.radius + 1)) ≤
      max (1 + limit * n + n) (n * limit * limit + n * (limit + 1)) :=
    max_le_max (Nat.add_le_add_right hc _)
      (Nat.add_le_add hs (Nat.mul_le_mul_left _ (Nat.add_le_add_right hk _)))
  have hl := Nat.log_mono_right (b := 2) (Nat.mul_le_mul hv hv)
  simp only [n, ← Nat.log2_eq_log_two] at hl
  simp only [SourceRound.roundStateBound, SourceRound.callerStateBound, roundContext, hr.1,
    SourceRound.encContext_apply, SourceRound.encContextFields, encTally_apply, encTallyFields,
    length_encPair]
  omega

/-- Compose the single-round state envelope with the retained loop and membership states.
The round callback workspace bound is needed only for in-range requests. -/
theorem withSourceRound_length_run_le (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool)
    (encMember : μ ↪ List Bool) (member : NondeterministicQueryMachine μ)
    (memberStart : Registers κ → μ) (memberReply : μ → Option Bool) (input : List Bool)
    (calleeBound memberBound : ℕ)
    (hcallee : ∀ r, Admissible context (size context) limit r → ∀ req,
      req.InRange (size r.context) → ∀ bits,
      (encCallee (callee.replay input bits (calleeStart (roundContext size source r) req))).length ≤
        calleeBound)
    (hmember : ∀ r, Admissible context (size context) limit r → ∀ bits,
      (encMember (member.replay input bits (memberStart r))).length ≤ memberBound)
    (bits : List Bool) :
    (encState encContext (SourceRound.encMachineState τ encCallee) encMember
      ((withSourceRound size source callee calleeStart calleeReply context limit
        member memberStart memberReply).run input bits)).length ≤
      2 * registerStateBound encContext context (size context) limit +
        max (SourceRound.roundStateBound ⟨size context, source context, limit,
          ⟨1 + limit * size context, size context * limit * limit⟩⟩ calleeBound) memberBound +
        (encNat limit).length + 4 := by
  apply length_run_le _ _ _ _ _ _ _ _ _ _ _
    (Admissible context (size context) limit)
    (start_admissible context (size context) limit)
    (admissible_closed size source callee calleeStart calleeReply context limit input)
    _ _ memberBound (fun _ hr => length_encRegisters_le encContext hr) _ hmember
  intro r hr choices
  rw [← run_withInit, singleRound_withInit]
  have h := SourceRound.length_encMachineState_run_le encCallee (roundContext size source r)
    callee calleeStart calleeReply input choices calleeBound (hcallee r hr)
  exact h.trans (roundStateBound_le size source context limit r hr calleeBound)

/-- Compile the composed source loop from native certificates for the round callee, final
membership callback, and input-dependent initial registers. The state budget covers all runs. -/
theorem withSourceRound_exists_routines {α : Type} (enc : α ↪ List Bool) (S : α → ℕ)
    (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool) (encMember : μ ↪ List Bool)
    (member : NondeterministicQueryMachine μ) (memberStart : Registers κ → μ)
    (memberReply : μ → Option Bool) (contextOf : α → κ) (limitOf : α → ℕ)
    (hregisters : ComputableInSpace (fun a => start (contextOf a) (limitOf a))
      enc (encRegisters encContext) S)
    (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hsize : ComputableInSpace size encContext encNat (fun c => (encContext c).length))
    (hsource : ComputableInSpace source encContext encNat (fun c => (encContext c).length))
    (hcalleeStart : ComputableInSpace
      (fun q : SourceRound.State => calleeStart q.context (SourceRound.request q))
      SourceRound.encState encCallee (fun q => (SourceRound.encState q).length))
    (hcalleeReply : ComputableInSpace calleeReply encCallee (encOption encBool)
      (fun t => (encCallee t).length))
    (hcalleeQuery : ComputableInSpace callee.query encCallee encNat (fun t => (encCallee t).length))
    (hcalleeHalt : ComputableInSpace callee.halted encCallee encBool
      (fun t => (encCallee t).length))
    (hcalleeNext : ComputableInSpace callee.next (encPair encCallee encReadChoice)
      encCallee (fun p => (encPair encCallee encReadChoice p).length))
    (hmemberStart : ComputableInSpace memberStart (encRegisters encContext) encMember
      (fun r => (encRegisters encContext r).length))
    (hmemberReply : ComputableInSpace memberReply encMember (encOption encBool)
      (fun s => (encMember s).length))
    (hmemberQuery : ComputableInSpace member.query encMember encNat (fun s => (encMember s).length))
    (hmemberHalt : ComputableInSpace member.halted encMember encBool
      (fun s => (encMember s).length))
    (hmemberNext : ComputableInSpace member.next (encPair encMember encReadChoice) encMember
      (fun p => (encPair encMember encReadChoice p).length))
    (hstates : ∃ c, ∀ a bits, (encState encContext (SourceRound.encMachineState τ encCallee)
      encMember ((withSourceRound size source callee calleeStart calleeReply
        (contextOf a) (limitOf a) member memberStart memberReply).run (enc a) bits)).length ≤
      c * S a) :
    Nonempty (Routines (withSourceRound size source callee calleeStart calleeReply context limit
      member memberStart memberReply)
      (fun a => (withSourceRound size source callee calleeStart calleeReply
        (contextOf a) (limitOf a) member memberStart memberReply).init) enc S) :=
  exists_routines encContext (SourceRound.encMachineState τ encCallee) encMember
    (start context limit) (singleRound) (entryRound) SourceRound.answer member memberStart
    memberReply enc S (fun a => start (contextOf a) (limitOf a)) hregisters hlog
    (roundEntry_inSpace size source encContext encCallee hsize hsource) hmemberStart
    (SourceRound.answer_inSpace encCallee) hmemberReply
    (SourceRound.machine_query_inSpace encCallee _ _ _ _ hcalleeQuery) hmemberQuery
    (SourceRound.machine_halted_inSpace encCallee _ _ _ _) hmemberHalt
    (SourceRound.machine_next_inSpace encCallee _ _ _ _ hcalleeStart hcalleeReply
      hcalleeHalt hcalleeNext) hmemberNext hstates

end Composition

end Turing.DoubleCounting.SourceRoundLoop
