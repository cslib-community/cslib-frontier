/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.BoundedWalk.Runtime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Retain

/-!
# Membership tallies with a runtime bounded walk

A tally can call a bounded-walk machine whose transition rules read the dimension from the
walk state. Each call enters at the tally's dimension, source, candidate and radius. This
allows different tally queries to use the same walk on the original input. A retained-context
tally also loads the adjacency context from its own entry state.

## Main definitions

* `Turing.DoubleCounting.MembershipTally.withRuntimeWalk`: the existing membership tally
  using a walk with runtime dimensions.
* `Turing.DoubleCounting.MembershipTally.retainedMachine`: one machine with a re-entrant
  adjacency context.

## Main results

* `Turing.DoubleCounting.MembershipTally.withRuntimeWalk_firstHalting_iff`: a successful
  first-halt selector list describes exactly one successful typed scan with the same reply.
* `Turing.DoubleCounting.MembershipTally.withRuntimeWalk_existsUnique_firstHalting`: a unique
  passing transcript at the exact round totals gives one successful selector list.
* `Turing.DoubleCounting.MembershipTally.withRuntimeWalk_haltsWithin` and
  `Turing.DoubleCounting.MembershipTally.withRuntimeWalk_length_run_le`: the common selector
  clock and encoded-state bound for all branches starting from a valid source.
* `Turing.DoubleCounting.MembershipTally.retainedMachine_replay`: every selector prefix agrees
  with the tally for the retained adjacency context.
* `Turing.DoubleCounting.MembershipTally.retainedMachine_existsUnique_firstHalting`:
  the same successful-selector uniqueness for the tally with retained adjacency context.
* The retained entry, transition, query, halt, and reply operations have linear-space
  certificates.
* `Turing.DoubleCounting.MembershipTally.retainedMachine_exists_routines`: compile the tally
  with input-dependent entry parameters and the all-branch encoded-state bound.
* `Turing.DoubleCounting.MembershipTally.retainedMachine_native_firstHalting_iff`: one
  accepting native occurrence list for the selectors of each passing typed tally.
-/

public section

namespace Turing.DoubleCounting.MembershipTally

open Cslib.DoubleCounting MultiTapeTM ComputableInSpace
open Turing.DoubleCounting.BoundedWalk

variable {κ τ : Type} (edge : QueryMachine τ) (start : κ → ℕ → ℕ → τ)
  (verdict : τ → Bool) (clock : ℕ)

private def enterRuntimeWalk (context : κ) (r : Registers) : Runtime.State κ τ :=
  if h : r.context.source < r.context.size ∧ r.cursor < r.context.size then
    Runtime.entry edge start verdict clock context
      ⟨⟨r.context.source, h.1⟩, ⟨r.cursor, h.2⟩, r.context.radius⟩
  else ⟨context, 1, Nat.zero_lt_one, .done none⟩

variable (initialWalk : Runtime.State κ τ) (context : κ)

/-- Run a membership tally with the supplied runtime walk. The walk enters at each valid
candidate with the tally's dimension and supplied adjacency context. An invalid walk entry
rejects. -/
def withRuntimeWalk (ctx : Context) : NondeterministicQueryMachine (State (Runtime.State κ τ)) :=
  machine ctx (Runtime.machine edge start verdict clock initialWalk)
    (enterRuntimeWalk edge start verdict clock context) Runtime.remainingFuel

/-- Re-enter the tally at new query parameters using the same runtime walk and adjacency context. -/
theorem withRuntimeWalk_withInit (ctx newContext : Context) :
    (withRuntimeWalk edge start verdict clock initialWalk context ctx).withInit
      (initial newContext) =
    withRuntimeWalk edge start verdict clock initialWalk context newContext := by
  unfold withRuntimeWalk NondeterministicQueryMachine.withInit
  rfl

/-- A successful first halt has exactly the selectors of a unique successful typed scan
and preserves its membership bit. The walk's original entry can have a different dimension
and adjacency context. -/
theorem withRuntimeWalk_firstHalting_iff {N : ℕ} (input : List Bool)
    (adjacent : Fin N → Fin N → Bool) (source target : Fin N) (radius : ℕ)
    (expected : Tally)
    (hclock : ∀ u v : Fin N,
      edge.halted (edge.runFrom input (start context u.val v.val) clock) = true)
    (hedge : ∀ u v : Fin N,
      verdict (edge.runFrom input (start context u.val v.val) clock) = adjacent u v)
    (bits : List Bool) (hit : Bool) :
    let M := withRuntimeWalk edge start verdict clock initialWalk context
      ⟨N, source.val, target.val, radius, expected⟩
    M.FirstHalting input bits M.init ∧ reply (M.run input bits) = some hit ↔
      ∃! branch, bits = selectors (BoundedWalk.selectors clock) branch ∧
        Scan.run adjacent source target radius expected branch = some hit := by
  unfold withRuntimeWalk
  refine firstHalting_iff_scan _ _ _ input adjacent source target radius expected
    (BoundedWalk.selectors clock) (BoundedWalk.eq_of_selectors_prefix clock) ?_ bits hit
  intro v acc ws left
  simpa only [enterRuntimeWalk, source.isLt, v.isLt, and_self, dite_true] using
    Runtime.firstHalting_remainingFuel_iff edge start verdict clock initialWalk context
      ⟨source, v, radius⟩ input adjacent hclock hedge ws left

/-- With the exact round totals and a unique passing transcript, the runtime tally has
exactly one successful first-halting selector list, for either membership answer. -/
theorem withRuntimeWalk_existsUnique_firstHalting {N : ℕ} (input : List Bool)
    (adjacent : Fin N → Fin N → Bool) (source target : Fin N) (radius : ℕ)
    (hclock : ∀ u v : Fin N,
      edge.halted (edge.runFrom input (start context u.val v.val) clock) = true)
    (hedge : ∀ u v : Fin N,
      verdict (edge.runFrom input (start context u.val v.val) clock) = adjacent u v)
    (hpass : ∃! w, Passes (fun u v => adjacent u v = true) source radius w) :
    let totals := expected (fun u v => adjacent u v = true) source radius
    let M := withRuntimeWalk edge start verdict clock initialWalk context
      ⟨N, source.val, target.val, radius, totals⟩
    ∃! bits, M.FirstHalting input bits M.init ∧ (reply (M.run input bits)).isSome := by
  intro totals M
  obtain ⟨chosen, hchosen, hunique⟩ :=
    Scan.existsUnique_successful_branch adjacent source target radius hpass
  have branch_eq_chosen {branch : Scan.Branch N} {hit : Bool}
      (h : Scan.run adjacent source target radius totals branch = some hit) : branch = chosen :=
    hunique branch (Option.isSome_iff_exists.mpr ⟨hit, h⟩)
  have hreplay (bits : List Bool) (hit : Bool) :=
    withRuntimeWalk_firstHalting_iff edge start verdict clock initialWalk context input
      adjacent source target radius totals hclock hedge bits hit
  dsimp only at hreplay
  let render := selectors (BoundedWalk.selectors (N := N) clock)
  obtain ⟨hit, hhit⟩ := Option.isSome_iff_exists.mp hchosen
  have hsuccess := (hreplay (render chosen) hit).mpr
    ⟨chosen, ⟨rfl, hhit⟩, fun _ h => branch_eq_chosen h.2⟩
  refine ⟨render chosen, ⟨hsuccess.1, Option.isSome_iff_exists.mpr ⟨hit, hsuccess.2⟩⟩, ?_⟩
  intro bits hbits
  obtain ⟨answer, hanswer⟩ := Option.isSome_iff_exists.mp hbits.2
  obtain ⟨branch, ⟨hword, hscan⟩, _⟩ := (hreplay bits answer).mp ⟨hbits.1, hanswer⟩
  exact hword.trans (congrArg render (branch_eq_chosen hscan))

private theorem runtimeWalk_withInit {ctx : Context} (r : Registers) (hr : r.context = ctx)
    (hsource : ctx.source < ctx.size) (hcursor : r.cursor < ctx.size) :
    let entry := Runtime.entry edge start verdict clock context
      ⟨⟨ctx.source, hsource⟩, ⟨r.cursor, hcursor⟩, ctx.radius⟩
    (Runtime.machine edge start verdict clock initialWalk).withInit
      (enterRuntimeWalk edge start verdict clock context r) =
    Runtime.machine edge start verdict clock entry := by
  cases hr
  simp only [Runtime.machine_withInit, enterRuntimeWalk, dite_eq_left (And.intro hsource hcursor)]

/-- The common selector clock charges the walk, entry and return for each candidate. -/
@[expose] def runtimeWalkClock (clock : ℕ) (ctx : Context) : ℕ :=
  ctx.size * (ctx.radius * (ctx.size.size + clock + 3) + (ctx.size.size + 2) + 2) + 1

/-- Charge the candidate scan and its calls, including all rejecting selector lists. -/
theorem withRuntimeWalk_haltsWithin (ctx : Context) (hsource : ctx.source < ctx.size)
    (input : List Bool) :
    (withRuntimeWalk edge start verdict clock initialWalk context ctx).HaltsWithin input
      (runtimeWalkClock clock ctx) := by
  apply haltsWithin
  intro r hr _ hcursor
  rw [runtimeWalk_withInit edge start verdict clock initialWalk context r hr hsource hcursor]
  exact Runtime.haltsWithin edge start verdict clock context
    ⟨⟨ctx.source, hsource⟩, ⟨r.cursor, hcursor⟩, ctx.radius⟩ input

/-- Add the framed adjacency context and runtime dimension to the fixed-dimension tally bound. -/
@[expose] def runtimeWalkStateBound (clock : ℕ) (ctx : Context)
    (contextLength calleeBound : ℕ) : ℕ :=
  stateBound ctx (Runtime.stateBound ctx.size ctx.radius clock contextLength calleeBound)

/-- Bound the encoded tally state on every selector prefix, including while a walk retains
the adjacency context and a suspended callback state. -/
theorem withRuntimeWalk_length_run_le (encK : κ ↪ List Bool) (encCallee : τ ↪ List Bool)
    (ctx : Context) (hsource : ctx.source < ctx.size) (input : List Bool) (calleeBound : ℕ)
    (hcallee : ∀ u v : Fin ctx.size, ∀ t ≤ clock,
      (encCallee (edge.runFrom input (start context u.val v.val) t)).length ≤ calleeBound)
    (bits : List Bool) :
    (encState (Runtime.encState encK encCallee)
      ((withRuntimeWalk edge start verdict clock initialWalk context ctx).run input bits)).length ≤
      runtimeWalkStateBound clock ctx (encK context).length calleeBound := by
  unfold runtimeWalkStateBound
  apply length_replay_le
  intro r hr _ hcursor choices
  rw [← NondeterministicQueryMachine.run_withInit,
    runtimeWalk_withInit edge start verdict clock initialWalk context r hr hsource hcursor]
  exact Runtime.length_run_le edge start verdict clock context
    ⟨⟨ctx.source, hsource⟩, ⟨r.cursor, hcursor⟩, ctx.radius⟩ input choices
    encK encCallee calleeBound hcallee

/-- A tally phase together with the adjacency context used at each walk entry. -/
structure RetainedState (κ τ : Type) where
  /-- The context passed to each adjacency call, such as the initialized seed and field. -/
  walkContext : κ
  /-- The existing tally state, including a suspended runtime walk when present. -/
  tally : State (Runtime.State κ τ)

/-- Frame the adjacency context before the existing encoded tally state. -/
enc_structure encRetainedState (encK : κ ↪ List Bool) (encCallee : τ ↪ List Bool) :
    RetainedState κ τ where
  walkContext : encK, tally : (encState (Runtime.encState encK encCallee))

/-- Enter the tally with the supplied adjacency context and query parameters. -/
def retainedInitial (walkContext : κ) (ctx : Context) : RetainedState κ τ :=
  ⟨walkContext, initial ctx⟩

/-- Decode the terminal membership reply from the retained tally. -/
def retainedReply (s : RetainedState κ τ) : Option Bool := reply s.tally

private def retainedStateEquiv : RetainedState κ τ ≃ κ × State (Runtime.State κ τ) where
  toFun s := (s.walkContext, s.tally)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Run the existing tally with the adjacency context taken from its state. -/
def retainedMachine (ctx : Context) : NondeterministicQueryMachine (RetainedState κ τ) :=
  NondeterministicQueryMachine.retain retainedStateEquiv
    (fun k => withRuntimeWalk edge start verdict clock initialWalk k ctx) context

/-- Native acceptance records successful tally completion, including a false reply. -/
theorem retainedMachine_accept (ctx : Context) (s : RetainedState κ τ) :
    (retainedMachine edge start verdict clock initialWalk context ctx).accept s =
      (retainedReply s).isSome := by rfl

/-- Changing both the adjacency context and the query at entry preserves the transitions. -/
theorem retainedMachine_withInit (ctx newCtx : Context) (newContext : κ) :
    (retainedMachine edge start verdict clock initialWalk context ctx).withInit
      (retainedInitial newContext newCtx) =
    retainedMachine edge start verdict clock initialWalk newContext newCtx := by
  unfold retainedMachine
  rw [show retainedInitial newContext newCtx = retainedStateEquiv.symm (newContext, initial newCtx)
    from rfl, NondeterministicQueryMachine.retain_withInit]
  simp only [withRuntimeWalk_withInit]

/-- Replay preserves the retained context and forwards exactly the same selectors and input. -/
theorem retainedMachine_replay (ctx : Context) (input bits : List Bool) (s : RetainedState κ τ) :
    (retainedMachine edge start verdict clock initialWalk context ctx).replay input bits s =
      ⟨s.walkContext,
        (withRuntimeWalk edge start verdict clock initialWalk s.walkContext ctx).replay
          input bits s.tally⟩ :=
  NondeterministicQueryMachine.replay_retain retainedStateEquiv
    (fun k => withRuntimeWalk edge start verdict clock initialWalk k ctx)
    context s.walkContext input bits s.tally

/-- The first-halting selectors and reply agree with the tally at the retained adjacency context. -/
theorem retainedMachine_firstHalting_reply_iff (ctx : Context) (input bits : List Bool)
    (hit : Bool) :
    let M := retainedMachine edge start verdict clock initialWalk context ctx
    let T := withRuntimeWalk edge start verdict clock initialWalk context ctx
    M.FirstHalting input bits M.init ∧ retainedReply (M.run input bits) = some hit ↔
      T.FirstHalting input bits T.init ∧ reply (T.run input bits) = some hit := by
  dsimp only
  refine and_congr (NondeterministicQueryMachine.firstHalting_retain retainedStateEquiv
    (fun k => withRuntimeWalk edge start verdict clock initialWalk k ctx)
    context context input bits _) ?_
  rw [NondeterministicQueryMachine.run, retainedMachine_replay]
  rfl

/-- A unique passing transcript at the exact round totals gives one successful retained
selector list. Either Boolean reply is successful. -/
theorem retainedMachine_existsUnique_firstHalting {N : ℕ} (input : List Bool)
    (adjacent : Fin N → Fin N → Bool) (source target : Fin N) (radius : ℕ)
    (hclock : ∀ u v : Fin N,
      edge.halted (edge.runFrom input (start context u.val v.val) clock) = true)
    (hedge : ∀ u v : Fin N,
      verdict (edge.runFrom input (start context u.val v.val) clock) = adjacent u v)
    (hpass : ∃! w, Passes (fun u v => adjacent u v = true) source radius w) :
    let totals := expected (fun u v => adjacent u v = true) source radius
    let M := retainedMachine edge start verdict clock initialWalk context
      ⟨N, source.val, target.val, radius, totals⟩
    ∃! bits, M.FirstHalting input bits M.init ∧ (retainedReply (M.run input bits)).isSome := by
  intro totals M
  refine (existsUnique_congr fun bits => ?_).mpr
    (withRuntimeWalk_existsUnique_firstHalting edge start verdict clock initialWalk context input
      adjacent source target radius hclock hedge hpass)
  simp only [Option.isSome_iff_exists, ← exists_and_left]
  exact exists_congr fun hit =>
    retainedMachine_firstHalting_reply_iff edge start verdict clock initialWalk context
      ⟨N, source.val, target.val, radius, totals⟩ input bits hit

/-- The retained tally has the same all-branch selector clock. -/
theorem retainedMachine_haltsWithin (ctx : Context) (hsource : ctx.source < ctx.size)
    (input : List Bool) :
    (retainedMachine edge start verdict clock initialWalk context ctx).HaltsWithin input
      (runtimeWalkClock clock ctx) := by
  intro bits hlen
  rw [NondeterministicQueryMachine.run, retainedMachine_replay]
  change (withRuntimeWalk edge start verdict clock initialWalk context ctx).halted
    ((withRuntimeWalk edge start verdict clock initialWalk context ctx).run input bits) = true
  exact withRuntimeWalk_haltsWithin edge start verdict clock initialWalk context ctx hsource
    input bits hlen

/-- The encoded state bound adds the context frame to the existing runtime tally envelope. -/
@[expose] def retainedStateBound (clock : ℕ) (ctx : Context)
    (contextLength calleeBound : ℕ) : ℕ :=
  2 * contextLength + 1 + runtimeWalkStateBound clock ctx contextLength calleeBound

/-- The encoded-state bound covers every retained tally state, including suspended walks. -/
theorem retainedMachine_length_run_le (encK : κ ↪ List Bool) (encCallee : τ ↪ List Bool)
    (ctx : Context) (hsource : ctx.source < ctx.size) (input : List Bool) (calleeBound : ℕ)
    (hcallee : ∀ u v : Fin ctx.size, ∀ t ≤ clock,
      (encCallee (edge.runFrom input (start context u.val v.val) t)).length ≤ calleeBound)
    (bits : List Bool) :
    (encRetainedState encK encCallee
      ((retainedMachine edge start verdict clock initialWalk context ctx).run input bits)).length ≤
      retainedStateBound clock ctx (encK context).length calleeBound := by
  have h := withRuntimeWalk_length_run_le edge start verdict clock initialWalk context
    encK encCallee ctx hsource input calleeBound hcallee bits
  rw [NondeterministicQueryMachine.run, retainedMachine_replay]
  let tally := withRuntimeWalk edge start verdict clock initialWalk context ctx
  change (encRetainedState encK encCallee ⟨context, tally.run input bits⟩).length ≤ _
  simp only [encRetainedState_apply, encRetainedStateFields, length_encPair, retainedStateBound]
  exact Nat.add_le_add_left h (2 * (encK context).length + 1)

section RetainedSpace

variable (encK : κ ↪ List Bool) (encCallee : τ ↪ List Bool)

local notation "E" => encRetainedState encK encCallee
local notation "T" => encState (Runtime.encState encK encCallee)

/-- Initialize a retained tally within the common budget for the context and query producers. -/
theorem retainedInitial_budget {α : Type} {encIn : α ↪ List Bool} {budget : α → ℕ}
    {walkContext : α → κ} {params : α → Context}
    (hcontext : ComputableInSpace walkContext encIn encK budget)
    (hparams : ComputableInSpace params encIn encContext budget) :
    ComputableInSpace (fun a => retainedInitial (τ := τ) (walkContext a) (params a))
      encIn E budget :=
  encRetainedState_mk_budget encK encCallee hcontext
    (budget_comp_linear (initial_inSpace (Runtime.encState encK encCallee)) hparams)

private theorem tally_inSpace :
    ComputableInSpace RetainedState.tally E T (fun s => (E s).length) :=
  encRetainedState_tally_budget encK encCallee (budget_id (enc := E) (.refl _))

/-- Read the active walk's original-input query position in linear workspace. -/
theorem retainedMachine_query_inSpace (ctx : Context)
    (hquery : ComputableInSpace edge.query encCallee encNat (fun s => (encCallee s).length)) :
    ComputableInSpace (retainedMachine edge start verdict clock initialWalk context ctx).query
      E encNat (fun s => (E s).length) := by
  let W := Runtime.machine edge start verdict clock initialWalk
  have hw := Runtime.query_inSpace edge start verdict clock initialWalk encK encCallee hquery
  have ht := query_inSpace _ ctx W (enterRuntimeWalk edge start verdict clock context)
    Runtime.remainingFuel hw
  exact (budget_comp_linear ht (tally_inSpace encK encCallee)).of_enc_eq fun _ => rfl

/-- Detect the terminal phase of the retained tally in linear workspace. -/
theorem retainedMachine_halted_inSpace (ctx : Context) :
    ComputableInSpace (retainedMachine edge start verdict clock initialWalk context ctx).halted
      E encBool (fun s => (E s).length) := by
  let W := Runtime.machine edge start verdict clock initialWalk
  have ht := halted_inSpace (Runtime.encState encK encCallee) ctx W
    (enterRuntimeWalk edge start verdict clock context) Runtime.remainingFuel
  exact (budget_comp_linear ht (tally_inSpace encK encCallee)).of_enc_eq fun _ => rfl

/-- Decode the optional membership reply without changing the passing negative value. -/
theorem retainedReply_inSpace :
    ComputableInSpace retainedReply E (encOption encBool) (fun s => (E s).length) :=
  (budget_comp_linear (reply_inSpace (Runtime.encState encK encCallee))
    (tally_inSpace encK encCallee)).of_enc_eq fun _ => rfl

private theorem enterRuntimeWalk_inSpace :
    let encIn := encPair encK encRegisters
    ComputableInSpace (fun p : κ × Registers => enterRuntimeWalk edge start verdict clock p.1 p.2)
      encIn (Runtime.encState encK encCallee) (fun p => (encIn p).length) := by
  let encIn := encPair encK encRegisters
  let dimension (p : κ × Registers) :=
    if 0 < p.2.context.size then p.2.context.size else 1
  have hdpos (p : κ × Registers) : 0 < dimension p := by
    unfold dimension
    split <;> omega
  have hcontext := fst encK encRegisters
  have hregisters := snd encK encRegisters
  have hquery := encRegisters_context_budget hregisters
  have hsize := encContext_size_budget hquery
  have hsource := encContext_source_budget hquery
  have hcursor := encRegisters_cursor_budget hregisters
  have hfuel := encContext_radius_budget hquery
  have hzero := budget_const (encIn := encIn) (encB := encNat) 0 (.refl _)
  have hone := budget_const (encIn := encIn) (encB := encNat) 1 (.refl _)
  have hdimension : ComputableInSpace dimension encIn encNat (fun p => (encIn p).length) :=
    budget_iteProp (budget_natLt hzero hsize) hsize hone
  have hentry := Runtime.entryRanks_budget edge start verdict clock encK encCallee
    hdpos hcontext hdimension hsource hcursor hfuel
  have hreject := Runtime.state_budget encK encCallee
    (walk := fun _ => .done none) (positive := fun _ => Nat.zero_lt_one) hcontext hone
    (budget_const (encB := encBits)
      (BoundedWalk.encState (N := 1) encCallee (.done none)) (.refl _))
  have hvalid := budget_boolAnd (budget_natLt hsource hsize) (budget_natLt hcursor hsize)
  refine (budget_ite hvalid hentry hreject).of_enc_eq ?_
  rintro ⟨context, r⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, enterRuntimeWalk]
  by_cases h : r.context.source < r.context.size ∧ r.cursor < r.context.size
  · have hpos := Nat.zero_lt_of_lt h.1
    rw [dite_eq_left h, ite_eq_left h]
    simp only [dimension, ite_eq_left hpos]
    rw [Runtime.entryRanks_eq_entry edge start verdict clock context hpos
      ⟨⟨r.context.source, h.1⟩, ⟨r.cursor, h.2⟩, r.context.radius⟩]
  · rw [dite_eq_right h, ite_eq_right h]

open NondeterministicQueryMachine (encReadChoice) in
/-- Step the retained tally in linear workspace from the adjacency callback certificates. -/
theorem retainedMachine_next_inSpace (ctx : Context)
    (hstart : ComputableInSpace (fun (k, u, v) => start k u v)
      (BoundedWalk.encStartRequest encK) encCallee
      (fun p => (BoundedWalk.encStartRequest encK p).length))
    (hnext : ComputableInSpace edge.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hhalted : ComputableInSpace edge.halted encCallee encBool (fun s => (encCallee s).length))
    (hverdict : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length)) :
    let encStep := encPair E encReadChoice
    ComputableInSpace (retainedMachine edge start verdict clock initialWalk context ctx).next
      encStep E (fun p => (encStep p).length) := by
  let W := Runtime.machine edge start verdict clock initialWalk
  have hstep := next_withParameter_inSpace encK (Runtime.encState encK encCallee)
    ctx W (enterRuntimeWalk edge start verdict clock) Runtime.remainingFuel
    (enterRuntimeWalk_inSpace edge start verdict clock encK encCallee)
    (Runtime.next_inSpace edge start verdict clock initialWalk encK encCallee hstart hnext
      hhalted hverdict)
    (Runtime.halted_inSpace edge start verdict clock initialWalk encK encCallee)
    (Runtime.remainingFuel_inSpace encK encCallee)
  have hs := fst E encReadChoice
  have hk := encRetainedState_walkContext_budget encK encCallee hs
  have ht := encRetainedState_tally_budget encK encCallee hs
  have hp := budget_prod ht (budget_prod hk (snd E encReadChoice))
  exact (encRetainedState_mk_budget encK encCallee hk
    (budget_comp_linear hstep hp)).of_enc_eq fun _ => rfl

/-- The tally accepts exactly when its terminal state carries a membership reply. -/
theorem retainedMachine_accept_inSpace (ctx : Context) :
    ComputableInSpace (retainedMachine edge start verdict clock initialWalk context ctx).accept
      E encBool (fun s => (E s).length) :=
  (budget_optionIsSome (retainedReply_inSpace encK encCallee)).of_enc_eq fun _ => rfl

open NondeterministicQueryMachine in
/-- Compile the retained tally using the state bound for every selector branch. -/
theorem retainedMachine_exists_routines {α : Type} (enc : α ↪ List Bool) (S : α → ℕ)
    (ctx : Context) (walkContext : α → κ) (params : α → Context)
    (hcontext : ComputableInSpace walkContext enc encK S)
    (hparams : ComputableInSpace params enc encContext S)
    (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hstart : ComputableInSpace (fun (k, u, v) => start k u v)
      (BoundedWalk.encStartRequest encK) encCallee
      (fun p => (BoundedWalk.encStartRequest encK p).length))
    (hq : ComputableInSpace edge.query encCallee encNat (fun s => (encCallee s).length))
    (hn : ComputableInSpace edge.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hh : ComputableInSpace edge.halted encCallee encBool (fun s => (encCallee s).length))
    (hv : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length))
    (hsource : ∀ a, (params a).source < (params a).size)
    (calleeBound : α → ℕ)
    (hcallee : ∀ a, ∀ u v : Fin (params a).size, ∀ t ≤ clock,
      (encCallee (edge.runFrom (enc a) (start (walkContext a) u.val v.val) t)).length ≤
        calleeBound a)
    (hstate : ∀ a,
      retainedStateBound clock (params a) (encK (walkContext a)).length (calleeBound a) ≤ S a) :
    Nonempty (Routines (retainedMachine edge start verdict clock initialWalk context ctx)
      (fun a => retainedInitial (walkContext a) (params a)) enc S) := by
  refine (retainedMachine edge start verdict clock initialWalk context ctx).exists_routines
    (retainedMachine_query_inSpace edge start verdict clock initialWalk context encK encCallee
      ctx hq)
    (retainedMachine_next_inSpace edge start verdict clock initialWalk context encK encCallee ctx
      hstart hn hh hv)
    (retainedMachine_halted_inSpace edge start verdict clock initialWalk context encK encCallee ctx)
    (retainedMachine_accept_inSpace edge start verdict clock initialWalk context encK encCallee ctx)
    _ S hlog (retainedInitial_budget encK encCallee hcontext hparams) ⟨1, ?_⟩
  intro a bits
  rw [retainedMachine_withInit, Nat.one_mul]
  exact (retainedMachine_length_run_le edge start verdict clock initialWalk (walkContext a)
    encK encCallee (params a) (hsource a) (enc a) (calleeBound a) (hcallee a) bits).trans
    (hstate a)

end RetainedSpace

open NondeterministicQueryMachine in
/-- Native accepting occurrences record exactly the selectors of passing typed tallies
at the input's retained context, with one occurrence list per selector list. -/
theorem retainedMachine_native_firstHalting_iff {α : Type}
    {enc : α ↪ List Bool} {S : α → ℕ} {N : ℕ}
    (ctx : Context) (walkContext : α → κ) (params : α → Context)
    (R : Routines (retainedMachine edge start verdict clock initialWalk context ctx)
      (fun a => retainedInitial (walkContext a) (params a)) enc S)
    (a : α) (adjacent : Fin N → Fin N → Bool) (source target : Fin N) (radius : ℕ)
    (expected : Tally) (bits : List Bool)
    (hparams : params a = ⟨N, source.val, target.val, radius, expected⟩)
    (hclock : ∀ u v : Fin N,
      edge.halted (edge.runFrom (enc a) (start (walkContext a) u.val v.val) clock) = true)
    (hedge : ∀ u v : Fin N,
      verdict (edge.runFrom (enc a) (start (walkContext a) u.val v.val) clock) = adjacent u v) :
    (∃! indices, ∃ final,
      Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (enc a)) indices =
        some (bits, final) ∧ final.Halted ∧ final.output = [true]) ↔
      ∃! branch, bits = selectors (BoundedWalk.selectors clock) branch ∧
        ∃ hit, Scan.run adjacent source target radius expected branch = some hit := by
  apply native_firstHalting_iff_of_reply R a bits retainedReply (BoundedWalk.selectors clock)
    (BoundedWalk.eq_of_selectors_prefix clock) adjacent source target radius expected
    (retainedMachine_accept edge start verdict clock initialWalk context ctx)
  intro hit
  have hM := retainedMachine_withInit edge start verdict clock initialWalk context ctx (params a)
    (walkContext a)
  rw [hparams] at hM
  have hspec := (retainedMachine_firstHalting_reply_iff edge start verdict clock initialWalk
    (walkContext a) ⟨N, source.val, target.val, radius, expected⟩ (enc a) bits hit).trans
    (withRuntimeWalk_firstHalting_iff edge start verdict clock initialWalk (walkContext a)
      (enc a) adjacent source target radius expected hclock hedge bits hit)
  simpa only [← hM, init_withInit, firstHalting_withInit, run_withInit, hparams] using hspec

end Turing.DoubleCounting.MembershipTally
