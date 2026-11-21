/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.BoundedWalk
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic

/-!
# Retained dimensions for bounded same-input walks

One abstract transition machine runs the existing bounded walk with dimension and
adjacency context taken from its entry state. It makes the same original-input reads,
and preserves first-halting selector lists and unused fuel. The encoded state adds the
binary dimension and context to the existing bound on every branch.

The `entry_budget` certificate loads the runtime context, binary dimension, and registers.
Native space certificates cover the query position, phase transition, halt flag, and unused fuel.
-/

public section

namespace Turing.DoubleCounting.BoundedWalk.Runtime

open MultiTapeTM ComputableInSpace

/-- A walk and its retained vertex count and adjacency context. A walk starts with a vertex,
so the carrier is nonempty. -/
structure State (κ τ : Type) where
  /-- Runtime parameters used to construct an adjacency call. -/
  context : κ
  /-- Number of vertices in the retained carrier. -/
  size : ℕ
  /-- The carrier at a walk entry is nonempty. -/
  positive : 0 < size
  /-- The existing walk state for this carrier. -/
  walk : BoundedWalk.State size τ

variable {κ τ : Type}

/-- Frame the adjacency context and binary vertex count, then write the existing walk state. -/
def encState (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool) : State κ τ ↪ List Bool where
  toFun s := frame (encContext s.context) ++
    (frame (encNat s.size) ++ BoundedWalk.encState encCallee s.walk)
  inj' := by
    rintro ⟨a, n, hn, s⟩ ⟨b, m, hm, t⟩ h
    obtain ⟨hab, hrest⟩ := frame_append_inj h
    obtain ⟨hnm, hst⟩ := frame_append_inj hrest
    cases encContext.injective hab
    cases encNat.injective hnm
    cases (BoundedWalk.encState encCallee).injective hst
    rfl

/-- The framing overhead charges both retained fields and the unchanged inner encoding. -/
theorem length_encState (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool)
    (s : State κ τ) :
    (encState encContext encCallee s).length =
      2 * (encContext s.context).length + 2 * (encNat s.size).length +
        (BoundedWalk.encState encCallee s.walk).length + 2 := by
  change (frame (encContext s.context) ++
    (frame (encNat s.size) ++ BoundedWalk.encState encCallee s.walk)).length = _
  simp only [List.length_append, length_frame]
  omega

/-- Frame the retained context and vertex count around a supplied encoded walk state. -/
theorem state_budget {α : Type} {encIn : α ↪ List Bool} {budget : α → ℕ}
    (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool)
    {context : α → κ} {dimension : α → ℕ} {walk : (a : α) → BoundedWalk.State (dimension a) τ}
    {positive : ∀ a, 0 < dimension a}
    (hcontext : ComputableInSpace context encIn encContext budget)
    (hdim : ComputableInSpace dimension encIn encNat budget)
    (hwalk : ComputableInSpace (fun a => BoundedWalk.encState encCallee (walk a))
      encIn encBits budget) :
    ComputableInSpace (fun a => State.mk (context a) (dimension a) (positive a) (walk a))
      encIn (encState encContext encCallee) budget :=
  (budget_prod hcontext (budget_prod hdim hwalk)).of_enc_eq fun _ => rfl

variable (edge : QueryMachine τ) (start : κ → ℕ → ℕ → τ) (verdict : τ → Bool) (clock : ℕ)

private def typedMachine {N : ℕ} (ctx : κ) (r : Registers N) :=
  BoundedWalk.machine edge (fun u v => start ctx u.val v.val) verdict clock r

private def innerMachine (s : State κ τ) :=
  typedMachine edge start verdict clock s.context ⟨⟨0, s.positive⟩, ⟨0, s.positive⟩, 0⟩

/-- Enter the runtime machine at the existing bounded walk's initial registers. -/
def entry {N : ℕ} (ctx : κ) (r : Registers N) : State κ τ :=
  ⟨ctx, N, Nat.zero_lt_of_lt r.current.isLt, (typedMachine edge start verdict clock ctx r).init⟩

/-- Load a runtime walk entry within a common budget for the retained context, binary
dimension, valid binary endpoints, and fuel. The entry computes the destination reader
width from the dimension. -/
theorem entry_budget {α : Type} {encIn : α ↪ List Bool} {budget : α → ℕ}
    (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool)
    {context : α → κ} {dimension : α → ℕ} {registers : (a : α) → Registers (dimension a)}
    (hcontext : ComputableInSpace context encIn encContext budget)
    (hdim : ComputableInSpace dimension encIn encNat budget)
    (hcurrent : ComputableInSpace (fun a => (registers a).current.val) encIn encNat budget)
    (htarget : ComputableInSpace (fun a => (registers a).target.val) encIn encNat budget)
    (hfuel : ComputableInSpace (fun a => (registers a).fuel) encIn encNat budget) :
    ComputableInSpace (fun a => entry edge start verdict clock (context a) (registers a))
      encIn (encState encContext encCallee) budget := by
  have hregisters := BoundedWalk.registersWord_budget (r := registers) hcurrent htarget hfuel
  have hchoice := BoundedWalk.choiceWord_budget hregisters (NondeterministicChoice.init_budget hdim)
  refine state_budget encContext encCallee hcontext hdim (hchoice.of_enc_eq fun a => ?_)
  simp only [typedMachine, encBits_apply, BoundedWalk.encState_init]

/-- One same-input transition machine selects the walk's context and dimension from its
current state, including during a suspended adjacency call. -/
def machine (initial : State κ τ) : NondeterministicQueryMachine (State κ τ) where
  init := initial
  query s := BoundedWalk.query edge.query s.walk
  next := fun (s, reply, selector) =>
    {s with walk := (innerMachine edge start verdict clock s).next (s.walk, reply, selector)}
  halted s := BoundedWalk.halted s.walk
  accept s := (innerMachine edge start verdict clock s).accept s.walk

/-- The choice update uses the retained context to initiate an adjacency call. -/
theorem machine_next_choice (initial : State κ τ) {N : ℕ} (ctx : κ) (hp : 0 < N)
    (r : Registers N) (s : NondeterministicChoice.State) (answer : Option Bool)
    (selector : Bool) :
    (machine edge start verdict clock initial).next (⟨ctx, N, hp, .choose r s⟩, answer, selector) =
      ⟨ctx, N, hp, BoundedWalk.advanceChoice
        (fun u v => start ctx u.val v.val) clock r s selector⟩ := by
  simp only [machine, innerMachine, typedMachine, BoundedWalk.machine_next_choice]

/-- The active-call update retains the runtime context and dimension. -/
theorem machine_next_call (initial : State κ τ) {N : ℕ} (ctx : κ) (hp : 0 < N)
    (r : Registers N) (v : Fin N) (remaining : ℕ) (s : τ) (answer : Option Bool)
    (selector : Bool) :
    (machine edge start verdict clock initial).next
        (⟨ctx, N, hp, .call r v remaining s⟩, answer, selector) =
      ⟨ctx, N, hp, BoundedWalk.advanceCall edge verdict r v remaining s answer selector⟩ := by
  simp only [machine, innerMachine, typedMachine, BoundedWalk.machine_next_call]

/-- Entering the same machine with different registers does not change its transition rules. -/
theorem machine_withInit (initial state : State κ τ) :
    (machine edge start verdict clock initial).withInit state =
      machine edge start verdict clock state := by
  unfold machine NondeterministicQueryMachine.withInit
  rfl

/-- The runtime machine starts in the supplied entry state. -/
theorem machine_init (initial : State κ τ) :
    (machine edge start verdict clock initial).init = initial := by
  unfold machine
  rfl

private theorem innerMachine_withInit {N : ℕ} (ctx : κ) (hp : 0 < N)
    (s : BoundedWalk.State N τ) (r : Registers N) :
    (innerMachine edge start verdict clock ⟨ctx, N, hp, s⟩).withInit
      (typedMachine edge start verdict clock ctx r).init =
      typedMachine edge start verdict clock ctx r :=
  BoundedWalk.machine_withInit _ _ _ _ _ _

private theorem step_eq {N : ℕ} (initial : State κ τ) (ctx : κ) (hp : 0 < N) (r : Registers N)
    (input : List Bool) (s : BoundedWalk.State N τ) (bit : Bool) :
    (machine edge start verdict clock initial).step input ⟨ctx, N, hp, s⟩ bit =
      ⟨ctx, N, hp, (typedMachine edge start verdict clock ctx r).step input s bit⟩ := by
  rw [← innerMachine_withInit edge start verdict clock ctx hp s r,
    NondeterministicQueryMachine.step_withInit]
  simp only [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, machine,
    innerMachine, typedMachine, BoundedWalk.machine_query, BoundedWalk.machine_halted]
  by_cases h : BoundedWalk.halted s = true <;> simp [h]

private theorem replay_eq {N : ℕ} (initial : State κ τ) (ctx : κ) (hp : 0 < N) (r : Registers N)
    (input selectors : List Bool) (s : BoundedWalk.State N τ) :
    (machine edge start verdict clock initial).replay input selectors ⟨ctx, N, hp, s⟩ =
      ⟨ctx, N, hp, (typedMachine edge start verdict clock ctx r).replay input selectors s⟩ := by
  exact List.foldl_hom (fun inner => State.mk ctx N hp inner)
    (step_eq edge start verdict clock initial ctx hp r input)

/-- Every replay retains the entry dimension and context and uses exactly the existing
bounded walk's state on the original input and selectors. -/
theorem run_eq {N : ℕ} (ctx : κ) (r : Registers N) (input selectors : List Bool) :
    let initial := entry edge start verdict clock ctx r
    (machine edge start verdict clock initial).run input selectors =
      ⟨ctx, N, Nat.zero_lt_of_lt r.current.isLt,
        (BoundedWalk.machine edge (fun u v => start ctx u.val v.val) verdict clock r).run
          input selectors⟩ :=
  replay_eq edge start verdict clock _ ctx _ r input selectors _

/-- Decode the optional unused fuel from the runtime walk state. -/
def remainingFuel (s : State κ τ) : Option ℕ := BoundedWalk.remainingFuel s.walk

private theorem stateFields_budget {α : Type} {encIn : α ↪ List Bool} {budget : α → ℕ}
    {encContext : κ ↪ List Bool} {encCallee : τ ↪ List Bool} {state : α → State κ τ}
    (hs : ComputableInSpace state encIn (encState encContext encCallee) budget) :
    ComputableInSpace (fun a => ((state a).context, (state a).size,
      BoundedWalk.encState encCallee (state a).walk))
      encIn (encPair encContext (encPair encNat encBits)) budget :=
  hs.of_enc_eq fun _ => rfl

private theorem walkWord_inSpace (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool) :
    ComputableInSpace (fun s => BoundedWalk.encState encCallee s.walk)
      (encState encContext encCallee) encBits
      (fun s => (encState encContext encCallee s).length) :=
  snd' (snd' (stateFields_budget (of_inO (ComputableInO.of_eq fun _ => rfl))))

/-- Framed runtime state and optional read reply, followed by the selector bit. -/
abbrev encStep (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool) :
    (State κ τ × Option Bool × Bool) ↪ List Bool :=
  encPair (encState encContext encCallee) (encPair (encOption encBool) encBool)

/-- A single runtime transition uses space linear in the encoded state, reply, and selector.
It retains the context and dimension and dispatches the existing bounded-walk update. -/
theorem next_inSpace (initial : State κ τ) (encContext : κ ↪ List Bool)
    (encCallee : τ ↪ List Bool)
    (hstart : ComputableInSpace (fun (ctx, src, dst) => start ctx src dst)
      (BoundedWalk.encStartRequest encContext) encCallee
      (fun p => (BoundedWalk.encStartRequest encContext p).length))
    (hnext : ComputableInSpace edge.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hhalted : ComputableInSpace edge.halted encCallee encBool (fun s => (encCallee s).length))
    (hverdict : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length)) :
    ComputableInSpace (machine edge start verdict clock initial).next
      (encStep encContext encCallee) (encState encContext encCallee)
      (fun p => (encStep encContext encCallee p).length) := by
  let encReply := encPair (encOption encBool) encBool
  have hs := stateFields_budget (fst (encState encContext encCallee) encReply)
  have hcontext := fst' hs
  have hdim := fst' (snd' hs)
  have hinput := snd (encState encContext encCallee) encReply
  have hstep := BoundedWalk.advance_budget (state := fun p => p.1.walk) clock hstart hnext
    hhalted hverdict hcontext hdim (fun p => p.1.positive) (snd' (snd' hs))
    (fst' hinput) (snd' hinput)
  refine (state_budget (positive := fun p => p.1.positive)
    encContext encCallee hcontext hdim hstep).of_enc_eq ?_
  rintro ⟨state, reply, selector⟩
  simp only [machine, innerMachine, typedMachine, BoundedWalk.machine_next]

/-- Read the active adjacency query position from a runtime state in linear space. -/
theorem query_inSpace (initial : State κ τ) (encContext : κ ↪ List Bool)
    (encCallee : τ ↪ List Bool)
    (hquery : ComputableInSpace edge.query encCallee encNat (fun s => (encCallee s).length)) :
    ComputableInSpace (machine edge start verdict clock initial).query
      (encState encContext encCallee) encNat
      (fun s => (encState encContext encCallee s).length) :=
  BoundedWalk.query_budget (state := State.walk) hquery (walkWord_inSpace encContext encCallee)

/-- Detect a terminal runtime state in linear space. -/
theorem halted_inSpace (initial : State κ τ) (encContext : κ ↪ List Bool)
    (encCallee : τ ↪ List Bool) :
    ComputableInSpace (machine edge start verdict clock initial).halted
      (encState encContext encCallee) encBool
      (fun s => (encState encContext encCallee s).length) :=
  BoundedWalk.halted_budget (state := State.walk) (walkWord_inSpace encContext encCallee)

/-- Decode the optional unused fuel from a runtime state in linear space. -/
theorem remainingFuel_inSpace (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool) :
    ComputableInSpace (remainingFuel (κ := κ) (τ := τ))
      (encState encContext encCallee) (encOption encNat)
      (fun s => (encState encContext encCallee s).length) :=
  BoundedWalk.remainingFuel_budget (state := State.walk) (walkWord_inSpace encContext encCallee)

private theorem halted_run_eq {N : ℕ} (ctx : κ) (r : Registers N) (input selectors : List Bool) :
    let initial := entry edge start verdict clock ctx r
    let M := machine edge start verdict clock initial
    let B := typedMachine edge start verdict clock ctx r
    M.halted (M.run input selectors) = B.halted (B.run input selectors) := by
  dsimp only
  rw [run_eq]
  simp only [machine, typedMachine, BoundedWalk.machine_halted]

/-- Runtime re-entry preserves both terminal halting and liveness of every strict prefix. -/
theorem firstHalting_iff {N : ℕ} (ctx : κ) (r : Registers N) (input selectors : List Bool) :
    let initial := entry edge start verdict clock ctx r
    let B := BoundedWalk.machine edge (fun u v => start ctx u.val v.val) verdict clock r
    (machine edge start verdict clock initial).FirstHalting input selectors initial ↔
      B.FirstHalting input selectors B.init := by
  let M := machine edge start verdict clock (entry edge start verdict clock ctx r)
  let B := typedMachine edge start verdict clock ctx r
  change (M.halted (M.run input selectors) = true ∧
      ∀ n < selectors.length, M.halted (M.run input (selectors.take n)) = false) ↔
    B.halted (B.run input selectors) = true ∧
      ∀ n < selectors.length, B.halted (B.run input (selectors.take n)) = false
  have h (bits : List Bool) : M.halted (M.run input bits) = B.halted (B.run input bits) :=
    halted_run_eq edge start verdict clock ctx r input bits
  simp only [h]

/-- The optional fuel agrees with the result of the existing walk on the same selector list. -/
theorem remainingFuel_run {N : ℕ} (ctx : κ) (r : Registers N) (input selectors : List Bool) :
    let initial := entry edge start verdict clock ctx r
    remainingFuel ((machine edge start verdict clock initial).run input selectors) =
      BoundedWalk.remainingFuel ((BoundedWalk.machine edge (fun u v => start ctx u.val v.val)
        verdict clock r).run input selectors) := by
  dsimp only
  rw [run_eq]
  rfl

/-- The runtime walk preserves the common clock on every branch. -/
theorem haltsWithin {N : ℕ} (ctx : κ) (r : Registers N) (input : List Bool) :
    (machine edge start verdict clock (entry edge start verdict clock ctx r)).HaltsWithin
      input (r.fuel * (N.size + clock + 3) + (N.size + 2)) := by
  intro selectors hlen
  rw [halted_run_eq]
  exact BoundedWalk.haltsWithin edge (fun u v => start ctx u.val v.val) verdict clock r
    input selectors hlen

/-- Every runtime branch adds only the framed context and binary dimension to the bounded walk's
retained state, including on rejection and during an adjacency call. -/
theorem length_run_le {N : ℕ} (ctx : κ) (r : Registers N) (input selectors : List Bool)
    (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool) (calleeBound : ℕ)
    (hcallee : ∀ (u v : Fin N) t, t ≤ clock →
      (encCallee (edge.runFrom input (start ctx u.val v.val) t)).length ≤ calleeBound) :
    let initial := entry edge start verdict clock ctx r
    (encState encContext encCallee ((machine edge start verdict clock initial).run
      input selectors)).length ≤
        2 * (encContext ctx).length + 14 * (encNat N).length +
          4 * (Nat.log2 N.size + 1) + 4 * (encNat r.fuel).length +
          2 * (encNat clock).length + calleeBound + 23 := by
  dsimp only
  rw [run_eq, length_encState]
  have h := BoundedWalk.length_run_le edge (fun u v => start ctx u.val v.val) verdict clock r
    input encCallee calleeBound hcallee selectors
  dsimp only
  omega

end Turing.DoubleCounting.BoundedWalk.Runtime
