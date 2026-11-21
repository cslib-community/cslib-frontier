/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.BranchReplay
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Fuel-bounded source controller with same-input calls

A source scan repeatedly calls a supplied round machine. A tied round reports the next
radius. A stable round calls a membership machine with the current radius and tally.
Only the false selector can return from a call. A rejected call or exhausted round fuel
rejects the source scan.

## Main results

* `firstHalting_iff_replayRounds` identifies successful selector streams with replay of the
  existing fuel-bounded loop.
* `haltsWithin` and `length_run_le` charge the retained registers and supplied callback bounds
  on every branch.
* `exists_routines` compiles the loop with supplied native callbacks and
  `native_firstHalting_accept_iff` preserves its accepting occurrence lists.
-/

public section

namespace Turing.DoubleCounting.SourceRoundLoop

open Cslib.DoubleCounting MultiTapeTM ComputableInSpace
variable {κ ρ μ : Type}

/-- Scalar round registers and data needed to initialize either callback. -/
structure Registers (κ : Type) where
  /-- Source, target and retained graph data for the supplied callbacks. -/
  context : κ
  /-- Remaining number of round calls. -/
  fuel : ℕ
  /-- Radius of the current verified tally. -/
  radius : ℕ
  /-- Current round size and distance sum. -/
  tally : Tally

/-- Frame the retained context and three binary round registers. -/
enc_structure encRegisters (encContext : κ ↪ List Bool) : Registers κ where
  context : encContext, fuel : encNat, radius : encNat, tally : encTally

/-- Enter the controller with only the source in its tally. -/
@[expose] def start (context : κ) (fuel : ℕ) : Registers κ :=
  ⟨context, fuel, 0, ⟨1, 0⟩⟩

/-- Advance to the next radius with the tally returned by the completed round. -/
@[expose] def Registers.advance (r : Registers κ) (next : Tally) : Registers κ :=
  ⟨r.context, r.fuel - 1, r.radius + 1, next⟩

private def verdictView : ControllerVerdict ≃ (ℕ ⊕ Bool) where
  toFun
    | .bad radius => .inl radius
    | .decided answer => .inr answer
  invFun := Sum.elim ControllerVerdict.bad ControllerVerdict.decided
  left_inv v := by cases v <;> rfl
  right_inv v := by cases v <;> rfl

/-- One tag followed by the tied radius or the reachability bit. -/
def encVerdict : ControllerVerdict ↪ List Bool :=
  verdictView.toEmbedding.trans (encSum encNat encBool)

/-- A pending round, a pending final membership query, or the terminal verdict. -/
abbrev State (κ ρ μ : Type) :=
  ((Registers κ × ρ) ⊕ (Registers κ × μ)) ⊕ Option ControllerVerdict

/-- Encode the suspended registers with the active callback state. -/
def encState {κ ρ μ : Type} (encContext : κ ↪ List Bool) (encRound : ρ ↪ List Bool)
    (encMember : μ ↪ List Bool) : State κ ρ μ ↪ List Bool :=
  encSum (encSum (encPair (encRegisters encContext) encRound)
    (encPair (encRegisters encContext) encMember)) (encOption encVerdict)

/-- Enter a supplied round, or reject if no round fuel remains. -/
@[expose] def enterRound (roundStart : Registers κ → ρ) (r : Registers κ) : State κ ρ μ :=
  if r.fuel = 0 then .inr none else .inl (.inl (r, roundStart r))

/-- Dispatch the round reply, retaining the current tally for a final membership query. -/
@[expose] def returnRound (roundStart : Registers κ → ρ) (memberStart : Registers κ → μ)
    (r : Registers κ) : Option RoundUpdate → State κ ρ μ
  | none => .inr none
  | some a =>
    if a.bad then .inr (some (.bad (r.radius + 1)))
    else if a.tally.count == r.tally.count then .inl (.inr (r, memberStart r))
    else enterRound roundStart (r.advance a.tally)

/-- Recover the verdict at a successful halt. Live states and rejecting halts have no verdict. -/
@[expose] def reply : State κ ρ μ → Option ControllerVerdict
  | .inr verdict => verdict
  | _ => none

/-- Run the two callbacks on the original input, retaining the outer registers across each
call. A final membership query uses the tally at the current radius. -/
@[expose] def machine {κ ρ μ : Type} (initial : Registers κ)
    (round : NondeterministicQueryMachine ρ) (roundStart : Registers κ → ρ)
    (roundReply : ρ → Option RoundUpdate)
    (member : NondeterministicQueryMachine μ) (memberStart : Registers κ → μ)
    (memberReply : μ → Option Bool) : NondeterministicQueryMachine (State κ ρ μ) where
  init := enterRound roundStart initial
  query
    | .inl (.inl (_, s)) => round.query s
    | .inl (.inr (_, s)) => member.query s
    | .inr _ => 0
  next
    | (.inl (.inl (r, s)), read, choice) =>
      if round.halted s then
        if choice then .inr none else returnRound roundStart memberStart r (roundReply s)
      else .inl (.inl (r, round.next (s, read, choice)))
    | (.inl (.inr (r, s)), read, choice) =>
      if member.halted s then
        .inr (if choice then none else (memberReply s).map ControllerVerdict.decided)
      else .inl (.inr (r, member.next (s, read, choice)))
    | (.inr verdict, _, _) => .inr verdict
  halted
    | .inl _ => false
    | .inr _ => true
  accept s := (reply s).isSome

/-- Re-enter the same transitions with different source or round registers. -/
theorem machine_withInit {κ ρ μ : Type} (r r' : Registers κ)
    (round : NondeterministicQueryMachine ρ) (roundStart : Registers κ → ρ)
    (roundReply : ρ → Option RoundUpdate)
    (member : NondeterministicQueryMachine μ) (memberStart : Registers κ → μ)
    (memberReply : μ → Option Bool) :
    (machine r round roundStart roundReply member memberStart memberReply).withInit
      (machine r' round roundStart roundReply member memberStart memberReply).init =
      machine r' round roundStart roundReply member memberStart memberReply := by
  unfold machine NondeterministicQueryMachine.withInit
  rfl

private theorem live_prefix {α : Type} (M : NondeterministicQueryMachine α)
    (input bits : List Bool) (s : α) (hlive : M.halted (M.replay input bits s) = false)
    (n : ℕ) : M.halted (M.replay input (bits.take n) s) = false := by
  cases hp : M.halted (M.replay input (bits.take n) s)
  · rfl
  · have he := M.replay_append input (bits.take n) (bits.drop n) s
    rw [List.take_append_drop, M.replay_of_halted input hp] at he
    rw [he, hp] at hlive
    cases hlive

private theorem split_call {α β : Type} (outer : NondeterministicQueryMachine α)
    (callee : NondeterministicQueryMachine β) (input : List Bool) (wrap : β → α)
    (hwrap : ∀ s, outer.halted (wrap s) = false)
    (hstep : ∀ s bit, callee.halted s = false →
      outer.step input (wrap s) bit = wrap (callee.step input s bit))
    (bits : List Bool) (s : β)
    (hh : outer.halted (outer.replay input bits (wrap s)) = true) :
    ∃ callBits selector rest, bits = callBits ++ selector :: rest ∧
      callee.FirstHalting input callBits s ∧
      outer.replay input callBits (wrap s) = wrap (callee.replay input callBits s) := by
  have hc : callee.halted (callee.replay input bits s) = true := by
    by_contra hn
    have hlive := Bool.eq_false_iff.mpr hn
    rw [outer.replay_map_of_live input callee wrap hstep bits s
      (fun n _ => live_prefix callee input bits s hlive n), hwrap] at hh
    cases hh
  obtain ⟨callBits, ⟨hp, hfirst, _⟩, _⟩ := callee.existsUnique_firstHalting_prefix input hc
  obtain ⟨rest, he⟩ := hp
  have hr := outer.replay_map_of_live input callee wrap hstep callBits s hfirst.2
  cases rest with
  | nil =>
    rw [List.append_nil] at he
    rw [← he, hr, hwrap] at hh
    cases hh
  | cons selector rest =>
    exact ⟨callBits, selector, rest, he.symm, hfirst, hr⟩

private theorem firstHalting_append_live_iff {α : Type} (M : NondeterministicQueryMachine α)
    (input before after : List Bool) (s : α)
    (hlive : M.halted (M.replay input before s) = false) :
    M.FirstHalting input (before ++ after) s ↔
      M.FirstHalting input after (M.replay input before s) := by
  constructor
  · intro h
    refine ⟨by simpa only [M.replay_append] using h.1, fun n hn => ?_⟩
    have hh := h.2 (before.length + n) (by simp only [List.length_append]; omega)
    rw [List.take_append, List.take_of_length_le (by omega : before.length ≤ before.length + n),
      Nat.add_sub_cancel_left, M.replay_append] at hh
    exact hh
  · intro h
    refine ⟨by simpa only [M.replay_append] using h.1, fun n hn => ?_⟩
    by_cases hle : n ≤ before.length
    · rw [List.take_append_of_le_length hle]
      exact live_prefix M input before s hlive n
    · rw [List.take_append, List.take_of_length_le (by omega : before.length ≤ n), M.replay_append]
      exact h.2 (n - before.length) (by simp only [List.length_append] at hn; omega)

private def readReply {β γ : Type} (callee : NondeterministicQueryMachine β)
    (ret : β → Option γ) (input : List Bool) (s : β) : List Bool → Option (γ × List Bool)
  | [] => none
  | bit :: rest =>
    if callee.halted s then
      if bit then none else (ret s).map fun value => (value, rest)
    else readReply callee ret input (callee.step input s bit) rest

private theorem readReply_iff {β γ : Type} (callee : NondeterministicQueryMachine β)
    (ret : β → Option γ) (input bits : List Bool) (s : β) (value : γ) (rest : List Bool) :
    readReply callee ret input s bits = some (value, rest) ↔
      ∃ callBits, bits = callBits ++ false :: rest ∧ callee.FirstHalting input callBits s ∧
        ret (callee.replay input callBits s) = some value := by
  induction bits generalizing s with
  | nil => simp [readReply, List.append_eq_nil_iff]
  | cons bit bits ih =>
    cases hhalt : callee.halted s
    · rw [readReply, ite_eq_right (by simp [hhalt]), ih]
      constructor
      · rintro ⟨callBits, rfl, hfirst, hret⟩
        exact ⟨bit :: callBits, rfl,
          (callee.firstHalting_cons_iff input _ _ _).mpr ⟨hhalt, hfirst⟩, hret⟩
      · rintro ⟨(_ | hd) , he, hfirst, hret⟩
        · have hh := hfirst.1
          rw [callee.replay_nil, hhalt] at hh
          cases hh
        · rename_i tl
          change bit :: bits = hd :: (tl ++ false :: rest) at he
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          exact ⟨tl, rfl, ((callee.firstHalting_cons_iff input _ _ _).mp hfirst).2, hret⟩
    · rw [readReply, ite_eq_left hhalt]
      suffices hh : (∃ callBits, bit :: bits = callBits ++ false :: rest ∧
          callee.FirstHalting input callBits s ∧
          ret (callee.replay input callBits s) = some value) ↔
          bit = false ∧ bits = rest ∧ ret s = some value by
        rw [hh]
        cases bit <;> simp [eq_comm, and_comm]
      constructor
      · rintro ⟨(_ | hd), he, hfirst, hret⟩
        · exact ⟨(List.cons.inj he).1, (List.cons.inj he).2, hret⟩
        · have hl := ((callee.firstHalting_cons_iff input _ _ _).mp hfirst).1
          rw [hhalt] at hl
          cases hl
      · rintro ⟨rfl, rfl, hret⟩
        exact ⟨[], rfl, ⟨hhalt, by simp⟩, hret⟩

private theorem successful_call_iff {α β γ : Type}
    (outer : NondeterministicQueryMachine α) (callee : NondeterministicQueryMachine β)
    (input : List Bool) (wrap : β → α) (ret : β → Option γ) (resume : γ → α)
    (reject final : α) (hreject : outer.halted reject = true) (hne : reject ≠ final)
    (hfinal : outer.halted final = true) (hwrap : ∀ s, outer.halted (wrap s) = false)
    (hlive : ∀ s bit, callee.halted s = false →
      outer.step input (wrap s) bit = wrap (callee.step input s bit))
    (hreturn : ∀ s bit, callee.halted s = true →
      outer.step input (wrap s) bit = if bit then reject else (ret s).elim reject resume)
    (s : β) (bits : List Bool) :
    outer.FirstHalting input bits (wrap s) ∧ outer.replay input bits (wrap s) = final ↔
      ∃ value rest, readReply callee ret input s bits = some (value, rest) ∧
        outer.FirstHalting input rest (resume value) ∧
        outer.replay input rest (resume value) = final := by
  have finish (callBits rest : List Bool) (bit : Bool) (h : callee.FirstHalting input callBits s) :
      let t := outer.step input (wrap (callee.replay input callBits s)) bit
      (outer.FirstHalting input (callBits ++ bit :: rest) (wrap s) ∧
        outer.replay input (callBits ++ bit :: rest) (wrap s) = final) ↔
      (outer.FirstHalting input rest t ∧ outer.replay input rest t = final) := by
    have hr := outer.replay_map_of_live input callee wrap hlive callBits s h.2
    have hp := firstHalting_append_live_iff outer input callBits (bit :: rest) (wrap s)
      (by rw [hr, hwrap])
    simp only [hp, outer.replay_append, hr, outer.firstHalting_cons_iff, hwrap, true_and,
      outer.replay_cons]
  constructor
  · rintro ⟨hfirst, hend⟩
    have hh : outer.halted (outer.replay input bits (wrap s)) = true := hend ▸ hfinal
    obtain ⟨callBits, bit, rest, rfl, hc, _⟩ :=
      split_call outer callee input wrap hwrap hlive bits s hh
    have hs := (finish callBits rest bit hc).mp ⟨hfirst, hend⟩
    rw [hreturn _ _ hc.1] at hs
    cases bit
    · simp only [Bool.false_eq_true, ite_false] at hs
      cases he : ret (callee.replay input callBits s) with
      | none =>
        rw [he, Option.elim_none, outer.replay_of_halted input hreject] at hs
        exact (hne hs.2).elim
      | some value =>
        rw [he, Option.elim_some] at hs
        exact ⟨value, rest, (readReply_iff _ _ _ _ _ _ _).mpr ⟨_, rfl, hc, he⟩, hs⟩
    · simp only [ite_true, outer.replay_of_halted input hreject] at hs
      exact (hne hs.2).elim
  · rintro ⟨value, rest, hread, hs⟩
    obtain ⟨callBits, rfl, hc, hret⟩ := (readReply_iff _ _ _ _ _ _ _).mp hread
    apply (finish callBits rest false hc).mpr
    simpa only [hreturn _ _ hc.1, Bool.false_eq_true, ite_false, hret, Option.elim_some] using hs

private theorem call_returns_by {β : Type} (callee : NondeterministicQueryMachine β)
    (input bits : List Bool) (s : β) (clock : ℕ)
    (hclock : (callee.withInit s).HaltsWithin input clock)
    (hlen : clock < bits.length) :
    ∃ callBits selector rest, bits = callBits ++ selector :: rest ∧ callBits.length ≤ clock ∧
      callee.FirstHalting input callBits s := by
  have htake : (bits.take clock).length = clock := List.length_take_of_le hlen.le
  have hhalt := hclock (bits.take clock) htake
  have hh : callee.halted (callee.replay input (bits.take clock) s) = true := hhalt
  obtain ⟨callBits, ⟨hpre, hfirst, _⟩, _⟩ := callee.existsUnique_firstHalting_prefix input hh
  have hcl : callBits.length ≤ clock := htake ▸ hpre.length_le
  obtain ⟨suffix, hsuffix⟩ := hpre.trans (List.take_prefix clock bits)
  cases suffix with
  | nil =>
    rw [List.append_nil] at hsuffix
    rw [hsuffix] at hcl
    omega
  | cons selector rest => exact ⟨callBits, selector, rest, hsuffix.symm, hcl, hfirst⟩

section Replay

variable (initial : Registers κ)
  (round : NondeterministicQueryMachine ρ) (roundStart : Registers κ → ρ)
  (roundReply : ρ → Option RoundUpdate)
  (member : NondeterministicQueryMachine μ) (memberStart : Registers κ → μ)
  (memberReply : μ → Option Bool) (input : List Bool)

local notation "M" => machine initial round roundStart roundReply member memberStart memberReply

private def roundState (r : Registers κ) (s : ρ) : State κ ρ μ := .inl (.inl (r, s))

private def memberState (r : Registers κ) (s : μ) : State κ ρ μ := .inl (.inr (r, s))

private theorem round_step (r : Registers κ) (s : ρ) (bit : Bool)
    (h : round.halted s = false) :
    (M).step input (roundState r s) bit = roundState r (round.step input s bit) := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read,
    machine, roundState, h]

private theorem member_step (r : Registers κ) (s : μ) (bit : Bool)
    (h : member.halted s = false) :
    (M).step input (memberState r s) bit = memberState r (member.step input s bit) := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read,
    machine, memberState, h]

private theorem round_return (r : Registers κ) (s : ρ) (bit : Bool)
    (h : round.halted s = true) :
    (M).step input (roundState r s) bit =
      if bit then .inr none else returnRound roundStart memberStart r (roundReply s) := by
  simp [NondeterministicQueryMachine.step, machine, roundState, h]

private theorem member_return (r : Registers κ) (s : μ) (bit : Bool)
    (h : member.halted s = true) :
    (M).step input (memberState r s) bit =
      .inr (if bit then none else (memberReply s).map ControllerVerdict.decided) := by
  simp [NondeterministicQueryMachine.step, machine, memberState, h]

/-- Replay the existing round loop using the supplied callbacks and a stream of selectors.
On success the result records the verdict and the selector suffix still unused. -/
def replayRounds (r : Registers κ) (bits : List Bool) :
    Option (Option ControllerVerdict × List Bool) :=
  (runRoundsWith (m := StateT (List Bool) Option)
    (fun fuel radius tally => readReply round roundReply input
      (roundStart ⟨r.context, fuel, radius, tally⟩))
    (fun fuel radius tally => readReply member memberReply input
      (memberStart ⟨r.context, fuel, radius, tally⟩)) r.fuel r.radius r.tally).run bits

private theorem replayRounds_step (r : Registers κ) (bits : List Bool) (hf : r.fuel ≠ 0) :
    replayRounds round roundStart roundReply member memberStart memberReply input r bits =
      match readReply round roundReply input (roundStart r) bits with
      | none => none
      | some (a, rest) =>
        if a.bad then some (some (.bad (r.radius + 1)), rest)
        else if a.tally.count == r.tally.count then
          (readReply member memberReply input (memberStart r) rest).map fun (hit, suffix) =>
            (some (.decided hit), suffix)
        else replayRounds round roundStart roundReply member memberStart memberReply input
          (r.advance a.tally) rest := by
  rcases r with ⟨context, _ | fuel, radius, tally⟩
  · exact (hf rfl).elim
  · simp only [replayRounds, runRoundsWith, StateT.run, bind, StateT.bind]
    cases hread : readReply round roundReply input
        (roundStart ⟨context, fuel + 1, radius, tally⟩) bits with
    | none => rfl
    | some p =>
      obtain ⟨a, rest⟩ := p
      rw [Option.bind_some]
      dsimp only
      by_cases hbad : a.bad = true
      · simp only [ite_eq_left hbad]; rfl
      · simp only [ite_eq_right hbad]
        by_cases hcount : (a.tally.count == tally.count) = true
        · simp only [ite_eq_left hcount]
          change (readReply member memberReply input
            (memberStart ⟨context, fuel + 1, radius, tally⟩) rest).bind _ = _
          cases readReply member memberReply input
              (memberStart ⟨context, fuel + 1, radius, tally⟩) rest <;> rfl
        · simp only [ite_eq_right hcount]; rfl

private theorem finish_iff (terminal : Option ControllerVerdict) (verdict : ControllerVerdict)
    (bits : List Bool) :
    (M).FirstHalting input bits (.inr terminal) ∧
        (M).replay input bits (.inr terminal) = .inr (some verdict) ↔
      bits = [] ∧ terminal = some verdict := by
  cases bits with
  | nil => simp [NondeterministicQueryMachine.FirstHalting, machine]
  | cons bit bits =>
    rw [(M).firstHalting_cons_iff]
    simp [machine]

private theorem member_success_iff (r : Registers κ) (bits : List Bool)
    (verdict : ControllerVerdict) :
    (M).FirstHalting input bits (memberState r (memberStart r)) ∧
        (M).replay input bits (memberState r (memberStart r)) = .inr (some verdict) ↔
      ∃ hit, readReply member memberReply input (memberStart r) bits = some (hit, []) ∧
        ControllerVerdict.decided hit = verdict := by
  rw [successful_call_iff (M) member input (memberState r) memberReply
    (fun hit => .inr (some (.decided hit))) (.inr none) (.inr (some verdict))
    rfl (by simp) rfl (fun _ => rfl)
    (member_step initial round roundStart roundReply member memberStart memberReply input r) ?_]
  · simp only [finish_iff, Option.some.injEq]
    constructor
    · rintro ⟨hit, rest, hr, rfl, hv⟩
      exact ⟨hit, hr, hv⟩
    · rintro ⟨hit, hr, hv⟩
      exact ⟨hit, [], hr, rfl, hv⟩
  · intro t bit hh
    rw [member_return _ _ _ _ _ _ _ _ _ _ _ hh]
    cases bit <;> cases memberReply t <;> rfl

/-- Successful first-halting selectors are exactly the complete selector streams consumed by
the existing round loop. The selector list is kept intact, so equal verdicts from distinct
callback occurrences remain distinct. -/
theorem firstHalting_iff_replayRounds (bits : List Bool) (verdict : ControllerVerdict) :
    (M).FirstHalting input bits (M).init ∧
        (M).run input bits = .inr (some verdict) ↔
      replayRounds round roundStart roundReply member memberStart memberReply input initial bits =
        some (some verdict, []) := by
  have aux (r : Registers κ) (bits : List Bool) :
      (M).FirstHalting input bits (enterRound roundStart r) ∧
          (M).replay input bits (enterRound roundStart r) = .inr (some verdict) ↔
        replayRounds round roundStart roundReply member memberStart memberReply input r bits =
          some (some verdict, []) := by
    induction hf : r.fuel using Nat.strongRecOn generalizing r bits with
    | ind fuel ih =>
      by_cases hz : r.fuel = 0
      · rw [enterRound, ite_eq_left hz, finish_iff]
        constructor
        · rintro ⟨_, he⟩
          cases he
        · intro h
          unfold replayRounds at h
          rw [hz, runRoundsWith] at h
          cases h
      · have hentry : enterRound (μ := μ) roundStart r = roundState r (roundStart r) := by
          simp only [enterRound, ite_eq_right hz, roundState]
        rw [hentry, successful_call_iff (M) round input (roundState r) roundReply
          (fun a => returnRound roundStart memberStart r (some a))
          (.inr none) (.inr (some verdict)) rfl (by simp) rfl (fun _ => rfl)
          (round_step initial round roundStart roundReply member memberStart memberReply input r)
          ?_, replayRounds_step _ _ _ _ _ _ _ r bits hz]
        · cases hread : readReply round roundReply input (roundStart r) bits with
          | none => simp
          | some p =>
            obtain ⟨a, rest⟩ := p
            simp only [Option.some.injEq, Prod.mk.injEq, and_assoc, exists_and_left,
              exists_eq_left']
            by_cases hbad : a.bad = true
            · rw [returnRound, ite_eq_left hbad, ite_eq_left hbad, finish_iff]
              simp [and_comm]
            · by_cases hcount : (a.tally.count == r.tally.count) = true
              · rw [returnRound, ite_eq_right hbad, ite_eq_left hcount,
                  ite_eq_right hbad, ite_eq_left hcount]
                rw [show Sum.inl (Sum.inr (r, memberStart r)) =
                  memberState (ρ := ρ) r (memberStart r) from rfl, member_success_iff]
                cases hmember : readReply member memberReply input (memberStart r) rest
                · simp
                · rename_i p
                  obtain ⟨hit, suffix⟩ := p
                  cases hit <;> simp [and_comm]
              · rw [returnRound, ite_eq_right hbad, ite_eq_right hcount,
                  ite_eq_right hbad, ite_eq_right hcount]
                have hlt : (r.advance a.tally).fuel < fuel := by
                  simp only [Registers.advance]
                  omega
                exact ih _ hlt (r.advance a.tally) rest rfl
        · intro t bit hh
          rw [round_return _ _ _ _ _ _ _ _ _ _ _ hh]
          cases bit <;> cases roundReply t <;> rfl
  exact aux initial bits

/-- A register invariant preserved when a round grows without tying. -/
@[expose] def Closed (P : Registers κ → Prop) : Prop :=
  ∀ r, P r → ∀ bits a,
    roundReply (round.replay input bits (roundStart r)) = some a →
    a.bad = false → a.tally.count ≠ r.tally.count → P (r.advance a.tally)

/-- A round fuel bound, the common round clock and the final membership clock bound every
source branch. Both return selectors and all rejections are charged to the same clock. -/
theorem haltsWithin (P : Registers κ → Prop) (hp : P initial)
    (hclosed : Closed round roundStart roundReply input P) (roundClock memberClock : ℕ)
    (hround : ∀ r, P r → (round.withInit (roundStart r)).HaltsWithin input roundClock)
    (hmember : ∀ r, P r → (member.withInit (memberStart r)).HaltsWithin input memberClock) :
    (M).HaltsWithin input (initial.fuel * (roundClock + 1) + memberClock + 1) := by
  have memberHalts (r : Registers κ) (hr : P r) (bits : List Bool)
      (hlen : memberClock < bits.length) :
      (M).halted ((M).replay input bits (memberState r (memberStart r))) = true := by
    obtain ⟨callBits, selector, rest, rfl, _, hfirst⟩ :=
      call_returns_by member input bits (memberStart r) memberClock (hmember r hr) hlen
    rw [(M).replay_append,
      (M).replay_map_of_live input member (memberState r)
        (member_step initial round roundStart roundReply member memberStart memberReply input r)
        callBits (memberStart r) hfirst.2,
      (M).replay_cons, member_return _ _ _ _ _ _ _ _ _ _ _ hfirst.1]
    rw [(M).replay_of_halted input (by rfl)]
    rfl
  have roundHalts (r : Registers κ) (hr : P r) (bits : List Bool)
      (hlen : r.fuel * (roundClock + 1) + memberClock + 1 ≤ bits.length) :
      (M).halted ((M).replay input bits (enterRound roundStart r)) = true := by
    induction hfuel : r.fuel using Nat.strongRecOn generalizing r bits with
    | ind fuel ih =>
      by_cases hzero : r.fuel = 0
      · rw [enterRound, ite_eq_left hzero, (M).replay_of_halted input (by rfl)]
        rfl
      · have hlen' : roundClock < bits.length := by
          have hle := Nat.mul_le_mul_right (roundClock + 1) (show 1 ≤ r.fuel by omega)
          rw [Nat.one_mul] at hle
          omega
        obtain ⟨callBits, selector, rest, rfl, hcl, hfirst⟩ :=
          call_returns_by round input bits (roundStart r) roundClock (hround r hr) hlen'
        let t := round.replay input callBits (roundStart r)
        have hentry : enterRound (μ := μ) roundStart r = roundState r (roundStart r) := by
          simp only [enterRound, ite_eq_right hzero, roundState]
        rw [hentry, (M).replay_append,
          (M).replay_map_of_live input round (roundState r)
            (round_step initial round roundStart roundReply member memberStart memberReply input r)
            callBits (roundStart r) hfirst.2,
          (M).replay_cons, round_return _ _ _ _ _ _ _ _ _ _ _ hfirst.1]
        simp only [List.length_append, List.length_cons] at hlen
        have hreject : (M).halted ((M).replay input rest (.inr none)) = true := by
          rw [(M).replay_of_halted input (by rfl)]
          rfl
        cases selector
        · change (M).halted ((M).replay input rest (returnRound roundStart memberStart r
            (roundReply t))) = true
          cases hret : roundReply t with
          | none => exact hreject
          | some a =>
            by_cases hbad : a.bad = true
            · rw [returnRound, ite_eq_left hbad, (M).replay_of_halted input (by rfl)]
              rfl
            · by_cases hstable : (a.tally.count == r.tally.count) = true
              · rw [returnRound, ite_eq_right hbad, ite_eq_left hstable]
                have hle := Nat.mul_le_mul_right (roundClock + 1) (show 1 ≤ r.fuel by omega)
                rw [Nat.one_mul] at hle
                exact memberHalts r hr rest (by omega)
              · rw [returnRound, ite_eq_right hbad, ite_eq_right hstable]
                have hnext : (r.advance a.tally).fuel + 1 = r.fuel := by
                  simp only [Registers.advance]
                  omega
                have hlt : (r.advance a.tally).fuel < fuel := by omega
                have hprod : r.fuel * (roundClock + 1) =
                    (r.advance a.tally).fuel * (roundClock + 1) + (roundClock + 1) := by
                  rw [← hnext, Nat.add_mul, Nat.one_mul]
                have hp' : P (r.advance a.tally) :=
                  hclosed r hr callBits a hret (Bool.eq_false_iff.mpr hbad)
                    (by simpa only [beq_iff_eq] using hstable)
                exact ih _ hlt (r.advance a.tally) hp' rest (by omega) rfl
        · exact hreject
  intro bits hb
  exact roundHalts initial hp bits hb.ge

private def Invariant (P : Registers κ → Prop) : State κ ρ μ → Prop
  | .inl (.inl (r, s)) => P r ∧ 0 < r.fuel ∧ r.fuel + r.radius = initial.fuel + initial.radius ∧
      ∃ bits, round.replay input bits (roundStart r) = s
  | .inl (.inr (r, s)) => P r ∧
      ∃ bits, member.replay input bits (memberStart r) = s
  | .inr (some (.bad k)) => k ≤ initial.fuel + initial.radius
  | .inr _ => True

private theorem invariant_enter {P : Registers κ → Prop} (r : Registers κ)
    (hp : P r) (hr : r.fuel + r.radius = initial.fuel + initial.radius) :
    Invariant initial round roundStart member memberStart input P (enterRound roundStart r) := by
  by_cases hz : r.fuel = 0
  · simp [enterRound, hz, Invariant]
  · rw [enterRound, ite_eq_right hz]
    exact ⟨hp, Nat.pos_of_ne_zero hz, hr, [], rfl⟩

private theorem invariant_step {P : Registers κ → Prop}
    (hclosed : Closed round roundStart roundReply input P)
    (s : State κ ρ μ) (bit : Bool)
    (hs : Invariant initial round roundStart member memberStart input P s) :
    Invariant initial round roundStart member memberStart input P ((M).step input s bit) := by
  rcases s with (⟨r, t⟩ | ⟨r, t⟩) | verdict
  · obtain ⟨hp, hfuel, hr, bits, ht⟩ := hs
    by_cases hlive : round.halted t = false
    · have hstep := round_step initial round roundStart roundReply member memberStart memberReply
        input r t bit hlive
      rw [show Sum.inl (Sum.inl (r, t)) = roundState (μ := μ) r t from rfl, hstep]
      exact ⟨hp, hfuel, hr, bits ++ [bit], by
        rw [round.replay_append, ht, round.replay_cons, round.replay_nil]⟩
    · have hhalt := Bool.eq_true_of_not_eq_false hlive
      rw [show Sum.inl (Sum.inl (r, t)) = roundState (μ := μ) r t from rfl,
        round_return _ _ _ _ _ _ _ _ _ _ _ hhalt]
      cases bit
      · change Invariant initial round roundStart member memberStart input P
          (returnRound roundStart memberStart r (roundReply t))
        cases ha : roundReply t with
        | none => trivial
        | some a =>
          by_cases hbad : a.bad = true
          · rw [returnRound, ite_eq_left hbad]
            change r.radius + 1 ≤ initial.fuel + initial.radius
            omega
          · by_cases heq : (a.tally.count == r.tally.count) = true
            · rw [returnRound, ite_eq_right hbad, ite_eq_left heq]
              exact ⟨hp, [], rfl⟩
            · rw [returnRound, ite_eq_right hbad, ite_eq_right heq]
              apply invariant_enter
              · exact hclosed r hp bits a (ht.symm ▸ ha)
                  (Bool.eq_false_iff.mpr hbad) (by simpa only [beq_iff_eq] using heq)
              · simp only [Registers.advance]
                omega
      · trivial
  · obtain ⟨hp, bits, ht⟩ := hs
    by_cases hlive : member.halted t = false
    · have hstep := member_step initial round roundStart roundReply member memberStart memberReply
        input r t bit hlive
      rw [show Sum.inl (Sum.inr (r, t)) = memberState (ρ := ρ) r t from rfl, hstep]
      exact ⟨hp, bits ++ [bit], by
        rw [member.replay_append, ht, member.replay_cons, member.replay_nil]⟩
    · have hhalt := Bool.eq_true_of_not_eq_false hlive
      rw [show Sum.inl (Sum.inr (r, t)) = memberState (ρ := ρ) r t from rfl,
        member_return _ _ _ _ _ _ _ _ _ _ _ hhalt]
      cases bit <;> cases memberReply t <;> trivial
  · have hhalt : (M).halted (.inr verdict) = true := rfl
    rwa [(M).step_of_halted input hhalt]

/-- The entire controller fits the suspended registers and one live callback state.
The register invariant may be taken from the verified round bounds. -/
theorem length_run_le (encContext : κ ↪ List Bool) (encRound : ρ ↪ List Bool)
    (encMember : μ ↪ List Bool) (P : Registers κ → Prop) (hp : P initial)
    (hclosed : Closed round roundStart roundReply input P)
    (registerBound roundBound memberBound : ℕ)
    (hreg : ∀ r, P r → (encRegisters encContext r).length ≤ registerBound)
    (hround : ∀ r, P r → ∀ bits,
      (encRound (round.replay input bits (roundStart r))).length ≤ roundBound)
    (hmember : ∀ r, P r → ∀ bits,
      (encMember (member.replay input bits (memberStart r))).length ≤ memberBound)
    (choices : List Bool) :
    (encState encContext encRound encMember ((M).run input choices)).length ≤
      2 * registerBound + max roundBound memberBound +
        (encNat (initial.fuel + initial.radius)).length + 4 := by
  have hreach (bits : List Bool) :
      Invariant initial round roundStart member memberStart input P ((M).run input bits) := by
    induction bits using List.reverseRecOn with
    | nil => exact invariant_enter initial round roundStart member memberStart input initial hp rfl
    | append_singleton bits bit ih =>
      rw [(M).run_append, (M).replay_cons, (M).replay_nil]
      exact invariant_step initial round roundStart roundReply member memberStart memberReply
        input hclosed _ bit ih
  have h := hreach choices
  generalize (M).run input choices = state at h ⊢
  rcases state with (⟨r, t⟩ | ⟨r, t⟩) | (_ | verdict)
  · obtain ⟨hr, _, _, bits, rfl⟩ := h
    have hc := hround r hr bits
    have hg := hreg r hr
    simp only [encState, encSum_inl, List.length_cons, length_encPair]
    omega
  · obtain ⟨hr, bits, rfl⟩ := h
    have hc := hmember r hr bits
    have hg := hreg r hr
    simp only [encState, encSum_inl, encSum_inr, List.length_cons, length_encPair]
    omega
  · simp [encState, encOption]
  · cases verdict with
    | bad k =>
      change k ≤ initial.fuel + initial.radius at h
      have hk := length_encNat_mono h
      change (encNat k).length + 3 ≤ _
      omega
    | decided answer =>
      change 4 ≤ _
      omega

end Replay

section Native

variable (encContext : κ ↪ List Bool) (encRound : ρ ↪ List Bool) (encMember : μ ↪ List Bool)

local notation "R" => encRegisters encContext
local notation "P" => encPair R encRound
local notation "Q" => encPair R encMember
local notation "F" => encOption encVerdict
local notation "E" => encState encContext encRound encMember
/-- A query answer paired with the selected branch bit. -/
abbrev encChoice := encPair (encOption encBool) encBool

private theorem round_budget {α : Type} {enc : α ↪ List Bool} {budget : α → ℕ}
    {r : α → Registers κ} {s : α → ρ}
    (hr : ComputableInSpace r enc R budget) (hs : ComputableInSpace s enc encRound budget) :
    ComputableInSpace (fun a => roundState (μ := μ) (r a) (s a)) enc E budget := by
  have htag := of_inO (ComputableInO.inl (encSum P Q) F)
  have hphase := of_inO (ComputableInO.inl P Q)
  exact budget_comp_linear htag (budget_comp_linear hphase (budget_prod hr hs))

private theorem member_budget {α : Type} {enc : α ↪ List Bool} {budget : α → ℕ}
    {r : α → Registers κ} {s : α → μ}
    (hr : ComputableInSpace r enc R budget) (hs : ComputableInSpace s enc encMember budget) :
    ComputableInSpace (fun a => memberState (ρ := ρ) (r a) (s a)) enc E budget := by
  have htag := of_inO (ComputableInO.inl (encSum P Q) F)
  have hphase := of_inO (ComputableInO.inr P Q)
  exact budget_comp_linear htag (budget_comp_linear hphase (budget_prod hr hs))

private theorem finish_budget {α : Type} {enc : α ↪ List Bool} {budget : α → ℕ}
    {v : α → Option ControllerVerdict} (hv : ComputableInSpace v enc F budget) :
    ComputableInSpace (fun a => Sum.inr (v a)) enc E budget := by
  have htag := of_inO (ComputableInO.inr (encSum P Q) F)
  exact budget_comp_linear htag hv

/-- Load a round-loop entry from encoded caller registers, rejecting exhausted fuel. -/
theorem enterRound_inSpace (roundStart : Registers κ → ρ)
    (hstart : ComputableInSpace roundStart R encRound (fun r => (R r).length)) :
    ComputableInSpace (enterRound roundStart) R E (fun r => (R r).length) := by
  have hr := budget_id (enc := R) (.refl _)
  have hzero := budget_natIsZero (encRegisters_fuel_budget encContext hr)
  have hentry := round_budget encContext encRound encMember hr hstart
  have hreject := budget_const (encIn := R) (encB := E) (.inr none) (.refl _)
  exact (budget_ite hzero hreject hentry).of_enc_eq fun r => by simp [enterRound, roundState]

/-- Decode the optional source verdict in linear workspace. -/
theorem reply_inSpace :
    ComputableInSpace reply E F (fun s => (E s).length) := by
  have hlive := budget_const (encIn := encSum P Q) (encB := F) none (.refl _)
  have hend := budget_id (enc := F) (.refl _)
  exact (sumElim hlive hend).of_enc_eq fun | .inl _ | .inr _ => rfl

private theorem returnRound_inSpace (roundStart : Registers κ → ρ)
    (memberStart : Registers κ → μ)
    (hr : ComputableInSpace roundStart R encRound (fun r => (R r).length))
    (hm : ComputableInSpace memberStart R encMember (fun r => (R r).length)) :
    ComputableInSpace (fun p : Registers κ × Option RoundUpdate =>
      returnRound roundStart memberStart p.1 p.2) (encPair R (encOption encRoundUpdate)) E
      (fun p => (encPair R (encOption encRoundUpdate) p).length) := by
  have hreg := fst R encRoundUpdate
  have hu := snd R encRoundUpdate
  have hnew := encRoundUpdate_tally_budget hu
  have hcount := budget_natEq (encTally_count_budget hnew)
    (encTally_count_budget (encRegisters_tally_budget encContext hreg))
  have hbad := encRoundUpdate_bad_budget hu
  have hnext := encRegisters_mk_budget encContext (encRegisters_context_budget encContext hreg)
    (budget_natPred (encRegisters_fuel_budget encContext hreg))
    (budget_natSucc (encRegisters_radius_budget encContext hreg)) hnew
  have hcontinue := budget_comp_linear (enterRound_inSpace encContext encRound encMember _ hr)
    hnext
  have hmember := member_budget encContext encRound encMember hreg (budget_comp_linear hm hreg)
  have htag : ComputableInSpace ControllerVerdict.bad encNat encVerdict
      (fun v => (encNat v).length) :=
    (of_inO (ComputableInO.inl encNat encBool)).of_enc_eq fun _ => rfl
  have htied := finish_budget encContext encRound encMember (budget_optionSome
    (budget_comp_linear htag (budget_natSucc (encRegisters_radius_budget encContext hreg))))
  have hsome := budget_ite hbad htied (budget_ite hcount hmember hcontinue)
  have hnone := budget_const (encIn := R) (encB := E) (.inr none) (.refl _)
  refine (optionElimSnd hnone hsome).of_enc_eq ?_
  rintro ⟨r, a | _⟩
  · rfl
  · rfl

variable (initial : Registers κ)
  (round : NondeterministicQueryMachine ρ) (roundStart : Registers κ → ρ)
  (roundReply : ρ → Option RoundUpdate)
  (member : NondeterministicQueryMachine μ) (memberStart : Registers κ → μ)
  (memberReply : μ → Option Bool)

local notation "M" => machine initial round roundStart roundReply member memberStart memberReply

/-- Query the active callback's read position on the unchanged input. -/
theorem query_inSpace
    (hr : ComputableInSpace round.query encRound encNat (fun r => (encRound r).length))
    (hm : ComputableInSpace member.query encMember encNat (fun t => (encMember t).length)) :
    ComputableInSpace (M).query E encNat (fun s => (E s).length) :=
  (sumElim (sumElim (budget_comp_linear hr (snd R encRound))
    (budget_comp_linear hm (snd R encMember)))
    (budget_const (encIn := F) (encB := encNat) 0 (.refl _))).of_enc_eq fun
      | .inl (.inl _) | .inl (.inr _) | .inr _ => rfl

/-- The phase tag distinguishes terminal from active rounds and membership calls. -/
theorem halted_inSpace :
    ComputableInSpace (M).halted E encBool (fun s => (E s).length) :=
  (sumElim (budget_const (encIn := encSum P Q) (encB := encBool) false (.refl _))
    (budget_const (encIn := F) (encB := encBool) true (.refl _))).of_enc_eq fun
      | .inl _ | .inr _ => rfl

/-- Advance one selector, preserving the suspended controller registers across a live call. -/
theorem next_inSpace
    (hroundStart : ComputableInSpace roundStart R encRound (fun r => (R r).length))
    (hmemberStart : ComputableInSpace memberStart R encMember (fun r => (R r).length))
    (hroundReply : ComputableInSpace roundReply encRound (encOption encRoundUpdate)
      (fun s => (encRound s).length))
    (hmemberReply : ComputableInSpace memberReply encMember (encOption encBool)
      (fun s => (encMember s).length))
    (hroundHalt : ComputableInSpace round.halted encRound encBool (fun s => (encRound s).length))
    (hmemberHalt : ComputableInSpace member.halted encMember encBool
      (fun s => (encMember s).length))
    (hroundNext : ComputableInSpace round.next (encPair encRound encChoice) encRound
      (fun p => (encPair encRound encChoice p).length))
    (hmemberNext : ComputableInSpace member.next (encPair encMember encChoice) encMember
      (fun p => (encPair encMember encChoice p).length)) :
    ComputableInSpace (M).next (encPair E encChoice) E
      (fun p => (encPair E encChoice p).length) := by
  have hroundFrame := fst P encChoice
  have hroundRead := snd P encChoice
  have hroundRegs := fst' hroundFrame
  have hroundState := snd' hroundFrame
  have hroundBit := snd' hroundRead
  have hreturned := budget_comp_linear
    (returnRound_inSpace encContext encRound encMember _ _ hroundStart hmemberStart)
    (budget_prod hroundRegs (budget_comp_linear hroundReply hroundState))
  have hroundReject := budget_const (encIn := encPair P encChoice) (encB := E)
    (.inr none) (.refl _)
  have hroundContinue := round_budget encContext encRound encMember hroundRegs
    (budget_comp_linear hroundNext (budget_prod hroundState hroundRead))
  have hround := budget_ite (budget_comp_linear hroundHalt hroundState)
    (budget_ite hroundBit hroundReject hreturned) hroundContinue
  have hmFrame := fst Q encChoice
  have hmRead := snd Q encChoice
  have hmRegs := fst' hmFrame
  have hmState := snd' hmFrame
  have hmBit := snd' hmRead
  have hdecide : ComputableInSpace ControllerVerdict.decided encBool encVerdict
      (fun v => (encBool v).length) :=
    (of_inO (ComputableInO.inr encNat encBool)).of_enc_eq fun _ => rfl
  have hmReply := budget_comp_linear hmemberReply hmState
  have hmHit := budget_comp_linear hdecide (budget_optionGetD false hmReply)
  have hmNone := budget_const (encIn := encPair Q encChoice) (encB := F) none (.refl _)
  have hmResult := budget_ite (budget_optionIsSome hmReply) (budget_optionSome hmHit) hmNone
  have hmReject := budget_const (encIn := encPair Q encChoice) (encB := E)
    (.inr none) (.refl _)
  have hmDone := finish_budget encContext encRound encMember hmResult
  have hmContinue := member_budget encContext encRound encMember hmRegs
    (budget_comp_linear hmemberNext (budget_prod hmState hmRead))
  have hmember := budget_ite (budget_comp_linear hmemberHalt hmState)
    (budget_ite hmBit hmReject hmDone) hmContinue
  have hfinished := finish_budget encContext encRound encMember (fst F encChoice)
  refine (sumElimFst (sumElimFst hround hmember) hfinished).of_enc_eq ?_
  rintro ⟨(⟨r, s⟩ | ⟨r, s⟩) | verdict, read, bit⟩
  · cases bit <;> cases round.halted s <;> rfl
  · cases bit <;> cases hh : member.halted s <;> cases ha : memberReply s <;>
      simp [machine, memberState, hh, ha]
  · rfl

open NondeterministicQueryMachine in
/-- Compile the source loop from native callbacks and an input-dependent register initializer.
The caller supplies a common encoded-state budget for the complete runs. -/
theorem exists_routines {α : Type} (enc : α ↪ List Bool) (S : α → ℕ)
    (registers : α → Registers κ)
    (hregisters : ComputableInSpace registers enc R S)
    (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hroundStart : ComputableInSpace roundStart R encRound (fun r => (R r).length))
    (hmemberStart : ComputableInSpace memberStart R encMember (fun r => (R r).length))
    (hroundReply : ComputableInSpace roundReply encRound (encOption encRoundUpdate)
      (fun s => (encRound s).length))
    (hmemberReply : ComputableInSpace memberReply encMember (encOption encBool)
      (fun s => (encMember s).length))
    (hroundQuery : ComputableInSpace round.query encRound encNat (fun s => (encRound s).length))
    (hmemberQuery : ComputableInSpace member.query encMember encNat (fun s => (encMember s).length))
    (hroundHalt : ComputableInSpace round.halted encRound encBool (fun s => (encRound s).length))
    (hmemberHalt : ComputableInSpace member.halted encMember encBool
      (fun s => (encMember s).length))
    (hroundNext : ComputableInSpace round.next (encPair encRound encChoice) encRound
      (fun p => (encPair encRound encChoice p).length))
    (hmemberNext : ComputableInSpace member.next (encPair encMember encChoice) encMember
      (fun p => (encPair encMember encChoice p).length))
    (hstates : ∃ c, ∀ a bits, (E ((machine (registers a) round roundStart roundReply
      member memberStart memberReply).run (enc a) bits)).length ≤ c * S a) :
    Nonempty (Routines (M) (fun a => enterRound roundStart (registers a)) enc S) := by
  have hq := query_inSpace encContext encRound encMember initial round roundStart roundReply
    member memberStart memberReply hroundQuery hmemberQuery
  have hn := next_inSpace encContext encRound encMember initial round roundStart roundReply
    member memberStart memberReply hroundStart hmemberStart hroundReply hmemberReply
    hroundHalt hmemberHalt hroundNext hmemberNext
  have hh := halted_inSpace encContext encRound encMember initial round roundStart roundReply
    member memberStart memberReply
  have ha : ComputableInSpace (M).accept E encBool (fun s => (E s).length) :=
    budget_optionIsSome (reply_inSpace encContext encRound encMember)
  have hinit := budget_comp_linear
    (enterRound_inSpace encContext encRound encMember roundStart hroundStart) hregisters
  obtain ⟨c, hstates⟩ := hstates
  refine (M).exists_routines hq hn hh ha _ S hlog hinit ⟨c, fun a bits => ?_⟩
  change (E (((M).withInit (machine (registers a) round roundStart roundReply member
    memberStart memberReply).init).run (enc a) bits)).length ≤ c * S a
  rw [machine_withInit]
  exact hstates a bits

open NondeterministicQueryMachine in
/-- Each successful selector list of the round loop determines exactly one accepting native
occurrence list. The replay specification retains the full source verdict. -/
theorem native_firstHalting_accept_iff {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (registers : α → Registers κ)
    (routines : Routines (M) (fun a => enterRound roundStart (registers a)) enc S)
    (a : α) (bits : List Bool) :
    (∃! indices, ∃ final,
      Native.replayChoices routines.I routines.P routines.F routines.C
        (routines.machine.initCfg (enc a)) indices = some (bits, final) ∧
        final.Halted ∧ final.output = [true]) ↔
      ∃ verdict, replayRounds round roundStart roundReply member memberStart memberReply (enc a)
        (registers a) bits = some (some verdict, []) := by
  have hinit := machine_withInit initial (registers a) round roundStart roundReply
    member memberStart memberReply
  have hspec (verdict : ControllerVerdict) :
      (M).FirstHalting (enc a) bits (enterRound roundStart (registers a)) ∧
          (M).replay (enc a) bits (enterRound roundStart (registers a)) =
            .inr (some verdict) ↔
        replayRounds round roundStart roundReply member memberStart memberReply (enc a)
          (registers a) bits = some (some verdict, []) := by
    have h := firstHalting_iff_replayRounds (registers a) round roundStart roundReply
      member memberStart memberReply (enc a) bits verdict
    rw [← hinit, init_withInit, firstHalting_withInit, run_withInit] at h
    exact h
  have haccept (s : State κ ρ μ) :
      (M).accept s = true ↔ ∃ verdict, s = .inr (some verdict) := by
    rcases s with _ | (_ | verdict) <;> simp [machine, reply]
  constructor
  · rintro ⟨_, ⟨final, hreplay, hhalt, hout⟩, _⟩
    obtain ⟨hfirst, houtput⟩ := routines.replay_correct a hreplay hhalt
    obtain ⟨verdict, hresult⟩ := (haccept _).mp (List.cons.inj (houtput.symm.trans hout)).1
    exact ⟨verdict, (hspec verdict).mp ⟨hfirst, hresult⟩⟩
  · rintro ⟨verdict, hrun⟩
    obtain ⟨hfirst, hresult⟩ := (hspec verdict).mpr hrun
    obtain ⟨indices, ⟨final, hreplay, hhalt⟩, hunique⟩ :=
      (routines.existsUnique_replay_iff a bits).mpr hfirst
    have hout := (routines.replay_correct a hreplay hhalt).2
    have ha := (haccept _).mpr ⟨verdict, hresult⟩
    exact ⟨indices, ⟨final, hreplay, hhalt, by rwa [ha] at hout⟩,
      fun other ⟨finish, hr, hh, _⟩ => hunique other ⟨finish, hr, hh⟩⟩

end Native

end Turing.DoubleCounting.SourceRoundLoop
