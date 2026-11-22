/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.BranchReplay
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay
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

* `subsingleton_successful_firstHalting` composes callback occurrence uniqueness.
* `firstHalting_iff_replayRounds` identifies successful selector streams with replay of the
  existing fuel-bounded loop.
* `replayRounds_correct` gives the mathematical verdict of a successful full-fuel replay.
* `haltsWithin` and `length_run_le` charge the retained registers and supplied callback bounds
  on every branch.
* `verdictElimSnd_inSpace` dispatches an optional verdict while retaining encoded caller data.
* `exists_routines` compiles the loop with supplied native callbacks and
  `native_firstHalting_accept_iff` preserves its accepting occurrence lists.
-/

public section

namespace Turing.DoubleCounting.SourceRoundLoop

open Cslib.DoubleCounting MultiTapeTM ComputableInSpace
open NondeterministicQueryMachine (encReadChoice exists_firstHalting_prefix_with_next readReply
  successful_call_iff)
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

/-- Case analysis on an optional verdict retains the caller's first component.
The missing, bad-radius, and decided branches supply their linear-space certificates. -/
theorem verdictElimSnd_inSpace {π ε : Type} {encP : π ↪ List Bool} {encE : ε ↪ List Bool}
    {missing : π → ε} {bad : π × ℕ → ε} {decided : π × Bool → ε}
    (hmissing : ComputableInSpace missing encP encE (fun p => (encP p).length))
    (hbad : ComputableInSpace bad (encPair encP encNat) encE
      (fun p => (encPair encP encNat p).length))
    (hdecided : ComputableInSpace decided (encPair encP encBool) encE
      (fun p => (encPair encP encBool p).length)) :
    let E := encPair encP (encOption encVerdict)
    ComputableInSpace (fun p : π × Option ControllerVerdict =>
      match p.2 with
      | none => missing p.1
      | some (.bad radius) => bad (p.1, radius)
      | some (.decided answer) => decided (p.1, answer))
      E encE (fun p => (E p).length) := by
  have hsome := (sumElimSnd hbad hdecided).of_encIn_eq
    (encIn' := encPair encP encVerdict)
    (fun p : π × ControllerVerdict => (p.1, verdictView p.2)) (fun _ => rfl)
  exact (optionElimSnd hmissing hsome).of_enc_eq fun
    | (_, none) | (_, some (.bad _)) | (_, some (.decided _)) => rfl

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

section Replay

variable (initial : Registers κ)
  (round : NondeterministicQueryMachine ρ) (roundStart : Registers κ → ρ)
  (roundReply : ρ → Option RoundUpdate)
  (member : NondeterministicQueryMachine μ) (memberStart : Registers κ → μ)
  (memberReply : μ → Option Bool) (input : List Bool)

local notation "M" => machine initial round roundStart roundReply member memberStart memberReply

/-- The loop accepts exactly terminal states that carry a verdict, including a negative
reachability verdict. -/
theorem machine_accept_iff (s : State κ ρ μ) :
    (M).accept s = true ↔ ∃ verdict, s = .inr (some verdict) := by
  rcases s with _ | (_ | verdict) <;> simp [machine, reply]

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
@[expose] def replayRounds (r : Registers κ) (bits : List Bool) :
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
  have hh : (M).halted (.inr terminal) = true := rfl
  rw [(M).firstHalting_iff_nil_of_halted input bits _ hh, (M).replay_of_halted input hh]
  simp only [Sum.inr.injEq]

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

/-- A register invariant preserved when a completed round with fuel grows without tying. -/
@[expose] def Closed (P : Registers κ → Prop) : Prop :=
  ∀ r, P r → 0 < r.fuel → ∀ bits a,
    round.FirstHalting input bits (roundStart r) →
    roundReply (round.replay input bits (roundStart r)) = some a →
    a.bad = false → a.tally.count ≠ r.tally.count → P (r.advance a.tally)

/-- Successful round and final membership traces give a successful first halt of the loop.
The invariant must give positive fuel and be preserved by completed rounds that continue. -/
theorem exists_successful_firstHalting (P : Registers κ → Prop) (hp : P initial)
    (hpositive : ∀ r, P r → 0 < r.fuel)
    (hclosed : Closed round roundStart roundReply input P)
    (hround : ∀ r, P r → ∃ bits a, round.FirstHalting input bits (roundStart r) ∧
      roundReply (round.replay input bits (roundStart r)) = some a)
    (hmember : ∀ r, P r → ∃ bits hit, member.FirstHalting input bits (memberStart r) ∧
      memberReply (member.replay input bits (memberStart r)) = some hit) :
    ∃ bits verdict, (M).FirstHalting input bits (M).init ∧
      (M).run input bits = .inr (some verdict) := by
  have aux (r : Registers κ) (hr : P r) :
      ∃ bits verdict,
        replayRounds round roundStart roundReply member memberStart memberReply input r bits =
          some (some verdict, []) := by
    induction r using (measure (fun r : Registers κ => r.fuel)).wf.induction with
    | h r ih =>
      have hfuel := hpositive r hr
      have hne := Nat.ne_of_gt hfuel
      obtain ⟨roundBits, a, hfirst, hreply⟩ := hround r hr
      have hread (rest : List Bool) :
          readReply round roundReply input (roundStart r) (roundBits ++ false :: rest) =
            some (a, rest) :=
        (round.readReply_iff roundReply input _ _ a rest).mpr ⟨roundBits, rfl, hfirst, hreply⟩
      by_cases hbad : a.bad = true
      · refine ⟨roundBits ++ [false], .bad (r.radius + 1), ?_⟩
        rw [replayRounds_step _ _ _ _ _ _ _ _ _ hne, hread []]
        simp only [hbad, ite_true]
      · by_cases hcount : a.tally.count = r.tally.count
        · obtain ⟨memberBits, hit, hmfirst, hmreply⟩ := hmember r hr
          have hmread :
              readReply member memberReply input (memberStart r) (memberBits ++ [false]) =
                some (hit, []) :=
            (member.readReply_iff memberReply input _ _ hit []).mpr
              ⟨memberBits, rfl, hmfirst, hmreply⟩
          refine ⟨roundBits ++ false :: (memberBits ++ [false]), .decided hit, ?_⟩
          rw [replayRounds_step _ _ _ _ _ _ _ _ _ hne, hread]
          simp [hbad, hcount, hmread]
        · have hlt : (r.advance a.tally).fuel < r.fuel := by
            simp only [Registers.advance]
            omega
          obtain ⟨rest, verdict, hrest⟩ := ih _ hlt (hclosed r hr hfuel roundBits a hfirst hreply
            (Bool.eq_false_iff.mpr hbad) hcount)
          refine ⟨roundBits ++ false :: rest, verdict, ?_⟩
          rw [replayRounds_step _ _ _ _ _ _ _ _ _ hne, hread]
          simpa [hbad, hcount] using hrest
  obtain ⟨bits, verdict, h⟩ := aux initial hp
  exact ⟨bits, verdict,
    (firstHalting_iff_replayRounds initial round roundStart roundReply member memberStart
      memberReply input bits verdict).mpr h⟩

/-- The source loop has at most one successful first-halting selector list if each round and
final membership invocation at an admissible register state has at most one successful list.
The invariant is needed only at the initial state and after a round that continues the loop. -/
theorem subsingleton_successful_firstHalting (P : Registers κ → Prop) (hp : P initial)
    (hclosed : Closed round roundStart roundReply input P)
    (hround : ∀ r, P r → 0 < r.fuel →
      {bits : List Bool | round.FirstHalting input bits (roundStart r) ∧
        (roundReply (round.replay input bits (roundStart r))).isSome}.Subsingleton)
    (hmember : ∀ r, P r → 0 < r.fuel →
      {bits : List Bool | member.FirstHalting input bits (memberStart r) ∧
        (memberReply (member.replay input bits (memberStart r))).isSome}.Subsingleton) :
    {bits : List Bool | (M).FirstHalting input bits (M).init ∧
      (M).accept ((M).run input bits) = true}.Subsingleton := by
  have aux (r : Registers κ) (hr : P r) (left right : List Bool)
      (v v' : ControllerVerdict) :
      replayRounds round roundStart roundReply member memberStart memberReply input r left =
        some (some v, []) →
      replayRounds round roundStart roundReply member memberStart memberReply input r right =
        some (some v', []) → left = right := by
    induction hf : r.fuel using Nat.strongRecOn generalizing r left right v v' with
    | ind fuel ih =>
      intro hleft hright
      by_cases hz : r.fuel = 0
      · rw [replayRounds, hz, runRoundsWith] at hleft
        cases hleft
      · have hpos : 0 < r.fuel := Nat.pos_of_ne_zero hz
        rw [replayRounds_step _ _ _ _ _ _ _ _ _ hz] at hleft hright
        cases hl : readReply round roundReply input (roundStart r) left with
        | none => simp [hl] at hleft
        | some l =>
          cases hr' : readReply round roundReply input (roundStart r) right with
          | none => simp [hr'] at hright
          | some r' =>
            obtain ⟨a, suffix⟩ := l
            obtain ⟨a', suffix'⟩ := r'
            obtain ⟨callBits, hlBits, hrBits, hfirst, hret, rfl⟩ :=
              round.readReply_commonPrefix roundReply input (roundStart r) (hround r hr hpos) hl hr'
            simp only [hl] at hleft
            simp only [hr'] at hright
            rw [hlBits, hrBits]
            suffices he : suffix = suffix' by rw [he]
            by_cases hb : a.bad = true
            · rw [ite_eq_left hb] at hleft hright
              exact (congrArg Prod.snd (Option.some.inj hleft)).trans
                (congrArg Prod.snd (Option.some.inj hright)).symm
            · rw [ite_eq_right hb] at hleft hright
              by_cases hc : (a.tally.count == r.tally.count) = true
              · rw [ite_eq_left hc] at hleft hright
                obtain ⟨⟨hit, tail⟩, hread, hout⟩ := Option.map_eq_some_iff.mp hleft
                obtain ⟨⟨hit', tail'⟩, hread', hout'⟩ := Option.map_eq_some_iff.mp hright
                have htail : tail = [] := congrArg Prod.snd hout
                have htail' : tail' = [] := congrArg Prod.snd hout'
                obtain ⟨memberBits, hl', hr', _, _, _⟩ :=
                  member.readReply_commonPrefix memberReply input (memberStart r)
                    (hmember r hr hpos) hread hread'
                rw [hl', hr', htail, htail']
              · rw [ite_eq_right hc] at hleft hright
                have hc' : a.tally.count ≠ r.tally.count := fun he => hc (beq_iff_eq.mpr he)
                have hnext := hclosed r hr hpos callBits a hfirst hret
                  (Bool.eq_false_iff.mpr hb) hc'
                have hlt : (r.advance a.tally).fuel < fuel := by
                  simp only [Registers.advance]
                  omega
                exact ih _ hlt (r.advance a.tally) hnext suffix suffix' v v' rfl hleft hright
  intro left hl right hr
  have haccept := machine_accept_iff initial round roundStart roundReply
    member memberStart memberReply
  obtain ⟨v, hv⟩ := (haccept _).mp hl.2
  obtain ⟨v', hv'⟩ := (haccept _).mp hr.2
  exact aux initial hp left right v v'
    ((firstHalting_iff_replayRounds initial round roundStart roundReply member memberStart
      memberReply input left v).mp ⟨hl.1, hv⟩)
    ((firstHalting_iff_replayRounds initial round roundStart roundReply member memberStart
      memberReply input right v').mp ⟨hr.1, hv'⟩)

section Verdict

open Relation

variable {n : ℕ} {r : Fin n → Fin n → Prop} {source target : Fin n} (context : κ)
  (hround : ∀ fuel k, (∃! w, Passes r source k w) → ∀ bits a rest,
    readReply round roundReply input (roundStart ⟨context, fuel, k, expected r source k⟩) bits =
      some (a, rest) →
    a.tally = expected r source (k + 1) ∧
      (a.bad = false ↔ ∃! w, Passes r source (k + 1) w))
  (hmember : ∀ fuel k, (∃! w, Passes r source k w) → ∀ bits hit rest,
    readReply member memberReply input (memberStart ⟨context, fuel, k, expected r source k⟩)
      bits = some (hit, rest) → (hit = true ↔ target ∈ Cslib.DoubleCounting.round r source k))

include hround hmember in
private theorem replayRounds_eq_runRounds {edge : Fin n → Fin n → Id Bool}
    {membership : MembershipScan Id n}
    (he : ∀ u v, edge u v = pure (by classical exact decide (r u v)))
    (hm : ∀ k, (∃! w, Passes r source k w) → ∀ v,
      membership k (expected r source k) v =
        pure (by classical exact decide (v ∈ Cslib.DoubleCounting.round r source k)))
    (fuel k : ℕ) (hpass : ∃! w, Passes r source k w)
    (bits rest : List Bool) (out : Option ControllerVerdict)
    (h : replayRounds round roundStart roundReply member memberStart memberReply input
      ⟨context, fuel, k, expected r source k⟩ bits = some (out, rest)) :
    runRounds edge membership target fuel k (expected r source k) = out := by
  classical
  induction fuel generalizing k bits with
  | zero =>
    change some (none, bits) = some (out, rest) at h
    exact congrArg Prod.fst (Option.some.inj h)
  | succ fuel ih =>
    rw [replayRounds_step round roundStart roundReply member memberStart memberReply
      input _ bits (Nat.succ_ne_zero fuel)] at h
    cases hread : readReply round roundReply input
        (roundStart ⟨context, fuel + 1, k, expected r source k⟩) bits with
    | none => simp [hread] at h
    | some result =>
      obtain ⟨a, suffix⟩ := result
      have ⟨ha, hab⟩ := hround (fuel + 1) k hpass bits a suffix hread
      obtain ⟨reference, href, ht, hb⟩ := scanNextRound_correct he (hm k hpass) hpass
      have hflag : reference.bad = a.bad := by
        apply Bool.not_inj
        apply Bool.eq_iff_iff.mpr
        simpa only [Bool.not_eq_true_eq_eq_false] using hb.trans hab.symm
      have heq : reference = a := by
        cases reference
        cases a
        exact congrArg₂ RoundUpdate.mk (ht.trans ha.symm) hflag
      simp only [hread] at h
      simp only [runRounds, runRoundsWith, href, heq, pure_bind]
      by_cases hbad : a.bad = true
      · rw [ite_eq_left hbad] at h ⊢
        exact congrArg Prod.fst (Option.some.inj h)
      · rw [ite_eq_right hbad] at h ⊢
        by_cases hstable : (a.tally.count == (expected r source k).count) = true
        · rw [ite_eq_left hstable] at h ⊢
          obtain ⟨⟨hit, tail⟩, hhit, hout⟩ := Option.map_eq_some_iff.mp h
          have hbit := hmember (fuel + 1) k hpass suffix hit tail hhit
          have hm' : membership k (expected r source k) target = hit := by
            rw [hm k hpass]
            change decide (target ∈ Cslib.DoubleCounting.round r source k) = hit
            apply Bool.eq_iff_iff.mpr
            simpa only [decide_eq_true_eq] using hbit.symm
          rw [hm']
          exact congrArg Prod.fst hout
        · rw [ite_eq_right hstable] at h ⊢
          rw [ha] at h ⊢
          have hnext := hab.mp (Bool.eq_false_iff.mpr hbad)
          exact ih (k + 1) hnext suffix h

include hround hmember in
/-- With full vertex-count fuel, a successful replay reports the first tied round, or
correctly decides reachability when every round is unique. The callback contracts only
concern successful replies at exact totals and a unique current round. -/
theorem replayRounds_correct {bits rest : List Bool} {verdict : ControllerVerdict}
    (h : replayRounds round roundStart roundReply member memberStart memberReply input
      (start context n) bits = some (some verdict, rest)) :
    verdict.Correct r source target := by
  classical
  let edge (u v : Fin n) : Id Bool := decide (r u v)
  let membership : MembershipScan Id n :=
    fun k _ v => decide (v ∈ Cslib.DoubleCounting.round r source k)
  have he (u v : Fin n) : edge u v = pure (decide (r u v)) := rfl
  have hm k (_ : ∃! w, Passes r source k w) (v : Fin n) :
      membership k (expected r source k) v =
        pure (decide (v ∈ Cslib.DoubleCounting.round r source k)) := rfl
  obtain ⟨reference, href, hspec⟩ := runController_correct (target := target) he hm
  have hzero := expected_zero r source
  have hrun := replayRounds_eq_runRounds round roundStart roundReply member memberStart
    memberReply input context hround hmember he hm n 0 (existsUnique_passes_zero r source)
    bits rest (some verdict) (by simpa only [hzero, start] using h)
  rw [hzero, ← runController, href] at hrun
  have heq := Option.some.inj hrun
  subst reference
  exact hspec

end Verdict

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
      exists_firstHalting_prefix_with_next member input bits (memberStart r) memberClock
        (hmember r hr) hlen
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
          exists_firstHalting_prefix_with_next round input bits (roundStart r) roundClock
            (hround r hr) hlen'
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
                  hclosed r hr (Nat.pos_of_ne_zero hzero) callBits a hfirst hret
                    (Bool.eq_false_iff.mpr hbad)
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
              · obtain ⟨first, ⟨_, hfirst, hstate⟩, _⟩ :=
                  round.existsUnique_firstHalting_prefix input (ht.symm ▸ hhalt)
                exact hclosed r hp hfuel first a hfirst ((hstate.trans ht).symm ▸ ha)
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
    (hroundNext : ComputableInSpace round.next (encPair encRound encReadChoice) encRound
      (fun p => (encPair encRound encReadChoice p).length))
    (hmemberNext : ComputableInSpace member.next (encPair encMember encReadChoice) encMember
      (fun p => (encPair encMember encReadChoice p).length)) :
    ComputableInSpace (M).next (encPair E encReadChoice) E
      (fun p => (encPair E encReadChoice p).length) := by
  have hroundFrame := fst P encReadChoice
  have hroundRead := snd P encReadChoice
  have hroundRegs := fst' hroundFrame
  have hroundState := snd' hroundFrame
  have hroundBit := snd' hroundRead
  have hreturned := budget_comp_linear
    (returnRound_inSpace encContext encRound encMember _ _ hroundStart hmemberStart)
    (budget_prod hroundRegs (budget_comp_linear hroundReply hroundState))
  have hroundReject := budget_const (encIn := encPair P encReadChoice) (encB := E)
    (.inr none) (.refl _)
  have hroundContinue := round_budget encContext encRound encMember hroundRegs
    (budget_comp_linear hroundNext (budget_prod hroundState hroundRead))
  have hround := budget_ite (budget_comp_linear hroundHalt hroundState)
    (budget_ite hroundBit hroundReject hreturned) hroundContinue
  have hmFrame := fst Q encReadChoice
  have hmRead := snd Q encReadChoice
  have hmRegs := fst' hmFrame
  have hmState := snd' hmFrame
  have hmBit := snd' hmRead
  have hdecide : ComputableInSpace ControllerVerdict.decided encBool encVerdict
      (fun v => (encBool v).length) :=
    (of_inO (ComputableInO.inr encNat encBool)).of_enc_eq fun _ => rfl
  have hmReply := budget_comp_linear hmemberReply hmState
  have hmHit := budget_comp_linear hdecide (budget_optionGetD false hmReply)
  have hmNone := budget_const (encIn := encPair Q encReadChoice) (encB := F) none (.refl _)
  have hmResult := budget_ite (budget_optionIsSome hmReply) (budget_optionSome hmHit) hmNone
  have hmReject := budget_const (encIn := encPair Q encReadChoice) (encB := E)
    (.inr none) (.refl _)
  have hmDone := finish_budget encContext encRound encMember hmResult
  have hmContinue := member_budget encContext encRound encMember hmRegs
    (budget_comp_linear hmemberNext (budget_prod hmState hmRead))
  have hmember := budget_ite (budget_comp_linear hmemberHalt hmState)
    (budget_ite hmBit hmReject hmDone) hmContinue
  have hfinished := finish_budget encContext encRound encMember (fst F encReadChoice)
  refine (sumElimFst (sumElimFst hround hmember) hfinished).of_enc_eq ?_
  rintro ⟨(⟨r, s⟩ | ⟨r, s⟩) | verdict, read, bit⟩
  · cases bit <;> cases round.halted s <;> rfl
  · cases bit <;> cases hh : member.halted s <;> cases ha : memberReply s <;>
      simp [machine, memberState, hh, ha]
  · rfl

/-- Compose the callback certificates for query, transition, halt and optional verdict
decoding in workspace linear in the encoded arguments. -/
theorem parts_inSpace
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
    (hroundNext : ComputableInSpace round.next (encPair encRound encReadChoice) encRound
      (fun p => (encPair encRound encReadChoice p).length))
    (hmemberNext : ComputableInSpace member.next (encPair encMember encReadChoice) encMember
      (fun p => (encPair encMember encReadChoice p).length)) :
    let encStep := encPair E encReadChoice
    ComputableInSpace (M).query E encNat (fun s => (E s).length) ∧
      ComputableInSpace (M).next encStep E (fun p => (encStep p).length) ∧
      ComputableInSpace (M).halted E encBool (fun s => (E s).length) ∧
      ComputableInSpace reply E (encOption encVerdict) (fun s => (E s).length) := by
  intro encStep
  have hq := query_inSpace encContext encRound encMember initial round roundStart roundReply
    member memberStart memberReply hroundQuery hmemberQuery
  have hn := next_inSpace encContext encRound encMember initial round roundStart roundReply
    member memberStart memberReply hroundStart hmemberStart hroundReply hmemberReply
    hroundHalt hmemberHalt hroundNext hmemberNext
  have hh := halted_inSpace encContext encRound encMember initial round roundStart roundReply
    member memberStart memberReply
  exact ⟨hq, hn, hh, reply_inSpace encContext encRound encMember⟩

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
    (hroundNext : ComputableInSpace round.next (encPair encRound encReadChoice) encRound
      (fun p => (encPair encRound encReadChoice p).length))
    (hmemberNext : ComputableInSpace member.next (encPair encMember encReadChoice) encMember
      (fun p => (encPair encMember encReadChoice p).length))
    (hstates : ∃ c, ∀ a bits, (E ((machine (registers a) round roundStart roundReply
      member memberStart memberReply).run (enc a) bits)).length ≤ c * S a) :
    Nonempty (Routines (M) (fun a => enterRound roundStart (registers a)) enc S) := by
  obtain ⟨hq, hn, hh, hreply⟩ := parts_inSpace encContext encRound encMember
    initial round roundStart roundReply member memberStart memberReply hroundStart
    hmemberStart hroundReply hmemberReply hroundQuery hmemberQuery hroundHalt
    hmemberHalt hroundNext hmemberNext
  have ha : ComputableInSpace (M).accept E encBool (fun s => (E s).length) :=
    budget_optionIsSome hreply
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
  have haccept := machine_accept_iff initial round roundStart roundReply
    member memberStart memberReply
  rw [routines.existsUnique_accepting_replay_iff]
  constructor
  · rintro ⟨hfirst, htrue⟩
    obtain ⟨verdict, hresult⟩ := (haccept _).mp htrue
    exact ⟨verdict, (hspec verdict).mp ⟨hfirst, hresult⟩⟩
  · rintro ⟨verdict, hrun⟩
    obtain ⟨hfirst, hresult⟩ := (hspec verdict).mpr hrun
    exact ⟨hfirst, (haccept _).mpr ⟨verdict, hresult⟩⟩

end Native

end Turing.DoubleCounting.SourceRoundLoop
