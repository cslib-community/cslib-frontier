/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally

/-! Checks for the source loop’s tie, stabilization, and callback rejection. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingSourceRoundLoop

open Cslib.DoubleCounting Turing Turing.DoubleCounting.SourceRoundLoop
open MultiTapeTM ComputableInSpace NondeterministicQueryMachine

private def done : NondeterministicQueryMachine Unit where
  init := ()
  query := fun _ => 0
  next := fun _ => ()
  halted := fun _ => true
  accept := fun _ => true

private def round : NondeterministicQueryMachine (Registers Unit) where
  init := start () 0
  query := fun _ => 0
  next := fun (r, _, _) => r
  halted := fun _ => true
  accept := fun _ => true

private def runWith (answer : Registers Unit → Option RoundUpdate) (choices : List Bool) :
    State Unit (Registers Unit) Unit :=
  (machine (start () 2) round id answer done (fun _ => ()) (fun _ => some false)).run [] choices

-- A tied round reports the next radius, and no final membership call is made.
example : reply (runWith (fun _ => some ⟨⟨1, 0⟩, true⟩) [false]) = some (.bad 1) := rfl

-- A growing round is followed by a stable round and the final membership query.
example : reply (runWith (fun _ => some ⟨⟨2, 1⟩, false⟩) [false, false, false]) =
    some (.decided false) := rfl

-- A rejected round never produces a source verdict.
example : runWith (fun _ => none) [false] = .inr none := rfl

-- A true selector at a deterministic return rejects, even after a successful round.
example : runWith (fun _ => some ⟨⟨1, 0⟩, true⟩) [true] = .inr none := rfl

private def growingRound (_ : Registers Unit) : Option RoundUpdate := some ⟨⟨2, 1⟩, false⟩

/-- Both complete outer selector returns and membership input are represented in exact replay. -/
example :
    replayRounds round id growingRound done (fun _ => ()) (fun _ => some false)
      [] (start () 2) [false, false, false] = some (some (.decided false), []) := by
  apply (firstHalting_iff_replayRounds (start () 2) round id growingRound done
    (fun _ => ()) (fun _ => some false) [] _ _).mp
  refine ⟨?_, rfl⟩
  exact NondeterministicQueryMachine.firstHalting_append_singleton _ [] [false, false] false
    rfl rfl

/-- A growing round, a stable round and a passing negative have one complete selector list. -/
example :
    let scan := machine (start () 2) round id growingRound done (fun _ => ())
      (fun _ => some false)
    {bits : List Bool | scan.FirstHalting [] bits scan.init ∧
      scan.accept (scan.run [] bits) = true} = {[false, false, false]} := by
  let scan := machine (start () 2) round id growingRound done (fun _ => ())
    (fun _ => some false)
  let traces : Set (List Bool) :=
    {bits | scan.FirstHalting [] bits scan.init ∧ scan.accept (scan.run [] bits) = true}
  change traces = _
  have hu := subsingleton_successful_firstHalting (start () 2) round id growingRound
    done (fun _ => ()) (fun _ => some false) [] (fun _ => True) trivial
    (fun _ _ _ _ _ _ _ _ _ => trivial)
    (fun r _ _ _ hx _ hy =>
      ((round.firstHalting_iff_nil_of_halted [] _ r rfl).mp hx.1).trans
        ((round.firstHalting_iff_nil_of_halted [] _ r rfl).mp hy.1).symm)
    (fun _ _ _ _ hx _ hy =>
      ((done.firstHalting_iff_nil_of_halted [] _ () rfl).mp hx.1).trans
        ((done.firstHalting_iff_nil_of_halted [] _ () rfl).mp hy.1).symm)
  have hmem : [false, false, false] ∈ traces :=
    ⟨NondeterministicQueryMachine.firstHalting_append_singleton scan [] [false, false] false
      rfl rfl, rfl⟩
  exact hu.eq_singleton_of_mem hmem

/-- A growing round followed by stabilization and a negative reply has a successful trace. -/
example :
    let scan := machine (start () 2) round id growingRound done (fun _ => ())
      (fun _ => some false)
    ∃ bits verdict, scan.FirstHalting [] bits scan.init ∧
      scan.run [] bits = .inr (some verdict) := by
  let P (r : Registers Unit) := 0 < r.fuel ∧ (r.tally.count ≠ 2 → 1 < r.fuel)
  refine exists_successful_firstHalting (start () 2) round id growingRound
    done (fun _ => ()) (fun _ => some false) [] P (by decide)
    (fun _ hr => hr.1) ?_ ?_ ?_
  · intro r hr _ _ a _ ha _ hcount
    have hupdate : a = ⟨⟨2, 1⟩, false⟩ := Option.some.inj ha.symm
    subst a
    refine ⟨?_, fun h => (h rfl).elim⟩
    have hfuel := hr.2 (Ne.symm hcount)
    simp only [Registers.advance]
    omega
  · intro r _
    exact ⟨[], ⟨⟨2, 1⟩, false⟩, (round.firstHalting_iff_nil_of_halted [] [] r rfl).mpr rfl, rfl⟩
  · intro _ _
    exact ⟨[], false, (done.firstHalting_iff_nil_of_halted [] [] () rfl).mpr rfl, rfl⟩

private def lateRound : NondeterministicQueryMachine (Option Bool) where
  init := none
  query _ := 0
  next := fun (_, _, choice) => some (!choice)
  halted := Option.isSome
  accept := fun state => state == some true

private def lateReply : Option Bool → Option RoundUpdate
  | none => some ⟨⟨2, 0⟩, false⟩
  | some false => none
  | some true => some ⟨⟨1, 0⟩, false⟩

private theorem lateRound_closed :
    Closed lateRound (fun _ => none) lateReply [] (· = start () 1) := by
  rintro _ rfl _ bits a hfirst ha _ hcount
  have hhalt := hfirst.1
  change lateReply (lateRound.replay [] bits none) = some a at ha
  cases hs : lateRound.replay [] bits none with
  | none =>
    change (lateRound.replay [] bits none).isSome = true at hhalt
    simp [hs] at hhalt
  | some hit =>
    cases hit
    · simp [lateReply, hs] at ha
    · have ha' : a = ⟨⟨1, 0⟩, false⟩ := Option.some.inj (by simpa [lateReply, hs] using ha.symm)
      exact (hcount (by rw [ha']; rfl)).elim

private theorem lateRound_trace (bits : List Bool)
    (h : lateRound.FirstHalting [] bits none ∧
      (lateReply (lateRound.replay [] bits none)).isSome) : bits = [false] := by
  cases bits with
  | nil => cases h.1.1
  | cons bit bits =>
    have hfirst := ((lateRound.firstHalting_cons_iff [] bit bits none).mp h.1).2
    have hhalt : lateRound.halted (lateRound.step [] none bit) = true := by
      cases bit <;> rfl
    have hnil := (lateRound.firstHalting_iff_nil_of_halted [] bits _ hhalt).mp hfirst
    subst bits
    cases bit
    · rfl
    · cases h.2

/-- A live prefix exposes a growth reply, but the completed stable round has a unique trace. -/
example :
    let scan := machine (start () 1) lateRound (fun _ => none) lateReply
      done (fun _ => ()) (fun _ => some false)
    lateReply (lateRound.replay [] [] none) = some ⟨⟨2, 0⟩, false⟩ ∧
      (∃ bits verdict, scan.FirstHalting [] bits scan.init ∧
        scan.run [] bits = .inr (some verdict)) ∧
      {bits : List Bool | scan.FirstHalting [] bits scan.init ∧
        scan.accept (scan.run [] bits) = true}.Subsingleton := by
  refine ⟨rfl, ?_, ?_⟩
  · refine exists_successful_firstHalting (start () 1) lateRound (fun _ => none) lateReply
      done (fun _ => ()) (fun _ => some false) [] (· = start () 1) rfl
      (by rintro _ rfl; decide) lateRound_closed ?_ ?_
    · intro _ _
      exact ⟨[false], ⟨⟨1, 0⟩, false⟩,
        lateRound.firstHalting_append_singleton [] [] false rfl rfl, rfl⟩
    · intro _ _
      exact ⟨[], false, (done.firstHalting_iff_nil_of_halted [] [] () rfl).mpr rfl, rfl⟩
  · exact subsingleton_successful_firstHalting (start () 1)
      lateRound (fun _ => none) lateReply done (fun _ => ()) (fun _ => some false)
      [] (· = start () 1) rfl lateRound_closed
      (fun _ _ _ left hl right hr =>
        (lateRound_trace left hl).trans (lateRound_trace right hr).symm)
      (fun _ _ _ left hl right hr =>
        ((done.firstHalting_iff_nil_of_halted [] left () rfl).mp hl.1).trans
          ((done.firstHalting_iff_nil_of_halted [] right () rfl).mp hr.1).symm)

private def stableRound (r : Registers Unit) : Option RoundUpdate := some ⟨r.tally, false⟩

open Turing.DoubleCounting in
private def tallyInit (r : Registers Unit) : MembershipTally.State Unit :=
  MembershipTally.initial ⟨2, 0, 1, r.radius, r.tally⟩

open Turing.DoubleCounting in
private def tally : NondeterministicQueryMachine (MembershipTally.State Unit) :=
  MembershipTally.machine ⟨2, 0, 1, 0, ⟨1, 0⟩⟩ done (fun _ => ()) (fun _ => some 0)

open Turing.DoubleCounting in
-- The stable round enters the existing tally and reads a passing negative via its reply decoder.
example :
    reply ((machine (start () 1) round id stableRound tally tallyInit
        MembershipTally.reply).run [] [false, true, false, false, false, false]) =
      some (.decided false) := rfl

example (input : List Bool) :
    (machine (start () 2) round id growingRound done (fun _ => ())
      (fun _ => some false)).HaltsWithin input 3 :=
  haltsWithin (start () 2) round id growingRound done (fun _ => ()) (fun _ => some false) input
    (fun _ => True) trivial (fun _ _ _ _ _ _ _ _ _ => trivial)
    0 0 (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

private def stableReply (_ : Unit) : Option RoundUpdate := some ⟨⟨1, 0⟩, false⟩

private def negativeReply (_ : Unit) : Option Bool := some false

private def callbackInit (_ : Registers Unit) : Unit := ()

private def initialRegisters : Registers Unit := start () 1

-- A full-fuel replay on two isolated vertices returns a justified negative verdict.
example :
    let edge : Fin 2 → Fin 2 → Prop := fun _ _ => False
    (∀ k, ∃! w, Passes edge 0 k w) ∧ (false = true ↔ Relation.ReflTransGen edge 0 1) := by
  let edge : Fin 2 → Fin 2 → Prop := fun _ _ => False
  have hreached (v : Fin 2) : Relation.ReflTransGen edge 0 v ↔ v = 0 :=
    Relation.reflTransGen_iff_eq (fun _ h => h)
  have hvertices (k : ℕ) :
      Cslib.DoubleCounting.round edge 0 k = Cslib.DoubleCounting.round edge 0 0 := by
    ext v
    simp only [mem_round, Relation.reachableWithin_zero, Set.mem_singleton_iff]
    constructor
    · exact fun h => (hreached v).mp (Relation.reachableWithin_subset_setOf_reflTransGen h)
    · rintro rfl
      apply Relation.reachableWithin_mono (Nat.zero_le k)
      simp [Relation.reachableWithin_zero]
  have htotals (k : ℕ) : expected edge 0 k = ⟨1, 0⟩ := by
    rw [← expected_zero edge 0]
    simp only [expected, hvertices]
  have hp (k : ℕ) : ∃! w, Passes edge 0 k w := by
    have hzero := (existsUnique_passes_iff.mp (existsUnique_passes_zero edge 0))
    rw [existsUnique_passes_iff, hvertices]
    exact hzero
  have readDone {α : Type} (decode : Unit → Option α) (bits : List Bool)
      (value : α) (rest : List Bool)
      (hread : done.readReply decode [] () bits = some (value, rest)) :
      decode () = some value := by
    obtain ⟨callBits, _, hfirst, hreply⟩ :=
      (done.readReply_iff decode [] bits () value rest).mp hread
    have he := (done.firstHalting_iff_nil_of_halted [] callBits () rfl).mp hfirst
    subst callBits
    exact hreply
  have h :
      replayRounds done callbackInit stableReply done callbackInit negativeReply
        [] (start () 2) [false, false] = some (some (.decided false), []) := rfl
  refine replayRounds_correct (r := edge) (source := 0) (target := 1)
    done callbackInit stableReply done callbackInit negativeReply [] () ?_ ?_ h
  · intro fuel k _ bits a rest hread
    have hreply := readDone stableReply bits a rest hread
    have ha : a = ⟨⟨1, 0⟩, false⟩ := Option.some.inj hreply.symm
    exact ⟨ha ▸ (htotals (k + 1)).symm, by simp [ha, hp]⟩
  · intro fuel k _ bits hit rest hread
    have hreply := readDone negativeReply bits hit rest hread
    have hh : hit = false := Option.some.inj hreply.symm
    simp [hh, hvertices k, Cslib.DoubleCounting.round_zero]

private def nativeBudget (input : List Bool) : ℕ :=
  Nat.log2 input.length + 2 * (encRegisters encUnit initialRegisters).length +
    (encNat (initialRegisters.fuel + initialRegisters.radius)).length + 4

private theorem nativeRoutines : Nonempty
    (Routines (machine initialRegisters done callbackInit stableReply
      done callbackInit negativeReply)
      (fun _ : List Bool => enterRound (μ := Unit) callbackInit initialRegisters)
      encBits nativeBudget) := by
  refine exists_routines encUnit encUnit encUnit initialRegisters done callbackInit stableReply
    done callbackInit negativeReply encBits nativeBudget (fun _ => initialRegisters)
    (ComputableInSpace.budget_const initialRegisters) ?_
    (budget_const ()) (budget_const ())
    (budget_const (stableReply ())) (budget_const (some false))
    (budget_const 0) (budget_const 0)
    (budget_const true) (budget_const true)
    (budget_const ()) (budget_const ()) ⟨1, ?_⟩
  · intro input
    simp only [nativeBudget, encBits_apply]
    omega
  · intro input bits
    rw [Nat.one_mul]
    refine (length_run_le initialRegisters done callbackInit stableReply done callbackInit
      negativeReply (encBits input) encUnit encUnit encUnit (· = initialRegisters) rfl
      ?_ (encRegisters encUnit initialRegisters).length 0 0
      (by rintro _ rfl; exact le_rfl) (fun _ _ _ => Nat.zero_le 0)
      (fun _ _ _ => Nat.zero_le 0) bits).trans ?_
    · intro r hr _ _ a _ ha _ hc
      subst r
      have he : a = ⟨⟨1, 0⟩, false⟩ := Option.some.inj ha.symm
      subst a
      exact (hc rfl).elim
    · unfold nativeBudget
      omega

/-- A stabilized negative result determines exactly one accepting native callback occurrence. -/
example : ∃ R : Routines (machine initialRegisters done callbackInit stableReply
      done callbackInit negativeReply)
      (fun _ : List Bool => enterRound (μ := Unit) callbackInit initialRegisters)
      encBits nativeBudget,
    ∃! indices, ∃ final,
      Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg []) indices =
        some ([false, false], final) ∧ final.Halted ∧ final.output = [true] := by
  obtain ⟨R⟩ := nativeRoutines
  refine ⟨R, (native_firstHalting_accept_iff initialRegisters done callbackInit stableReply
    done callbackInit negativeReply (fun _ => initialRegisters) R [] [false, false]).mpr ?_⟩
  refine ⟨.decided false, (firstHalting_iff_replayRounds initialRegisters done callbackInit
    stableReply done callbackInit negativeReply [] _ _).mp ⟨?_, rfl⟩⟩
  exact NondeterministicQueryMachine.firstHalting_append_singleton _ [] [false] false rfl rfl

end CslibFrontierTests.DoubleCountingSourceRoundLoop
