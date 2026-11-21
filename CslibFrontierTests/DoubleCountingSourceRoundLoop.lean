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
    (fun _ _ _ _ _ _ _ _ => trivial)
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
    (fun _ => True) trivial (fun _ _ _ _ _ _ _ _ => trivial)
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
    ((ComputableInSpace.constZero initialRegisters).mono_le fun _ => Nat.zero_le _) ?_
    (budget_const () (.refl _)) (budget_const () (.refl _))
    (budget_const (stableReply ()) (.refl _)) (budget_const (some false) (.refl _))
    (budget_const 0 (.refl _)) (budget_const 0 (.refl _))
    (budget_const true (.refl _)) (budget_const true (.refl _))
    (budget_const () (.refl _)) (budget_const () (.refl _)) ⟨1, ?_⟩
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
    · intro r hr _ _ a ha _ hc
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
