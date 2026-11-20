/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.NondeterministicOutput
import CslibFrontier.Computability.Complexity.Classes.NP.Nondeterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.HaltedReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput

/-!
# Output graphs of nondeterministic polynomial-time machines

A halted branch with output `true :: w` certifies the result `w`. As in the machine
characterization of NP, the certificate lists coins that select actions from a fixed finite
enumeration. Two replays of the same coins recover the output and confirm that the branch halted.
The time bound gives both a bound on output length and enough coins for any successful branch.

## Main results

* `Cslib.Complexity.mem_NPMV_of_runsInPolyTime`: the successful output relation of a binary
  nondeterministic polynomial-time machine belongs to `NPMV`.
-/

public section

open Turing

namespace Cslib.Complexity

open MultiTapeTM MultiTapeNTM

variable {k : ℕ} {State : Type} [Finite State]
  {ntm : MultiTapeNTM k Bool State} {input : List Bool}

/-- An index into the choice enumeration, with an extra index past its end. -/
private abbrev Candidate (k : ℕ) (State : Type) :=
  Fin (Nat.card (Action k Bool State) + 1)

private noncomputable def nextCandidate (j : Candidate k State) : Candidate k State :=
  ⟨min (j.val + 1) (Nat.card (Action k Bool State)), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- A false coin skips a candidate and a true coin takes it. At an exhausted list a true
coin leaves the simulation unchanged. The two modes emit the output or a halting verdict. -/
private noncomputable def graphReplay (ntm : MultiTapeNTM k Bool State) (verdict : Bool) :
    MultiTapePTM k Bool (State × Candidate k State) where
  initial := (ntm.q₀, 0)
  tr s symbol work _ bit := .step
    (if bit then
      match (ntm.actions s.1 symbol work)[s.2.val]? with
      | none => ChoiceTable.idle (some s)
      | some a => ⟨a.inputTape, a.workTapes,
          if verdict then (if a.state.isNone then some true else none) else a.output,
          a.state.map (fun q => (q, 0))⟩
    else ChoiceTable.idle (some (s.1, nextCandidate s.2))) Empty.elim Empty.elim

private def replayCfg (c : Cfg k Bool State input) (j : Candidate k State) (verdict : Bool) :
    Cfg k Bool (State × Candidate k State) input :=
  ⟨c.state.map (fun q => (q, j)), c.inputPos, c.workTapes, c.workTapePos,
    if verdict then (if c.state.isNone then [true] else []) else c.output⟩

private theorem replayStep_skip (c : Cfg k Bool State input) (j : Candidate k State)
    (verdict : Bool) :
    ((graphReplay ntm verdict).withCoin false).toTM.step (replayCfg c j verdict) =
      replayCfg c (nextCandidate j) verdict := by
  rcases hs : c.state with _ | q
  · rw [MultiTapeTM.step_of_halt (by simp [replayCfg, hs])]
    simp [replayCfg, hs]
  · rw [MultiTapeTM.step_of_state (show (replayCfg c j verdict).state = some (q, j) by
      simp [replayCfg, hs]), MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
    change (ChoiceTable.idle _).apply _ = _
    rw [ChoiceTable.apply_idle]
    simp [replayCfg, hs]

private theorem replayStep_take {c : Cfg k Bool State input} {q : State}
    {j : Candidate k State} (hs : c.state = some q) (verdict : Bool) :
    ((graphReplay ntm verdict).withCoin true).toTM.step (replayCfg c j verdict) =
      match (ntm.actions q c.inputSymbol c.workTapeSymbols)[j.val]? with
      | none => replayCfg c j verdict
      | some a => replayCfg (a.apply c) 0 verdict := by
  rw [MultiTapeTM.step_of_state (show (replayCfg c j verdict).state = some (q, j) by
    simp [replayCfg, hs]), MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
  change (match (ntm.actions q c.inputSymbol c.workTapeSymbols)[j.val]? with
    | none => ChoiceTable.idle (some (q, j))
    | some a => ⟨a.inputTape, a.workTapes,
        if verdict then (if a.state.isNone then some true else none) else a.output,
        a.state.map (fun s => (s, 0))⟩).apply _ = _
  split
  · rw [ChoiceTable.apply_idle]
    simp [replayCfg, hs]
  · rename_i action _
    cases verdict <;> cases ha : action.state <;> simp [replayCfg, hs, ha, Action.apply]

private theorem replayStep_reachable (p : ntm.ComputationPath input)
    (j : Candidate k State) (bit : Bool) :
    ∃ (q : ntm.ComputationPath input) (i : Candidate k State), ∀ verdict,
      ((graphReplay ntm verdict).withCoin bit).toTM.step (replayCfg p.last j verdict) =
        replayCfg q.last i verdict := by
  cases bit
  · exact ⟨p, nextCandidate j, replayStep_skip p.last j⟩
  rcases hs : p.last.state with _ | state
  · exact ⟨p, j, fun verdict => MultiTapeTM.step_of_halt (by simp [replayCfg, hs])⟩
  rcases ha : (ntm.actions state p.last.inputSymbol p.last.workTapeSymbols)[j.val]? with _ | a
  · exact ⟨p, j, fun verdict => by rw [replayStep_take hs, ha]⟩
  have hstep : ntm.Step p.last (a.apply p.last) := by
    simp only [Step, hs]
    exact ⟨a, ntm.mem_actions.mp (List.mem_of_getElem? ha), rfl⟩
  obtain ⟨q, -, hq⟩ := p.exists_snoc hstep
  exact ⟨q, 0, fun verdict => by
    rw [replayStep_take hs, ha]
    exact congrArg (fun c => replayCfg c 0 verdict) hq.symm⟩

private theorem replayCoins_reachable (coins : List Bool) (p : ntm.ComputationPath input)
    (j : Candidate k State) :
    ∃ (q : ntm.ComputationPath input) (i : Candidate k State), ∀ verdict,
      (graphReplay ntm verdict).stepCoins coins (replayCfg p.last j verdict) =
        replayCfg q.last i verdict := by
  induction coins generalizing p j with
  | nil => exact ⟨p, j, fun _ => rfl⟩
  | cons bit coins ih =>
    obtain ⟨p', j', hp⟩ := replayStep_reachable p j bit
    obtain ⟨q, i, hq⟩ := ih p' j'
    exact ⟨q, i, fun verdict => by rw [MultiTapePTM.stepCoins_cons, hp, hq]⟩

private theorem replayCoins_skip (c : Cfg k Bool State input) (i : ℕ)
    (hi : i ≤ Nat.card (Action k Bool State)) (verdict : Bool) :
    (graphReplay ntm verdict).stepCoins (List.replicate i false) (replayCfg c 0 verdict) =
      replayCfg c ⟨i, Nat.lt_succ_of_le hi⟩ verdict := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [List.replicate_succ', MultiTapePTM.stepCoins_append, ih (by omega),
      MultiTapePTM.stepCoins_cons, MultiTapePTM.stepCoins_nil, replayStep_skip]
    simp [nextCandidate, min_eq_left hi]

private theorem replayCoins_complete (p : ntm.RunPath input) :
    ∃ coins : List Bool, coins.length ≤ Nat.card (Action k Bool State) * p.length ∧
      ∀ verdict, (graphReplay ntm verdict).stepCoins coins (replayCfg p.head 0 verdict) =
        replayCfg p.last 0 verdict := by
  induction p using RelSeries.inductionOn' with
  | singleton c => exact ⟨[], by simp, fun _ => rfl⟩
  | snoc p c hc ih =>
    obtain ⟨coins, hlen, hcoins⟩ := ih
    simp only [RelSeries.head_snoc, RelSeries.last_snoc, RelSeries.snoc_length]
    rcases hs : p.last.state with _ | q
    · have heq : c = p.last := (MultiTapeNTM.step_of_halt hs).mp hc
      exact ⟨coins, hlen.trans (Nat.mul_le_mul_left _ (Nat.le_succ _)), heq ▸ hcoins⟩
    · change ntm.Step p.last c at hc
      simp only [Step, hs] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      obtain ⟨j, hj, hget⟩ := List.getElem_of_mem (ntm.mem_actions.mpr ha)
      have hcard := ntm.length_actions_le q p.last.inputSymbol p.last.workTapeSymbols
      refine ⟨coins ++ (List.replicate j false ++ [true]), ?_, fun verdict => ?_⟩
      · simp only [List.length_append, List.length_replicate, List.length_singleton, Nat.mul_succ]
        omega
      · rw [MultiTapePTM.stepCoins_append, hcoins, MultiTapePTM.stepCoins_append,
          replayCoins_skip _ _ (by omega), MultiTapePTM.stepCoins_cons,
          MultiTapePTM.stepCoins_nil, replayStep_take hs]
        rw [List.getElem?_eq_getElem hj, hget]

private theorem runClosedCoins_graphReplay (verdict : Bool) (coins : List Bool) :
    (graphReplay ntm verdict).runClosedCoins coins input =
      ((graphReplay ntm verdict).stepCoins coins
        (replayCfg (ntm.initCfg input) 0 verdict)).output := by
  rw [MultiTapePTM.runClosedCoins_eq_output_stepCoins]
  cases verdict <;> rfl

variable {α : Type} {enc : α ↪ List Bool}

private noncomputable def verifyGraph (ntm : MultiTapeNTM k Bool State) (enc : α ↪ List Bool)
    (x : (α × List Bool) × List Bool) : Bool :=
  decide ((graphReplay ntm true).runClosedCoins x.2 (enc x.1.1) = [true] ∧
    (graphReplay ntm false).runClosedCoins x.2 (enc x.1.1) = true :: x.1.2)

open ComputableInPolyTime in
private theorem computableInPolyTime_verifyGraph :
    ComputableInPolyTime (verifyGraph ntm enc) (encPair (encPair enc encBits) encBits) encBool := by
  let encGraph := encPair enc encBits
  let encVerifier := encPair encGraph encBits
  have hEncode : ComputableInPolyTime (fun a => enc a) enc encBits := of_eq fun _ => rfl
  have ha := hEncode.comp ((fst enc encBits).comp (fst encGraph encBits))
  have hcoins := snd encGraph encBits
  have hrun (verdict : Bool) := ((graphReplay ntm verdict).computableInPolyTime_runClosedCoins).comp
    (hcoins.prod ha)
  have hw := (snd enc encBits).comp (fst encGraph encBits)
  have hword : ComputableInPolyTime (fun x : (α × List Bool) × List Bool => true :: x.1.2)
      encVerifier encBits := bitsCons (const true) hw
  exact decide_and ((hrun true).decide_eq' (const [true])) ((hrun false).decide_eq' hword)

/-- A finite binary machine with polynomially bounded running time has a polynomially balanced
successful output relation whose graph is in NP. A successful branch halts with output
`true :: w`, where `w` is the result. -/
theorem mem_NPMV_of_runsInPolyTime {t : α → ℕ}
    (ht : PolyBounded (fun a => (enc a).length) t) (hrun : ∀ a, ntm.RunsInTime (enc a) (t a)) :
    (fun a w => ntm.Produces (enc a) w) ∈ NPMV enc := by
  obtain ⟨c, d, hle⟩ := ht.exists_le
  refine ⟨⟨Polynomial.C c * (Polynomial.X + 1) ^ d, ?_⟩, ?_⟩
  · rintro a w ⟨p, hp, hout⟩
    obtain ⟨q, hq, hlast⟩ := (hrun a).exists_time_eq p hp
    have hlen := RunPath.length_output_last_le q.toRunPath
    change q.last.output.length ≤ q.head.output.length + q.time at hlen
    rw [q.head_eq, hq, hlast, hout] at hlen
    have hinit : (ntm.initCfg (enc a)).output = [] := rfl
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, hinit, List.length_nil, Nat.zero_add,
      List.length_cons] at hlen ⊢
    exact (Nat.le_succ _).trans (hlen.trans (hle a))
  refine ⟨Polynomial.C (Nat.card (Action k Bool State) * c) * (Polynomial.X + 1) ^ d,
    verifyGraph ntm enc, computableInPolyTime_verifyGraph, IsVerifier.of_padding ?_ ?_⟩
  · rintro ⟨a, w⟩ coins - hverify
    let p : ntm.ComputationPath (enc a) := ⟨RelSeries.singleton _ (ntm.initCfg (enc a)), rfl⟩
    obtain ⟨q, j, hq⟩ := replayCoins_reachable (ntm := ntm) coins p 0
    simp only [verifyGraph, decide_eq_true_eq, runClosedCoins_graphReplay] at hverify
    change ((graphReplay ntm true).stepCoins coins (replayCfg p.last 0 true)).output = [true] ∧
      ((graphReplay ntm false).stepCoins coins (replayCfg p.last 0 false)).output = true :: w
      at hverify
    rw [hq true, hq false] at hverify
    exact ⟨q, by simpa [replayCfg, Cfg.Halted] using hverify.1,
      by simpa [replayCfg] using hverify.2⟩
  · rintro ⟨a, w⟩ ⟨p, hp, hout⟩
    obtain ⟨q, hq, hlast⟩ := (hrun a).exists_time_eq p hp
    obtain ⟨coins, hlen, hcoins⟩ := replayCoins_complete q.toRunPath
    refine ⟨coins, ?_, fun n => ?_⟩
    · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_one, mul_assoc]
      exact hlen.trans (Nat.mul_le_mul_left _ (by
        rw [show q.toRunPath.length = q.time from rfl, hq]
        refine (hle a).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left ?_ d))
        exact Nat.add_le_add_right (length_le_encPair_left enc encBits (a, w)) 1))
    · have hhalt : q.last.state = none := hlast ▸ hp
      have hreplay (verdict : Bool) :
          (graphReplay ntm verdict).runClosedCoins (coins ++ List.replicate n false) (enc a) =
            (replayCfg q.last 0 verdict).output := by
        rw [runClosedCoins_graphReplay, MultiTapePTM.stepCoins_append, ← q.head_eq, hcoins,
          MultiTapePTM.stepCoins_of_halted _ (by simp [replayCfg, hhalt])]
      simp [verifyGraph, hreplay, replayCfg, hlast, hout, show p.last.state = none from hp]

end Cslib.Complexity
