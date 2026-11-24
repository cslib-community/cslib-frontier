/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Counting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.BranchReplay

/-!
# Compiling unambiguous query machines into native UL

The native compiler preserves the accepting first-halting occurrence count. An abstract query
machine with logspace-certified components, a common stopping clock on each input and at most
one accepting first-halting trace therefore gives a native `UL` witness.

## Main results

* `Turing.NondeterministicQueryMachine.mem_UL_of_firstHalting`: compile a resource-certified
  unambiguous query-machine decider to the counting-machine definition of `UL`.
-/

public section

namespace Turing.NondeterministicQueryMachine

open Cslib.Complexity MultiTapeTM

/-- A query-machine decider with at most one accepting first-halting trace is in native `UL`
when its transition routines use linear space in the encoded state and its reachable states
have logarithmic encoded length. Each input has a common abstract clock for all branches. -/
theorem mem_UL_of_firstHalting {α σ : Type} {enc : α ↪ List Bool} {encS : σ ↪ List Bool}
    (M : NondeterministicQueryMachine σ)
    (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hnext : ComputableInSpace M.next
      (encPair encS (encPair (encOption encBool) encBool)) encS
      fun p => (encPair encS (encPair (encOption encBool) encBool) p).length)
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (haccept : ComputableInSpace M.accept encS encBool fun s => (encS s).length)
    (start : α → σ)
    (hstart : ComputableInSpace start enc encS (fun a => Nat.log2 (enc a).length + 1))
    (hsize : ∃ c, ∀ a choices,
      (encS (M.replay (enc a) choices (start a))).length ≤ c * (Nat.log2 (enc a).length + 1))
    (hhalt : ∀ a, ∃ time, (M.withInit (start a)).HaltsWithin (enc a) time)
    (hunique : ∀ a, {bits : List Bool | M.FirstHalting (enc a) bits (start a) ∧
      M.accept (M.replay (enc a) bits (start a)) = true}.Subsingleton)
    {A : Set α} (hcorrect : ∀ a, a ∈ A ↔ (M.withInit (start a)).Accepts (enc a)) :
    A ∈ UL enc := by
  classical
  let S (a : α) := Nat.log2 (enc a).length + 1
  obtain ⟨R⟩ := M.exists_routines hquery hnext hhalted haccept start S (fun _ => le_rfl)
    hstart hsize
  let : Finite R.SI := R.finiteI
  let : ∀ b, Finite (R.SP b) := R.finiteP
  let : Finite R.SF := R.finiteF
  choose time htime using hhalt
  choose fuel hfuel using fun a => R.exists_runsInTime a (htime a)
  let N := Native.countingMachine R.I R.P R.F R.C
  let f (a : α) := N.acceptCount (fuel a) (R.machine.initCfg (enc a))
  have hcount (a : α) : (f a : ℕ∞) =
      {bits : List Bool | M.FirstHalting (enc a) bits (start a) ∧
        M.accept (M.replay (enc a) bits (start a)) = true}.encard :=
    R.acceptCount_eq_encard_firstHalting a (hfuel a)
  refine ⟨f, ⟨R.k, Native.State R.SI R.SP R.SF, inferInstance, N, R.k * (2 * R.c + 1), ?_⟩,
    ?_, ?_⟩
  · intro a
    have hmachine : N.toNTM = R.machine := Native.toNTM_countingMachine R.I R.P R.F R.C
    have hcfg : Cfg.init N.initial (enc a) = R.machine.initCfg (enc a) :=
      congrArg (fun m => m.initCfg (enc a)) hmachine
    have hspace := (R.recognizesInSpace hcorrect
      (fun x => Nat.succ_pos (Nat.log2 (enc x).length)) a).1
    refine ⟨hmachine.symm ▸ hspace, fuel a, ?_, ?_⟩
    · rw [hcfg]
      exact Native.countingMachine_haltsWithin R.I R.P R.F R.C (hfuel a)
    · rw [hcfg]
  · intro a
    have hle : (f a : ℕ∞) ≤ 1 :=
      (hcount a).trans_le (Set.encard_le_one_iff_subsingleton.mpr (hunique a))
    exact_mod_cast hle
  · intro a
    rw [hcorrect a, accepts_iff_exists_firstHalting]
    have hp : (0 < f a) ↔ (0 : ℕ∞) < (f a : ℕ∞) := by exact_mod_cast Iff.rfl
    rw [hp, hcount a, Set.encard_pos]
    rfl

end Turing.NondeterministicQueryMachine
