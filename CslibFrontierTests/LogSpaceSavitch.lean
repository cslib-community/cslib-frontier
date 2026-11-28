/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Savitch
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.Savitch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Savitch

/-!
# Tests: Savitch's theorem

Words of a fixed width; the edge test, the recursion of a round and a round of the search over
the radices as certified functions of stored registers and the input;
the two recursions, reporting no overflow and deciding acceptance, for a machine without work
tapes that accepts every input, so that the hypotheses of the machine-level theorem are
satisfiable; the general inclusion `NSPACE(s) ⊆ DSPACE(s²)` at linear and sublinear bounds; and
the class inclusions `NL ⊆ DSPACE(log² n)` and `RL ⊆ DSPACE(log² n)` on concrete problems. A
nontrivial first-bit language checks the RL bridge and the quadratic-space conclusion on
accepting, rejecting and empty inputs.
-/

-- This module contains only checked clients.
set_option linter.privateModule false

namespace CslibFrontierTests.LogSpaceSavitch

open Cslib.Turing Turing Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeNTM.ConfigurationGraph Turing.MultiTapeNTM.SquareSavitch
open Cslib.BitString (lowBits)

/-! ### Words of a fixed width -/

example : lowBits 4 5 = [true, false, true, false] := by decide
example : ofBits (lowBits 6 37) = 37 := by decide
example : (lowBits 3 0, lowBits 0 0) = ([false, false, false], []) := by decide

/-! ### A machine accepting every input -/

def acceptAction : Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }

private def acceptMachine : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ a := a = acceptAction

private theorem accepts_acceptMachine (w : List Bool) : acceptMachine.Accepts w := by
  have hstep : acceptMachine.Step (acceptMachine.initCfg w)
      (acceptAction.apply (acceptMachine.initCfg w)) := ⟨acceptAction, rfl, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (acceptMachine.initCfg w) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [acceptAction]

/-- The edge test of a round is a certified function of two stored words, the stored radix and the
input, within the stored words and the logarithm of the length of the input. -/
example (mode : Bool) : ComputableInSpace
    (fun q : ((List Bool × List Bool) × SearchState) × List Bool =>
      inputEdge acceptMachine mode q.1.2.radix q.2 q.1.1.1 q.1.1.2)
    (encPair encEdgeRegisters encBits) encBool
    fun q => (encEdgeRegisters q.1).length + Nat.log2 (encBits q.2).length :=
  inputEdge_inSpace acceptMachine encBits mode

/-- The recursion of a round, from the stored radix and the input. -/
example (mode : Bool) : ComputableInSpace
    (fun p : SearchState × List Bool => sinkReach acceptMachine mode p.1.radix p.2)
    (encPair encSearch encBits) encBool (roundBudget (k := 0) encBits) :=
  sinkReach_inSpace acceptMachine encBits mode

/-- A round of the search over the radices, within the budget of a round. -/
example : ComputableInSpace (search acceptMachine encBits) (encPair encSearch encBits)
    (encOption encSearch) (roundBudget (k := 0) encBits) :=
  search_inSpace acceptMachine encBits

/-- A machine within space `0` has no reachable overflow from round `1` on, so the overflow
recursion reports none. -/
example (w : List Bool) : sinkReach acceptMachine true (roundRadix Unit w.length 1) w = false :=
  Bool.eq_false_iff.mpr fun h => not_overflowReachable_of_runsInSpace (S := 0)
    (MultiTapeNTM.runsInSpace_zero_tapes _ _ _) le_rfl ((sinkReach_true_iff
      (card_lt_roundRadix (State := Unit) w.length 1)).mp h)

/-- Without reachable overflow, the acceptance recursion decides acceptance, here of every
input. -/
example (w : List Bool) : sinkReach acceptMachine false (roundRadix Unit w.length 1) w = true :=
  (sinkReach_false_iff (card_lt_roundRadix (State := Unit) w.length 1)
    (not_overflowReachable_of_runsInSpace (S := 0) (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)
      le_rfl)).mpr (accepts_acceptMachine w)

/-- The machine-level theorem applies to a concrete recognizer, without a space bound to
construct. -/
example : ∃ t c', DecidableInTimeAndSpace (Set.univ : Set (List Bool)) encBits t
    fun w => c' * (0 + Nat.log2 (encBits w).length + 1) ^ 2 :=
  MultiTapeNTM.exists_decidableInTimeAndSpace_sq (ntm := acceptMachine) (S := fun _ => 0)
    fun w => ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, by simpa using accepts_acceptMachine w⟩

example : (Set.univ : Set (List Bool)) ∈ DSPACE encBits fun n => Nat.log2 n ^ 2 :=
  mem_DSPACE_sq_of_recognizesInSpace (fun _ => le_rfl) (ntm := acceptMachine) (c₁ := 0) (c₂ := 0)
    fun w => ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, by simpa using accepts_acceptMachine w⟩

/-! ### The general inclusion -/

example {α : Type} (enc : α ↪ List Bool) : NSPACE enc id ⊆ DSPACE enc fun n => id n ^ 2 :=
  NSPACE_subset_DSPACE_sq Nat.log2_le_self

/-- A sublinear bound other than `log₂`. -/
example {α : Type} (enc : α ↪ List Bool) :
    NSPACE enc (fun n => Nat.log2 n ^ 2) ⊆ DSPACE enc fun n => (Nat.log2 n ^ 2) ^ 2 :=
  NSPACE_subset_DSPACE_sq fun _ => Nat.le_self_pow two_ne_zero _

/-! ### The class inclusions -/

example {α : Type} (enc : α ↪ List Bool) : NL enc ⊆ DSPACE enc fun n => Nat.log2 n ^ 2 :=
  NL_subset_DSPACE_log2_sq

example {α : Type} (enc : α ↪ List Bool) : RL enc ⊆ DSPACE enc fun n => Nat.log2 n ^ 2 :=
  RL_subset_DSPACE_log2_sq

/-- Every problem in `L` is in `DSPACE(log² n)` through `RL`. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ L enc) :
    A ∈ DSPACE enc fun n => Nat.log2 n ^ 2 :=
  RL_subset_DSPACE_log2_sq (L_subset_RL h)

/-! ### A nontrivial language through the RL and native Savitch bridges -/

/-- Words beginning in `true`; the empty word is rejected. -/
private def startsTrue : Set (List Bool) := {w | w.headD false = true}

private theorem startsTrue_mem_RL : startsTrue ∈ RL encBits :=
  L_subset_RL ⟨_, ComputableInLogSpace.bitsHeadD false, fun _ => Iff.rfl⟩

example : [true, false] ∈ startsTrue := by simp [startsTrue]
example : [false, true] ∉ startsTrue := by simp [startsTrue]
example : [] ∉ startsTrue := by simp [startsTrue]

/-- An actual logspace client reaches the deterministic quadratic-space endpoint. -/
example : startsTrue ∈ DSPACE encBits fun n => Nat.log2 n ^ 2 :=
  RL_subset_DSPACE_log2_sq startsTrue_mem_RL

/-- The native simulation supplies a total decider, not just a graph-level reachability fact. -/
example : ∃ c₁ c₂ t, DecidableInTimeAndSpace startsTrue encBits t
    fun w => c₁ * Nat.log2 (encBits w).length ^ 2 + c₂ :=
  mem_DSPACE_iff.mp (RL_subset_DSPACE_log2_sq startsTrue_mem_RL)

/-! ### Named registers keep the encoded words -/

example (s : SearchState) :
    encSearch s = encPair encNat (encOption encBool) (s.radix, s.answer) := rfl

end CslibFrontierTests.LogSpaceSavitch
