/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Native
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Independent clients of the native quantified-word compiler

One client has a runtime unary number of existential choices and tests their disjunction.
The other changes quantifier order at runtime: equality is winnable exactly when the universal
bit comes first. Both choose their finite machine and polynomial constants before the input.
-/

public section

namespace Turing.MultiTapeATM.QuantifiedWord.Tests

open MultiTapeTM Cslib.BitString

private theorem plays_or (n : ℕ) :
    plays (fun xs => xs.any id = true) [] (List.replicate n false) ↔ 0 < n := by
  have h := plays_exists_field (fun xs => xs.any id = true) [] [] n
  simp only [List.append_nil, List.nil_append, plays] at h
  rw [h]
  cases n with
  | zero => simp [lowBits]
  | succ n =>
    constructor
    · intro _
      exact Nat.succ_pos n
    · intro _
      let word := true :: List.replicate n false
      have hword : word.length = n + 1 := by simp [word]
      refine ⟨⟨lsbValue word, by simpa only [hword] using lsbValue_lt word⟩, ?_⟩
      change (lowBits (n + 1) (lsbValue word)).any id = true
      rw [← hword, lowBits_lsbValue]
      simp [word]

/-- A single native machine accepts the disjunction of any positive number of existential
bits, and rejects the empty disjunction. Its clock depends only on the unary length input. -/
theorem existential_disjunction :
    ∃ (K : ℕ) (source : Fin K) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM K Bool S) (C D : ℕ),
      ∀ (input : List Bool) (n : ℕ),
        let start := WordGameLeaf.config source (some atm.toPTM.initial) (encUnary n) 0
          (TwoWordLoad.blank K input)
        let time := C * ((encUnary n).length + 1) ^ D
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ 0 < n) := by
  have hcheck : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.any id)
      (encPair encUnary encBits) encBool :=
    ComputableInPolyTime.bitsAnyWithInput (by fun_prop) (by fun_prop)
  obtain ⟨K, source, S, hS, atm, C, D, h⟩ :=
    exists_evaluator encUnary (fun n => List.replicate n false)
      (fun p => p.2.any id) (ComputableInPolyTime.bitsReplicate false) hcheck
  exact ⟨K, source, S, hS, atm, C, D, fun input n =>
    ⟨(h input n).1, (h input n).2.trans (plays_or n)⟩⟩

private def orderFlags (universalFirst : Bool) : List Bool :=
  if universalFirst then [true, false] else [false, true]

private def equalBits (p : Bool × List Bool) : Bool :=
  decide (p.2.headD false = p.2.tail.headD false)

private theorem plays_equalBits (universalFirst : Bool) :
    plays (fun xs => equalBits (universalFirst, xs) = true) [] (orderFlags universalFirst) ↔
      universalFirst = true := by
  cases universalFirst <;>
    simp [orderFlags, plays, equalBits, Bool.forall_bool]

/-- The same machine handles both runtime quantifier orders. An existential bit can match
an earlier universal bit, but cannot match both values of a later universal bit. -/
theorem alternating_equality :
    ∃ (K : ℕ) (source : Fin K) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM K Bool S) (C D : ℕ),
      ∀ (input : List Bool) (universalFirst : Bool),
        let start := WordGameLeaf.config source (some atm.toPTM.initial)
          (encBool universalFirst) 0 (TwoWordLoad.blank K input)
        let time := C * ((encBool universalFirst).length + 1) ^ D
        atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔ universalFirst = true) := by
  have hcheck : ComputableInPolyTime equalBits (encPair encBool encBits) encBool := by
    unfold equalBits
    fun_prop
  obtain ⟨K, source, S, hS, atm, C, D, h⟩ :=
    exists_evaluator encBool orderFlags equalBits
      (ComputableInPolyTime.of_finite orderFlags) hcheck
  exact ⟨K, source, S, hS, atm, C, D, fun input universalFirst =>
    ⟨(h input universalFirst).1, (h input universalFirst).2.trans
      (plays_equalBits universalFirst)⟩⟩

end Turing.MultiTapeATM.QuantifiedWord.Tests
