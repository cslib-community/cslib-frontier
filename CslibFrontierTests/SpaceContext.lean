/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Context
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Tactic.Space

/-!
# Certificates of stored registers next to a read-only input, by `space`

A counter held in registers next to a word that is only read: the body steps the counter, tests
it for overflow, compares it with a stored word and looks up the input where the value of the
counter points. Its budget charges the registers and the logarithm of the length of the word, not
the word. The leaves are the registers and the input bit at a computed position; `space` composes
the rest, including the constants, which need no allowance for the length of the input.
-/

-- This module contains only checked clients.
set_option linter.privateModule false

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

namespace SpaceContextTest

/-- The registers: a counter and a word to compare it with. -/
abbrev encReg : List Bool × List Bool ↪ List Bool := encPair encBits encBits

/-- The budget: the registers and the logarithm of the length of the input. -/
abbrev budget (p : (List Bool × List Bool) × List Bool) : ℕ :=
  (encReg p.1).length + Nat.log2 (encBits p.2).length

/-- The body: stop when the counter overflows or equals the stored word, or when the input has a
one where the value of the counter points; otherwise step the counter. -/
def step (p : (List Bool × List Bool) × List Bool) : Option (List Bool × List Bool) :=
  if p.1.1.all id || decide (p.1.1 = p.1.2) || p.2[ofBits p.1.1]?.getD false then none
  else some (Cslib.BitString.increment p.1.1, p.1.2)

example : step (([false, false], [true, true]), [false, true]) =
    some ([true, false], [true, true]) := by decide
example : step (([true, false], [true, true]), [false, true]) = none := by decide
example : step (([true, true], [false, false]), []) = none := by decide

theorem step_inSpace :
    ComputableInSpace step (encPair encReg encBits) (encOption encReg) budget := by
  have hreg := budget_registers (encR := encReg) (encA := encBits) (Bs := budget) (.refl _)
  have hbit : ComputableInSpace
      (fun p : (List Bool × List Bool) × List Bool => p.2[ofBits p.1.1]?)
      (encPair encReg encBits) (encOption encBool) budget :=
    budget_inputBit (budget_ofBits hreg.fst') (.refl _)
  space [step]

/-- The input length occurs both in a certificate and in the goal's workspace budget. -/
example {α : Type} (encA : α ↪ List Bool) (test : α → List Bool → Bool)
    (htest : ComputableInSpace (fun p : List Bool × α => test p.2 p.1)
      (encPair encBits encA) encBool
      fun p => (encBits p.1).length + Nat.log2 (encA p.2).length) :
    ComputableInSpace (fun p : List Bool × α => !(test p.2 p.1))
      (encPair encBits encA) encBool
      fun p => (encBits p.1).length + Nat.log2 (encA p.2).length := by
  have hlen := budget_inputLength (encR := encBits) (encA := encA)
    (Bs := fun p => (encBits p.1).length + Nat.log2 (encA p.2).length) (.refl _)
  space

/-- A budget with a third summand: the registers are found by `space`, which proves that the
budget covers them as a bound of a sum by a sum that contains its terms. -/
example {S : List Bool → ℕ} : ComputableInSpace
    (fun p : (List Bool × List Bool) × List Bool => (Cslib.BitString.increment p.1.1, p.1.2))
    (encPair encReg encBits) encReg
    fun p => (encReg p.1).length + S p.2 + Nat.log2 (encBits p.2).length := by
  space

/-- A certified function of one stored word and the input, applied to the first register
(`budget_subst`), next to the concatenation of the registers. `space` turns its unary value into
binary (`budget_unaryToNat`) and concatenates (`budget_bitsAppend`). -/
example {g : List Bool × List Bool → ℕ}
    (hg : ComputableInSpace g (encPair encBits encBits) encUnary
      fun q => (encBits q.1).length + Nat.log2 (encBits q.2).length) :
    ComputableInSpace
      (fun p : (List Bool × List Bool) × List Bool => (p.1.2 ++ p.1.1, g (p.1.1, p.2)))
      (encPair encReg encBits) (encPair encBits encNat) budget := by
  have hsub := budget_subst (encR := encReg) (Bs := budget) hg
    ((ComputableInLogSpace.fst encBits encBits).comp' (.fst encReg encBits)) (.refl _)
    (.of_le fun p => by simp only [budget, length_encPair]; omega)
  space

/-- A constant, the word of zeros of a stored width and the length of the input, under a budget
that does not cover the input. -/
example : ComputableInSpace
    (fun p : ℕ × List Bool => (List.replicate p.1 false, p.2.length, 7))
    (encPair encUnary encBits) (encPair encBits (encPair encNat encNat))
    fun p => (encUnary p.1).length + Nat.log2 (encBits p.2).length := by
  have hlen : ComputableInSpace (fun p : ℕ × List Bool => p.2.length) (encPair encUnary encBits)
      encNat fun p => (encUnary p.1).length + Nat.log2 (encBits p.2).length :=
    budget_inputLength (.refl _)
  space

/-- A function of two groups of registers and the input, read as a function of the inner group
next to the outer group and the input. -/
example {f : (ℕ × ℕ) × List Bool → Bool} {T : (ℕ × ℕ) × List Bool → ℕ}
    (hf : ComputableInSpace f (encPair (encPair encNat encNat) encBits) encBool T) :
    ComputableInSpace (fun q : ℕ × ℕ × List Bool => f ((q.1, q.2.1), q.2.2))
      (encPair encNat (encPair encNat encBits)) encBool fun q =>
        T ((q.1, q.2.1), q.2.2) + (encNat q.1).length + (encNat q.2.1).length +
          Nat.log2 (encBits q.2.2).length :=
  assoc_context hf

-- The registers are not available under a budget that does not cover them.
example (_S : ℕ × List Bool → ℕ) : True := by
  fail_if_success
    have : ComputableInSpace (fun p : ℕ × List Bool => p.1 + 1) (encPair encNat encBits) encNat
        _S := by space
  trivial

end SpaceContextTest
