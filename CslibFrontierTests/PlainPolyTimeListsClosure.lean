/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (ordinary-import regression client)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-! # Plain list closure clients

Computed lists and captured callbacks retain their argument order and duplicates. Unary and
binary lookup agree on examples outside the list, without expanding an unbounded binary index.
The resource example enlarges workspace independently of the actual time clock.
-/

-- This ordinary-import regression module exports no fixtures.
set_option linter.privateModule false

open Turing.MultiTapeTM
open ComputableInPolyTime

private def captured (p : Bool × List Bool) : List (Bool × Bool) :=
  p.2.reverse.map (fun bit => (p.1, bit))

example : ComputableInPolyTime captured (encPair encBool (encList encBool))
    (encList (encPair encBool encBool)) := by
  unfold captured
  apply mapWithInput
  · exact listReverseWithInput (snd _ _)
  · fun_prop

example : captured (true, [false, true, true]) =
    [(true, true), (true, true), (true, false)] := rfl

example : captured (false, [false, true, true]) =
    [(false, true), (false, true), (false, false)] := rfl

private def selected (p : Bool × List Bool) : List Bool :=
  p.2.filter (fun bit => bit == p.1)

example : ComputableInPolyTime selected (encPair encBool encBits) encBits := by
  unfold selected
  apply bitsFilterWithInput (snd _ _)
  fun_prop

example : selected (true, [false, true, false, true]) = [true, true] := rfl

example : ComputableInPolyTime
    (fun p : Bool × List Bool => p.2.count p.1) (encPair encBool encBits) encUnary := by
  exact bitsCountWithInput (snd _ _) (fst _ _)

example : ComputableInPolyTime
    (fun p : List Bool × ℕ => p.1.getD p.2 false) (encPair encBits encNat) encBool := by
  exact listGetD_binary false (fst _ _) (snd _ _)

example : ([true, false, true] : List Bool).getD (2 ^ 100) false = false := by decide

example : ComputableInPolyTime
    (fun p : ℕ × List Bool => Cslib.BitString.boundedBinaryValue p.1 p.2)
    (encPair encUnary encBits) encUnary := by
  exact bitsBoundedBinaryValueWithInput (fst _ _) (snd _ _)

example : Cslib.BitString.boundedBinaryValue 2 [true, false, true] = 2 := by decide

example : ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    ComputableInTimeAndSpace selected (encPair encBool encBits) encBits
      (fun p => t (encPair encBool encBits p).length)
      (fun p => s (encPair encBool encBits p).length +
        ((encPair encBool encBits p).length + 1) ^ 7) := by
  have hc : ComputableInPolyTime selected (encPair encBool encBits) encBits := by
    unfold selected
    apply bitsFilterWithInput (snd _ _)
    fun_prop
  obtain ⟨t, s, ht, hs, hmachine⟩ := hc
  exact ⟨t, s, ht, hs, hmachine.mono (fun _ => le_rfl)
    (fun _ => Nat.le_add_right _ _)⟩

-- A nonempty constant output needs no work cells; output is separate from workspace.
example : ∃ t : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧
    ComputableInTimeAndSpace (fun _ : List Bool => [true, false, true]) encBits encBits
      (fun word => t word.length) (fun _ => 0) := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const
    (encIn := encBits) (encOut := encBits) [true, false, true]
  exact ⟨fun _ => c, by fun_prop, h⟩
