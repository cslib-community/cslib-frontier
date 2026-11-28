/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer.Copy
import Mathlib.Tactic.FinCases

import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives

/-!
# Basic functions with bounds of given degrees

Functions on unary numbers and integers, in linear time and space, and signed-unary transducers.

## Main definitions

* `Turing.MultiTapeTM.encUnary`: natural numbers in unary.
* `Turing.MultiTapeTM.encIntUnary`: integers in unary, as a sign bit followed by a unary
  magnitude.

## Main results

* successor, predecessor and zero test in unary, and adding one or subtracting one on unary
  integers.
-/

namespace Turing.MultiTapeTM

/-! ### Unary numbers -/




/-! ### Integers -/

/-- Integers in **unary**: `false` followed by `n` ones for `n ≥ 0`, and `true` followed by `n`
ones for `-(n + 1)`. The code of `z` has `z.natAbs + 1` bits when `0 ≤ z` and `z.natAbs` bits when
`z < 0`; `Turing.MultiTapeTM.encIntBin` is the binary sign-magnitude encoding. -/
@[expose] public def encIntUnary : ℤ ↪ List Bool :=
  ⟨fun z => match z with
    | .ofNat n => false :: List.replicate n true
    | .negSucc n => true :: List.replicate n true,
   fun a b h => by
    cases a <;> cases b <;> simp_all [List.replicate_inj]⟩

@[simp]
public lemma encIntUnary_ofNat (n : ℕ) :
    encIntUnary (Int.ofNat n) = false :: List.replicate n true :=
  rfl

@[simp]
public lemma encIntUnary_natCast (n : ℕ) :
    encIntUnary (n : ℤ) = false :: List.replicate n true :=
  rfl

@[simp]
public lemma encIntUnary_zero : encIntUnary 0 = [false] := rfl

@[simp]
public lemma encIntUnary_natCast_add_one (n : ℕ) :
    encIntUnary ((n : ℤ) + 1) = false :: true :: List.replicate n true :=
  rfl

@[simp]
public lemma encIntUnary_negSucc (n : ℕ) :
    encIntUnary (Int.negSucc n) = true :: List.replicate n true :=
  rfl

public lemma length_encIntUnary (z : ℤ) :
    (encIntUnary z).length = if z < 0 then (-z).toNat else z.toNat + 1 := by
  rcases z with n | n <;> simp [Int.negSucc_lt_zero]

public lemma length_encIntUnary_add_one_le (z : ℤ) :
    (encIntUnary (z + 1)).length ≤ (encIntUnary z).length + 1 := by
  rw [length_encIntUnary, length_encIntUnary]; split_ifs <;> omega

public lemma length_encIntUnary_sub_one_le (z : ℤ) :
    (encIntUnary (z - 1)).length ≤ (encIntUnary z).length + 1 := by
  rw [length_encIntUnary, length_encIntUnary]; split_ifs <;> omega

namespace EncIntUnary

/-- Adds one to a unary encoded integer. -/
public def succT : Transducer Bool (Fin 3) where
  q₀ := 0
  step q b := match q, b with
    | 0, false => (2, [false, true])
    | 0, true => (1, [])
    | 1, b => (2, [b])
    | _, b => (2, [b])
  final q := if q = 1 then [false] else []
  length_step_le q b := by fin_cases q <;> cases b <;> simp
  length_final_le q := by split_ifs <;> simp

/-- Subtracts one from a unary encoded integer. -/
public def predT : Transducer Bool (Fin 3) where
  q₀ := 0
  step q b := match q, b with
    | 0, false => (1, [])
    | 0, true => (2, [true, true])
    | 1, _ => (2, [false])
    | _, b => (2, [b])
  final q := if q = 1 then [true] else []
  length_step_le q b := by fin_cases q <;> cases b <;> simp
  length_final_le q := by split_ifs <;> simp

/-- The signed-unary successor transducer, started in its designated initial state, computes
integer successor. -/
public theorem run_succT (z : ℤ) :
    encIntUnary (z + 1) = succT.run succT.q₀ (encIntUnary z) := by
  have copy := Transducer.run_eq_self succT 2 (fun bit => by cases bit <;> rfl) rfl
  have hq : succT.q₀ = 0 := rfl
  have h0f : succT.step 0 false = (2, [false, true]) := rfl
  have h0t : succT.step 0 true = (1, []) := rfl
  have h1t : succT.step 1 true = (2, [true]) := rfl
  have hf1 : succT.final 1 = [false] := rfl
  rw [hq]
  rcases z with n | _ | n
  · simp [h0f, copy]
  · change [false] = succT.run 0 [true]
    simp [h0t, hf1]
  · change encIntUnary (Int.negSucc n) = _
    simp [h0t, h1t, copy, List.replicate_succ]

/-- The signed-unary predecessor transducer, started in its designated initial state, computes
integer predecessor. -/
public theorem run_predT (z : ℤ) :
    encIntUnary (z - 1) = predT.run predT.q₀ (encIntUnary z) := by
  have copy := Transducer.run_eq_self predT 2 (fun bit => by cases bit <;> rfl) rfl
  have hq : predT.q₀ = 0 := rfl
  have h0f : predT.step 0 false = (1, []) := rfl
  have h0t : predT.step 0 true = (2, [true, true]) := rfl
  have h1t : predT.step 1 true = (2, [false]) := rfl
  have hf1 : predT.final 1 = [true] := rfl
  rw [hq]
  rcases z with (_ | n) | n
  · change [true] = predT.run 0 [false]
    simp [h0f, hf1]
  · simp [h0f, h1t, copy]
  · simp [h0t, copy, List.replicate_succ]

end EncIntUnary

namespace ComputableInDegree

open EncIntUnary in
/-- Signed-unary successor from the existing public transducer. -/
public theorem int_succ : ComputableInDegree (· + 1) encIntUnary encIntUnary 1 1 :=
  .of_transducer succT run_succT

open EncIntUnary in
/-- Signed-unary predecessor from the existing public transducer. -/
public theorem int_pred : ComputableInDegree (· - 1) encIntUnary encIntUnary 1 1 :=
  .of_transducer predT run_predT

end ComputableInDegree

end Turing.MultiTapeTM
