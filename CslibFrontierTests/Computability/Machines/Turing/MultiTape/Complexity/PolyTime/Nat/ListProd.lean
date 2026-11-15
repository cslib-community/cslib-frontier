/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd

/-! # Clients of the polynomial-time product of a list of binary naturals -/

open Turing.MultiTapeTM

/-- `fun_prop` finds `binary_prod`. -/
example : ComputableInPolyTime (fun l : List ℕ => l.prod) (encList encNat) encNat := by
  fun_prop

/-- The composed form at a concrete `H`, the binary value `ofBits w` of a word: a product of
hashes `∏ H x` over a list of words. -/
example : ComputableInPolyTime (fun l : List (List Bool) => (l.map ofBits).prod)
    (encList encBits) encNat :=
  ComputableInPolyTime.binary_prod_map ComputableInPolyTime.bitsToNat

/-- `fun_prop` also composes `binary_prod` with `List.map` for a hash `H` given only by its
certificate. -/
example (H : List Bool → ℕ) (hH : ComputableInPolyTime H encBits encNat) :
    ComputableInPolyTime (fun l : List (List Bool) => (l.map H).prod) (encList encBits) encNat := by
  fun_prop

/-- The empty list: the certified product is `1`, whose binary code is `[true]`, although the
encoded input is the empty word. -/
example : encNat (([] : List (List Bool)).map ofBits).prod = [true] := rfl

/-- A list containing `0`, whose code is the empty word: the product is `0`, whose binary code is
also empty. Here `ofBits [false] = 0`. -/
example : encNat ([3, 0, 1] : List ℕ).prod = [] ∧
    encNat ([[true, true], [false], [true]].map ofBits).prod = [] :=
  ⟨rfl, rfl⟩

/-- The certificate applies to a computed list that contains `0`. -/
example : ComputableInPolyTime (fun l : List ℕ => (0 :: l).prod) (encList encNat) encNat := by
  fun_prop
