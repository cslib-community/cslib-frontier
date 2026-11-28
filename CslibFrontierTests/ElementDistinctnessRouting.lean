/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import Cslib.Computability.Circuit.Full
import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.RoutingNetwork
import CslibFrontier.Computability.Circuit.InnerSize
import Mathlib.Data.ZMod.Basic

/-! The incoming records can be distinct while both tags request address zero. One unused
selector cancels the sum in characteristic two. Swapping the two addresses is a valid routing. -/

set_option linter.privateModule false

open Cslib Cslib.Circuits.Boolean Cslib.Circuits.Boolean.ElementDistinctness Finset
open Cslib.Circuits Cslib.Circuits.Frontier

private def payload (i : Fin 2) : BitString 1 := fun _ => i = 1

private def word (j : Fin 2) (x : BitString 1) :=
  Fin.append (BitString.indexBits j) x

private def test (tag : Fin 2 → Fin 2) (y : Fin 2 → BitString 1) (S : Finset (Fin 2)) :=
  elementDistinctness _ _ (comparisonInput (fun i => word (tag i) (payload i))
    (fun j => word j (y j)) S)

example : test (fun _ => 0) payload ∅ = true ∧ test (fun _ => 0) payload {1} = true := by
  decide

example : (∑ S : Finset (Fin 2), if test (fun _ => 0) payload S then (-1 : ZMod 2) ^ #S else 0)
    = 0 := by decide

private def twoRows (tag input output : Fin 2 → Bool) : RoutingBit 1 → Bool
  | .tag i _ => tag i
  | .input i _ => input i
  | .output i _ => output i

-- The same network extracted from a circuit for five six-bit records accepts a swap and
-- rejects a repeated destination. Five is strictly between two dyadic list lengths.
example :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
      (M : OpenBitNetwork (ZMod 2) (RoutingBit 1) V E), M.Trivalent ∧
        M.contraction (twoRows (· == 0) (· == 0) (· == 1)) = 1 ∧
        M.contraction (twoRows (fun _ => false) (· == 0) (· == 0)) = 0 := by
  obtain ⟨C, hc, _⟩ := exists_computes_size_eq_complexity (I := fullInterpretation (k := 2))
    (f := single (elementDistinctness 5 (2 * Nat.clog 2 5)))
  obtain ⟨V, E, iV, iE, dE, M, ht, _, heval⟩ := exists_routingNetwork_of_computes
    (h := 1) (by decide) (by decide) fullInterpretation C C.fanInAtMost_fullSignature hc (ZMod 2)
  refine ⟨V, E, iV, iE, dE, M, ht, ?_, ?_⟩
  · have hswap : TaggedPermutation (twoRows (· == 0) (· == 0) (· == 1)) := by
      unfold TaggedPermutation Function.Bijective Function.Injective Function.Surjective
      decide
    simp [heval, hswap]
  · have hrepeat : ¬TaggedPermutation (twoRows (fun _ => false) (· == 0) (· == 0)) := by
      unfold TaggedPermutation Function.Bijective Function.Injective Function.Surjective
      decide
    simp [heval, hrepeat]

example : (∑ S : Finset (Fin 2), if test Fin.rev (payload ∘ Fin.rev) S then (-1 : ℤ) ^ #S else 0)
    = 1 := by decide

example : (∑ S : Finset (Fin 2), if test id (payload ∘ Fin.rev) S then (-1 : ℤ) ^ #S else 0)
    = 0 := by decide
