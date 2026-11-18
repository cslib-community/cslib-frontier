/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Scheme

/-!
# Tests for Free-XOR garbling as a scheme family

A client of `CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Scheme` under module encapsulation.

We build two multi-gate circuits combining AND, OR and XOR gates with the same topology and XOR
gate positions, and check garbling, evaluation and decoding across all eight inputs.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GarblingFreeXORFamily

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling Cslib.Probability

/-- Four-gate circuit over 3 inputs: gate 0 is `x₀ ∧ x₁` (wire 4), gate 1 is `x₁ ∨ x₂` (wire 5),
gate 2 is `x₀ ⊕ (x₀ ∧ x₁)` (output 0), and gate 3 is `(x₀ ∧ x₁) ⊕ (x₁ ∨ x₂)` (output 1). -/
def circuit₁ : ConventionalCircuit :=
  ⟨3, 2, 4, ![1, 2, 1, 4], ![2, 3, 4, 5], ![(· && ·), (· || ·), xor, xor]⟩

/-- A second circuit with the same topology and XOR positions, swapping AND and OR at gates 0 and
1. -/
def circuit₂ : ConventionalCircuit :=
  ⟨3, 2, 4, ![1, 2, 1, 4], ![2, 3, 4, 5], ![(· || ·), (· && ·), xor, xor]⟩

/-- Both circuits are valid. -/
def validCircuit₁ : ValidCircuit := ⟨circuit₁, by decide⟩

/-- The second circuit is valid too. -/
def validCircuit₂ : ValidCircuit := ⟨circuit₂, by decide⟩

/-- The two circuits themselves are distinct. -/
example : validCircuit₁ ≠ validCircuit₂ := by decide

/-- A polynomial-time toy hash on words: the label XORed with copies of the tweak. -/
def toyHash (x t : List Bool) : List Bool := List.zipWith xor x (t ++ t ++ t)

/-- Fixed coins for `k = 2`: `3` bits for the offset key, then `7 * 4 = 28` bits for the `3 + 4`
wire labels. -/
def coins : List Bool := List.ofFn fun i : Fin 31 => decide (i.val % 3 = 1)

/-- The first circuit garbled at `k = 2` on `coins`. -/
def garbled₁ : Scheme.Garbled := (FreeXOR.scheme toyHash).gb 2 validCircuit₁ coins

/-- The second circuit garbled at `k = 2` on `coins`. -/
def garbled₂ : Scheme.Garbled := (FreeXOR.scheme toyHash).gb 2 validCircuit₂ coins

/-- `garbled₁` is in the support of `garble 2 validCircuit₁`. -/
example :
    garbled₁ ∈ (ProbComp.eval ((FreeXOR.scheme toyHash).garble 2 validCircuit₁)).support :=
  (FreeXOR.scheme toyHash).mem_support_eval_garble_iff.mpr ⟨coins, by decide, rfl⟩

/-- Changing non-XOR truth tables does not change the garbled function bit length. -/
example : garbled₁.fn.length = garbled₂.fn.length := by
  simp only [garbled₁, garbled₂, FreeXOR.scheme, FreeXOR.fnWord]
  decide

/-- Encoding, evaluating and decoding `garbled₁` computes the mixed AND/OR/XOR outputs on all
eight 3-bit inputs. -/
example : ∀ x₀ x₁ x₂ : Bool,
    (FreeXOR.scheme toyHash).decode garbled₁.decInfo
      ((FreeXOR.scheme toyHash).evalGarbled garbled₁.fn
        ((FreeXOR.scheme toyHash).encode garbled₁.encInfo [x₀, x₁, x₂])) =
      some [xor x₀ (x₀ && x₁), xor (x₀ && x₁) (x₁ || x₂)] := by
  simp only [garbled₁, FreeXOR.scheme, FreeXOR.fnWord, FreeXOR.evalWord,
    PointPermute.fnDecoder.decode_enc]
  decide

/-- Every outcome of the randomized garbler at every `k > 0` computes the circuit semantics. -/
example (k : ℕ) (hk : 0 < k) (x₀ x₁ x₂ : Bool) (g : Scheme.Garbled)
    (hg : g ∈ (ProbComp.eval ((FreeXOR.scheme toyHash).garble k validCircuit₁)).support) :
    (FreeXOR.scheme toyHash).decode g.decInfo
      ((FreeXOR.scheme toyHash).evalGarbled g.fn
        ((FreeXOR.scheme toyHash).encode g.encInfo [x₀, x₁, x₂])) =
      some [xor x₀ (x₀ && x₁), xor (x₀ && x₁) (x₁ || x₂)] := by
  rw [FreeXOR.scheme_correct toyHash k hk validCircuit₁ [x₀, x₁, x₂] rfl g hg]
  cases x₀ <;> cases x₁ <;> cases x₂ <;> rfl

end CslibFrontierTests.Crypto.GarblingFreeXORFamily
