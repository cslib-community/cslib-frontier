/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Scheme

/-!
# Tests for half-gates garbling as a garbling scheme

A client of `CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Conventional` and
`CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Scheme` under module encapsulation.

The circuit `x₀ ⊕ (x₀ ∧ x₁)`, one AND gate and one XOR gate, is an XOR–AND circuit. It is garbled
by `HalfGates.scheme` at `k = 2`, with a hash that XORs the label with copies of the tweak and
with fixed coins. The garbled function carries two ciphertexts for the AND gate and none for the
XOR gate. Encoding, evaluating and decoding gives `x₀ ⊕ (x₀ ∧ x₁)` on all four inputs, by
computation, and `scheme_correct` gives the same answer for every outcome of the randomized
garbler at every `k > 0`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GarblingHalfGates

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling

/-- `x₀ ⊕ (x₀ ∧ x₁)`: wire `3` is the AND of wires `1` and `2`, and wire `4`, the output, is the
XOR of wires `1` and `3`. -/
def circuit : ConventionalCircuit :=
  ⟨2, 1, 2, ![1, 1], ![2, 3], ![(· && ·), xor]⟩

/-- The circuit is a valid XOR–AND circuit. -/
def xorAndCircuit : XorAndCircuit := ⟨⟨circuit, by decide⟩, by decide⟩

/-- A hash on words: the label XORed with copies of the tweak. -/
def toyHash (x t : List Bool) : List Bool := List.zipWith xor x (t ++ t ++ t)

/-- Fixed coins for `k = 2`: a 3-bit offset key, then two 4-bit input zero labels. -/
def coins : List Bool := List.ofFn fun i : Fin 11 => decide (i.val % 3 = 1)

/-- The circuit garbled at `k = 2` on these coins. -/
def garbled : Scheme.Garbled := (HalfGates.scheme toyHash).gb 2 xorAndCircuit coins

/-- The coins have the length that `Gb` samples, so `garbled` is an outcome of `garble`. -/
example :
    garbled ∈ (ProbComp.eval ((HalfGates.scheme toyHash).garble 2 xorAndCircuit)).support :=
  (HalfGates.scheme toyHash).mem_support_eval_garble_iff.mpr ⟨coins, by decide, rfl⟩

/-- The garbled function has 53 bits: 31 for the framed header `(2, 2, 1, 2)`, then the AND gate's
two 3-bit wire numbers, its AND bit and two 4-bit ciphertexts, and the XOR gate's two wire numbers
and its AND bit, with no ciphertext. -/
example : garbled.fn.length = 31 + (3 + 3 + 1 + 4 + 4) + (3 + 3 + 1) := by
  simp only [garbled, HalfGates.scheme, HalfGates.fnWord]
  decide

/-- Garbling, encoding, evaluating and decoding computes `x₀ ⊕ (x₀ ∧ x₁)` on every input. `Ev`
reads the header through `PointPermute.fnDecoder`, whose body is not exposed; its inverse law
`decode_enc` is. -/
example : ∀ x₀ x₁ : Bool,
    (HalfGates.scheme toyHash).decode garbled.decInfo
      ((HalfGates.scheme toyHash).evalGarbled garbled.fn
        ((HalfGates.scheme toyHash).encode garbled.encInfo [x₀, x₁])) =
      some [xor x₀ (x₀ && x₁)] := by
  simp only [garbled, HalfGates.scheme, HalfGates.fnWord, HalfGates.evalWord,
    PointPermute.fnDecoder.decode_enc]
  decide

/-- Every outcome of the randomized garbler, at every `k > 0`, decodes `x₀ ⊕ (x₀ ∧ x₁)`. -/
example (k : ℕ) (hk : 0 < k) (x₀ x₁ : Bool) (g : Scheme.Garbled)
    (hg : g ∈ (ProbComp.eval ((HalfGates.scheme toyHash).garble k xorAndCircuit)).support) :
    (HalfGates.scheme toyHash).decode g.decInfo
      ((HalfGates.scheme toyHash).evalGarbled g.fn
        ((HalfGates.scheme toyHash).encode g.encInfo [x₀, x₁])) =
      some [xor x₀ (x₀ && x₁)] := by
  rw [HalfGates.scheme_correct toyHash k hk xorAndCircuit [x₀, x₁] rfl g hg]
  cases x₀ <;> cases x₁ <;> rfl

end CslibFrontierTests.Crypto.GarblingHalfGates
