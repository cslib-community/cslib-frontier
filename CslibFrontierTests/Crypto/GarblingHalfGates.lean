/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Scheme
import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Simulator
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for half-gates garbling as a garbling scheme

A client of `CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Conventional`,
`CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Scheme`,
`CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Efficient` and
`CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Simulator` under module encapsulation.

The circuit `x₀ ⊕ (x₀ ∧ x₁)`, one AND gate and one XOR gate, is an XOR–AND circuit. It is garbled
by `HalfGates.scheme` at `k = 2`, with a hash that XORs the label with copies of the tweak and
with fixed coins. The garbled function carries two ciphertexts for the AND gate and none for the
XOR gate. Encoding, evaluating and decoding gives `x₀ ⊕ (x₀ ∧ x₁)` on all four inputs, by
computation, and `scheme_correct` gives the same answer for every outcome of the randomized
garbler at every `k > 0`.

The toy hash is computed in polynomial time, so the scheme is efficient (`scheme_isEfficient`) and
its simulator is PPT (`isPPTOn_simWord`); the hash of a circular correlation robust family is
too. The simulator samples `(2 + 2 · 1) · 4 = 16` coins for the circuit at `k = 2`; on fixed coins
its garbled function has the length of the real one, and the view decodes to the output it was
given, by computation.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GarblingHalfGates

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling Cslib.Probability

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

/-- The toy hash is computed in polynomial time. -/
theorem toyHash_polyTime : Turing.MultiTapeTM.ComputableInPolyTime
    (fun p : List Bool × List Bool => toyHash p.1 p.2)
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    Turing.MultiTapeTM.encBits := by
  polytime [toyHash]

/-- Half-gates garbling with the toy hash is efficient. -/
example : (HalfGates.scheme toyHash).IsEfficient encXorAndCircuit :=
  HalfGates.scheme_isEfficient toyHash_polyTime

/-- The evaluation premise of circular correlation robustness is the premise of efficiency. -/
example {hash : List Bool → List Bool → List Bool} (h : CircularCorrelationRobust hash) :
    (HalfGates.scheme hash).IsEfficient encXorAndCircuit :=
  HalfGates.scheme_isEfficient h.polyTime

/-- The simulator with the toy hash is PPT. -/
example : IsPPTOn (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits encXorAndCircuit)) encPrvView
    (fun (k, y, f) => HalfGates.simWord toyHash k y f) :=
  HalfGates.isPPTOn_simWord toyHash_polyTime

/-- The simulator samples two input labels and two labels for the AND gate, at `k = 2`. -/
example : HalfGates.simCoinLen 2 circuit = 16 := by decide

/-- Fixed coins for the simulator at `k = 2`. -/
def simCoins : List Bool := List.ofFn fun i : Fin 16 => decide (i.val % 3 = 2)

/-- The simulated view of the output `[true]` on these coins. -/
def simView : PrvView := HalfGates.simViewWord toyHash 2 [true] circuit simCoins

/-- The simulated garbled function has the layout of the real one: 53 bits. -/
example : simView.fn.length = garbled.fn.length := by
  simp only [simView, HalfGates.simViewWord, garbled, HalfGates.scheme, HalfGates.fnWord]
  decide

/-- The simulated view decodes to the output it was given, by computation. -/
example : PointPermute.decodeWord simView.decInfo
    (HalfGates.evalWord toyHash simView.fn simView.input) = some [true] := by
  simp only [simView, HalfGates.simViewWord, HalfGates.evalWord, PointPermute.fnDecoder.decode_enc]
  decide

end CslibFrontierTests.Crypto.GarblingHalfGates
