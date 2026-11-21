/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Simulator
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for Free-XOR garbling as a scheme family

A client of `CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Scheme`,
`CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Efficient` and
`CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Simulator` under module encapsulation.

We build two multi-gate circuits combining AND, OR and XOR gates with the same topology and XOR
gate positions, verify that `phiXor` identifies them while hiding non-XOR gate truth tables, check
garbling, evaluation and decoding across all eight inputs, and check the simulator's efficiency,
layout and decoding.
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

/-- `phiXor` hides non-XOR gate truth tables while preserving topology and XOR flags. -/
example : FreeXOR.phiXor.phi validCircuit₁ = FreeXOR.phiXor.phi validCircuit₂ := by
  simp only [FreeXOR.phiXor, FreeXOR.XorTopology.mk.injEq, phiTopo, validCircuit₁, validCircuit₂,
    circuit₁, circuit₂, ConventionalCircuit.topo, true_and, FreeXOR.isXorGate,
    ← FreeXOR.isXorTable_eq]
  decide

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

/-- The toy hash is computed in polynomial time. -/
theorem toyHash_polyTime : Turing.MultiTapeTM.ComputableInPolyTime
    (fun p : List Bool × List Bool => toyHash p.1 p.2)
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    Turing.MultiTapeTM.encBits := by
  polytime [toyHash]

/-- Free-XOR garbling with the toy hash is efficient. -/
example : (FreeXOR.scheme toyHash).IsEfficient encValidCircuit :=
  FreeXOR.scheme_isEfficient toyHash_polyTime

/-- Any circular correlation robust hash yields an efficient Free-XOR scheme. -/
example {hash : List Bool → List Bool → List Bool} (h : CircularCorrelationRobust hash) :
    (FreeXOR.scheme hash).IsEfficient encValidCircuit :=
  FreeXOR.scheme_isEfficient h.polyTime

/-- The simulator with the toy hash is PPT. -/
example : IsPPTOn (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits FreeXOR.encXorTopology)) encPrvView
    (fun (k, y, t) => FreeXOR.simWord toyHash k y t) :=
  FreeXOR.isPPTOn_simWord toyHash_polyTime

/-- At `k = 2`, the simulator samples `(3 + 4 + 4 · 2) · 4 = 60` coin bits for `validCircuit₁`. -/
example : FreeXOR.simCoinLen 2 (FreeXOR.phiXor.phi validCircuit₁) = 60 := by decide

/-- Fixed simulator coins for `k = 2`. -/
def simCoins : List Bool := List.ofFn fun i : Fin 60 => decide (i.val % 5 = 2)

/-- The simulated view on `simCoins` for output `[true, false]`. -/
def simView : PrvView :=
  FreeXOR.simViewWord toyHash 2 [true, false] (FreeXOR.phiXor.phi validCircuit₁) simCoins

/-- The simulated garbled function matches the real garbled function bit length. -/
example : simView.fn.length = garbled₁.fn.length := by
  simp only [simView, FreeXOR.simViewWord, garbled₁, FreeXOR.scheme, FreeXOR.fnWord]
  decide

/-- The simulated view decodes to the output `[true, false]`. -/
example : PointPermute.decodeWord simView.decInfo
    (FreeXOR.evalWord toyHash simView.fn simView.input) = some [true, false] := by
  simp only [simView, FreeXOR.simViewWord, FreeXOR.evalWord, PointPermute.fnDecoder.decode_enc]
  decide

end CslibFrontierTests.Crypto.GarblingFreeXORFamily
