/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Reduction
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for Free-XOR garbling as a scheme family

A client of `CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Scheme`,
`CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Efficient`,
`CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Simulator` and
`CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Reduction` under module encapsulation.

We build two multi-gate circuits combining AND, OR and XOR gates with the same topology and XOR
gate positions, verify that `phiXor` identifies them while hiding non-XOR gate truth tables, check
garbling, evaluation and decoding across all eight inputs, check the simulator's efficiency,
layout and decoding, and instantiate the reduction legality and oracle-PPT certificates on a
stateful strict PPT adversary.
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

/-- The query of the stateful `prv.sim` adversary: `validCircuit₁` on `[true, false, true]`. -/
private def query : Query ValidCircuit := ⟨validCircuit₁, [true, false, true]⟩

/-- Stateful guess function: reads the saved bit and the first decoding bit, or `false` on `⊥`. -/
private def advGuess (state : Bool) (view : Option PrvView) : Bool :=
  view.elim false fun v => state && v.decInfo.getD 0 false

/-- A stateful uniform strict PPT `prv.sim` adversary against Free-XOR garbling. -/
private def adversary : ℕ → PrvSimAdversary ValidCircuit Bool := fun _ =>
  ⟨fun () => pure (query, true), fun state view => pure (advGuess state view)⟩

open Turing.MultiTapeTM in
/-- The adversary is uniform strict PPT. -/
private theorem adversary_isPPT : TwoStage.IsPPT encUnit (encQuery ValidCircuit encValidCircuit)
    (encOption encPrvView) encBool encBool adversary where
  choose := ComputableInPolyTime.isPPTOn (ComputableInPolyTime.const _)
  guess := ComputableInPolyTime.isPPTOn
    (f := fun ((_, state, view) : ℕ × Bool × Option PrvView) => advGuess state view)
    (by polytime [advGuess])

/-- The reduction for `adversary` is uniform strict oracle PPT. -/
example : IsOraclePPT Turing.MultiTapeTM.encBool (FreeXOR.prvSimReduction toyHash adversary) :=
  FreeXOR.isOraclePPT_prvSimReduction toyHash_polyTime adversary_isPPT

/-- The reduction asks each tweak at most once at every security level. -/
example (k : ℕ) :
    CCR.IsTweakUnique ((CCR.codec k).adapt (FreeXOR.prvSimReduction toyHash adversary k [])) :=
  FreeXOR.isTweakUnique_prvSimReduction toyHash adversary k

/-- At level `k = 5`, `prvSimReduction` enters the guarded branch and issues `16` oracle
requests (`8` for each of `validCircuit₁`'s two non-XOR gates). -/
example {State : Type} (oracle : Unit × List Bool → StateT State PMF (List Bool)) (s : State) :
    ∃ result s' transcript,
      (result, s', transcript) ∈
        (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
          (FreeXOR.prvSimReduction toyHash adversary 5 []) (s, [])).support ∧
      transcript.length = 16 := by
  obtain ⟨⟨result, s', transcript⟩, hmem⟩ := PMF.support_nonempty
    (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
      (FreeXOR.prvSimReduction toyHash adversary 5 []) (s, []))
  obtain ⟨q, st, hq, hlen⟩ :=
    FreeXOR.exists_of_mem_support_runWith_prvSimReduction toyHash adversary 5 oracle hmem
  simp only [adversary, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hq
  obtain ⟨rfl, -⟩ := hq
  refine ⟨result, s', transcript, hmem, ?_⟩
  rw [hlen]
  decide

end CslibFrontierTests.Crypto.GarblingFreeXORFamily
