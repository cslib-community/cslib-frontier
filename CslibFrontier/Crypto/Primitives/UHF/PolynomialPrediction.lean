/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.ZMod
public import CslibFrontier.Crypto.Primitives.UHF.PairwiseUnpredictability
public import CslibFrontier.Probability.HashFamily.Polynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Languages.Probabilistic.Semantics

/-!
# Predicting the variable-length polynomial hash

In [BonehShoup2023], Exercise 7.29, the adversary queries the empty message. Its `Hxpoly`
digest is the key, so squaring it gives the digest of the singleton-zero message. The same
argument works over every finite field. For prime fields the two stages have polynomial-time
certificates on binary residues.

## Main results

* `eval_predictionExperiment_xpolyHash`: the explicit adversary wins with probability one.
* `isPPT_xpolyPrediction`: the two deterministic stages are polynomial time over prime fields.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

variable {M Y : Type}

/-- Encode a prediction by framing its message followed by its digest. -/
enc_structure encPredictionGuess (encM : M ↪ List Bool)
    (encY : Y ↪ List Bool) : PredictionGuess M Y where
  message : encM,
  digest : encY

/-- A bounded block list has the same encoding as the underlying framed list of binary residues. -/
abbrev encXpolyMessage (p ℓ : ℕ) : {m : List (ZMod p) // m.length ≤ ℓ} ↪ List Bool :=
  (Function.Embedding.subtype _).trans (encList (encZMod p))

/-- Query the empty message and predict that the digest of `[0]` is the revealed digest squared. -/
@[expose] def xpolyPrediction {F : Type} [Field F] {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    PredictionAdversary {m : List F // m.length ≤ ℓ} F Unit where
  choose _ := pure (⟨[], by simp⟩, ())
  guess _ t := pure ⟨⟨[0], hℓ⟩, t * t⟩

/-- **Exercise 7.29** ([BonehShoup2023], v0.6, printed p. 285).
When one-block messages are allowed, the adversary wins Attack Game 7.5 against `Hxpoly`
with probability one. The same program works over any finite field with a uniform key. -/
theorem eval_predictionExperiment_xpolyHash {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ProbComp.eval (predictionExperiment
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m.val)
      (xpolyPrediction hℓ)) true = 1 := by
  have hne : (⟨[0], hℓ⟩ : {m : List F // m.length ≤ ℓ}) ≠ ⟨[], by simp⟩ := by
    simp
  simp [predictionExperiment, xpolyPrediction, xpolyHash, polyHash, hne, ENNReal.mul_inv_cancel]

private theorem squareZMod_polyTime (p : ℕ) [NeZero p] :
    ComputableInPolyTime (fun t : ZMod p => t * t) (encZMod p) (encZMod p) := by
  have hval : ComputableInPolyTime (fun t : ZMod p => (t.val : ℤ)) (encZMod p) encIntBin :=
    .of_eq fun t => by simp only [encZMod, Function.Embedding.coeFn_mk, ZMod.cast_eq_val]
  have hsq := ComputableInPolyTime.intBin_mul' hval hval
  have hmod := ComputableInPolyTime.intBin_emodNat' hsq (.const p)
  refine (ComputableInPolyTime.intBin_natCast.comp hmod).of_enc_eq fun t => ?_
  simp only [encZMod, Function.Embedding.coeFn_mk, ZMod.cast_eq_val, Function.comp_apply,
    ZMod.val_mul, ← Int.natCast_mul, ← Int.natCast_emod, Int.toNat_natCast]

/-- The winning adversary's actual deterministic choice and guess stages are polynomial time
for each prime modulus. The guess stage uses binary multiplication and remainder. -/
theorem isPPT_xpolyPrediction {p ℓ : ℕ} [Fact p.Prime] (hℓ : 1 ≤ ℓ) :
    TwoStage.IsPPT encUnit (encXpolyMessage p ℓ) (encZMod p)
      (encPredictionGuess (encXpolyMessage p ℓ) (encZMod p)) encUnit
      (fun _ => xpolyPrediction hℓ) := by
  refine ⟨?_, ?_⟩
  · let empty : {m : List (ZMod p) // m.length ≤ ℓ} := ⟨[], by simp⟩
    exact (ComputableInPolyTime.const (empty, ())).isPPTOn
  · have htag := (ComputableInPolyTime.snd encUnit (encZMod p)).comp
          (ComputableInPolyTime.snd encUnary (encPair encUnit (encZMod p)))
    exact (encPredictionGuess_mk_polyTime (encXpolyMessage p ℓ) (encZMod p)
      (ComputableInPolyTime.const ⟨[0], hℓ⟩)
      ((squareZMod_polyTime p).comp htag)).isPPTOn

end Cslib.Crypto.UHF
