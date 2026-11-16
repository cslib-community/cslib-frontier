/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomPermutation
public import CslibFrontier.Crypto.Primitives.PRP.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
import CslibFrontier.Crypto.Primitives.PRP.StrongSwitching

/-!
# The ideal strong-PRP game against the forgetful sampler

A `StrongPRPDistinguisher` asks words on two channels: channel `false` for the permutation and
channel `true` for its inverse. `strongPermCodec m` reads such a request with an `m`-bit word as a
typed `PermQuery (BitString m)`, so that the ideal strong-PRP game `strongPRPIdealGame` becomes the
typed experiment `PRP.strongIdealExperiment` (`strongPRPIdealGame_eq_strongIdealExperiment`). The
bidirectional switching bound of `CslibFrontier.Crypto.Primitives.PRP.StrongSwitching` then
compares the ideal game with its run against `RandomPermutation.forgetfulAnswer`, the lazy sampler
that answers every new query, in either direction, with a fresh uniform block. The forgetful
sampler is neither a random function nor a random permutation; it is the object that
`RandomPermutation.abs_sub_uniformPerm_forgetful_le` compares a uniform permutation with.

The bound is information-theoretic: nothing is claimed about running time.

## Main definitions

* `permQueryEquiv`: a bidirectional permutation query as a channel bit and a point.
* `strongPermCodec`: the codec between word requests on two channels and typed permutation
  queries on `m`-bit blocks.

## Main results

* `strongPermCodec_wordOracle_of_length`, `strongPermCodec_wordOracle_of_length_ne`: the word
  oracle of `strongPermCodec` on requests of the block length and on all others.
* `strongPermCodec_wordOracle_evalPerm`: a permutation table presents `strongRandomPermOracle`.
* `strongPRPIdealGame_eq_strongIdealExperiment`: the ideal strong-PRP game as a typed experiment.
* `advantage_strongPRPIdealGame_forgetful_le`: a distinguisher making at most `Q` calls has
  advantage at most `Q.choose 2 / 2 ^ blockLen n` between the ideal strong-PRP game and its run
  against the forgetful sampler.
-/

public section

namespace Cslib.Crypto

open Probability RandomPermutation

/-- Bidirectional permutation queries as channel-tagged points. -/
def permQueryEquiv (α : Type) : PermQuery α ≃ Bool × α where
  toFun q := match q with
    | .forward x => (false, x)
    | .inverse y => (true, y)
  invFun := PermQuery.ofBoolProd
  left_inv q := by cases q <;> rfl
  right_inv p := by obtain ⟨b, x⟩ := p; cases b <;> rfl

/-- Bidirectional requests on `m`-bit blocks: channel `true` asks for the inverse. -/
def strongPermCodec (m : ℕ) :
    OracleCodec Bool (PermQuery (BitString m)) (PermOracleSpec (BitString m)) :=
  (OracleCodec.withOp Bool (OracleCodec.bitString m)).comap (permQueryEquiv (BitString m))
    (fun _ => Function.Embedding.refl _)

/-- On a request of the block length, the word oracle of `strongPermCodec` asks the typed query
and writes the reply as a word. -/
theorem strongPermCodec_wordOracle_of_length {M : Type → Type} [Monad M] {m : ℕ}
    (oracle : (q : PermQuery (BitString m)) → M (BitString m)) (inverse : Bool)
    {word : List Bool} (hword : word.length = m) :
    (strongPermCodec m).wordOracle oracle (inverse, word) =
      (List.ofFn : BitString m → List Bool) <$>
        oracle (PermQuery.ofBoolProd (inverse, BitString.ofList m word)) := by
  simp [strongPermCodec, OracleCodec.wordOracle, OracleCodec.comap, OracleCodec.withOp,
    OracleCodec.bitString, hword, permQueryEquiv]

/-- On any other request, the word oracle of `strongPermCodec` answers `[]`. -/
theorem strongPermCodec_wordOracle_of_length_ne {M : Type → Type} [Monad M] {m : ℕ}
    (oracle : (q : PermQuery (BitString m)) → M (BitString m)) (inverse : Bool)
    {word : List Bool} (hword : word.length ≠ m) :
    (strongPermCodec m).wordOracle oracle (inverse, word) = pure [] := by
  simp [strongPermCodec, OracleCodec.wordOracle, OracleCodec.comap, OracleCodec.withOp,
    OracleCodec.bitString, hword]

/-- A permutation table presents `strongRandomPermOracle` on the word channels. -/
theorem strongPermCodec_wordOracle_evalPerm {M : Type → Type} [Monad M] [LawfulMonad M] (m : ℕ)
    (π : Equiv.Perm (BitString m)) :
    (strongPermCodec m).wordOracle (fun q => (pure (evalPerm π q) : M (BitString m))) =
      fun request => pure (strongRandomPermOracle m π request) := by
  funext ⟨inverse, word⟩
  by_cases hword : word.length = m
  · rw [strongPermCodec_wordOracle_of_length _ _ hword]
    cases inverse <;> simp [strongRandomPermOracle, hword, PermQuery.ofBoolProd]
  · rw [strongPermCodec_wordOracle_of_length_ne _ _ hword]
    simp [strongRandomPermOracle, hword]

/-- The ideal strong-PRP game is the typed ideal chosen-ciphertext experiment
`PRP.strongIdealExperiment` of the adversary that reads valid words as blocks through
`strongPermCodec (blockLen n)`. -/
theorem strongPRPIdealGame_eq_strongIdealExperiment (blockLen : ℕ → ℕ)
    (adversary : StrongPRPDistinguisher) (n : ℕ) :
    strongPRPIdealGame blockLen adversary n =
      PRP.strongIdealExperiment ((strongPermCodec (blockLen n)).adapt (adversary n [])) := by
  simp only [PRP.strongIdealExperiment, OracleCodec.run_adapt,
    strongPermCodec_wordOracle_evalPerm]
  rfl

/-- **A strong-PRP distinguisher against the forgetful sampler**: a distinguisher making at most
`Q` calls tells the ideal strong-PRP game from its run against the forgetful lazy sampler with
advantage at most `Q.choose 2 / 2 ^ blockLen n`. This is
`PRP.advantage_strongIdealExperiment_forgetful_le` for the adversary reading valid words as blocks
through `strongPermCodec (blockLen n)`. -/
theorem advantage_strongPRPIdealGame_forgetful_le (blockLen : ℕ → ℕ)
    (adversary : StrongPRPDistinguisher) (n Q : ℕ) (hQ : (adversary n []).IsQueryBounded Q) :
    (Game.advantage (ProbComp.eval (strongPRPIdealGame blockLen adversary n))
      ((ProbOracleComp.runWith ((strongPermCodec (blockLen n)).wordOracle forgetfulAnswer)
        (adversary n []) []).map Prod.fst) : ℝ) ≤
      (Q.choose 2 : ℝ) * ((2 : ℝ) ^ blockLen n)⁻¹ := by
  have h := PRP.advantage_strongIdealExperiment_forgetful_le
    ((strongPermCodec (blockLen n)).isQueryBounded_adapt hQ)
  rw [OracleCodec.runWith_adapt] at h
  rw [strongPRPIdealGame_eq_strongIdealExperiment]
  simpa [div_eq_mul_inv] using h

end Cslib.Crypto
