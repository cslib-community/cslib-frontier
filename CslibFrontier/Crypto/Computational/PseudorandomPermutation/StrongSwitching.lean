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
channel `true` for its inverse. `strongBitStringCodec m` reads such a request with an `m`-bit word
as a typed `PermQuery (BitString m)` (`strongPermCodec` in `Crypto.Computational.LubyRackoff` reads
it as a query on pairs of halves), so that the ideal strong-PRP game `strongPRPIdealGame` becomes
the typed experiment `PRP.strongIdealExperiment` (`strongPRPIdealGame_eq_strongIdealExperiment`).
The bidirectional switching bound of `CslibFrontier.Crypto.Primitives.PRP.StrongSwitching` then
compares the ideal game with its run against `RandomPermutation.forgetfulAnswer`, the lazy sampler
that keeps the pairs `(x, y)` it has answered, answers `.forward x` or `.inverse y` from a recorded
pair when there is one, and otherwise with a fresh uniform block, which may repeat a recorded one.
The forgetful sampler is neither a random function nor a random permutation; it is the object that
`RandomPermutation.abs_sub_uniformPerm_forgetful_le` compares a uniform permutation with.

The bound is information-theoretic: nothing is claimed about running time.

## Main definitions

* `strongBitStringCodec`: the codec between word requests on two channels and typed permutation
  queries on `m`-bit blocks.

## Main results

* `strongBitStringCodec_wordOracle_evalPerm`: a permutation table presents `strongRandomPermOracle`.
* `advantage_strongPRPIdealGame_forgetful_le`: a distinguisher making at most `Q` calls has
  advantage at most `Q.choose 2 / 2 ^ blockLen n` between the ideal strong-PRP game and its run
  against the forgetful sampler.
-/

public section

namespace Cslib.Crypto

open Probability RandomPermutation

/-- Bidirectional requests on `m`-bit blocks: channel `true` asks for the inverse. -/
def strongBitStringCodec (m : ℕ) :
    OracleCodec Bool (PermQuery (BitString m)) (PermOracleSpec (BitString m)) :=
  (OracleCodec.withOp Bool (OracleCodec.bitString m)).comap (PermQuery.equivBoolProd (BitString m))
    (fun _ => Function.Embedding.refl _)

/-- On a request of the block length, the word oracle of `strongBitStringCodec` asks the typed query
and writes the reply as a word. -/
theorem strongBitStringCodec_wordOracle_of_length {M : Type → Type} [Monad M] {m : ℕ}
    (oracle : (q : PermQuery (BitString m)) → M (BitString m)) (inverse : Bool)
    {word : List Bool} (hword : word.length = m) :
    (strongBitStringCodec m).wordOracle oracle (inverse, word) =
      (List.ofFn : BitString m → List Bool) <$>
        oracle (PermQuery.ofBoolProd (inverse, BitString.ofList m word)) := by
  simp [strongBitStringCodec, OracleCodec.wordOracle, OracleCodec.comap, OracleCodec.withOp,
    OracleCodec.bitString, hword]

/-- On any other request, the word oracle of `strongBitStringCodec` answers `[]`. -/
theorem strongBitStringCodec_wordOracle_of_length_ne {M : Type → Type} [Monad M] {m : ℕ}
    (oracle : (q : PermQuery (BitString m)) → M (BitString m)) (inverse : Bool)
    {word : List Bool} (hword : word.length ≠ m) :
    (strongBitStringCodec m).wordOracle oracle (inverse, word) = pure [] := by
  simp [strongBitStringCodec, OracleCodec.wordOracle, OracleCodec.comap, OracleCodec.withOp,
    OracleCodec.bitString, hword]

/-- A permutation table presents `strongRandomPermOracle` on the word channels. -/
theorem strongBitStringCodec_wordOracle_evalPerm {M : Type → Type} [Monad M] [LawfulMonad M] (m : ℕ)
    (π : Equiv.Perm (BitString m)) :
    (strongBitStringCodec m).wordOracle (fun q => (pure (evalPerm π q) : M (BitString m))) =
      fun request => pure (strongRandomPermOracle m π request) := by
  funext ⟨inverse, word⟩
  by_cases hword : word.length = m
  · rw [strongBitStringCodec_wordOracle_of_length _ _ hword]
    cases inverse <;> simp [strongRandomPermOracle, hword, PermQuery.ofBoolProd]
  · rw [strongBitStringCodec_wordOracle_of_length_ne _ _ hword]
    simp [strongRandomPermOracle, hword]

/-- The ideal strong-PRP game is the typed ideal chosen-ciphertext experiment
`PRP.strongIdealExperiment` of the adversary that reads valid words as blocks through
`strongBitStringCodec (blockLen n)`. -/
theorem strongPRPIdealGame_eq_strongIdealExperiment (blockLen : ℕ → ℕ)
    (adversary : StrongPRPDistinguisher) (n : ℕ) :
    strongPRPIdealGame blockLen adversary n =
      PRP.strongIdealExperiment ((strongBitStringCodec (blockLen n)).adapt (adversary n [])) := by
  simp only [PRP.strongIdealExperiment, OracleCodec.run_adapt,
    strongBitStringCodec_wordOracle_evalPerm]
  rfl

/-- **A strong-PRP distinguisher against the forgetful sampler**: a distinguisher making at most
`Q` calls tells the ideal strong-PRP game from its run against the forgetful lazy sampler with
advantage at most `Q.choose 2 / 2 ^ blockLen n`. This is
`PRP.advantage_strongIdealExperiment_forgetful_le` for the adversary reading valid words as blocks
through `strongBitStringCodec (blockLen n)`. -/
theorem advantage_strongPRPIdealGame_forgetful_le (blockLen : ℕ → ℕ)
    (adversary : StrongPRPDistinguisher) (n Q : ℕ) (hQ : (adversary n []).IsQueryBounded Q) :
    (Game.advantage (ProbComp.eval (strongPRPIdealGame blockLen adversary n))
      ((ProbOracleComp.runWith ((strongBitStringCodec (blockLen n)).wordOracle forgetfulAnswer)
        (adversary n []) []).map Prod.fst) : ℝ) ≤
      (Q.choose 2 : ℝ) * ((2 : ℝ) ^ blockLen n)⁻¹ := by
  have h := PRP.advantage_strongIdealExperiment_forgetful_le
    ((strongBitStringCodec (blockLen n)).isQueryBounded_adapt hQ)
  rw [OracleCodec.runWith_adapt] at h
  rw [strongPRPIdealGame_eq_strongIdealExperiment]
  simpa [div_eq_mul_inv] using h

end Cslib.Crypto
