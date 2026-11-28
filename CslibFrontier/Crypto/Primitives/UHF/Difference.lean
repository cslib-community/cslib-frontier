/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.ZMod
public import CslibFrontier.Crypto.Primitives.UHF.Computational
import CslibFrontier.Computability.Probabilistic.PPT.Capture

/-!
# Computational difference unpredictability

An adversary receives the unary security parameter and the public setup, then submits two
messages and an encoded digest difference. The challenger keeps the uniform hash key private.
Checking the encoded difference allows the digest group to vary with the public setup while the
adversary's output encoding stays fixed.

## Main definitions

* `Cslib.Crypto.UHF.encDifferenceGuess`: a framed collision guess followed by the prediction.
* `Cslib.Crypto.UHF.differenceGame`: Attack Game 7.3 for encoded differences.
* `Cslib.Crypto.UHF.IsComputationalDUF`: negligible success for every uniform strict PPT
  difference predictor.

## Main results

* `Cslib.Crypto.UHF.IsComputationalDUF.isComputationalUHF_of_zero_polyTime`: predicting an
  efficiently encoded zero transfers difference security to collision security.
* `Cslib.Crypto.UHF.IsComputationalDUF.isComputationalUHF_zmod`: the canonical binary encoding
  of zero works for every cyclic modulus, including when the setup chooses it.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 7.4, Attack Game 7.3, Definition 7.5 and Remark 7.3, printed pp. 268–269.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability Turing.MultiTapeTM

variable {D M T : Type} {K Y : D → Type}

/-- Frame the encoded pair of messages, then write the encoded difference. -/
enc_structure encDifferenceGuess (encM : M ↪ List Bool) (encT : T ↪ List Bool) :
    DifferenceGuess M T where
  toCollisionGuess : (encCollisionGuess encM),
  difference : encT

variable [∀ d, Fintype (K d)] [∀ d, Nonempty (K d)] [DecidableEq M] [∀ d, AddGroup (Y d)]

/-- Attack Game 7.3 ([BonehShoup2023], v0.6, §7.4, p. 268) with public setup. Two distinct valid
messages win when the submitted bits encode the second digest minus the first. The key is uniform
in `K d` and private. Digest groups can vary with setup. Remark 7.3 allows group-valued digests. -/
@[expose] noncomputable def differenceGame (setup : ℕ → ProbComp D) (valid : ℕ → D → M → Bool)
    (H : ℕ → (d : D) → K d → M → Y d) (encY : ∀ d, Y d ↪ List Bool)
    (A : ℕ × D → ProbComp (DifferenceGuess M (List Bool))) (n : ℕ) : Game :=
  Game.withSetup (ProbComp.eval (setup n)) fun d => do
    let guess ← A (n, d)
    let k ← ProbComp.uniform (K d)
    return decide (guess.first ≠ guess.second ∧ valid n d guess.first = true ∧
      valid n d guess.second = true ∧
      encY d (H n d k guess.second - H n d k guess.first) = guess.difference)

/-- Computational DUF security ([BonehShoup2023], Definition 7.5 and Remark 7.3, printed p. 269)
against uniform strict PPT adversaries who receive the framed unary parameter and public setup.
Predictions are digest words. Malformed words and invalid or repeated messages lose. Setup may
have arbitrary runtime in this security predicate. Applications supply the hash family's
recognition, sampling and evaluation requirements from Definition 7.4. -/
@[expose] def IsComputationalDUF (encD : D ↪ List Bool) (encM : M ↪ List Bool)
    (setup : ℕ → ProbComp D) (valid : ℕ → D → M → Bool)
    (H : ℕ → (d : D) → K d → M → Y d) (encY : ∀ d, Y d ↪ List Bool) : Prop :=
  Game.Indistinguishable (differenceGame setup valid H encY) (fun _ _ => PMF.pure false)
    (IsPPTOn (encPair encUnary encD) (encDifferenceGuess encM encBits))

open ComputableInPolyTime in
/-- If the encoded zero is efficiently available from setup, a collision guess gives a
difference guess with the same success probability. This transports computational DUF security
across arbitrary digest encodings using the zero prediction of [BonehShoup2023], p. 269. -/
theorem IsComputationalDUF.isComputationalUHF_of_zero_polyTime [∀ d, DecidableEq (Y d)]
    {encD : D ↪ List Bool} {encM : M ↪ List Bool} {setup : ℕ → ProbComp D}
    {valid : ℕ → D → M → Bool} {H : ℕ → (d : D) → K d → M → Y d}
    {encY : ∀ d, Y d ↪ List Bool} (hH : IsComputationalDUF encD encM setup valid H encY)
    (hzero : ComputableInPolyTime (fun d => encY d 0) encD encBits) :
    IsComputationalUHF encD encM setup valid H := by
  apply Game.Indistinguishable.of_negligible_succProbability
  intro A hA
  let B : ℕ × D → ProbComp (DifferenceGuess M (List Bool)) :=
    fun p => (fun guess => DifferenceGuess.mk guess (encY p.2 0)) <$> A p
  let encInput := encPair encUnary encD
  let encGuess := encCollisionGuess encM
  have hD := (snd encUnary encD).comp (fst encInput encGuess)
  have hB : IsPPTOn encInput (encDifferenceGuess encM encBits) B :=
    hA.map_with (encDifferenceGuess_mk_polyTime encM encBits
      (snd encInput encGuess) (hzero.comp hD))
  have heq (n : ℕ) : differenceGame setup valid H encY B n = collisionGame setup valid H A n := by
    have hdiff (d : D) (k : K d) (guess : CollisionGuess M) :
        encY d (H n d k guess.second - H n d k guess.first) = encY d 0 ↔
          H n d k guess.first = H n d k guess.second := by
      rw [Function.Embedding.apply_eq_iff_eq, sub_eq_zero, eq_comm]
    simp only [differenceGame, collisionGame, Game.withSetup, B, ProbComp.eval_bind,
      ProbComp.eval_map, PMF.bind_map, Function.comp_def, hdiff]
  simpa only [heq] using hH.negligible_succProbability B hB

/-- Computational difference unpredictability over canonically encoded residues implies
computational universal hashing. This is the asymptotic form of the zero-prediction reduction in
[BonehShoup2023], v0.6, §7.4, p. 269. The certified predictor writes the encoding of integer zero,
which is the same at every modulus. -/
theorem IsComputationalDUF.isComputationalUHF_zmod {encD : D ↪ List Bool} {encM : M ↪ List Bool}
    {setup : ℕ → ProbComp D} {valid : ℕ → D → M → Bool} {modulus : D → ℕ}
    {H : ℕ → (d : D) → K d → M → ZMod (modulus d)}
    (hH : IsComputationalDUF encD encM setup valid H (fun d => encZMod (modulus d))) :
    IsComputationalUHF encD encM setup valid H := by
  refine hH.isComputationalUHF_of_zero_polyTime
    ((ComputableInPolyTime.const (encOut := encBits) (encIntBin (0 : ℤ))).of_enc_eq fun d => ?_)
  simp [encZMod]

end Cslib.Crypto.UHF
