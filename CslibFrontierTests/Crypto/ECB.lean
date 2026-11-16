/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Primitives.BlockCipher.ECB

/-!
# Tests for ECB mode

Checks that ECB decrypts what it encrypts, applies the two-block attack and Theorem 4.1, and shows
that each hypothesis the statements carry is needed. Without `2 ≤ ℓ` or `x ≠ y` the two-block
attack has advantage `0`. Without the restriction to distinct blocks, Theorem 4.1 fails: against
the ECB cipher of a uniformly random permutation, whose block-cipher advantage is `0` for every
adversary, the two-block attack has advantage `1`.
-/

public section

namespace Cslib.Tests.ECB

open Cslib Cslib.Crypto Cslib.Crypto.ECB

/-- ECB decrypts every encryption: `D′(k, E′(k, m)) = m`. -/
example {Key D : Type} (E : Key → Equiv.Perm D) : (Cipher.ecb E).Correct := by
  intro k m c hc
  simp only [Cipher.ecb, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
  simp [Cipher.ecb, hc, List.map_map]

/-- The ECB cipher of a uniformly random permutation: the key is the permutation itself. -/
abbrev idealECB (D : Type) : Cipher (Equiv.Perm D) (List D) (List D) :=
  Cipher.ecb fun π : Equiv.Perm D => π

/-- Against a uniformly random permutation the block-cipher advantage of every adversary is `0`:
the real and the ideal experiments are the same program. -/
theorem prpAdvantage_id_eq_zero {D : Type} [Fintype D] [DecidableEq D] (B : PRF.Adversary D D) :
    PRP.advantage (fun π : Equiv.Perm D => π) B = 0 := by
  simp [PRP.advantage, PRP.realExperiment, PRF.realExperiment, PRP.idealExperiment]

/-- Theorem 4.1 for the ideal block cipher: on sequences of distinct blocks, ECB of a uniformly
random permutation is perfectly secure, for every one-time adversary. -/
example {D σ : Type} [Fintype D] [DecidableEq D] (ℓ : ℕ)
    (A : TwoStage Unit (MessagePair (List D)) (List D) Bool σ) :
    Experiment.advantage
      ((idealECB D).oneTimeExperiment (ProbComp.uniform _) (distinctAdmissible ℓ) A false)
      ((idealECB D).oneTimeExperiment (ProbComp.uniform _) (distinctAdmissible ℓ) A true) = 0 := by
  rw [advantage_eq_two_mul_prpAdvantage, prpAdvantage_id_eq_zero, mul_zero]

/-- The restriction to distinct blocks is needed in Theorem 4.1: on `X^{≤2}` the two-block attack
has advantage `1` against the ECB cipher of a uniformly random permutation of `Fin 2`, while every
block-cipher adversary has advantage `0` against that permutation (`prpAdvantage_id_eq_zero`). -/
example :
    Experiment.advantage
      ((idealECB (Fin 2)).oneTimeExperiment (ProbComp.uniform _) (admissible 2)
        (twoBlockAdversary 0 1) false)
      ((idealECB (Fin 2)).oneTimeExperiment (ProbComp.uniform _) (admissible 2)
        (twoBlockAdversary 0 1) true) = 1 :=
  advantage_twoBlockAdversary _ _ le_rfl (by decide)

/-- `ECB.reduction ℓ A` makes at most `ℓ` queries, here for the two-block attack with `ℓ = 2`. -/
example : (reduction 2 (twoBlockAdversary (0 : Fin 2) 1)).IsQueryBounded 2 :=
  isQueryBounded_reduction 2 _

/-- `2 ≤ ℓ` is needed: with `ℓ = 1` the two-block pair is not admissible and the attack has
advantage `0`. -/
example {Key : Type} (E : Key → Equiv.Perm (Fin 2)) (sampleKey : ProbComp Key) :
    Experiment.advantage
      ((Cipher.ecb E).oneTimeExperiment sampleKey (admissible 1) (twoBlockAdversary 0 1) false)
      ((Cipher.ecb E).oneTimeExperiment sampleKey (admissible 1) (twoBlockAdversary 0 1) true) =
      0 := by
  simp [Cipher.oneTimeExperiment, lrExperiment, twoBlockAdversary, admissible]

/-- `x ≠ y` is needed: with `x = y` the two messages are equal and the attack has advantage `0`. -/
example {Key : Type} (E : Key → Equiv.Perm (Fin 2)) (sampleKey : ProbComp Key) :
    Experiment.advantage
      ((Cipher.ecb E).oneTimeExperiment sampleKey (admissible 2) (twoBlockAdversary 0 0) false)
      ((Cipher.ecb E).oneTimeExperiment sampleKey (admissible 2) (twoBlockAdversary 0 0) true) =
      0 := by
  simp [Cipher.oneTimeExperiment, lrExperiment, twoBlockAdversary, MessagePair.select]

end Cslib.Tests.ECB
