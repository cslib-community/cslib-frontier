/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SchnorrGuessing
import CslibFrontier.Crypto.Protocols.SigmaProtocol.Guessing
import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrIdentification
import CslibFrontier.Tactic.Negligible

/-!
# Tests for Sigma-protocol and Schnorr guessing attacks

Exercises the typed Sigma-protocol guessing bound (`SigmaProtocol.Guessing`) on concrete
instances (including a statement without a witness) and the word-level Schnorr guessing
impersonator (`SchnorrGuessing`) on constant-length `k n = 1` challenges.
-/

namespace CslibFrontierTests.Crypto.SigmaGuessing

open Cslib.Crypto
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.SigmaProtocol
open scoped NNReal

section Typed

variable {q : ℕ} [NeZero q] {C G : Type} [Fintype C] [Nonempty C]
  [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G]

-- Checks the typed special-HVZK guessing bound on Schnorr for arbitrary base `g` and
-- challenge set `C`.
example (ι : C ↪ ZMod q) (g : G) :
    (Fintype.card C : ℝ≥0)⁻¹ ≤ Game.succProbability ((schnorr ι g).directAttack (schnorrKeyGen g)
      (guessingImpersonator
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod q) G g) id ι))) :=
  schnorr_specialHVZK.inv_card_le_succProbability_directAttack _

-- Probe: checks that no witness is needed in `keyGen` (`PMF.pure (0, 1)` over `ZMod 5` with
-- base `0`).
example :
    (Fintype.card (ZMod 5) : ℝ≥0)⁻¹ ≤ Game.succProbability
      ((schnorr (Function.Embedding.refl (ZMod 5)) (0 : ZMod 5)).directAttack (PMF.pure (0, 1))
        (guessingImpersonator (linearSimulate
          (fun _ => LinearMap.toSpanSingleton (ZMod 5) (ZMod 5) 0) id
          (Function.Embedding.refl (ZMod 5))))) :=
  schnorr_specialHVZK.inv_card_le_succProbability_directAttack _

end Typed

section WordLevel

open Cslib.Probability

variable {F : PrimeOrderGroupFamily}

-- Checks the word-level guessing probability bound at one-bit challenges (`k n = 1`).
example (setup : ℕ → PMF F.Desc) (n : ℕ) :
    (1 : ℝ≥0) / 2 ≤ Game.succProbability
      (F.schnorrDirectGame setup (fun _ => 1) (F.schnorrGuessingImpersonator fun _ => 1) n) := by
  simpa [pow_one] using PrimeOrderGroupFamily.inv_two_pow_le_succProbability_schnorrDirectGame
    (F := F) setup (fun _ => 1) (fun _ => 1) n le_rfl

-- Checks the zero-bit prepared challenge bound (`m n = 0 ≤ k n`) used in the converse theorem.
example (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ) (n : ℕ) :
    (1 : ℝ≥0) / 2 ^ k n ≤ Game.succProbability
      (F.schnorrDirectGame setup k (F.schnorrGuessingImpersonator fun _ => 0) n) :=
  PrimeOrderGroupFamily.inv_two_pow_le_succProbability_schnorrDirectGame
    (F := F) setup k (fun _ => 0) n (Nat.zero_le _)

-- Probe: checks that `schnorrGuessingImpersonator` is uniform strict PPT for constant `k n = 1`.
example : (F.schnorrGuessingImpersonator fun _ => 1).IsPPT :=
  PrimeOrderGroupFamily.isPPT_schnorrGuessingImpersonator (by fun_prop)

-- Probe: checks necessity of `hchallenge` in `negligible_schnorrDirectGame` at `k n = 1` inside
-- the uniform strict-PPT class.
example (setup : ℕ → PMF F.Desc) :
    ¬ ∀ A : F.SchnorrImpersonator, A.IsPPT →
      Negligible fun n => Game.succProbability (F.schnorrDirectGame setup (fun _ => 1) A n) :=
  fun h => not_negligible_const (by norm_num)
    (PrimeOrderGroupFamily.negligible_inv_two_pow_of_negligible_schnorrDirectGame setup h)

end WordLevel

end CslibFrontierTests.Crypto.SigmaGuessing
