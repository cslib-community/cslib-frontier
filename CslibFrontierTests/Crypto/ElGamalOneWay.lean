/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiffieHellman.Static
public import CslibFrontier.Crypto.Computational.ElGamal
public import CslibFrontier.Crypto.Computational.ElGamal.OneWay
import CslibFrontier.Tactic.PPT

/-!
# Tests for the one-wayness of multiplicative ElGamal

Checks of `CslibFrontier/Crypto/Computational/ElGamal/OneWay.lean` as an ordinary `module` client:
the book's literal draws `x ←R 𝔾` and `y ←R 𝔾` give the same equality when `g` generates the
group; at a member of a group family the scheme's encryption and decryption are the library's
`elGamalEncrypt` and `elGamalDecrypt`, and decryption is the decryption oracle of the static
Diffie–Hellman module; and `CDH.elGamal_oneWay` applies to a named adversary with its efficiency
proof.
-/

public section

namespace CslibFrontierTests.Crypto.ElGamalOneWay

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols Turing.MultiTapeTM

/-- The book's literal form: when `γ ↦ γ • g` is a bijection, drawing the message and `ℬ`'s `y`
uniformly from the group gives the same one-way and CDH laws. -/
example {G : Type} [AddCommGroup G] [Fintype G] [Nonempty G] [DecidableEq G] (q : ℕ) [NeZero q]
    [Module (ZMod q) G] (g : G) (hg : Function.Bijective fun c : ZMod q => c • g)
    (A : G → G × G → ProbComp G) :
    ProbComp.eval (PKE.owExperiment (elGamalExplicitCoinPKE q g).toPKE ($ᵗ G) A) =
      ProbComp.eval (cdhExperiment q g (elGamalOWToCDH ($ᵗ G) A)) := by
  have hS : ProbComp.eval ((fun γ : ZMod q => γ • g) <$> ($ᵗ ZMod q)) = ProbComp.eval ($ᵗ G) := by
    rw [ProbComp.eval_map, ProbComp.eval_uniform, ProbComp.eval_uniform, PMF.map,
      ← PMF.bind_pure (PMF.uniformOfFintype G)]
    exact uniformOfFintype_bind_smul hg PMF.pure
  have h1 (S S' : ProbComp G) (h : ProbComp.eval S = ProbComp.eval S') :
      ProbComp.eval (PKE.owExperiment (elGamalExplicitCoinPKE q g).toPKE S A) =
        ProbComp.eval (PKE.owExperiment (elGamalExplicitCoinPKE q g).toPKE S' A) := by
    simp only [PKE.owExperiment, ProbComp.eval_bind, h]
  have h2 (S S' : ProbComp G) (h : ProbComp.eval S = ProbComp.eval S') :
      ProbComp.eval (cdhExperiment q g (elGamalOWToCDH S A)) =
        ProbComp.eval (cdhExperiment q g (elGamalOWToCDH S' A)) := by
    simp only [cdhExperiment, elGamalOWToCDH, ProbComp.eval_bind, h]
  rw [← h1 _ _ hS, ← h2 _ _ hS]
  exact owExperiment_elGamalExplicitCoinPKE_eq_cdhExperiment q g A

/-- At a member of a group family, encryption is the library's `elGamalEncrypt`. -/
example (F : PrimeOrderGroupFamily) (d : F.Desc) (u x : F.Carrier d) (β : ZMod (F.order d)) :
    (elGamalExplicitCoinPKE (F.order d) (F.generator d)).encDet u x β =
      F.elGamalEncrypt d u x β := rfl

/-- At a member of a group family, decryption is the library's `elGamalDecrypt`. -/
example (F : PrimeOrderGroupFamily) (d : F.Desc) (α : ZMod (F.order d))
    (ct : F.Carrier d × F.Carrier d) :
    (elGamalExplicitCoinPKE (F.order d) (F.generator d)).dec α ct =
      some (F.elGamalDecrypt d α ct) := rfl

/-- Decryption is the decryption oracle of the static Diffie–Hellman module. -/
example {G : Type} [AddCommGroup G] [DecidableEq G] (q : ℕ) [NeZero q] [Module (ZMod q) G] (g : G)
    (α : ZMod q) (ct : G × G) :
    pure ((elGamalExplicitCoinPKE q g).dec α ct) =
      (some <$> elGamalDecryptOracle q α ct : ProbComp (Option G)) := by
  simp [elGamalExplicitCoinPKE, elGamalDecryptOracle]

/-- The adversary that guesses the second ciphertext component as the message. -/
def guessSecond (F : PrimeOrderGroupFamily) : F.ElGamalOWAdversary :=
  fun _ _ _ ct => pure ct.2

theorem isPPT_guessSecond (F : PrimeOrderGroupFamily) : (guessSecond F).IsPPT :=
  (ComputableInPolyTime.isPPTOn (f := fun x : F.DDHInput =>
    F.encode x.groupParameters x.candidateShared)
    (F.encDDHInput_candidateShared_polyTime .id')).congr fun x => by
      simp [guessSecond]

/-- Under CDH, `guessSecond` wins Attack Game 12.6 with negligible probability. -/
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hCDH : F.CDH setup) :
    Negligible fun n => Game.succProbability (F.elGamalOWGame setup (guessSecond F) n) :=
  PrimeOrderGroupFamily.CDH.elGamal_oneWay hCDH (guessSecond F) (isPPT_guessSecond F)

end CslibFrontierTests.Crypto.ElGamalOneWay
