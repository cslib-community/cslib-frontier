/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.ElGamal.OneWay
import CslibFrontier.Tactic.PPT

/-!
# Tests for the one-wayness of multiplicative ElGamal

Checks of `CslibFrontier/Crypto/Computational/ElGamal/OneWay.lean` as an ordinary `module` client:
`γ • g` for uniform `γ` is uniform when `g` generates the group, which holds at every member of a
group family and transfers the fixed-group equality to the book's literal draws `x ←R 𝔾` and
`y ←R 𝔾`; one value of the advantage, at `g = 0`, in the one-way game and in the CDH game of `ℬ`;
with a point setup law the family game is `PKE.owAdvantage` at that group; and
`CDH.elGamal_oneWay_ideal` applies to a named adversary with its efficiency proof.
-/

public section

namespace CslibFrontierTests.Crypto.ElGamalOneWay

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols Turing.MultiTapeTM

/-! ### The message law -/

/-- When `γ ↦ γ • g` is a bijection, `γ • g` for uniform `γ` is uniform on the group. -/
theorem eval_smul_uniform {G : Type} [AddCommGroup G] [Fintype G] (q : ℕ) [NeZero q]
    [Module (ZMod q) G] (g : G) (hg : Function.Bijective fun c : ZMod q => c • g) :
    ProbComp.eval ((fun γ : ZMod q => γ • g) <$> ($ᵗ ZMod q)) = PMF.uniformOfFintype G := by
  rw [ProbComp.eval_map, ProbComp.eval_uniform, PMF.map,
    ← PMF.bind_pure (PMF.uniformOfFintype G)]
  exact uniformOfFintype_bind_smul hg PMF.pure

/-- At a member of a group family the message of `elGamalOWGame` is uniform on the group, as the
book's `x ←R 𝔾` is. -/
example (F : PrimeOrderGroupFamily) (d : F.Desc) [Fintype (F.Carrier d)] :
    ProbComp.eval ((fun γ : ZMod (F.order d) => γ • F.generator d) <$> ($ᵗ ZMod (F.order d))) =
      PMF.uniformOfFintype (F.Carrier d) :=
  eval_smul_uniform (F.order d) (F.generator d) (F.smul_generator_bijective d)

/-- The book's literal draws: for a generator `g`, the fixed-group equality transfers through
`eval_smul_uniform` to a message and a `y` drawn by `$ᵗ G`. The bijection is used only to identify
the sampler `γ • g` with `$ᵗ G`. -/
example {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] (q : ℕ) [NeZero q]
    [Module (ZMod q) G] (g : G) (hg : Function.Bijective fun c : ZMod q => c • g)
    (A : G → G × G → ProbComp G) :
    ProbComp.eval (PKE.owExperiment (elGamalExplicitCoinPKE q g).toPKE ($ᵗ G) A) =
      ProbComp.eval (cdhExperiment q g (elGamalOWToCDH ($ᵗ G) A)) := by
  have hS : ProbComp.eval ((fun γ : ZMod q => γ • g) <$> ($ᵗ ZMod q)) = ProbComp.eval ($ᵗ G) := by
    rw [eval_smul_uniform q g hg, ProbComp.eval_uniform]
  have h1 (S S' : ProbComp G) (h : ProbComp.eval S = ProbComp.eval S') :
      ProbComp.eval (PKE.owExperiment (elGamalExplicitCoinPKE q g).toPKE S A) =
        ProbComp.eval (PKE.owExperiment (elGamalExplicitCoinPKE q g).toPKE S' A) := by
    simp only [PKE.owExperiment, ProbComp.eval_bind, h]
  have h2 (S S' : ProbComp G) (h : ProbComp.eval S = ProbComp.eval S') :
      ProbComp.eval (cdhExperiment q g (elGamalOWToCDH S A)) =
        ProbComp.eval (cdhExperiment q g (elGamalOWToCDH S' A)) := by
    simp only [cdhExperiment, elGamalOWToCDH, ProbComp.eval_bind, h]
  rw [← h1 _ _ hS, ← h2 _ _ hS]
  exact eval_owExperiment_elGamalExplicitCoinPKE q g A

/-! ### One value of the advantage -/

/-- At `g = 0` the message is always `0`, so the adversary that answers `0` has one-way
advantage `1`. -/
theorem owAdvantage_zero_generator {G : Type} [AddCommGroup G] [DecidableEq G] (q : ℕ) [NeZero q]
    [Module (ZMod q) G] :
    PKE.owAdvantage (elGamalExplicitCoinPKE q (0 : G)).toPKE
      ((fun γ : ZMod q => γ • (0 : G)) <$> ($ᵗ ZMod q)) (fun _ _ => pure 0) = 1 := by
  simp [PKE.owAdvantage, PKE.owExperiment, Experiment.succProbability, Game.succProbability]

/-- The advantage theorem carries that value to the CDH game: at `g = 0`, where CDH is false, the
adversary `ℬ` built from the zero adversary has CDH advantage `1`. -/
example {G : Type} [AddCommGroup G] [DecidableEq G] (q : ℕ) [NeZero q] [Module (ZMod q) G] :
    cdhAdvantage q (0 : G)
      (elGamalOWToCDH ((fun γ : ZMod q => γ • (0 : G)) <$> ($ᵗ ZMod q)) fun _ _ => pure 0) = 1 := by
  rw [← owAdvantage_elGamalExplicitCoinPKE_eq_cdhAdvantage, owAdvantage_zero_generator]

/-! ### The family game -/

/-- With a point setup law, the game of `CDH.elGamal_oneWay_ideal` is Attack Game 12.6 on the
scheme of that group: its success probability is `PKE.owAdvantage`. -/
example (F : PrimeOrderGroupFamily) (d : F.Desc) (A : F.ElGamalOWAdversary) (n : ℕ) :
    Game.succProbability (F.elGamalOWGame (fun _ => PMF.pure d) A n) =
      PKE.owAdvantage (elGamalExplicitCoinPKE (F.order d) (F.generator d)).toPKE
        ((fun γ : ZMod (F.order d) => γ • F.generator d) <$> ($ᵗ ZMod (F.order d))) (A n d) := by
  rw [PrimeOrderGroupFamily.elGamalOWGame, Game.withSetup_pure]
  rfl

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
  PrimeOrderGroupFamily.CDH.elGamal_oneWay_ideal hCDH (guessSecond F) (isPPT_guessSecond F)

end CslibFrontierTests.Crypto.ElGamalOneWay
