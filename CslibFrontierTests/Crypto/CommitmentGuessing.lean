/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Commitment.Guessing
import CslibFrontier.Tactic.PPT

/-!
# Predicting the bit of a Naor commitment

The joint law on two bits can encode a biased secret with a noisy prior observation. The receiver
uses the observation as its challenge and state, chooses the pair `(false, true)`, and applies an
arbitrary efficient test to the commitment. The baseline predictor learns only the observation.

In the uniform single-bit protocol a receiver saves its random challenge and uses it to guess the
committed bit. The client constructs the prescribed stretch starting from an arbitrary uniform PRG.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.CommitmentGuessing

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

private def receiver (guess : ℕ → List Bool → List Bool → ProbComp Bool) : CommitmentReceiver where
  choose _ z := pure ((z, false, true), z)
  guess := guess

example {G : List Bool → List Bool} {length : ℕ → ℕ} (hG : NonuniformPRG G length)
    (guess : ℕ → List Bool → List Bool → ProbComp Bool)
    (hguess : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
      (fun ⟨n, z, c⟩ => guess n z c)) :
    ∃ predict : ℕ → List Bool → ProbComp Bool, IsPPT encBool predict ∧
      ∀ μ : ℕ → PMF (Bool × Bool), Negligible fun n => Game.advantage
        (do
          let (bit, obs) ← μ n
          let seed ← BitString.uniformList n
          let g ← ProbComp.eval (guess n [obs] (naorCommit G [obs] bit seed))
          return g == bit)
        (predictionExperiment (μ n) Prod.snd Prod.fst
          fun obs => ProbComp.eval (predict n [obs])) := by
  have hR : (receiver guess).IsPPT := ⟨by dsimp only [receiver]; ppt, hguess⟩
  obtain ⟨predict, hppt, h⟩ := hG.naorStatefulHiding.exists_priorPredictor
    (computableInPolyTime_naorCommit hG.polyTime (by fun_prop) (by fun_prop) (by fun_prop)) hR
  refine ⟨predict, hppt, fun μ => ?_⟩
  let pack (p : Bool × Bool) := (p.1, [p.2])
  have hlen (n x) (hx : x ∈ ((μ n).map pack).support) : x.2.length ≤ 1 := by
    obtain ⟨p, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact Nat.le_refl _
  simpa [pack, predictionExperiment, commitmentHidingGame, receiver, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.monad_bind_eq_bind, PMF.bind_map,
    PMF.bind_bind, Function.comp_def] using h (fun n => (μ n).map pack) (fun _ => 1) (.const 1) hlen

private noncomputable def uniformReceiver (n : ℕ) : TwoStage Unit (List Bool) (List Bool) Bool
    (List Bool) where
  choose _ := do
    let r ← BitString.sampleList (3 * n)
    return (r, r)
  guess state c := pure (state.headD false ^^ c.headD false)

open Filter in
example {G : List Bool → List Bool} {length p : ℕ → ℕ} (hG : PseudorandomGenerator G length)
    (hp : PolynomiallyBounded p) (hpos : ∀ n, 0 < p n) :
    let pad := PRGStretch.stretch (fun seed => (G seed).take (seed.length + 1))
      (fun n => max 1 (3 * n) - n)
    (∀ᶠ n in atTop, (Game.succProbability (ProbComp.eval (Experiment.guessBit fun bit => do
      let (r, state) ← (uniformReceiver n).choose ()
      let seed ← BitString.sampleList n
      (uniformReceiver n).guess state (naorCommit pad r bit seed))) : ℝ) ≤ 1 / 2 + 1 / p n) ∧
    naorBindingProb pad (fun n => 3 * n) 1 < 1 / 2 := by
  have hone := hG.truncate (fun n => n + 1) (by polytime) hG.stretch (fun n => by lia)
  have hpad := hone.amplify (fun n => max 1 (3 * n)) (by polytime) (fun n => by lia)
  obtain ⟨hhide, hbind⟩ := hpad.naorCommit_guessing_and_binding
  have hR : TwoStage.IsPPT encUnit encBits encBits encBool encBits uniformReceiver := by
    constructor <;> dsimp only [uniformReceiver] <;> ppt
  refine ⟨?_, by simpa using hbind 1 (by decide)⟩
  filter_upwards [(hhide _ hR).eventually_le_inv_polynomial hp hpos] with n hn
  rw [Game.coe_guessingAdvantage] at hn
  linarith only [(le_abs_self _).trans hn]

-- The bad event counted by the binding bound is exactly an unbounded sender's ability to
-- give two accepted openings of the same commitment.
example (G : List Bool → List Bool) (n : ℕ) (r : List Bool) :
    ¬ NaorBinding G n r ↔ ∃ c s₀ s₁,
      naorVerify G n r c false s₀ = true ∧ naorVerify G n r c true s₁ = true := by
  constructor
  · intro h
    unfold NaorBinding at h
    push Not at h
    obtain ⟨s₀, s₁, h₀, h₁, heq⟩ := h
    exact ⟨_, s₀, s₁, naorVerify_naorCommit r false h₀, heq.symm ▸ naorVerify_naorCommit r true h₁⟩
  · rintro ⟨c, s₀, s₁, h₀, h₁⟩ hbind
    obtain ⟨hlen₀, heq₀⟩ := eq_naorCommit_of_naorVerify h₀
    obtain ⟨hlen₁, heq₁⟩ := eq_naorCommit_of_naorVerify h₁
    exact hbind _ _ hlen₀ hlen₁ (heq₀.symm.trans heq₁)

end CslibFrontierTests.Crypto.CommitmentGuessing
