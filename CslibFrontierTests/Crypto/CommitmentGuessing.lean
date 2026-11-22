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

end CslibFrontierTests.Crypto.CommitmentGuessing
