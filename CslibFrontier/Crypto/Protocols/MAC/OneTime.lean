/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Crypto.Game.Forgery
public import CslibFrontier.Crypto.Primitives.UHF.PairwiseUnpredictability
import CslibFrontier.Languages.Probabilistic.Semantics

/-!
# One-time authentication from pairwise unpredictability

[BonehShoup2023], Section 7.6, uses the fresh-pair MAC game with one signing response. A keyed
hash defines a deterministic MAC by using its digest as the tag and checking equality at
verification. For this MAC, a valid fresh pair necessarily has a fresh message. Thus an adversary
can forge precisely when it can predict a second digest after seeing the first.
-/

public section

namespace Cslib.Crypto

open scoped ENNReal

variable {K M T σ : Type}

/-- **Theorem 7.12** ([BonehShoup2023], v0.6, Section 7.6.3, printed p. 276).
For a private uniform key, using an `ε`-PUF's digest as the tag gives success probability at
most `ε` for every fresh-pair forger after one signing response. The two-stage adversary can
use arbitrary private state and has no runtime restriction. -/
theorem oneTimeForgeExperiment_hash_le [Fintype K] [Nonempty K] [DecidableEq M] [DecidableEq T]
    {H : K → M → T} {ε : ℝ≥0∞} (h : UHF.IsPairwiseUnpredictable H ε)
    (A : TwoStage Unit M T (M × T) σ) :
    ProbComp.eval (oneTimeForgeExperiment (ProbComp.uniform K) (fun k m => pure (H k m))
      (fun k m t => decide (H k m = t)) (A.choose ()) A.guess) true ≤ ε := by
  let B : UHF.PredictionAdversary M T σ :=
    ⟨A.choose, fun state t => (fun p => ⟨p.1, p.2⟩) <$> A.guess state t⟩
  have sameLaw : ProbComp.eval
      (oneTimeForgeExperiment (ProbComp.uniform K) (fun k m => pure (H k m))
        (fun k m t => decide (H k m = t)) (A.choose ()) A.guess) =
      ProbComp.eval (UHF.predictionExperiment H B) := by
    simp only [oneTimeForgeExperiment, UHF.predictionExperiment, B, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.pure_bind]
    congr 1 with k : 1
    congr 1 with chosen : 1
    rcases chosen with ⟨m, state⟩
    simp only [ProbComp.eval_map, PMF.bind_map, Function.comp_def]
    congr 1 with guess : 1
    rcases guess with ⟨m', t'⟩
    by_cases ht : H k m' = t'
    · subst t'
      by_cases hm : m' = m
      · subst m'
        simp [freshPair]
      · simp [freshPair, hm]
    · simp [ht]
  rw [sameLaw]
  exact h σ B

end Cslib.Crypto
