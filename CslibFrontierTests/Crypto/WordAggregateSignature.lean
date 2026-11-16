/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.WordAggregateSignature.AppendHash
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Tests for aggregate signature schemes on bit strings

Both security notions fail for a scheme whose verifiers accept everything; the hash transform of
Exercise 15.11(c) with a constant hash is not strongly binding, so collision resistance cannot be
dropped; and the winning conditions reject outputs of unequal lengths, queried messages and equal
pairs.
-/

public section

namespace Cslib.Tests.WordAggregateSignature

open Cslib Cslib.Crypto Cslib.Crypto.AggregateSignature Cslib.Crypto.WordAggregateSignatureScheme
  Probability Turing.MultiTapeTM
open scoped NNReal

/-- The scheme whose signatures and aggregate signatures are empty and whose verifiers accept
everything. -/
def acceptAll : WordAggregateSignatureScheme where
  setup _ := pure []
  setup_ppt := by ppt
  base :=
    { keyGen := fun _ => pure ([], [])
      sign := fun _ _ => pure []
      verify := fun _ _ _ => true
      keyGen_ppt := by ppt
      sign_ppt := by ppt
      verify_polyTime := by polytime
      verify_sign := fun _ _ _ _ _ _ _ => rfl }
  aggregate _ _ _ _ := pure []
  aggregate_ppt := by ppt
  aggregateVerify _ _ _ _ := true
  aggregateVerify_polyTime := by polytime

example : acceptAll.CorrectOn fun _ _ => True :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl

/-- `ASIG` can fail: a forger that makes no query and outputs one key and one message wins against
`acceptAll` with probability `1`. -/
theorem not_asig_trivial : ¬ acceptAll.ASIG := by
  intro hASIG
  let A : ASIGForger := fun _ => pure ([[]], [[]], [])
  have hA : IsPPTOn asigInputEnc asigOutputEnc (fun _ => pure ([[]], [[]], [])) := by
    ppt [asigInputEnc, asigOutputEnc]
  have hneg :
      Negligible fun n => Game.succProbability (ProbComp.eval (acceptAll.asigGame A n)) := by
    simpa only [Game.advantage_pure_false] using hASIG A hA.isOraclePPTOn
  have hone : ∀ n, (1 : ℝ≥0) ≤ Game.succProbability (ProbComp.eval (acceptAll.asigGame A n)) := by
    intro n
    simp [acceptAll, A, asigGame, asigFresh, ProbOracleComp.runState_pure, StateT.run_pure,
      Game.succProbability]
  exact not_negligible_const one_ne_zero (negligible_of_le hneg hone)

/-- The constant hash is computable in polynomial time. -/
theorem constHash_polyTime :
    ComputableInPolyTime (fun _ : List Bool × List Bool => ([] : List Bool))
      (encPair encBits encBits) encBits := by
  polytime

/-- Collision resistance cannot be dropped from Exercise 15.11(c): with a constant hash the
transform of `acceptAll` is not strongly binding. -/
theorem constantHash_not_strongBinding :
    ¬ (acceptAll.appendHash encBits Decoder.bits (fun _ => encBits) (fun _ => pure []) (by ppt)
      (fun _ _ => []) constHash_polyTime).StrongBinding := by
  intro hSB
  let A : SBAdversary := fun _ =>
    pure ([[]], [[]], [[]], [[true]], encPair encBits encBits ([], []))
  have hA : IsPPTOn sbAsigInputEnc sbAsigOutputEnc A := by
    ppt [A, sbAsigInputEnc, sbAsigOutputEnc]
  have hneg : Negligible fun n => Game.succProbability (ProbComp.eval
      ((acceptAll.appendHash encBits Decoder.bits (fun _ => encBits) (fun _ => pure []) (by ppt)
        (fun _ _ => []) constHash_polyTime).sbAsigGame A n)) := by
    simpa only [Game.advantage_pure_false] using hSB A hA
  have hone : ∀ n, (1 : ℝ≥0) ≤ Game.succProbability (ProbComp.eval
      ((acceptAll.appendHash encBits Decoder.bits (fun _ => encBits) (fun _ => pure []) (by ppt)
        (fun _ _ => []) constHash_polyTime).sbAsigGame A n)) := by
    intro n
    simp only [acceptAll, A, sbAsigGame, appendHash, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.pure_bind, Decoder.decode_enc]
    simp [sbAsigWin, Game.succProbability]
  exact not_negligible_const one_ne_zero (negligible_of_le hneg hone)

/-! ### The winning conditions -/

/-- A forgery on the challenge key and an unqueried message is fresh. -/
example : asigFresh [true] [[true]] [[false]] [] = true := by decide

/-- A forgery with more keys than messages is not fresh. -/
example : asigFresh [true] [[true]] ([] : List (List Bool)) [] = false := by decide

/-- A forgery on a queried message is not fresh. -/
example : asigFresh [true] [[true]] [[false]] [[false]] = false := by decide

/-- Two different pairs on which the aggregate signature verifies win the binding game. -/
example : sbAsigWin true true [[true]] [[false]] [[true]] [[true]] = true := by decide

/-- A pair with fewer messages than keys does not win the binding game. -/
example : sbAsigWin true true [[true]] ([] : List (List Bool)) [[true]] [[false]] = false := by
  decide

/-- Two equal pairs do not win the binding game. -/
example : sbAsigWin true true [[true]] [[false]] [[true]] [[false]] = false := by decide

end Cslib.Tests.WordAggregateSignature
