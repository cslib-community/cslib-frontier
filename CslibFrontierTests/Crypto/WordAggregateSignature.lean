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

Both security notions fail for a scheme whose verifiers accept everything, and both hold for one
whose aggregate verifier rejects everything, which is not correct. The hash transform of
Exercise 15.11(c) preserves correctness (applied to the accept-all scheme with a constant hash) and
needs it (the transform of the reject-all scheme is not correct). The constant-hash transform of
the accept-all scheme is not strongly binding. The winning conditions are applied as
a caller would, and reject outputs of unequal lengths, without the challenge key, on queried
messages, with a rejecting verdict, and equal pairs.
-/

public section

namespace CslibFrontierTests.Crypto.WordAggregateSignature

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

theorem correctOn_acceptAll : acceptAll.CorrectOn fun _ _ => True :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl

/-- `ASIG` can fail: a forger that makes no query and outputs one key and one message wins against
`acceptAll` with probability `1`. -/
theorem not_asig_trivial : ¬ acceptAll.ASIG := by
  intro hASIG
  let A : ASIGForger := fun _ => pure ([[]], [[]], [])
  have hA : IsPPTOn asigInputEnc asigOutputEnc (fun _ => pure ([[]], [[]], [])) := by
    ppt [asigInputEnc, asigOutputEnc]
  have hneg := hASIG.negligible_succProbability A hA.isOraclePPTOn
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

/-- The transform of Exercise 15.11(c) with the constant hash `[]`. -/
def constantHash (S : WordAggregateSignatureScheme) : WordAggregateSignatureScheme :=
  S.appendHash encBits Decoder.bits (fun _ => encBits) (fun _ => pure []) (by ppt)
    (fun _ _ => []) constHash_polyTime

/-- The transform preserves the correctness of `acceptAll`. -/
example : (constantHash acceptAll).CorrectOn fun _ _ => True :=
  appendHash_correctOn _ _ _ _ _ _ _ _ correctOn_acceptAll

/-- The constant-hash transform of `acceptAll` is not strongly binding. -/
theorem not_strongBinding_constantHash : ¬ (constantHash acceptAll).StrongBinding := by
  intro hSB
  let A : SBAdversary := fun _ =>
    pure ([[]], [[]], [[]], [[true]], encPair encBits encBits ([], []))
  have hA : IsPPTOn sbAsigInputEnc sbAsigOutputEnc A := by
    ppt [A, sbAsigInputEnc, sbAsigOutputEnc]
  have hneg := hSB.negligible_succProbability A hA
  have hone : ∀ n, (1 : ℝ≥0) ≤
      Game.succProbability (ProbComp.eval ((constantHash acceptAll).sbAsigGame A n)) := by
    intro n
    simp only [constantHash, acceptAll, A, sbAsigGame, appendHash, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.pure_bind, Decoder.decode_enc]
    simp [sbAsigWin, Game.succProbability]
  exact not_negligible_const one_ne_zero (negligible_of_le hneg hone)

/-- The scheme with the base scheme of `acceptAll` whose aggregate verifier rejects everything. -/
def rejectAll : WordAggregateSignatureScheme :=
  { acceptAll with
    aggregateVerify := fun _ _ _ _ => false
    aggregateVerify_polyTime := by polytime }

/-- No forger wins Attack Game 15.2 against `rejectAll`. -/
theorem asig_rejectAll : rejectAll.ASIG :=
  Game.Indistinguishable.of_negligible_succProbability fun A _ => by
    simp [asigGame, rejectAll, Game.succProbability]

/-- No adversary wins Attack Game 15.3 against `rejectAll`. -/
theorem strongBinding_rejectAll : rejectAll.StrongBinding :=
  Game.Indistinguishable.of_negligible_succProbability fun A _ => by
    simp [sbAsigGame, sbAsigWin, rejectAll, Game.succProbability]

/-- A scheme whose aggregate verifier rejects everything is not correct: it rejects the aggregate
of no signatures. -/
theorem not_correctOn_of_aggregateVerify_eq_false {S : WordAggregateSignatureScheme}
    (hS : ∀ param pks ms sigAg, S.aggregateVerify param pks ms sigAg = false) :
    ¬ S.CorrectOn fun _ _ => True := by
  intro h
  obtain ⟨param, hparam⟩ := (ProbComp.eval (S.setup 0)).support_nonempty
  obtain ⟨sigAg, hsigAg⟩ := (ProbComp.eval (S.aggregate param [] [] [])).support_nonempty
  simpa [hS] using h 0 param hparam [] [] [] rfl rfl trivial
    (fun _ hi => absurd hi (Nat.not_lt_zero _)) sigAg hsigAg

/-- `rejectAll` is not correct. -/
example : ¬ rejectAll.CorrectOn fun _ _ => True :=
  not_correctOn_of_aggregateVerify_eq_false fun _ _ _ _ => rfl

/-- Nor is its transform, so the hypothesis of `appendHash_correctOn` is needed. -/
example : ¬ (constantHash rejectAll).CorrectOn fun _ _ => True :=
  not_correctOn_of_aggregateVerify_eq_false fun _ _ _ _ => by
    simp [constantHash, appendHash, rejectAll]

/-! ### The winning conditions -/

/-- A fresh forgery carries the challenge key and a message outside the signing queries. -/
example {pk : List Bool} {pks ms queried : List (List Bool)}
    (h : asigFresh pk pks ms queried = true) : pk ∈ pks ∧ ∃ m ∈ ms, m ∉ queried := by
  obtain ⟨-, j, hj, hj', hpk, hm⟩ := (asigFresh_eq_true_iff pk pks ms queried).mp h
  exact ⟨hpk ▸ List.getElem_mem hj, ms[j], List.getElem_mem hj', hm⟩

/-- A winning output of the binding game verifies twice, for key vectors or message vectors that
differ. -/
example {b₁ b₂ : Bool} {pks ms pks' ms' : List (List Bool)}
    (h : sbAsigWin b₁ b₂ pks ms pks' ms' = true) :
    b₁ = true ∧ b₂ = true ∧ (pks ≠ pks' ∨ ms ≠ ms') := by
  obtain ⟨hne, -, -, h₁, h₂⟩ := (sbAsigWin_eq_true_iff b₁ b₂ pks ms pks' ms').mp h
  exact ⟨h₁, h₂, not_and_or.mp fun ⟨hk, hm⟩ => hne (by rw [hk, hm])⟩

/-- A forgery on the challenge key and an unqueried message is fresh. -/
example : asigFresh [true] [[true]] [[false]] [] = true := by decide

/-- A forgery with more keys than messages is not fresh. -/
example : asigFresh [true] [[true]] ([] : List (List Bool)) [] = false := by decide

/-- A forgery on a queried message is not fresh. -/
example : asigFresh [true] [[true]] [[false]] [[false]] = false := by decide

/-- A forgery in which no position carries the challenge key is not fresh. -/
example : asigFresh [true] [[false]] [[false]] [] = false := by decide

/-- A forgery is not fresh when the challenge key signs only queried messages, even if an
unqueried message sits under another key. -/
example : asigFresh [true] [[true], [false]] [[false], [true]] [[false]] = false := by decide

/-- Two different pairs on which the aggregate signature verifies win the binding game. -/
example : sbAsigWin true true [[true]] [[false]] [[true]] [[true]] = true := by decide

/-- A rejecting verdict on either pair does not win the binding game. -/
example : sbAsigWin true false [[true]] [[false]] [[true]] [[true]] = false := by decide

/-- A pair with fewer messages than keys does not win the binding game. -/
example : sbAsigWin true true [[true]] ([] : List (List Bool)) [[true]] [[false]] = false := by
  decide

/-- Two equal pairs do not win the binding game. -/
example : sbAsigWin true true [[true]] [[false]] [[true]] [[false]] = false := by decide

end CslibFrontierTests.Crypto.WordAggregateSignature
