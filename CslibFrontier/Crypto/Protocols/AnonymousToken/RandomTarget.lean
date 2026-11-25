/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.AnonymousToken.Basic
public import CslibFrontier.Crypto.Protocols.Signature.OneMore
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Data.List.Nodup

/-!
# Extracted single-issuer redemptions and a random-target one-more game

An extracted redemption supplies the certifying witness already. Public message labels are
embedded injectively into a finite vector of challenge slots. A valid token for message `m`
certifies the target at its slot; different slots may contain equal target values. The attacker
has the raw chosen-target certification oracle, with every call counted, including repeats and
failed answers. The experiment accepts more than the configured budget of valid tokens with
distinct semantic messages after at most that budget of oracle calls.

`reduceRedemptions` runs the same attacker and retains its first `budget + 1` tokens, translating
messages to slots and witnesses to preimage claims. Injectivity of the public labels preserves
distinctness. This pure postprocessing preserves every query bound, and every accepting
redemption run yields an accepting one-more run, giving a success bound with coefficient one.
The target sampler remains explicit. In the ideal UOV instance it is an independent uniform
vector, and optional preimages retain the real failure probability of the supplied finite signer.

This is an original finite extracted single-issuer composition step; uniform polynomial-time
certification (`reduceRedemptionsWord`) is provided in
`CslibFrontier.Crypto.Protocols.AnonymousToken.RandomTargetPolyTime`. It does not realize the
public slot labels by a random oracle, extract witnesses from redemption proofs, or hide an
issuer. The complete multi-issuer VOLE-IHAT proof and those extraction and random-oracle
obligations remain issue #7068.

## Main definitions

* `extractedRedemptionAccept`, `extractedRedemptionExperiment`: redemption witnesses for more
  than the fixed issuance budget, with distinct semantic messages.
* `reduceRedemptions`: the explicit prefix-and-slot reduction to fixed-budget one-more inversion.

## Main results

* `reduceRedemptions_queryBound`: pure output processing preserves the oracle query bound.
* `extractedRedemption_succProbability_le`: extracted redemption success is bounded by the
  success of the concrete one-more reduction.

## References

* [*VOLE-IHAT*][VOLEIHAT2026], Protocol / Redemption, `RedeemRelation` (`#redemption`).
* [Baum et al., *PoMFRIT*, USENIX prepublication, Definition 3.1][PoMFRIT2026].
-/

public section

namespace Cslib.Crypto.AnonymousToken

open Probability

variable {PK SK Message Target Sig : Type} {N : ℕ}

/-- The extracted fixed-budget redemption test. Distinctness concerns semantic messages;
target values may collide. Every answered raw oracle query contributes to the budget. -/
@[expose] def extractedRedemptionAccept [DecidableEq Message]
    (S : Signature.Scheme PK SK Target Sig) (pk : PK) (targets : Fin N → Target)
    (slot : Message ↪ Fin N) (budget : ℕ) (out : List (Token Message Unit Sig))
    (log : List (Target × Sig)) : Bool :=
  decide (log.length ≤ budget ∧ budget < out.length ∧
    (out.map fun token => token.payload.message).Nodup) &&
  out.all (Token.valid S (fun message _ => targets (slot message)) pk)

/-- The single-issuer experiment with already extracted witnesses and explicit public target
slots. It supplies the raw chosen-target oracle and retains its exact answer distribution. -/
@[expose] def extractedRedemptionExperiment [DecidableEq Message]
    (S : Signature.Scheme PK SK Target Sig) (targets : PK → ProbComp (Fin N → Target))
    (slot : Message ↪ Fin N) (budget : ℕ)
    (A : PK → (Fin N → Target) →
      ProbOracleComp (fun _ : Target => Sig) (List (Token Message Unit Sig))) : Experiment := do
  let keys ← S.keyGen
  let ys ← targets keys.1
  let (out, log) ← (A keys.1 ys).runLog (S.sign keys.2)
  return extractedRedemptionAccept S keys.1 ys slot budget out log

/-- Keep the first `budget + 1` extracted tokens and translate their messages to challenge slots.
This reduction makes exactly the original attacker's oracle calls. -/
@[expose] def reduceRedemptions (slot : Message ↪ Fin N) (budget : ℕ)
    (A : PK → (Fin N → Target) →
      ProbOracleComp (fun _ : Target => Sig) (List (Token Message Unit Sig)))
    (pk : PK) (targets : Fin N → Target) :
    ProbOracleComp (fun _ : Target => Sig) (List (Signature.PreimageClaim N Sig)) :=
  (fun out => (out.take (budget + 1)).map fun token =>
    (⟨slot token.payload.message, token.signature⟩ : Signature.PreimageClaim N Sig)) <$>
      A pk targets

/-- The reduction's output processing adds no calls, for any bound on the original program. -/
theorem reduceRedemptions_queryBound (slot : Message ↪ Fin N) (budget : ℕ)
    (A : PK → (Fin N → Target) →
      ProbOracleComp (fun _ : Target => Sig) (List (Token Message Unit Sig)))
    (pk : PK) (targets : Fin N → Target) {queries : ℕ}
    (h : (A pk targets).IsQueryBounded queries) :
    (reduceRedemptions slot budget A pk targets).IsQueryBounded queries := by
  simpa only [reduceRedemptions, ProbOracleComp.IsQueryBounded,
    OracleComp.isCostBounded_map_iff] using h

private theorem extractedRedemptionAccept_implies_oneMore [DecidableEq Message]
    (S : Signature.Scheme PK SK Target Sig) (pk : PK) (targets : Fin N → Target)
    (slot : Message ↪ Fin N) (budget : ℕ) (out : List (Token Message Unit Sig))
    (log : List (Target × Sig))
    (h : extractedRedemptionAccept S pk targets slot budget out log = true) :
    Signature.oneMoreAccept S pk targets budget
      ((out.take (budget + 1)).map fun token =>
        (⟨slot token.payload.message, token.signature⟩ : Signature.PreimageClaim N Sig))
      log = true := by
  simp only [extractedRedemptionAccept, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Signature.oneMoreAccept, Bool.and_eq_true, decide_eq_true_eq,
    List.length_map, List.length_take]
  refine ⟨⟨h.1.1, Nat.min_eq_left (Nat.succ_le_iff.mpr h.1.2.1), ?_⟩, ?_⟩
  · have hprefix : ((out.take (budget + 1)).map fun token => token.payload.message).Nodup := by
      rw [List.map_take]
      exact List.Nodup.sublist (List.take_sublist _ _) h.1.2.2
    simpa only [List.map_map, Function.comp_def] using List.Nodup.map slot.injective hprefix
  · apply List.all_eq_true.mpr
    intro claim hclaim
    obtain ⟨token, htoken, rfl⟩ := List.mem_map.mp hclaim
    exact (List.all_eq_true.mp h.2) token (List.mem_of_mem_take htoken)

/-- This finite extracted single-issuer step loses no success probability. It is not the full
VOLE-IHAT security theorem: the attacker already supplies witnesses and the slot assignment is
given. No correctness, hardness, or efficiency hypothesis is imposed on the signer. -/
theorem extractedRedemption_succProbability_le [DecidableEq Message]
    (S : Signature.Scheme PK SK Target Sig) (targets : PK → ProbComp (Fin N → Target))
    (slot : Message ↪ Fin N) (budget : ℕ)
    (A : PK → (Fin N → Target) →
      ProbOracleComp (fun _ : Target => Sig) (List (Token Message Unit Sig))) :
    Experiment.succProbability (extractedRedemptionExperiment S targets slot budget A) ≤
      Experiment.succProbability
        (Signature.oneMoreExperiment S targets budget (reduceRedemptions slot budget A)) := by
  apply Game.succProbability_mono
  simp only [extractedRedemptionExperiment, Signature.oneMoreExperiment, reduceRedemptions,
    ProbOracleComp.runLog, ProbOracleComp.runState_map, StateT.run_map,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_map]
  refine PMF.bind_apply_mono_on_support _ _ fun keys _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun ys _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun result _ => ?_
  dsimp only [Function.comp_def]
  cases h : extractedRedemptionAccept S keys.1 ys slot budget result.1 result.2
  · simp
  · rw [extractedRedemptionAccept_implies_oneMore S keys.1 ys slot budget result.1 result.2 h]

end Cslib.Crypto.AnonymousToken
