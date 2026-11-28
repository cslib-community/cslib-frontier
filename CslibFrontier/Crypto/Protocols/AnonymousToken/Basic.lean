/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Signature.Scheme
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunLog
import CslibFrontier.Probability.PMF.Bool

/-!
# Certification of anonymous-token witnesses

A token certifies a target computed from a semantic message and an opening. The certification
algorithm is the existing `Signature.Scheme`: it may be an ordinary signature, or a raw
trapdoor-preimage relation whose verifier tests that its public map evaluates to the target.
`selectedIssuerRelation` is the witness relation used when an IHAT redemption hides which
issuer signed its target ([VOLEIHAT2026], Protocol / Redemption, `RedeemRelation`). Its bounded
issuer index compresses the source's one-hot selector; it does not model the selector circuit.
For ACT the semantic message is the full credit state, including the refund, and the target may
be `Tag (Com state opening) refund` ([VOLEACT2026], Overview and Protocol Specification / Tag).

`extractedExperiment` gives the adversary chosen semantic messages and openings and requires an
actual certifying witness for a fresh semantic message. `targetForger` forwards each signing
query once; `bindingReduction` searches the query transcript and returns two different semantic
messages encoding to the same target. `extracted_succProbability_le` proves the additive bound
with coefficient one on both terms, and `targetForger_queryBound` preserves the signing-query
budget. These are explicit programs, without a hypothesis about a reduction's success.

This is an original extracted-witness composition step, not the full security theorem of either
protocol. In particular, the target EUF-CMA term need not be small for a raw UOV map: unrestricted
chosen-target forgery is different from the random-target one-more assumption. Applying this
composition to raw ACT-MQ therefore does not establish its structured-target hardness. Adaptive
VOLE/random-oracle extraction and complete runtime certificates remain tracked in issue #7068.

## Main definitions

* `Payload`, `Token`, `Token.valid`, `issue`: semantic message/opening pairs, certified tokens,
  verification, and issuance.
* `RedemptionWitness`, `selectedIssuerRelation`: extracted witness and selected-issuer relation for
  issuer-hiding redemptions.
* `ExtractedForger`, `Execution`, `runExtracted`, `extractedAccept`, `extractedExperiment`:
  extracted-witness adversary, logged execution, fresh-message acceptance test, and experiment.
* `BindingWitness`, `checkBindingWitness`, `findBindingWitness`, `bindingReduction`,
  `bindingExperiment`, `targetForger`: explicit target-collision and target-forgery reductions.

## Main results

* `issue_correct`: a correct certifier issues a valid token.
* `extracted_succProbability_le`: semantic forgery produces a target forgery or a binding witness.
* `targetForger_queryBound`: the reduction forwards at most the original number of signing calls.
* `execution_log_length_le`: the collision search receives at most that many transcript entries.

## References

* [*VOLE-IHAT*][VOLEIHAT2026], Protocol / Redemption, `RedeemRelation` (`#redemption`).
* [*VOLE-ACT*][VOLEACT2026], Overview (`#overview`), Tag (`#tag`), and Spending (`#spending`).
-/

@[expose] public section

namespace Cslib.Crypto.AnonymousToken

open Probability

variable {PK SK Message Opening Target Sig : Type}

/-- A semantic message and the randomness opening its encoded target. -/
structure Payload (Message Opening : Type) where
  /-- The state or message whose authorization is meaningful to the application. -/
  message : Message
  /-- The opening supplied to the target encoder. -/
  opening : Opening
  deriving DecidableEq

/-- A target opening together with its certification witness. -/
structure Token (Message Opening Sig : Type) where
  /-- The semantic message and its opening. -/
  payload : Payload Message Opening
  /-- A signature, or a preimage when the certifier is a trapdoor map. -/
  signature : Sig
  deriving DecidableEq

/-- Check the certifier on the target encoded by this token. -/
def Token.valid (S : Signature.Scheme PK SK Target Sig) (target : Message → Opening → Target)
    (pk : PK) (token : Token Message Opening Sig) : Bool :=
  S.verify pk (target token.payload.message token.payload.opening) token.signature

/-- Issue a token by signing its encoded target. This operation does not supply a proof system. -/
def issue (S : Signature.Scheme PK SK Target Sig) (target : Message → Opening → Target)
    (sk : SK) (payload : Payload Message Opening) : ProbComp (Token Message Opening Sig) :=
  (fun signature => ⟨payload, signature⟩) <$> S.sign sk (target payload.message payload.opening)

/-- Correct certification gives a valid issued token at every supported key pair. -/
theorem issue_correct (S : Signature.Scheme PK SK Target Sig)
    (target : Message → Opening → Target) (hS : S.Correct)
    {keys : PK × SK} (hkeys : keys ∈ (ProbComp.eval S.keyGen).support)
    (payload : Payload Message Opening) {token : Token Message Opening Sig}
    (htoken : token ∈ (ProbComp.eval (issue S target keys.2 payload)).support) :
    token.valid S target keys.1 = true := by
  simp only [issue, ProbComp.eval_map, PMF.mem_support_map_iff] at htoken
  obtain ⟨signature, hsignature, rfl⟩ := htoken
  exact hS keys hkeys (target payload.message payload.opening) signature hsignature

/-- The private witness of an issuer-hidden redemption. Its issuer selector is bounded by the
public anchor type, rather than an unchecked natural-number index. -/
structure RedemptionWitness (Issuer Opening Sig : Type) where
  /-- Which public issuer key certifies the hidden target. -/
  issuer : Issuer
  /-- The opening of the public semantic message's encoded target. -/
  opening : Opening
  /-- Certification witness under the selected key. -/
  signature : Sig

/-- The selected-issuer witness relation of extracted IHAT redemption. A proof of this relation
must hide `witness`; this definition does not claim zero knowledge or extractability. -/
def selectedIssuerRelation {Issuer : Type} (S : Signature.Scheme PK SK Target Sig)
    (target : Message → Opening → Target) (anchors : Issuer → PK) (message : Message)
    (witness : RedemptionWitness Issuer Opening Sig) : Bool :=
  S.verify (anchors witness.issuer) (target message witness.opening) witness.signature

/-- An adversary already producing the semantic opening and certification witness. It may choose
both the message and opening of every signing request. -/
abbrev ExtractedForger (PK Message Opening Sig : Type) :=
  PK → ProbOracleComp (fun _ : Payload Message Opening => Sig) (Token Message Opening Sig)

/-- The public key, candidate witness, and ordered signing transcript of an extracted attack. -/
structure Execution (PK Message Opening Sig : Type) where
  /-- Public certification key sampled by the experiment. -/
  publicKey : PK
  /-- Candidate output by the attack. -/
  output : Token Message Opening Sig
  /-- Every semantic signing query and its reply, including repetitions and invalid replies. -/
  log : List (Payload Message Opening × Sig)

/-- Execute the extracted attack with the real target signer, retaining all queries and replies. -/
def runExtracted (S : Signature.Scheme PK SK Target Sig)
    (target : Message → Opening → Target) (A : ExtractedForger PK Message Opening Sig) :
    ProbComp (Execution PK Message Opening Sig) := do
  let keys ← S.keyGen
  let (output, log) ← (A keys.1).runLog
    (fun payload => S.sign keys.2 (target payload.message payload.opening))
  return ⟨keys.1, output, log⟩

/-- Whether an extracted execution verifies on a semantic message never queried in `run.log`.
Invalid or failed replies remain in the log and still disqualify their semantic messages. -/
def extractedAccept [DecidableEq Message] (S : Signature.Scheme PK SK Target Sig)
    (target : Message → Opening → Target) (run : Execution PK Message Opening Sig) : Bool :=
  run.output.valid S target run.publicKey &&
    decide (run.output.payload.message ∉ run.log.map (fun entry => entry.1.message))

/-- The structured-target extracted-witness experiment: the output verifies and its full semantic
message was never queried. Invalid replies remain in the log. ACT freshness concerns the entire
state, including the refund. -/
def extractedExperiment [DecidableEq Message] (S : Signature.Scheme PK SK Target Sig)
    (target : Message → Opening → Target) (A : ExtractedForger PK Message Opening Sig) :
    Experiment :=
  extractedAccept S target <$> runExtracted S target A

/-- Two openings to the same encoded target, with different semantic messages. -/
structure BindingWitness (Message Opening : Type) where
  /-- One message and its opening. -/
  first : Payload Message Opening
  /-- The other message and its opening. -/
  second : Payload Message Opening
  deriving DecidableEq

/-- Verify a binding witness for the complete target encoding. -/
def checkBindingWitness [DecidableEq Message] [DecidableEq Target]
    (target : Message → Opening → Target) (witness : BindingWitness Message Opening) : Bool :=
  decide (witness.first.message ≠ witness.second.message ∧
    target witness.first.message witness.first.opening =
      target witness.second.message witness.second.opening)

/-- Search the actual transcript for the first request sharing the candidate's target. The result
is a candidate binding witness; `checkBindingWitness` also checks that its messages differ. -/
def findBindingWitness [DecidableEq Target] (target : Message → Opening → Target)
    (payload : Payload Message Opening) (log : List (Payload Message Opening × Sig)) :
    Option (BindingWitness Message Opening) :=
  (log.find? fun entry => decide
    (target entry.1.message entry.1.opening = target payload.message payload.opening)).map
      (fun entry => ⟨payload, entry.1⟩)

/-- An explicit binding attack: run the extracted attack with a locally generated signing key,
then return two openings if its output reuses a queried target. -/
def bindingReduction [DecidableEq Target] (S : Signature.Scheme PK SK Target Sig)
    (target : Message → Opening → Target) (A : ExtractedForger PK Message Opening Sig) :
    ProbComp (Option (BindingWitness Message Opening)) :=
  (fun run => findBindingWitness target run.output.payload run.log) <$> runExtracted S target A

/-- Run and check the binding attack's actual returned witness. -/
def bindingExperiment [DecidableEq Message] [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (target : Message → Opening → Target)
    (A : ExtractedForger PK Message Opening Sig) : Experiment :=
  (fun witness => witness.any (checkBindingWitness target)) <$> bindingReduction S target A

/-- Forward each semantic signing request to the certification target, preserving private coins,
and output the target and certificate from the extracted candidate. -/
def targetForger (target : Message → Opening → Target)
    (A : ExtractedForger PK Message Opening Sig) : Signature.Forger PK Target Sig := fun pk =>
  (fun token : Token Message Opening Sig =>
      (target token.payload.message token.payload.opening, token.signature)) <$>
    ProbOracleComp.simulate
      (fun payload => ProbOracleComp.query (target payload.message payload.opening)) (A pk)

/-- The target reduction uses at most `q` signing calls when its input attack uses at most `q`.
No runtime bound or fair-coin efficiency follows from this oracle-call bound alone. -/
theorem targetForger_queryBound (target : Message → Opening → Target)
    (A : ExtractedForger PK Message Opening Sig) (pk : PK) {q : Nat}
    (hA : (A pk).IsQueryBounded q) : (targetForger target A pk).IsQueryBounded q := by
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
    (hA.simulate fun _ => ProbOracleComp.IsQueryBounded.query _)

/-- A `q`-query attack leaves at most `q` entries for the binding search, including repeated
requests. This bounds the search's input length without treating target evaluation as free time. -/
theorem execution_log_length_le (S : Signature.Scheme PK SK Target Sig)
    (target : Message → Opening → Target) (A : ExtractedForger PK Message Opening Sig) {q : Nat}
    (hA : ∀ pk, (A pk).IsQueryBounded q) {run : Execution PK Message Opening Sig}
    (hrun : run ∈ (ProbComp.eval (runExtracted S target A)).support) : run.log.length ≤ q := by
  simp only [runExtracted, ProbComp.eval_bind, PMF.mem_support_bind_iff,
    ProbComp.eval_pure, PMF.mem_support_pure_iff] at hrun
  obtain ⟨keys, -, result, hresult, rfl⟩ := hrun
  exact (hA keys.1).length_runLog_le _ result hresult

private def targetAccept [DecidableEq Target] (S : Signature.Scheme PK SK Target Sig)
    (target : Message → Opening → Target) (run : Execution PK Message Opening Sig) : Bool :=
  run.output.valid S target run.publicKey && decide
    (target run.output.payload.message run.output.payload.opening ∉
      run.log.map fun entry => target entry.1.message entry.1.opening)

private theorem targetExperiment_eq [DecidableEq Target] [Inhabited Sig]
    (S : Signature.Scheme PK SK Target Sig) (target : Message → Opening → Target)
    (A : ExtractedForger PK Message Opening Sig) :
    S.eufCmaExperiment (targetForger target A) =
      targetAccept S target <$> runExtracted S target A := by
  simp only [Signature.Scheme.eufCmaExperiment, forgeExperiment, targetForger,
    ProbOracleComp.runLogWith_map, runExtracted, map_bind, bind_map_left]
  refine bind_congr fun ⟨pk, sk⟩ => ?_
  have hsigner : Signer.ofSign S.sign sk = fun _ message => some (S.sign sk message) := by
    funext _ _
    exact Signer.ofSign_apply _ _ _ _
  rw [hsigner, ProbOracleComp.runLogWith_some, ProbOracleComp.runLog_simulate_query]
  simp only [bind_map_left]
  refine bind_congr fun ⟨output, log⟩ => ?_
  simp only [targetAccept, Token.valid, freshMessage, map_pure, Prod.map, id_eq, List.map_map,
    Function.comp_def]

private theorem extractedAccept_cases [DecidableEq Message] [DecidableEq Target]
    (S : Signature.Scheme PK SK Target Sig) (target : Message → Opening → Target)
    (run : Execution PK Message Opening Sig) (h : extractedAccept S target run = true) :
    targetAccept S target run = true ∨
      (findBindingWitness target run.output.payload run.log).any (checkBindingWitness target) =
        true := by
  obtain ⟨hvalid, hfresh⟩ := Bool.and_eq_true_iff.mp h
  cases hfind : run.log.find? (fun entry => decide
      (target entry.1.message entry.1.opening =
        target run.output.payload.message run.output.payload.opening)) with
  | none =>
    refine Or.inl ?_
    have ht : target run.output.payload.message run.output.payload.opening ∉
        run.log.map (fun entry => target entry.1.message entry.1.opening) := fun hmem => by
      obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
      exact List.find?_eq_none.mp hfind entry hentry (decide_eq_true heq)
    simp [targetAccept, hvalid, ht]
  | some entry =>
    refine Or.inr ?_
    have hsame := List.find?_some hfind
    have hne : run.output.payload.message ≠ entry.1.message := fun hm =>
      of_decide_eq_true hfresh (List.mem_map.mpr ⟨entry, List.mem_of_find?_eq_some hfind, hm.symm⟩)
    simp [findBindingWitness, hfind, checkBindingWitness, hne, of_decide_eq_true hsame]

/-- Explicit extracted-witness composition: a fresh semantic authorization yields either a fresh
target certificate or two differently messaged openings to the same target. The success loss is
additive with coefficient one on both explicit reductions. This does not assert that either
right-hand game is hard for a particular target family. -/
theorem extracted_succProbability_le [DecidableEq Message] [DecidableEq Target] [Inhabited Sig]
    (S : Signature.Scheme PK SK Target Sig) (target : Message → Opening → Target)
    (A : ExtractedForger PK Message Opening Sig) :
    Experiment.succProbability (extractedExperiment S target A) ≤
      Experiment.succProbability (S.eufCmaExperiment (targetForger target A)) +
        Experiment.succProbability (bindingExperiment S target A) := by
  rw [targetExperiment_eq]
  simp only [extractedExperiment, bindingExperiment, bindingReduction,
    Experiment.succProbability, ProbComp.eval_map, PMF.map_comp, Function.comp_def,
    Game.succProbability, ← ENNReal.toNNReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  exact ENNReal.toNNReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩)
    (PMF.map_true_le_add _ fun run _ => extractedAccept_cases S target run)

end Cslib.Crypto.AnonymousToken
