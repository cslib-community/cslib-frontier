/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.AnonymousToken.Basic
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Credit
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunLog

/-!
# Clients of extracted anonymous-token certification and credit accounting

The client composes the existing signature interface with a commitment target. The deliberately
nonbinding target `message + opening` admits a semantic forgery by changing both summands; the
executable reduction must return its two openings. The credit client spends a refund-bearing
state and checks that a repeated nullifier is rejected.
-/

namespace CslibFrontierTests.Crypto.AnonymousToken

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken

private def certification : Signature.Scheme Unit Unit Nat Nat where
  keyGen := pure ((), ())
  sign _ target := pure target
  verify _ target signature := decide (target = signature)

private def target (message opening : Nat) : Nat := message + opening

private def changeOpening : ExtractedForger Unit Nat Nat Nat := fun _ => do
  let signature ← ProbOracleComp.query (⟨0, 1⟩ : Payload Nat Nat)
  return ⟨⟨1, 0⟩, signature⟩

-- The top-level reduction has no security premise about the reduced programs.
example :
    Experiment.succProbability (extractedExperiment certification target changeOpening) ≤
      Experiment.succProbability
        (certification.eufCmaExperiment (targetForger target changeOpening)) +
      Experiment.succProbability (bindingExperiment certification target changeOpening) :=
  extracted_succProbability_le certification target changeOpening

example (pk : Unit) : (targetForger target changeOpening pk).IsQueryBounded 1 :=
  targetForger_queryBound target changeOpening pk
    (ProbOracleComp.IsQueryBounded.query_bind_pure (⟨0, 1⟩ : Payload Nat Nat)
      fun signature => (⟨⟨1, 0⟩, signature⟩ : Token Nat Nat Nat))

example :
    extractedAccept certification target
      ⟨(), ⟨⟨1, 0⟩, 1⟩, [(⟨0, 1⟩, (1 : Nat))]⟩ = true := by decide

example :
    findBindingWitness target (⟨1, 0⟩ : Payload Nat Nat) [(⟨0, 1⟩, (1 : Nat))] =
      some ⟨⟨1, 0⟩, ⟨0, 1⟩⟩ := by decide

example : checkBindingWitness target (⟨⟨1, 0⟩, ⟨0, 1⟩⟩ : BindingWitness Nat Nat) = true :=
  by decide

-- The same signature interface supports a hidden selected issuer.
example (anchors : Fin 3 → Unit) (issuer : Fin 3) :
    selectedIssuerRelation certification target anchors 1 ⟨issuer, 0, 1⟩ = true := by
  simp [selectedIssuerRelation, certification, target]

-- ACT's two-stage target encoder composes directly with the same extracted-state reduction.
/-- The ACT target constructor feeds the public extracted-state reduction through ordinary
module imports; neither hidden implementation helpers nor a reduced-advantage premise are used. -/
public theorem act_extracted_reduction {PK SK NF Context Opening Commitment Target Sig : Type}
    [DecidableEq NF] [DecidableEq Context] [DecidableEq Target] [Inhabited Sig]
    (S : Signature.Scheme PK SK Target Sig)
    (commit : NF → Context → Nat → Opening → Commitment) (tag : Commitment → Nat → Target)
    (A : ExtractedForger PK (Credit.Note NF Context) Opening Sig) :
    Experiment.succProbability (extractedExperiment S (Credit.target commit tag) A) ≤
      Experiment.succProbability
        (S.eufCmaExperiment (targetForger (Credit.target commit tag) A)) +
      Experiment.succProbability (bindingExperiment S (Credit.target commit tag) A) :=
  extracted_succProbability_le S (Credit.target commit tag) A

private def initialNote : Credit.Note Nat Unit := ⟨7, (), 10, 2⟩

private def funded : Credit.Ledger Nat Unit := Credit.Ledger.empty.fund initialNote

private def afterSpend : Credit.Ledger Nat Unit :=
  { available := [⟨8, (), 7, 3⟩]
    spent := [7]
    granted := 15
    paid := 5 }

example : (Credit.Ledger.empty : Credit.Ledger Nat Unit).Conserves := by simp

example : funded.spend initialNote 8 5 3 = some afterSpend := by decide

example : afterSpend.Conserves := by decide

example : afterSpend.spend initialNote 9 1 0 = none := by decide

-- Even an explicitly funded state with a spent nullifier cannot be spent again.
example : (afterSpend.fund initialNote).spend initialNote 9 1 0 = none := by decide

/-- The public spending invariant and payout bound compose after ordinary module imports. -/
public theorem conserving_spend_paid_le_granted {NF Context : Type}
    [DecidableEq NF] [DecidableEq Context]
    (ledger next : Credit.Ledger NF Context) (old : Credit.Note NF Context)
    (nextNullifier : NF) (debit refund : Nat)
    (hledger : ledger.Conserves)
    (hstep : ledger.spend old nextNullifier debit refund = some next) :
    next.paid ≤ next.granted :=
  (Credit.Ledger.spend_conserves hledger hstep).paid_le_granted

end CslibFrontierTests.Crypto.AnonymousToken
