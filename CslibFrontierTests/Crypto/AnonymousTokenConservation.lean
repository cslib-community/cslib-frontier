/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module

import CslibFrontier.Crypto.Protocols.AnonymousToken.Conservation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunLog
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Regressions and clients for extracted single-issuer VOLE-ACT credit conservation

Exercises `Cslib.Crypto.AnonymousToken.Conservation` through an ordinary module import:
* an honest issuance-and-spend transcript satisfying conservation and rejecting double spends, plus
  per-context nullifier scoping;
* Part I (`spentDebit_le_of_certified`) on an honest trace, with its balance premise from
  `balance_of_validTrace`, an out-of-order trace where a spend precedes the issuance of its input
  note, and a duplicate-issuance trace exercising deduplication;
* the 64-bit modular wraparound and nullifier-reuse regressions, evaluating
  `extractedConservationAccept` on hand-built executions (`t = 0, x = 0, d = 1, t' = 2^64 - 1`
  under mod-`2^64` `(V3)`, and repeating `spendOne` without nullifier tracking);
* end-to-end losing adversaries through the oracle (`honestAdversary` and `doubleSpendAdversary`),
  including verifying that the second spend is answered `none` and not logged;
* concrete forging and commitment-collision adversaries instantiating `noteForger`,
  `extractedExperiment`, `targetForger`, `bindingExperiment`, `commitmentBindingReduction`,
  `noteForger_queryBound`, `targetForger_queryBound`, `checkBindingWitness_prod_mk_iff`, and
  `bindingExperiment_prod_mk_le_commitment`, showing that each term of the
  `extractedConservationExperiment_succProbability_le` bound can be `1`;
* generic `example`s applying `acceptLocal_of_validTrace`,
  `nodup_spends_of_validTrace`, `spentDebit_le_of_certified`,
  `extractedConservationExperiment_succProbability_le_extractedExperiment`,
  `runExtractedConservation_log_length_le`, the composed query bound, and
  `extractedConservationExperiment_succProbability_le_prod_mk` at the keyless scheme `comScheme`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.AnonymousTokenConservation

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken Cslib.Crypto.AnonymousToken.Conservation

/-- Deterministic injective commitment `(nf, ctx, credit)` ignoring opening randomness. -/
private def testCom (nf ctx t _r : ℕ) : ℕ × ℕ × ℕ := (nf, ctx, t)

/-- Deterministic trivial certifier signing a message with itself. -/
private def testSig : Signature.Scheme Unit Unit ((ℕ × ℕ × ℕ) × ℕ) ((ℕ × ℕ × ℕ) × ℕ) where
  keyGen := pure ((), ())
  sign _ msg := pure msg
  verify _ msg sig := decide (msg = sig)

private def issue0 : IssueRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) :=
  { ctx := 1, amount := 10, commitment := (1, 1, 10), nullifier := 1, opening := 0 }

private def spend1 : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
  { ctx := 1
    nullifier := 1
    debit := 4
    refund := 2
    changeCommitment := (2, 1, 6)
    oldCredit := 10
    oldOpening := 0
    oldRefund := 0
    signature := ((1, 1, 10), 0)
    newNullifier := 2
    newCredit := 6
    newOpening := 0 }

private def spend2 : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
  { ctx := 1
    nullifier := 2
    debit := 7
    refund := 0
    changeCommitment := (3, 1, 1)
    oldCredit := 6
    oldOpening := 0
    oldRefund := 2
    signature := ((2, 1, 6), 2)
    newNullifier := 3
    newCredit := 1
    newOpening := 0 }

private def honestTrace : List (Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ)) :=
  [.issue issue0, .spend spend1, .spend spend2]

private def honestExecution :
    ExtractedConservationExecution ℕ ℕ ℕ (ℕ × ℕ × ℕ) Unit ((ℕ × ℕ × ℕ) × ℕ) :=
  { publicKey := ()
    targetCtx := 1
    log := honestTrace.map fun r => (r, some (r.signedMessage Prod.mk)) }

-- Honest transcript passes trace verification and satisfies credit conservation: 11 ≤ 10 + 2.
example : validTrace testCom Prod.mk testSig () honestTrace = true := by decide
example : spentDebit honestTrace 1 = 11 := by decide
example : issuedAmount honestTrace 1 = 10 := by decide
example : grantedRefund honestTrace 1 = 2 := by decide
example : extractedConservationAccept honestExecution = false := by decide

-- Concrete Part I client on `honestTrace`: both trace invariants feed Part I.
example : spentDebit honestTrace 1 ≤ issuedAmount honestTrace 1 + grantedRefund honestTrace 1 :=
  have h : validTrace testCom Prod.mk testSig () honestTrace = true := by decide
  spentDebit_le_of_certified honestTrace (balance_of_validTrace h) (nodup_spends_of_validTrace h)
    (by decide) 1

-- Order-independence Part I client: `spend1` appears before `issue0` (the creator of its input
-- note), verified directly without `validTrace`.
private def outOfOrderTrace : List (Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ)) :=
  [.spend spend1, .issue issue0, .spend spend2]

example :
    spentDebit outOfOrderTrace 1 ≤
      issuedAmount outOfOrderTrace 1 + grantedRefund outOfOrderTrace 1 :=
  spentDebit_le_of_certified outOfOrderTrace (by decide) (by decide) (by decide) 1

-- Duplicate-issuance Part I client: issuing `issue0` twice creates duplicate output notes in
-- `outList`, exercising deduplication (`List.dedup_sublist`) in `spentDebit_le_of_certified`.
private def dupIssueTrace : List (Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ)) :=
  [.issue issue0, .issue issue0, .spend spend1, .spend spend2]

example : validTrace testCom Prod.mk testSig () dupIssueTrace = true := by decide
example : issuedAmount dupIssueTrace 1 = 20 := by decide
example : spentDebit dupIssueTrace 1 = 11 := by decide
example :
    spentDebit dupIssueTrace 1 ≤ issuedAmount dupIssueTrace 1 + grantedRefund dupIssueTrace 1 :=
  spentDebit_le_of_certified dupIssueTrace (by decide) (by decide) (by decide) 1

-- Reusing nullifier `1` in the same context `1` is rejected by `acceptRequest`.
private def doubleSpendSameCtx : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
  { ctx := 1
    nullifier := 1
    debit := 1
    refund := 0
    changeCommitment := (4, 1, 9)
    oldCredit := 10
    oldOpening := 0
    oldRefund := 0
    signature := ((1, 1, 10), 0)
    newNullifier := 4
    newCredit := 9
    newOpening := 0 }

example :
    acceptRequest testCom Prod.mk testSig () honestTrace (.spend doubleSpendSameCtx) = false := by
  decide

-- Nullifier uniqueness is scoped per context: `nf = 1` may still be issued and spent in `ctx = 2`.
private def issueCtx2 : IssueRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) :=
  { ctx := 2, amount := 5, commitment := (1, 2, 5), nullifier := 1, opening := 0 }

private def spendCtx2 : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
  { ctx := 2
    nullifier := 1
    debit := 5
    refund := 0
    changeCommitment := (2, 2, 0)
    oldCredit := 5
    oldOpening := 0
    oldRefund := 0
    signature := ((1, 2, 5), 0)
    newNullifier := 2
    newCredit := 0
    newOpening := 0 }

example :
    validTrace testCom Prod.mk testSig () (honestTrace ++ [.issue issueCtx2, .spend spendCtx2]) =
      true := by
  decide

/-! ### Regression 1: 64-bit modular wraparound in `(V3)` -/

/-- Broken per-request check replacing `ℕ` balance conservation `(V3)` with mod-`2^64` equality. -/
private def acceptLocalMod64 {Nullifier Context Opening Commitment Target PK SK Sig : Type}
    [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK) :
    Request Nullifier Context Opening Commitment Sig → Bool
  | .issue req => decide (com req.nullifier req.ctx req.amount req.opening = req.commitment)
  | .spend req =>
      S.verify pk (Credit.target com tag req.inputNote req.oldOpening) req.signature &&
      decide (com req.newNullifier req.ctx req.newCredit req.newOpening = req.changeCommitment) &&
      decide ((req.oldCredit + req.oldRefund) % 2 ^ 64 = (req.newCredit + req.debit) % 2 ^ 64)

private def issueZero : IssueRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) :=
  { ctx := 1, amount := 0, commitment := (10, 1, 0), nullifier := 10, opening := 0 }

private def wraparoundSpend : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
  { ctx := 1
    nullifier := 10
    debit := 1
    refund := 0
    changeCommitment := (11, 1, 2 ^ 64 - 1)
    oldCredit := 0
    oldOpening := 0
    oldRefund := 0
    signature := ((10, 1, 0), 0)
    newNullifier := 11
    newCredit := 2 ^ 64 - 1
    newOpening := 0 }

private def wraparoundTrace : List (Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ)) :=
  [.issue issueZero, .spend wraparoundSpend]

-- Under mod-2^64 V3, the single spend with t=0, x=0, d=1, t'=2^64-1 is accepted and violates
-- conservation (`spentDebit = 1 > 0 = issuedAmount + grantedRefund`). Evaluated on a hand-built
-- execution matching the accepted trace.
example : acceptLocalMod64 testCom Prod.mk testSig () (.spend wraparoundSpend) = true := by decide
example : wraparoundTrace.all (acceptLocalMod64 testCom Prod.mk testSig ()) = true := by decide
example : acceptLocal testCom Prod.mk testSig () (.spend wraparoundSpend) = false := by decide
example :
    extractedConservationAccept
        ⟨(), 1, wraparoundTrace.map fun r => (r, some (r.signedMessage Prod.mk))⟩ =
      true := by
  decide

/-! ### Regression 2: Nullifier reuse without the spent-nullifier check -/

private def issueOne : IssueRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) :=
  { ctx := 1, amount := 1, commitment := (20, 1, 1), nullifier := 20, opening := 0 }

private def spendOne : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
  { ctx := 1
    nullifier := 20
    debit := 1
    refund := 0
    changeCommitment := (21, 1, 0)
    oldCredit := 1
    oldOpening := 0
    oldRefund := 0
    signature := ((20, 1, 1), 0)
    newNullifier := 21
    newCredit := 0
    newOpening := 0 }

private def doubleSpendTrace : List (Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ)) :=
  [.issue issueOne, .spend spendOne, .spend spendOne]

-- Every request satisfies `acceptLocal` and has a certified input note (`findNoteForgery = none`),
-- yet omitting the nullifier check violates conservation (`spentDebit = 2 > 1 = issuedAmount`).
-- Evaluated on a hand-built execution representing a trace without nullifier tracking.
example : doubleSpendTrace.all (acceptLocal testCom Prod.mk testSig ()) = true := by decide
example : findNoteForgery doubleSpendTrace = none := by decide
example : validTrace testCom Prod.mk testSig () doubleSpendTrace = false := by decide
example :
    extractedConservationAccept
        ⟨(), 1, doubleSpendTrace.map fun r => (r, some (r.signedMessage Prod.mk))⟩ =
      true := by
  decide

/-! ### End-to-end losing adversaries through the oracle -/

/-- Honest adversary issuing `issue0`, spending with `spend1`, then spending with `spend2`. -/
private def honestAdversary :
    ExtractedAdversary ℕ ℕ ℕ (ℕ × ℕ × ℕ) Unit ((ℕ × ℕ × ℕ) × ℕ) := fun _ => do
  let sig0? ← ProbOracleComp.query (.issue issue0)
  let s1 : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
    { spend1 with signature := sig0?.getD ((0, 0, 0), 0) }
  let sig1? ← ProbOracleComp.query (.spend s1)
  let s2 : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
    { spend2 with signature := sig1?.getD ((0, 0, 0), 0) }
  let _ ← ProbOracleComp.query (.spend s2)
  return 1

example :
    Experiment.succProbability
        (extractedConservationExperiment testCom Prod.mk testSig honestAdversary) =
      0 := by
  simp [extractedConservationExperiment, runExtractedConservation, ProbOracleComp.runLogWith,
    honestAdversary, extractedIssuerOracle, acceptRequest, acceptLocal, hasSpentNullifier,
    SpendRequest.inputNote, Credit.target, Request.signedMessage, issue0, spend1, spend2,
    testCom, testSig, extractedConservationAccept, spentDebit, spendsIn, spends, issuedAmount,
    issuesIn, grantedRefund, Experiment.succProbability, Game.succProbability]

/-- Double-spending adversary attempting to spend `(1, 20)` twice after issuing `issueOne`. -/
private def doubleSpendAdversary :
    ExtractedAdversary ℕ ℕ ℕ (ℕ × ℕ × ℕ) Unit ((ℕ × ℕ × ℕ) × ℕ) := fun _ => do
  let sig0? ← ProbOracleComp.query (.issue issueOne)
  let s : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
    { spendOne with signature := sig0?.getD ((0, 0, 0), 0) }
  let _ ← ProbOracleComp.query (.spend s)
  let _ ← ProbOracleComp.query (.spend s)
  return 1

/-- Probe variant returning the second spend reply `r2` to observe refusal directly. -/
private def doubleSpendReplyProbe :
    ProbOracleComp (fun _ : Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) =>
      Option ((ℕ × ℕ × ℕ) × ℕ)) (Option ((ℕ × ℕ × ℕ) × ℕ)) := do
  let sig0? ← ProbOracleComp.query (.issue issueOne)
  let s : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
    { spendOne with signature := sig0?.getD ((0, 0, 0), 0) }
  let _ ← ProbOracleComp.query (.spend s)
  ProbOracleComp.query (.spend s)

example :
    Experiment.succProbability
        (extractedConservationExperiment testCom Prod.mk testSig doubleSpendAdversary) =
      0 := by
  simp [extractedConservationExperiment, runExtractedConservation, ProbOracleComp.runLogWith,
    doubleSpendAdversary, extractedIssuerOracle, acceptRequest, acceptLocal, hasSpentNullifier,
    SpendRequest.inputNote, Credit.target, Request.signedMessage, issueOne, spendOne,
    testCom, testSig, extractedConservationAccept, spentDebit, spendsIn, spends, issuedAmount,
    issuesIn, grantedRefund, Experiment.succProbability, Game.succProbability]

-- The second spend receives `none` and is omitted from the accepted log (only 2 entries logged).
example :
    ProbComp.eval
        (doubleSpendReplyProbe.runLogWith
          (extractedIssuerOracle testCom Prod.mk testSig ((), ()))) =
      PMF.pure
        (none,
          [(Request.issue issueOne,
              some ((Request.issue (Sig := (ℕ × ℕ × ℕ) × ℕ) issueOne).signedMessage Prod.mk)),
           (Request.spend spendOne,
              some ((Request.spend spendOne).signedMessage Prod.mk))]) := by
  have hdef : (default : Option ((ℕ × ℕ × ℕ) × ℕ)) = none := rfl
  simp [ProbOracleComp.runLogWith, doubleSpendReplyProbe, extractedIssuerOracle, acceptRequest,
    acceptLocal, hasSpentNullifier, SpendRequest.inputNote, Credit.target, Request.signedMessage,
    issueOne, spendOne, testCom, testSig, hdef]

example :
    ProbComp.eval (runExtractedConservation testCom Prod.mk testSig doubleSpendAdversary) =
      PMF.pure
        ⟨(), 1,
          [(Request.issue issueOne,
              some ((Request.issue (Sig := (ℕ × ℕ × ℕ) × ℕ) issueOne).signedMessage Prod.mk)),
           (Request.spend spendOne,
              some ((Request.spend spendOne).signedMessage Prod.mk))]⟩ := by
  simp [runExtractedConservation, ProbOracleComp.runLogWith, doubleSpendAdversary,
    extractedIssuerOracle, acceptRequest, acceptLocal, hasSpentNullifier, SpendRequest.inputNote,
    Credit.target, Request.signedMessage, issueOne, spendOne, testCom, testSig]

/-! ### Nonvacuity and reduction checks -/

/-- Evaluation of `noteForger` on a single-query-then-return adversary. -/
private theorem noteForger_query_bind_pure
    {Nullifier Context Opening Commitment Target PK SK Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK)
    (req : Request Nullifier Context Opening Commitment Sig) (outCtx : Context) :
    noteForger com tag S (fun _ => ProbOracleComp.query req >>= fun _ => pure outCtx) pk =
      if acceptRequest com tag S pk [] req then do
        let _ ← ProbOracleComp.query req.outputPayload
        return (findNoteForgery [req]).getD ⟨⟨⟨default, default, 0, 0⟩, default⟩, default⟩
      else
        pure
          ((findNoteForgery ([] : List (Request Nullifier Context Opening Commitment Sig))).getD
            ⟨⟨⟨default, default, 0, 0⟩, default⟩, default⟩) := by
  simp only [noteForger, ProbOracleComp.query, OracleComp.interpret_bind,
    OracleComp.interpret_query, OracleComp.interpret_pure, OracleComp.sumHandler]
  simp only [StateT.run_bind, StateT.run_pure]
  simp only [StateT.run, noteForgerHandler]
  split_ifs
  · simp [ProbOracleComp.query]
  · simp

/-- Forged spend request used by `forgingAdversary`. -/
private def forgedSpend : SpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) where
  ctx := 1
  nullifier := 1
  debit := 5
  refund := 0
  changeCommitment := (2, 1, 0)
  oldCredit := 5
  oldOpening := 0
  oldRefund := 0
  signature := ((1, 1, 5), 0)
  newNullifier := 2
  newCredit := 0
  newOpening := 0

/-- A 1-query forging adversary fabricating a signature on an unissued note and spending it. -/
private def forgingAdversary :
    ExtractedAdversary ℕ ℕ ℕ (ℕ × ℕ × ℕ) Unit ((ℕ × ℕ × ℕ) × ℕ) := fun _ => do
  let _ ← ProbOracleComp.query (.spend forgedSpend)
  return 1

private theorem noteForger_forgingAdversary :
    noteForger testCom Prod.mk testSig forgingAdversary () = do
      let _ ← ProbOracleComp.query (Request.spend forgedSpend).outputPayload
      return (findNoteForgery [Request.spend forgedSpend]).getD
        ⟨⟨⟨default, default, 0, 0⟩, default⟩, default⟩ := by
  unfold forgingAdversary
  simpa [acceptRequest, acceptLocal, hasSpentNullifier, SpendRequest.inputNote,
    Credit.target, testCom, testSig, forgedSpend] using
    noteForger_query_bind_pure testCom Prod.mk testSig () (.spend forgedSpend) 1

example : (noteForger testCom Prod.mk testSig forgingAdversary ()).IsQueryBounded 1 :=
  noteForger_queryBound testCom Prod.mk testSig forgingAdversary ()
    (ProbOracleComp.IsQueryBounded.query_bind_pure _ _)

example :
    (targetForger (Credit.target testCom Prod.mk)
      (noteForger testCom Prod.mk testSig forgingAdversary) ()).IsQueryBounded 1 :=
  targetForger_queryBound _ _ ()
    (noteForger_queryBound testCom Prod.mk testSig forgingAdversary ()
      (ProbOracleComp.IsQueryBounded.query_bind_pure _ _))

example :
    Experiment.succProbability
        (extractedConservationExperiment testCom Prod.mk testSig forgingAdversary) =
      1 := by
  simp [extractedConservationExperiment, runExtractedConservation, ProbOracleComp.runLogWith,
    forgingAdversary, forgedSpend, extractedIssuerOracle, acceptRequest, acceptLocal,
    hasSpentNullifier, SpendRequest.inputNote, Credit.target, testCom, testSig,
    extractedConservationAccept, spentDebit, spendsIn, spends, issuedAmount, issuesIn,
    grantedRefund, Experiment.succProbability, Game.succProbability]

example :
    Experiment.succProbability
      (extractedExperiment testSig (Credit.target testCom Prod.mk)
        (noteForger testCom Prod.mk testSig forgingAdversary)) = 1 := by
  have heval :
      ProbComp.eval
          (extractedExperiment testSig (Credit.target testCom Prod.mk)
            (noteForger testCom Prod.mk testSig forgingAdversary)) =
        PMF.pure true := by
    simp only [extractedExperiment, ProbComp.eval_map, runExtracted]
    rw [show testSig.keyGen = pure ((), ()) from rfl]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
    rw [noteForger_forgingAdversary, ← ProbOracleComp.runLogWith_some]
    simp [ProbOracleComp.runLogWith, testSig, Request.outputPayload, findNoteForgery, spends,
      SpendRequest.inputNote, SpendRequest.inputPayload, extractedAccept, Token.valid,
      Credit.target, testCom, forgedSpend]
  simp [Experiment.succProbability, Game.succProbability, heval]

example :
    Experiment.succProbability
      (testSig.eufCmaExperiment
        (targetForger (Credit.target testCom Prod.mk)
          (noteForger testCom Prod.mk testSig forgingAdversary))) = 1 := by
  have heval :
      ProbComp.eval
          (testSig.eufCmaExperiment
            (targetForger (Credit.target testCom Prod.mk)
              (noteForger testCom Prod.mk testSig forgingAdversary))) =
        PMF.pure true := by
    simp only [Signature.Scheme.eufCmaExperiment, forgeExperiment, targetForger]
    rw [show testSig.keyGen = pure ((), ()) from rfl]
    simp only [ProbOracleComp.runLogWith_map, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_map, PMF.pure_bind]
    rw [noteForger_forgingAdversary]
    simp [ProbOracleComp.runLogWith, Signer.ofSign, testSig, Request.outputPayload,
      findNoteForgery, spends, SpendRequest.inputNote, SpendRequest.inputPayload, Credit.target,
      testCom, freshMessage, forgedSpend]
  simp [Experiment.succProbability, Game.succProbability, heval]

/-- Constant non-binding commitment `fun _ _ _ _ => ()`. -/
private def constCom (_nf _ctx _t _r : ℕ) : Unit := ()

private def constSig : Signature.Scheme Unit Unit (Unit × ℕ) (Unit × ℕ) where
  keyGen := pure ((), ())
  sign _ msg := pure msg
  verify _ msg sig := decide (msg = sig)

/-- Keyless `Cslib.Crypto.Commitment.Scheme` induced by a deterministic `com` function. -/
private def comScheme
    {Nullifier Context Opening Commitment : Type} [DecidableEq Commitment] [Inhabited Opening]
    (com : Nullifier → Context → ℕ → Opening → Commitment) :
    Crypto.Commitment.Scheme Unit (Nullifier × Context × ℕ) Commitment Opening where
  keyGen := pure ()
  commit _ := fun ⟨nf, ctx, t⟩ => pure (com nf ctx t default, default)
  verify _ := fun ⟨nf, ctx, t⟩ c o => decide (com nf ctx t o = c)

/-- A 2-query adversary breaking credit conservation by colliding a `T = 0` issue with a
`t = 5` spend under the constant non-binding commitment `constCom`. -/
private def collidingAdversary :
    ExtractedAdversary ℕ ℕ ℕ Unit Unit (Unit × ℕ) := fun _ => do
  let sig? ← ProbOracleComp.query (.issue
    { ctx := 1, amount := 0, commitment := (), nullifier := 1, opening := 0 })
  let sig := sig?.getD ((), 0)
  let _ ← ProbOracleComp.query (.spend
    { ctx := 1, nullifier := 2, debit := 5, refund := 0, changeCommitment := (),
      oldCredit := 5, oldOpening := 0, oldRefund := 0, signature := sig,
      newNullifier := 3, newCredit := 0, newOpening := 0 })
  return 1

example :
    Experiment.succProbability
      (extractedConservationExperiment constCom Prod.mk constSig collidingAdversary) = 1 := by
  simp [extractedConservationExperiment, runExtractedConservation, ProbOracleComp.runLogWith,
    collidingAdversary, extractedIssuerOracle, acceptRequest, acceptLocal, hasSpentNullifier,
    SpendRequest.inputNote, Request.signedMessage, Credit.target, constCom, constSig,
    extractedConservationAccept, spentDebit, spendsIn, spends, issuedAmount, issuesIn,
    grantedRefund, Experiment.succProbability, Game.succProbability]

private theorem bindingExperiment_constCom_eq_one :
    Experiment.succProbability
      (bindingExperiment constSig (Credit.target constCom Prod.mk)
        (noteForger constCom Prod.mk constSig collidingAdversary)) = 1 := by
  have heval :
      ProbComp.eval
          (bindingExperiment constSig (Credit.target constCom Prod.mk)
            (noteForger constCom Prod.mk constSig collidingAdversary)) =
        PMF.pure true := by
    simp only [bindingExperiment, bindingReduction, runExtracted, constSig, ProbComp.eval_map,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
    rw [← ProbOracleComp.runLogWith_some, ProbOracleComp.runLogWith, ProbOracleComp.eval_runState]
    simp only [noteForger, collidingAdversary, ProbOracleComp.query,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_pure, OracleComp.interpret_bind,
      OracleComp.interpret_query, OracleComp.interpret_pure, OracleComp.sumHandler,
      StateT.run_bind, StateT.run_pure, ProbOracleComp.logOracle]
    simp [StateT.run, noteForgerHandler, acceptRequest, acceptLocal, hasSpentNullifier,
      SpendRequest.inputNote, SpendRequest.inputPayload, Request.outputPayload,
      findNoteForgery, spends, findBindingWitness, checkBindingWitness, Credit.target, constCom,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
  simp [Experiment.succProbability, Game.succProbability, heval]

example :
    Experiment.succProbability
      ((comScheme constCom).bindingExperiment
        (commitmentBindingReduction constCom constSig collidingAdversary)) = 1 := by
  refine le_antisymm (Game.succProbability_le_one _) ?_
  calc (1 : NNReal)
      = Experiment.succProbability
          (bindingExperiment constSig (Credit.target constCom Prod.mk)
            (noteForger constCom Prod.mk constSig collidingAdversary)) :=
        bindingExperiment_constCom_eq_one.symm
    _ ≤ Experiment.succProbability
          ((comScheme constCom).bindingExperiment
            (commitmentBindingReduction constCom constSig collidingAdversary)) :=
        bindingExperiment_prod_mk_le_commitment constCom (comScheme constCom)
          (fun _ _ _ _ _ _ => rfl) constSig collidingAdversary

-- Witness check on the colliding pair: equal refunds (`0`), distinct `(nf, ctx, credit)`
-- triples (`(2, 1, 5) ≠ (1, 1, 0)`), and equal `constCom` commitments.
example :
    let w : BindingWitness (Credit.Note ℕ ℕ) ℕ :=
      ⟨⟨⟨2, 1, 5, 0⟩, 0⟩, ⟨⟨1, 1, 0, 0⟩, 0⟩⟩
    checkBindingWitness (Credit.target constCom Prod.mk) w = true ∧
      w.first.message.refund = w.second.message.refund ∧
      (w.first.message.nullifier, w.first.message.context, w.first.message.credit) ≠
        (w.second.message.nullifier, w.second.message.context, w.second.message.credit) ∧
      constCom w.first.message.nullifier w.first.message.context w.first.message.credit
          w.first.opening =
        constCom w.second.message.nullifier w.second.message.context w.second.message.credit
          w.second.opening := by
  intro w
  exact ⟨by decide, (checkBindingWitness_prod_mk_iff constCom w).mp (by decide)⟩

/-! ### Generic clients through an ordinary import -/

-- `acceptLocal_of_validTrace` and `nodup_spends_of_validTrace` on an arbitrary accepted trace.
example {Nullifier Context Opening Commitment Target PK SK Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK)
    (reqs : List (Request Nullifier Context Opening Commitment Sig))
    (h : validTrace com tag S pk reqs = true) :
    (∀ r ∈ reqs, Conservation.acceptLocal com tag S pk r = true) ∧
      ((spends reqs).map fun s => (s.ctx, s.nullifier)).Nodup :=
  ⟨acceptLocal_of_validTrace h, nodup_spends_of_validTrace h⟩

-- Part I needs only the balance equations, distinct spent pairs and certified inputs: no
-- commitment, tag or certifier appears in its statement.
example {Nullifier Context Opening Commitment Sig : Type} [DecidableEq Context]
    (reqs : List (Request Nullifier Context Opening Commitment Sig))
    (hbalance : ∀ s ∈ spends reqs, s.oldCredit + s.oldRefund = s.newCredit + s.debit)
    (hnodup : ((spends reqs).map fun s => (s.ctx, s.nullifier)).Nodup)
    (hcertified : ∀ s ∈ spends reqs, s.inputNote ∈ reqs.map (fun r => r.outputPayload.message))
    (ctx : Context) :
    spentDebit reqs ctx ≤ issuedAmount reqs ctx + grantedRefund reqs ctx :=
  spentDebit_le_of_certified reqs hbalance hnodup hcertified ctx

-- The coupling `extractedConservationExperiment_succProbability_le_extractedExperiment`.
example {Nullifier Context Opening Commitment Target PK SK Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) :
    Experiment.succProbability (extractedConservationExperiment com tag S A) ≤
      Experiment.succProbability
        (extractedExperiment S (Credit.target com tag) (noteForger com tag S A)) :=
  extractedConservationExperiment_succProbability_le_extractedExperiment com tag S A

-- `runExtractedConservation_log_length_le`: a `q`-query adversary logs at most `q` requests.
example {Nullifier Context Opening Commitment Target PK SK Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) {q : ℕ}
    (hA : ∀ pk, (A pk).IsQueryBounded q)
    {run : ExtractedConservationExecution Nullifier Context Opening Commitment PK Sig}
    (hrun : run ∈ (ProbComp.eval (runExtractedConservation com tag S A)).support) :
    run.log.length ≤ q :=
  runExtractedConservation_log_length_le com tag S A hA hrun

-- `extractedConservationExperiment_succProbability_le_prod_mk` instantiated with the concrete
-- keyless commitment scheme `comScheme com`.
example {Nullifier Context Opening Commitment PK SK Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (S : Signature.Scheme PK SK (Commitment × ℕ) Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) :
    Experiment.succProbability (extractedConservationExperiment com Prod.mk S A) ≤
      Experiment.succProbability
          (S.eufCmaExperiment
            (targetForger (Credit.target com Prod.mk) (noteForger com Prod.mk S A))) +
        Experiment.succProbability
          ((comScheme com).bindingExperiment (commitmentBindingReduction com S A)) :=
  extractedConservationExperiment_succProbability_le_prod_mk
    com (comScheme com) (fun _ _ _ _ _ _ => rfl) S A

-- `targetForger` on `noteForger` makes at most `q` signing queries for a `q`-query adversary,
-- composing `noteForger_queryBound` with `targetForger_queryBound`.
example {Nullifier Context Opening Commitment Target PK SK Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (A : ExtractedAdversary Nullifier Context Opening Commitment PK Sig) (pk : PK) {q : ℕ}
    (hA : (A pk).IsQueryBounded q) :
    (targetForger (Credit.target com tag) (noteForger com tag S A) pk).IsQueryBounded q :=
  targetForger_queryBound _ _ pk (noteForger_queryBound com tag S A pk hA)

end CslibFrontierTests.Crypto.AnonymousTokenConservation
