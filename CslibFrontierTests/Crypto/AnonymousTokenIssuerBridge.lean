/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import CslibFrontier.Crypto.Protocols.AnonymousToken.IssuerBridge

/-!
# Regressions and clients for the VOLE-ACT draft issuer bridge

Exercises `Cslib.Crypto.AnonymousToken.IssuerBridge` through an ordinary import:
* positive oracle execution (`draftIssuerOracle` accepting `.agreeIssue`, `.issue`, and `.spend`),
  policy declines (`none`), `T = 0` and `T ≥ bound` rejections, and ticket single-use enforcement;
* isolated range checks on `(d, t, x, t', x')` where `(V1)`–`(V3)` and nullifier freshness pass
  (`Conservation.acceptRequest = true`) yet `draftIssuerOracle` rejects solely via range guards;
* double-spend rejection, an end-to-end honest stateful transcript verifying `x' = 1` then `2` and
  conservation (`succProbability = 0`), a winning `forgingAdversary` (`succProbability = 1`), and
  a probabilistic policy (`randPolicy`) granting refunds `1` and `2` with probability `1 / 2` each;
* concrete compositions of `bridgeAdversary_queryBound`, `Conservation.noteForger_queryBound`,
  `targetForger_queryBound`, and
  `extractedDraftConservationExperiment_succProbability_le_prod_mk` at a keyless commitment
  scheme `comScheme`;
* the `L = 8` (`bound = 2 ^ 64`) carry-bit boundary and `T = 1 → 0 → 2 ^ 64 - 1` wraparound
  separation, instantiating `eq_iff_mod_eq_and_testBit_eq` and `wraparound_gap_of_mod_eq_ne`
  and separating `extractedDraftConservationExperiment` (probability `0`) from a mod-`2 ^ 64`
  `(V3)` issuer (probability `1`).
-/

namespace CslibFrontierTests.Crypto.AnonymousTokenIssuerBridge

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken Cslib.Crypto.AnonymousToken.IssuerBridge

/-- Deterministic injective commitment `(nf, ctx, credit)` ignoring opening randomness. -/
private def testCom (nf ctx t _r : ℕ) : ℕ × ℕ × ℕ := (nf, ctx, t)

/-- Deterministic trivial certifier signing a message with itself. -/
private def testSig : Signature.Scheme Unit Unit ((ℕ × ℕ × ℕ) × ℕ) ((ℕ × ℕ × ℕ) × ℕ) where
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

/-- Deterministic stateful policy:
* `hint = 0` declines issuance (`none`);
* `hint = 1` proposes `T = 0` (to test the `1 ≤ T` guard in `.issue`);
* `hint = 2` proposes `T = 100` (to test `T < bound` when `bound = 16`);
* any other `hint` proposes `T = hint`.
For refunds, `debit = 7` proposes `x' = 100` (to test `x' < bound`), state `99` declines (`none`),
and otherwise the issuer grants stateful `x' = st` and increments `st`. -/
private def detPolicy : IssuerPolicy ℕ ℕ ℕ (ℕ × ℕ × ℕ) ℕ where
  init := pure 0
  agreeIssue _ hint := fun st =>
    if hint = 0 then pure (none, st + 1)
    else if hint = 1 then pure (some 0, st + 1)
    else if hint = 2 then pure (some 100, st + 1)
    else pure (some hint, st + 1)
  chooseRefund _ _ debit _ := fun st =>
    if st = 99 then pure (none, st)
    else if debit = 7 then pure (some 100, st + 1)
    else pure (some st, st + 1)

private def issueValid : DraftIssueRequest ℕ ℕ (ℕ × ℕ × ℕ) :=
  { ticket := 0, commitment := (1, 1, 10), nullifier := 1, opening := 0 }

private def spendStep1 (sig : (ℕ × ℕ × ℕ) × ℕ) :
    DraftSpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
  { ctx := 1
    nullifier := 1
    debit := 4
    changeCommitment := (2, 1, 6)
    oldCredit := 10
    oldOpening := 0
    oldRefund := 0
    signature := sig
    newNullifier := 2
    newCredit := 6
    newOpening := 0 }

private def spendStep2 (sig : (ℕ × ℕ × ℕ) × ℕ) :
    DraftSpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
  { ctx := 1
    nullifier := 2
    debit := 5
    changeCommitment := (3, 1, 2)
    oldCredit := 6
    oldOpening := 0
    oldRefund := 1
    signature := sig
    newNullifier := 3
    newCredit := 2
    newOpening := 0 }

/-! ### Positive oracle behavior and policy/range/replay rejections -/

-- Policy decline (`hint = 0`) on `draftIssuerOracle` returns `none` and leaves `pending` unchanged.
example :
    let st0 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ := ⟨0, [], [], []⟩
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.agreeIssue 1 0)).run st0) =
      PMF.pure (none, ⟨1, [], [], []⟩) := by
  simp only [run_draftIssuerOracle_agreeIssue]
  simp [detPolicy, StateT.run]
  rfl

-- Positive witness: `.agreeIssue` (`hint = 10`) allocates ticket `0` and steps `policyState`.
example :
    let st0 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ := ⟨0, [], [], []⟩
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.agreeIssue 1 10)).run st0) =
      PMF.pure (some ⟨0, 10⟩, ⟨1, [⟨1, 10⟩], [], []⟩) := by
  simp only [run_draftIssuerOracle_agreeIssue]
  simp [detPolicy, StateT.run]
  rfl

-- Positive witness: `.issue` on a fresh valid ticket is accepted, signed, consumed, and logged.
example :
    let st1 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ := ⟨1, [⟨1, 10⟩], [], []⟩
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.issue issueValid)).run st1) =
      PMF.pure (some ((1, 1, 10), 0),
        ⟨1, [⟨1, 10⟩], [0], [.issue ⟨1, 10, (1, 1, 10), 1, 0⟩]⟩) := by
  simp only [run_draftIssuerOracle_issue]
  simp [acceptDraftIssue, issueValid, testCom, testSig, Conservation.Request.signedMessage]
  rfl

-- Positive witness: `.spend` passing the pre-check is accepted with stateful refund `2`.
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st1 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨2, [⟨1, 10⟩], [0], [creq]⟩
    let req := spendStep1 ((1, 1, 10), 0)
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.spend req)).run st1) =
      PMF.pure (some ⟨2, ((2, 1, 6), 2)⟩,
        ⟨3, [⟨1, 10⟩], [0], [creq, .spend (req.toSpendRequest 2)]⟩) := by
  simp only [run_draftIssuerOracle_spend]
  simp [acceptDraftSpendPre, DraftSpendRequest.withinRange, DraftSpendRequest.toSpendRequest,
    Conservation.acceptRequest, Conservation.acceptLocal, Conservation.hasSpentNullifier,
    Conservation.SpendRequest.inputNote, Credit.target, Conservation.Request.signedMessage,
    detPolicy, spendStep1, testCom, testSig, StateT.run]
  rfl

-- `T = 0` agreed via `hint = 1` is rejected by `.issue` (`none`) without consuming ticket `0`.
example :
    let st0 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ := ⟨1, [⟨1, 0⟩], [], []⟩
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.issue { ticket := 0, commitment := (1, 1, 0), nullifier := 1, opening := 0 })).run
          st0) =
      PMF.pure (none, st0) := by
  simp only [run_draftIssuerOracle_issue]
  simp [acceptDraftIssue, testCom]
  rfl

-- `T ≥ bound` (`T = 100`, `bound = 16`) agreed via `hint = 2` is rejected by `.issue`.
example :
    let st0 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ := ⟨1, [⟨1, 100⟩], [], []⟩
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.issue { ticket := 0, commitment := (1, 1, 100), nullifier := 1, opening := 0 })).run
          st0) =
      PMF.pure (none, st0) := by
  simp only [run_draftIssuerOracle_issue]
  simp [acceptDraftIssue, testCom]
  rfl

-- Ticket replay: once ticket `0` is in `st.consumed`, a second `.issue` on ticket `0` returns
-- `none` and leaves `accepted` unchanged.
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st1 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨1, [⟨1, 10⟩], [0], [creq]⟩
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.issue issueValid)).run st1) =
      PMF.pure (none, st1) := by
  simp only [run_draftIssuerOracle_issue]
  simp [acceptDraftIssue, issueValid, testCom]
  rfl

-- Isolated range check on `d = 16 ≥ bound`: `(V1)`–`(V3)` pass (`10 + 8 = 2 + 16`, with
-- `t, x, t' < 16`), so `Conservation.acceptRequest` accepts, yet `draftIssuerOracle` rejects.
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st1 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨5, [⟨1, 10⟩], [0], [creq]⟩
    let badD : DraftSpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      { ctx := 1, nullifier := 1, debit := 16, changeCommitment := (2, 1, 2), oldCredit := 10,
        oldOpening := 0, oldRefund := 8, signature := ((1, 1, 10), 8), newNullifier := 2,
        newCredit := 2, newOpening := 0 }
    Conservation.acceptRequest testCom Prod.mk testSig () [creq] (.spend (badD.toSpendRequest 0)) =
        true ∧
      ProbComp.eval
          ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
            (.spend badD)).run st1) =
        PMF.pure (none, st1) := by
  constructor
  · simp [DraftSpendRequest.toSpendRequest, Conservation.acceptRequest, Conservation.acceptLocal,
      Conservation.hasSpentNullifier, Conservation.SpendRequest.inputNote, Credit.target,
      testCom, testSig]
  · simp only [run_draftIssuerOracle_spend]
    simp [acceptDraftSpendPre, DraftSpendRequest.withinRange]
    rfl

-- Isolated range checks on `t = 16`, `x = 16`, and `t' = 16`: each satisfies
-- `Conservation.acceptRequest = true` (`16 + 0 = 12 + 4`, `10 + 16 = 14 + 12`, `10 + 8 = 16 + 2`)
-- while the other three fields are `< 16`, yet `draftIssuerOracle` rejects before `chooseRefund`.
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st1 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨5, [⟨1, 10⟩], [0], [creq]⟩
    let badT : DraftSpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      { ctx := 1, nullifier := 1, debit := 4, changeCommitment := (2, 1, 12), oldCredit := 16,
        oldOpening := 0, oldRefund := 0, signature := ((1, 1, 16), 0), newNullifier := 2,
        newCredit := 12, newOpening := 0 }
    let badX : DraftSpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      { ctx := 1, nullifier := 1, debit := 12, changeCommitment := (2, 1, 14), oldCredit := 10,
        oldOpening := 0, oldRefund := 16, signature := ((1, 1, 10), 16), newNullifier := 2,
        newCredit := 14, newOpening := 0 }
    let badT' : DraftSpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      { ctx := 1, nullifier := 1, debit := 2, changeCommitment := (2, 1, 16), oldCredit := 10,
        oldOpening := 0, oldRefund := 8, signature := ((1, 1, 10), 8), newNullifier := 2,
        newCredit := 16, newOpening := 0 }
    (Conservation.acceptRequest testCom Prod.mk testSig () [creq]
          (.spend (badT.toSpendRequest 0)) = true ∧
        ProbComp.eval
            ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
              (.spend badT)).run st1) =
          PMF.pure (none, st1)) ∧
      (Conservation.acceptRequest testCom Prod.mk testSig () [creq]
            (.spend (badX.toSpendRequest 0)) = true ∧
          ProbComp.eval
              ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
                (.spend badX)).run st1) =
            PMF.pure (none, st1)) ∧
      (Conservation.acceptRequest testCom Prod.mk testSig () [creq]
            (.spend (badT'.toSpendRequest 0)) = true ∧
          ProbComp.eval
              ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
                (.spend badT')).run st1) =
            PMF.pure (none, st1)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
    | (simp [DraftSpendRequest.toSpendRequest, Conservation.acceptRequest, Conservation.acceptLocal,
        Conservation.hasSpentNullifier, Conservation.SpendRequest.inputNote, Credit.target,
        testCom, testSig]; done)
    | (simp only [run_draftIssuerOracle_spend];
        simp [acceptDraftSpendPre, DraftSpendRequest.withinRange]; rfl)

-- `(V4)` refund range check rejects issuer-proposed `x' = 100 ≥ 16` (triggered by `debit = 7`)
-- while recording the updated `policyState` from calling `chooseRefund`.
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st1 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨1, [⟨1, 10⟩], [0], [creq]⟩
    let req7 : DraftSpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      { spendStep1 ((1, 1, 10), 0) with debit := 7, newCredit := 3, changeCommitment := (2, 1, 3) }
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.spend req7)).run st1) =
      PMF.pure (none, { st1 with policyState := 2 }) := by
  simp only [run_draftIssuerOracle_spend]
  simp [acceptDraftSpendPre, DraftSpendRequest.withinRange, DraftSpendRequest.toSpendRequest,
    Conservation.acceptRequest, Conservation.acceptLocal, Conservation.hasSpentNullifier,
    Conservation.SpendRequest.inputNote, Credit.target, detPolicy, spendStep1, testCom, testSig,
    StateT.run]
  rfl

-- Policy decline (`chooseRefund = none` at `policyState = 99`) also rejects with `none`.
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st99 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨99, [⟨1, 10⟩], [0], [creq]⟩
    let req := spendStep1 ((1, 1, 10), 0)
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.spend req)).run st99) =
      PMF.pure (none, st99) := by
  simp only [run_draftIssuerOracle_spend]
  simp [acceptDraftSpendPre, DraftSpendRequest.withinRange, DraftSpendRequest.toSpendRequest,
    Conservation.acceptRequest, Conservation.acceptLocal, Conservation.hasSpentNullifier,
    Conservation.SpendRequest.inputNote, Credit.target, detPolicy, spendStep1, testCom, testSig,
    StateT.run]
  rfl

/-! ### Honest transcript, winnable forger, and probabilistic policy -/

/-- Honest draft adversary: agrees on `T = 10`, redeems ticket `0`, spends twice receiving
stateful refunds `1` and `2`, and attempts a double-spend of `nullifier = 1` that is rejected. -/
private def honestDraftAdversary :
    DraftAdversary ℕ ℕ ℕ (ℕ × ℕ × ℕ) Unit ((ℕ × ℕ × ℕ) × ℕ) ℕ := fun _ => do
  let _ ← ProbOracleComp.query
    (DraftQuery.agreeIssue 1 10 :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  let sig0? ← ProbOracleComp.query
    (DraftQuery.issue issueValid :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  let s1 := spendStep1 (sig0?.getD ((0, 0, 0), 0))
  let r1? ← ProbOracleComp.query
    (DraftQuery.spend s1 :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  let sig1 := (r1?.getD ⟨0, ((0, 0, 0), 0)⟩).signature
  let _ ← ProbOracleComp.query
    (DraftQuery.spend (spendStep2 sig1) :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  let _ ← ProbOracleComp.query
    (DraftQuery.spend s1 :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  return 1

-- End-to-end accepted log of `honestDraftAdversary`: confirms stateful refunds `x' = 1` then `2`
-- and rejection of the trailing double-spend (`3` accepted entries, not `4`).
example :
    let s1 := spendStep1 ((1, 1, 10), 0)
    let s2 := spendStep2 ((2, 1, 6), 1)
    ProbComp.eval
        (runExtractedDraftConservation testCom Prod.mk testSig detPolicy 16 honestDraftAdversary) =
      PMF.pure ⟨(), 1,
        [.issue ⟨1, 10, (1, 1, 10), 1, 0⟩,
         .spend (s1.toSpendRequest 1),
         .spend (s2.toSpendRequest 2)]⟩ := by
  simp only [runExtractedDraftConservation, honestDraftAdversary, testSig, detPolicy,
    ProbOracleComp.runState_bind, ProbOracleComp.runState_query, ProbOracleComp.runState_pure,
    StateT.run_bind, StateT.run_pure, run_draftIssuerOracle_agreeIssue,
    run_draftIssuerOracle_issue, run_draftIssuerOracle_spend]
  simp [StateT.run, draftReply, acceptDraftIssue, acceptDraftSpendPre,
    DraftSpendRequest.withinRange, DraftSpendRequest.toSpendRequest, Conservation.acceptRequest,
    Conservation.acceptLocal, Conservation.hasSpentNullifier, Conservation.SpendRequest.inputNote,
    Credit.target, Conservation.Request.signedMessage, issueValid, spendStep1, spendStep2,
    testCom]

-- Honest stateful transcript loses `extractedDraftConservationExperiment` (`9 ≤ 10 + 3`).
example :
    Experiment.succProbability
        (extractedDraftConservationExperiment testCom Prod.mk testSig detPolicy 16
          honestDraftAdversary) =
      0 := by
  simp only [extractedDraftConservationExperiment, runExtractedDraftConservation,
    honestDraftAdversary, testSig, detPolicy, ProbOracleComp.runState_bind,
    ProbOracleComp.runState_query, ProbOracleComp.runState_pure, StateT.run_bind, StateT.run_pure,
    run_draftIssuerOracle_agreeIssue, run_draftIssuerOracle_issue, run_draftIssuerOracle_spend]
  simp [StateT.run, draftReply, acceptDraftIssue, acceptDraftSpendPre,
    DraftSpendRequest.withinRange, DraftSpendRequest.toSpendRequest, Conservation.acceptRequest,
    Conservation.acceptLocal, Conservation.hasSpentNullifier, Conservation.SpendRequest.inputNote,
    Credit.target, Conservation.Request.signedMessage, issueValid, spendStep1, spendStep2,
    testCom, extractedDraftConservationAccept, Conservation.extractedConservationAccept,
    Conservation.spentDebit, Conservation.spendsIn, Conservation.spends,
    Conservation.issuedAmount, Conservation.issuesIn, Conservation.grantedRefund,
    Experiment.succProbability, Game.succProbability]

-- Zero-loss simulation check on `honestDraftAdversary`: both games have exact equal distributions.
example :
    ProbComp.eval
        (Conservation.extractedConservationExperiment testCom Prod.mk testSig
          (bridgeAdversary testCom Prod.mk testSig detPolicy 16 honestDraftAdversary)) =
      ProbComp.eval
        (extractedDraftConservationExperiment testCom Prod.mk testSig detPolicy 16
          honestDraftAdversary) :=
  (eval_extractedDraftConservationExperiment_eq testCom Prod.mk testSig detPolicy 16
    honestDraftAdversary).symm

/-- Constant zero-refund policy with unbounded honest agreement for the winnability and `L = 8`
wraparound tests. -/
private def zeroRefundPolicy : IssuerPolicy ℕ ℕ ℕ (ℕ × ℕ × ℕ) ℕ where
  init := pure 0
  agreeIssue _ hint := fun st => pure (some hint, st)
  chooseRefund _ _ _ _ := fun st => pure (some 0, st)

/-- Forging adversary: `testSig` signs a message with itself, so a note is self-certified. -/
private def forgingAdversary :
    DraftAdversary ℕ ℕ ℕ (ℕ × ℕ × ℕ) Unit ((ℕ × ℕ × ℕ) × ℕ) ℕ := fun _ => do
  let _ ← ProbOracleComp.query
    (DraftQuery.spend
      { ctx := 1
        nullifier := 1
        debit := 5
        changeCommitment := (2, 1, 0)
        oldCredit := 5
        oldOpening := 0
        oldRefund := 0
        signature := ((1, 1, 5), 0)
        newNullifier := 2
        newCredit := 0
        newOpening := 0 } :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  return 1

-- `extractedDraftConservationExperiment` is non-vacuous and winnable with probability `1`.
example :
    Experiment.succProbability
        (extractedDraftConservationExperiment testCom Prod.mk testSig zeroRefundPolicy 16
          forgingAdversary) =
      1 := by
  simp only [extractedDraftConservationExperiment, runExtractedDraftConservation, forgingAdversary,
    testSig, zeroRefundPolicy, ProbOracleComp.runState_bind, ProbOracleComp.runState_query,
    ProbOracleComp.runState_pure, StateT.run_bind, StateT.run_pure, run_draftIssuerOracle_spend]
  simp [StateT.run, draftReply, acceptDraftSpendPre, DraftSpendRequest.withinRange,
    DraftSpendRequest.toSpendRequest, Conservation.acceptRequest, Conservation.acceptLocal,
    Conservation.hasSpentNullifier, Conservation.SpendRequest.inputNote, Credit.target,
    Conservation.Request.signedMessage, testCom, extractedDraftConservationAccept,
    Conservation.extractedConservationAccept, Conservation.spentDebit, Conservation.spendsIn,
    Conservation.spends, Conservation.issuedAmount, Conservation.issuesIn,
    Conservation.grantedRefund, Experiment.succProbability, Game.succProbability]

/-- Genuinely probabilistic issuer policy drawing random bit + `1` or `2` refunds via `unifFin 1`.
-/
private def randPolicy : IssuerPolicy ℕ ℕ ℕ (ℕ × ℕ × ℕ) ℕ where
  init := do
    let b ← ProbComp.unifFin 1
    return b.val
  agreeIssue _ hint := fun st => return (some (hint + st), st)
  chooseRefund _ _ _ _ := fun st => do
    let r ← ProbComp.unifFin 1
    return (some (r.val + 1), st + r.val)

-- Under `randPolicy`, a single valid `.spend` yields refund `1` and refund `2` with equal
-- probability `1 / 2` (`2⁻¹` in `ℝ≥0∞`).
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st1 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨0, [⟨1, 10⟩], [0], [creq]⟩
    let req := spendStep1 ((1, 1, 10), 0)
    (ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig randPolicy 16 ((), ())
          (.spend req)).run st1))
        (some ⟨1, ((2, 1, 6), 1)⟩, ⟨0, [⟨1, 10⟩], [0], [creq, .spend (req.toSpendRequest 1)]⟩) =
        2⁻¹ ∧
      (ProbComp.eval
          ((draftIssuerOracle testCom Prod.mk testSig randPolicy 16 ((), ())
            (.spend req)).run st1))
          (some ⟨2, ((2, 1, 6), 2)⟩, ⟨1, [⟨1, 10⟩], [0], [creq, .spend (req.toSpendRequest 2)]⟩) =
        2⁻¹ := by
  intro creq st1 req
  have hpre :
      acceptDraftSpendPre testCom Prod.mk testSig 16 () st1 req = true := by
    simp [acceptDraftSpendPre, DraftSpendRequest.withinRange, DraftSpendRequest.toSpendRequest,
      Conservation.acceptRequest, Conservation.acceptLocal, Conservation.hasSpentNullifier,
      Conservation.SpendRequest.inputNote, Credit.target, req, spendStep1, st1, creq, testCom,
      testSig]
  let stOf (n : ℕ) : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
    ⟨n, [⟨1, 10⟩], [0], [creq, .spend (req.toSpendRequest (n + 1))]⟩
  let res (n : ℕ) :
      Option (SpendReply ((ℕ × ℕ × ℕ) × ℕ)) ×
        IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
    (some ⟨n + 1, ((2, 1, 6), n + 1)⟩, stOf n)
  have heval :
      ProbComp.eval
          ((draftIssuerOracle testCom Prod.mk testSig randPolicy 16 ((), ()) (.spend req)).run
            st1) =
        (Probability.PMF.uniformOfFintype (Fin 2)).bind fun r => PMF.pure (res r.val) := by
    rw [run_draftIssuerOracle_spend]
    simp only [hpre, ↓reduceIte, randPolicy, StateT.run]
    change (Probability.PMF.uniformOfFintype (Fin 2)).bind _ = _
    refine congrArg (PMF.bind (Probability.PMF.uniformOfFintype (Fin 2))) (funext fun r => ?_)
    have hr : r.val + 1 < 16 := by omega
    simp [res, stOf, hr, Conservation.Request.signedMessage, DraftSpendRequest.toSpendRequest,
      req, spendStep1, testSig, st1, draftReply]
  have hrhs (k : Fin 2) :
      ((Probability.PMF.uniformOfFintype (Fin 2)).bind fun r => PMF.pure (res r.val))
          (res k.val) =
        2⁻¹ := by
    rw [PMF.bind_apply, tsum_fintype, Fin.sum_univ_two]
    fin_cases k <;> simp [res, stOf, Probability.PMF.uniformOfFintype_apply, creq]
  exact ⟨(congrFun (congrArg DFunLike.coe heval) (res 0)).trans (hrhs 0),
    (congrFun (congrArg DFunLike.coe heval) (res 1)).trans (hrhs 1)⟩

/-! ### Generic query-bound and keyless-binding compositions -/

example {PolicyState Nullifier Context Opening Commitment Target PK SK Sig IssueHint : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment] [DecidableEq Target]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ)
    (A : DraftAdversary Nullifier Context Opening Commitment PK Sig IssueHint)
    (pk : PK) {q : ℕ} (hA : (A pk).IsQueryBounded q) :
    (targetForger (Credit.target com tag)
      (Conservation.noteForger com tag S (bridgeAdversary com tag S policy bound A))
      pk).IsQueryBounded q :=
  targetForger_queryBound _ _ pk
    (Conservation.noteForger_queryBound com tag S (bridgeAdversary com tag S policy bound A) pk
      (bridgeAdversary_queryBound com tag S policy bound A pk hA))

example {PolicyState Nullifier Context Opening Commitment PK SK Sig IssueHint : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (S : Signature.Scheme PK SK (Commitment × ℕ) Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ)
    (A : DraftAdversary Nullifier Context Opening Commitment PK Sig IssueHint) :
    Experiment.succProbability
        (extractedDraftConservationExperiment com Prod.mk S policy bound A) ≤
      Experiment.succProbability
          (S.eufCmaExperiment
            (targetForger (Credit.target com Prod.mk)
              (Conservation.noteForger com Prod.mk S
                (bridgeAdversary com Prod.mk S policy bound A)))) +
        Experiment.succProbability
          ((comScheme com).bindingExperiment
            (Conservation.commitmentBindingReduction com S
              (bridgeAdversary com Prod.mk S policy bound A))) :=
  extractedDraftConservationExperiment_succProbability_le_prod_mk com
    (comScheme com) (fun _ _ _ _ _ _ => rfl) S policy bound A

/-! ### Carry-bit boundary and `L = 8` (`2 ^ 64`) wraparound separation -/

-- Concrete 64-bit (`L = 8`) boundary instantiation at `(t = 0, x = 0, t' = 2^64 - 1, d = 1)`:
-- `(0 + 0) % 2^64 = (2^64 - 1 + 1) % 2^64`, yet bit 64 differs (`false ≠ true`),
-- producing the exact `2^64`-credit wraparound discrepancy.
example :
    (0 + 0) % 2 ^ 64 = (2 ^ 64 - 1 + 1) % 2 ^ 64 ∧
      (0 + 0).testBit 64 = false ∧
      (2 ^ 64 - 1 + 1).testBit 64 = true ∧
      0 + 0 ≠ 2 ^ 64 - 1 + 1 := by
  have hsum0 : (0 + 0 : ℕ) < 2 ^ (64 + 1) := by decide
  have hsum1 : (2 ^ 64 - 1 + 1 : ℕ) < 2 ^ (64 + 1) := by decide
  have hmod : (0 + 0) % 2 ^ 64 = (2 ^ 64 - 1 + 1) % 2 ^ 64 := by decide
  have hb0 : (0 + 0).testBit 64 = false := by decide
  have hb1 : (2 ^ 64 - 1 + 1).testBit 64 = true := by decide
  have hne : 0 + 0 ≠ 2 ^ 64 - 1 + 1 := by
    intro heq
    have hc := ((eq_iff_mod_eq_and_testBit_eq hsum0 hsum1).mp heq).2
    rw [hb0, hb1] at hc
    cases hc
  exact ⟨hmod, hb0, hb1, hne⟩

example :
    (2 ^ 64 - 1) + 1 = 0 + 0 + 2 ^ 64 ∧
      0 + 0 < 2 ^ 64 ∧
      2 ^ 64 ≤ (2 ^ 64 - 1) + 1 := by
  have hgap :=
    wraparound_gap_of_mod_eq_ne (t := 0) (x := 0) (t' := 2 ^ 64 - 1) (d := 1) (bound := 2 ^ 64)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hgap with hleft | hright <;> omega

/-- Vulnerable mod-`2^64` variant of `draftIssuerOracle`: delegates `.agreeIssue` and `.issue`
unchanged to `draftIssuerOracle`, while replacing integer `(V3)` with `(V3)` modulo `2 ^ 64` in
`.spend` (keeping `(V4)` `< 2 ^ 64`). -/
private def mod64ZeroRefundOracle :
    (q : DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ) →
    StateT (IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ) ProbComp
      (draftReply ((ℕ × ℕ × ℕ) × ℕ) q)
  | .agreeIssue ctx hint =>
      draftIssuerOracle testCom Prod.mk testSig zeroRefundPolicy (2 ^ 64) ((), ())
        (.agreeIssue ctx hint)
  | .issue req =>
      draftIssuerOracle testCom Prod.mk testSig zeroRefundPolicy (2 ^ 64) ((), ())
        (.issue req)
  | .spend req => fun st =>
      let okV1 := testSig.verify () (Credit.target testCom Prod.mk (⟨req.nullifier, req.ctx,
        req.oldCredit, req.oldRefund⟩) req.oldOpening) req.signature
      let okV2 := decide (testCom req.newNullifier req.ctx req.newCredit req.newOpening =
        req.changeCommitment)
      let okV3Mod64 := decide ((req.oldCredit + req.oldRefund) % 2 ^ 64 =
        (req.newCredit + req.debit) % 2 ^ 64)
      let okFresh := !Conservation.hasSpentNullifier st.accepted req.ctx req.nullifier
      if req.withinRange (2 ^ 64) && okV1 && okV2 && okV3Mod64 && okFresh then do
        let (refund?, pst') ←
          (zeroRefundPolicy.chooseRefund req.ctx req.nullifier req.debit req.changeCommitment).run
            st.policyState
        let st' := { st with policyState := pst' }
        match refund? with
        | none => return (none, st')
        | some refund =>
            if refund < 2 ^ 64 then
              let sreq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
                .spend (req.toSpendRequest refund)
              let σ ← testSig.sign () (sreq.signedMessage Prod.mk)
              return (some ⟨refund, σ⟩, { st' with accepted := st'.accepted ++ [sreq] })
            else
              return (none, st')
      else
        pure (none, st)

/-- Wraparound adversary along `T = 1 → t' = 0 → t' = 2^64 - 1`. -/
private def wraparoundDraftAdversary :
    DraftAdversary ℕ ℕ ℕ (ℕ × ℕ × ℕ) Unit ((ℕ × ℕ × ℕ) × ℕ) ℕ := fun _ => do
  let _ ← ProbOracleComp.query
    (DraftQuery.agreeIssue 1 1 :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  let sig0? ← ProbOracleComp.query
    (DraftQuery.issue { ticket := 0, commitment := (10, 1, 1), nullifier := 10, opening := 0 } :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  let r1? ← ProbOracleComp.query
    (DraftQuery.spend
      { ctx := 1
        nullifier := 10
        debit := 1
        changeCommitment := (11, 1, 0)
        oldCredit := 1
        oldOpening := 0
        oldRefund := 0
        signature := sig0?.getD ((0, 0, 0), 0)
        newNullifier := 11
        newCredit := 0
        newOpening := 0 } :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  let sig1 := (r1?.getD ⟨0, ((0, 0, 0), 0)⟩).signature
  let _ ← ProbOracleComp.query
    (DraftQuery.spend
      { ctx := 1
        nullifier := 11
        debit := 1
        changeCommitment := (12, 1, 2 ^ 64 - 1)
        oldCredit := 0
        oldOpening := 0
        oldRefund := 0
        signature := sig1
        newNullifier := 12
        newCredit := 2 ^ 64 - 1
        newOpening := 0 } :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  return 1

-- Under integer `(V3)` + `(V4)` (`extractedDraftConservationExperiment` with `bound = 2 ^ 64`), the
-- wraparound spend is rejected and conservation holds (`succProbability = 0`).
example :
    Experiment.succProbability
        (extractedDraftConservationExperiment testCom Prod.mk testSig zeroRefundPolicy (2 ^ 64)
          wraparoundDraftAdversary) =
      0 := by
  simp only [extractedDraftConservationExperiment, runExtractedDraftConservation,
    wraparoundDraftAdversary, testSig, zeroRefundPolicy, ProbOracleComp.runState_bind,
    ProbOracleComp.runState_query, ProbOracleComp.runState_pure, StateT.run_bind, StateT.run_pure,
    run_draftIssuerOracle_agreeIssue, run_draftIssuerOracle_issue, run_draftIssuerOracle_spend]
  simp [StateT.run, draftReply, acceptDraftIssue, acceptDraftSpendPre,
    DraftSpendRequest.withinRange, DraftSpendRequest.toSpendRequest, Conservation.acceptRequest,
    Conservation.acceptLocal, Conservation.hasSpentNullifier, Conservation.SpendRequest.inputNote,
    Credit.target, Conservation.Request.signedMessage, testCom,
    extractedDraftConservationAccept, Conservation.extractedConservationAccept,
    Conservation.spentDebit, Conservation.spendsIn, Conservation.spends,
    Conservation.issuedAmount, Conservation.issuesIn, Conservation.grantedRefund,
    Experiment.succProbability, Game.succProbability]

-- Replacing integer `(V3)` with mod-`2^64` `(V3)` (`mod64ZeroRefundOracle`) accepts the exact
-- same `T = 1 → 0 → 2^64 - 1` transcript (`spentDebit = 2 > 1 = issuedAmount + grantedRefund`)
-- with probability `1`.
example :
    Experiment.succProbability
        (extractedDraftConservationAccept <$> (do
          let keys ← testSig.keyGen
          let pst₀ ← zeroRefundPolicy.init
          let (targetCtx, st) ←
            ((wraparoundDraftAdversary keys.1).runState mod64ZeroRefundOracle).run
              ⟨pst₀, [], [], []⟩
          return ⟨keys.1, targetCtx, st.accepted⟩)) =
      1 := by
  simp only [wraparoundDraftAdversary, testSig, zeroRefundPolicy, ProbOracleComp.runState_bind,
    ProbOracleComp.runState_query, ProbOracleComp.runState_pure, StateT.run_bind, StateT.run_pure,
    mod64ZeroRefundOracle, run_draftIssuerOracle_agreeIssue, run_draftIssuerOracle_issue]
  simp [StateT.run, draftReply, acceptDraftIssue, DraftSpendRequest.withinRange,
    DraftSpendRequest.toSpendRequest, Conservation.hasSpentNullifier, Credit.target,
    Conservation.Request.signedMessage, testCom, extractedDraftConservationAccept,
    Conservation.extractedConservationAccept,
    Conservation.spentDebit, Conservation.spendsIn, Conservation.spends,
    Conservation.issuedAmount, Conservation.issuesIn, Conservation.grantedRefund,
    Experiment.succProbability, Game.succProbability]

end CslibFrontierTests.Crypto.AnonymousTokenIssuerBridge
