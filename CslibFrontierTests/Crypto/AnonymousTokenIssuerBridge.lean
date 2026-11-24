/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.AnonymousToken.IssuerBridge

/-!
# Regressions and clients for the VOLE-ACT draft issuer bridge

Exercises `Cslib.Crypto.AnonymousToken.IssuerBridge` through an ordinary import:
* a stateful issuer policy (`detPolicy`) driving out-of-band `T` agreement, policy declines
  (`none`), `T = 0` and `T ≥ bound` rejections, ticket single-use enforcement, `(V4)` range checks
  on `(d, t, x, t', x')`, double-spend rejection, and stateful refund selection (`x' = 1`, then
  `2`);
* an end-to-end honest stateful transcript verifying conservation (`succProbability = 0`), plus a
  probabilistic policy check (`randPolicy`) applying `eval_draftConservationExperiment_eq` and
  `draftConservationExperiment_succProbability_le_prod_mk`;
* concrete compositions of `bridgeAdversary_queryBound`, `Conservation.noteForger_queryBound`,
  `targetForger_queryBound`, and `draftConservationExperiment_succProbability_le_prod_mk` at a
  keyless commitment scheme `comScheme`;
* the `L = 8` (`bound = 2 ^ 64`) carry-bit boundary and `T = 1 → 0 → 2 ^ 64 - 1` wraparound
  separation, instantiating `eq_iff_mod_eq_and_testBit_eq` and `wraparound_gap_of_mod_eq_ne`
  and separating `draftConservationExperiment` (probability `0`) from a mod-`2 ^ 64` `(V3)` issuer
  (probability `1`).
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
and otherwise the issuer grants stateful `x' = st + 1` and increments `st`. -/
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
    else pure (some (st + 1), st + 1)

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

/-! ### Policy, range, ticket-replay, and double-spend rejections -/

-- Policy decline (`hint = 0`) returns `none` and leaves `pending` unchanged while stepping state.
example :
    (detPolicy.agreeIssue 1 0).run 0 = pure (none, 1) := rfl

-- `T = 0` agreed via `hint = 1` is rejected by `.issue` (`none`) without consuming ticket `0`.
example :
    let st0 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ := ⟨1, [(1, 0)], [], []⟩
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.issue { ticket := 0, commitment := (1, 1, 0), nullifier := 1, opening := 0 })).run
          st0) =
      PMF.pure (none, st0) := by
  simp [draftIssuerOracle, acceptDraftIssue, testCom, StateT.run]
  rfl

-- `T ≥ bound` (`T = 100`, `bound = 16`) agreed via `hint = 2` is rejected by `.issue`.
example :
    let st0 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ := ⟨1, [(1, 100)], [], []⟩
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.issue { ticket := 0, commitment := (1, 1, 100), nullifier := 1, opening := 0 })).run
          st0) =
      PMF.pure (none, st0) := by
  simp [draftIssuerOracle, acceptDraftIssue, testCom, StateT.run]
  rfl

-- Ticket replay: once ticket `0` is in `st.consumed`, a second `.issue` on ticket `0` returns
-- `none` and leaves `accepted` unchanged.
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st1 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨1, [(1, 10)], [0], [creq]⟩
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.issue issueValid)).run st1) =
      PMF.pure (none, st1) := by
  simp [draftIssuerOracle, acceptDraftIssue, issueValid, testCom, StateT.run]
  rfl

-- `(V4)` range check rejects `d ≥ bound` before calling `chooseRefund`, keeping `policyState`.
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st1 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨5, [(1, 10)], [0], [creq]⟩
    let badSpend : DraftSpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      { spendStep1 ((1, 1, 10), 0) with debit := 16 }
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.spend badSpend)).run st1) =
      PMF.pure (none, st1) := by
  simp [draftIssuerOracle, acceptDraftSpendPre, DraftSpendRequest.withinRange,
    DraftSpendRequest.toSpendRequest, Conservation.acceptRequest, Conservation.acceptLocal,
    spendStep1, testSig, StateT.run]
  rfl

-- `(V4)` refund range check rejects issuer-proposed `x' = 100 ≥ 16` (triggered by `debit = 7`)
-- while recording the updated `policyState` from calling `chooseRefund`.
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st1 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨1, [(1, 10)], [0], [creq]⟩
    let req7 : DraftSpendRequest ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      { spendStep1 ((1, 1, 10), 0) with debit := 7, newCredit := 3, changeCommitment := (2, 1, 3) }
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.spend req7)).run st1) =
      PMF.pure (none, { st1 with policyState := 2 }) := by
  simp [draftIssuerOracle, acceptDraftSpendPre, DraftSpendRequest.withinRange,
    DraftSpendRequest.toSpendRequest, Conservation.acceptRequest, Conservation.acceptLocal,
    Conservation.hasSpentNullifier, Conservation.SpendRequest.inputNote, Credit.target,
    detPolicy, spendStep1, testCom, testSig, StateT.run]
  rfl

-- Policy decline (`chooseRefund = none` at `policyState = 99`) also rejects with `none`.
example :
    let creq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
      .issue ⟨1, 10, (1, 1, 10), 1, 0⟩
    let st99 : IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ :=
      ⟨99, [(1, 10)], [0], [creq]⟩
    let req := spendStep1 ((1, 1, 10), 0)
    ProbComp.eval
        ((draftIssuerOracle testCom Prod.mk testSig detPolicy 16 ((), ())
          (.spend req)).run st99) =
      PMF.pure (none, st99) := by
  simp [draftIssuerOracle, acceptDraftSpendPre, DraftSpendRequest.withinRange,
    DraftSpendRequest.toSpendRequest, Conservation.acceptRequest, Conservation.acceptLocal,
    Conservation.hasSpentNullifier, Conservation.SpendRequest.inputNote, Credit.target,
    detPolicy, spendStep1, testCom, testSig, StateT.run]
  rfl

/-! ### Honest stateful transcript and end-to-end conservation evaluation -/

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
  let sig1 := (r1?.getD (0, ((0, 0, 0), 0))).2
  let _ ← ProbOracleComp.query
    (DraftQuery.spend (spendStep2 sig1) :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  let _ ← ProbOracleComp.query
    (DraftQuery.spend s1 :
      DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ)
  return 1

-- Honest stateful transcript (with double-spend attempt) loses `draftConservationExperiment`,
-- receiving stateful refunds `1` and `2` (`9 ≤ 10 + 3`).
example :
    Experiment.succProbability
        (draftConservationExperiment testCom Prod.mk testSig detPolicy 16 honestDraftAdversary) =
      0 := by
  simp only [draftConservationExperiment, runDraftConservation, honestDraftAdversary,
    testSig, detPolicy, ProbOracleComp.runState_bind, ProbOracleComp.runState_query,
    ProbOracleComp.runState_pure, StateT.run_bind, StateT.run_pure]
  simp [StateT.run, draftIssuerOracle, acceptDraftIssue, acceptDraftSpendPre,
    DraftSpendRequest.withinRange, DraftSpendRequest.toSpendRequest, Conservation.acceptRequest,
    Conservation.acceptLocal, Conservation.hasSpentNullifier, Conservation.SpendRequest.inputNote,
    Credit.target, Conservation.Request.signedMessage, issueValid, spendStep1,
    spendStep2, testCom, draftConservationAccept, Conservation.spentDebit,
    Conservation.spendsIn, Conservation.spends, Conservation.issuedAmount, Conservation.issuesIn,
    Conservation.grantedRefund, Experiment.succProbability, Game.succProbability]

-- Zero-loss simulation check on `honestDraftAdversary`: both games have exact equal distributions.
example :
    ProbComp.eval
        (Conservation.extractedConservationExperiment testCom Prod.mk testSig
          (bridgeAdversary testCom Prod.mk testSig detPolicy 16 honestDraftAdversary)) =
      ProbComp.eval
        (draftConservationExperiment testCom Prod.mk testSig detPolicy 16 honestDraftAdversary) :=
  (eval_draftConservationExperiment_eq testCom Prod.mk testSig detPolicy 16
    honestDraftAdversary).symm

/-- Genuinely probabilistic issuer policy drawing random bit + `0`/`1` refunds via `unifFin 1`. -/
private def randPolicy : IssuerPolicy ℕ ℕ ℕ (ℕ × ℕ × ℕ) ℕ where
  init := do
    let b ← ProbComp.unifFin 1
    return b.val
  agreeIssue _ hint := fun st => return (some (hint + st), st)
  chooseRefund _ _ _ _ := fun st => do
    let r ← ProbComp.unifFin 1
    return (some (r.val + 1), st + r.val)

example :
    ProbComp.eval
        (Conservation.extractedConservationExperiment testCom Prod.mk testSig
          (bridgeAdversary testCom Prod.mk testSig randPolicy 16 honestDraftAdversary)) =
      ProbComp.eval
        (draftConservationExperiment testCom Prod.mk testSig randPolicy 16 honestDraftAdversary) :=
  (eval_draftConservationExperiment_eq testCom Prod.mk testSig randPolicy 16
    honestDraftAdversary).symm

example :
    Experiment.succProbability
        (draftConservationExperiment testCom Prod.mk testSig randPolicy 16 honestDraftAdversary) ≤
      Experiment.succProbability
          (testSig.eufCmaExperiment
            (targetForger (Credit.target testCom Prod.mk)
              (Conservation.noteForger testCom Prod.mk testSig
                (bridgeAdversary testCom Prod.mk testSig randPolicy 16 honestDraftAdversary)))) +
        Experiment.succProbability
          ((comScheme testCom).bindingExperiment
            (Conservation.commitmentBindingReduction testCom testSig
              (bridgeAdversary testCom Prod.mk testSig randPolicy 16 honestDraftAdversary))) :=
  draftConservationExperiment_succProbability_le_prod_mk testCom
    (comScheme testCom) (fun _ _ _ _ _ _ => rfl) testSig randPolicy 16
    honestDraftAdversary

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
    Experiment.succProbability (draftConservationExperiment com Prod.mk S policy bound A) ≤
      Experiment.succProbability
          (S.eufCmaExperiment
            (targetForger (Credit.target com Prod.mk)
              (Conservation.noteForger com Prod.mk S
                (bridgeAdversary com Prod.mk S policy bound A)))) +
        Experiment.succProbability
          ((comScheme com).bindingExperiment
            (Conservation.commitmentBindingReduction com S
              (bridgeAdversary com Prod.mk S policy bound A))) :=
  draftConservationExperiment_succProbability_le_prod_mk com
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
  have ht : (0 : ℕ) < 2 ^ 64 := by decide
  have hx : (0 : ℕ) < 2 ^ 64 := by decide
  have ht' : (2 ^ 64 - 1 : ℕ) < 2 ^ 64 := by decide
  have hd : (1 : ℕ) < 2 ^ 64 := by decide
  have hmod : (0 + 0) % 2 ^ 64 = (2 ^ 64 - 1 + 1) % 2 ^ 64 := by decide
  have hb0 : (0 + 0).testBit 64 = false := by decide
  have hb1 : (2 ^ 64 - 1 + 1).testBit 64 = true := by decide
  have hne : 0 + 0 ≠ 2 ^ 64 - 1 + 1 := by
    intro heq
    have hc := ((eq_iff_mod_eq_and_testBit_eq ht hx ht' hd).mp heq).2
    rw [hb0, hb1] at hc
    cases hc
  exact ⟨hmod, hb0, hb1, hne⟩

example :
    decide (2 ^ 64 ≤ 0 + 0) = false ∧
      decide (2 ^ 64 ≤ (2 ^ 64 - 1) + 1) = true ∧
      (2 ^ 64 - 1) + 1 = 0 + 0 + 2 ^ 64 := by
  have hgap :=
    wraparound_gap_of_mod_eq_ne (t := 0) (x := 0) (t' := 2 ^ 64 - 1) (d := 1) (bound := 2 ^ 64)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hgap with hleft | hright
  · exact hleft
  · exfalso
    have hfalse : decide (2 ^ 64 ≤ 0 + 0) = false := by decide
    rw [hfalse] at hright
    cases hright.1

/-- Constant zero-refund policy with unbounded honest agreement for the `L = 8` wraparound
separation (`T = 1 → t' = 0 → t' = 2 ^ 64 - 1`). -/
private def zeroRefundPolicy : IssuerPolicy ℕ ℕ ℕ (ℕ × ℕ × ℕ) ℕ where
  init := pure 0
  agreeIssue _ hint := fun st => pure (some hint, st)
  chooseRefund _ _ _ _ := fun st => pure (some 0, st)

/-- Vulnerable mod-`2^64` variant of `draftIssuerOracle` replacing integer `(V3)` with `(V3)`
modulo `2 ^ 64` while keeping `(V4)` `< 2 ^ 64` and `1 ≤ T < 2 ^ 64`. -/
private def mod64ZeroRefundOracle :
    (q : DraftQuery ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ) →
    StateT (IssuerState ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) ℕ) ProbComp
      (draftReply ((ℕ × ℕ × ℕ) × ℕ) q)
  | .agreeIssue ctx hint => fun st => do
      let (amt?, pst') ← (zeroRefundPolicy.agreeIssue ctx hint).run st.policyState
      match amt? with
      | none => return (none, { st with policyState := pst' })
      | some amt =>
          let ticket := st.pending.length
          return (some (ticket, amt),
            { st with policyState := pst', pending := st.pending ++ [(ctx, amt)] })
  | .issue req => fun st =>
      match acceptDraftIssue testCom (2 ^ 64) req st with
      | none => pure (none, st)
      | some creq => do
          let σ ← testSig.sign () (creq.signedMessage Prod.mk)
          return (some σ,
            { st with
              consumed := req.ticket :: st.consumed
              accepted := st.accepted ++ [creq] })
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
        match refund? with
        | none => return (none, { st with policyState := pst' })
        | some refund =>
            if refund < 2 ^ 64 then
              let sreq : Conservation.Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) ((ℕ × ℕ × ℕ) × ℕ) :=
                .spend (req.toSpendRequest refund)
              let σ ← testSig.sign () (sreq.signedMessage Prod.mk)
              return (some (refund, σ),
                { st with policyState := pst', accepted := st.accepted ++ [sreq] })
            else
              return (none, { st with policyState := pst' })
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
  let sig1 := (r1?.getD (0, ((0, 0, 0), 0))).2
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

-- Under integer `(V3)` + `(V4)` (`draftConservationExperiment` with `bound = 2 ^ 64`), the
-- wraparound spend is rejected and conservation holds (`succProbability = 0`).
example :
    Experiment.succProbability
        (draftConservationExperiment testCom Prod.mk testSig zeroRefundPolicy (2 ^ 64)
          wraparoundDraftAdversary) =
      0 := by
  simp only [draftConservationExperiment, runDraftConservation, wraparoundDraftAdversary,
    testSig, zeroRefundPolicy, ProbOracleComp.runState_bind, ProbOracleComp.runState_query,
    ProbOracleComp.runState_pure, StateT.run_bind, StateT.run_pure]
  simp [StateT.run, draftIssuerOracle, acceptDraftIssue, acceptDraftSpendPre,
    DraftSpendRequest.withinRange, DraftSpendRequest.toSpendRequest, Conservation.acceptRequest,
    Conservation.acceptLocal, Conservation.hasSpentNullifier, Conservation.SpendRequest.inputNote,
    Credit.target, Conservation.Request.signedMessage, testCom,
    draftConservationAccept, Conservation.spentDebit, Conservation.spendsIn, Conservation.spends,
    Conservation.issuedAmount, Conservation.issuesIn, Conservation.grantedRefund,
    Experiment.succProbability, Game.succProbability]

-- Replacing integer `(V3)` with mod-`2^64` `(V3)` (`mod64ZeroRefundOracle`) accepts the exact
-- same `T = 1 → 0 → 2^64 - 1` transcript (`spentDebit = 2 > 1 = issuedAmount + grantedRefund`)
-- with probability `1`.
example :
    Experiment.succProbability
        (draftConservationAccept <$> (do
          let keys ← testSig.keyGen
          let pst₀ ← zeroRefundPolicy.init
          let (targetCtx, st) ←
            ((wraparoundDraftAdversary keys.1).runState mod64ZeroRefundOracle).run
              ⟨pst₀, [], [], []⟩
          return ⟨keys.1, targetCtx, st.accepted⟩)) =
      1 := by
  simp only [wraparoundDraftAdversary, testSig, zeroRefundPolicy, ProbOracleComp.runState_bind,
    ProbOracleComp.runState_query, ProbOracleComp.runState_pure, StateT.run_bind, StateT.run_pure]
  simp [StateT.run, mod64ZeroRefundOracle, acceptDraftIssue, DraftSpendRequest.withinRange,
    DraftSpendRequest.toSpendRequest, Conservation.hasSpentNullifier, Credit.target,
    Conservation.Request.signedMessage, zeroRefundPolicy, testCom, testSig, draftConservationAccept,
    Conservation.spentDebit, Conservation.spendsIn, Conservation.spends, Conservation.issuedAmount,
    Conservation.issuesIn, Conservation.grantedRefund, Experiment.succProbability,
    Game.succProbability]

end CslibFrontierTests.Crypto.AnonymousTokenIssuerBridge
