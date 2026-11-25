/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.AnonymousToken.Conservation
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Map

/-!
# Draft issuer bridge and carry-bit boundary for single-issuer VOLE-ACT

`Cslib.Crypto.AnonymousToken.Conservation` analyzes a permissive extracted game in which the
adversary supplies the initial balance `T` and the spend refund `x'` directly, and range checks
(`V4`, plus `T ≥ 1`) are omitted. In the draft specification ([VOLEACT2026], Protocol
Specification), `T` is agreed out of band via the issuer's issuance policy (`T ∈ [1..2^(8*L)]`),
`x'` is chosen by the issuer in `SpendResponse`, and range checks are enforced (`T_init ≠ 0` at
issuance; `t', x, d < 2^(8*L)` in SpendRelation `(V4)`, `t < 2^(8*L)` from witness size, and
`d, x' < 2^(8*L)` in `SpendResponse`) with rejection replies.

This module formalizes that stateful, probabilistic draft-style issuer within the extracted-witness
model and proves an exact, zero-loss simulation reduction (`bridgeAdversary`,
`eval_extractedDraftConservationExperiment_eq`) into `Conservation.extractedConservationExperiment`.
Because `Conservation`'s bound already holds for the permissive issuer and the conservation win
predicate depends only on the log of accepted requests, the range checks, `T ≥ 1` guard, and
ticket single-use serve faithfulness to the draft rather than tightening the inequality; composing
with `Conservation` directly transfers the concrete EUF-CMA and target/keyless-commitment binding
bounds to `extractedDraftConservationExperiment`, while `bridgeAdversary_queryBound` preserves query
budgets.

This draft-style game, the ticket-allocation device (`agreeIssue`/`consumed`), and the simulation
reduction are original to this library. Modeling choices relative to the draft pseudocode:
* `IssuerPolicy` is fixed before `keyGen` and has no access to `(pk, sk)`.
* Out-of-band issuance agreement is modeled by `.agreeIssue` returning a sequential ticket index,
  and `.issue` enforces `amt < bound` alongside `1 ≤ amt` (representing the draft's input-domain
  bound `T_init < 2^(8*L)`).
* `acceptDraftSpendPre` enforces `(V1)`–`(V4)` and nullifier freshness before invoking
  `policy.chooseRefund` (matching the draft's Overview order rather than `SpendResponse` input
  order): `policy.chooseRefund` is not called when `acceptDraftSpendPre` fails, whereas when
  `policy.chooseRefund` returns `none` or `refund ≥ bound`, the spend is rejected after the
  policy runs and retains its updated `policyState`.
* A spend's `ctx` is read from `DraftSpendRequest.ctx` and matched against the certified input note,
  allowing multi-context requests under one oracle.

This bridge stays in the extracted-witness model and bounds oracle queries rather than runtime:
VOLEitH proof extraction, zero-knowledge, random-oracle or ideal-permutation arguments for `Com`
and `Tag`, multi-issuer selection, and polynomial-time machine certificates remain tracked under
#7068.

It also establishes the standalone arithmetic carry-bit boundary explaining why `(V3)` uses full
integer equality rather than equality modulo `2 ^ w`: for `w`-bit sums `< 2 ^ (w + 1)` (as implied
by `(V4)` `< 2 ^ w`), equality holds if and only if modular equality modulo `2 ^ w` holds together
with matching top carry bit `Nat.testBit · w` (`eq_iff_mod_eq_and_testBit_eq`), and any modular
collision between sums under `2 * bound` forces an exact `bound`-credit wraparound discrepancy
(`wraparound_gap_of_mod_eq_ne`).

## Main definitions

* `IssuerPolicy`: stateful, probabilistic key-independent issuer policy supplying agreed issuance
  amounts and spend refunds from public spend metadata only.
* `IssueAgreement`, `SpendReply`, `AgreedTicket`, `DraftIssueRequest`, `DraftSpendRequest`,
  `DraftQuery`, `draftReply`, `IssuerState`: draft-style queries, named replies, and stateful
  issuer bookkeeping, without adversary-chosen `T` or `x'`.
* `draftIssuerOracle` (with client transition laws `run_draftIssuerOracle_agreeIssue`,
  `run_draftIssuerOracle_issue`, `run_draftIssuerOracle_spend`), `DraftAdversary`,
  `ExtractedDraftConservationExecution`, `runExtractedDraftConservation`,
  `extractedDraftConservationAccept`, `extractedDraftConservationExperiment`: draft-style
  stateful issuer oracle and extracted conservation game with range and policy rejections.
* `bridgeAdversary`: explicit simulation reduction to `Conservation.ExtractedAdversary`.

## Main results

* `bridgeAdversary_queryBound`: `bridgeAdversary` preserves query budgets (`≤ q`).
* `eval_extractedDraftConservationExperiment_eq`: exact zero-loss distribution equality between
  `extractedDraftConservationExperiment` and `Conservation.extractedConservationExperiment` on
  `bridgeAdversary`.
* `extractedDraftConservationExperiment_succProbability_le`,
  `extractedDraftConservationExperiment_succProbability_le_prod_mk`: concrete EUF-CMA plus binding
  bounds against the draft-style issuer.
* `eq_iff_mod_eq_and_testBit_eq`, `wraparound_gap_of_mod_eq_ne`: exact carry-bit equivalence and
  `bound`-credit wraparound separation under `(V4)` range limits.

## References

* [*VOLE-ACT*][VOLEACT2026], Protocol Specification / Parameters (`#parameters`), Initial Issuance
  (`#issuance`), and Spending (`#spending`).
-/

public section

namespace Cslib.Crypto.AnonymousToken.IssuerBridge

open Probability

variable {PolicyState Nullifier Context Opening Commitment Target PK SK Sig IssueHint : Type}

@[expose] section

/-! ### Issuer policy, draft-style requests, and range checks -/

/-- Stateful, probabilistic policy driving a draft-style issuer: fixed independently of the
certification keys `(pk, sk)`, `agreeIssue` chooses (or declines) the initial credit balance `T`
during out-of-band issuance agreement, and `chooseRefund` chooses (or declines) the spend refund
`x'` from public spend metadata `(ctx, nf, d, c')` without seeing private witnesses. -/
structure IssuerPolicy (PolicyState Context Nullifier Commitment IssueHint : Type) where
  /-- Initial private state of the issuer policy. -/
  init : ProbComp PolicyState
  /-- Stateful, probabilistic initial-balance agreement (`T_init`) for context and hint. -/
  agreeIssue : Context → IssueHint → StateT PolicyState ProbComp (Option ℕ)
  /-- Stateful, probabilistic refund selection (`x'`) given public spend request data. -/
  chooseRefund : Context → Nullifier → ℕ → Commitment → StateT PolicyState ProbComp (Option ℕ)

/-- An extracted draft-style issuance submission referencing an agreed ticket (a library-specific
representation of out-of-band `T_init` agreement). Neither `ctx` nor `amount` is chosen in this
message; both come from the issuer's ticket. -/
structure DraftIssueRequest (Nullifier Opening Commitment : Type) where
  /-- Identifier returned by an earlier `.agreeIssue` query. -/
  ticket : ℕ
  /-- Commitment `c` to `(nullifier, ctx, T)` under `opening`. -/
  commitment : Commitment
  /-- Extracted nullifier `nf`. -/
  nullifier : Nullifier
  /-- Extracted opening randomness `r`. -/
  opening : Opening

/-- An extracted draft-style spend submission: identical to `Conservation.SpendRequest` except that
the refund `x'` is omitted because the issuer chooses it in `SpendResponse`. -/
structure DraftSpendRequest (Nullifier Context Opening Commitment Sig : Type) where
  /-- Issuance context `ctx` shared by input and change tokens. -/
  ctx : Context
  /-- Revealed nullifier `nf` of the spent token. -/
  nullifier : Nullifier
  /-- Amount `d` debited by this spend. -/
  debit : ℕ
  /-- Commitment `c'` to the change token. -/
  changeCommitment : Commitment
  /-- Extracted committed balance `t` of the input token. -/
  oldCredit : ℕ
  /-- Extracted opening randomness `r` of the input token. -/
  oldOpening : Opening
  /-- Extracted prior refund `x` carried by the input token. -/
  oldRefund : ℕ
  /-- Extracted certification signature `s` on the input state. -/
  signature : Sig
  /-- Extracted nullifier `nf'` of the change token. -/
  newNullifier : Nullifier
  /-- Extracted committed balance `t'` of the change token. -/
  newCredit : ℕ
  /-- Extracted opening randomness `r'` of the change token. -/
  newOpening : Opening

/-- Promote a `DraftSpendRequest` to `Conservation.SpendRequest` using issuer-chosen `refund`. -/
def DraftSpendRequest.toSpendRequest
    (req : DraftSpendRequest Nullifier Context Opening Commitment Sig) (refund : ℕ) :
    Conservation.SpendRequest Nullifier Context Opening Commitment Sig :=
  { ctx := req.ctx
    nullifier := req.nullifier
    debit := req.debit
    refund := refund
    changeCommitment := req.changeCommitment
    oldCredit := req.oldCredit
    oldOpening := req.oldOpening
    oldRefund := req.oldRefund
    signature := req.signature
    newNullifier := req.newNullifier
    newCredit := req.newCredit
    newOpening := req.newOpening }

/-- Check upper bounds `< bound` on the client-supplied debit `d`, extracted witness balance `t`
(bounded implicitly by the draft's witness field `2^(8*L)`), and `(V4)` fields `x, t'`
([VOLEACT2026], SpendRelation `V4` and `SpendResponse` step 2). -/
def DraftSpendRequest.withinRange (bound : ℕ)
    (req : DraftSpendRequest Nullifier Context Opening Commitment Sig) : Bool :=
  decide (req.debit < bound ∧ req.oldCredit < bound ∧ req.oldRefund < bound ∧ req.newCredit < bound)

/-- Queries admitted by the draft-style extracted issuer oracle: out-of-band issuance agreement,
issuance submission, and spend submission. -/
inductive DraftQuery (Nullifier Context Opening Commitment Sig IssueHint : Type) where
  /-- Negotiate an initial balance `T` under `ctx` with policy hint `hint`. -/
  | agreeIssue (ctx : Context) (hint : IssueHint)
  /-- Submit an issuance commitment and extracted opening for an agreed ticket. -/
  | issue (req : DraftIssueRequest Nullifier Opening Commitment)
  /-- Submit a spend request and extracted witness; the issuer supplies any refund `x'`. -/
  | spend (req : DraftSpendRequest Nullifier Context Opening Commitment Sig)

/-- Out-of-band issuance agreement reply returning the sequential ticket index and agreed balance
`T`. -/
structure IssueAgreement where
  /-- Sequential index of the allocated agreement ticket. -/
  ticket : ℕ
  /-- Initial credit balance `T` agreed by the issuer policy. -/
  amount : ℕ
  deriving DecidableEq

/-- Spend reply returning the issuer-chosen refund `x'` and certification signature on
`Tag(c', x')`. -/
structure SpendReply (Sig : Type) where
  /-- Refund `x'` chosen by the issuer policy. -/
  refund : ℕ
  /-- Issuer certification signature on the change token. -/
  signature : Sig
  deriving DecidableEq

/-- Server-side record of an agreed issuance ticket under `ctx` for initial balance `T`. -/
structure AgreedTicket (Context : Type) where
  /-- Issuance context negotiated for this ticket. -/
  ctx : Context
  /-- Initial credit balance `T` agreed for this ticket. -/
  amount : ℕ
  deriving DecidableEq

/-- Reply type of each `DraftQuery`: `Option IssueAgreement` for `.agreeIssue`, `Option Sig` for
`.issue`, and `Option (SpendReply Sig)` for `.spend`. -/
def draftReply (Sig : Type) :
    DraftQuery Nullifier Context Opening Commitment Sig IssueHint → Type
  | .agreeIssue _ _ => Option IssueAgreement
  | .issue _ => Option Sig
  | .spend _ => Option (SpendReply Sig)

/-- Private state of the draft-style issuer: policy state, issued agreement tickets, consumed
ticket indices, and accepted `Conservation.Request` log (oldest first). -/
structure IssuerState (Nullifier Context Opening Commitment Sig PolicyState : Type) where
  /-- Current private state of the issuer policy. -/
  policyState : PolicyState
  /-- Agreed issuance tickets indexed by allocation order. -/
  pending : List (AgreedTicket Context)
  /-- Ticket indices already redeemed by an accepted `.issue` call. -/
  consumed : List ℕ
  /-- Accepted requests recorded in `Conservation.Request` format, oldest first. -/
  accepted : List (Conservation.Request Nullifier Context Opening Commitment Sig)

/-- Validate a `.issue` submission for `draftIssuerOracle` and `bridgeAdversary` (via internal
`bridgeHandler`) against `st.pending`, single-use `st.consumed`, `1 ≤ amt` (`T_init ≠ 0` in
`IssueResponse`), `amt < bound` (the draft's `[1..2^(8*L)]` input domain), and the `IssueRelation`
commitment check. Returns `none` on rejection without modifying state. -/
def acceptDraftIssue [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment) (bound : ℕ)
    (req : DraftIssueRequest Nullifier Opening Commitment)
    (st : IssuerState Nullifier Context Opening Commitment Sig PolicyState) :
    Option (Conservation.Request Nullifier Context Opening Commitment Sig) :=
  match st.pending[req.ticket]? with
  | none => none
  | some agreed =>
      if req.ticket ∉ st.consumed ∧ 1 ≤ agreed.amount ∧ agreed.amount < bound ∧
          com req.nullifier agreed.ctx agreed.amount req.opening = req.commitment then
        some (.issue ⟨agreed.ctx, agreed.amount, req.commitment, req.nullifier, req.opening⟩)
      else
        none

/-- Pre-refund validity check for `.spend`, called by `draftIssuerOracle` and `bridgeAdversary`
(via internal `bridgeHandler`) before `policy.chooseRefund`: enforces `(V4)` `< bound` on
`d, t, x, t'`, `(V1)`–`(V3)`, and spent-nullifier uniqueness against `st.accepted`. -/
def acceptDraftSpendPre [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (bound : ℕ) (pk : PK)
    (st : IssuerState Nullifier Context Opening Commitment Sig PolicyState)
    (req : DraftSpendRequest Nullifier Context Opening Commitment Sig) : Bool :=
  req.withinRange bound &&
    Conservation.acceptRequest com tag S pk st.accepted (.spend (req.toSpendRequest 0))

end

private def agreeIssueTransition (ctx : Context) (amt? : Option ℕ) (pst' : PolicyState)
    (st : IssuerState Nullifier Context Opening Commitment Sig PolicyState) :
    Option IssueAgreement × IssuerState Nullifier Context Opening Commitment Sig PolicyState :=
  match amt? with
  | none => (none, { st with policyState := pst' })
  | some amt =>
      (some ⟨st.pending.length, amt⟩,
        { st with policyState := pst', pending := st.pending ++ [⟨ctx, amt⟩] })

private def commitDraftIssue (ticket : ℕ)
    (creq : Conservation.Request Nullifier Context Opening Commitment Sig) (σ : Sig)
    (st : IssuerState Nullifier Context Opening Commitment Sig PolicyState) :
    Option Sig × IssuerState Nullifier Context Opening Commitment Sig PolicyState :=
  (some σ, { st with consumed := ticket :: st.consumed, accepted := st.accepted ++ [creq] })

private def acceptedSpendRefund (bound : ℕ) (refund? : Option ℕ) : Option ℕ :=
  match refund? with
  | none => none
  | some refund => if refund < bound then some refund else none

private def commitDraftSpend (refund : ℕ)
    (creq : Conservation.Request Nullifier Context Opening Commitment Sig) (σ : Sig)
    (st : IssuerState Nullifier Context Opening Commitment Sig PolicyState) :
    Option (SpendReply Sig) × IssuerState Nullifier Context Opening Commitment Sig PolicyState :=
  (some ⟨refund, σ⟩, { st with accepted := st.accepted ++ [creq] })

private def draftQueryStep {ι : Type} {qspec : ι → Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ) (pk : PK)
    (samplePolicy : ∀ {α : Type}, ProbComp α → OracleComp qspec α)
    (certify :
      Conservation.Request Nullifier Context Opening Commitment Sig →
        OracleComp qspec (Option Sig)) :
    (q : DraftQuery Nullifier Context Opening Commitment Sig IssueHint) →
      StateT (IssuerState Nullifier Context Opening Commitment Sig PolicyState) (OracleComp qspec)
        (draftReply Sig q)
  | .agreeIssue ctx hint => fun st => do
      let (amt?, pst') ← samplePolicy ((policy.agreeIssue ctx hint).run st.policyState)
      return agreeIssueTransition ctx amt? pst' st
  | .issue req => fun st =>
      match acceptDraftIssue com bound req st with
      | none => pure (none, st)
      | some creq => do
          let σ? ← certify creq
          match σ? with
          | none => pure (none, st)
          | some σ => pure (commitDraftIssue req.ticket creq σ st)
  | .spend req => fun st =>
      if acceptDraftSpendPre com tag S bound pk st req then do
        let (refund?, pst') ← samplePolicy
          ((policy.chooseRefund req.ctx req.nullifier req.debit req.changeCommitment).run
            st.policyState)
        let st' := { st with policyState := pst' }
        match acceptedSpendRefund bound refund? with
        | none => return (none, st')
        | some refund => do
            let creq : Conservation.Request Nullifier Context Opening Commitment Sig :=
              .spend (req.toSpendRequest refund)
            let σ? ← certify creq
            match σ? with
            | none => return (none, st')
            | some σ => return commitDraftSpend refund creq σ st'
      else
        pure (none, st)

/-- Draft-style stateful issuer oracle implementing out-of-band `T` agreement, issuer-chosen `x'`,
`T ≥ 1` and `< bound` `(V4)` range checks, `(V1)`–`(V3)`, and nullifier-uniqueness rejections.
Rejected `.issue` calls leave `st.consumed` and `st.policyState` unchanged; `.spend` calls failing
`acceptDraftSpendPre` return `none` without calling `policy.chooseRefund`, whereas `chooseRefund`
returning `none` or `refund ≥ bound` updates `policyState` before returning `none`. -/
def draftIssuerOracle [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ) (keys : PK × SK) :
    (q : DraftQuery Nullifier Context Opening Commitment Sig IssueHint) →
      StateT (IssuerState Nullifier Context Opening Commitment Sig PolicyState) ProbComp
        (draftReply Sig q) :=
  draftQueryStep com tag S policy bound keys.1 (fun p => p)
    (fun creq => some <$> S.sign keys.2 (creq.signedMessage tag))

/-- Transition law of `draftIssuerOracle` on `.agreeIssue`: samples `policy.agreeIssue` and, on
`some amt`, allocates the next sequential ticket under `ctx`. -/
theorem run_draftIssuerOracle_agreeIssue
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ) (keys : PK × SK) (ctx : Context) (hint : IssueHint)
    (st : IssuerState Nullifier Context Opening Commitment Sig PolicyState) :
    (draftIssuerOracle com tag S policy bound keys (.agreeIssue ctx hint)).run st = do
      let (amt?, pst') ← (policy.agreeIssue ctx hint).run st.policyState
      return match amt? with
      | none => (none, { st with policyState := pst' })
      | some amt =>
          (some ⟨st.pending.length, amt⟩,
            { st with policyState := pst', pending := st.pending ++ [⟨ctx, amt⟩] }) := by
  rfl

/-- Transition law of `draftIssuerOracle` on `.issue`: validates via `acceptDraftIssue`, signs the
accepted request, marks the ticket consumed, and appends to `st.accepted`. -/
theorem run_draftIssuerOracle_issue
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ) (keys : PK × SK) (req : DraftIssueRequest Nullifier Opening Commitment)
    (st : IssuerState Nullifier Context Opening Commitment Sig PolicyState) :
    (draftIssuerOracle com tag S policy bound keys (.issue req)).run st =
      match acceptDraftIssue com bound req st with
      | none => pure (none, st)
      | some creq => do
          let σ ← S.sign keys.2 (creq.signedMessage tag)
          return (some σ,
            { st with
              consumed := req.ticket :: st.consumed,
              accepted := st.accepted ++ [creq] }) := by
  simp only [draftIssuerOracle, draftQueryStep, commitDraftIssue, StateT.run, draftReply]
  cases acceptDraftIssue com bound req st with
  | none => rfl
  | some creq => simp only [bind_map_left]

/-- Transition law of `draftIssuerOracle` on `.spend`: skips `policy.chooseRefund` when
`acceptDraftSpendPre` fails, otherwise samples the policy, rejects `none` or `refund ≥ bound`
retaining the updated `policyState`, and otherwise signs and logs the spend request. -/
theorem run_draftIssuerOracle_spend
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ) (keys : PK × SK)
    (req : DraftSpendRequest Nullifier Context Opening Commitment Sig)
    (st : IssuerState Nullifier Context Opening Commitment Sig PolicyState) :
    (draftIssuerOracle com tag S policy bound keys (.spend req)).run st =
      if acceptDraftSpendPre com tag S bound keys.1 st req then do
        let (refund?, pst') ←
          (policy.chooseRefund req.ctx req.nullifier req.debit req.changeCommitment).run
            st.policyState
        let st' := { st with policyState := pst' }
        match refund? with
        | none => return (none, st')
        | some refund =>
            if refund < bound then
              let creq : Conservation.Request Nullifier Context Opening Commitment Sig :=
                .spend (req.toSpendRequest refund)
              let σ ← S.sign keys.2 (creq.signedMessage tag)
              return (some ⟨refund, σ⟩, { st' with accepted := st'.accepted ++ [creq] })
            else
              return (none, st')
      else
        pure (none, st) := by
  simp only [draftIssuerOracle, draftQueryStep, acceptedSpendRefund, commitDraftSpend, StateT.run,
    draftReply]
  by_cases hpre : acceptDraftSpendPre com tag S bound keys.1 st req = true
  · simp only [hpre, ↓reduceIte]
    congr 1 with ⟨refund?, pst'⟩ : 1
    cases refund? with
    | none => rfl
    | some refund =>
        by_cases hlt : refund < bound
        · simp only [hlt, ↓reduceIte, bind_map_left]
        · simp only [hlt, ↓reduceIte]
  · simp [hpre]

/-- An adaptive adversary interacting with the draft-style issuer oracle and returning a target
context `ctx*`. -/
abbrev DraftAdversary (Nullifier Context Opening Commitment PK Sig IssueHint : Type) :=
  PK → ProbOracleComp
    (draftReply (Nullifier := Nullifier) (Context := Context) (Opening := Opening)
      (Commitment := Commitment) (IssueHint := IssueHint) Sig)
    Context

/-- The public key, target context, and accepted request log of an extracted draft conservation
execution. -/
structure ExtractedDraftConservationExecution
    (Nullifier Context Opening Commitment PK Sig : Type) where
  /-- Public verification key sampled by the experiment. -/
  publicKey : PK
  /-- Target context `ctx*` output by the adversary. -/
  targetCtx : Context
  /-- Accepted requests recorded in `Conservation.Request` format, oldest first. -/
  accepted : List (Conservation.Request Nullifier Context Opening Commitment Sig)

/-- Execute `A` against the draft-style stateful issuer in the extracted-witness model. -/
@[expose] def runExtractedDraftConservation
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ)
    (A : DraftAdversary Nullifier Context Opening Commitment PK Sig IssueHint) :
    ProbComp (ExtractedDraftConservationExecution Nullifier Context Opening Commitment PK Sig) := do
  let keys ← S.keyGen
  let pst₀ ← policy.init
  let st₀ : IssuerState Nullifier Context Opening Commitment Sig PolicyState := ⟨pst₀, [], [], []⟩
  let (targetCtx, finalSt) ←
    ((A keys.1).runState (draftIssuerOracle com tag S policy bound keys)).run st₀
  return ⟨keys.1, targetCtx, finalSt.accepted⟩

/-- Acceptance predicate of the extracted draft conservation game, delegating directly to
`Conservation.extractedConservationAccept`. -/
@[expose] def extractedDraftConservationAccept [DecidableEq Context]
    (run : ExtractedDraftConservationExecution Nullifier Context Opening Commitment PK Sig) :
    Bool :=
  Conservation.extractedConservationAccept
    ⟨run.publicKey, run.targetCtx, run.accepted.map (·, none)⟩

/-- Extracted draft-style VOLE-ACT credit-conservation experiment ([VOLEACT2026], Protocol
Specification). Unlike `Conservation.extractedConservationExperiment`, initial amounts `T` are
agreed via `policy.agreeIssue`, spend refunds `x'` are chosen by `policy.chooseRefund`, and `(V4)`
plus `1 ≤ T < bound` range checks are enforced with `none` rejection replies. Because this game is
still in the extracted-witness model, extraction from VOLEitH proofs, zero-knowledge, RO/ideal-
permutation arguments, and runtime efficiency certificates remain outside this model (#7068). -/
@[expose] def extractedDraftConservationExperiment
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ)
    (A : DraftAdversary Nullifier Context Opening Commitment PK Sig IssueHint) : Experiment :=
  extractedDraftConservationAccept <$> runExtractedDraftConservation com tag S policy bound A

/-! ### Simulation reduction to `Conservation` -/

/-- Simulation handler translating `DraftQuery` calls into `Conservation.extractedIssuerOracle`
queries. Out-of-band agreements, policy state, range checks, and rejected requests are handled
locally without querying `Conservation`'s oracle; accepted issuances and spends forward exactly one
request each. -/
private def bridgeHandler [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ) (pk : PK) :
    (q : DraftQuery Nullifier Context Opening Commitment Sig IssueHint) →
      StateT (IssuerState Nullifier Context Opening Commitment Sig PolicyState)
        (ProbOracleComp (fun _ : Conservation.Request Nullifier Context Opening Commitment Sig =>
          Option Sig))
        (draftReply Sig q) :=
  draftQueryStep com tag S policy bound pk
    (fun p => ProbOracleComp.sample p) (fun creq => ProbOracleComp.query creq)

/-- Explicit simulation reduction from `DraftAdversary` to `Conservation.ExtractedAdversary`.
Encapsulates `policy`, ticket tracking, and `(V4)` range rejections while forwarding only accepted
issuances and spends to `Conservation.extractedIssuerOracle`. No runtime certificate is established
for this program; query bounds are proved in `bridgeAdversary_queryBound` (#7068). -/
def bridgeAdversary [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ)
    (A : DraftAdversary Nullifier Context Opening Commitment PK Sig IssueHint) :
    Conservation.ExtractedAdversary Nullifier Context Opening Commitment PK Sig := fun pk => do
  let pst₀ ← ProbOracleComp.sample policy.init
  let st₀ : IssuerState Nullifier Context Opening Commitment Sig PolicyState := ⟨pst₀, [], [], []⟩
  let result ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (bridgeHandler com tag S policy bound pk))
    (A pk)).run st₀
  return result.1

/-- `bridgeAdversary` makes at most `q` queries to the `Conservation` oracle whenever `A` makes
at most `q` draft-oracle queries (no runtime or polynomial-time certificate is claimed here; #7068).
-/
theorem bridgeAdversary_queryBound
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ)
    (A : DraftAdversary Nullifier Context Opening Commitment PK Sig IssueHint)
    (pk : PK) {q : ℕ} (hA : (A pk).IsQueryBounded q) :
    (bridgeAdversary com tag S policy bound A pk).IsQueryBounded q := by
  dsimp only [bridgeAdversary]
  rw [← Nat.zero_add q]
  refine (ProbOracleComp.IsQueryBounded.sample policy.init).bind fun pst₀ => ?_
  let st₀ : IssuerState Nullifier Context Opening Commitment Sig PolicyState := ⟨pst₀, [], [], []⟩
  have hbody :
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (bridgeHandler com tag S policy bound pk))
        (A pk)).run st₀).IsQueryBounded q := by
    refine OracleComp.IsCostBounded.run_interpret (fun r st => ?_) hA st₀
    rcases r with k | req
    · simpa [OracleComp.sumHandler, StateT.run, StateT.lift] using
        (ProbOracleComp.IsQueryBounded.sample
          (spec := fun _ : Conservation.Request Nullifier Context Opening Commitment Sig =>
            Option Sig)
          (ProbComp.unifFin k)).bind fun a => OracleComp.IsCostBounded.pure (a, st) 0
    · cases req with
      | agreeIssue ctx hint =>
          simp only [OracleComp.sumHandler, Sum.elim_inr, StateT.run, bridgeHandler,
            draftQueryStep]
          rw [← Nat.zero_add 1]
          refine (ProbOracleComp.IsQueryBounded.sample _).bind fun p => ?_
          exact OracleComp.IsCostBounded.pure _ 1
      | issue ireq =>
          simp only [OracleComp.sumHandler, Sum.elim_inr, StateT.run, bridgeHandler,
            draftQueryStep]
          cases acceptDraftIssue com bound ireq st with
          | none => exact OracleComp.IsCostBounded.pure (none, st) 1
          | some creq =>
              dsimp only
              rw [← Nat.add_zero 1]
              refine (ProbOracleComp.IsQueryBounded.query creq).bind fun σ? => ?_
              cases σ? <;> exact OracleComp.IsCostBounded.pure _ 0
      | spend sreq =>
          simp only [OracleComp.sumHandler, Sum.elim_inr, StateT.run, bridgeHandler,
            draftQueryStep]
          by_cases hpre : acceptDraftSpendPre com tag S bound pk st sreq = true
          · simp only [hpre, ↓reduceIte]
            rw [← Nat.zero_add 1]
            refine (ProbOracleComp.IsQueryBounded.sample _).bind fun p => ?_
            rcases p with ⟨refund?, pst'⟩
            dsimp only
            cases acceptedSpendRefund bound refund? with
            | none => exact OracleComp.IsCostBounded.pure _ 1
            | some refund =>
                dsimp only
                rw [← Nat.add_zero 1]
                refine (ProbOracleComp.IsQueryBounded.query
                  (spec := fun _ : Conservation.Request Nullifier Context Opening Commitment Sig =>
                    Option Sig)
                  (.spend (sreq.toSpendRequest refund))).bind fun σ? => ?_
                cases σ? <;> exact OracleComp.IsCostBounded.pure _ 0
          · simp only [hpre, Bool.false_eq_true, ↓reduceIte]
            exact OracleComp.IsCostBounded.pure (none, st) 1
  exact hbody.bind fun _ => OracleComp.IsCostBounded.pure _ 0

private theorem acceptRequest_toSpendRequest
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK)
    (accepted : List (Conservation.Request Nullifier Context Opening Commitment Sig))
    (req : DraftSpendRequest Nullifier Context Opening Commitment Sig) (refund : ℕ) :
    Conservation.acceptRequest com tag S pk accepted (.spend (req.toSpendRequest refund)) =
      Conservation.acceptRequest com tag S pk accepted (.spend (req.toSpendRequest 0)) := by
  rfl

private theorem acceptRequest_of_acceptDraftIssue
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {bound : ℕ} {pk : PK}
    {req : DraftIssueRequest Nullifier Opening Commitment}
    {st : IssuerState Nullifier Context Opening Commitment Sig PolicyState}
    {creq : Conservation.Request Nullifier Context Opening Commitment Sig}
    (h : acceptDraftIssue com bound req st = some creq) :
    Conservation.acceptRequest com tag S pk st.accepted creq = true := by
  simp only [acceptDraftIssue] at h
  cases hp : st.pending[req.ticket]? with
  | none => simp [hp] at h
  | some agreed =>
      simp only [hp] at h
      split_ifs at h with hcond
      · simp only [Option.some.injEq] at h
        subst creq
        simp only [Conservation.acceptRequest, Conservation.acceptLocal, decide_eq_true_eq]
        exact hcond.2.2.2

private theorem acceptRequest_of_acceptDraftSpendPre
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {tag : Commitment → ℕ → Target}
    {S : Signature.Scheme PK SK Target Sig} {bound : ℕ} {pk : PK}
    {st : IssuerState Nullifier Context Opening Commitment Sig PolicyState}
    {req : DraftSpendRequest Nullifier Context Opening Commitment Sig}
    (h : acceptDraftSpendPre com tag S bound pk st req = true) (refund : ℕ) :
    Conservation.acceptRequest com tag S pk st.accepted (.spend (req.toSpendRequest refund)) =
      true := by
  rw [acceptRequest_toSpendRequest]
  exact (Bool.and_eq_true_iff.mp h).2

/-- Exact simulation equality in the extracted-witness model: the draft-style conservation
experiment has the exact same Boolean distribution as
`Conservation.extractedConservationExperiment` on `bridgeAdversary`, with zero probability loss.
This bridges `Conservation.extractedConservationExperiment`'s permissive game to the draft's
stateful issuer within the extracted-witness model (extraction, zero-knowledge, RO/ideal-permutation
realization, and PPT runtime certificates remain outside this model, #7068). -/
theorem eval_extractedDraftConservationExperiment_eq
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ)
    (A : DraftAdversary Nullifier Context Opening Commitment PK Sig IssueHint) :
    ProbComp.eval (extractedDraftConservationExperiment com tag S policy bound A) =
      ProbComp.eval (Conservation.extractedConservationExperiment com tag S
        (bridgeAdversary com tag S policy bound A)) := by
  simp only [extractedDraftConservationExperiment, Conservation.extractedConservationExperiment,
    runExtractedDraftConservation, Conservation.runExtractedConservation, ProbComp.eval_map,
    ProbComp.eval_bind, PMF.map_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ _ => ?_
  dsimp only
  let extLogOracle :
      Conservation.Request Nullifier Context Opening Commitment Sig →
      StateT (List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig))
        PMF (Option Sig) :=
    fun req log =>
      ProbComp.eval
        (ProbOracleComp.logOracle (Conservation.extractedIssuerOracle com tag S (pk, sk)) req log)
  let draftOracle :
      (q : DraftQuery Nullifier Context Opening Commitment Sig IssueHint) →
      StateT (IssuerState Nullifier Context Opening Commitment Sig PolicyState) PMF
        (draftReply Sig q) :=
    fun q st => ProbComp.eval (draftIssuerOracle com tag S policy bound (pk, sk) q st)
  let jointOracle :
      (q : DraftQuery Nullifier Context Opening Commitment Sig IssueHint) →
      StateT (IssuerState Nullifier Context Opening Commitment Sig PolicyState ×
        List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig))
        PMF (draftReply Sig q) :=
    fun q state =>
      (ProbOracleComp.runWith extLogOracle
        ((bridgeHandler com tag S policy bound pk q).run state.1) state.2).map
        fun ⟨⟨a, b⟩, c⟩ => (a, b, c)
  have hrunExt :
      ProbComp.eval
          ((bridgeAdversary com tag S policy bound A pk).runLogWith
            (Conservation.extractedIssuerOracle com tag S (pk, sk))) =
        (ProbComp.eval policy.init).bind fun pst₀ =>
          (ProbOracleComp.runWith jointOracle (A pk) (⟨pst₀, [], [], []⟩, [])).map
            fun ⟨ctx, _, log⟩ => (ctx, log) := by
    rw [ProbOracleComp.runLogWith, ProbOracleComp.eval_runState]
    dsimp only [bridgeAdversary]
    rw [ProbOracleComp.runWith_sample_bind]
    refine PMF.bind_congr_on_support _ _ _ fun pst₀ _ => ?_
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_run_interpret, PMF.bind_map]
    simp only [ProbOracleComp.runWith_pure]
    rfl
  rw [hrunExt]
  simp only [ProbComp.eval_pure, PMF.pure_map, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun pst₀ _ => ?_
  let st₀ : IssuerState Nullifier Context Opening Commitment Sig PolicyState := ⟨pst₀, [], [], []⟩
  have hcertify_mem : ∀ {β : Type}
      (creq : Conservation.Request Nullifier Context Opening Commitment Sig)
      (rejSt : IssuerState Nullifier Context Opening Commitment Sig PolicyState)
      (commit : Sig → Option β × IssuerState Nullifier Context Opening Commitment Sig PolicyState)
      (log : List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig))
      (hreq : Conservation.acceptRequest com tag S pk (log.map Prod.fst) creq = true)
      (hrej : rejSt.accepted = log.map Prod.fst)
      (hacc : ∀ σ, (commit σ).2.accepted = rejSt.accepted ++ [creq])
      (ans : Option β)
      (next : IssuerState Nullifier Context Opening Commitment Sig PolicyState ×
        List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig)),
      ((ans, next.1), next.2) ∈ (ProbOracleComp.runWith extLogOracle (do
          let σ? ← ProbOracleComp.query creq
          match σ? with
          | none => pure (none, rejSt)
          | some σ => pure (commit σ)) log).support →
        next.1.accepted = next.2.map Prod.fst := by
    intro β creq rejSt commit log hreq hrej hacc ans next hmem
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query] at hmem
    dsimp only [extLogOracle, ProbOracleComp.logOracle, Conservation.extractedIssuerOracle] at hmem
    simp only [hreq, ↓reduceIte, ProbComp.eval_map, Functor.map_map, PMF.bind_map,
      Function.comp_def, PMF.mem_support_bind_iff] at hmem
    obtain ⟨σ, _, hmem'⟩ := hmem
    simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hmem'
    have hL := congrArg Prod.fst hmem'
    have hSt := congrArg Prod.snd hL
    have hLg := congrArg Prod.snd hmem'
    dsimp only at hSt hLg
    rw [hSt, hLg]
    simp only [hacc σ, hrej, List.map_append, List.map_cons, List.map_nil]
  have hcertify_eq : ∀ {β : Type}
      (creq : Conservation.Request Nullifier Context Opening Commitment Sig)
      (rejSt : IssuerState Nullifier Context Opening Commitment Sig PolicyState)
      (commit : Sig → Option β × IssuerState Nullifier Context Opening Commitment Sig PolicyState)
      (log : List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig))
      (hreq : Conservation.acceptRequest com tag S pk (log.map Prod.fst) creq = true),
      ((ProbOracleComp.runWith extLogOracle (do
          let σ? ← ProbOracleComp.query creq
          match σ? with
          | none => pure (none, rejSt)
          | some σ => pure (commit σ)) log).map fun (p, _) => p) =
        (ProbComp.eval (S.sign sk (creq.signedMessage tag))).bind fun σ =>
          PMF.pure (commit σ) := by
    intro β creq rejSt commit log hreq
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    dsimp only [extLogOracle, ProbOracleComp.logOracle, Conservation.extractedIssuerOracle]
    simp only [hreq, ↓reduceIte, ProbComp.eval_map, Functor.map_map, PMF.bind_map,
      Function.comp_def, PMF.map_bind, ProbOracleComp.runWith_pure, PMF.pure_map]
  have hpreserve :
      ∀ (q : DraftQuery Nullifier Context Opening Commitment Sig IssueHint)
        (state : IssuerState Nullifier Context Opening Commitment Sig PolicyState ×
          List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig)),
        state.1.accepted = state.2.map Prod.fst →
        ∀ (ans : draftReply Sig q)
          (next : IssuerState Nullifier Context Opening Commitment Sig PolicyState ×
            List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig)),
          (ans, next) ∈ (jointOracle q state).support →
          next.1.accepted = next.2.map Prod.fst := by
    intro q ⟨st, log⟩ hstate
    dsimp only at hstate
    cases q with
    | agreeIssue ctx hint =>
        dsimp only [draftReply]
        intro ans next hnext
        simp only [jointOracle, bridgeHandler, draftQueryStep, StateT.run, draftReply] at hnext
        rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample] at hnext
        simp only [PMF.bind_map, Function.comp_def, PMF.map_bind] at hnext
        obtain ⟨⟨amt?, pst'⟩, _, hmem⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
        simp only [ProbOracleComp.runWith_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hmem
        obtain ⟨_, rfl⟩ := hmem
        cases amt? <;> exact hstate
    | issue req =>
        dsimp only [draftReply]
        intro ans next hnext
        simp only [jointOracle, bridgeHandler, draftQueryStep, StateT.run, draftReply] at hnext
        cases hacc : acceptDraftIssue com bound req st with
        | none =>
            simp only [hacc, ProbOracleComp.runWith_pure, PMF.pure_map] at hnext
            obtain ⟨_, rfl⟩ := (PMF.mem_support_pure_iff _ _).mp hnext
            exact hstate
        | some creq =>
            simp only [hacc] at hnext
            obtain ⟨⟨p, log'⟩, hmem, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
            cases heq
            exact hcertify_mem creq st (fun σ => commitDraftIssue req.ticket creq σ st) log
              (hstate ▸ acceptRequest_of_acceptDraftIssue hacc) hstate (fun _ => rfl)
              p.1 (p.2, log') hmem
    | spend req =>
        dsimp only [draftReply]
        intro ans next hnext
        simp only [jointOracle, bridgeHandler, draftQueryStep, StateT.run, draftReply] at hnext
        by_cases hpre : acceptDraftSpendPre com tag S bound pk st req = true
        · simp only [hpre, ↓reduceIte, ProbOracleComp.runWith_bind,
            ProbOracleComp.runWith_sample, PMF.bind_map, Function.comp_def, PMF.map_bind] at hnext
          obtain ⟨⟨refund?, pst'⟩, _, hmem⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
          cases haccRef : acceptedSpendRefund bound refund? with
          | none =>
              simp only [haccRef, ProbOracleComp.runWith_pure, PMF.pure_map,
                PMF.mem_support_pure_iff] at hmem
              obtain ⟨_, rfl⟩ := hmem
              exact hstate
          | some refund =>
              simp only [haccRef, PMF.mem_support_map_iff] at hmem
              obtain ⟨⟨p, log'⟩, hmem', heq⟩ := hmem
              cases heq
              exact hcertify_mem (.spend (req.toSpendRequest refund))
                { st with policyState := pst' }
                (fun σ => commitDraftSpend refund (.spend (req.toSpendRequest refund)) σ
                  { st with policyState := pst' })
                log (hstate ▸ acceptRequest_of_acceptDraftSpendPre hpre refund) hstate
                (fun _ => rfl) p.1 (p.2, log') hmem'
        · simp only [hpre, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure,
            PMF.pure_map] at hnext
          obtain ⟨_, rfl⟩ := (PMF.mem_support_pure_iff _ _).mp hnext
          exact hstate
  have hinv :
      ∀ ctx st log,
        (ctx, st, log) ∈ (ProbOracleComp.runWith jointOracle (A pk) (st₀, [])).support →
        st.accepted = log.map Prod.fst :=
    fun ctx st log hres => ProbOracleComp.runWith_invariant jointOracle
      (fun p => p.1.accepted = p.2.map Prod.fst) hpreserve (A pk) (st₀, []) rfl ctx (st, log) hres
  have hproj :
      (ProbOracleComp.runWith jointOracle (A pk) (st₀, [])).map (fun (ctx, p) => (ctx, p.1)) =
        ProbOracleComp.runWith draftOracle (A pk) st₀ := by
    refine ProbOracleComp.runWith_map_state_of_invariant jointOracle draftOracle Prod.fst
      (fun p => p.1.accepted = p.2.map Prod.fst) hpreserve (fun q state hstate => ?_)
      (A pk) (st₀, []) rfl
    rcases state with ⟨st, log⟩
    dsimp only at hstate
    cases q with
    | agreeIssue ctx hint =>
        simp only [jointOracle, draftOracle, bridgeHandler, draftIssuerOracle, draftQueryStep,
          StateT.run, draftReply]
        rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, ProbComp.eval_bind]
        simp only [PMF.bind_map, Function.comp_def, PMF.map_bind,
          ProbComp.eval_pure, ProbOracleComp.runWith_pure, PMF.pure_map]
    | issue req =>
        simp only [jointOracle, draftOracle, bridgeHandler, draftIssuerOracle, draftQueryStep,
          StateT.run, draftReply, PMF.map_comp, Function.comp_def]
        cases hacc : acceptDraftIssue com bound req st with
        | none => simp [ProbComp.eval_pure, ProbOracleComp.runWith_pure, PMF.pure_map]
        | some creq =>
            simp only [ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map, Function.comp_def]
            exact hcertify_eq creq st (fun σ => commitDraftIssue req.ticket creq σ st) log
              (hstate ▸ acceptRequest_of_acceptDraftIssue hacc)
    | spend req =>
        simp only [jointOracle, draftOracle, bridgeHandler, draftIssuerOracle, draftQueryStep,
          StateT.run, draftReply, PMF.map_comp, Function.comp_def]
        by_cases hpre : acceptDraftSpendPre com tag S bound pk st req = true
        · simp only [hpre, ↓reduceIte, ProbOracleComp.runWith_bind,
            ProbOracleComp.runWith_sample, ProbComp.eval_bind, PMF.bind_map, Function.comp_def,
            PMF.map_bind]
          congr 1 with ⟨refund?, pst'⟩ : 1
          dsimp only
          cases acceptedSpendRefund bound refund? with
          | none => simp [ProbComp.eval_pure, ProbOracleComp.runWith_pure, PMF.pure_map]
          | some refund =>
              simp only [ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map, Function.comp_def]
              exact hcertify_eq (.spend (req.toSpendRequest refund))
                { st with policyState := pst' }
                (fun σ => commitDraftSpend refund (.spend (req.toSpendRequest refund)) σ
                  { st with policyState := pst' })
                log (hstate ▸ acceptRequest_of_acceptDraftSpendPre hpre refund)
        · simp [hpre, ProbComp.eval_pure, ProbOracleComp.runWith_pure, PMF.pure_map]
  have hcongr :
      (ProbOracleComp.runWith jointOracle (A pk) (st₀, [])).map
          (fun ⟨ctx, st, _⟩ => extractedDraftConservationAccept ⟨pk, ctx, st.accepted⟩) =
        (ProbOracleComp.runWith jointOracle (A pk) (st₀, [])).map
          (fun ⟨ctx, _, log⟩ => Conservation.extractedConservationAccept ⟨pk, ctx, log⟩) := by
    refine PMF.map_congr_on_support _ _ _ fun ⟨ctx, st, log⟩ hmem => ?_
    have heq : st.accepted = log.map Prod.fst := hinv ctx st log hmem
    dsimp only [extractedDraftConservationAccept, Conservation.extractedConservationAccept]
    simp only [heq, List.map_map, Function.comp_def]
  have hd :
      ((ProbComp.eval (((A pk).runState (draftIssuerOracle com tag S policy bound (pk, sk))).run
          st₀)).map fun p => extractedDraftConservationAccept ⟨pk, p.1, p.2.accepted⟩) =
        (ProbOracleComp.runWith jointOracle (A pk) (st₀, [])).map
          (fun ⟨ctx, st, _⟩ => extractedDraftConservationAccept ⟨pk, ctx, st.accepted⟩) := by
    rw [ProbOracleComp.eval_runState, ← hproj, PMF.map_comp]
    rfl
  change
      ((ProbComp.eval (((A pk).runState (draftIssuerOracle com tag S policy bound (pk, sk))).run
          st₀)).map fun p => extractedDraftConservationAccept ⟨pk, p.1, p.2.accepted⟩) =
        ((ProbOracleComp.runWith jointOracle (A pk) (st₀, [])).map
          fun ⟨ctx, _, log⟩ => (ctx, log)).map
            (fun p => Conservation.extractedConservationAccept ⟨pk, p.1, p.2⟩)
  rw [hd, hcongr, PMF.map_comp]
  rfl

private theorem succProbability_extractedDraftConservationExperiment_eq
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ)
    (A : DraftAdversary Nullifier Context Opening Commitment PK Sig IssueHint) :
    Experiment.succProbability (extractedDraftConservationExperiment com tag S policy bound A) =
      Experiment.succProbability
        (Conservation.extractedConservationExperiment com tag S
          (bridgeAdversary com tag S policy bound A)) := by
  simp only [Experiment.succProbability, Game.succProbability,
    eval_extractedDraftConservationExperiment_eq]

/-- Concrete extracted-model bound for the draft-style issuer: winning
`extractedDraftConservationExperiment` yields either a `targetForger` existential forgery against
`S` or a target collision in `noteForger`'s run, each with coefficient one. Not a
credit-conservation theorem for the unextracted protocol; VOLEitH extraction, zero-knowledge,
RO/ideal-permutation realization, and PPT machine witnesses remain outside this model (#7068). -/
theorem extractedDraftConservationExperiment_succProbability_le
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment] [DecidableEq Target]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (policy : IssuerPolicy PolicyState Context Nullifier Commitment IssueHint)
    (bound : ℕ)
    (A : DraftAdversary Nullifier Context Opening Commitment PK Sig IssueHint) :
    Experiment.succProbability (extractedDraftConservationExperiment com tag S policy bound A) ≤
      Experiment.succProbability
          (S.eufCmaExperiment
            (targetForger (Credit.target com tag)
              (Conservation.noteForger com tag S (bridgeAdversary com tag S policy bound A)))) +
        Experiment.succProbability
          (bindingExperiment S (Credit.target com tag)
            (Conservation.noteForger com tag S (bridgeAdversary com tag S policy bound A))) := by
  rw [succProbability_extractedDraftConservationExperiment_eq]
  exact Conservation.extractedConservationExperiment_succProbability_le com tag S
    (bridgeAdversary com tag S policy bound A)

/-- Concrete extracted-model keyless-commitment specialization at `tag = Prod.mk`: winning
`extractedDraftConservationExperiment` yields either a `targetForger` EUF-CMA forgery against `S`
or a binding collision for a keyless commitment scheme `CS` whose verifier accepts exactly when
`com nf ctx t o = c` under every key (`hverify`), via `Conservation.commitmentBindingReduction`,
each with coefficient one. VOLEitH extraction, zero-knowledge, RO/ideal-permutation realization,
and PPT machine witnesses remain outside this model (#7068). -/
theorem extractedDraftConservationExperiment_succProbability_le_prod_mk
    {K : Type} [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (hverify : ∀ k nf ctx t c o, CS.verify k (nf, ctx, t) c o = decide (com nf ctx t o = c))
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
          (CS.bindingExperiment
            (Conservation.commitmentBindingReduction com S
              (bridgeAdversary com Prod.mk S policy bound A))) := by
  rw [succProbability_extractedDraftConservationExperiment_eq]
  exact Conservation.extractedConservationExperiment_succProbability_le_prod_mk com CS hverify S
    (bridgeAdversary com Prod.mk S policy bound A)

/-! ### Carry-bit vs modular arithmetic boundary under `(V4)` -/

private theorem add_lt_two_mul_decomp {a bound : ℕ} (ha : a < 2 * bound) :
    (a < bound ∧ a % bound = a) ∨ (bound ≤ a ∧ a = bound + a % bound) := by
  by_cases hle : bound ≤ a
  · right
    have h1 := Nat.div_add_mod a bound
    have hdiv : a / bound = 1 := Nat.div_eq_of_lt_le (by simpa using hle) (by simpa using ha)
    rw [hdiv, Nat.mul_one] at h1
    exact ⟨hle, h1.symm⟩
  · left
    have hlt := Nat.lt_of_not_le hle
    exact ⟨hlt, Nat.mod_eq_of_lt hlt⟩

/-- Arithmetic carry-bit boundary for sums `< 2 ^ (w + 1)` (in particular `t + x` and `t' + d`
under `w`-bit `(V4)` bounds `< 2 ^ w`, where the draft sets `w = 8 * L`): integer equality
`a = b` holds if and only if modular equality modulo `2 ^ w` holds together with equality of the
`(w + 1)`-st carry bit `Nat.testBit · w` ([VOLEACT2026], Spending `V3` and `V4`). -/
theorem eq_iff_mod_eq_and_testBit_eq {a b w : ℕ}
    (ha : a < 2 ^ (w + 1)) (hb : b < 2 ^ (w + 1)) :
    a = b ↔ a % 2 ^ w = b % 2 ^ w ∧ a.testBit w = b.testBit w := by
  refine ⟨fun h => by simp [h], fun ⟨hm, hbit⟩ => ?_⟩
  have ha2 : a / 2 ^ w < 2 := Nat.div_lt_of_lt_mul (by rw [← Nat.pow_succ]; exact ha)
  have hb2 : b / 2 ^ w < 2 := Nat.div_lt_of_lt_mul (by rw [← Nat.pow_succ]; exact hb)
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at hbit
  have hq : a / 2 ^ w = b / 2 ^ w := by
    have := decide_eq_decide.mp hbit
    generalize a / 2 ^ w = p at ha2 this ⊢
    generalize b / 2 ^ w = q at hb2 this ⊢
    omega
  exact (Nat.div_add_mod a _).symm.trans (by rw [hq, hm]; exact Nat.div_add_mod b _)

/-- Under `(V4)` bounds `< bound`, any pair of sums `(t + x)` and `(t' + d)` that agree modulo
`bound` yet violate integer `(V3)` (`t + x ≠ t' + d`) differs by an exact `bound`-credit wraparound
(`t' + d = t + x + bound ∨ t + x = t' + d + bound`). -/
theorem wraparound_gap_of_mod_eq_ne {t x t' d bound : ℕ}
    (ht : t < bound) (hx : x < bound) (ht' : t' < bound) (hd : d < bound)
    (hmod : (t + x) % bound = (t' + d) % bound) (hne : t + x ≠ t' + d) :
    t' + d = t + x + bound ∨ t + x = t' + d + bound := by
  rcases add_lt_two_mul_decomp (by omega : t + x < 2 * bound) with ⟨h1, hm1⟩ | ⟨h1, hm1⟩ <;>
    rcases add_lt_two_mul_decomp (by omega : t' + d < 2 * bound) with ⟨h2, hm2⟩ | ⟨h2, hm2⟩
  · omega
  · left; omega
  · right; omega
  · omega

end Cslib.Crypto.AnonymousToken.IssuerBridge
